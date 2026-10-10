-- Prove2me | solution 1 for IntMul.TrackedOutputReturn.output_correct
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-09T22:29:10.26167+00:00
-- url     : https://prove2.me/submissions/dbeff75a-31de-4e4f-95ce-a4847db04aea

import Definitions.Def_IntMul_TrackedOutputReturn
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)


namespace IntMul.TrackedOutputReturn

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem work_ge (M : MultitapeTM) (j : Fin M.k) : 2 ≤ (workTape M j).val := by simp [workTape]

private theorem inner_work (M : MultitapeTM) (j : Fin M.k) (h : 2 ≤ (workTape M j).val) :
    innerTape M (workTape M j) h = j := by
  apply Fin.ext
  simp [workTape,innerTape]

private theorem work_inner (M : MultitapeTM) (i : Fin (M.k + 2)) (h : 2 ≤ i.val) :
    workTape M (innerTape M i h) = i := by
  apply Fin.ext
  simp only [workTape,innerTape]
  omega

private theorem buffer_boundary (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    bufferTape M base sigma w sigma = some (M.startSym,true) := by simp [bufferTape]

private theorem buffer_payload (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List Bool) (p : ℕ) :
    bufferTape M base sigma w (sigma + p + 1) =
      some ((w.map M.bitSym).getD p M.blank,decide (p < w.length)) := by
  simp only [bufferTape,if_neg (by omega : ¬sigma + p + 1 < sigma),
    if_neg (by omega : sigma + p + 1 ≠ sigma),
    show sigma + p + 1 - sigma - 1 = p by omega]

private theorem buffer_append (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ)
    (w : List Bool) (b : Bool) :
    Function.update (bufferTape M base sigma w) (sigma + w.length + 1) (some (M.bitSym b,true)) =
      bufferTape M base sigma (w ++ [b]) := by
  classical
  funext p
  by_cases hp : p < sigma
  · rw [Function.update_of_ne (by omega : p ≠ sigma + w.length + 1)]
    simp only [bufferTape,if_pos hp]
  · by_cases he : p = sigma + w.length + 1
    · subst p
      rw [Function.update_self,buffer_payload]
      simp
    · rw [Function.update_of_ne he]
      by_cases hs : p = sigma
      · subst p
        rw [buffer_boundary,buffer_boundary]
      · have hg : sigma < p := by omega
        have hn : p = sigma + (p - sigma - 1) + 1 := by omega
        rw [hn,buffer_payload,buffer_payload]
        have hq : p - sigma - 1 ≠ w.length := by omega
        simp only [List.map_append,List.map_singleton,List.length_append,List.length_singleton]
        by_cases hl : p - sigma - 1 < w.length
        · rw [List.getD_append _ _ _ _ (by simpa using hl)]
          simp only [hl,show p - sigma - 1 < w.length + 1 by omega,decide_true]
        · have hb : w.length ≤ p - sigma - 1 := by omega
          rw [List.getD_eq_default _ _ (by simpa using hb),
            List.getD_append_right _ _ _ _ (by simpa using hb),
            List.getD_eq_default _ _ (by simp; omega)]
          simp only [hl,show ¬p - sigma - 1 < w.length + 1 by omega,decide_false]

private theorem buffer_next_blank (M : MultitapeTM) (base : ℕ → Sym M) (sigma : ℕ) (w : List Bool) :
    bufferTape M base sigma w (sigma + w.length + 1) = some (M.blank,false) := by
  rw [buffer_payload]
  simp

private theorem payload_not_marker (M : MultitapeTM) (w : List Bool) (p : ℕ) :
    (w.map M.bitSym).getD p M.blank ≠ M.startSym := by
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  by_cases hp : p < w.length
  · rw [List.getD_eq_getElem _ _ (by simpa using hp),List.getElem_map]
    cases w[p] <;> simp only [MultitapeTM.bitSym,Bool.false_eq_true,if_false,if_true] <;> aesop
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    aesop

private theorem buffer_marker_iff (M : MultitapeTM) (base : ℕ → Sym M)
    (sigma : ℕ) (w : List Bool) (p : ℕ) :
    bufferTape M base sigma w (sigma + p) = some (M.startSym,true) ↔ p = 0 := by
  cases p with
  | zero => simp only [Nat.add_zero,buffer_boundary,iff_true]
  | succ p =>
      rw [show sigma + (p + 1) = sigma + p + 1 by omega,buffer_payload]
      constructor
      · intro h
        exact False.elim (payload_not_marker M w p (congrArg Prod.fst (Option.some.inj h)))
      · intro h
        omega

private theorem buffer_not_none (M : MultitapeTM) (base : ℕ → Sym M)
    (sigma : ℕ) (w : List Bool) (p : ℕ) :
    bufferTape M base sigma w (sigma + p) ≠ none := by
  simp only [bufferTape,if_neg (by omega : ¬sigma + p < sigma)]
  split <;> exact Option.some_ne_none _

private theorem tracked_scan (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j + p) =
      some (c.cells j p,decide (p ≤ extent j)) := by
  simp only [TrackedBankedSimulation.embed,dif_pos (work_ge M j),inner_work,
    if_neg (by omega : ¬offset j + p < offset j),Nat.add_sub_cancel_left]

private theorem tracked_marker_iff (M : MultitapeTM) (base : (TrackedBankedSimulation.machine M).Cfg)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (j : Fin M.k) (p : ℕ)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0) :
    (TrackedBankedSimulation.embed M base offset extent c).cells (workTape M j) (offset j + p) =
      some (M.startSym,true) ↔ p = 0 := by
  rw [tracked_scan]
  constructor
  · intro h
    exact (unique j p).mp (congrArg Prod.fst (Option.some.inj h))
  · intro h
    simp only [h,(unique j 0).mpr rfl,Nat.zero_le,decide_true]

end IntMul.TrackedOutputReturn



namespace IntMul.TrackedOutputReturn

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem rewind_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem rewind_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem rewind_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem rewind_protect_left (M : MultitapeTM) (a : Sym M) (h : a ≠ none) :
    TrackedBankCleanup.protect M a a .left = (a,.left) := by
  cases a with
  | none => exact False.elim (h rfl)
  | some s => rfl

private theorem rewind_output_origin_iff (M : MultitapeTM) (c : M.Cfg) (w : List Bool)
    (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (p : ℕ) :
    c.cells M.outTape p = M.startSym ↔ p = 0 := by
  rw [out]
  cases p with
  | zero => simp [MultitapeTM.tapeOf]
  | succ p =>
      change (w.map M.bitSym).getD p M.blank = M.startSym ↔ p + 1 = 0
      constructor
      · intro h
        exact False.elim (payload_not_marker M w p h)
      · intro h
        omega

private theorem rewind_return_scans (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    let f := returnFrame M base sigma offset extent c a b
    (f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.startSym,true) ↔ a = 0) ∧
    (f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.startSym,true) ↔ b = 0) ∧
    f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none ∧
    f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none := by
  dsimp only
  have h₁ : (returnFrame M base sigma offset extent c a b).cells
      ⟨1,by change 1 < M.k + 2; omega⟩
      ((returnFrame M base sigma offset extent c a b).head ⟨1,by change 1 < M.k + 2; omega⟩) =
      bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma [] (sigma + a) := by
    simp [returnFrame,TrackedBankedSimulation.embed,callerBase]
  have h₃ : (returnFrame M base sigma offset extent c a b).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((returnFrame M base sigma offset extent c a b).head
        ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) =
      some (c.cells M.outTape b,decide (b ≤ extent M.outTape)) := by
    have hi : 2 ≤ (⟨3,by have := M.two_le_k; omega⟩ : Fin (M.k + 2)).val := by change 2 ≤ 3; omega
    have he : innerTape M ⟨3,by have := M.two_le_k; omega⟩ hi = M.outTape := by
      apply Fin.ext
      simp [innerTape,MultitapeTM.outTape]
    simp only [returnFrame,if_neg (by omega : (3 : ℕ) ≠ 1),if_true,
      TrackedBankedSimulation.embed,dif_pos hi,he,
      if_neg (by omega : ¬offset M.outTape + b < offset M.outTape),Nat.add_sub_cancel_left]
  rw [h₁,h₃]
  refine ⟨buffer_marker_iff M _ sigma [] a,?_,buffer_not_none M _ sigma [] a,Option.some_ne_none _⟩
  constructor
  · intro h
    exact (rewind_output_origin_iff M c w out b).mp (congrArg Prod.fst (Option.some.inj h))
  · intro h
    simp only [h,(rewind_output_origin_iff M c w out 0).mpr rfl,Nat.zero_le,decide_true]

private theorem rewind_return_left_transition (M : MultitapeTM) (f : (machine M).Cfg) (a b : ℕ)
    (h₁ : f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.startSym,true) ↔ a = 0)
    (h₃ : f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.startSym,true) ↔ b = 0)
    (n₁ : f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) ≠ none)
    (n₃ : f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) ≠ none)
    (hab : ¬(a = 0 ∧ b = 0)) :
    transition M .rewind (fun i => f.cells i (f.head i)) =
      (.rewind,fun i => (f.cells i (f.head i),
        if i.val = 1 then (if a = 0 then .stay else .left)
        else if i.val = 3 then (if b = 0 then .stay else .left) else .stay)) := by
  classical
  have hn : ¬(f.cells ⟨1,by change 1 < M.k + 2; omega⟩ (f.head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.startSym,true) ∧
      f.cells ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ (f.head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = some (M.startSym,true)) := by
    intro h
    exact hab ⟨h₁.mp h.1,h₃.mp h.2⟩
  simp only [transition,rawTransition,if_neg hn]
  congr 1
  funext i
  by_cases hi : i.val = 1
  · have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext hi
    by_cases ha : a = 0
    · have hm : f.cells i (f.head i) = some (M.startSym,true) := by rw [he]; exact h₁.mpr ha
      have hd : ¬((i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some (M.startSym,true)) := by intro h; exact h.2 hm
      simp only [if_neg hd,if_pos hi,if_pos ha,rewind_protect_stay]
    · have hm : f.cells i (f.head i) ≠ some (M.startSym,true) := by rw [he]; exact mt h₁.mp ha
      have hd : (i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some (M.startSym,true) := ⟨Or.inl hi,hm⟩
      simp only [if_pos hd,if_pos hi,if_neg ha]
      exact rewind_protect_left M _ (by rw [he]; exact n₁)
  · by_cases ho : i.val = 3
    · have he : i = ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ := Fin.ext ho
      by_cases hb : b = 0
      · have hm : f.cells i (f.head i) = some (M.startSym,true) := by rw [he]; exact h₃.mpr hb
        have hd : ¬((i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some (M.startSym,true)) := by intro h; exact h.2 hm
        simp only [if_neg hd,if_neg hi,if_pos ho,if_pos hb,rewind_protect_stay]
      · have hm : f.cells i (f.head i) ≠ some (M.startSym,true) := by rw [he]; exact mt h₃.mp hb
        have hd : (i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some (M.startSym,true) := ⟨Or.inr ho,hm⟩
        simp only [if_pos hd,if_neg hi,if_pos ho,if_neg hb]
        exact rewind_protect_left M _ (by rw [he]; exact n₃)
    · have hd : ¬((i.val = 1 ∨ i.val = 3) ∧ f.cells i (f.head i) ≠ some (M.startSym,true)) := by tauto
      simp only [if_neg hi,if_neg ho,if_neg hd,rewind_protect_stay]

private theorem rewind_return_left_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ)
    (hab : ¬(a = 0 ∧ b = 0)) :
    (machine M).step (returnFrame M base sigma offset extent c a b) =
      returnFrame M base sigma offset extent c (a - 1) (b - 1) := by
  obtain ⟨h₁,h₃,n₁,n₃⟩ := rewind_return_scans M base sigma offset extent c w out a b
  have ht := rewind_return_left_transition M (returnFrame M base sigma offset extent c a b) a b h₁ h₃ n₁ n₃ hab
  change transition M (returnFrame M base sigma offset extent c a b).state
    (fun i => (returnFrame M base sigma offset extent c a b).cells i
      ((returnFrame M base sigma offset extent c a b).head i)) = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnFrame,if_pos hi]
      by_cases ha : a = 0
      · simp only [if_pos ha]
        subst a
        rfl
      · simp only [if_neg ha]
        omega
    · by_cases ho : i.val = 3
      · simp only [returnFrame,if_neg hi,if_pos ho]
        by_cases hb : b = 0
        · simp only [if_pos hb]
          subst b
          rfl
        · simp only [if_neg hb]
          omega
      · simp only [returnFrame,if_neg hi,if_neg ho,TrackedBankedSimulation.embed,callerBase,if_neg hi]

/-- Each return head stops independently at its marker. The exact number of
left transitions is the maximum of the two initial distances. -/
private theorem rewind_pair_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset : Fin M.k → ℕ) (extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b] (returnFrame M base sigma offset extent c a b) =
      returnFrame M base sigma offset extent c 0 0 := by
  generalize hn : max a b = n
  induction n using Nat.strong_induction_on generalizing a b with
  | h n ih =>
      by_cases hz : a = 0 ∧ b = 0
      · obtain ⟨rfl,rfl⟩ := hz
        simp only [max_self] at hn
        subst n
        rfl
      · have hm : max (a - 1) (b - 1) < n := by omega
        have he : n = max (a - 1) (b - 1) + 1 := by omega
        rw [he,Function.iterate_succ_apply,rewind_return_left_step M base sigma offset extent c w out a b hz]
        exact ih _ hm (a - 1) (b - 1) rfl


private theorem rewind_return_marker_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h₁ : a ⟨1,by omega⟩ = some (M.startSym,true))
    (h₃ : a ⟨3,by have := M.two_le_k; omega⟩ = some (M.startSym,true)) :
    transition M (.rewind) a = (.copy,fun i =>
      (a i,if i.val = 1 ∨ i.val = 3 then .right else .stay)) := by
  classical
  simp only [transition,rawTransition,if_pos (And.intro h₁ h₃)]
  congr 1
  funext i
  by_cases hi : i.val = 1 ∨ i.val = 3
  · simp only [if_pos hi,rewind_protect_right]
  · simp only [if_neg hi,rewind_protect_stay]


private theorem rewind_return_marker_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (returnFrame M base sigma offset extent c 0 0) =
      copyFrame M base sigma offset extent c w 0 := by
  obtain ⟨h₁,h₃,_,_⟩ := rewind_return_scans M base sigma offset extent c w out 0 0
  have ht := rewind_return_marker_transition M
    (fun i => (returnFrame M base sigma offset extent c 0 0).cells i
      ((returnFrame M base sigma offset extent c 0 0).head i)) (h₁.mpr rfl) (h₃.mpr rfl)
  change transition M (returnFrame M base sigma offset extent c 0 0).state
    (fun i => (returnFrame M base sigma offset extent c 0 0).cells i
      ((returnFrame M base sigma offset extent c 0 0).head i)) = _ at ht
  apply rewind_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    by_cases hi : i.val = 1
    · simp only [returnFrame,copyFrame,if_pos hi,List.take_zero,
        TrackedBankedSimulation.embed,dif_neg (by omega : ¬2 ≤ i.val),callerBase,if_pos hi]
    · simp only [returnFrame,copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [returnFrame,copyFrame,if_pos hi,if_pos (Or.inl hi),Nat.add_zero]
    · by_cases ho : i.val = 3
      · simp only [returnFrame,copyFrame,if_neg hi,if_pos ho,if_pos (Or.inr ho),Nat.add_zero]
      · simp only [returnFrame,copyFrame,if_neg hi,if_neg ho,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3))]

private theorem rewind_output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b + 1] (returnFrame M base sigma offset extent c a b) =
      copyFrame M base sigma offset extent c w 0 := by
  rw [Function.iterate_succ_apply',rewind_pair_correct M base sigma offset extent c w out a b,
    rewind_return_marker_step M base sigma offset extent c w out]

end IntMul.TrackedOutputReturn



namespace IntMul.TrackedOutputReturn

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

private theorem copy_cfg_ext (N : MultitapeTM) (c d : N.Cfg)
    (hs : c.state = d.state) (hc : c.cells = d.cells) (hh : c.head = d.head) : c = d := by
  cases c
  cases d
  cases hs
  cases hc
  cases hh
  rfl

private theorem copy_protect_right (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .right = (a,.right) := by cases a <;> rfl

private theorem copy_protect_stay (M : MultitapeTM) (a : Sym M) :
    TrackedBankCleanup.protect M a a .stay = (a,.stay) := by cases a <;> rfl

private theorem decoded_output_scan (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (j : ℕ) :
    TrackedBankedSimulation.decode M ((copyFrame M base sigma offset extent c w j).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset extent c w j).head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩)) =
        c.cells M.outTape (j + 1) := by
  have hi : 2 ≤ (⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ : Fin (M.k + 2)).val := by change 2 ≤ 3; omega
  have he : innerTape M ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩ hi = M.outTape := by
    apply Fin.ext
    simp [innerTape,MultitapeTM.outTape]
  simp only [copyFrame,if_neg (by omega : (3 : ℕ) ≠ 1),if_true,
    TrackedBankedSimulation.embed,dif_pos hi,he,
    if_neg (by omega : ¬offset M.outTape + j + 1 < offset M.outTape),
    show offset M.outTape + j + 1 - offset M.outTape = j + 1 by omega,
    TrackedBankedSimulation.decode]

private theorem copy_copy_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (b : Bool) (source : TrackedBankedSimulation.decode M
      (a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = M.bitSym b)
    (target : a ⟨1,by change 1 < M.k + 2; omega⟩ = some (M.blank,false)) :
    transition M .copy a = (.copy,fun i =>
      (if i.val = 1 then some (M.bitSym b,true) else a i,
        if i.val = 1 ∨ i.val = 3 then .right else .stay)) := by
  classical
  have hb : TrackedBankedSimulation.decode M (a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = M.zero ∨
      TrackedBankedSimulation.decode M (a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = M.one := by
    rw [source]
    cases b <;> simp [MultitapeTM.bitSym]
  simp only [transition,rawTransition,if_pos hb]
  congr 1
  funext i
  by_cases ht : i.val = 1
  · have he : i = ⟨1,by change 1 < M.k + 2; omega⟩ := Fin.ext ht
    simp only [if_pos ht,if_pos (Or.inl ht)]
    rw [he,target,source]
    rfl
  · simp only [if_neg ht]
    by_cases hs : i.val = 3
    · simp only [if_pos (Or.inr hs),copy_protect_right]
    · simp only [if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3)),copy_protect_stay]

private theorem copy_copy_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j < w.length) :
    (machine M).step (copyFrame M base sigma offset extent c w j) =
      copyFrame M base sigma offset extent c w (j + 1) := by
  have hs : TrackedBankedSimulation.decode M ((copyFrame M base sigma offset extent c w j).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset extent c w j).head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩)) = M.bitSym w[j] := by
    rw [decoded_output_scan,out]
    change (w.map M.bitSym).getD j M.blank = _
    rw [List.getD_eq_getElem _ _ (by simpa using hj),List.getElem_map]
  have hl : (w.take j).length = j := by simp [Nat.min_eq_left hj.le]
  have hb : (copyFrame M base sigma offset extent c w j).cells
      ⟨1,by change 1 < M.k + 2; omega⟩ ((copyFrame M base sigma offset extent c w j).head ⟨1,by change 1 < M.k + 2; omega⟩) = some (M.blank,false) := by
    change bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (w.take j) (sigma + j + 1) = _
    simpa only [hl] using buffer_next_blank M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (w.take j)
  have ht := copy_copy_transition M
    (fun i => (copyFrame M base sigma offset extent c w j).cells i
      ((copyFrame M base sigma offset extent c w j).head i)) w[j] hs hb
  change transition M (copyFrame M base sigma offset extent c w j).state
    (fun i => (copyFrame M base sigma offset extent c w j).cells i
      ((copyFrame M base sigma offset extent c w j).head i)) = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [if_pos hi,copyFrame]
      change Function.update (bufferTape M (base.cells i) sigma (w.take j))
        (sigma + j + 1) (some (M.bitSym w[j],true)) =
          bufferTape M (base.cells i) sigma (w.take (j + 1))
      rw [List.take_succ_eq_append_getElem hj]
      simpa only [hl] using buffer_append M (base.cells i) sigma (w.take j) w[j]
    · simp only [if_neg hi]
      rw [Function.update_eq_self]
      simp only [copyFrame,if_neg hi]
  · simp only [MultitapeTM.step,ht]
    funext i
    by_cases hi : i.val = 1
    · simp only [copyFrame,if_pos hi,if_pos (Or.inl hi),Nat.add_assoc]
    · by_cases ho : i.val = 3
      · simp only [copyFrame,if_neg hi,if_pos ho,if_pos (Or.inr ho),Nat.add_assoc]
      · simp only [copyFrame,if_neg hi,if_neg ho,
          if_neg (by tauto : ¬(i.val = 1 ∨ i.val = 3))]

private theorem copy_run (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (j : ℕ) (hj : j ≤ w.length) :
    (machine M).step^[j] (copyFrame M base sigma offset extent c w 0) =
      copyFrame M base sigma offset extent c w j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply',ih (by omega),
      copy_copy_step M base sigma offset extent c w out j (by omega)]

private theorem copy_copy_end_transition (M : MultitapeTM) (a : Fin (M.k + 2) → Sym M)
    (h : TrackedBankedSimulation.decode M (a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = M.blank) :
    transition M .copy a = (.halt,fun i => (a i,.stay)) := by
  classical
  have hd := M.syms_distinct
  simp only [List.nodup_cons,List.mem_cons,not_or] at hd
  have hn : ¬(TrackedBankedSimulation.decode M (a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = M.zero ∨
      TrackedBankedSimulation.decode M (a ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩) = M.one) := by
    rw [h]
    aesop
  simp [transition,rawTransition,hn,copy_protect_stay]

private theorem copy_end_step (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    (machine M).step (copyFrame M base sigma offset extent c w w.length) =
      finalFrame M base sigma offset extent c w := by
  have hr : TrackedBankedSimulation.decode M ((copyFrame M base sigma offset extent c w w.length).cells
      ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩
      ((copyFrame M base sigma offset extent c w w.length).head ⟨3,by change 3 < M.k + 2; have := M.two_le_k; omega⟩)) = M.blank := by
    rw [decoded_output_scan,out]
    change (w.map M.bitSym).getD w.length M.blank = _
    rw [List.getD_eq_default _ _ (by simp)]
  have ht := copy_copy_end_transition M
    (fun i => (copyFrame M base sigma offset extent c w w.length).cells i
      ((copyFrame M base sigma offset extent c w w.length).head i)) hr
  change transition M (copyFrame M base sigma offset extent c w w.length).state
    (fun i => (copyFrame M base sigma offset extent c w w.length).cells i
      ((copyFrame M base sigma offset extent c w w.length).head i)) = _ at ht
  apply copy_cfg_ext
  · simp only [MultitapeTM.step,ht]
    rfl
  · simp only [MultitapeTM.step,ht]
    funext i
    rw [Function.update_eq_self]
    rfl
  · simp only [MultitapeTM.step,ht]
    rfl

end IntMul.TrackedOutputReturn



namespace IntMul.TrackedOutputReturn

open IntMul.BankedSimulation (workTape innerTape)
open IntMul.TrackedBankedSimulation (Sym)

/-- Both seeks, the marker-to-payload dispatch, every copied bit and the final
blank-to-halt transition are physically charged. Child workspace stays intact. -/
private theorem output_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b + w.length + 2] (returnFrame M base sigma offset extent c a b) =
      finalFrame M base sigma offset extent c w := by
  rw [show max a b + w.length + 2 = (w.length + (max a b + 1)) + 1 by omega,
    Function.iterate_succ_apply',Function.iterate_add_apply,
    rewind_output_correct M base sigma offset extent c w out a b,
    copy_run M base sigma offset extent c w out w.length le_rfl,
    copy_end_step M base sigma offset extent c w out]

/-- Every child-bank cell, including its finite visited flag, is unchanged;
the caller input is unchanged, and the output buffer has the returned word. -/
private theorem returned_cells (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) (a b : ℕ) :
    (∀ i : Fin (M.k + 2), i.val ≠ 1 →
      (finalFrame M base sigma offset extent c w).cells i =
        (returnFrame M base sigma offset extent c a b).cells i) ∧
      (finalFrame M base sigma offset extent c w).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
        bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w := by
  constructor
  · intro i hi
    simp only [finalFrame,copyFrame,returnFrame,if_neg hi]
    rfl
  · simp [finalFrame,copyFrame]

/-- Only the two copy heads move; all other heads retain their original
child/caller positions. Work prefixes remain outside every local seek. -/
private theorem returned_heads (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg) (w : List Bool) :
    (finalFrame M base sigma offset extent c w).head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma + w.length + 1 ∧
      (∀ j, (finalFrame M base sigma offset extent c w).head (workTape M j) =
        offset j + (if j = M.outTape then w.length + 1 else c.head j)) := by
  constructor
  · simp [finalFrame,copyFrame]
  · intro j
    have hn : (workTape M j).val ≠ 1 := by simp [workTape]
    have ho : (workTape M j).val = 3 ↔ j = M.outTape := by
      simp only [workTape,MultitapeTM.outTape,Fin.ext_iff]
      omega
    by_cases hj : j = M.outTape
    · subst j
      simp [finalFrame,copyFrame,workTape,MultitapeTM.outTape,Nat.add_assoc]
    · have hv : (workTape M j).val ≠ 3 := mt ho.mp hj
      simp only [finalFrame,copyFrame,if_neg hn,if_neg hv,if_neg hj,
        TrackedBankedSimulation.embed,dif_pos (work_ge M j),inner_work]

end IntMul.TrackedOutputReturn


open IntMul IntMul.TrackedOutputReturn

theorem solution (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma : ℕ) (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (w : List Bool) (out : c.cells M.outTape = M.tapeOf (w.map M.bitSym)) (a b : ℕ) :
    (machine M).step^[max a b + w.length + 2] (returnFrame M base sigma offset extent c a b) =
      finalFrame M base sigma offset extent c w :=
  IntMul.TrackedOutputReturn.output_correct M base sigma offset extent c w out a b

#print axioms solution
