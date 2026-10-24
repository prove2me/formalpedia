-- Prove2me | solution 1 for OAI.ExactFourier.SparseReflection.exists_reflection_nnz
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:04:42.931849+00:00
-- url     : https://prove2.me/submissions/7cdfcc6a-91b2-401d-bb87-0f23cd0d765e

import Mathlib
import Definitions.Def_ExactFourier
import Definitions.Def_OAIQWEXF000
import Theorems.Thm_OAI_ExactFourier_SparseReflection_exists_tangent

section
-- module Solutions.OAIQW_ExactFourier.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Shears
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

theorem Gate.eval_add {w : ℕ} (g : Gate w) (v v' : Fin w → ℂ) :
    g.eval (v + v') = g.eval v + g.eval v' := by
  cases g <;> simp only [Gate.eval, Pi.add_apply] <;> ring

theorem snoc_add {n : ℕ} (v v' : Fin n → ℂ) (a a' : ℂ) :
    (Fin.snoc (v + v') (a + a') : Fin (n + 1) → ℂ) =
      (Fin.snoc v a : Fin (n + 1) → ℂ) + (Fin.snoc v' a' : Fin (n + 1) → ℂ) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem Program.dirtyEval_add {n k : ℕ} (p : Program n k)
    (x x' : Fin n → ℂ) (z z' : Fin k → ℂ) :
    p.dirtyEval (x + x') (z + z') = p.dirtyEval x z + p.dirtyEval x' z' := by
  induction p with
  | nil => simpa [Program.dirtyEval] using snoc_add x x' 0 0
  | @step k p g ih =>
      simp only [Program.dirtyEval]
      rw [show Fin.init (z + z') = Fin.init z + Fin.init z' from rfl,
        ih, Gate.eval_add]
      have e : (z + z') (Fin.last k) + (g.eval (p.dirtyEval x (Fin.init z)) + g.eval (p.dirtyEval x' (Fin.init z'))) =
          (z (Fin.last k) + g.eval (p.dirtyEval x (Fin.init z))) +
            (z' (Fin.last k) + g.eval (p.dirtyEval x' (Fin.init z'))) := by
        simp only [Pi.add_apply]; ring
      rw [e]
      exact snoc_add _ _ _ _

theorem Program.dirtyEval_clean {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) :
    p.dirtyEval x 0 = p.eval x := by
  induction p with
  | nil => rfl
  | @step k p g ih =>
      simp only [Program.dirtyEval, Program.eval]
      rw [show Fin.init (0 : Fin (k + 1) → ℂ) = 0 from rfl, ih]
      simp

/-- Exact identity behind the two replays (`fft:dirty-forward`, `fft:dirty-output`). -/
theorem Program.dirtyEval_split {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) :
    p.dirtyEval x z = p.eval x + p.dirtyEval 0 z := by
  simpa only [add_zero, zero_add, Program.dirtyEval_clean] using
    p.dirtyEval_add x 0 0 z

end ExactFourier

namespace ExactFourier

theorem readCoord_congr_except {ι : Type*} (d : ι) (r : Option ι)
    (h : ∀ i, r = some i → d ≠ i) (v v' : ι → ℂ)
    (hv : ∀ i, i ≠ d → v' i = v i) : readCoord r v' = readCoord r v := by
  cases r with
  | none => rfl
  | some i => exact hv i (h i rfl).symm

/-- Adding one permitted reference uses at most one elementary coordinate shear. -/
theorem add_reference {ι : Type*} (d : ι) (r : Option ι) (c : ℂ)
    (h : ∀ i, r = some i → d ≠ i) :
    ∃ W : List (Shear ι), W.length ≤ 1 ∧ ∀ v : ι → ℂ,
      runShears W v d = v d + c * readCoord r v ∧
      ∀ i, i ≠ d → runShears W v i = v i := by
  classical
  cases r with
  | none =>
      refine ⟨[], by simp, ?_⟩
      intro v
      simp [readCoord]
  | some j =>
      refine ⟨[⟨d, j, h j rfl, c⟩], by simp, ?_⟩
      intro v
      constructor
      · simp [readCoord, Shear.act]
      · intro i hi
        simp [Shear.act, hi]

/-- A gate's two (or one) distinct-from-destination reads, with repeated operands allowed. -/
theorem add_gate {ι : Type*} {w : ℕ} (d : ι) (refs : Fin w → Option ι)
    (h : ∀ a j, refs a = some j → d ≠ j) (g : Gate w) :
    ∃ W : List (Shear ι), W.length ≤ 2 ∧ ∀ v : ι → ℂ,
      runShears W v d = v d + g.eval (fun a => readCoord (refs a) v) ∧
      ∀ i, i ≠ d → runShears W v i = v i := by
  classical
  cases g with
  | scale c a =>
      obtain ⟨W, hw, he⟩ := add_reference d (refs a) c (h a)
      exact ⟨W, hw.trans (by omega), he⟩
  | add a b =>
      obtain ⟨W, hw, he⟩ := add_reference d (refs a) 1 (h a)
      obtain ⟨V, hv, hf⟩ := add_reference d (refs b) 1 (h b)
      refine ⟨W ++ V, by simp only [List.length_append]; omega, ?_⟩
      intro v
      rw [runShears_append]
      constructor
      · rw [(hf _).1, (he v).1,
          readCoord_congr_except d (refs b) (h b) v (runShears W v) (he v).2]
        simp only [Gate.eval, one_mul]
        ring
      · intro i hi
        rw [(hf _).2 i hi, (he v).2 i hi]
  | sub a b =>
      obtain ⟨W, hw, he⟩ := add_reference d (refs a) 1 (h a)
      obtain ⟨V, hv, hf⟩ := add_reference d (refs b) (-1) (h b)
      refine ⟨W ++ V, by simp only [List.length_append]; omega, ?_⟩
      intro v
      rw [runShears_append]
      constructor
      · rw [(hf _).1, (he v).1,
          readCoord_congr_except d (refs b) (h b) v (runShears W v) (he v).2]
        simp only [Gate.eval, one_mul, neg_mul]
        ring
      · intro i hi
        rw [(hf _).2 i hi, (he v).2 i hi]

end ExactFourier

namespace ExactFourier

theorem Program.dirtyEval_input {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) (i : Fin (n + 1)) :
    p.dirtyEval x z (Fin.castAdd k i) = (Fin.snoc x 0 : Fin (n + 1) → ℂ) i := by
  induction p with
  | nil => simp [Program.dirtyEval]
  | @step k p g ih =>
      change (Fin.snoc (p.dirtyEval x (Fin.init z)) _ : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (Fin.castAdd k i)) = _
      rw [Fin.snoc_castSucc, ih]

theorem Program.dirtyEval_available {n k : ℕ} (p : Program n k)
    (x : Fin n → ℂ) (z : Fin k → ℂ) :
    p.dirtyEval x z = available x (p.dirtyScratch x z) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [available, Program.dirtyEval_input]
  · simp [available, Program.dirtyScratch]

theorem read_referenceMap {ι : Type*} {n k : ℕ} (enabled : Bool)
    (xs : Fin n → ι) (zs : Fin k → ι) (v : ι → ℂ) :
    (fun a => readCoord (referenceMap enabled xs zs a) v) =
      available (replayInputs enabled xs v) (v ∘ zs) := by
  funext a
  refine Fin.addCases (fun i => ?_) (fun j => ?_) a
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [referenceMap, available, readCoord]
    · cases enabled <;> simp [referenceMap, available, replayInputs, readCoord]
  · simp [referenceMap, available, readCoord]

theorem referenceMap_avoids {ι : Type*} {n k : ℕ} (enabled : Bool)
    (xs : Fin n → ι) (zs : Fin k → ι) (d : ι)
    (hx : ∀ i, d ≠ xs i) (hz : ∀ j, d ≠ zs j) :
    ∀ a j, referenceMap enabled xs zs a = some j → d ≠ j := by
  intro a
  refine Fin.addCases (fun i => ?_) (fun i => ?_) a
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [referenceMap]
    · cases enabled <;> simp [referenceMap, hx]
  · simpa [referenceMap] using hz i

/-- The full forward-sweep construction, with one coordinate per gate and NO zero
register. Its exact semantic statement is uniform in arbitrary dirty initial values. -/
theorem Program.dirtySweep_exists {ι : Type*} {n k : ℕ} (p : Program n k)
    (enabled : Bool) (xs : Fin n → ι) (zs : Fin k → ι)
    (hz : Function.Injective zs) (hxz : ∀ i j, xs i ≠ zs j) :
    ∃ W : List (Shear ι), W.length ≤ 2 * k ∧ ∀ v : ι → ℂ,
      (∀ j, runShears W v (zs j) =
        p.dirtyScratch (replayInputs enabled xs v) (v ∘ zs) j) ∧
      (∀ r, (∀ j, r ≠ zs j) → runShears W v r = v r) := by
  classical
  induction p with
  | nil =>
      refine ⟨[], by simp, ?_⟩
      intro v
      exact ⟨fun j => Fin.elim0 j, fun _ _ => rfl⟩
  | @step k p g ih =>
      let zs' : Fin k → ι := fun j => zs j.castSucc
      have hzi : Function.Injective zs' := hz.comp (Fin.castSucc_injective k)
      have hxzi : ∀ i j, xs i ≠ zs' j := fun i j => hxz i j.castSucc
      obtain ⟨W, hW, hWe⟩ := ih zs' hzi hxzi
      let d := zs (Fin.last k)
      have hdold : ∀ j, d ≠ zs' j := by
        intro j he
        have := hz he
        have hv := congrArg Fin.val this
        simp only [Fin.val_last, Fin.val_castSucc] at hv
        omega
      have hdx : ∀ i, d ≠ xs i := fun i => (hxz i (Fin.last k)).symm
      obtain ⟨V, hV, hVe⟩ := add_gate d (referenceMap enabled xs zs')
        (referenceMap_avoids enabled xs zs' d hdx hdold) g
      refine ⟨W ++ V, by simp only [List.length_append]; omega, ?_⟩
      intro v
      have hsrc : replayInputs enabled xs (runShears W v) = replayInputs enabled xs v := by
        funext i
        simp only [replayInputs]
        congr 1
        exact (hWe v).2 (xs i) (hxzi i)
      have hscratch : (runShears W v) ∘ zs' =
          p.dirtyScratch (replayInputs enabled xs v) (v ∘ zs') := by
        funext j
        exact (hWe v).1 j
      constructor
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · rw [runShears_append, (hVe _).1, (hWe v).2 d hdold,
            Program.dirtyScratch_step_last]
          rw [read_referenceMap, hsrc, hscratch, ← Program.dirtyEval_available]
          rfl
        · rw [runShears_append, (hVe _).2 (zs j.castSucc) (hdold j).symm,
            (hWe v).1 j, Program.dirtyScratch_step_cast]
          rfl
      · intro r hr
        rw [runShears_append, (hVe _).2 r (hr (Fin.last k))]
        exact (hWe v).2 r (fun j => hr j.castSucc)

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Prices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

/-- Lifting an in-place word to disjoint targets adds no auxiliary coordinates. -/
theorem Shear.act_sumInl {ι κ : Type*} (s : Shear ι) (v : ι → ℂ) (y : κ → ℂ) :
    Shear.act (s.sumInl κ) (Sum.elim v y) = Sum.elim (s.act v) y := by
  classical
  funext a
  cases a <;> simp [Shear.act, Matrix.TransvectionStruct.sumInl]

theorem runShears_sumInl {ι κ : Type*} (W : List (Shear ι)) (v : ι → ℂ) (y : κ → ℂ) :
    runShears (W.map (fun s => s.sumInl κ)) (Sum.elim v y) =
      Sum.elim (runShears W v) y := by
  induction W generalizing v with
  | nil => rfl
  | cons s W ih =>
      simp only [List.map_cons, runShears_cons, Shear.act_sumInl, ih]

theorem Program.memorySweep_exists {n k : ℕ} (p : Program n k) (enabled : Bool) :
    ∃ W : List (Shear (Fin n ⊕ Fin k)), W.length ≤ 2 * k ∧
      ∀ (x : Fin n → ℂ) (z : Fin k → ℂ),
        runShears W (Sum.elim x z) =
          Sum.elim x (p.dirtyScratch (if enabled then x else 0) z) := by
  obtain ⟨W, hW, he⟩ := p.dirtySweep_exists enabled Sum.inl Sum.inr
    (fun _ _ h => Sum.inr.inj h) (by intros; simp)
  refine ⟨W, hW, ?_⟩
  intro x z
  funext r
  cases r with
  | inl i => simpa using (he (Sum.elim x z)).2 (Sum.inl i) (by intros; simp)
  | inr j =>
      have hi := (he (Sum.elim x z)).1 j
      convert hi using 1
      cases enabled <;> rfl

open Classical in
/-- The designated outputs are individual reads, not uncharged arbitrary linear maps. -/
theorem broadcast_subset_exists {ι κ : Type*} (S : Finset κ) (refs : κ → Option ι) :
    ∃ W : List (Shear (ι ⊕ κ)), W.length ≤ S.card ∧
      ∀ (v : ι → ℂ) (y : κ → ℂ),
        runShears W (Sum.elim v y) =
          Sum.elim v (fun j => y j + if j ∈ S then readCoord (refs j) v else 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨[], by simp, ?_⟩
      intros
      simp
  | @insert j S hj ih =>
      obtain ⟨W, hW, hWe⟩ := ih
      obtain ⟨V, hV, hVe⟩ := add_reference (Sum.inr j) ((refs j).map Sum.inl) 1
        (by intro r hr; cases h : refs j <;> simp [h] at hr
            subst r; simp)
      refine ⟨W ++ V, by simp only [List.length_append, Finset.card_insert_of_notMem hj]; omega,
        ?_⟩
      intro v y
      rw [runShears_append, hWe]
      funext r
      cases r with
      | inl i =>
          simpa using (hVe (Sum.elim v
            (fun k => y k + if k ∈ S then readCoord (refs k) v else 0))).2 (Sum.inl i)
              (by simp)
      | inr k =>
          by_cases hkj : k = j
          · subst k
            rw [(hVe _).1]
            cases h : refs j <;> simp [h, readCoord, hj]
          · rw [(hVe _).2 (Sum.inr k) (by simp [hkj])]
            simp [hkj]

theorem broadcast_exists {ι κ : Type*} [Fintype κ] (refs : κ → Option ι) :
    ∃ W : List (Shear (ι ⊕ κ)), W.length ≤ Fintype.card κ ∧
      ∀ (v : ι → ℂ) (y : κ → ℂ),
        runShears W (Sum.elim v y) = Sum.elim v (fun j => y j + readCoord (refs j) v) := by
  classical
  simpa using broadcast_subset_exists Finset.univ refs

/-- Inverting the output-read word subtracts exactly the same reads. -/
theorem broadcast_reverse {ι κ : Type*} (W : List (Shear (ι ⊕ κ)))
    (R : (ι → ℂ) → κ → ℂ)
    (hW : ∀ v y, runShears W (Sum.elim v y) = Sum.elim v (fun j => y j + R v j))
    (v : ι → ℂ) (y : κ → ℂ) :
    runShears (reverseShears W) (Sum.elim v y) =
      Sum.elim v (fun j => y j - R v j) := by
  have h := runShears_reverse W (Sum.elim v (fun j => y j - R v j))
  rw [hW] at h
  simpa using h

end ExactFourier

namespace ExactFourier

/-- Forward/read/reverse on arbitrary memory. This is a word identity, not an
assumption that dirty scratch starts at zero. -/
theorem replay_readout {ι κ : Type*} (W : List (Shear ι))
    (B : List (Shear (ι ⊕ κ))) (R : (ι → ℂ) → κ → ℂ)
    (hB : ∀ v y, runShears B (Sum.elim v y) = Sum.elim v (fun j => y j + R v j))
    (v : ι → ℂ) (y : κ → ℂ) :
    runShears ((W.map (fun s => s.sumInl κ)) ++ B ++
        reverseShears (W.map (fun s => s.sumInl κ))) (Sum.elim v y) =
      Sum.elim v (fun j => y j + R (runShears W v) j) := by
  simp only [runShears_append, runShears_sumInl, hB]
  have h := runShears_reverse (W.map (fun s => s.sumInl κ))
    (Sum.elim v (fun j => y j + R (runShears W v) j))
  rw [runShears_sumInl] at h
  exact h

theorem dirty_coordinate_replay_count {n a : ℕ} (C : LinearDAG n a) :
    ∃ W : List (Shear ((Fin n ⊕ Fin C.size) ⊕ Fin a)),
      W.length ≤ 8 * C.size + 2 * a ∧
      ∀ (x : Fin n → ℂ) (y : Fin a → ℂ) (z : Fin C.size → ℂ),
        runShears W (Sum.elim (Sum.elim x z) y) =
          Sum.elim (Sum.elim x z) (fun j => y j + C.eval x j) := by
  classical
  let mem := Fin n ⊕ Fin C.size
  let refs (enabled : Bool) : Fin a → Option mem := fun j =>
    referenceMap enabled Sum.inl Sum.inr (C.outputs j)
  let R (enabled : Bool) (v : mem → ℂ) (j : Fin a) := readCoord (refs enabled j) v
  obtain ⟨W, hW, hWe⟩ := C.program.memorySweep_exists true
  obtain ⟨V, hV, hVe⟩ := C.program.memorySweep_exists false
  obtain ⟨B, hB, hBe⟩ := broadcast_exists (refs true)
  obtain ⟨D, hD, hDe⟩ := broadcast_exists (refs false)
  let W' := W.map (fun s => s.sumInl (Fin a))
  let V' := V.map (fun s => s.sumInl (Fin a))
  let first := W' ++ B ++ reverseShears W'
  let second := V' ++ reverseShears D ++ reverseShears V'
  refine ⟨first ++ second, ?_, ?_⟩
  · simp only [first, second, W', V', List.length_append, List.length_map,
      reverseShears_length, Fintype.card_fin] at *
    omega
  · intro x y z
    have hR (enabled : Bool) (xs : Fin n → ℂ) (zs : Fin C.size → ℂ) (j : Fin a) :
        R enabled (Sum.elim xs zs) j =
          available (if enabled then xs else 0) zs (C.outputs j) := by
      have h := congrFun (read_referenceMap enabled
        (Sum.inl : Fin n → mem) Sum.inr (Sum.elim xs zs)) (C.outputs j)
      cases enabled <;> exact h
    have hFirst : runShears first (Sum.elim (Sum.elim x z) y) =
        Sum.elim (Sum.elim x z)
          (fun j => y j + C.program.dirtyEval x z (C.outputs j)) := by
      rw [show first = W.map (fun s => s.sumInl (Fin a)) ++ B ++
          reverseShears (W.map (fun s => s.sumInl (Fin a))) from rfl]
      rw [replay_readout W B (R true) hBe, hWe]
      simp only [↓reduceIte, hR]
      rw [← C.program.dirtyEval_available x z]
    have hDrev : ∀ v y, runShears (reverseShears D) (Sum.elim v y) =
        Sum.elim v (fun j => y j + -R false v j) := by
      intro v y
      simpa only [sub_eq_add_neg] using broadcast_reverse D (R false) hDe v y
    have hSecond (ys : Fin a → ℂ) :
        runShears second (Sum.elim (Sum.elim x z) ys) =
          Sum.elim (Sum.elim x z)
            (fun j => ys j - C.program.dirtyEval 0 z (C.outputs j)) := by
      rw [show second = V.map (fun s => s.sumInl (Fin a)) ++ reverseShears D ++
          reverseShears (V.map (fun s => s.sumInl (Fin a))) from rfl]
      rw [replay_readout V (reverseShears D) (fun v j => -R false v j) hDrev, hVe]
      simp only [Bool.false_eq_true, ↓reduceIte, hR, sub_eq_add_neg]
      rw [← C.program.dirtyEval_available 0 z]
    rw [runShears_append, hFirst, hSecond]
    congr 1
    funext j
    rw [C.program.dirtyEval_split x z]
    simp [LinearDAG.eval, add_sub_assoc]

end ExactFourier

namespace ExactFourier

/-- The operational shears above are the ordinary elementary matrices. -/
theorem Shear.act_eq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Shear ι) (v : ι → ℂ) : s.act v = s.toMatrix.mulVec v := by
  funext i
  by_cases h : i = s.i <;> simp [Shear.act, Matrix.TransvectionStruct.toMatrix,
    Matrix.transvection, Matrix.add_mulVec, Matrix.single_mulVec, h]

theorem runShears_eq_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : List (Shear ι)) (v : ι → ℂ) : runShears W v = (shearMatrix W).mulVec v := by
  induction W generalizing v with
  | nil => simp [shearMatrix]
  | cons s W ih =>
      rw [runShears_cons, ih, Shear.act_eq_mulVec]
      simp [shearMatrix, Matrix.mulVec_mulVec]

theorem replayMatrix_mulVec {n a k : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (x : Fin n → ℂ) (z : Fin k → ℂ) (y : Fin a → ℂ) :
    (replayMatrix G).mulVec (Sum.elim (Sum.elim x z) y) =
      Sum.elim (Sum.elim x z) (fun j => y j + G.mulVec x j) := by
  funext r
  cases r <;> simp [replayMatrix, Matrix.fromBlocks_mulVec, Matrix.fromCols_mulVec,
    Function.comp_def, add_comm]

/-- Matrix endpoint of the dirty replay, necessary for the price and boundary laws. -/
theorem dirty_coordinate_replay_matrix {n a : ℕ} (C : LinearDAG n a)
    (G : Matrix (Fin a) (Fin n) ℂ) (hG : ∀ x, C.eval x = G.mulVec x) :
    ∃ W : List (Shear ((Fin n ⊕ Fin C.size) ⊕ Fin a)),
      W.length ≤ 8 * C.size + 2 * a ∧ shearMatrix W = replayMatrix G := by
  obtain ⟨W, hW, hWe⟩ := dirty_coordinate_replay_count C
  refine ⟨W, hW, ?_⟩
  apply Matrix.mulVec_injective
  funext v
  have hv : v = Sum.elim (Sum.elim (fun i => v (.inl (.inl i)))
      (fun i => v (.inl (.inr i)))) (fun i => v (.inr i)) := by
    funext i
    rcases i with (i | i) | i <;> rfl
  rw [hv, ← runShears_eq_mulVec, hWe, replayMatrix_mulVec, hG]

end ExactFourier

namespace ExactFourier
open scoped Kronecker

namespace MatrixPrice

theorem identity_pad (p : MatrixPrice) {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix ι ι ℂ) (hA : IsUnit A) :
    p.value (Matrix.fromBlocks A 0 0 (1 : Matrix κ κ ℂ)) = p.value A := by
  rw [p.directSum A 1 hA isUnit_one, p.one, add_zero]

/-- Diagonal conjugation varies the shear coefficient, including all complex values. -/
theorem shear_two (p : MatrixPrice) (c : ℂ) (hc : c ≠ 0) :
    p.value (Matrix.transvection (1 : Fin 2) 0 c) = 1 := by
  let d : Fin 2 → ℂ := ![1, c]
  let L := Matrix.diagonal d
  let R := Matrix.diagonal (fun i => (d i)⁻¹)
  have hd : ∀ i, d i ≠ 0 := by intro i; fin_cases i <;> simp [d, hc]
  have h : L * Matrix.transvection (1 : Fin 2) 0 (1 : ℂ) * R =
      Matrix.transvection (1 : Fin 2) 0 c := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L, R, d, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection,
        Matrix.single, hc]
  rw [← h, p.monomial _ L R (transvection_isUnit 1 0 (by decide) 1)
    (MonomialMatrix.diagonal d hd)
    (MonomialMatrix.diagonal _ (fun i => inv_ne_zero (hd i))), p.normalized]

/-- Every coordinate shear is a single two-coordinate shear, with literal identity padding. -/
theorem transvection_le_one (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) (c : ℂ) : p.value (Matrix.transvection i j c) ≤ 1 := by
  classical
  by_cases hc : c = 0
  · subst c
    simp
  let κ := {t : ι // t ≠ i ∧ t ≠ j}
  let t : Matrix.TransvectionStruct (Fin 2) ℂ := ⟨1, 0, by decide, c⟩
  let e := pairComplement i j hij
  have he : Matrix.reindex e e (Matrix.fromBlocks t.toMatrix 0 0 (1 : Matrix κ κ ℂ)) =
      Matrix.transvection i j c := by
    rw [← t.toMatrix_sumInl κ]
    exact ((t.sumInl κ).toMatrix_reindexEquiv e).symm
  have ht : IsUnit t.toMatrix := transvection_isUnit 1 0 (by decide) c
  have hpad : IsUnit (Matrix.fromBlocks t.toMatrix 0 0 (1 : Matrix κ κ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨ht, isUnit_one⟩
  rw [← he, p.reindex e _ hpad, p.identity_pad t.toMatrix ht]
  exact le_of_eq (p.shear_two c hc)

theorem transvection_list_isUnit {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι ℂ)) :
    IsUnit (L.map Matrix.TransvectionStruct.toMatrix).prod := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.TransvectionStruct.det_toMatrix_prod]
  exact isUnit_one

/-- Every literal shear in an implementing word is charged. -/
theorem transvection_list_le (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι]
    (L : List (Matrix.TransvectionStruct ι ℂ)) :
    p.value (L.map Matrix.TransvectionStruct.toMatrix).prod ≤ L.length := by
  induction L with
  | nil => simp
  | cons t L ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      have ht := p.transvection_le_one t.i t.j t.hij t.c
      have hm := p.mul_le t.toMatrix (L.map Matrix.TransvectionStruct.toMatrix).prod
        (transvection_isUnit t.i t.j t.hij t.c) (transvection_list_isUnit L)
      calc
        _ ≤ p.value t.toMatrix + p.value (L.map Matrix.TransvectionStruct.toMatrix).prod := hm
        _ ≤ 1 + (L.length : ℝ) := add_le_add ht ih
        _ = (L.length : ℝ) + 1 := add_comm _ _

/-- Inverse symmetry and subadditivity control a relative transformation in both directions. -/
theorem difference_le (p : MatrixPrice) {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (hA : IsUnit A) (hB : IsUnit B) :
    |p.value B - p.value A| ≤ p.value (A⁻¹ * B) := by
  have hAi : IsUnit A⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hA
  have hBi : IsUnit B⁻¹ := (Matrix.isUnit_nonsing_inv_iff).mpr hB
  have hAB : A * (A⁻¹ * B) = B := by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      one_mul]
  have hu : IsUnit (A⁻¹ * B) := hAi.mul hB
  have hb := p.mul_le A (A⁻¹ * B) hA hu
  rw [hAB] at hb
  have ha := p.mul_le B (A⁻¹ * B)⁻¹ hB ((Matrix.isUnit_nonsing_inv_iff).mpr hu)
  have hBA : B * (A⁻¹ * B)⁻¹ = A := by
    nth_rw 1 [← hAB]
    rw [Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hu), mul_one]
  rw [hBA, p.inverse _ hu] at ha
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end MatrixPrice
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PortMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe fourierU1 fourierU2

section

namespace ExactFourier

theorem rectangularShear_unit {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) : IsUnit (rectangularShear G) :=
  Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one, isUnit_one⟩

theorem replayMatrix_reindex {n a k : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    Matrix.reindex replayOrder replayOrder
      (Matrix.fromBlocks (rectangularShear G) 0 0 (1 : Matrix (Fin k) (Fin k) ℂ)) =
      replayMatrix G := by
  ext i j
  rcases i with (i | i) | i <;> rcases j with (j | j) | j <;>
    simp [Matrix.reindex_apply, replayOrder, rectangularShear, replayMatrix,
      Matrix.one_apply]

theorem MatrixPrice.rectangularShear_bound (p : MatrixPrice) {n a : ℕ}
    (C : LinearDAG n a) (G : Matrix (Fin a) (Fin n) ℂ)
    (hG : ∀ x, C.eval x = G.mulVec x) :
    p.value (rectangularShear G) ≤ 8 * (C.size : ℝ) + 2 * a := by
  obtain ⟨W, hW, hWe⟩ := dirty_coordinate_replay_matrix C G hG
  have hu := rectangularShear_unit G
  have hp : IsUnit (Matrix.fromBlocks (rectangularShear G) 0 0
      (1 : Matrix (Fin C.size) (Fin C.size) ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hu, isUnit_one⟩
  have he : p.value (replayMatrix (k := C.size) G) = p.value (rectangularShear G) := by
    rw [← replayMatrix_reindex, p.reindex _ _ hp, p.identity_pad _ hu]
  have h := p.transvection_list_le W.reverse
  rw [List.map_reverse] at h
  change p.value (shearMatrix W) ≤ (W.reverse.length : ℝ) at h
  rw [hWe, he] at h
  simp only [List.length_reverse] at h
  have hn : (W.length : ℝ) ≤ (8 * C.size + 2 * a : ℕ) := by exact_mod_cast hW
  push_cast at hn
  exact h.trans hn

end ExactFourier

namespace ExactFourier

theorem rectangularShear_mul {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G H : Matrix ι κ ℂ) :
    rectangularShear G * rectangularShear H = rectangularShear (G + H) := by
  simp [rectangularShear, Matrix.fromBlocks_multiply, add_comm]

theorem rectangularShear_inv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) :
    (rectangularShear G)⁻¹ = rectangularShear (-G) := by
  apply Matrix.inv_eq_right_inv
  rw [rectangularShear_mul]
  simp [rectangularShear, ← Matrix.fromBlocks_one]

theorem MatrixPrice.rectangularShear_neg (p : MatrixPrice) {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (G : Matrix ι κ ℂ) :
    p.value (rectangularShear (-G)) = p.value (rectangularShear G) := by
  rw [← rectangularShear_inv, p.inverse _ (rectangularShear_unit G)]

theorem lowerShear_reindex {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (G : Matrix κ ι ℂ) :
    Matrix.reindex (Equiv.sumComm κ ι) (Equiv.sumComm κ ι) (rectangularShear G) =
      lowerShear G := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.reindex_apply, rectangularShear, lowerShear]

theorem lowerShear_unit {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (G : Matrix κ ι ℂ) : IsUnit (lowerShear G) :=
  Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one, isUnit_one⟩

theorem MatrixPrice.lowerShear_price (p : MatrixPrice) {ι κ : Type}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (G : Matrix κ ι ℂ) :
    p.value (lowerShear G) = p.value (rectangularShear G) := by
  rw [← lowerShear_reindex, p.reindex _ _ (rectangularShear_unit G)]

theorem signedSwap_monomial {ι : Type*} [DecidableEq ι] :
    MonomialMatrix (Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) (-1) 0) := by
  refine ⟨Equiv.sumComm ι ι, Sum.elim (fun _ => -1) (fun _ => 1), ?_, ?_⟩
  · rintro (i | i) <;> norm_num
  · rintro (i | i) (j | j) <;> simp [Matrix.one_apply, neg_ite]

theorem twoWay_identity {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Matrix ι ι ℂ) (hG : IsUnit G) :
    rectangularShear G * lowerShear (-G⁻¹) * rectangularShear G =
      Matrix.fromBlocks (0 : Matrix ι ι ℂ) G (-G⁻¹) 0 := by
  have hdet := (Matrix.isUnit_iff_isUnit_det G).mp hG
  simp [rectangularShear, lowerShear, Matrix.fromBlocks_multiply,
    Matrix.mul_nonsing_inv G hdet, Matrix.nonsing_inv_mul G hdet]

/-- Necessary pre-corner price bound: both the forward and inverse circuits are charged. -/
theorem MatrixPrice.twoWay_bound (p : MatrixPrice) {ι : Type}
    [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (hG : IsUnit G) :
    2 * p.value G ≤ 2 * p.value (rectangularShear G) + p.value (rectangularShear G⁻¹) := by
  have hi : IsUnit G⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hG
  have hs := rectangularShear_unit G
  have hl := lowerShear_unit (-G⁻¹)
  have h1 := p.mul_le (rectangularShear G) (lowerShear (-G⁻¹)) hs hl
  have h2 := p.mul_le (rectangularShear G * lowerShear (-G⁻¹)) (rectangularShear G)
    (hs.mul hl) hs
  rw [twoWay_identity G hG] at h2
  rw [p.lowerShear_price, p.rectangularShear_neg] at h1
  have hd : IsUnit (Matrix.fromBlocks G 0 0 G⁻¹) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hG, hi⟩
  have he : Matrix.fromBlocks G (0 : Matrix ι ι ℂ) 0 G⁻¹ *
      Matrix.fromBlocks 0 (1 : Matrix ι ι ℂ) (-1) 0 =
      Matrix.fromBlocks (0 : Matrix ι ι ℂ) G (-G⁻¹) 0 := by
    simp [Matrix.fromBlocks_multiply]
  have hp := p.monomial (Matrix.fromBlocks G 0 0 G⁻¹) 1
    (Matrix.fromBlocks (0 : Matrix ι ι ℂ) 1 (-1) 0) hd
    MonomialMatrix.one signedSwap_monomial
  rw [one_mul, he, p.directSum G G⁻¹ hG hi, p.inverse _ hG] at hp
  rw [hp] at h2
  linarith

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.LinearDAG
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

/-- Literal semantics of DAG composition, including preservation of every existing value. -/
theorem Program.eval_append {n m k l : ℕ} (p : Program n k) (q : Program m l)
    (f : Fin (m + 1) → Fin (n + 1 + k)) (x : Fin n → ℂ) (y : Fin m → ℂ)
    (hf : ∀ (i : Fin (m + 1)), p.eval x (f i) = (Fin.snoc y 0 : Fin (m + 1) → ℂ) i) :
    (∀ j, (p.append f q).eval x (keepIndex j) = p.eval x j) ∧
    (∀ i, (p.append f q).eval x (appendIndex f i) = q.eval y i) := by
  induction q with
  | nil =>
      constructor
      · intro j; rfl
      · intro i; simpa [Program.append, Program.eval] using hf i
  | @step l q g ih =>
      constructor
      · intro j
        simp only [Program.append, Program.eval, keepIndex_succ, Fin.snoc_castSucc]
        exact ih.1 j
      · intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · calc
            _ = (p.append f (q.step g)).eval x (Fin.last (n + 1 + (k + l))) :=
              congrArg ((p.append f (q.step g)).eval x) (appendIndex_last f)
            _ = _ := by
              simp only [Program.append, Program.eval, Nat.add_eq, Fin.snoc_last, Gate.eval_map]
              congr 1
              funext j
              exact ih.2 j
        · simp only [appendIndex_castSucc, Program.append, Program.eval, Fin.snoc_castSucc]
          exact ih.2 j

theorem Program.eval_zero {n k : ℕ} (p : Program n k) (x : Fin n → ℂ) :
    p.eval x ⟨n, by omega⟩ = 0 := by
  induction p with
  | nil => exact Fin.snoc_last _ _
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n + 1 + k + 1) → ℂ)
        (Fin.castSucc (⟨n, by omega⟩ : Fin (n + 1 + k))) = 0
      rw [Fin.snoc_castSucc, ih]

theorem LinearDAG.eval_comp {n a b : ℕ} (D : LinearDAG a b) (C : LinearDAG n a)
    (x : Fin n → ℂ) : (D.comp C).eval x = D.eval (C.eval x) := by
  have hf : ∀ (i : Fin (a + 1)), C.program.eval x
      ((Fin.snoc C.outputs (⟨n, by omega⟩ : Fin (n + 1 + C.size)) :
        Fin (a + 1) → Fin (n + 1 + C.size)) i) =
      (Fin.snoc (C.eval x) 0 : Fin (a + 1) → ℂ) i := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using C.program.eval_zero x
    · simp [LinearDAG.eval]
  have he := C.program.eval_append D.program (Fin.snoc C.outputs ⟨n, by omega⟩) x (C.eval x) hf
  funext i
  exact he.2 (D.outputs i)

end ExactFourier

namespace ExactFourier

theorem LinearDAG.eval_layer {n a : ℕ} (g : Fin a → Gate (n + 1))
    (x : Fin n → ℂ) : (LinearDAG.layer g).eval x = fun i => (g i).eval (Fin.snoc x 0) := by
  funext i
  exact (Program.nil.eval_emit g x).2 i

end ExactFourier

namespace ExactFourier

private theorem foldColumns_size {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ)
    (L : List (Fin n)) (C : LinearDAG n a) :
    (L.foldl (fun C j => C.addColumn j (fun i => G i j)) C).size =
      C.size + 2 * a * L.length := by
  induction L generalizing C with
  | nil => simp
  | cons j L ih =>
      rw [List.foldl_cons, ih]
      simp only [LinearDAG.addColumn, List.length_cons]
      ring

@[simp] theorem LinearDAG.size_matrix {n a : ℕ} (G : Matrix (Fin a) (Fin n) ℂ) :
    (LinearDAG.matrix n a G).size = 2 * a * n := by
  simp [LinearDAG.matrix, foldColumns_size, LinearDAG.wires]

end ExactFourier

namespace ExactFourier

/-- Quantitative version of the two-way pre-corner argument, with no hidden inverse
oracle: `D` is an actual charged DAG computing the inverse map. -/
theorem MatrixPrice.twoWay_DAG_bound (p : MatrixPrice) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G) (C D : LinearDAG n n)
    (hC : ∀ x, C.eval x = G.mulVec x) (hD : ∀ x, D.eval x = G⁻¹.mulVec x) :
    p.value G ≤ 8 * C.size + 4 * D.size + 3 * n := by
  have h := p.twoWay_bound G hG
  have h1 := p.rectangularShear_bound C G hC
  have h2 := p.rectangularShear_bound D G⁻¹ hD
  linarith

end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.TensorTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Exact finite tensor and disjoint-block constructions for the triangular
monotonicity experiment in 05-corners:130–201. -/
namespace ExactFourier
open scoped Kronecker BigOperators
namespace TensorTools

variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq τ]

 theorem pad_middle
    {ι : Type} {κ : Type} {τ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] (A : Matrix ι ι ℂ) (E : Matrix ι κ ℂ) (Y : Matrix κ κ ℂ) :
    Matrix.reindex (middleEquiv (τ := τ)) middleEquiv
      (Matrix.fromBlocks (Matrix.fromBlocks A E 0 Y) 0 0 (1 : Matrix τ τ ℂ)) =
    Matrix.fromBlocks (Matrix.fromBlocks A 0 0 (1 : Matrix τ τ ℂ))
      (Matrix.fromRows E 0) 0 Y := by
  ext i j
  rcases i with (i|t)|k <;> rcases j with (j|t')|k' <;>
    simp [Matrix.reindex_apply, middleEquiv, Matrix.fromBlocks, Matrix.fromRows, Sum.elim, Matrix.one_apply]

 theorem pad_front
    {ι : Type} {κ : Type} {τ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] (B : Matrix τ τ ℂ) (F : Matrix τ κ ℂ) (Z : Matrix κ κ ℂ) :
    Matrix.reindex (Equiv.sumAssoc ι τ κ).symm (Equiv.sumAssoc ι τ κ).symm
      (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (Matrix.fromBlocks B F 0 Z)) =
    Matrix.fromBlocks (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 B)
      (Matrix.fromRows 0 F) 0 Z := by
  ext i j
  rcases i with (i|t)|k <;> rcases j with (j|t')|k' <;>
    simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.fromRows, Sum.elim, Matrix.one_apply]

 theorem join_mul
    {ι : Type} {κ : Type} {τ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] (A : Matrix ι ι ℂ) (B : Matrix τ τ ℂ)
    (E : Matrix ι κ ℂ) (F : Matrix τ κ ℂ) (Y Z : Matrix κ κ ℂ) :
    Matrix.fromBlocks (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 B)
        (Matrix.fromRows 0 F) 0 Z *
      Matrix.fromBlocks (Matrix.fromBlocks A 0 0 (1 : Matrix τ τ ℂ))
        (Matrix.fromRows E 0) 0 Y =
    Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B)
      (Matrix.fromRows E (F * Y)) 0 (Z * Y) := by
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext i j
  rcases i with i|t <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.fromRows, Sum.elim, Matrix.one_apply]

theorem price_join (p : MatrixPrice) (A : Matrix ι ι ℂ) (B : Matrix τ τ ℂ)
    (E : Matrix ι κ ℂ) (F : Matrix τ κ ℂ) (Y Z : Matrix κ κ ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (hY : IsUnit Y) (hZ : IsUnit Z) :
    p.value (Matrix.fromBlocks (Matrix.fromBlocks A 0 0 B)
      (Matrix.fromRows E (F * Y)) 0 (Z * Y)) ≤
      p.value (Matrix.fromBlocks A E 0 Y) + p.value (Matrix.fromBlocks B F 0 Z) := by
  have hT : IsUnit (Matrix.fromBlocks A E 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hA,hY⟩
  have hU : IsUnit (Matrix.fromBlocks B F 0 Z) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hB,hZ⟩
  have hT' : IsUnit (Matrix.fromBlocks (Matrix.fromBlocks A E 0 Y) 0 0 (1 : Matrix τ τ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hT,isUnit_one⟩
  have hU' : IsUnit (Matrix.fromBlocks (1 : Matrix ι ι ℂ) 0 0 (Matrix.fromBlocks B F 0 Z)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hU⟩
  rw [← join_mul, ← pad_middle, ← pad_front]
  calc
    _ ≤ _ := p.mul_le _ _ (unit_reindex _ _ hU') (unit_reindex _ _ hT')
    _ = _ := by rw [p.reindex _ _ hU', p.reindex _ _ hT',
      p.directSum _ _ isUnit_one hU, p.identity_pad _ hT, p.one]; ring

end TensorTools
end ExactFourier

end

section
/-! Two cell programs sharing only their persistent state space. Unlike the
triangular experiment, no invertibility of the state block is assumed. -/
namespace ExactFourier
open TensorTools
namespace CellJoin
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem join_eq
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ) :
    join X Y =
    Matrix.reindex (Equiv.sumAssoc α γ β).symm (Equiv.sumAssoc α γ β).symm
        (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 Y) *
      Matrix.reindex (middleEquiv (ι := α) (κ := β) (τ := γ)) middleEquiv
        (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) := by
  have hX : Matrix.reindex (middleEquiv (ι := α) (κ := β) (τ := γ)) middleEquiv
      (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) =
      Matrix.fromBlocks (Matrix.fromBlocks X.toBlocks₁₁ 0 0 1)
        (Matrix.fromRows X.toBlocks₁₂ 0) (Matrix.fromCols X.toBlocks₂₁ 0) X.toBlocks₂₂ := by
    ext i j
    rcases i with (a|c)|b <;> rcases j with (a'|c')|b' <;>
      simp [Matrix.reindex_apply, middleEquiv, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  have hY : Matrix.reindex (Equiv.sumAssoc α γ β).symm (Equiv.sumAssoc α γ β).symm
        (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 Y) =
      Matrix.fromBlocks (Matrix.fromBlocks 1 0 0 Y.toBlocks₁₁)
        (Matrix.fromRows 0 Y.toBlocks₁₂) (Matrix.fromCols 0 Y.toBlocks₂₁) Y.toBlocks₂₂ := by
    ext i j
    rcases i with (a|c)|b <;> rcases j with (a'|c')|b' <;>
      simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [hX,hY]
  simp only [join, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with (a|c)|b <;> rcases j with (a'|c')|b' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.fromRows, Matrix.fromCols, Sum.elim, Matrix.one_apply]

theorem unit (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) : IsUnit (join X Y) := by
  rw [join_eq]
  exact (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hY⟩)).mul
    (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩))

theorem price (p : MatrixPrice) (X : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (Y : Matrix (γ ⊕ β) (γ ⊕ β) ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    p.value (join X Y) ≤ p.value X + p.value Y := by
  have hX' : IsUnit (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩
  have hY' : IsUnit (Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨isUnit_one,hY⟩
  rw [join_eq]
  calc
    _ ≤ _ := p.mul_le _ _ (unit_reindex _ _ hY') (unit_reindex _ _ hX')
    _ = _ := by rw [p.reindex _ _ hY',p.reindex _ _ hX',
      p.directSum _ _ isUnit_one hY,p.identity_pad _ hX,p.one]; ring

end CellJoin
end ExactFourier

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools

variable {α β σ κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ]

 theorem lift_identity
    {α : Type} {β : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ] (M : Matrix α α ℂ) (E : Matrix (σ × α) κ ℂ)
    (Y : Matrix κ κ ℂ) :
    Matrix.reindex liftEquiv liftEquiv
      (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y ⊗ₖ (1 : Matrix β β ℂ)) =
    Matrix.fromBlocks ((1 : Matrix (σ × β) (σ × β) ℂ) ⊗ₖ M) (oldE E) 0
      (Y ⊗ₖ (1 : Matrix β β ℂ)) := by
   ext i j
   rcases i with ⟨⟨s,b⟩,a⟩|⟨i,b⟩ <;> rcases j with ⟨⟨s',b'⟩,a'⟩|⟨j,b'⟩ <;>
     simp [Matrix.reindex_apply, liftEquiv, swapLast, Matrix.kroneckerMap_apply,
       Matrix.fromBlocks, oldE, Matrix.one_apply, mul_comm,        Prod.mk.injEq, and_comm]
   split_ifs <;> simp_all

 theorem new_identity
    {α : Type} {β : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq κ] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    Matrix.reindex (Equiv.prodSumDistrib κ α β) (Equiv.prodSumDistrib κ α β)
      ((1 : Matrix κ κ ℂ) ⊗ₖ Matrix.fromBlocks M C 0 D) =
    Matrix.fromBlocks ((1 : Matrix κ κ ℂ) ⊗ₖ M) ((1 : Matrix κ κ ℂ) ⊗ₖ C) 0
      ((1 : Matrix κ κ ℂ) ⊗ₖ D) := by
  ext i j
  rcases i with ⟨i,a⟩|⟨i,b⟩ <;> rcases j with ⟨j,a'⟩|⟨j,b'⟩ <;>
    simp [Matrix.reindex_apply, Matrix.kroneckerMap_apply, Matrix.fromBlocks]

 theorem merge_identity
    {α : Type} {β : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ] (M : Matrix α α ℂ) (C : Matrix α β ℂ) (D : Matrix β β ℂ)
    (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ) :
    Matrix.reindex mergeEquiv mergeEquiv
      (Matrix.fromBlocks
        (Matrix.fromBlocks ((1 : Matrix (σ × β) (σ × β) ℂ) ⊗ₖ M) 0 0
          ((1 : Matrix κ κ ℂ) ⊗ₖ M))
        (Matrix.fromRows (oldE E) (((1 : Matrix κ κ ℂ) ⊗ₖ C) *
          (Y ⊗ₖ (1 : Matrix β β ℂ)))) 0
        (((1 : Matrix κ κ ℂ) ⊗ₖ D) * (Y ⊗ₖ (1 : Matrix β β ℂ)))) =
    Matrix.fromBlocks ((1 : Matrix ((σ × β) ⊕ κ) ((σ × β) ⊕ κ) ℂ) ⊗ₖ M)
      (nextE E Y C) 0 (Y ⊗ₖ D) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with ⟨s|k,a⟩|⟨i,b⟩ <;> rcases j with ⟨s'|k',a'⟩|⟨j,b'⟩ <;>
    simp [Matrix.reindex_apply, mergeEquiv, Matrix.kroneckerMap_apply,
      Matrix.fromBlocks, Matrix.fromRows, Sum.elim, oldE, nextE, Matrix.one_apply]

 theorem next_price (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ)
    (hM : IsUnit M) (hD : IsUnit D) (hY : IsUnit Y) :
    p.value (Matrix.fromBlocks ((1 : Matrix ((σ × β) ⊕ κ) ((σ × β) ⊕ κ) ℂ) ⊗ₖ M)
       (nextE E Y C) 0 (Y ⊗ₖ D)) ≤
      Fintype.card β * p.value (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) +
      Fintype.card κ * p.value (Matrix.fromBlocks M C 0 D) := by
  have hT : IsUnit (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ isUnit_one hM,hY⟩
  have hK : IsUnit (Matrix.fromBlocks M C 0 D) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,hD⟩
  have hh := price_join p ((1 : Matrix (σ × β) (σ × β) ℂ) ⊗ₖ M)
    ((1 : Matrix κ κ ℂ) ⊗ₖ M) (oldE E) ((1 : Matrix κ κ ℂ) ⊗ₖ C)
    (Y ⊗ₖ (1 : Matrix β β ℂ)) ((1 : Matrix κ κ ℂ) ⊗ₖ D)
    (unit_tensor _ _ isUnit_one hM) (unit_tensor _ _ isUnit_one hM)
    (unit_tensor _ _ hY isUnit_one) (unit_tensor _ _ isUnit_one hD)
  rw [← lift_identity, ← new_identity] at hh
  rw [p.reindex _ _ (unit_tensor _ _ hT isUnit_one),
    p.reindex _ _ (unit_tensor _ _ isUnit_one hK),
    p.tensor _ _ hT isUnit_one, p.tensor _ _ isUnit_one hK, p.one, p.one] at hh
  simp only [mul_zero, add_zero, zero_add] at hh
  rw [← merge_identity, p.reindex]
  · exact hh
  · apply Matrix.isUnit_fromBlocks_zero₂₁.mpr
    constructor
    · exact Matrix.isUnit_fromBlocks_zero₂₁.mpr
        ⟨unit_tensor _ _ isUnit_one hM, unit_tensor _ _ isUnit_one hM⟩
    · exact (unit_tensor _ _ isUnit_one hD).mul (unit_tensor _ _ hY isUnit_one)

end ExactFourier.Triangular

end

section
/-! Whole-row-block compression used in the proof of triangular monotonicity
(05-corners.tex:145–209). Only the block-copy index is changed; individual rows
of a spatial block are never independently mixed. -/
namespace ExactFourier.RowCompression
open scoped BigOperators

section Splitting
variable {K E F : Type*} [Field K] [AddCommGroup E] [Module K E]
  [AddCommGroup F] [Module K F]

/-- Two surjections from the same finite-dimensional domain differ by an
invertible change of domain. This is the block-copy coordinate change V. -/
theorem surjective_equiv [FiniteDimensional K E] (f g : E →ₗ[K] F)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    ∃ e : E ≃ₗ[K] E, ∀ x, f (e x) = g x := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf)
  obtain ⟨t, ht⟩ := g.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hg)
  have hd : Module.finrank K (LinearMap.ker g) = Module.finrank K (LinearMap.ker f) := by
    have h1 := f.finrank_range_add_finrank_ker
    have h2 := g.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hf] at h1
    rw [LinearMap.range_eq_top.mpr hg] at h2
    omega
  let a : LinearMap.ker g ≃ₗ[K] LinearMap.ker f := LinearEquiv.ofFinrankEq _ _ hd
  let e := (splitEquiv g t ht).trans
    ((LinearEquiv.prodCongr (LinearEquiv.refl K F) a).trans (splitEquiv f s hs).symm)
  refine ⟨e, ?_⟩
  intro x
  have h := congrArg Prod.fst ((splitEquiv f s hs).apply_symm_apply
    (g x, a (splitEquiv g t ht x).2))
  exact h

/-- Equality of row spaces, not an assumption of full row rank, suffices. -/
theorem range_equiv [FiniteDimensional K E] (f g : E →ₗ[K] F)
    (hfg : LinearMap.range f = LinearMap.range g) :
    ∃ e : E ≃ₗ[K] E, ∀ x, f (e x) = g x := by
  let g' : E →ₗ[K] LinearMap.range f := g.codRestrict (LinearMap.range f)
    (by intro x; rw [hfg]; exact LinearMap.mem_range_self g x)
  have hg' : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    rw [hfg] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  obtain ⟨e, he⟩ := surjective_equiv f.rangeRestrict g'
    (LinearMap.range_eq_top.mp f.range_rangeRestrict) hg'
  exact ⟨e, fun x => congrArg Subtype.val (he x)⟩

end Splitting
section Matrices
variable {K α β : Type*} [Field K] [Fintype α] [DecidableEq α]

/-- The row-space equivalence as an actual invertible left multiplier. -/
theorem matrix_row_equiv (R S : Matrix α β K)
    (hRS : Submodule.span K (Set.range R) = Submodule.span K (Set.range S)) :
    ∃ V : Matrix α α K, IsUnit V ∧ V * R = S := by
  obtain ⟨e, he⟩ := range_equiv R.vecMulLinear S.vecMulLinear
    (by simpa only [range_vecMulLinear, Matrix.row] using hRS)
  let V := e.toLinearMap.toMatrixRight'
  let W := e.symm.toLinearMap.toMatrixRight'
  have hVW : V * W = 1 := by
    rw [← LinearMap.toMatrixRight'_comp]
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext x; simp
    rw [h, LinearMap.toMatrixRight'_id]
  have hWV : W * V = 1 := by
    rw [← LinearMap.toMatrixRight'_comp]
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext x; simp
    rw [h, LinearMap.toMatrixRight'_id]
  refine ⟨V, ⟨⟨V, W, hVW, hWV⟩, rfl⟩, ?_⟩
  apply Matrix.toLinearMapRight'.injective
  rw [Matrix.toLinearMapRight'_mul]
  change R.vecMulLinear.comp (LinearMap.toMatrixRight'.symm
      (LinearMap.toMatrixRight' e.toLinearMap)) = S.vecMulLinear
  rw [LinearEquiv.symm_apply_apply]
  exact LinearMap.ext he

/-- Select a sparse spanning-family basis and perform the invertible compression
on the *whole* row-block index. At most dim(β → K) rows remain. -/
theorem sparse_row_compression {γ : Type*} [Fintype β] (R : Matrix α β K)
    (Q : γ → β → K)
    (hspan : Submodule.span K (Set.range R) = Submodule.span K (Set.range Q)) :
    ∃ V : Matrix α α K, IsUnit V ∧ ∃ I : Finset α,
      I.card ≤ Fintype.card β ∧
      (∀ i, i ∉ I → (V*R) i = 0) ∧
      (∀ i ∈ I, ∃ g, (V*R) i = Q g) := by
  classical
  obtain ⟨t, htQ, htcard, htspan, hti⟩ :=
    Submodule.exists_finset_span_eq_linearIndepOn K (Set.range Q)
  have hta : Fintype.card t ≤ Fintype.card α := by
    rw [Fintype.card_coe, htcard, ← hspan]
    exact finrank_range_le_card R
  have htb : t.card ≤ Fintype.card β := by
    rw [htcard]
    simpa using (Submodule.finrank_le (Submodule.span K (Set.range Q)))
  let e : t ↪ α := Classical.choice (Function.Embedding.nonempty_of_card_le hta)
  let S : Matrix α β K := fun i => if h : ∃ b : t, e b = i then (h.choose : β → K) else 0
  have hSe (b : t) : S (e b) = b := by
    dsimp only [S]
    have hb : ∃ c : t, e c = e b := ⟨b,rfl⟩
    rw [dite_eq_left hb]
    exact congrArg Subtype.val (e.injective hb.choose_spec)
  have hspanS : Submodule.span K (Set.range S) = Submodule.span K (t : Set (β → K)) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i,rfl⟩
      dsimp only [S]
      split_ifs with hi
      · exact Submodule.subset_span hi.choose.property
      · exact Submodule.zero_mem _
    · apply Submodule.span_le.mpr
      intro b hb
      exact Submodule.subset_span ⟨e ⟨b,hb⟩, hSe ⟨b,hb⟩⟩
  have hRS : Submodule.span K (Set.range R) = Submodule.span K (Set.range S) := by
    rw [hspanS, htspan, hspan]
  obtain ⟨V,hV,hVS⟩ := matrix_row_equiv R S hRS
  let I := Finset.univ.map e
  refine ⟨V,hV,I, ?_, ?_, ?_⟩
  · simpa [I] using htb
  · intro i hi
    rw [hVS]

    dsimp [S]
    apply dite_eq_right
    simpa [I] using hi
  · intro i hi
    obtain ⟨b, _, rfl⟩ := Finset.mem_map.mp hi
    have hbQ := htQ b.property
    obtain ⟨g,hg⟩ := hbQ
    refine ⟨g, ?_⟩
    rw [hVS, hSe, hg]

end Matrices
end ExactFourier.RowCompression

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SparseShear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Sparse whole-block cancellations in triangular monotonicity. -/
namespace ExactFourier
open scoped BigOperators

namespace MatrixPrice
variable (p : MatrixPrice)
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem rectangularShear_add_le (G H : Matrix ι κ ℂ) :
    p.value (rectangularShear (G+H)) ≤
      p.value (rectangularShear G) + p.value (rectangularShear H) := by
  rw [← rectangularShear_mul]
  exact p.mul_le _ _ (rectangularShear_unit G) (rectangularShear_unit H)

theorem rectangularShear_single
    {ι : Type} {κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (i : ι) (j : κ) (c : ℂ) :
    rectangularShear (Matrix.single i j c) =
      Matrix.transvection (Sum.inl i) (Sum.inr j) c := by
  ext a b
  cases a <;> cases b <;>
    simp [rectangularShear, Matrix.transvection, Matrix.single, Matrix.one_apply]

theorem rectangularShear_sum_le {α : Type*} (s : Finset α) (G : α → Matrix ι κ ℂ) :
    p.value (rectangularShear (∑ i ∈ s, G i)) ≤
      ∑ i ∈ s, p.value (rectangularShear (G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rectangularShear]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (p.rectangularShear_add_le (G a) (∑ i ∈ s, G i)).trans (add_le_add le_rfl ih)

/-- A rectangular shear costs at most one per nonzero matrix entry. -/
theorem rectangularShear_sparse (G : Matrix ι κ ℂ) :
    p.value (rectangularShear G) ≤
      ((Finset.univ.filter fun ij : ι × κ => G ij.1 ij.2 ≠ 0).card : ℝ) := by
  classical
  let S := Finset.univ.filter fun ij : ι × κ => G ij.1 ij.2 ≠ 0
  have hsum : (∑ ij ∈ S, Matrix.single ij.1 ij.2 (G ij.1 ij.2)) = G := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.single_apply]
    rw [Finset.sum_eq_single (i,j)]
    · simp
    · intro b hb hne
      by_cases hi : i=b.1
      · have hj : j≠b.2 := by intro hj; exact hne (Prod.ext hi.symm hj.symm)
        simp [hj, eq_comm]
      · simp [hi, eq_comm]
    · intro hn
      have hz : G i j = 0 := by simpa [S] using hn
      simp [hz]
  calc
    p.value (rectangularShear G) = p.value (rectangularShear (∑ ij ∈ S, Matrix.single ij.1 ij.2 (G ij.1 ij.2))) := by rw [hsum]
    _ ≤ ∑ ij ∈ S, p.value (rectangularShear (Matrix.single ij.1 ij.2 (G ij.1 ij.2))) :=
      p.rectangularShear_sum_le S _
    _ ≤ ∑ _ij ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro ij hij
      rw [rectangularShear_single]
      exact p.transvection_le_one _ _ (by simp) _
    _ = _ := by simp [S]

end MatrixPrice
end ExactFourier

end

section
/-! Normalized whole-row-block tensor recursion and its sparse generators.
The change of basis acts only on the call index, as in corner:eq:actual-row-block. -/
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools
variable {α β σ κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ]

theorem liftRows_mul
    {α : Type} {β : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ] (V : Matrix σ σ ℂ) (B : Matrix β β ℂ)
    (R : Matrix σ (α × κ) ℂ) (H : Matrix β β ℂ) :
    (V ⊗ₖ B) * liftRows R H = liftRows (V * R) (B * H) := by
  ext i j
  change (∑ x : σ × β, (V i.1 x.1 * B i.2 x.2) *
    (R x.1 (j.1,j.2.1) * H x.2 j.2.2)) =
    (∑ s, V i.1 s * R s (j.1,j.2.1)) * (∑ b, B i.2 b * H b j.2.2)
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem nextRows_change (V : Matrix σ σ ℂ) (D : Matrix β β ℂ)
    (R : Matrix σ (α × κ) ℂ) (T : Matrix α β ℂ) (hD : IsUnit D) :
    Matrix.fromBlocks (V ⊗ₖ D) 0 0 (1 : Matrix κ κ ℂ) * nextRows R T D⁻¹ =
      nextRows (V * R) T 1 := by
  simp only [nextRows, Matrix.fromBlocks_mul_fromRows, Matrix.zero_mul, Matrix.one_mul,
    add_zero, zero_add, liftRows_mul,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det D).mp hD)]

theorem flat_next_normalized
    {α : Type} {β : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ] (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ)
    (C : Matrix α β ℂ) (D : Matrix β β ℂ) (hY : IsUnit Y) :
    flat (nextE E Y C * (Y ⊗ₖ D)⁻¹) =
      nextRows (flat (E * Y⁻¹)) (C * D⁻¹) D⁻¹ := by
  rw [Matrix.inv_kronecker]
  ext i j
  rcases i with ⟨s,b⟩|i
  · change (∑ x : κ × β, (E (s,j.1) x.1 * (1 : Matrix β β ℂ) b x.2) *
          (Y⁻¹ x.1 j.2.1 * D⁻¹ x.2 j.2.2)) =
        (∑ x : κ, E (s,j.1) x * Y⁻¹ x j.2.1) * D⁻¹ b j.2.2
    simp [Fintype.sum_prod_type, Matrix.one_apply, ← mul_assoc, Finset.sum_mul]
  · change ∑ x : κ × β, (Y i x.1 * C j.1 x.2) * (Y⁻¹ x.1 j.2.1 * D⁻¹ x.2 j.2.2) = _
    have hh : (Y ⊗ₖ C) * (Y⁻¹ ⊗ₖ D⁻¹) = (1 : Matrix κ κ ℂ) ⊗ₖ (C * D⁻¹) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det Y).mp hY)]
    exact congrFun (congrFun hh (i,j.1)) j.2

/-- Ordinary matrix row spaces are unchanged by an invertible row multiplier. -/
theorem span_rows_unit_mul {δ : Type} (V : Matrix σ σ ℂ) (R : Matrix σ δ ℂ)
    (hV : IsUnit V) :
    Submodule.span ℂ (Set.range (V * R)) = Submodule.span ℂ (Set.range R) := by
  have le_mul (W : Matrix σ σ ℂ) (S : Matrix σ δ ℂ) :
      Submodule.span ℂ (Set.range (W * S)) ≤ Submodule.span ℂ (Set.range S) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hh : (W * S) i = ∑ j, W i j • S j := by ext j; simp [Matrix.mul_apply]
    rw [hh]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  apply le_antisymm (le_mul V R)
  have hh := le_mul V⁻¹ (V * R)
  rwa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det V).mp hV),
    Matrix.one_mul] at hh

theorem nnz_lift_one
    {α : Type} {β : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq σ] [DecidableEq κ] (Q : Matrix σ (α × κ) ℂ) (s : σ) (b : β) :
    nnz (liftRows Q (1 : Matrix β β ℂ) (s,b)) ≤ nnz (Q s) := by
  classical
  apply Finset.card_le_card_of_injOn (fun j : α × (κ × β) => (j.1,j.2.1))
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact (mul_ne_zero_iff.mp hj).1
  · intro j hj l hl h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hl
    have hjb : j.2.2 = b := by
      have hn : (1 : Matrix β β ℂ) b j.2.2 ≠ 0 := (mul_ne_zero_iff.mp hj).2
      simpa [Matrix.one_apply, eq_comm] using hn
    have hlb : l.2.2 = b := by
      have hn : (1 : Matrix β β ℂ) b l.2.2 ≠ 0 := (mul_ne_zero_iff.mp hl).2
      simpa [Matrix.one_apply, eq_comm] using hn
    exact Prod.ext (congrArg (fun z : α × κ => z.1) h) (Prod.ext (congrArg (fun z : α × κ => z.2) h) (hjb.trans hlb.symm))

theorem nnz_fresh
    {α : Type} {β : Type} {κ : Type} [Fintype α] [Fintype β] [Fintype κ] [DecidableEq α] [DecidableEq β] [DecidableEq κ] (T : Matrix α β ℂ) (i : κ) :
    nnz (freshRows T i) ≤ Fintype.card α * Fintype.card β := by
  classical
  rw [← Fintype.card_prod]
  apply Finset.card_le_card_of_injOn (t := Finset.univ) (fun j : α × (κ × β) => (j.1,j.2.2))
  · intro j hj; exact Finset.mem_univ _
  · intro j hj l hl h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hj hl
    have hji : j.2.1 = i := by
      have hn : (1 : Matrix κ κ ℂ) i j.2.1 ≠ 0 := (mul_ne_zero_iff.mp hj).1
      simpa [Matrix.one_apply, eq_comm] using hn
    have hli : l.2.1 = i := by
      have hn : (1 : Matrix κ κ ℂ) i l.2.1 ≠ 0 := (mul_ne_zero_iff.mp hl).1
      simpa [Matrix.one_apply, eq_comm] using hn
    exact Prod.ext (congrArg (fun z : α × β => z.1) h) (Prod.ext (hji.trans hli.symm) (congrArg (fun z : α × β => z.2) h))

theorem nnz_nextRows (Q : Matrix σ (α × κ) ℂ) (T : Matrix α β ℂ)
    (hQ : ∀ s, nnz (Q s) ≤ Fintype.card α * Fintype.card β) :
    ∀ s, nnz (nextRows Q T (1 : Matrix β β ℂ) s) ≤ Fintype.card α * Fintype.card β := by
  rintro (⟨s,b⟩|i)
  · exact (nnz_lift_one Q s b).trans (hQ s)
  · exact nnz_fresh T i

end ExactFourier.Triangular

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem tensorPower_unit (D : Matrix β β ℂ) (hD : IsUnit D) (k : ℕ) :
    IsUnit (tensorPower D k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact unit_tensor _ _ ih hD

theorem rowBasis_unit (D : Matrix β β ℂ) (hD : IsUnit D) (k : ℕ) :
    IsUnit (rowBasis D k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih => exact Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ ih hD,isUnit_one⟩

theorem rowBasis_normalizes (C : Matrix α β ℂ) (D : Matrix β β ℂ)
    (hD : IsUnit D) (k : ℕ) :
    rowBasis D k * flat (contamination C D k * (tensorPower D k)⁻¹) = generators C D k := by
  induction k with
  | zero => ext i j; exact PEmpty.elim i
  | succ k ih =>
    change Matrix.fromBlocks (rowBasis D k ⊗ₖ D) 0 0 1 *
      flat (nextE (contamination C D k) (tensorPower D k) C * (tensorPower D k ⊗ₖ D)⁻¹) = _
    rw [flat_next_normalized _ _ _ _ (tensorPower_unit D hD k), nextRows_change _ _ _ _ hD, ih]
    rfl

theorem generators_sparse (C : Matrix α β ℂ) (D : Matrix β β ℂ) (k : ℕ) :
    ∀ i, nnz (generators C D k i) ≤ Fintype.card α * Fintype.card β := by
  induction k with
  | zero => intro i; exact PEmpty.elim i
  | succ k ih => exact nnz_nextRows _ _ ih

theorem tensorPower_price (p : MatrixPrice) (D : Matrix β β ℂ) (hD : IsUnit D) (k : ℕ) :
    p.value (tensorPower D k) = Fintype.card (Calls β k) * p.value D := by
  induction k with
  | zero => simp [tensorPower]
  | succ k ih =>
    rw [tensorPower, p.tensor _ _ (tensorPower_unit D hD k) hD, ih, calls_card_succ]
    push_cast
    ring

theorem experiment_price (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) (k : ℕ) :
    p.value (Matrix.fromBlocks ((1 : Matrix (Calls β k) (Calls β k) ℂ) ⊗ₖ M)
      (contamination C D k) 0 (tensorPower D k)) ≤
      Fintype.card (Calls β k) * p.value (Matrix.fromBlocks M C 0 D) := by
  induction k with
  | zero =>
    have h : ((1 : Matrix (Calls β 0) (Calls β 0) ℂ) ⊗ₖ M) = 1 := by
      ext i j; exact PEmpty.elim i.1
    simp only [contamination, tensorPower, h]
    rw [p.directSum _ _ isUnit_one isUnit_one, p.one, p.one]
    norm_num
  | succ k ih =>
    calc
      _ ≤ Fintype.card β * p.value (Matrix.fromBlocks ((1 : Matrix (Calls β k) (Calls β k) ℂ) ⊗ₖ M)
            (contamination C D k) 0 (tensorPower D k)) +
          Fintype.card (Bottom β k) * p.value (Matrix.fromBlocks M C 0 D) :=
        next_price p M C D _ _ hM hD (tensorPower_unit D hD k)
      _ ≤ Fintype.card β * (Fintype.card (Calls β k) * p.value (Matrix.fromBlocks M C 0 D)) +
          Fintype.card (Bottom β k) * p.value (Matrix.fromBlocks M C 0 D) :=
        add_le_add (mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)) le_rfl
      _ = _ := by rw [calls_card_succ]; push_cast; ring

end ExactFourier.Triangular

end

section
namespace ExactFourier.Triangular
open scoped Kronecker BigOperators
open TensorTools
variable {α σ κ : Type} [Fintype α] [Fintype σ] [Fintype κ]
  [DecidableEq α] [DecidableEq σ] [DecidableEq κ]

theorem flat_left
    {α : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq σ] [DecidableEq κ] (V : Matrix σ σ ℂ) (E : Matrix (σ × α) κ ℂ) :
    flat ((V ⊗ₖ (1 : Matrix α α ℂ)) * E) = V * flat E := by
  ext s j
  simp [flat, Matrix.mul_apply, Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Matrix.one_apply]

theorem nnz_flat
    {α : Type} {σ : Type} {κ : Type} [Fintype α] [Fintype σ] [Fintype κ] [DecidableEq α] [DecidableEq σ] [DecidableEq κ] (E : Matrix (σ × α) κ ℂ) :
    nnz (fun ij : (σ × α) × κ => E ij.1 ij.2) = ∑ s, nnz (flat E s) := by
  change nnz (fun ij : (σ × α) × κ => E ij.1 ij.2) =
    ∑ s, nnz (fun j : α × κ => E (s,j.1) j.2)
  change (σ × α) → κ → ℂ at E
  simp only [nnz, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

theorem nnz_selected_le
    {σ : Type} [Fintype σ] [DecidableEq σ] {δ : Type} [Fintype δ] (R : Matrix σ δ ℂ)
    (I : Finset σ) (B : ℕ) (hzero : ∀ i, i ∉ I → R i = 0)
    (hB : ∀ i ∈ I, nnz (R i) ≤ B) :
    ∑ i, nnz (R i) ≤ I.card * B := by
  classical
  calc
    _ = ∑ i ∈ I, nnz (R i) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ I)
      intro i hi hn
      simp [hzero i hn, nnz]
    _ ≤ ∑ _i ∈ I, B := Finset.sum_le_sum hB
    _ = _ := by simp

theorem cancellation_identity (M : Matrix α α ℂ) (E : Matrix (σ × α) κ ℂ)
    (Y : Matrix κ κ ℂ) (V : Matrix σ σ ℂ) (hY : IsUnit Y) :
    rectangularShear (-((V ⊗ₖ (1 : Matrix α α ℂ)) * (E * Y⁻¹))) *
      Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ) *
      Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y =
      Matrix.fromBlocks (V ⊗ₖ M) 0 0 Y := by
  simp only [rectangularShear, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  rw [Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det Y).mp hY), Matrix.mul_one]
  exact add_neg_cancel _

theorem compressed_price (p : MatrixPrice) (M : Matrix α α ℂ)
    (E : Matrix (σ × α) κ ℂ) (Y : Matrix κ κ ℂ)
    (hM : IsUnit M) (hY : IsUnit Y) {γ : Type} (Q : γ → α × κ → ℂ)
    (hspan : Submodule.span ℂ (Set.range (flat (E * Y⁻¹))) = Submodule.span ℂ (Set.range Q))
    (B : ℕ) (hQ : ∀ g, nnz (Q g) ≤ B) :
    Fintype.card σ * p.value M + p.value Y ≤
      p.value (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) +
      (Fintype.card α * Fintype.card κ : ℝ) * B := by
  obtain ⟨V,hV,I,hI,hzero,hbasis⟩ := RowCompression.sparse_row_compression
    (flat (E * Y⁻¹)) Q hspan
  let G := (V ⊗ₖ (1 : Matrix α α ℂ)) * (E * Y⁻¹)
  have hGn : nnz (fun ij : (σ × α) × κ => G ij.1 ij.2) ≤ I.card * B := by
    rw [nnz_flat, flat_left]
    apply nnz_selected_le _ I B hzero
    intro i hi
    obtain ⟨g,hg⟩ := hbasis i hi
    rw [hg]
    exact hQ g
  have hG : p.value (rectangularShear G) ≤
      (Fintype.card α * Fintype.card κ : ℝ) * B := by
    have hh := p.rectangularShear_sparse G
    change p.value (rectangularShear G) ≤ (nnz (fun ij : (σ × α) × κ => G ij.1 ij.2) : ℝ) at hh
    have hc : nnz (fun ij : (σ × α) × κ => G ij.1 ij.2) ≤
        (Fintype.card α * Fintype.card κ) * B :=
      hGn.trans (Nat.mul_le_mul_right B (by simpa using hI))
    exact hh.trans (by exact_mod_cast hc)
  have hL : IsUnit (Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ hV isUnit_one,isUnit_one⟩
  have hT : IsUnit (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨unit_tensor _ _ isUnit_one hM,hY⟩
  have hh := p.mul_le
    (rectangularShear (-G) * Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ))
    (Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y)
    ((rectangularShear_unit _).mul hL) hT
  have hl := p.mul_le (rectangularShear (-G))
    (Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ))
    (rectangularShear_unit _) hL
  rw [show rectangularShear (-G) *
      Matrix.fromBlocks (V ⊗ₖ (1 : Matrix α α ℂ)) 0 0 (1 : Matrix κ κ ℂ) *
      Matrix.fromBlocks ((1 : Matrix σ σ ℂ) ⊗ₖ M) E 0 Y =
      Matrix.fromBlocks (V ⊗ₖ M) 0 0 Y from cancellation_identity M E Y V hY,
    p.directSum _ _ (unit_tensor _ _ hV hM) hY, p.tensor _ _ hV hM] at hh
  rw [p.identity_pad _ (unit_tensor _ _ hV isUnit_one), p.tensor _ _ hV isUnit_one,
    p.one, mul_zero, add_zero, p.rectangularShear_neg] at hl
  linarith

end ExactFourier.Triangular

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Triangular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Triangular monotonicity, 05-corners:116–209. The arbitrary block-copy basis
change is paid on both sides and cancels exactly, not estimated or assumed free. -/
namespace ExactFourier
open scoped Kronecker BigOperators
open Triangular TensorTools
namespace MatrixPrice
variable (p : MatrixPrice)
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem triangular_experiment_bound (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) (k : ℕ) :
    (Fintype.card (Calls β k) : ℝ) *
        (p.value M + p.value D - p.value (Matrix.fromBlocks M C 0 D)) ≤
      (Fintype.card α : ℝ)^2 * Fintype.card β * Fintype.card (Bottom β k) := by
  have hspan : Submodule.span ℂ (Set.range (flat (contamination C D k * (Triangular.tensorPower D k)⁻¹))) =
      Submodule.span ℂ (Set.range (generators C D k)) := by
    rw [← rowBasis_normalizes C D hD k]
    exact (span_rows_unit_mul _ _ (rowBasis_unit D hD k)).symm
  have h := compressed_price p M (contamination C D k) (Triangular.tensorPower D k) hM
    (tensorPower_unit D hD k) (generators C D k) hspan
    (Fintype.card α * Fintype.card β) (generators_sparse C D k)
  rw [tensorPower_price p D hD k] at h
  have he := experiment_price p M C D hM hD k
  push_cast at h
  nlinarith

/-- The literal upper block triangular conclusion, including empty blocks. -/
theorem upper_triangular (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) :
    p.value M + p.value D ≤ p.value (Matrix.fromBlocks M C 0 D) := by
  let δ := p.value M + p.value D - p.value (Matrix.fromBlocks M C 0 D)
  suffices δ ≤ 0 by dsimp [δ] at this; linarith
  by_cases hβ : Fintype.card β = 0
  · have h := p.triangular_experiment_bound M C D hM hD 1
    simpa [hβ, δ] using h
  · have hβpos : 0 < Fintype.card β := Nat.pos_of_ne_zero hβ
    have hb (k : ℕ) : (k : ℝ) * δ ≤ (Fintype.card α * Fintype.card β : ℝ)^2 := by
      have h := p.triangular_experiment_bound M C D hM hD k
      change (Fintype.card (Calls β k) : ℝ) * δ ≤ _ at h
      have hh := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg (Fintype.card β) : (0 : ℝ) ≤ _)
      have hr : (Fintype.card (Calls β k) : ℝ) * Fintype.card β =
          (k : ℝ) * Fintype.card (Bottom β k) := by exact_mod_cast calls_card_relation (β := β) k
      have hrδ := congrArg (fun x : ℝ => x * δ) hr
      have ht : 0 < (Fintype.card (Bottom β k) : ℝ) := by exact_mod_cast bottom_card_pos hβpos k
      apply (mul_le_mul_iff_right₀ ht).mp
      nlinarith only [hh, hrδ]
    by_contra hn
    have hd : 0 < δ := lt_of_not_ge hn
    obtain ⟨k,hk⟩ := exists_nat_gt ((Fintype.card α * Fintype.card β : ℝ)^2 / δ)
    have hk' := (div_lt_iff₀ hd).mp hk
    exact (not_lt_of_ge (hb k)) hk'

theorem lower_triangular (M : Matrix α α ℂ) (C : Matrix β α ℂ)
    (D : Matrix β β ℂ) (hM : IsUnit M) (hD : IsUnit D) :
    p.value M + p.value D ≤ p.value (Matrix.fromBlocks M 0 C D) := by
  have hMt : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa using (Matrix.isUnit_iff_isUnit_det _).mp hM)
  have hDt : IsUnit D.transpose := (Matrix.isUnit_iff_isUnit_det _).mpr
    (by simpa using (Matrix.isUnit_iff_isUnit_det _).mp hD)
  have h := p.upper_triangular M.transpose C.transpose D.transpose hMt hDt
  rw [p.transpose M hM, p.transpose D hD] at h
  have hK : IsUnit (Matrix.fromBlocks M 0 C D) := Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hM,hD⟩
  have he : Matrix.fromBlocks M.transpose C.transpose 0 D.transpose =
      (Matrix.fromBlocks M 0 C D).transpose := by ext i j; cases i <;> cases j <;> rfl
  rw [he, p.transpose _ hK] at h
  exact h

end MatrixPrice
end ExactFourier

end

section
/-! Exact coefficient-basis truncation, as used in the time cascade and feedback
proof on the path to the absent finite-win main theorem. Time comes first. -/

namespace ExactFourier.CoefficientTime
open scoped BigOperators Kronecker

/-- Repeated invertible constant term makes the time coefficient matrix invertible. -/
theorem trunc_isUnit {R : Type*} [Ring R] (t : ℕ) (F : PowerSeries R)
    (hF : IsUnit (PowerSeries.constantCoeff F)) : IsUnit (truncMatrix t F) :=
  (PowerSeries.isUnit_iff_constantCoeff.mpr hF).map (truncHom t)

theorem blockTrunc_isUnit {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (F : Matrix ι ι (PowerSeries ℂ))
    (hF : IsUnit (F.map PowerSeries.constantCoeff)) :
    IsUnit (blockTruncHom t F) := by
  apply IsUnit.map (f := blockTruncHom t)
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [RingHom.map_det]
  exact (Matrix.isUnit_iff_isUnit_det _).mp hF

theorem coeff_mul_truncated {R : Type*} [Semiring R] {t : ℕ}
    (F G : PowerSeries R) (a : Fin t) :
    PowerSeries.coeff a.val (F*G) = ∑ k : Fin t,
      (if k.val ≤ a.val then PowerSeries.coeff (a.val-k.val) F else 0) *
        PowerSeries.coeff k.val G := by
  have ht : 0<t := Nat.zero_lt_of_lt a.isLt
  have h := congrFun (congrFun (truncMatrix_mul t F G) a) (⟨0, ht⟩ : Fin t)
  simpa only [truncMatrix, Nat.zero_le, ite_true, Nat.sub_zero, Matrix.mul_apply] using h

/-- A matrix series acts on vectors of truncated coefficients by the literal
coefficient product. This is the state-response and boundary-quotient interface. -/
theorem blocks_mul_columns {ι κ : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ)
    (F : Matrix ι ι (PowerSeries ℂ)) (V : Matrix ι κ (PowerSeries ℂ)) :
    blockTruncHom t F * coefficientColumns t V = coefficientColumns t (F*V) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, blockTruncHom_apply, coefficientColumns,
    Fintype.sum_prod_type, map_sum, coeff_mul_truncated _ _ a.1]
  rw [Finset.sum_comm]

theorem prefixScalar_isUnit (t T : ℕ) (f : PowerSeries ℂ)
    (hf : IsUnit (PowerSeries.constantCoeff f)) : IsUnit (prefixScalar t T f) := by
  obtain ⟨u, hu⟩ := PowerSeries.isUnit_iff_constantCoeff.mpr hf
  subst f
  refine ⟨⟨prefixScalar t T (u : PowerSeries ℂ), prefixScalar t T (↑u⁻¹ : PowerSeries ℂ), ?_, ?_⟩, rfl⟩
  · rw [← prefixScalar_mul]; simp
  · rw [← prefixScalar_mul]; simp

/-- On an early row the partial scalar convolution is a full coefficient
convolution; on a late row it leaves the original series coefficient unchanged. -/
theorem prefix_mul_columns {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f : PowerSeries ℂ) (V : Matrix ι κ (PowerSeries ℂ))
    (a : Fin t × ι) (b : κ) :
    ((prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) * coefficientColumns t V) a b =
      if a.1.val < T then PowerSeries.coeff a.1.val (f * V a.2 b)
      else PowerSeries.coeff a.1.val (V a.2 b) := by
  classical
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply, coefficientColumns,
    Fintype.sum_prod_type]
  simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  by_cases ha : a.1.val < T
  · simp only [ha, ite_true, prefixScalar]
    symm
    exact coeff_mul_truncated f (V a.2 b) a.1
  · simp only [ha, ite_false, prefixScalar, Matrix.one_apply]
    simp

theorem zero_prefix_columns_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f : PowerSeries ℂ) (S : Matrix (Fin t × ι) (Fin t × ι) ℂ)
    (hS : ∀ a b, b.1.val < T → S a b = 0) :
    S * (prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) = S := by
  classical
  have h : S * (prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) =
      S * ((1 : Matrix (Fin t) (Fin t) ℂ) ⊗ₖ (1 : Matrix ι ι ℂ)) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkT : k.1.val < T
    · rw [hS a k hkT]
      simp
    · simp [prefixScalar, hkT]
  simpa using h

end ExactFourier.CoefficientTime

end

section
namespace ExactFourier
open scoped BigOperators
open TensorTools

namespace MatrixPrice
variable (p : MatrixPrice) {α : Type} [Fintype α] [DecidableEq α]

theorem blocks_lower (t : ℕ) (F : Matrix (Fin t × α) (Fin t × α) ℂ)
    (A : Fin t → Matrix α α ℂ) (hA : ∀ i, IsUnit (A i))
    (hdiag : ∀ i a b, F (i,a) (i,b) = A i a b)
    (hbelow : ∀ i j a b, i < j → F (i,a) (j,b) = 0) :
    IsUnit F ∧ (∑ i, p.value (A i)) ≤ p.value F := by
  induction t with
  | zero =>
    have hF : F = 1 := by ext i j; exact Fin.elim0 i.1
    rw [hF, p.one]
    exact ⟨isUnit_one, by simp⟩
  | succ t ih =>
    let D : Matrix (Fin t × α) (Fin t × α) ℂ := fun i j => F (i.1.succ,i.2) (j.1.succ,j.2)
    let C : Matrix (Fin t × α) α ℂ := fun i a => F (i.1.succ,i.2) (0,a)
    obtain ⟨hD,hprice⟩ := ih D (fun i => A i.succ) (fun i => hA i.succ)
      (fun i a b => hdiag i.succ a b)
      (fun i j a b hij => hbelow i.succ j.succ a b (by simpa using hij))
    have he : Matrix.reindex (timeSplit t α) (timeSplit t α) F =
        Matrix.fromBlocks (A 0) 0 C D := by
      ext i j
      rcases i with a|⟨i,a⟩ <;> rcases j with b|⟨j,b⟩
      · exact hdiag 0 a b
      · exact hbelow 0 j.succ a b (by simp)
      · rfl
      · rfl
    have hK : IsUnit (Matrix.fromBlocks (A 0) 0 C D) :=
      Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨hA 0,hD⟩
    have hF : IsUnit F := by
      have hh : IsUnit ((Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)) F) := by
        change IsUnit (Matrix.reindex (timeSplit t α) (timeSplit t α) F)
        rw [he]
        exact hK
      have hh' := hh.map (Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)).symm.toMonoidHom
      change IsUnit ((Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)).symm
        ((Matrix.reindexAlgEquiv ℂ ℂ (timeSplit t α)) F)) at hh'
      simpa only [AlgEquiv.symm_apply_apply] using hh'
    refine ⟨hF, ?_⟩
    have hb := p.lower_triangular (A 0) C D (hA 0) hD
    rw [← he, p.reindex _ _ hF] at hb
    rw [Fin.sum_univ_succ]
    linarith

theorem trunc_lower_bound (t : ℕ) (F : Matrix α α (PowerSeries ℂ))
    (hF : IsUnit (F.map PowerSeries.constantCoeff)) :
    (t : ℝ) * p.value (F.map PowerSeries.constantCoeff) ≤
      p.value (CoefficientTime.blockTruncHom t F) := by
  have h := p.blocks_lower t (CoefficientTime.blockTruncHom t F)
    (fun _ => F.map PowerSeries.constantCoeff) (fun _ => hF)
    (by intro i a b; simp [CoefficientTime.blockTruncHom_apply])
    (by intro i j a b hij; simp [CoefficientTime.blockTruncHom_apply, not_le.mpr hij])
  simpa using h.2

end MatrixPrice
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.StreamSeries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The finite-coefficient meaning of the cell transfer H(z). The geometric
resolvent is defined coefficientwise, without assumptions on D. -/
namespace ExactFourier
open scoped BigOperators
namespace CellSeries
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem constant_transfer
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    (transfer M C B D).map PowerSeries.constantCoeff = M := by
  ext i j
  simp [transfer, Matrix.add_apply, Matrix.smul_apply]

theorem resolvent_right_inverse (D : Matrix β β ℂ) :
    (1 - (PowerSeries.X : PowerSeries ℂ) • D.map PowerSeries.C) * resolvent D = 1 := by
  rw [sub_mul, one_mul, Matrix.smul_mul]
  ext i j n
  cases n with
  | zero => simp [Matrix.sub_apply, Matrix.smul_apply, resolvent, Matrix.one_apply]
  | succ n =>
    have hc : PowerSeries.coeff n ((D.map PowerSeries.C * resolvent D) i j) =
        (D*D^n) i j := by simp [Matrix.mul_apply, PowerSeries.coeff_C_mul]
    simp only [Matrix.sub_apply, map_sub, Matrix.smul_apply, smul_eq_mul,
      PowerSeries.coeff_succ_X_mul, coeff_resolvent, hc, ← pow_succ', sub_self]
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]

end CellSeries
end ExactFourier

end

section
/-! Literal finite cell word, one persistent state carried through t fresh data
blocks. All coordinates are allowed arbitrary initial values. -/
namespace ExactFourier
open TensorTools CoefficientTime
open scoped BigOperators
namespace CellStream
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem unit (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) (hK : IsUnit K) (t : ℕ) :
    IsUnit (run K t) := by
  induction t with
  | zero => exact isUnit_one
  | succ t ih => exact unit_reindex _ _ (CellJoin.unit K (run K t) hK ih)

theorem price (p : MatrixPrice) (K : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hK : IsUnit K) (t : ℕ) : p.value (run K t) ≤ (t : ℝ) * p.value K := by
  induction t with
  | zero => simp [run,p.one]
  | succ t ih =>
    rw [run, p.reindex _ _ (CellJoin.unit _ _ hK (unit K hK t))]
    have h := CellJoin.price p K (run K t) hK (unit K hK t)
    push_cast
    linarith

variable (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ)

theorem state_entry (t : ℕ) (i : Fin t) (a : α) (b : β) :
    run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inr b) = (C*D^i.val) a b := by
  induction t generalizing b with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · rw [succ_state]
      simp_rw [ih]
      change (C*D^j.val*D) a b = (C*D^(j.val+1)) a b
      rw [Matrix.mul_assoc, pow_succ]

theorem state_block (t : ℕ) :
    (run (Matrix.fromBlocks M C B D) t).toBlocks₁₂ =
      coefficientColumns t (CellSeries.state C D) := by
  ext ⟨i,a⟩ b
  exact (state_entry M C B D t i a b).trans (CellSeries.coeff_state C D i.val a b).symm

theorem data_entry (t : ℕ) (i j : Fin t) (a b : α) :
    run (Matrix.fromBlocks M C B D) t (Sum.inl (i,a)) (Sum.inl (j,b)) =
      if j.val ≤ i.val then PowerSeries.coeff (i.val-j.val) (CellSeries.transfer M C B D a b) else 0 := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j <;> simp
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [succ_fst, Fin.val_zero, Nat.zero_le, ite_true, Nat.sub_zero,
          Fin.val_succ, CellSeries.coeff_transfer_succ, state_entry]
        rfl
      · simpa using ih i j

theorem data_block (t : ℕ) :
    (run (Matrix.fromBlocks M C B D) t).toBlocks₁₁ =
      blockTruncHom t (CellSeries.transfer M C B D) := by
  ext ⟨i,a⟩ ⟨j,b⟩
  exact data_entry M C B D t i j a b

end CellStream
end ExactFourier

end

section
/-! Sequential tensor-axis programs share the full data space but have disjoint
persistent state spaces. The ordering of all noncommuting factors is explicit. -/
namespace ExactFourier
open TensorTools
namespace AxisJoin
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem join_eq
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ) :
    join X Y =
      Matrix.reindex rightOrder rightOrder (Matrix.fromBlocks Y 0 0 (1 : Matrix β β ℂ)) *
      Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
        (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) := by
  have hX : Matrix.reindex (Equiv.sumAssoc α β γ) (Equiv.sumAssoc α β γ)
      (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) =
      Matrix.fromBlocks X.toBlocks₁₁ (Matrix.fromCols X.toBlocks₁₂ 0)
        (Matrix.fromRows X.toBlocks₂₁ 0) (Matrix.fromBlocks X.toBlocks₂₂ 0 0 1) := by
    ext i j
    rcases i with a|(b|c) <;> rcases j with a'|(b'|c') <;>
      simp [Matrix.reindex_apply, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  have hY : Matrix.reindex (rightOrder (α := α) (β := β) (γ := γ)) rightOrder
      (Matrix.fromBlocks Y 0 0 (1 : Matrix β β ℂ)) =
      Matrix.fromBlocks Y.toBlocks₁₁ (Matrix.fromCols 0 Y.toBlocks₁₂)
        (Matrix.fromRows 0 Y.toBlocks₂₁) (Matrix.fromBlocks 1 0 0 Y.toBlocks₂₂) := by
    ext i j
    rcases i with a|(b|c) <;> rcases j with a'|(b'|c') <;>
      simp [Matrix.reindex_apply, rightOrder, middleEquiv, Matrix.fromBlocks, Matrix.fromRows,
        Matrix.fromCols, Sum.elim, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₁,
        Matrix.toBlocks₂₂, Matrix.one_apply]
  rw [hX,hY]
  simp only [join, Matrix.fromBlocks_multiply]
  ext i j
  rcases i with a|(b|c) <;> rcases j with a'|(b'|c') <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.fromRows, Matrix.fromCols, Sum.elim, Matrix.one_apply]

theorem unit (X : Matrix (α ⊕ β) (α ⊕ β) ℂ) (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ)
    (hX : IsUnit X) (hY : IsUnit Y) : IsUnit (join X Y) := by
  rw [join_eq]
  exact (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hY,isUnit_one⟩)).mul
    (unit_reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩))

theorem price (p : MatrixPrice) (X : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (Y : Matrix (α ⊕ γ) (α ⊕ γ) ℂ) (hX : IsUnit X) (hY : IsUnit Y) :
    p.value (join X Y) ≤ p.value X + p.value Y := by
  have hX' : IsUnit (Matrix.fromBlocks X 0 0 (1 : Matrix γ γ ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hX,isUnit_one⟩
  have hY' : IsUnit (Matrix.fromBlocks Y 0 0 (1 : Matrix β β ℂ)) :=
    Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hY,isUnit_one⟩
  rw [join_eq]
  calc
    _ ≤ _ := p.mul_le _ _ (unit_reindex _ _ hY') (unit_reindex _ _ hX')
    _ = _ := by rw [p.reindex _ _ hY',p.reindex _ _ hX',
      p.identity_pad _ hY,p.identity_pad _ hX]; ring

end AxisJoin
end ExactFourier

end

section
/-! Parallel lifts of a finite stream. Time remains outermost, and no additional
coordinates are inserted. -/
namespace ExactFourier
open CoefficientTime TensorTools
open scoped Kronecker
namespace TimeLifts
variable {σ ρ α β : Type} [Fintype σ] [Fintype ρ] [Fintype α] [Fintype β]
  [DecidableEq σ] [DecidableEq ρ] [DecidableEq α] [DecidableEq β]

theorem right_unit (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ)
    (hX : IsUnit X) : IsUnit (right (α := α) t X) :=
  unit_reindex _ _ (unit_tensor _ _ hX isUnit_one)
theorem left_unit (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (hX : IsUnit X) : IsUnit (left (σ := σ) t X) :=
  unit_reindex _ _ (unit_tensor _ _ isUnit_one hX)
theorem right_price (p : MatrixPrice) (t : ℕ)
    (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ) (hX : IsUnit X) :
    p.value (right (α := α) t X) = (Fintype.card α : ℝ) * p.value X := by
  rw [right,p.reindex _ _ (unit_tensor _ _ hX isUnit_one),p.tensor _ _ hX isUnit_one,p.one]
  ring
theorem left_price (p : MatrixPrice) (t : ℕ)
    (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ) (hX : IsUnit X) :
    p.value (left (σ := σ) t X) = (Fintype.card σ : ℝ) * p.value X := by
  rw [left,p.reindex _ _ (unit_tensor _ _ isUnit_one hX),p.tensor _ _ isUnit_one hX,p.one]
  ring

theorem right_data
    {σ : Type} {ρ : Type} {α : Type} [Fintype σ] [Fintype ρ] [Fintype α] [DecidableEq σ] [DecidableEq ρ] [DecidableEq α] (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ)
    (H : Matrix σ σ (PowerSeries ℂ)) (hX : X.toBlocks₁₁ = blockTruncHom t H) :
    (right (α := α) t X).toBlocks₁₁ =
      blockTruncHom t (H ⊗ₖ (1 : Matrix α α (PowerSeries ℂ))) := by
  ext ⟨i,s,a⟩ ⟨j,u,b⟩
  have hx := congrFun (congrFun hX (i,s)) (j,u)
  change X (Sum.inl (i,s)) (Sum.inl (j,u)) = _ at hx
  change X (Sum.inl (i,s)) (Sum.inl (j,u)) * (1 : Matrix α α ℂ) a b = _
  rw [hx]
  by_cases hab : a=b <;> by_cases hji : j.val ≤ i.val <;>
    simp [blockTruncHom_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,hab,hji]

theorem left_data
    {σ : Type} {α : Type} {β : Type} [Fintype σ] [Fintype α] [Fintype β] [DecidableEq σ] [DecidableEq α] [DecidableEq β] (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (H : Matrix α α (PowerSeries ℂ)) (hX : X.toBlocks₁₁ = blockTruncHom t H) :
    (left (σ := σ) t X).toBlocks₁₁ =
      blockTruncHom t ((1 : Matrix σ σ (PowerSeries ℂ)) ⊗ₖ H) := by
  ext ⟨i,s,a⟩ ⟨j,u,b⟩
  have hx := congrFun (congrFun hX (i,a)) (j,b)
  change X (Sum.inl (i,a)) (Sum.inl (j,b)) = _ at hx
  change (1 : Matrix σ σ ℂ) s u * X (Sum.inl (i,a)) (Sum.inl (j,b)) = _
  rw [hx]
  by_cases hsu : s=u <;> by_cases hji : j.val ≤ i.val <;>
    simp [blockTruncHom_apply,Matrix.kroneckerMap_apply,Matrix.one_apply,hsu,hji]

theorem right_state
    {σ : Type} {ρ : Type} {α : Type} [Fintype σ] [Fintype ρ] [Fintype α] [DecidableEq σ] [DecidableEq ρ] [DecidableEq α] (t : ℕ) (X : Matrix ((Fin t × σ) ⊕ ρ) ((Fin t × σ) ⊕ ρ) ℂ)
    (E : Matrix σ ρ (PowerSeries ℂ)) (hX : X.toBlocks₁₂ = coefficientColumns t E) :
    (right (α := α) t X).toBlocks₁₂ =
      coefficientColumns t (E ⊗ₖ (1 : Matrix α α (PowerSeries ℂ))) := by
  ext ⟨i,s,a⟩ ⟨u,b⟩
  have hx := congrFun (congrFun hX (i,s)) u
  change X (Sum.inl (i,s)) (Sum.inr u) = _ at hx
  change X (Sum.inl (i,s)) (Sum.inr u) * (1 : Matrix α α ℂ) a b = _
  rw [hx]
  by_cases hab : a=b <;>
    simp [coefficientColumns,Matrix.kroneckerMap_apply,Matrix.one_apply,hab]

theorem left_state
    {σ : Type} {α : Type} {β : Type} [Fintype σ] [Fintype α] [Fintype β] [DecidableEq σ] [DecidableEq α] [DecidableEq β] (t : ℕ) (X : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (E : Matrix α β (PowerSeries ℂ)) (hX : X.toBlocks₁₂ = coefficientColumns t E) :
    (left (σ := σ) t X).toBlocks₁₂ =
      coefficientColumns t ((1 : Matrix σ σ (PowerSeries ℂ)) ⊗ₖ E) := by
  ext ⟨i,s,a⟩ ⟨u,b⟩
  have hx := congrFun (congrFun hX (i,a)) b
  change X (Sum.inl (i,a)) (Sum.inr b) = _ at hx
  change (1 : Matrix σ σ ℂ) s u * X (Sum.inl (i,a)) (Sum.inr b) = _
  rw [hx]
  by_cases hsu : s=u <;>
    simp [coefficientColumns,Matrix.kroneckerMap_apply,Matrix.one_apply,hsu]

end TimeLifts
end ExactFourier

end

section
/-! The same exact tensor index for scalar, polynomial, and series matrices.
The zero tensor power has one coordinate and is identity. -/
namespace ExactFourier
open scoped Kronecker BigOperators
open Triangular TensorTools
namespace TensorAxis

variable {α : Type} [Fintype α] [DecidableEq α]
variable {R S : Type} [CommSemiring R] [CommSemiring S]

theorem map_power
    {α : Type} [Fintype α] [DecidableEq α] {R : Type} {S : Type} [CommSemiring R] [CommSemiring S] (f : R →+* S) (A : Matrix α α R) (k : ℕ) :
    (power A k).map f = power (A.map f) k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    ext i j
    change f (power A k i.1 j.1 * A i.2 j.2) =
      power (A.map f) k i.1 j.1 * f (A i.2 j.2)
    rw [map_mul]
    exact congrArg (fun x => x * f (A i.2 j.2)) (congrFun (congrFun ih i.1) j.1)

theorem mul_power
    {α : Type} [Fintype α] [DecidableEq α] {R : Type} [CommSemiring R] (A B : Matrix α α R) (k : ℕ) :
    power A k * power B k = power (A*B) k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    change (power A k ⊗ₖ A) * (power B k ⊗ₖ B) = _
    rw [← Matrix.mul_kronecker_mul,ih]
    rfl

theorem price_power (p : MatrixPrice) (A : Matrix α α ℂ) (hA : IsUnit A) (k : ℕ) :
    p.value (power A k) = (Fintype.card (Fibers α k) : ℝ) * p.value A := by
  induction k with
  | zero => simp [power,p.one]
  | succ k ih =>
    rw [power,p.tensor _ _ (unit_power A hA k) hA,ih,calls_card_succ]
    push_cast
    ring

end TensorAxis
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CascadeWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
open scoped Kronecker BigOperators
open TensorAxis CoefficientTime TensorTools
namespace Cascade

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem unit (K : Matrix (α ⊕ β) (α ⊕ β) ℂ) (hK : IsUnit K) (t k : ℕ) :
    IsUnit (run K t k) := by
  induction k with
  | zero => exact isUnit_one
  | succ k ih =>
    exact AxisJoin.unit _ _ (TimeLifts.right_unit _ _ ih)
      (TimeLifts.left_unit _ _ (CellStream.unit K hK t))

theorem price (p : MatrixPrice) (K : Matrix (α ⊕ β) (α ⊕ β) ℂ)
    (hK : IsUnit K) (t k : ℕ) :
    p.value (run K t k) ≤ (t : ℝ) * Fintype.card (Fibers α k) * p.value K := by
  induction k with
  | zero => simp [run,p.one]
  | succ k ih =>
    have hj := AxisJoin.price p (TimeLifts.right (α := α) t (run K t k))
      (TimeLifts.left (σ := Space α k) t (CellStream.run K t))
      (TimeLifts.right_unit _ _ (unit K hK t k))
      (TimeLifts.left_unit _ _ (CellStream.unit K hK t))
    change p.value (run K t (k+1)) ≤ _ at hj
    rw [TimeLifts.right_price p _ _ (unit K hK t k),
      TimeLifts.left_price p _ _ (CellStream.unit K hK t)] at hj
    have h1 := mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _)
    have h2 := mul_le_mul_of_nonneg_left (CellStream.price p K hK t)
      (Nat.cast_nonneg (Fintype.card (Space α k)) : (0:ℝ) ≤ _)
    rw [Triangular.calls_card_succ]
    push_cast
    nlinarith only [hj,h1,h2]

variable (M : Matrix α α ℂ) (C : Matrix α β ℂ) (B : Matrix β α ℂ) (D : Matrix β β ℂ)

theorem data_block (t k : ℕ) :
    (run (Matrix.fromBlocks M C B D) t k).toBlocks₁₁ =
      blockTruncHom t (power (CellSeries.transfer M C B D) k) := by
  induction k with
  | zero =>
    simp only [run,power,map_one]
    ext i j
    simp [Matrix.toBlocks₁₁,Matrix.one_apply]
  | succ k ih =>
    change (TimeLifts.left (σ := Space α k) t (CellStream.run (Matrix.fromBlocks M C B D) t)).toBlocks₁₁ *
      (TimeLifts.right (α := α) t (run (Matrix.fromBlocks M C B D) t k)).toBlocks₁₁ = _
    rw [TimeLifts.right_data _ _ _ ih,
      TimeLifts.left_data _ _ _ (CellStream.data_block M C B D t),← map_mul,
      ← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]
    rfl

theorem columns_fromCols {σ ρ τ : Type} (t : ℕ)
    (E : Matrix σ ρ (PowerSeries ℂ)) (F : Matrix σ τ (PowerSeries ℂ)) :
    coefficientColumns t (Matrix.fromCols E F) =
      Matrix.fromCols (coefficientColumns t E) (coefficientColumns t F) := by
  ext i j; cases j <;> rfl

theorem state_block (t k : ℕ) :
    (run (Matrix.fromBlocks M C B D) t k).toBlocks₁₂ =
      coefficientColumns t (response (CellSeries.transfer M C B D) (CellSeries.state C D) k) := by
  induction k with
  | zero => ext i j; exact PEmpty.elim j
  | succ k ih =>
    change Matrix.fromCols
      ((TimeLifts.left (σ := Space α k) t (CellStream.run (Matrix.fromBlocks M C B D) t)).toBlocks₁₁ *
        (TimeLifts.right (α := α) t (run (Matrix.fromBlocks M C B D) t k)).toBlocks₁₂)
      (TimeLifts.left (σ := Space α k) t (CellStream.run (Matrix.fromBlocks M C B D) t)).toBlocks₁₂ = _
    rw [TimeLifts.left_data _ _ _ (CellStream.data_block M C B D t),
      TimeLifts.right_state _ _ _ ih,
      TimeLifts.left_state _ _ _ (CellStream.state_block M C B D t),
      blocks_mul_columns,← Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]
    exact (columns_fromCols _ _ _).symm

end Cascade
end ExactFourier

end

section
/-! Polynomial clearing for the cascade (05-corners:327–369). No inverse of D
and no genericity of evaluation points is used. -/
namespace ExactFourier
namespace CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem map_smul {R S : Type} [CommSemiring R] [CommSemiring S] {ι κ : Type}
    (f : R →+* S) (a : R) (A : Matrix ι κ R) :
    (a • A).map f = f a • A.map f := by
  ext i j; exact f.map_mul _ _

@[simp] theorem map_Z
    {β : Type} [Fintype β] [DecidableEq β] (D : Matrix β β ℂ) :
    (Z D).map ps = 1 - (PowerSeries.X : PowerSeries ℂ) • D.map PowerSeries.C := by
  rw [Z,Matrix.map_sub _ (map_sub ps),map_smul,Matrix.map_one _ (map_zero ps) (map_one ps),map_const]
  simp

@[simp] theorem eval_Z_zero
    {β : Type} [Fintype β] [DecidableEq β] (D : Matrix β β ℂ) : (Z D).map (evalRingHom 0) = 1 := by
  rw [Z,Matrix.map_sub _ (map_sub (evalRingHom 0)),map_smul]
  simp
@[simp] theorem eval_a_zero (D : Matrix β β ℂ) : (a D).eval 0 = 1 := by
  change evalRingHom 0 ((Z D).det) = 1
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_Z_zero,Matrix.det_one]
@[simp] theorem eval_F_zero
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    (F M C B D).map (evalRingHom 0) = M := by
  rw [F,Matrix.map_add _ (map_add (evalRingHom 0)),map_smul,map_smul]
  simp only [coe_evalRingHom,eval_a_zero,one_smul,eval_X,zero_smul,add_zero]
  ext i j; simp
@[simp] theorem eval_b_zero (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) : (b M C B D).eval 0 = M.det := by
  change evalRingHom 0 ((F M C B D).det) = _
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_F_zero]

theorem cleared_resolvent (D : Matrix β β ℂ) :
    ps (a D) • CellSeries.resolvent D = (R D).map ps := by
  have h := congrArg (fun A : Matrix β β (Polynomial ℂ) => A.map ps) (Matrix.adjugate_mul (Z D))
  rw [Matrix.map_mul,map_smul,Matrix.map_one _ (map_zero ps) (map_one ps)] at h
  change (R D).map ps * (Z D).map ps = ps (a D) • 1 at h
  have hz := CellSeries.resolvent_right_inverse D
  rw [← map_Z] at hz
  calc
    ps (a D) • CellSeries.resolvent D = (ps (a D) • (1 : Matrix β β (PowerSeries ℂ))) * CellSeries.resolvent D := by rw [Matrix.smul_mul,one_mul]
    _ = (R D).map ps * ((Z D).map ps * CellSeries.resolvent D) := by rw [← h,Matrix.mul_assoc]
    _ = (R D).map ps := by rw [hz,mul_one]

theorem cleared_state
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (C : Matrix α β ℂ) (D : Matrix β β ℂ) :
    ps (a D) • CellSeries.state C D = (C.map Polynomial.C * R D).map ps := by
  rw [Matrix.map_mul,map_const,CellSeries.state,← Matrix.mul_smul,cleared_resolvent]

theorem cleared_transfer (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    ps (a D) • CellSeries.transfer M C B D = (F M C B D).map ps := by
  rw [F,Matrix.map_add _ (map_add ps),map_smul,map_smul,Matrix.map_mul,map_const,map_const,
    CellSeries.transfer,smul_add,smul_comm (ps (a D)) (PowerSeries.X : PowerSeries ℂ),
    ← Matrix.smul_mul,cleared_state]
  simp

theorem right_clearing (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    CellSeries.transfer M C B D * (L M C B D).map ps = ps (b M C B D) • 1 := by
  rw [L,map_smul,Matrix.mul_smul,← Matrix.smul_mul,cleared_transfer,← Matrix.map_mul]
  have h := Matrix.mul_adjugate (F M C B D)
  change F M C B D * J M C B D = b M C B D • 1 at h
  rw [h,map_smul,Matrix.map_one _ (map_zero ps) (map_one ps)]

theorem state_clearing (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) :
    CellSeries.transfer M C B D * (T M C B D).map ps =
      ps (b M C B D) • CellSeries.state C D := by
  rw [T,Matrix.mul_assoc,Matrix.map_mul,← cleared_state,Matrix.mul_smul,Matrix.mul_smul,
    ← Matrix.mul_assoc,← Matrix.smul_mul]
  have hL : ps (a D) • (CellSeries.transfer M C B D * (J M C B D).map ps) =
      ps (b M C B D) • 1 := by
    have h := right_clearing M C B D
    simpa [L,map_smul,Matrix.mul_smul] using h
  rw [hL,Matrix.smul_mul,Matrix.one_mul]

end CellPoly
end ExactFourier

end

section
namespace ExactFourier
open scoped Kronecker
open TensorAxis
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
variable {R : Type} [CommSemiring R]

theorem power_smul
    {α : Type} [Fintype α] [DecidableEq α] {R : Type} [CommSemiring R] (c : R) (A : Matrix α α R) (k : ℕ) :
    power (c • A) k = c^k • power A k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    rw [power,ih,Matrix.smul_kronecker,Matrix.kronecker_smul,smul_smul,pow_succ]
    rfl

theorem map_cleared
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] {R : Type} [CommSemiring R] {S : Type} [CommSemiring S] (f : R →+* S)
    (b : R) (L : Matrix α α R) (T : Matrix α β R) (k : ℕ) :
    (cleared b L T k).map f = cleared (f b) (L.map f) (T.map f) k := by
  induction k with
  | zero => ext i j; exact PEmpty.elim j
  | succ k ih =>
    ext i j
    cases j with
    | inl j =>
      change f (b * (cleared b L T k i.1 j.1 * (1 : Matrix α α R) i.2 j.2)) = _
      rw [map_mul,map_mul]
      have he := congrFun (congrFun ih i.1) j.1
      change f (cleared b L T k i.1 j.1) = _ at he
      rw [he]
      by_cases hij : i.2=j.2 <;> simp [cleared,Matrix.one_apply,hij,Matrix.kroneckerMap_apply]
    | inr j =>
      change f (power L k i.1 j.1 * T i.2 j.2) = _
      rw [map_mul]
      have he := congrFun (congrFun (map_power f L k) i.1) j.1
      change f (power L k i.1 j.1) = _ at he
      rw [he]
      rfl

theorem clearing_identity
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (c : PowerSeries ℂ) (H L : Matrix α α (PowerSeries ℂ))
    (S T : Matrix α β (PowerSeries ℂ)) (hL : H*L=c•1) (hT : H*T=c•S) (k : ℕ) :
    power H k * cleared c L T k = c^k • response H S k := by
  induction k with
  | zero => simp [cleared,response,power]
  | succ k ih =>
    change (power H k ⊗ₖ H) * Matrix.fromCols _ _ = _
    rw [Matrix.mul_fromCols,Matrix.mul_smul,← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul,ih,Matrix.mul_one,mul_power,hL,hT,power_smul,power_one,
      Matrix.smul_kronecker,Matrix.kronecker_smul,Matrix.smul_kronecker,smul_smul,smul_smul]
    rw [mul_comm c (c^k),← pow_succ]
    ext i j; cases j <;> rfl

theorem cell_clearing (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (k : ℕ) :
    power (CellSeries.transfer M C B D) k *
      (cleared (CellPoly.b M C B D) (CellPoly.L M C B D) (CellPoly.T M C B D) k).map CellPoly.ps =
    CellPoly.ps ((CellPoly.b M C B D)^k) •
      response (CellSeries.transfer M C B D) (CellSeries.state C D) k := by
  rw [map_cleared,map_pow]
  exact clearing_identity _ _ _ _ _ (CellPoly.right_clearing M C B D)
    (CellPoly.state_clearing M C B D) k

end Cascade
end ExactFourier

end

section
namespace ExactFourier
open scoped BigOperators Kronecker
namespace PolynomialMatrix
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

theorem le_bound (A : Matrix ι κ (Polynomial ℂ)) (i : ι) (j : κ) :
    (A i j).natDegree ≤ bound A := by
  calc
    (A i j).natDegree ≤ ∑ v, (A i v).natDegree :=
      Finset.single_le_sum (f := fun v => (A i v).natDegree) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    _ ≤ ∑ u, ∑ v, (A u v).natDegree :=
      Finset.single_le_sum (f := fun u => ∑ v, (A u v).natDegree)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem bounded_one
    {ι : Type} [Fintype ι] [DecidableEq ι] : Bounded (1 : Matrix ι ι (Polynomial ℂ)) 0 := by
  intro i j
  by_cases h : i=j <;> simp [Matrix.one_apply,h]

theorem bounded_tensor
    {ι : Type} {κ : Type} {τ : Type} {υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ] (A : Matrix ι κ (Polynomial ℂ)) (B : Matrix τ υ (Polynomial ℂ))
    {d e : ℕ} (hA : Bounded A d) (hB : Bounded B e) : Bounded (A ⊗ₖ B) (d+e) := by
  intro i j
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hA _ _) (hB _ _))

theorem bounded_smul
    {ι : Type} {κ : Type} [Fintype ι] [Fintype κ] (b : Polynomial ℂ) (A : Matrix ι κ (Polynomial ℂ))
    {d e : ℕ} (hb : b.natDegree≤d) (hA : Bounded A e) : Bounded (b•A) (d+e) := by
  intro i j
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add hb (hA i j))

theorem bounded_power {α : Type} [Fintype α] [DecidableEq α]
    (A : Matrix α α (Polynomial ℂ)) {d : ℕ} (hA : Bounded A d) (k : ℕ) :
    Bounded (TensorAxis.power A k) (k*d) := by
  induction k with
  | zero => simpa [TensorAxis.power] using (bounded_one (ι := PUnit))
  | succ k ih => simpa [TensorAxis.power,Nat.succ_mul] using bounded_tensor _ _ ih hA

end PolynomialMatrix
namespace Cascade
open PolynomialMatrix TensorAxis
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem bounded_cleared
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (b : Polynomial ℂ) (L : Matrix α α (Polynomial ℂ))
    (T : Matrix α β (Polynomial ℂ)) {d : ℕ}
    (hb : b.natDegree≤d) (hL : Bounded L d) (hT : Bounded T d) (k : ℕ) :
    Bounded (cleared b L T k) (k*d) := by
  induction k with
  | zero => intro i j; exact PEmpty.elim j
  | succ k ih =>
    intro i j
    cases j with
    | inl j =>
      have h := bounded_smul b _ hb (bounded_tensor _ _ ih (bounded_one (ι := α))) i j
      simpa [cleared,Nat.succ_mul,Nat.add_comm] using h
    | inr j =>
      have h := bounded_tensor _ _ (bounded_power L hL k) hT i j
      simpa [cleared,Nat.succ_mul] using h

theorem exists_cleared_degree (b : Polynomial ℂ) (L : Matrix α α (Polynomial ℂ))
    (T : Matrix α β (Polynomial ℂ)) :
    ∃ d : ℕ, ∀ k, Bounded (cleared b L T k) (k*d) := by
  let d := b.natDegree + bound L + bound T
  refine ⟨d,fun k => bounded_cleared b L T ?_ ?_ ?_ k⟩
  · dsimp [d]; omega
  · intro i j; have h := le_bound L i j; dsimp [d]; omega
  · intro i j; have h := le_bound T i j; dsimp [d]; omega

end Cascade
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CircuitExtensions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier

theorem Program.eval_original {n k : ℕ} (p : Program n k) (x : Fin n → ℂ)
    (i : Fin (n+1)) : p.eval x (Fin.castAdd k i) = (Fin.snoc x 0 : Fin (n+1) → ℂ) i := by
  induction p with
  | nil => rfl
  | @step k p g ih =>
      change (Fin.snoc (p.eval x) (g.eval (p.eval x)) : Fin (n+1+k+1) → ℂ)
        (Fin.castSucc (Fin.castAdd k i)) = _
      rw [Fin.snoc_castSucc]
      exact ih

theorem LinearDAG.eval_fanout {n a b : ℕ}
    (C : LinearDAG n a) (D : LinearDAG n b) (x : Fin n → ℂ) :
    (C.fanout D).eval x = Fin.addCases (C.eval x) (D.eval x) := by
  have h := C.program.eval_append D.program (Fin.castAdd C.size) x x
    (fun i => C.program.eval_original x i)
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [LinearDAG.eval, LinearDAG.fanout, Fin.addCases_left] using h.1 (C.outputs j)
  · simpa only [LinearDAG.eval, LinearDAG.fanout, Fin.addCases_right] using h.2 (D.outputs j)

theorem LinearDAG.eval_withInputs {m n a : ℕ} (C : LinearDAG n a)
    (f : Fin n → Fin m) (x : Fin m → ℂ) : (C.withInputs f).eval x = C.eval (x ∘ f) := by
  rw [LinearDAG.withInputs, LinearDAG.eval_comp, LinearDAG.eval_wires]
  congr 1
  funext i
  simp only [Fin.snoc_castSucc, Function.comp_apply]

theorem LinearDAG.eval_butterflies {n m : ℕ} (C : LinearDAG n (m+m))
    (c : Fin m → ℂ) (x : Fin n → ℂ) :
    (C.butterflies c).eval x = Fin.addCases
      (fun i => C.eval x (Fin.castAdd m i) + c i * C.eval x (Fin.natAdd m i))
      (fun i => C.eval x (Fin.castAdd m i) - c i * C.eval x (Fin.natAdd m i)) := by
  let gs : Fin m → Gate (n+1+C.size) := fun i =>
    Gate.scale (c i) (C.outputs (Fin.natAdd m i))
  let gb : Fin (m+m) → Gate (n+1+(C.size+m)) := Fin.addCases
    (fun i => Gate.add (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i))
    (fun i => Gate.sub (keepIndex (C.outputs (Fin.castAdd m i))) (gateIndex i))
  have hs := C.program.eval_emit gs x
  have hb := (C.program.emit gs).eval_emit gb x
  funext i
  change (C.program.emit gs |>.emit gb).eval x (gateIndex i) = _
  rw [hb.2]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [gb, Fin.addCases_left, Gate.eval, hs.1, hs.2, gs]
    rfl
  · simp only [gb, Fin.addCases_right, Gate.eval, hs.1, hs.2, gs]
    rfl

end ExactFourier

end

section
/-! Finite-index wrappers for the exact charged DAG model. These are used for the
state-clearing tensor-axis maps in the cascade and coefficient boundary cost. -/
namespace ExactFourier
open scoped BigOperators Kronecker

namespace TypedDAG
variable {ι κ τ υ : Type} [Fintype ι] [Fintype κ] [Fintype τ] [Fintype υ]

@[simp] theorem eval_comp (D : TypedDAG κ τ) (C : TypedDAG ι κ) (x : ι → ℂ) :
    (D.comp C).eval x = D.eval (C.eval x) := by
  funext j
  simp [eval, comp, LinearDAG.eval_comp, Function.comp_def]

@[simp] theorem eval_inputs (C : TypedDAG ι κ) (f : ι → τ) (x : τ → ℂ) :
    (C.inputs f).eval x = C.eval (x ∘ f) := by
  funext j
  simp [eval, inputs, LinearDAG.eval_withInputs, Function.comp_def]

@[simp] theorem eval_fanout (C : TypedDAG ι κ) (D : TypedDAG ι τ) (x : ι → ℂ) :
    (C.fanout D).eval x = Sum.elim (C.eval x) (D.eval x) := by
  funext j
  cases j <;> simp [eval, fanout, LinearDAG.eval_fanout, Function.comp_def]

@[simp] theorem size_matrix (A : Matrix κ ι ℂ) :
    (matrix A).size = 2 * Fintype.card κ * Fintype.card ι := LinearDAG.size_matrix _
@[simp] theorem eval_scale (c : κ → ℂ) (x : κ → ℂ) :
    (scale c).eval x = fun i => c i * x i := by
  funext i
  simp [eval, scale, LinearDAG.eval_layer, Gate.eval, Function.comp_def]

@[simp] theorem eval_addPair (x : κ ⊕ κ → ℂ) :
    (addPair (κ := κ)).eval x = fun i => x (Sum.inl i) + x (Sum.inr i) := by
  funext i
  simp [eval, addPair, LinearDAG.eval_layer, Gate.eval, Function.comp_def]

theorem size_stackFin (n : ℕ) (C : Fin n → TypedDAG ι κ) :
    (stackFin n C).size = ∑ i, (C i).size := by
  induction n with
  | zero => simp [stackFin]
  | succ n ih => simp [stackFin, ih, Fin.sum_univ_succ]

theorem eval_stackFin (n : ℕ) (C : Fin n → TypedDAG ι κ) (x : ι → ℂ) :
    (stackFin n C).eval x = fun j => (C j.1).eval x j.2 := by
  induction n with
  | zero => funext ⟨i,j⟩; exact Fin.elim0 i
  | succ n ih =>
    funext ⟨i,j⟩
    refine Fin.cases ?_ (fun i => ?_) i <;> simp [stackFin, ih]

@[simp] theorem size_stack (C : τ → TypedDAG ι κ) :
    (stack C).size = ∑ i, (C i).size := by
  rw [stack, size_outputs, size_stackFin]
  exact (Fintype.equivFin τ).symm.sum_comp (fun i => (C i).size)
@[simp] theorem eval_stack (C : τ → TypedDAG ι κ) (x : ι → ℂ) :
    (stack C).eval x = fun j => (C j.1).eval x j.2 := by
  simp [stack, eval_stackFin, Function.comp_def]

@[simp] theorem size_parallel (C : TypedDAG ι κ) :
    (C.parallel τ).size = Fintype.card τ * C.size := by simp [parallel]
@[simp] theorem eval_parallel (C : TypedDAG ι κ) (x : τ × ι → ℂ) :
    (C.parallel τ).eval x = fun j => C.eval (fun i => x (j.1,i)) j.2 := by
  simp [parallel, Function.comp_def]

@[simp] theorem size_tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ) :
    (C.tensor D).size = Fintype.card ι * D.size + Fintype.card υ * C.size := by
  simp [tensor]

theorem eval_tensor (C : TypedDAG ι κ) (D : TypedDAG τ υ)
    (A : Matrix κ ι ℂ) (B : Matrix υ τ ℂ)
    (hC : ∀ x, C.eval x = A.mulVec x) (hD : ∀ x, D.eval x = B.mulVec x)
    (x : ι × τ → ℂ) : (C.tensor D).eval x = (A ⊗ₖ B).mulVec x := by
  funext j
  simp only [tensor, eval_outputs, eval_comp, eval_inputs, eval_parallel, Function.comp_apply,
    Prod.swap, hC, hD, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

end TypedDAG
end ExactFourier

end

section
/-! Charged scalar DAGs for the tensor-axis local maps used in the cascade. -/
namespace ExactFourier
open scoped Kronecker
namespace TypedDAG
variable {ι κ τ : Type} [Fintype ι] [Fintype κ] [Fintype τ]

theorem eval_blockCols (C : TypedDAG ι κ) (D : TypedDAG τ κ)
    (A : Matrix κ ι ℂ) (B : Matrix κ τ ℂ)
    (hC : ∀ x, C.eval x=A.mulVec x) (hD : ∀ x, D.eval x=B.mulVec x) (x : ι ⊕ τ → ℂ) :
    (blockCols C D).eval x = (Matrix.fromCols A B).mulVec x := by
  rw [blockCols,eval_comp,eval_fanout,eval_inputs,eval_inputs,eval_addPair,hC,hD,Matrix.fromCols_mulVec]
  rfl

theorem eval_scalar (c : ℂ) (C : TypedDAG ι κ) (A : Matrix κ ι ℂ)
    (hC : ∀ x, C.eval x=A.mulVec x) (x : ι → ℂ) :
    (scalar c C).eval x = (c • A).mulVec x := by
  simp only [scalar,eval_comp,eval_scale,hC,Matrix.smul_mulVec]
  rfl

variable {α : Type} [Fintype α] [DecidableEq α]

theorem eval_tensorPower
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (k : ℕ) (x : TensorAxis.Space α k → ℂ) :
    (tensorPower A k).eval x = (TensorAxis.power A k).mulVec x := by
  induction k with
  | zero => simp [tensorPower,TensorAxis.power]
  | succ k ih =>
    exact eval_tensor _ _ _ _ ih (eval_matrix A) x

theorem size_tensorPower (A : Matrix α α ℂ) (k : ℕ) :
    (tensorPower A k).size = 2*Fintype.card α*k*Fintype.card α^k := by
  induction k with
  | zero => simp [tensorPower]
  | succ k ih =>
    rw [tensorPower,size_tensor,ih,size_matrix,TensorAxis.card_space,pow_succ]
    ring

end TypedDAG
end ExactFourier

end

section
/-! Exact charged reconstruction of coefficient vectors from finitely many
scalar evaluations. All interpolation constants are prechosen and charged;
no pole avoidance or analytic limit is used. -/
namespace ExactFourier
open scoped BigOperators
namespace PolynomialDAG
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem nodes_injective (m : ℕ) : Function.Injective (nodes m) := by
  intro i j h
  apply Fin.ext
  dsimp [nodes] at h
  exact_mod_cast h

theorem coeff_interpolate (f : Polynomial ℂ) (m : ℕ) (hf : f.natDegree < m) (i : Fin m) :
    f.coeff i.val = ∑ j, weights m i j * f.eval (nodes m j) := by
  have hd : f.degree < (Finset.univ : Finset (Fin m)).card := by
    simp only [Finset.card_univ,Fintype.card_fin]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast hf)
  have h := congrArg (fun q : Polynomial ℂ => q.coeff i.val)
    (Lagrange.eq_interpolate (nodes_injective m).injOn hd)
  simpa [Lagrange.interpolate_apply,weights,Polynomial.finsetSum_coeff,mul_comm] using h

theorem size_reconstruct (m : ℕ) (C : Fin m → TypedDAG ι κ) :
    (reconstruct m C).size = (∑ i, (C i).size) + 2*m*m*Fintype.card κ := by
  simp [reconstruct,TypedDAG.size_stackFin]
  ring

theorem eval_reconstruct (A : Matrix κ ι (Polynomial ℂ)) (m : ℕ)
    (hA : ∀ i j, (A i j).natDegree < m) (C : Fin m → TypedDAG ι κ)
    (hC : ∀ j x, (C j).eval x = (evalMatrix A (nodes m j)).mulVec x) (x : ι → ℂ) :
    (reconstruct m C).eval x = (coefficients A m).mulVec x := by
  funext ⟨i,u⟩
  simp only [reconstruct,TypedDAG.eval_outputs,TypedDAG.eval_comp,TypedDAG.eval_inputs,
    TypedDAG.eval_parallel,TypedDAG.eval_matrix,TypedDAG.eval_stackFin,Function.comp_apply,
    Prod.swap,hC,Matrix.mulVec,dotProduct]
  change (∑ j, weights m i j * ∑ v, evalMatrix A (nodes m j) u v * x v) =
    ∑ v, (A u v).coeff i.val * x v
  simp_rw [coeff_interpolate _ m (hA _ _) i,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro j hj
  simp [evalMatrix,mul_assoc]

theorem eval_pad (A : Matrix κ ι (Polynomial ℂ)) (m t : ℕ)
    (hA : ∀ i j, (A i j).natDegree < m) (x : ι → ℂ) :
    (pad m t).eval ((coefficients A m).mulVec x) = (coefficients A t).mulVec x := by
  funext ⟨i,u⟩
  rw [pad,TypedDAG.eval_wires]
  by_cases hi : i.val < m
  · simp [hi,coefficients,Matrix.mulVec,dotProduct]
  · simp only [hi]
    symm
    apply Finset.sum_eq_zero
    intro v hv
    have hz := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hA u v) (Nat.le_of_not_gt hi))
    simp [coefficients,hz]

theorem exists_coefficients (A : Matrix κ ι (Polynomial ℂ)) (m t s : ℕ)
    (hA : ∀ i j, (A i j).natDegree < m)
    (hC : ∀ z : ℂ, ∃ C : TypedDAG ι κ, C.size ≤ s ∧ ∀ x, C.eval x=(evalMatrix A z).mulVec x) :
    ∃ C : TypedDAG ι (Fin t × κ), C.size ≤ m*s+2*m*m*Fintype.card κ ∧
      ∀ x, C.eval x=(coefficients A t).mulVec x := by
  classical
  choose C hs he using fun j : Fin m => hC (nodes m j)
  refine ⟨(pad m t).comp (reconstruct m C),?_,?_⟩
  · rw [TypedDAG.size_comp,size_pad,Nat.add_zero,size_reconstruct]
    apply Nat.add_le_add_right
    simpa using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j))
  · intro x
    rw [TypedDAG.eval_comp,eval_reconstruct A m hA C he,eval_pad A m t hA]

end PolynomialDAG
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.ClearedCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The O_K(k² n^k) evaluation DAG and O_K((k+1)³ n^k) coefficient
DAG for the literal polynomial state correction, uniform in truncation length. -/
namespace ExactFourier
open scoped Kronecker
open TensorAxis TypedDAG PolynomialDAG
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem eval_clearedDAG
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (b : ℂ) (L : Matrix α α ℂ) (T : Matrix α β ℂ)
    (k : ℕ) (x : States α β k → ℂ) :
    (clearedDAG b L T k).eval x = (cleared b L T k).mulVec x := by
  induction k with
  | zero => funext j; simp [clearedDAG,cleared]
  | succ k ih =>
    apply eval_blockCols _ _ _ _ ?_ ?_ x
    · exact fun y => eval_scalar _ _ _ (fun z => eval_tensor _ _ _ _ ih
        (fun z => by simp) z) y
    · exact fun y => eval_tensor _ _ _ _ (eval_tensorPower L k) (eval_matrix T) y

theorem size_clearedDAG
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (b : ℂ) (L : Matrix α α ℂ) (T : Matrix α β ℂ) (k : ℕ) :
    (clearedDAG b L T k).size ≤
      2*(Fintype.card β+Fintype.card α+1)*k^2*Fintype.card α^k := by
  let n := Fintype.card α
  let r := Fintype.card β
  change _ ≤ 2*(r+n+1)*k^2*n^k
  induction k with
  | zero => simp [clearedDAG]
  | succ k ih =>
    have hc : (clearedDAG b L T (k+1)).size = n*(clearedDAG b L T k).size +
        (2*r+2*n*k+2)*(n^k*n) := by
      simp [clearedDAG,size_tensorPower,Fintype.card_prod,card_space,n,r]
      ring
    rw [hc,pow_succ]
    calc
      n*(clearedDAG b L T k).size + (2*r+2*n*k+2)*(n^k*n) ≤
          (2*(r+n+1)*k^2 + (2*r+2*n*k+2))*(n^k*n) := by
        have h := Nat.mul_le_mul_left n ih
        nlinarith only [h]
      _ ≤ 2*(r+n+1)*(k+1)^2*(n^k*n) := by
        apply Nat.mul_le_mul_right
        nlinarith

theorem exists_cleared_coeff_dag (b : Polynomial ℂ) (L : Matrix α α (Polynomial ℂ))
    (T : Matrix α β (Polynomial ℂ)) :
    ∃ A : ℕ, ∀ k t, ∃ C : TypedDAG (States α β k) (Fin t × Space α k),
      C.size ≤ A*(k+1)^3*Fintype.card α^k ∧
      ∀ x, C.eval x=(coefficients (cleared b L T k) t).mulVec x := by
  obtain ⟨d,hd⟩ := exists_cleared_degree b L T
  let a := 2*(Fintype.card β+Fintype.card α+1)
  refine ⟨(d+1)*a+2*(d+1)^2,?_⟩
  intro k t
  have hcirc : ∀ z : ℂ, ∃ C : TypedDAG (States α β k) (Space α k),
      C.size ≤ a*k^2*Fintype.card α^k ∧
      ∀ x, C.eval x=(evalMatrix (cleared b L T k) z).mulVec x := by
    intro z
    refine ⟨clearedDAG (b.eval z) (L.map (Polynomial.evalRingHom z)) (T.map (Polynomial.evalRingHom z)) k,
      size_clearedDAG _ _ _ k,?_⟩
    intro x
    rw [eval_clearedDAG]
    change _ = ((cleared b L T k).map (Polynomial.evalRingHom z)).mulVec x
    rw [map_cleared]
    rfl
  obtain ⟨C,hC,he⟩ := exists_coefficients (cleared b L T k) (k*d+1) t
    (a*k^2*Fintype.card α^k) (fun i j => Nat.lt_succ_of_le (hd k i j)) hcirc
  refine ⟨C,le_trans hC ?_,he⟩
  rw [card_space]
  have hm : k*d+1 ≤ (d+1)*(k+1) := by nlinarith
  have hk : k^2 ≤ (k+1)^2 := Nat.pow_le_pow_left (by omega) 2
  have h1 := Nat.mul_le_mul hm (Nat.mul_le_mul_left a hk)
  have h2 := Nat.mul_le_mul hm hm
  calc
    (k*d+1)*(a*k^2*Fintype.card α^k)+2*(k*d+1)*(k*d+1)*Fintype.card α^k =
        ((k*d+1)*(a*k^2)+2*((k*d+1)^2))*Fintype.card α^k := by ring
    _ ≤ (((d+1)*a+2*(d+1)^2)*(k+1)^3)*Fintype.card α^k := by
      apply Nat.mul_le_mul_right
      have hp : (k+1)^2 ≤ (k+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    _ = _ := by ring

end Cascade
end ExactFourier

end

section
/-! Exact finite elimination of initial-state contamination. No corner principle
is used: only the already proved triangular monotonicity and dirty shear replay. -/
namespace ExactFourier
open scoped Kronecker BigOperators

namespace TypedDAG
variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem circuit_eval_of_matrix (C : TypedDAG ι κ) (A : Matrix κ ι ℂ)
    (hC : ∀ x, C.eval x = A.mulVec x) (x : Fin (Fintype.card ι) → ℂ) :
    C.circuit.eval x =
      (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) A).mulVec x := by
  funext j
  have h := congrFun (hC (x ∘ Fintype.equivFin ι)) ((Fintype.equivFin κ).symm j)
  simp only [eval, Function.comp_def, Equiv.apply_symm_apply] at h
  rw [h]
  simp only [Matrix.mulVec, dotProduct, Matrix.reindex_apply, Matrix.submatrix_apply]
  simpa only [Equiv.apply_symm_apply] using ((Fintype.equivFin ι).symm.sum_comp
    (fun i => A ((Fintype.equivFin κ).symm j) i * x (Fintype.equivFin ι i))).symm

theorem shear_price (p : MatrixPrice) [DecidableEq ι] [DecidableEq κ]
    (C : TypedDAG ι κ) (A : Matrix κ ι ℂ) (hC : ∀ x, C.eval x = A.mulVec x) :
    p.value (rectangularShear A) ≤ 8 * (C.size : ℝ) + 2 * Fintype.card κ := by
  have he : Matrix.reindex (Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin ι))
        (Equiv.sumCongr (Fintype.equivFin κ) (Fintype.equivFin ι)) (rectangularShear A) =
      rectangularShear (Matrix.reindex (Fintype.equivFin κ) (Fintype.equivFin ι) A) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.reindex_apply, rectangularShear, Matrix.fromBlocks, Matrix.one_apply]
  have h := p.rectangularShear_bound C.circuit _ (circuit_eval_of_matrix C A hC)
  rw [← he, p.reindex _ _ (rectangularShear_unit A)] at h
  exact h
end TypedDAG

namespace MatrixPrice
variable (p : MatrixPrice) {α β : Type} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem eliminate_top_right (A P : Matrix α α ℂ) (E Q : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ)
    (hK : IsUnit (Matrix.fromBlocks A E B D)) (hA : IsUnit A) (hP : IsUnit P)
    (hQ : A * P * Q = E) :
    p.value A ≤ p.value (Matrix.fromBlocks A E B D) +
      2 * p.value P + p.value (rectangularShear Q) := by
  let K := Matrix.fromBlocks A E B D
  let PP := Matrix.fromBlocks P 0 0 (1 : Matrix β β ℂ)
  let L := K * PP * rectangularShear (-Q)
  have hPP : IsUnit PP := Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hP,isUnit_one⟩
  have hL : IsUnit L := (hK.mul hPP).mul (rectangularShear_unit (-Q))
  have he : L = Matrix.fromBlocks (A*P) 0 (B*P) (D-B*P*Q) := by
    dsimp [L,K,PP,rectangularShear]
    simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero,       add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg]
    rw [hQ, neg_add_cancel]
    simp only [sub_eq_add_neg, add_comm]
  have hD : IsUnit (D-B*P*Q) :=
    (Matrix.isUnit_fromBlocks_zero₁₂.mp (he ▸ hL)).2
  have hlower := p.lower_triangular (A*P) (B*P) (D-B*P*Q) (hA.mul hP) hD
  rw [← he] at hlower
  have hnonneg := p.nonneg _ hD
  have h1 := p.mul_le K PP hK hPP
  have h2 := p.mul_le (K*PP) (rectangularShear (-Q)) (hK.mul hPP)
    (rectangularShear_unit (-Q))
  change p.value L ≤ _ at h2
  rw [p.rectangularShear_neg] at h2
  have hpp : p.value PP = p.value P := p.identity_pad P hP
  rw [hpp] at h1
  have hi : IsUnit P⁻¹ := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h3 := p.mul_le (A*P) P⁻¹ (hA.mul hP) hi
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv P (Matrix.isUnit_iff_isUnit_det _ |>.mp hP),
    Matrix.mul_one, p.inverse P hP] at h3
  dsimp only [K] at h1 h2
  linarith

end MatrixPrice
end ExactFourier

end

section
/-! Radix-two algebra used by the scalar-convolution bound in the missing main
proof. This is the ordinary O(n log n) support algorithm, NOT a main saving. -/
namespace ExactFourier.RadixTwo
open scoped BigOperators
open Polynomial

theorem sum_even_odd {R : Type*} [AddCommMonoid R] (n : ℕ) (f : Fin (n+n) → R) :
    ∑ i, f i = (∑ i : Fin n, f (evenIndex n i)) + ∑ i : Fin n, f (oddIndex n i) := by
  rw [← Fintype.sum_equiv (parityEquiv n) (fun p => f (parityEquiv n p)) f (fun _ => rfl)]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  exact Finset.sum_add_distrib

theorem power_even (ω : ℂ) (r j : ℕ) : ω^(r*(2*j)) = (ω^2)^(r*j) := by
  rw [← pow_mul]
  congr 1
  ring

theorem power_odd (ω : ℂ) (r j : ℕ) : ω^(r*(2*j+1)) = ω^r * (ω^2)^(r*j) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  ring

theorem evalAt_split (n : ℕ) (ω : ℂ) (x : Fin (n+n) → ℂ) (r : ℕ) :
    evalAt (n+n) ω x r = evalAt n (ω^2) (x ∘ evenIndex n) r +
      ω^r * evalAt n (ω^2) (x ∘ oddIndex n) r := by
  rw [evalAt, sum_even_odd]
  simp only [evenIndex, oddIndex, power_even, power_odd, Function.comp_apply, evalAt,
    Finset.mul_sum, mul_assoc]

theorem evalAt_periodic (n : ℕ) (ω : ℂ) (hω : ω^n=1) (x : Fin n → ℂ) (r : ℕ) :
    evalAt n ω x (r+n) = evalAt n ω x r := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_mul, pow_add, pow_mul ω n j.val, hω, one_pow, mul_one]

theorem square_period {n : ℕ} (ω : ℂ) (hω : ω^n = -1) : (ω^2)^n = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, hω]
  norm_num

/-- First and second frequency halves are the sum and difference butterfly. -/
theorem eval_split (n : ℕ) (ω : ℂ) (hω : ω^n = -1) (x : Fin (n+n) → ℂ) :
    eval (n+n) ω x = Fin.addCases
      (fun i => eval n (ω^2) (x ∘ evenIndex n) i + ω^i.val * eval n (ω^2) (x ∘ oddIndex n) i)
      (fun i => eval n (ω^2) (x ∘ evenIndex n) i - ω^i.val * eval n (ω^2) (x ∘ oddIndex n) i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa only [eval, Fin.val_castAdd, Fin.addCases_left] using evalAt_split n ω x j.val
  · simp only [eval, Fin.val_natAdd, Fin.addCases_right]
    rw [Nat.add_comm n j.val, evalAt_split,
      evalAt_periodic n (ω^2) (square_period ω hω),
      evalAt_periodic n (ω^2) (square_period ω hω), pow_add, hω]
    ring

/-- Orthogonality of the exact n-th root evaluation matrix. -/
theorem orthogonality {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (i k : Fin n) :
    (∑ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(k.val*j.val)) =
      if i=k then (n : ℂ) else 0 := by
  have hn0 := Nat.ne_of_gt hn
  have hω0 := hω.ne_zero hn0
  have he : ∀ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(k.val*j.val) =
      (ω^k.val / ω^i.val)^j.val := by
    intro j
    simp only [div_eq_mul_inv, mul_pow, inv_pow, pow_mul]
    rw [mul_comm]
  simp only [he]
  by_cases hik : i=k
  · subst k
    simp [hω0]
  · rw [ite_eq_right hik, Fin.sum_univ_eq_sum_range]
    have hne : ω^k.val / ω^i.val ≠ 1 := by
      intro h
      have hh : ω^k.val = ω^i.val := (div_eq_one_iff_eq (pow_ne_zero _ hω0)).mp h
      exact hik ((Fin.ext (hω.pow_inj k.isLt i.isLt hh)).symm)
    rw [geom_sum_eq hne]
    have hp : (ω^k.val / ω^i.val)^n = 1 := by
      rw [div_pow, ← pow_mul, Nat.mul_comm k.val n, pow_mul, hω.pow_eq_one,
        ← pow_mul, Nat.mul_comm i.val n, pow_mul, hω.pow_eq_one]
      simp
    rw [hp]
    simp

/-- The inverse FFT uses the inverse root and one scalar normalization. -/
theorem eval_inverse {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (x : Fin n → ℂ) :
    eval n ω⁻¹ (eval n ω x) = fun i => (n : ℂ) * x i := by
  classical
  funext i
  simp only [eval, evalAt, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul]
  have ho : ∀ k : Fin n,
      (∑ j : Fin n, (ω⁻¹)^(i.val*j.val) * ω^(j.val*k.val)) =
        if i=k then (n : ℂ) else 0 := by
    intro k
    simpa only [Nat.mul_comm k.val] using orthogonality hn ω hω i k
  simp only [ho]
  simp

/-- Polynomial evaluation of the vector of coefficients is exactly the DFT. -/
theorem eval_ofFn (n : ℕ) (ω : ℂ) (x : Fin n → ℂ) (i : Fin n) :
    (Polynomial.ofFn n x).eval (ω^i.val) = eval n ω x i := by
  classical
  rw [Polynomial.ofFn_eq_sum_monomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_monomial, eval, evalAt, pow_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_comm]

/-- Transform, multiply by precomputed scalar evaluations, inverse transform.
The only degree condition is that the product is represented by fewer than n
coefficients, so there is no wraparound. -/
theorem convolution_formula {n : ℕ} (hn : 0<n) (ω : ℂ) (hω : IsPrimitiveRoot ω n)
    (f g : ℂ[X]) (hfg : (f*g).natDegree < n) :
    eval n ω⁻¹ (fun i => (n : ℂ)⁻¹ * f.eval (ω^i.val) * g.eval (ω^i.val)) =
      fun i => (f*g).coeff i.val := by
  classical
  let y : Fin n → ℂ := fun i => (f*g).coeff i.val
  have hy : Polynomial.ofFn n y = f*g := by
    ext j
    by_cases hj : j<n
    · simp [Polynomial.ofFn_coeff_eq_val_of_lt _ hj, y]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]
      exact (Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)).symm
  have hev : (fun i : Fin n => f.eval (ω^i.val) * g.eval (ω^i.val)) = eval n ω y := by
    funext i
    rw [← Polynomial.eval_mul, ← hy, eval_ofFn]
  have hscale : ∀ (z : Fin n → ℂ) (c : ℂ),
      eval n ω⁻¹ (fun i => c*z i) = fun i => c*eval n ω⁻¹ z i := by
    intro z c
    funext i
    simp only [eval, evalAt, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [mul_assoc (n : ℂ)⁻¹]
  have hev' (i : Fin n) : f.eval (ω^i.val) * g.eval (ω^i.val) = eval n ω y i :=
    congrFun hev i
  simp_rw [hev']
  rw [hscale, eval_inverse hn ω hω]
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  funext i
  simp [y, hnC]

end ExactFourier.RadixTwo

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.FFTCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The exact radix-two DAG needed by scalar convolution in the missing main proof.
All multiplies by the roots and normalization scalars are charged. -/
namespace ExactFourier.RadixTwo
open scoped BigOperators

theorem exists_fft_dag (k : ℕ) (ω : ℂ) (hω : IsPrimitiveRoot ω (2^k)) :
    ∃ C : LinearDAG (2^k) (2^k), C.size ≤ 3*k*2^k ∧
      ∀ x, C.eval x = eval (2^k) ω x := by
  induction k generalizing ω with
  | zero =>
      refine ⟨LinearDAG.wires (fun i => i.castSucc), by simp [LinearDAG.wires], ?_⟩
      intro x
      funext i
      have hi : i = 0 := by
        apply Fin.ext
        have h := i.isLt
        simp only [pow_zero] at h
        omega
      simp [LinearDAG.eval_wires, eval, evalAt, hi]
  | succ k ih =>
      have hn : 0 < 2^k := pow_pos (by decide) _
      have hEq : 2^(k+1) = 2^k + 2^k := by rw [pow_succ]; omega
      have hs : IsPrimitiveRoot (ω^2) (2^k) :=
        IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ]; omega)
      have hh : ω^(2^k) = -1 :=
        (IsPrimitiveRoot.pow (pow_pos (by decide) _) hω (by rw [pow_succ])).eq_neg_one_of_two_right
      obtain ⟨C, hsize, heval⟩ := ih (ω^2) hs
      let D := ((C.withInputs (evenIndex (2^k))).fanout
        (C.withInputs (oddIndex (2^k)))).butterflies (fun i => ω^i.val)
      have hDsize : D.size ≤ 3*(k+1)*(2^k+2^k) := by
        simp only [D, LinearDAG.butterflies, LinearDAG.size_fanout,
          LinearDAG.size_withInputs]
        nlinarith
      have hDeval : ∀ x, D.eval x = eval (2^k+2^k) ω x := by
        intro x
        dsimp only [D]
        rw [LinearDAG.eval_butterflies]
        simp only [LinearDAG.eval_fanout]
        simp only [Fin.addCases_left, Fin.addCases_right,
          LinearDAG.eval_withInputs, heval]
        exact (eval_split (2^k) ω hh x).symm
      rw [hEq]
      exact ⟨D, hDsize, hDeval⟩

end ExactFourier.RadixTwo

end

section
/-! The uniform scalar-convolution main dependency. All operations are charged;
truncated series and constants may vary with the requested length. -/
namespace ExactFourier.ScalarConvolution
open Polynomial CoefficientTime RadixTwo
open scoped BigOperators

theorem eval_padding (t m : ℕ) (x : Fin t → ℂ) :
    (LinearDAG.wires (padIndex t m)).eval x = (padded x : Fin m → ℂ) := by
  funext i
  rw [LinearDAG.eval_wires]
  by_cases h : i.val < t
  · simp only [padIndex, dite_eq_left h, padded]
    exact @Fin.snoc_castSucc t (fun _ => ℂ) 0 x ⟨i.val,h⟩
  · simp only [padIndex, dite_eq_right h, padded, Fin.snoc_last]

theorem ofFn_padded {t m : ℕ} (htm : t ≤ m) (x : Fin t → ℂ) :
    Polynomial.ofFn m (padded x) = Polynomial.ofFn t x := by
  ext j
  by_cases hj : j < t
  · have hjm : j < m := hj.trans_le htm
    rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hjm,
      Polynomial.ofFn_coeff_eq_val_of_lt _ hj]
    simp [padded, hj]
  · have hjt : t ≤ j := by omega
    rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ hjt]
    by_cases hjm : j < m
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hjm]
      simp [padded, hj]
    · rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega)]

theorem diagonalDAG_eval {m : ℕ} (c : Fin m → ℂ) (x : Fin m → ℂ) :
    (diagonalDAG c).eval x = fun i => c i * x i := by
  rw [diagonalDAG, LinearDAG.eval_layer]
  funext i
  simp [Gate.eval]

/-- Polynomial convolution on any containing radix-two length. -/
theorem convolution_dag_at_power (k t : ℕ) (ht : 0 < t) (htm : 2*t ≤ 2^k)
    (f : ℂ[X]) (hf : f.natDegree < t) :
    ∃ C : LinearDAG t t, C.size ≤ (6*k+1)*2^k ∧
      ∀ x i, C.eval x i = (f * Polynomial.ofFn t x).coeff i.val := by
  have hm : 0 < 2^k := pow_pos (by decide) _
  let ω := zeta (2^k)
  have hω : IsPrimitiveRoot ω (2^k) :=
    Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt hm)
  obtain ⟨F, hFsize, hFeval⟩ := exists_fft_dag k ω hω
  obtain ⟨I, hIsize, hIeval⟩ := exists_fft_dag k ω⁻¹ hω.inv
  let c : Fin (2^k) → ℂ := fun i => (2^k : ℂ)⁻¹ * f.eval (ω^i.val)
  let D := I.comp ((diagonalDAG c).comp (F.comp (LinearDAG.wires (padIndex t (2^k)))))
  let out : Fin t → Fin (2^k) := fun i => ⟨i.val, by have := i.isLt; omega⟩
  refine ⟨D.withOutputs out, ?_, ?_⟩
  · change D.size ≤ _
    dsimp only [D, LinearDAG.comp, diagonalDAG, LinearDAG.layer, LinearDAG.wires]
    nlinarith
  · intro x i
    change D.eval x (out i) = _
    dsimp only [D]
    rw [LinearDAG.eval_comp, LinearDAG.eval_comp, LinearDAG.eval_comp,
      eval_padding, hFeval, diagonalDAG_eval, hIeval]
    have hev (j : Fin (2^k)) : eval (2^k) ω (padded x) j =
        (Polynomial.ofFn t x).eval (ω^j.val) := by
      rw [← eval_ofFn, ofFn_padded (by omega)]
    simp_rw [hev]
    have hfg : (f * Polynomial.ofFn t x).natDegree < 2^k := by
      have hx := Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ t) x
      have hh := Polynomial.natDegree_mul_le (p := f) (q := Polynomial.ofFn t x)
      omega
    have hconv := convolution_formula hm ω hω f (Polynomial.ofFn t x) hfg
    simpa [c, out] using congrFun hconv (out i)

/-- Uniform linear-DAG construction, with logarithmic cost independent of coefficients. -/
theorem exists_truncation_dag (t : ℕ) (ht : 0 < t) (f : PowerSeries ℂ) :
    ∃ C : LinearDAG t t, C.size ≤ 52 * t * (Nat.log 2 t + 1) ∧
      ∀ x, C.eval x = (truncMatrix t f).mulVec x := by
  let k := Nat.log 2 t + 2
  have hl := Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2) t
  have hsmall : 2*t ≤ 2^k := by
    dsimp [k]
    rw [pow_add]
    simp only [Nat.succ_eq_add_one, pow_add, pow_one] at hu
    norm_num at ⊢
    omega
  have hlarge : 2^k ≤ 4*t := by
    dsimp [k]
    rw [pow_add]
    norm_num
    omega
  have hdeg : (PowerSeries.trunc t f).natDegree < t := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
    exact PowerSeries.natDegree_trunc_lt f s
  obtain ⟨C, hC, hEval⟩ := convolution_dag_at_power k t ht hsmall
    (PowerSeries.trunc t f) hdeg
  refine ⟨C, ?_, ?_⟩
  · calc
      C.size ≤ (6*k+1)*2^k := hC
      _ ≤ (6*k+1)*(4*t) := Nat.mul_le_mul_left _ hlarge
      _ ≤ 52*t*(Nat.log 2 t+1) := by dsimp [k]; nlinarith
  · intro x
    funext i
    rw [hEval]
    rw [← Polynomial.coeff_coe, Polynomial.coe_mul, coeff_mul_truncated]
    simp only [Matrix.mulVec, dotProduct, truncMatrix]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hji : j.val ≤ i.val
    · have hlt : i.val-j.val < t := by have := i.isLt; omega
      simp [hji, PowerSeries.coeff_trunc, hlt,
        Polynomial.ofFn_coeff_eq_val_of_lt _ j.isLt]
    · simp [hji]

/-- Inversion commutes exactly with truncated scalar multiplication. -/
theorem truncMatrix_inv (t : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (truncMatrix t f)⁻¹ = truncMatrix t f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← truncMatrix_mul, PowerSeries.mul_inv_cancel _ hf, truncMatrix_one]

theorem price_truncation_nat (p : MatrixPrice) (t : ℕ) (ht : 0 < t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (truncMatrix t f) ≤ 627 * (t : ℝ) * (Nat.log 2 t + 1) := by
  obtain ⟨C, hC, hCe⟩ := exists_truncation_dag t ht f
  obtain ⟨D, hD, hDe⟩ := exists_truncation_dag t ht f⁻¹
  have hU := trunc_isUnit t f (isUnit_iff_ne_zero.mpr hf)
  have hInv : ∀ x, D.eval x = (truncMatrix t f)⁻¹.mulVec x := by
    intro x
    rw [truncMatrix_inv t f hf]
    exact hDe x
  have hb := p.twoWay_DAG_bound (truncMatrix t f) hU C D hCe hInv
  have hc' : (C.size : ℝ) ≤ 52 * (t : ℝ) * (Nat.log 2 t + 1) := by exact_mod_cast hC
  have hd' : (D.size : ℝ) ≤ 52 * (t : ℝ) * (Nat.log 2 t + 1) := by exact_mod_cast hD
  have ht' : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hl' : (0 : ℝ) ≤ Nat.log 2 t := Nat.cast_nonneg _
  nlinarith

/-- The literal O(t log(2t)) estimate, with one absolute constant, uniform in f and t. -/
theorem price_truncation (p : MatrixPrice) (t : ℕ) (ht : 0 < t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (truncMatrix t f) ≤ (627 / Real.log 2) * (t : ℝ) * Real.log (2*t) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2 : ℝ) ^ Nat.log 2 t ≤ t := by
    exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
  have hl : (Nat.log 2 t : ℝ) * Real.log 2 ≤ Real.log t := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by norm_num : (0 : ℝ)<2) _) hp
  have hb : (Nat.log 2 t : ℝ)+1 ≤ Real.log (2*t) / Real.log 2 := by
    apply (le_div_iff₀ h2).mpr
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt ht')]
    linarith
  calc
    p.value (truncMatrix t f) ≤ 627*(t : ℝ)*(Nat.log 2 t+1) :=
      price_truncation_nat p t ht f hf
    _ ≤ 627*(t : ℝ)*(Real.log (2*t) / Real.log 2) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = (627 / Real.log 2) * (t : ℝ) * Real.log (2*t) := by ring

end ExactFourier.ScalarConvolution

end

section
/-! Unsigned scalar preprocessing and exact elimination of the cleared
initial-state response, using triangular monotonicity only. -/
namespace ExactFourier
open scoped Kronecker
open CoefficientTime TensorTools
namespace CoefficientTime
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem blockTrunc_smul_one (t : ℕ) (q : PowerSeries ℂ) :
    blockTruncHom t (q • (1 : Matrix α α (PowerSeries ℂ))) =
      truncMatrix t q ⊗ₖ (1 : Matrix α α ℂ) := by
  ext i j
  by_cases h : i.2=j.2 <;> by_cases ht : j.1.val ≤ i.1.val <;>
    simp [blockTruncHom_apply,truncMatrix,Matrix.kroneckerMap_apply,Matrix.one_apply,h,ht]

theorem scalar_correction
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (H : Matrix α α (PowerSeries ℂ))
    (E Q : Matrix α β (PowerSeries ℂ)) (q : PowerSeries ℂ)
    (hq : PowerSeries.constantCoeff q ≠ 0) (hQ : H*Q=q•E) (t : ℕ) :
    blockTruncHom t H * (truncMatrix t q⁻¹ ⊗ₖ (1 : Matrix α α ℂ)) *
      coefficientColumns t Q = coefficientColumns t E := by
  rw [← blockTrunc_smul_one,← map_mul,blocks_mul_columns,
    Matrix.mul_smul,Matrix.mul_one,Matrix.smul_mul,hQ,smul_smul,
    PowerSeries.inv_mul_cancel _ hq,one_smul]

end CoefficientTime
namespace MatrixPrice
variable (p : MatrixPrice) {α β : Type} [Fintype α] [Fintype β]
  [DecidableEq α] [DecidableEq β]

theorem eliminate_series (H : Matrix α α (PowerSeries ℂ))
    (E Q : Matrix α β (PowerSeries ℂ)) (q : PowerSeries ℂ) (t : ℕ)
    (K : Matrix ((Fin t × α) ⊕ β) ((Fin t × α) ⊕ β) ℂ)
    (hK : IsUnit K) (hH : IsUnit (H.map PowerSeries.constantCoeff))
    (hdata : K.toBlocks₁₁=blockTruncHom t H)
    (hstate : K.toBlocks₁₂=coefficientColumns t E)
    (hq : PowerSeries.constantCoeff q ≠ 0) (hQ : H*Q=q•E) :
    p.value (blockTruncHom t H) ≤ p.value K +
      2*(Fintype.card α : ℝ)*p.value (truncMatrix t q⁻¹) +
      p.value (rectangularShear (coefficientColumns t Q)) := by
  have hqi : PowerSeries.constantCoeff q⁻¹ ≠ 0 := by simpa using inv_ne_zero hq
  have hP := trunc_isUnit t q⁻¹ (isUnit_iff_ne_zero.mpr hqi)
  have he : Matrix.fromBlocks (blockTruncHom t H) (coefficientColumns t E)
      K.toBlocks₂₁ K.toBlocks₂₂ = K := by rw [← hdata,← hstate]; exact Matrix.fromBlocks_toBlocks K
  have h := p.eliminate_top_right (blockTruncHom t H)
    (truncMatrix t q⁻¹ ⊗ₖ (1 : Matrix α α ℂ)) (coefficientColumns t E) (coefficientColumns t Q)
    K.toBlocks₂₁ K.toBlocks₂₂ (he.symm ▸ hK) (blockTrunc_isUnit t H hH)
    (unit_tensor _ _ hP isUnit_one) (scalar_correction H E Q q hq hQ t)
  rw [he,p.tensor _ _ hP isUnit_one,p.one] at h
  simpa only [mul_zero,add_zero,mul_assoc] using h

end MatrixPrice
end ExactFourier

end

section
namespace ExactFourier
open scoped Kronecker
open TensorAxis CoefficientTime PolynomialDAG
namespace Cascade
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem q_constant (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hM : IsUnit M) (k : ℕ) :
    PowerSeries.constantCoeff (CellPoly.ps ((CellPoly.b M C B D)^k)) ≠ 0 := by
  have hd : M.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hM)
  simpa [Polynomial.coeff_zero_eq_eval_zero] using pow_ne_zero k hd

theorem coefficients_eq_columns {σ ρ : Type} [Fintype σ] [Fintype ρ]
    (Q : Matrix σ ρ (Polynomial ℂ)) (t : ℕ) :
    coefficients Q t = coefficientColumns t (Q.map CellPoly.ps) := by
  ext i j
  simp [coefficients,coefficientColumns]

theorem uniform_bound (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hM : IsUnit M)
    (hK : IsUnit (Matrix.fromBlocks M C B D)) :
    ∃ CK : ℝ, 0 ≤ CK ∧ ∀ k t : ℕ, 0 < t →
      p.value (blockTruncHom t (power (CellSeries.transfer M C B D) k)) ≤
      (t : ℝ)*Fintype.card (Fibers α k)*p.value (Matrix.fromBlocks M C B D) +
      CK*((Fintype.card α : ℝ)^k*t*Real.log (2*t) + (k+1:ℝ)^3*Fintype.card α^k) := by
  obtain ⟨A,hA⟩ := exists_cleared_coeff_dag (CellPoly.b M C B D) (CellPoly.L M C B D) (CellPoly.T M C B D)
  let CK : ℝ := 1256 / Real.log 2 + 8*A
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨CK,by dsimp [CK]; positivity,?_⟩
  intro k t ht
  let H := power (CellSeries.transfer M C B D) k
  let E := response (CellSeries.transfer M C B D) (CellSeries.state C D) k
  let Q := cleared (CellPoly.b M C B D) (CellPoly.L M C B D) (CellPoly.T M C B D) k
  let q := CellPoly.ps ((CellPoly.b M C B D)^k)
  have hH : IsUnit (H.map PowerSeries.constantCoeff) := by
    dsimp only [H]
    rw [map_power,CellSeries.constant_transfer]
    exact unit_power M hM k
  have hq : PowerSeries.constantCoeff q ≠ 0 := q_constant M C B D hM k
  have hqi : PowerSeries.constantCoeff q⁻¹ ≠ 0 := by simpa using inv_ne_zero hq
  have helim := p.eliminate_series H E (Q.map CellPoly.ps) q t
    (run (Matrix.fromBlocks M C B D) t k) (unit _ hK t k) hH
    (data_block M C B D t k) (state_block M C B D t k) hq (cell_clearing M C B D k)
  obtain ⟨cq,hcq,heq⟩ := hA k t
  rw [coefficients_eq_columns] at heq
  have hshear := cq.shear_price p (coefficientColumns t (Q.map CellPoly.ps)) heq
  have hcq' : (cq.size : ℝ) ≤ (A : ℝ)*(k+1:ℝ)^3*Fintype.card α^k := by exact_mod_cast hcq
  have hprice := price p (Matrix.fromBlocks M C B D) hK t k
  have hp := ScalarConvolution.price_truncation p t ht q⁻¹ hqi
  have hN : (0:ℝ) ≤ Fintype.card (Space α k) := Nat.cast_nonneg _
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ) ≤ 2*Fintype.card (Space α k))
  rw [Fintype.card_prod,Fintype.card_fin,card_space] at hshear
  rw [card_space] at helim hp'
  push_cast at helim hshear hp'
  have ht' : (1:ℝ) ≤ t := by exact_mod_cast ht
  have hlog : Real.log 2 ≤ Real.log (2*(t : ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hlog' : 1 ≤ Real.log (2*(t : ℝ)) / Real.log 2 := (le_div_iff₀ hl2).mpr (by simpa using hlog)
  have htn : (0:ℝ) ≤ (Fintype.card α : ℝ)^k*t := by positivity
  have hpad := mul_le_mul_of_nonneg_left hlog' (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) htn)
  have hlognn : 0 ≤ (Fintype.card α : ℝ)^k*t*Real.log (2*t) :=
    mul_nonneg htn (hl2.le.trans hlog)
  have hpoly : 0 ≤ (k+1:ℝ)^3*(Fintype.card α : ℝ)^k := by positivity
  change p.value (blockTruncHom t H) ≤ _
  dsimp [CK]
  have hdiv : (0:ℝ) ≤ 1256/Real.log 2 := by positivity
  have hAcross : 0 ≤ 8*(A:ℝ)*((Fintype.card α : ℝ)^k*t*Real.log (2*t)) := by positivity
  have hCcross := mul_nonneg hdiv hpoly
  simp only [div_eq_mul_inv] at hp' hpad hCcross ⊢
  nlinarith only [helim,hshear,hcq',hprice,hp',hpad,hAcross,hCcross]

end Cascade
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Boundary
open Polynomial
open scoped BigOperators

/-- Inputs strictly before the final d times do not cross the coefficient boundary. -/
theorem prefix_quotient_zero (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d t b : ℕ} (ht : ℓ.natDegree = t) (hf : f.natDegree ≤ d) (hb : b + d < t) :
    (f * X ^ b) /ₘ ℓ = 0 := by
  apply (divByMonic_eq_zero_iff hℓ).mpr
  rw [degree_eq_natDegree hℓ.ne_zero, ht]
  apply (degree_le_natDegree).trans_lt
  exact_mod_cast (calc
    (f * X ^ b).natDegree ≤ f.natDegree + (X ^ b : ℂ[X]).natDegree := natDegree_mul_le
    _ ≤ d + b := by simpa using Nat.add_le_add_right hf b
    _ < t := by omega)

/-- The quotient, with sign reversed, has strictly fewer than d coefficients. -/
theorem quotient_degree_lt (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d t b : ℕ} (ht : ℓ.natDegree = t) (hd : 0 < d)
    (hf : f.natDegree ≤ d) (hb : b < t) :
    ((f * X ^ b) /ₘ ℓ).natDegree < d := by
  rw [natDegree_divByMonic _ hℓ, ht]
  have h : (f * X ^ b).natDegree ≤ d + b := by
    exact natDegree_mul_le.trans (by simpa using Nat.add_le_add_right hf b)
  omega

/-- Exact division of a shifted matrix entry. This keeps the generator coefficients
on the left, ready for the ordered J_i*G_j matrix formula. -/
theorem quotient_shift_expansion (ℓ f : ℂ[X]) (hℓ : ℓ.Monic)
    {d : ℕ} (hf : f.natDegree ≤ d) (b : ℕ) :
    (f * X ^ b) /ₘ ℓ =
      ∑ j ∈ Finset.range (d + 1), f.coeff j • ((X ^ (b + j) : ℂ[X]) /ₘ ℓ) := by
  have hF : f * X ^ b =
      ∑ j ∈ Finset.range (d + 1), f.coeff j • (X ^ (b + j) : ℂ[X]) := by
    conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := d+1) (by omega)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_eq_C_mul, mul_assoc, ← pow_add, Nat.add_comm j b]
  change quotientLinear ℓ hℓ (f * X ^ b) = _
  rw [hF, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp

/-- Entrywise modulus reduction differs from time truncation by minus the modulus
 times precisely the quotient above. No bounds on coefficients are imposed. -/
theorem boundary_difference (ℓ f : ℂ[X]) (b : ℕ) :
    (f * X ^ b) %ₘ ℓ - f * X ^ b = -ℓ * ((f * X ^ b) /ₘ ℓ) := by
  rw [modByMonic_eq_sub_mul_div]
  ring

theorem polynomial_ordered_expansion (η ℓ f g : ℂ[X]) (hℓ : ℓ.Monic)
    {d e : ℕ} (hg : g.natDegree ≤ d) (hf : f.natDegree ≤ e) (b : ℕ) :
    η * f * (-((g * X ^ b) /ₘ ℓ)) =
      ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (d+1),
        (f.coeff i * g.coeff j) • (-(η * X ^ i * ((X ^ (b+j) : ℂ[X]) /ₘ ℓ))) := by
  rw [quotient_shift_expansion ℓ g hℓ hg]
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' (n := e+1) (by omega)]
  simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_neg_distrib,
    mul_neg, smul_eq_C_mul]
  apply congrArg Neg.neg
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul]
  ring

/-- Exact ordered-span part of the coefficient-boundary comparison. There is no
commutation hypothesis on any pair of spatial coefficient matrices. -/
theorem ordered_span {ι : Type} [Fintype ι] (η ℓ : ℂ[X]) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι ℂ[X]) {d e : ℕ}
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e) (a b : ℕ) :
    coefficientMatrix (weightedCorrection η ℓ J G b) a =
      ∑ i ∈ Finset.range (e+1), ∑ j ∈ Finset.range (d+1),
        orderedWeight η ℓ a b i j • (coefficientMatrix J i * coefficientMatrix G j) := by
  classical
  ext u v
  simp only [coefficientMatrix, weightedCorrection, finsetSum_coeff,
    polynomial_ordered_expansion η ℓ _ _ hℓ (hG _ _) (hJ _ _) b,
    coeff_smul, coeff_neg]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.mul_apply,
    coefficientMatrix, orderedWeight, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- The prefix correction J*v has no coefficients at times a>=e+d. -/
theorem prefix_row_vanishes {ι : Type} [Fintype ι] (ℓ : ℂ[X]) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι ℂ[X]) {d e t a b : ℕ}
    (ht : ℓ.natDegree = t) (hd : 0 < d)
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e)
    (hb : b < t) (ha : e+d ≤ a) :
    coefficientMatrix (weightedCorrection 1 ℓ J G b) a = 0 := by
  classical
  ext u v
  simp only [coefficientMatrix, weightedCorrection, finsetSum_coeff, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x hx
  apply coeff_eq_zero_of_natDegree_lt
  rw [one_mul]
  have hq := quotient_degree_lt ℓ (G x v) hℓ ht hd (hG _ _) hb
  have hj := hJ u x
  have hp := natDegree_mul_le (p := J u x) (q := -((G x v * X ^ b) /ₘ ℓ))
  rw [natDegree_neg] at hp
  omega

/-- No weighted correction has an input column before the suffix. -/
theorem weightedCorrection_prefix_zero {ι : Type} [Fintype ι]
    (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X]) {d t b : ℕ}
    (ht : ℓ.natDegree = t) (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hb : b+d < t) : weightedCorrection η ℓ J G b = 0 := by
  classical
  funext u v
  simp only [weightedCorrection, Matrix.zero_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [prefix_quotient_zero ℓ (G x v) hℓ ht (hG _ _) hb]
  simp

theorem activeCorrection_column_support {ι : Type} [Fintype ι]
    (t d : ℕ) (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X])
    (ht : ℓ.natDegree = t) (hG : ∀ u v, (G u v).natDegree ≤ d)
    (a b : Fin t × ι) (hb : b.1.val < t-d) :
    activeCorrection t d η ℓ J G a b = 0 := by
  have hb' : b.1.val+d < t := by omega
  simp only [activeCorrection]
  rw [weightedCorrection_prefix_zero 1 ℓ hℓ J G ht hG hb',
    weightedCorrection_prefix_zero η ℓ hℓ J G ht hG hb']
  simp

theorem activeCorrection_row_support {ι : Type} [Fintype ι]
    (t d e : ℕ) (η ℓ : ℂ[X]) (hℓ : ℓ.Monic) (J G : Matrix ι ι ℂ[X])
    (ht : ℓ.natDegree = t) (hd : 0<d)
    (hG : ∀ u v, (G u v).natDegree ≤ d)
    (hJ : ∀ u v, (J u v).natDegree ≤ e)
    (a b : Fin t × ι) (ha : ¬ActiveTime t d e a.1.val) :
    activeCorrection t d η ℓ J G a b = 0 := by
  have ha' : a.1.val < t-d := by unfold ActiveTime at ha; omega
  have ha'' : e+d ≤ a.1.val := by unfold ActiveTime at ha; omega
  rw [activeCorrection, ite_eq_left ha']
  have hh := congrFun (congrFun (prefix_row_vanishes ℓ hℓ J G ht hd hG hJ
    b.1.isLt ha'') a.2) b.2
  exact hh

end ExactFourier.Boundary

end

section
/-! Literal relation between modulus multiplication and the supported correction.
This is the missing interface at 06-feedback:86--196, not an assumed theorem.
Noncommutative coefficient matrices remain ordered J_i G_j. -/
namespace ExactFourier.Boundary
open Polynomial
open CoefficientTime
open scoped Kronecker BigOperators

theorem timeMatrix_eq_trunc {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (G : Matrix ι ι ℂ[X]) :
    timeMatrix t G = blockTruncHom t (seriesMatrix G) := by
  ext a b
  simp only [timeMatrix, coeff_mul_X_pow', blockTruncHom_apply, seriesMatrix_apply,
    Polynomial.coeff_coe]

/-- The exact remainder-minus-truncation map: minus the quotient times ℓ. -/
theorem difference_eq_columns {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (ℓ : ℂ[X]) (G : Matrix ι ι ℂ[X]) :
    modulusMatrix t ℓ G - timeMatrix t G =
      coefficientColumns t ((ℓ : PowerSeries ℂ) • quotientColumns t ℓ G) := by
  ext a b
  change (((G a.2 b.2 * X^b.1.val) %ₘ ℓ).coeff a.1.val -
    (G a.2 b.2 * X^b.1.val).coeff a.1.val) =
    PowerSeries.coeff a.1.val ((ℓ : PowerSeries ℂ) *
      ((-((G a.2 b.2 * X^b.1.val) /ₘ ℓ) : ℂ[X]) : PowerSeries ℂ))
  rw [← coeff_sub, boundary_difference]
  rw [← Polynomial.coe_mul, Polynomial.coeff_coe]
  congr 1
  ring_nf

/-- The polynomial adjugate/denominator identity gives the TRUE inverse, before
any support reduction. This is not an inverse evaluation assumption. -/
theorem timeMatrix_inverse {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (u : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hGJ : G * J = Matrix.scalar ι u) :
    (timeMatrix t G)⁻¹ =
      blockTruncHom t ((u : PowerSeries ℂ)⁻¹ • seriesMatrix J) := by
  apply Matrix.inv_eq_right_inv
  rw [timeMatrix_eq_trunc, ← map_mul, Matrix.mul_smul, ← map_mul, hGJ]
  have hu' : PowerSeries.constantCoeff (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hs : (u : PowerSeries ℂ)⁻¹ • seriesMatrix (Matrix.scalar ι u) = 1 := by
    apply Matrix.ext
    intro i j
    by_cases hij : i=j
    · subst j
      simpa [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply] using
        PowerSeries.inv_mul_cancel (u : PowerSeries ℂ) hu'
    · simp [Matrix.smul_apply, Matrix.scalar_apply, hij]
  rw [hs, map_one]

/-- The relative correction is the coefficient map of (ℓ/u) J v, with the
quotient sign included in v. -/
theorem inverse_mul_difference {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hGJ : G * J = Matrix.scalar ι u) :
    (timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G - timeMatrix t G) =
      coefficientColumns t (((ℓ : PowerSeries ℂ) * (u : PowerSeries ℂ)⁻¹) •
        (seriesMatrix J * quotientColumns t ℓ G)) := by
  rw [timeMatrix_inverse t u G J hu hGJ, difference_eq_columns,
    blocks_mul_columns, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm (u : PowerSeries ℂ)⁻¹]

/-- A prefix-only scalar convolution cancels the denominator on early rows, and
literally leaves the late rows unchanged. -/
theorem prefix_scalar_cancels {ι κ : Type} [Fintype ι] [DecidableEq ι]
    (t T : ℕ) (f η : PowerSeries ℂ) (hfη : f*η=1)
    (V : Matrix ι κ (PowerSeries ℂ)) (a : Fin t × ι) (b : κ) :
    ((prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) *
      coefficientColumns t (η • V)) a b =
        if a.1.val < T then PowerSeries.coeff a.1.val (V a.2 b)
        else PowerSeries.coeff a.1.val (η * V a.2 b) := by
  rw [prefix_mul_columns]
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hfη, one_mul]

end ExactFourier.Boundary

namespace ExactFourier.Boundary
open Polynomial CoefficientTime
open scoped Kronecker BigOperators

/-- Coefficients below t cannot see the discarded tail of a scalar series. -/
theorem coeff_trunc_mul_series (t : ℕ) (η V : PowerSeries ℂ) (a : Fin t) :
    PowerSeries.coeff a.val (((PowerSeries.trunc t η : ℂ[X]) : PowerSeries ℂ) * V) =
      PowerSeries.coeff a.val (η*V) := by
  rw [coeff_mul_truncated _ _ a, coeff_mul_truncated _ _ a]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hka : k.val ≤ a.val
  · have hat : a.val-k.val < t := by have := a.isLt; omega
    simp [hka, PowerSeries.coeff_trunc, hat]
  · simp [hka]

/-- Converting the finite polynomial ordered generator formula to series changes
neither matrix order nor the sign of the quotient. -/
theorem weightedCorrection_series {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (η ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X])
    (i : ι) (b : Fin t × ι) :
    (((weightedCorrection η ℓ J G b.1.val) i b.2 : ℂ[X]) : PowerSeries ℂ) =
      (η : PowerSeries ℂ) * (seriesMatrix J * quotientColumns t ℓ G) i b := by
  simp only [weightedCorrection, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum, map_mul,
    Matrix.mul_apply, seriesMatrix_apply, quotientColumns, Finset.mul_sum, mul_assoc]

/-- The finite polynomial η used in the ordered-span certificate is exactly the
first t coefficients of ℓ/u; no truncation error survives in any output row. -/
theorem weightedCorrection_trunc_coeff {ι : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (η : PowerSeries ℂ) (ℓ : ℂ[X]) (J G : Matrix ι ι ℂ[X])
    (a b : Fin t × ι) :
    (weightedCorrection (PowerSeries.trunc t η) ℓ J G b.1.val a.2 b.2).coeff a.1.val =
      PowerSeries.coeff a.1.val (η * (seriesMatrix J * quotientColumns t ℓ G) a.2 b) := by
  rw [← Polynomial.coeff_coe, weightedCorrection_series]
  exact coeff_trunc_mul_series t η _ a.1

/-- Quotient columns vanish on the whole coefficient prefix, not merely on an
assumed active direct summand. -/
theorem quotientColumns_prefix_zero {ι : Type} (t d : ℕ) (ℓ : ℂ[X])
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (G : Matrix ι ι ℂ[X])
    (hG : ∀ i j, (G i j).natDegree ≤ d) (i : ι) (b : Fin t × ι)
    (hb : b.1.val < t-d) : quotientColumns t ℓ G i b = 0 := by
  have hb' : b.1.val+d<t := by omega
  simp only [quotientColumns, prefix_quotient_zero ℓ _ hℓ ht (hG _ _) hb',
    neg_zero, Polynomial.coe_zero]

/-- The actual relative map I+S is fixed on its right by every prefix map. -/
theorem inverse_difference_prefix_zero {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hGJ : G*J=Matrix.scalar ι u)
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (hG : ∀ i j, (G i j).natDegree ≤ d)
    (a b : Fin t × ι) (hb : b.1.val < t-d) :
    ((timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G - timeMatrix t G)) a b = 0 := by
  rw [inverse_mul_difference t u ℓ G J hu hGJ]
  simp only [coefficientColumns, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply]
  simp only [quotientColumns_prefix_zero t d ℓ hℓ ht G hG _ b hb, mul_zero,
    Finset.sum_const_zero, map_zero]

/-- Premultiplication of the literal relative correction gives exactly the
previously certified finite activeCorrection matrix. -/
theorem prefix_mul_inverse_difference {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hℓ0 : ℓ.coeff 0 ≠ 0)
    (hGJ : G*J=Matrix.scalar ι u) :
    (prefixScalar t (t-d) ((u : PowerSeries ℂ) * (ℓ : PowerSeries ℂ)⁻¹) ⊗ₖ
      (1 : Matrix ι ι ℂ)) *
      ((timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G - timeMatrix t G)) =
        activeCorrection t d
          (PowerSeries.trunc t ((ℓ : PowerSeries ℂ) * (u : PowerSeries ℂ)⁻¹)) ℓ J G := by
  have hu' : PowerSeries.constantCoeff (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hℓ' : PowerSeries.constantCoeff (ℓ : PowerSeries ℂ) ≠ 0 := by simpa using hℓ0
  have hic : ((u : PowerSeries ℂ) * (ℓ : PowerSeries ℂ)⁻¹) *
      ((ℓ : PowerSeries ℂ) * (u : PowerSeries ℂ)⁻¹) = 1 := by
    calc
      _ = ((u : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹) *
          ((ℓ : PowerSeries ℂ)⁻¹*(ℓ : PowerSeries ℂ)) := by ring
      _ = 1 := by rw [PowerSeries.mul_inv_cancel _ hu', PowerSeries.inv_mul_cancel _ hℓ', one_mul]
  rw [inverse_mul_difference t u ℓ G J hu hGJ]
  ext a b
  rw [prefix_scalar_cancels _ _ _ _ hic]
  rw [activeCorrection]
  split_ifs with ha
  · rw [← Polynomial.coeff_coe, weightedCorrection_series]
    simp
  · exact (weightedCorrection_trunc_coeff t _ ℓ J G a b).symm

end ExactFourier.Boundary

namespace ExactFourier.Boundary
open Polynomial CoefficientTime
open scoped Kronecker BigOperators

theorem prefix_conjugated_relative_map {ι : Type} [Fintype ι] [DecidableEq ι]
    (t d : ℕ) (u ℓ : ℂ[X]) (G J : Matrix ι ι ℂ[X])
    (hu : u.coeff 0 ≠ 0) (hℓ0 : ℓ.coeff 0 ≠ 0)
    (hGJ : G*J=Matrix.scalar ι u)
    (hG0 : IsUnit (G.map (fun f => f.coeff 0)))
    (hℓ : ℓ.Monic) (ht : ℓ.natDegree=t) (hG : ∀ i j, (G i j).natDegree ≤ d) :
    let P := prefixScalar t (t-d) ((u : PowerSeries ℂ)*(ℓ : PowerSeries ℂ)⁻¹) ⊗ₖ
      (1 : Matrix ι ι ℂ)
    P * ((timeMatrix t G)⁻¹ * modulusMatrix t ℓ G) * P⁻¹ =
      1 + activeCorrection t d
        (PowerSeries.trunc t ((ℓ : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹)) ℓ J G := by
  let f : PowerSeries ℂ := (u : PowerSeries ℂ)*(ℓ : PowerSeries ℂ)⁻¹
  let η : PowerSeries ℂ := (ℓ : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹
  let P := prefixScalar t (t-d) f ⊗ₖ (1 : Matrix ι ι ℂ)
  let Q := prefixScalar t (t-d) η ⊗ₖ (1 : Matrix ι ι ℂ)
  let S := (timeMatrix t G)⁻¹ * (modulusMatrix t ℓ G-timeMatrix t G)
  have hA : IsUnit (timeMatrix t G) := by
    rw [timeMatrix_eq_trunc]
    apply blockTrunc_isUnit
    exact hG0
  have hrel : (timeMatrix t G)⁻¹ * modulusMatrix t ℓ G = 1+S := by
    dsimp only [S]
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA)]
    abel
  have hu' : PowerSeries.constantCoeff (u : PowerSeries ℂ) ≠ 0 := by simpa using hu
  have hℓ' : PowerSeries.constantCoeff (ℓ : PowerSeries ℂ) ≠ 0 := by simpa using hℓ0
  have hfη : f*η=1 := by
    calc
      f*η = ((u : PowerSeries ℂ)*(u : PowerSeries ℂ)⁻¹) *
          ((ℓ : PowerSeries ℂ)⁻¹*(ℓ : PowerSeries ℂ)) := by dsimp [f, η]; ring
      _ = 1 := by rw [PowerSeries.mul_inv_cancel _ hu', PowerSeries.inv_mul_cancel _ hℓ', one_mul]
  have hPQ : P*Q=1 := by
    dsimp only [P, Q]
    rw [← Matrix.mul_kronecker_mul, ← prefixScalar_mul, hfη, prefixScalar_one]
    simp
  have hPinv : P⁻¹=Q := Matrix.inv_eq_right_inv hPQ
  have hSQ : S*Q=S := zero_prefix_columns_mul t (t-d) η S
    (fun a b hb => inverse_difference_prefix_zero t d u ℓ G J hu hGJ hℓ ht hG a b hb)
  change P * ((timeMatrix t G)⁻¹ * modulusMatrix t ℓ G) * P⁻¹ = _
  calc
    _ = P*(1+S)*Q := by rw [hrel, hPinv]
    _ = P*Q+P*(S*Q) := by noncomm_ring
    _ = 1+P*S := by rw [hPQ, hSQ]
    _ = _ := by rw [prefix_mul_inverse_difference t d u ℓ G J hu hℓ0 hGJ]

end ExactFourier.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.CascadeLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! The real limit used by the cascade-to-corner argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

theorem cascadeError_tendsto : Tendsto cascadeError atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hi1 : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have hi2 : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have hl : Tendsto (fun m : ℕ => Real.log ((m:ℝ)+2)/((m:ℝ)+2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp h2
  have ha := (hi1.const_mul (Real.log 2)).add
    ((hl.mul ((tendsto_const_nhds (x := (1:ℝ))).add hi1)).const_mul 4)
  have hb := ha.add (hi2.mul hi1)
  simp only [mul_zero,zero_mul,add_zero] at hb
  convert hb using 1
  funext m
  have hn1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (m:ℝ)+2 ≠ 0 := by positivity
  dsimp [cascadeError]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero _ hn2),Real.log_pow]
  field_simp
  ring

theorem fixed_price_of_cascade (x y C : ℝ)
    (h : ∀ k t : ℕ, 0 < k → 0 < t →
      (t:ℝ)*k*(x-y) ≤ C*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^3)) : x ≤ y := by
  have he (m : ℕ) : x-y ≤ C*cascadeError m := by
    have hh := h (m+1) ((m+2)^4) (by omega) (by positivity)
    push_cast at hh
    have ht : 0 < ((m:ℝ)+2)^4*((m:ℝ)+1) := by positivity
    have hh' : x-y ≤ (C*(((m:ℝ)+2)^4*Real.log (2*((m:ℝ)+2)^4)+((m:ℝ)+2)^3)) / (((m:ℝ)+2)^4*((m:ℝ)+1)) :=
      (le_div_iff₀ ht).mpr (by nlinarith only [hh])
    convert hh' using 1 ; dsimp [cascadeError] ; field_simp
  have hh := ge_of_tendsto (cascadeError_tendsto.const_mul C) (Filter.Eventually.of_forall he)
  have : x-y ≤ 0 := by simpa using hh
  linarith

end ExactFourier

end

section
/-! Invertible corners in block form, obtained from the exact uniform cascade,
not by deleting paid coordinates or assuming price continuity. -/
namespace ExactFourier
open TensorAxis CoefficientTime
namespace MatrixPrice
variable (p : MatrixPrice)
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem corner_block (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (hM : IsUnit M)
    (hK : IsUnit (Matrix.fromBlocks M C B D)) :
    p.value M ≤ p.value (Matrix.fromBlocks M C B D) := by
  by_cases hn : Fintype.card α = 0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    have he : M = 1 := by ext i; exact isEmptyElim i
    rw [he,p.one]
    exact p.nonneg _ (he ▸ hK)
  obtain ⟨C₀,hC₀,hbound⟩ := Cascade.uniform_bound p M C B D hM hK
  apply fixed_price_of_cascade (p.value M) (p.value (Matrix.fromBlocks M C B D))
    (C₀ * Fintype.card α)
  intro k t hk ht
  have hH : IsUnit ((power (CellSeries.transfer M C B D) k).map PowerSeries.constantCoeff) := by
    rw [map_power,CellSeries.constant_transfer]
    exact unit_power M hM k
  have hlo := p.trunc_lower_bound t (power (CellSeries.transfer M C B D) k) hH
  rw [map_power,CellSeries.constant_transfer,price_power p M hM] at hlo
  have hupper := hbound k t ht
  have hboth := hlo.trans hupper
  have hm := mul_le_mul_of_nonneg_right hboth (Nat.cast_nonneg (Fintype.card α) : (0:ℝ) ≤ _)
  have hrel : (Fintype.card (Fibers α k) : ℝ)*Fintype.card α =
      (k:ℝ)*(Fintype.card α : ℝ)^k := by
    have hh := Triangular.calls_card_relation (β := α) k
    change Fintype.card (Fibers α k) * Fintype.card α = k * Fintype.card (Space α k) at hh
    rw [card_space] at hh
    exact_mod_cast hh
  have hN : 0 < (Fintype.card α : ℝ)^k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) k
  apply (mul_le_mul_iff_right₀ hN).mp
  have ha := congrArg (fun a : ℝ => (t:ℝ)*a*p.value M) hrel
  have hb := congrArg (fun a : ℝ => (t:ℝ)*a*p.value (Matrix.fromBlocks M C B D)) hrel
  nlinarith only [hm,ha,hb]

end MatrixPrice
end ExactFourier

end

section
/-! Literal arbitrary invertible square submatrix theorem, and its one-way DAG
corollary. Independent permutations use only the standing monomial law. -/
namespace ExactFourier
namespace MatrixPrice
variable (p : MatrixPrice)
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem submatrix_equiv (A : Matrix ι ι ℂ) (hA : IsUnit A) (e f : κ ≃ ι) :
    p.value (A.submatrix e f) = p.value A := by
  let B := A.submatrix e e
  let τ := f.trans e.symm
  let R : Matrix κ κ ℂ := (1 : Matrix κ κ ℂ).submatrix id τ
  have hR : MonomialMatrix R := by
    refine ⟨τ,fun _ => 1,by simp,?_⟩
    intro i j
    rfl
  have hB : IsUnit B := (Matrix.isUnit_submatrix_equiv e e).mpr hA
  have hmul : B * R = A.submatrix e f := by
    change B * (1 : Matrix κ κ ℂ).submatrix (Equiv.refl κ) τ = _
    rw [Matrix.mul_submatrix_one]
    ext i j
    simp [B,τ,Matrix.submatrix_apply]
  have hm := p.monomial B 1 R hB MonomialMatrix.one hR
  rw [one_mul,hmul] at hm
  calc
    _ = p.value B := hm
    _ = p.value A := p.reindex e.symm A hA

end MatrixPrice

namespace MatrixPrice
variable (p : MatrixPrice)
variable {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem corner (K : Matrix ι ι ℂ) (hK : IsUnit K) (rows cols : κ → ι)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (hM : IsUnit (K.submatrix rows cols)) :
    p.value (K.submatrix rows cols) ≤ p.value K := by
  classical
  let δ := {i : ι // i ∉ Set.range rows}
  let ε := {i : ι // i ∉ Set.range cols}
  let er := extendInjection rows hr
  let ec₀ := extendInjection cols hc
  have hcard : Fintype.card δ = Fintype.card ε := by
    have h1 := Fintype.card_congr er
    have h2 := Fintype.card_congr ec₀
    simp only [Fintype.card_sum] at h1 h2
    change Fintype.card κ + Fintype.card δ = Fintype.card ι at h1
    change Fintype.card κ + Fintype.card ε = Fintype.card ι at h2
    omega
  let ec : κ ⊕ δ ≃ ι :=
    (Equiv.sumCongr (Equiv.refl κ) (Fintype.equivOfCardEq hcard)).trans ec₀
  let A := K.submatrix er ec
  have hAu : IsUnit A := (Matrix.isUnit_submatrix_equiv er ec).mpr hK
  have htop : A.toBlocks₁₁ = K.submatrix rows cols := by
    ext i j
    rfl
  have h := p.corner_block A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂
    (htop ▸ hM) (by rw [Matrix.fromBlocks_toBlocks]; exact hAu)
  rw [Matrix.fromBlocks_toBlocks,htop] at h
  exact h.trans_eq (p.submatrix_equiv K hK er ec)

theorem le_shear (G : Matrix ι ι ℂ) (hG : IsUnit G) :
    p.value G ≤ p.value (rectangularShear G) := by
  have h := p.corner (rectangularShear G) (rectangularShear_unit G)
    Sum.inl Sum.inr Sum.inl_injective Sum.inr_injective hG
  exact h

end MatrixPrice

namespace TypedDAG
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem price (C : TypedDAG ι ι) (p : MatrixPrice) (G : Matrix ι ι ℂ)
    (hG : IsUnit G) (hC : ∀ x, C.eval x = G.mulVec x) :
    p.value G ≤ 8*(C.size:ℝ)+2*Fintype.card ι :=
  (p.le_shear G hG).trans (C.shear_price p G hC)
end TypedDAG
end ExactFourier

end

section
/-! Charged common-generator circuits for the active coefficient boundary.
Generator outputs are shared across output times; every scalar weight is charged. -/
namespace ExactFourier
open scoped BigOperators
namespace TypedDAG
variable {α β γ ι : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype ι]

theorem size_weightedBlocks (W : Matrix α (β × γ) ℂ) (C : γ → TypedDAG ι ι) :
    (weightedBlocks W C).size = Fintype.card β * (∑ g, (C g).size) +
      2*Fintype.card ι*Fintype.card α*Fintype.card β*Fintype.card γ := by
  simp [weightedBlocks,Fintype.sum_prod_type]
  ring

theorem eval_weightedBlocks (W : Matrix α (β × γ) ℂ) (C : γ → TypedDAG ι ι)
    (G : γ → Matrix ι ι ℂ) (hC : ∀ g x, (C g).eval x = (G g).mulVec x) (x : β × ι → ℂ) :
    (weightedBlocks W C).eval x = (blockMatrix W G).mulVec x := by
  funext a
  simp only [weightedBlocks,eval_comp,eval_outputs,eval_inputs,eval_parallel,eval_matrix,
    eval_stack,hC,Function.comp_apply,Prod.swap,Matrix.mulVec,dotProduct,blockMatrix,
    Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul,mul_assoc]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.sum_comm]

theorem eval_addIdentity [DecidableEq ι] (C : TypedDAG ι ι) (A : Matrix ι ι ℂ)
    (hC : ∀ x, C.eval x=A.mulVec x) (x : ι → ℂ) :
    C.addIdentity.eval x=(1+A).mulVec x := by
  simp [addIdentity,hC,Matrix.add_mulVec,Pi.add_def]

end TypedDAG
end ExactFourier

end

section
/-! Uniform O((k+1)^2 n^k) DAGs for each tensor coefficient, with no
invertibility assumptions at interpolation nodes. -/
namespace ExactFourier
open TensorAxis PolynomialDAG PolynomialMatrix
namespace Boundary
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_tensor_coefficient_dag (G : Matrix α α (Polynomial ℂ)) :
    ∃ B : ℕ, ∀ k j : ℕ, ∃ C : TypedDAG (Space α k) (Space α k),
      C.size ≤ B*(k+1)^2*Fintype.card α^k ∧
      ∀ x, C.eval x=(coefficientMatrix (power G k) j).mulVec x := by
  let d := PolynomialMatrix.bound G
  let B := 2*Fintype.card α*(d+1)+2*(d+1)^2
  refine ⟨B,?_⟩
  intro k j
  have hdeg := bounded_power G (le_bound G) k
  have heval (z : ℂ) : ∃ C : TypedDAG (Space α k) (Space α k),
      C.size ≤ 2*Fintype.card α*k*Fintype.card α^k ∧
      ∀ x, C.eval x=(evalMatrix (power G k) z).mulVec x := by
    refine ⟨TypedDAG.tensorPower (evalMatrix G z) k, (TypedDAG.size_tensorPower _ _).le,?_⟩
    intro x
    rw [TypedDAG.eval_tensorPower]
    congr 1
    exact (map_power (Polynomial.evalRingHom z) G k).symm
  obtain ⟨C,hC,hEval⟩ := exists_coefficients (power G k) (k*d+1) (j+1)
    (2*Fintype.card α*k*Fintype.card α^k) (fun a b => Nat.lt_succ_of_le (hdeg a b)) heval
  refine ⟨C.outputs (fun i => (⟨j,by omega⟩,i)),?_,?_⟩
  · rw [TypedDAG.size_outputs]
    apply hC.trans
    rw [card_space]
    have hm : k*d+1 ≤ (d+1)*(k+1) := by nlinarith
    calc
      _ ≤ ((d+1)*(k+1))*(2*Fintype.card α*(k+1)*Fintype.card α^k) +
          2*((d+1)*(k+1))*((d+1)*(k+1))*Fintype.card α^k := by gcongr ; omega
      _ = B*(k+1)^2*Fintype.card α^k := by dsimp [B]; ring
  · intro x
    funext u
    rw [TypedDAG.eval_outputs,hEval]
    rfl

end Boundary
end ExactFourier

end

section
/-! The exact disjoint active set and its direct-summand price. -/
namespace ExactFourier.Boundary
open scoped BigOperators

theorem card_times (t d e : ℕ) : Fintype.card (Times t d e) ≤ e+2*d := by
  let f : Times t d e → Fin (e+2*d) := fun a =>
    if h : a.val.val < t-d then ⟨a.val.val,by
      have ha := a.property
      unfold ActiveTime at ha
      omega⟩
    else ⟨e+d+(a.val.val-(t-d)),by have ha := a.val.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Fin.val hab
    simp only [f] at h
    split_ifs at h with ha hb hb <;> dsimp only at h
    · exact Subtype.ext (Fin.ext h)
    · have hb' := b.val.isLt
      have ha' := a.property
      unfold ActiveTime at ha'
      omega
    · have ha' := a.val.isLt
      have hb' := b.property
      unfold ActiveTime at hb'
      omega
    · apply Subtype.ext; apply Fin.ext
      omega
  simpa using Fintype.card_le_of_injective f hf

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem active_split (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (ht : ℓ.natDegree=t) (hd : 0<d)
    (hG : ∀ i j, (G i j).natDegree ≤ d) (hJ : ∀ i j, (J i j).natDegree ≤ e) :
    (1+activeCorrection t d η ℓ J G).submatrix (timeActiveSplit t d e) (timeActiveSplit t d e) =
      Matrix.fromBlocks (activeMatrix t d e η ℓ J G) 0 0 1 := by
  simp only [Matrix.submatrix_add,Pi.add_apply,Matrix.submatrix_one_equiv]
  ext a b
  rcases a with ⟨a,i⟩|⟨a,i⟩ <;> rcases b with ⟨b,j⟩|⟨b,j⟩
  · simp [timeActiveSplit,activeMatrix,Matrix.submatrix,Matrix.one_apply]
  · have hz := activeCorrection_column_support t d η ℓ hℓ J G ht hG (a.val,i) (b.val,j)
      (by change b.val.val < t-d; have hb := b.property; unfold ActiveTime at hb; omega)
    have hne : a.val ≠ b.val := by intro h; exact b.property (h ▸ a.property)
    simp [timeActiveSplit,Matrix.submatrix,hz]
  · have hz := activeCorrection_row_support t d e η ℓ hℓ J G ht hd hG hJ (a.val,i) (b.val,j) a.property
    have hne : a.val ≠ b.val := by intro h; exact a.property (h.symm ▸ b.property)
    simp [timeActiveSplit,Matrix.submatrix,hz]
  · have hz := activeCorrection_row_support t d e η ℓ hℓ J G ht hd hG hJ (a.val,i) (b.val,j) a.property
    simp [timeActiveSplit,Matrix.submatrix,Matrix.one_apply,hz]

theorem active_price (p : MatrixPrice) (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (ht : ℓ.natDegree=t) (hd : 0<d)
    (hG : ∀ i j, (G i j).natDegree ≤ d) (hJ : ∀ i j, (J i j).natDegree ≤ e)
    (hu : IsUnit (1+activeCorrection t d η ℓ J G)) :
    IsUnit (activeMatrix t d e η ℓ J G) ∧
      p.value (1+activeCorrection t d η ℓ J G) = p.value (activeMatrix t d e η ℓ J G) := by
  have he := active_split t d e η ℓ hℓ J G ht hd hG hJ
  have hh := (Matrix.isUnit_submatrix_equiv (timeActiveSplit t d e) (timeActiveSplit t d e)).mpr hu
  rw [he] at hh
  have ha := (Matrix.isUnit_fromBlocks_zero₂₁.mp hh).1
  refine ⟨ha,?_⟩
  rw [← p.submatrix_equiv _ hu (timeActiveSplit t d e) (timeActiveSplit t d e),he,p.identity_pad _ ha]

end ExactFourier.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.BoundaryActiveCircuit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Common ordered spatial generators for the active boundary DAG. Scalar
weights may be arbitrarily large and depend on the modulus; every use is charged. -/
namespace ExactFourier.Boundary
open scoped BigOperators
open TensorAxis PolynomialMatrix
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem activeMatrix_blocks (t d e : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ))
    (hG : Bounded G d) (hJ : Bounded J e) :
    activeMatrix t d e η ℓ J G = 1 + TypedDAG.blockMatrix (activeWeights t d e η ℓ)
      (fun ij => coefficientMatrix J ij.1.val * coefficientMatrix G ij.2.val) := by
  unfold activeMatrix
  congr 1
  ext a b
  have h := ordered_span (if a.1.val.val<t-d then 1 else η) ℓ hℓ J G hG hJ a.1.val.val b.1.val.val
  have hh := congrFun (congrFun h a.2) b.2
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at hh
  simp only [Matrix.submatrix_apply,activeCorrection,TypedDAG.blockMatrix,activeWeights,Fintype.sum_prod_type]
  simp only [← Fin.sum_univ_eq_sum_range] at hh
  by_cases ha : a.1.val.val<t-d <;> simpa [ha,coefficientMatrix] using hh

theorem exists_active_dag (t d e sG sJ : ℕ) (η ℓ : Polynomial ℂ) (hℓ : ℓ.Monic)
    (J G : Matrix ι ι (Polynomial ℂ)) (hG : Bounded G d) (hJ : Bounded J e)
    (CG : (j : Fin (d+1)) → TypedDAG ι ι) (CJ : (i : Fin (e+1)) → TypedDAG ι ι)
    (hsG : ∀ j, (CG j).size ≤ sG) (hsJ : ∀ i, (CJ i).size ≤ sJ)
    (heG : ∀ j x, (CG j).eval x=(coefficientMatrix G j.val).mulVec x)
    (heJ : ∀ i x, (CJ i).eval x=(coefficientMatrix J i.val).mulVec x) :
    ∃ C : TypedDAG (Times t d e × ι) (Times t d e × ι),
      C.size ≤ Fintype.card (Times t d e)*((e+1)*(d+1))*(sG+sJ) +
        2*Fintype.card ι*Fintype.card (Times t d e)^2*((e+1)*(d+1)) +
        Fintype.card (Times t d e)*Fintype.card ι ∧
      ∀ x, C.eval x=(activeMatrix t d e η ℓ J G).mulVec x := by
  let Cij := fun ij : Fin (e+1) × Fin (d+1) => (CJ ij.1).comp (CG ij.2)
  refine ⟨(TypedDAG.weightedBlocks (activeWeights t d e η ℓ) Cij).addIdentity,?_,?_⟩
  · rw [TypedDAG.size_addIdentity,TypedDAG.size_weightedBlocks]
    have hs : (∑ ij, (Cij ij).size) ≤ ((e+1)*(d+1))*(sG+sJ) := by
      calc
        _ ≤ ∑ _ : Fin (e+1) × Fin (d+1), (sG+sJ) :=
          Finset.sum_le_sum (fun ij _ => Nat.add_le_add (hsG ij.2) (hsJ ij.1))
        _ = _ := by simp
    simp only [Fintype.card_prod,Fintype.card_fin]
    calc
      _ ≤ Fintype.card (Times t d e)*(((e+1)*(d+1))*(sG+sJ)) +
          2*Fintype.card ι*Fintype.card (Times t d e)*Fintype.card (Times t d e)*((e+1)*(d+1)) +
          Fintype.card (Times t d e)*Fintype.card ι := by gcongr
      _ = _ := by ring
  · intro x
    rw [activeMatrix_blocks t d e η ℓ hℓ J G hG hJ]
    apply TypedDAG.eval_addIdentity
    apply TypedDAG.eval_weightedBlocks
    intro ij v
    rw [TypedDAG.eval_comp,heG,heJ,Matrix.mulVec_mulVec]

end ExactFourier.Boundary

end

section
/-! Uniform sixth-degree active correction bound. No inverse evaluation circuit
and no bound on scalar interpolation weights is used. -/
namespace ExactFourier.Boundary
open TensorAxis PolynomialMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_uniform_active_dag (G J : Matrix α α (Polynomial ℂ))
    (dg dj : ℕ) (hG : Bounded G dg) (hJ : Bounded J dj) :
    ∃ A : ℕ, ∀ k t : ℕ, ∀ η ℓ : Polynomial ℂ, ℓ.Monic →
      ∃ C : TypedDAG (Times t (k*dg) (k*dj) × Space α k) (Times t (k*dg) (k*dj) × Space α k),
        C.size ≤ A*(k+1)^6*Fintype.card α^k ∧
        ∀ x, C.eval x=(activeMatrix t (k*dg) (k*dj) η ℓ (power J k) (power G k)).mulVec x := by
  obtain ⟨BG,hBG⟩ := exists_tensor_coefficient_dag G
  obtain ⟨BJ,hBJ⟩ := exists_tensor_coefficient_dag J
  let a := dj+2*dg
  let b := (dj+1)*(dg+1)
  let A := a*b*(BG+BJ)+2*a^2*b+a
  refine ⟨A,?_⟩
  intro k t η ℓ hℓ
  choose CG hsG heG using fun j : Fin (k*dg+1) => hBG k j.val
  choose CJ hsJ heJ using fun i : Fin (k*dj+1) => hBJ k i.val
  obtain ⟨C,hC,heC⟩ := exists_active_dag t (k*dg) (k*dj)
    (BG*(k+1)^2*Fintype.card α^k) (BJ*(k+1)^2*Fintype.card α^k) η ℓ hℓ
    (power J k) (power G k) (bounded_power G hG k) (bounded_power J hJ k)
    CG CJ hsG hsJ heG heJ
  refine ⟨C,hC.trans ?_,heC⟩
  rw [card_space]
  have hr : Fintype.card (Times t (k*dg) (k*dj)) ≤ a*(k+1) := by
    apply (card_times _ _ _).trans
    dsimp [a]
    nlinarith
  have hg : (k*dj+1)*(k*dg+1) ≤ b*(k+1)^2 := by
    calc
      _ ≤ ((dj+1)*(k+1))*((dg+1)*(k+1)) := by gcongr <;> nlinarith
      _ = _ := by dsimp [b]; ring
  have h5 : (k+1)^5 ≤ (k+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : (k+1)^4 ≤ (k+1)^6 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : k+1 ≤ (k+1)^6 := Nat.le_self_pow (by omega) _
  calc
    _ ≤ (a*(k+1))*(b*(k+1)^2)*(BG*(k+1)^2*Fintype.card α^k+BJ*(k+1)^2*Fintype.card α^k) +
      2*Fintype.card α^k*(a*(k+1))^2*(b*(k+1)^2) + a*(k+1)*Fintype.card α^k := by gcongr
    _ = a*b*(BG+BJ)*(k+1)^5*Fintype.card α^k +
      (2*a^2*b)*(k+1)^4*Fintype.card α^k + a*(k+1)*Fintype.card α^k := by ring
    _ ≤ a*b*(BG+BJ)*(k+1)^6*Fintype.card α^k +
      (2*a^2*b)*(k+1)^6*Fintype.card α^k + a*(k+1)^6*Fintype.card α^k := by gcongr
    _ = A*(k+1)^6*Fintype.card α^k := by dsimp [A]; ring

theorem exists_uniform_active_price (p : MatrixPrice) (G J : Matrix α α (Polynomial ℂ))
    (dg dj : ℕ) (hG : Bounded G dg) (hJ : Bounded J dj) :
    ∃ A : ℕ, ∀ k t : ℕ, ∀ η ℓ : Polynomial ℂ, ℓ.Monic → ℓ.natDegree=t → 0<k*dg →
      IsUnit (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) →
      p.value (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) ≤
        (A:ℝ)*(k+1:ℝ)^6*Fintype.card α^k := by
  obtain ⟨A,hA⟩ := exists_uniform_active_dag G J dg dj hG hJ
  refine ⟨8*A+2*(dj+2*dg),?_⟩
  intro k t η ℓ hℓ ht hd hu
  obtain ⟨C,hC,he⟩ := hA k t η ℓ hℓ
  obtain ⟨ha,hp⟩ := active_price p t (k*dg) (k*dj) η ℓ hℓ (power J k) (power G k) ht hd
    (bounded_power G hG k) (bounded_power J hJ k) hu
  rw [hp]
  have hc := C.price p _ ha he
  have hsz : (C.size:ℝ) ≤ (A:ℝ)*(k+1:ℝ)^6*Fintype.card α^k := by exact_mod_cast hC
  have hcard : Fintype.card (Times t (k*dg) (k*dj)) ≤ (dj+2*dg)*(k+1)^6 := by
    apply (card_times _ _ _).trans
    calc
      _ ≤ (dj+2*dg)*(k+1) := by nlinarith
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.le_self_pow (by omega) _)
  have hcr : (Fintype.card (Times t (k*dg) (k*dj)):ℝ) ≤ (dj+2*dg:ℝ)*(k+1:ℝ)^6 := by exact_mod_cast hcard
  rw [Fintype.card_prod,card_space] at hc
  push_cast at hc ⊢
  have hh := mul_le_mul_of_nonneg_right hcr (by positivity : (0:ℝ) ≤ (Fintype.card α:ℝ)^k)
  nlinarith only [hc,hsz,hh]

end ExactFourier.Boundary

end

section
/-! Uniform scalar-prefix price; the untouched suffix is restored literally. -/
namespace ExactFourier.ScalarConvolution
open CoefficientTime

theorem exists_prefix_dag (t T : ℕ) (ht : 0<t) (f : PowerSeries ℂ) :
    ∃ C : LinearDAG t t, C.size ≤ 52*t*(Nat.log 2 t+1) ∧
      ∀ x, C.eval x=(prefixScalar t T f).mulVec x := by
  obtain ⟨C,hC,he⟩ := exists_truncation_dag t ht f
  let I : LinearDAG t t := LinearDAG.wires Fin.castSucc
  refine ⟨(C.fanout I).withOutputs (fun i => if i.val<T then Fin.castAdd t i else Fin.natAdd t i),?_,?_⟩
  · exact hC
  · intro x
    funext i
    rw [LinearDAG.eval_withOutputs,LinearDAG.eval_fanout]
    simp only [Function.comp_apply]
    by_cases hi : i.val<T
    · simp only [hi,ite_true,Fin.addCases_left,he]
      simp [Matrix.mulVec,dotProduct,prefixScalar,hi]
    · simp only [hi,ite_false,Fin.addCases_right]
      have hm : (prefixScalar t T f).mulVec x i = x i := by
        simp [Matrix.mulVec,dotProduct,prefixScalar,hi,Matrix.one_apply]
      rw [hm]
      simp [I,LinearDAG.eval_wires]

theorem prefix_inv (t T : ℕ) (f : PowerSeries ℂ)
    (hf : PowerSeries.constantCoeff f ≠ 0) :
    (prefixScalar t T f)⁻¹=prefixScalar t T f⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← prefixScalar_mul,PowerSeries.mul_inv_cancel _ hf,prefixScalar_one]

theorem price_prefix (p : MatrixPrice) (t T : ℕ) (ht : 0<t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (prefixScalar t T f) ≤ (627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  obtain ⟨C,hC,hCe⟩ := exists_prefix_dag t T ht f
  obtain ⟨D,hD,hDe⟩ := exists_prefix_dag t T ht f⁻¹
  have hU := prefixScalar_isUnit t T f (isUnit_iff_ne_zero.mpr hf)
  have hInv : ∀ x, D.eval x=(prefixScalar t T f)⁻¹.mulVec x := by
    intro x; rw [prefix_inv t T f hf]; exact hDe x
  have hb := p.twoWay_DAG_bound (prefixScalar t T f) hU C D hCe hInv
  have hc' : (C.size:ℝ) ≤ 52*(t:ℝ)*(Nat.log 2 t+1) := by exact_mod_cast hC
  have hd' : (D.size:ℝ) ≤ 52*(t:ℝ)*(Nat.log 2 t+1) := by exact_mod_cast hD
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hl' : (0:ℝ)≤Nat.log 2 t := Nat.cast_nonneg _
  have hn : p.value (prefixScalar t T f) ≤ 627*(t:ℝ)*(Nat.log 2 t+1) := by nlinarith
  have h2 : (0:ℝ)<Real.log 2 := Real.log_pos (by norm_num)
  have hp : (2:ℝ)^Nat.log 2 t ≤ t := by exact_mod_cast Nat.pow_log_le_self 2 (Nat.ne_of_gt ht)
  have hl : (Nat.log 2 t:ℝ)*Real.log 2 ≤ Real.log t := by
    simpa only [Real.log_pow] using Real.log_le_log (pow_pos (by norm_num : (0:ℝ)<2) _) hp
  have he : (Nat.log 2 t:ℝ)+1 ≤ Real.log (2*t)/Real.log 2 := by
    apply (le_div_iff₀ h2).mpr
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt ht')]
    linarith
  calc
    _ ≤ 627*(t:ℝ)*(Nat.log 2 t+1) := hn
    _ ≤ 627*(t:ℝ)*(Real.log (2*t)/Real.log 2) := mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

end ExactFourier.ScalarConvolution

end

section
namespace ExactFourier.MatrixPrice
open scoped Kronecker
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem conjugate_le (p : MatrixPrice) (P A : Matrix ι ι ℂ)
    (hP : IsUnit P) (hA : IsUnit A) :
    p.value (P*A*P⁻¹) ≤ 2*p.value P+p.value A := by
  have hPi := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h1 := p.mul_le P A hP hA
  have h2 := p.mul_le (P*A) P⁻¹ (hP.mul hA) hPi
  rw [p.inverse P hP] at h2
  linarith

theorem le_conjugate (p : MatrixPrice) (P A : Matrix ι ι ℂ)
    (hP : IsUnit P) (hA : IsUnit A) :
    p.value A ≤ 2*p.value P+p.value (P*A*P⁻¹) := by
  have hPi := Matrix.isUnit_nonsing_inv_iff.mpr hP
  have h := p.conjugate_le P⁻¹ (P*A*P⁻¹) hPi ((hP.mul hA).mul hPi)
  have hh : P⁻¹*(P*A*P⁻¹)*(P⁻¹)⁻¹=A := by
    rw [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]
    calc
      _ = (P⁻¹*P)*A*(P⁻¹*P) := by noncomm_ring
      _ = A := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP)]; simp
  rw [hh,p.inverse P hP] at h
  exact h

theorem scalar (p : MatrixPrice) (A : Matrix ι ι ℂ) (hA : IsUnit A)
    (c : ℂ) (hc : c≠0) : p.value (c • A)=p.value A := by
  have he : c • A = Matrix.diagonal (fun _ : ι => c)*A*1 := by
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [he]
  exact p.monomial A _ _ hA (MonomialMatrix.diagonal _ (fun _ => hc)) MonomialMatrix.one

theorem scalar_unit (A : Matrix ι ι ℂ) (hA : IsUnit A)
    (c : ℂ) (hc : c≠0) : IsUnit (c • A) := by
  have he : c • A = Matrix.diagonal (fun _ : ι => c)*A := by
    ext i j
    simp [Matrix.diagonal_mul,Matrix.smul_apply]
  rw [he]
  exact (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun _ => isUnit_iff_ne_zero.mpr hc))).mul hA

theorem prefix_tensor_price (p : MatrixPrice) (t T : ℕ) (ht : 0<t)
    (f : PowerSeries ℂ) (hf : PowerSeries.constantCoeff f ≠ 0) :
    p.value (CoefficientTime.prefixScalar t T f ⊗ₖ (1 : Matrix ι ι ℂ)) ≤
      (Fintype.card ι:ℝ)*(627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  rw [p.tensor _ _ (CoefficientTime.prefixScalar_isUnit _ _ _ (isUnit_iff_ne_zero.mpr hf)) isUnit_one,p.one,mul_zero,add_zero]
  have h := ScalarConvolution.price_prefix p t T ht f hf
  calc
    _ ≤ (Fintype.card ι:ℝ)*((627/Real.log 2)*(t:ℝ)*Real.log (2*t)) := by gcongr
    _ = _ := by ring

end ExactFourier.MatrixPrice

end

section
/-! Uniform coefficient-boundary comparison, 06-feedback:20--46. All modulus
coefficients are literal charged constants. The estimate even holds at short
lengths; its intended use is t>k*deg G. -/
namespace ExactFourier.Boundary
open PolynomialMatrix TensorAxis CoefficientTime
open scoped Kronecker
variable {α : Type} [Fintype α] [DecidableEq α]

theorem exists_boundary_bound (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ))
    (hG0 : IsUnit (G.map (fun f => f.coeff 0))) :
    ∃ C : ℝ, 0≤C ∧ ∀ k t : ℕ, 0<k → 0<t → ∀ ℓ : Polynomial ℂ,
      ℓ.Monic → ℓ.natDegree=t → ℓ.coeff 0≠0 →
      IsUnit (modulusMatrix t ℓ (power G k)) →
      |p.value (modulusMatrix t ℓ (power G k))-p.value (timeMatrix t (power G k))| ≤
        C*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6) := by
  let J := G.adjugate
  let u := G.det
  let dg := bound G+1
  let dj := bound J
  have hG : Bounded G dg := fun i j => (le_bound G i j).trans (Nat.le_succ _)
  have hJ : Bounded J dj := le_bound J
  obtain ⟨A,hA⟩ := exists_uniform_active_price p G J dg dj hG hJ
  let C : ℝ := 1254/Real.log 2+A
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro k t hk ht ℓ hℓ hlt hℓ0 hW
  have hE : (fun f : Polynomial ℂ => f.coeff 0) = Polynomial.evalRingHom 0 := by
    funext f
    exact Polynomial.coeff_zero_eq_eval_zero f
  have hu : u.coeff 0≠0 := by
    have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG0)
    have he : (G.map (fun f => f.coeff 0)).det=u.coeff 0 := by
      rw [hE,congrFun hE u]
      exact (RingHom.map_det (Polynomial.evalRingHom 0) G).symm
    rwa [he] at hd
  have huk : (u^k).coeff 0≠0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero,Polynomial.eval_pow] using pow_ne_zero k (by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hu)
  have hGJ : power G k * power J k=Matrix.scalar (Space α k) (u^k) := by
    rw [mul_power]
    have h : G*J=u•1 := Matrix.mul_adjugate G
    rw [h,Cascade.power_smul,power_one]
    ext i j
    simp [Matrix.scalar_apply,Matrix.diagonal_apply,Matrix.one_apply,Matrix.smul_apply]
  have hGk0 : IsUnit ((power G k).map (fun f => f.coeff 0)) := by
    have he : (power G k).map (fun f => f.coeff 0)=power (G.map (fun f => f.coeff 0)) k := by
      rw [hE]
      exact map_power (Polynomial.evalRingHom 0) G k
    rw [he]
    exact unit_power _ hG0 k
  let f : PowerSeries ℂ := ((u^k : Polynomial ℂ):PowerSeries ℂ)*(ℓ:PowerSeries ℂ)⁻¹
  let P := prefixScalar t (t-k*dg) f ⊗ₖ (1 : Matrix (Space α k) (Space α k) ℂ)
  have hf : PowerSeries.constantCoeff f ≠ 0 := by
    simp only [f,map_mul,PowerSeries.constantCoeff_inv,Polynomial.constantCoeff_coe]
    exact mul_ne_zero huk (inv_ne_zero hℓ0)
  have hP : IsUnit P := TensorTools.unit_tensor _ _
    (prefixScalar_isUnit _ _ _ (isUnit_iff_ne_zero.mpr hf)) isUnit_one
  have hT : IsUnit (timeMatrix t (power G k)) := by
    rw [timeMatrix_eq_trunc]
    exact blockTrunc_isUnit _ _ hGk0
  have hR := (Matrix.isUnit_nonsing_inv_iff.mpr hT).mul hW
  let η := PowerSeries.trunc t ((ℓ:PowerSeries ℂ)*((u^k:Polynomial ℂ):PowerSeries ℂ)⁻¹)
  have he := prefix_conjugated_relative_map t (k*dg) (u^k) ℓ (power G k) (power J k)
    huk hℓ0 hGJ hGk0 hℓ hlt (bounded_power G hG k)
  change P*((timeMatrix t (power G k))⁻¹*modulusMatrix t ℓ (power G k))*P⁻¹ =
    1+activeCorrection t (k*dg) η ℓ (power J k) (power G k) at he
  have hactive : IsUnit (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) := by
    rw [← he]
    exact (hP.mul hR).mul (Matrix.isUnit_nonsing_inv_iff.mpr hP)
  have hb := hA k t η ℓ hℓ hlt (Nat.mul_pos hk (by dsimp [dg]; omega)) hactive
  have hp := p.prefix_tensor_price (ι := Space α k) t (t-k*dg) ht f hf
  change p.value P ≤ _ at hp
  rw [card_space] at hp
  push_cast at hp
  have hconj := p.le_conjugate P _ hP hR
  rw [he] at hconj
  have hdif := p.difference_le _ _ hT hW
  have hlog : 0≤(t:ℝ)*Real.log (2*t) := by
    have htr : (1:ℝ)≤t := by exact_mod_cast ht
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hC1 : 1254/Real.log 2≤C := by dsimp [C]; linarith [Nat.cast_nonneg (α := ℝ) A]
  have hC2 : (A:ℝ)≤C := by
    have hpos : (0:ℝ)≤1254/Real.log 2 := by positivity
    dsimp [C]; linarith
  calc
    _ ≤ 2*p.value P+p.value (1+activeCorrection t (k*dg) η ℓ (power J k) (power G k)) := hdif.trans hconj
    _ ≤ 2*((Fintype.card α:ℝ)^k*(627/Real.log 2)*(t:ℝ)*Real.log (2*t))+
        (A:ℝ)*(k+1:ℝ)^6*(Fintype.card α:ℝ)^k := add_le_add (by linarith [hp]) hb
    _ = (1254/Real.log 2)*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t))+
        (A:ℝ)*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by ring
    _ ≤ C*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t))+
        C*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by gcongr
    _ = _ := by ring

end ExactFourier.Boundary

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PolynomialClearing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
open TensorAxis CoefficientTime
open scoped Kronecker
namespace Boundary
variable {α : Type} [Fintype α] [DecidableEq α]

theorem time_power_clearing (G : Matrix α α (Polynomial ℂ))
    (H : Matrix α α (PowerSeries ℂ)) (q : Polynomial ℂ)
    (h : seriesMatrix G=(q:PowerSeries ℂ)•H) (k t : ℕ) :
    timeMatrix t (power G k) =
      (truncMatrix t ((q:PowerSeries ℂ)^k) ⊗ₖ (1 : Matrix (Space α k) (Space α k) ℂ))*
        blockTruncHom t (power H k) := by
  rw [timeMatrix_eq_trunc]
  have hh : seriesMatrix (power G k)=power (seriesMatrix G) k := by
    simpa only [seriesMatrix,RingHom.mapMatrix_apply] using
      map_power (Polynomial.coeToPowerSeries.ringHom : Polynomial ℂ →+* PowerSeries ℂ) G k
  rw [hh,h,Cascade.power_smul,← blockTrunc_smul_one,← map_mul,Matrix.smul_mul,one_mul]

theorem time_power_clearing_price (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ))
    (H : Matrix α α (PowerSeries ℂ)) (q : Polynomial ℂ)
    (h : seriesMatrix G=(q:PowerSeries ℂ)•H)
    (hq : q.coeff 0≠0) (hH : IsUnit (H.map PowerSeries.constantCoeff)) (k t : ℕ) (ht : 0<t) :
    p.value (timeMatrix t (power G k)) ≤ p.value (blockTruncHom t (power H k))+
      (Fintype.card α:ℝ)^k*(627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  have hq' : PowerSeries.constantCoeff ((q:PowerSeries ℂ)^k)≠0 := by simpa using pow_ne_zero k hq
  have h1 : IsUnit (truncMatrix t ((q:PowerSeries ℂ)^k)) := trunc_isUnit t _ (isUnit_iff_ne_zero.mpr hq')
  have h2 : IsUnit (blockTruncHom t (power H k)) := by
    apply blockTrunc_isUnit
    rw [map_power]
    exact unit_power _ hH k
  rw [time_power_clearing G H q h k t]
  have hm := p.mul_le _ _ (TensorTools.unit_tensor _ _ h1 isUnit_one) h2
  rw [p.tensor _ _ h1 isUnit_one,p.one,mul_zero,add_zero,card_space] at hm
  push_cast at hm
  have hp := ScalarConvolution.price_truncation p t ht ((q:PowerSeries ℂ)^k) hq'
  have hp' := mul_le_mul_of_nonneg_left hp (by positivity : (0:ℝ)≤(Fintype.card α:ℝ)^k)
  nlinarith

end Boundary
end ExactFourier

end

section
/-! Exact finite Taylor change of coefficient basis. -/
namespace ExactFourier.Taylor
open Polynomial
open scoped BigOperators Kronecker

theorem coefficient_sum (t : ℕ) (s : ℂ) (f : Polynomial ℂ) (hf : f.natDegree<t) (i : Fin t) :
    (taylor s f).coeff i.val = ∑ j : Fin t, (matrix t s) i j * f.coeff j.val := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
  simp only [map_sum,taylor_mul,taylor_C,finsetSum_coeff,coeff_C_mul]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [matrix,mul_comm]

theorem matrix_mul (t : ℕ) (s r : ℂ) : matrix t s * matrix t r = matrix t (s+r) := by
  ext i j
  have hd : (taylor r (X^j.val : Polynomial ℂ)).natDegree<t := by
    rw [natDegree_taylor,natDegree_X_pow]
    exact j.isLt
  have h := coefficient_sum t s (taylor r (X^j.val : Polynomial ℂ)) hd i
  rw [taylor_taylor] at h
  simpa only [Matrix.mul_apply,matrix] using h.symm

theorem matrix_unit (t : ℕ) (s : ℂ) : IsUnit (matrix t s) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply Matrix.isUnit_det_of_right_inverse (B := matrix t (-s))
  rw [matrix_mul,add_neg_cancel,matrix_zero]

theorem taylor_modulus (t : ℕ) (s : ℂ) :
    taylor s ((X-C s)^t : Polynomial ℂ)=X^t := by simp

theorem remainder_coeff (t : ℕ) (s : ℂ) (f : Polynomial ℂ) (i : Fin t) :
    (taylor s (f %ₘ (X-C s)^t)).coeff i.val=(taylor s f).coeff i.val := by
  rw [modByMonic_eq_sub_mul_div,map_sub,taylor_mul,taylor_modulus,coeff_sub]
  rw [coeff_X_pow_mul']
  simp [Nat.not_le_of_lt i.isLt]

variable {α : Type} [Fintype α] [DecidableEq α]

theorem intertwine (t : ℕ) (ht : 0<t) (s : ℂ) (G : Matrix α α (Polynomial ℂ)) :
    (matrix t s ⊗ₖ (1 : Matrix α α ℂ))*Boundary.modulusMatrix t ((X-C s)^t) G =
      Boundary.timeMatrix t (translate s G)*(matrix t s ⊗ₖ (1 : Matrix α α ℂ)) := by
  ext ⟨ai,aj⟩ ⟨bi,bj⟩
  let a : Fin t × α := (ai,aj)
  let b : Fin t × α := (bi,bj)
  change _ = _
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply]
  have hL : (∑ j : Fin t, ∑ i : α, (matrix t s a.1 j * if a.2=i then 1 else 0)*
      Boundary.modulusMatrix t ((X-C s)^t) G (j,i) b) =
      (taylor s ((G a.2 b.2*X^b.1.val)%ₘ (X-C s)^t)).coeff a.1.val := by
    simp only [mul_ite,mul_one,mul_zero,ite_mul,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    have hdeg : ((X-C s)^t : Polynomial ℂ).natDegree=t := by simp
    have hne : ((X-C s)^t : Polynomial ℂ)≠1 := by
      intro he
      have hh := congrArg Polynomial.natDegree he
      rw [hdeg] at hh
      simp only [natDegree_one] at hh
      omega
    have hd := natDegree_modByMonic_lt (G a.2 b.2*X^b.1.val) ((monic_X_sub_C s).pow t) hne
    rw [hdeg] at hd
    exact (coefficient_sum t s _ hd a.1).symm
  rw [hL,remainder_coeff]
  simp only [mul_ite,mul_one,mul_zero,mul_ite,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [taylor_mul]
  have hh := CoefficientTime.coeff_mul_truncated
    ((taylor s (G a.2 b.2):Polynomial ℂ):PowerSeries ℂ)
    ((taylor s (X^b.1.val):Polynomial ℂ):PowerSeries ℂ) a.1
  rw [← Polynomial.coe_mul] at hh
  simpa only [Polynomial.coeff_coe,Boundary.timeMatrix,translate,Matrix.map_apply,
    coeff_mul_X_pow',matrix] using hh

end ExactFourier.Taylor

end

section
namespace ExactFourier.Taylor
open Polynomial CoefficientTime
open scoped Kronecker

theorem diagonal_factorization (t : ℕ) (s : ℂ) :
    matrix t s = Matrix.diagonal (fun i : Fin t => (i.val.factorial:ℂ)⁻¹) *
      (truncMatrix t (kernel s)).transpose * Matrix.diagonal (fun j : Fin t => (j.val.factorial:ℂ)) := by
  ext i j
  rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
  simp only [matrix,taylor_X_pow,coeff_X_add_C_pow,Matrix.transpose_apply,truncMatrix,kernel,PowerSeries.coeff_mk]
  by_cases hij : i.val≤j.val
  · rw [ite_eq_left hij]
    have hfac : (j.val.choose i.val:ℂ)*(i.val.factorial:ℂ)*((j.val-i.val).factorial:ℂ)=(j.val.factorial:ℂ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hij
    have hi : (i.val.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero i.val
    have hd : ((j.val-i.val).factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (j.val-i.val)
    field_simp
    linear_combination s^(j.val-i.val)*hfac
  · rw [ite_eq_right hij,Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem price (p : MatrixPrice) (t : ℕ) (ht : 0<t) (s : ℂ) :
    p.value (matrix t s) ≤ (627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  have hu : IsUnit (truncMatrix t (kernel s)) := trunc_isUnit t _ (by simp)
  rw [diagonal_factorization,p.monomial _ _ _ ((Matrix.isUnit_transpose _).mpr hu)
    (MonomialMatrix.diagonal _ (fun i => inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i.val)))
    (MonomialMatrix.diagonal _ (fun i => by exact_mod_cast Nat.factorial_ne_zero i.val)),p.transpose _ hu]
  exact ScalarConvolution.price_truncation p t ht _ (by simp)

variable {α : Type} [Fintype α] [DecidableEq α]

theorem conjugacy (t : ℕ) (ht : 0<t) (s : ℂ) (G : Matrix α α (Polynomial ℂ)) :
    let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
    P*Boundary.modulusMatrix t ((X-C s)^t) G*P⁻¹=Boundary.timeMatrix t (translate s G) := by
  let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t s) isUnit_one
  change P*_*P⁻¹=_
  rw [intertwine t ht s G,Matrix.mul_assoc,
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det _).mp hP),mul_one]

theorem modulus_unit (t : ℕ) (ht : 0<t) (s : ℂ) (G : Matrix α α (Polynomial ℂ))
    (hG : IsUnit (G.map (Polynomial.eval s))) :
    IsUnit (Boundary.modulusMatrix t ((X-C s)^t) G) := by
  have hT : IsUnit (Boundary.timeMatrix t (translate s G)) := by
    rw [Boundary.timeMatrix_eq_trunc]
    apply blockTrunc_isUnit
    have he0 : (Boundary.seriesMatrix (translate s G)).map PowerSeries.constantCoeff = G.map (Polynomial.eval s) := by
      ext i j; simp [translate]
    rw [he0]
    exact hG
  have he := conjugacy t ht s G
  let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t s) isUnit_one
  change P*_*P⁻¹=_ at he
  rw [← he] at hT
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hT
  rw [Matrix.det_mul,Matrix.det_mul] at hd
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hd)).1).2

theorem modulus_lower (p : MatrixPrice) (t : ℕ) (ht : 0<t) (s : ℂ)
    (G : Matrix α α (Polynomial ℂ)) (hG : IsUnit (G.map (Polynomial.eval s))) :
    (t:ℝ)*p.value (G.map (Polynomial.eval s)) ≤
      p.value (Boundary.modulusMatrix t ((X-C s)^t) G) +
        2*(Fintype.card α:ℝ)*(627/Real.log 2)*(t:ℝ)*Real.log (2*t) := by
  let P := matrix t s ⊗ₖ (1 : Matrix α α ℂ)
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t s) isUnit_one
  have hW := modulus_unit t ht s G hG
  have hconj := p.conjugate_le P _ hP hW
  rw [conjugacy t ht s G] at hconj
  have he0 : (Boundary.seriesMatrix (translate s G)).map PowerSeries.constantCoeff =
      G.map (Polynomial.eval s) := by ext i j; simp [translate]
  have hlow := p.trunc_lower_bound t (Boundary.seriesMatrix (translate s G)) (by rw [he0]; exact hG)
  rw [he0,← Boundary.timeMatrix_eq_trunc] at hlow
  have hp := price p t ht s
  have hPt : p.value P=(Fintype.card α:ℝ)*p.value (matrix t s) := by
    rw [p.tensor _ _ (matrix_unit t s) isUnit_one,p.one,mul_zero,add_zero]
  rw [hPt] at hconj
  have hp' := mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤Fintype.card α by positivity)
  nlinarith

end ExactFourier.Taylor

end

section
namespace ExactFourier.CellPoly
open Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

@[simp] theorem eval_Z
    {β : Type} [Fintype β] [DecidableEq β] (D : Matrix β β ℂ) (s : ℂ) :
    (Z D).map (evalRingHom s)=1-s•D := by
  rw [Z,Matrix.map_sub _ (map_sub (evalRingHom s)),map_smul,
    Matrix.map_one _ (map_zero (evalRingHom s)) (map_one (evalRingHom s))]
  simp only [coe_evalRingHom,eval_X]
  congr 2
  ext i j
  exact eval_C

@[simp] theorem eval_a (D : Matrix β β ℂ) (s : ℂ) : (a D).eval s=(1-s•D).det := by
  change evalRingHom s ((Z D).det)=_
  rw [RingHom.map_det,RingHom.mapMatrix_apply,eval_Z]

@[simp] theorem eval_R (D : Matrix β β ℂ) (s : ℂ) :
    (R D).map (evalRingHom s)=(1-s•D).adjugate := by
  change (evalRingHom s).mapMatrix (Z D).adjugate=_
  rw [RingHom.map_adjugate,RingHom.mapMatrix_apply,eval_Z]

theorem adjugate_eq_det_smul_inv (A : Matrix β β ℂ) (hA : IsUnit A) :
    A.adjugate=A.det•A⁻¹ := by
  have h := congrArg (fun Q : Matrix β β ℂ => Q*A⁻¹) (Matrix.adjugate_mul A)
  rw [Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),mul_one,
    Matrix.smul_mul,one_mul] at h
  exact h

theorem eval_F
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ)
    (hD : IsUnit (1-s•D)) :
    (F M C B D).map (evalRingHom s)=(a D).eval s • feedback M C B D s := by
  rw [F,Matrix.map_add _ (map_add (evalRingHom s)),map_smul,map_smul,
    Matrix.map_mul,Matrix.map_mul,eval_R]
  have hconst {ι κ : Type} (X : Matrix ι κ ℂ) : (X.map Polynomial.C).map (evalRingHom s)=X := by ext i j; simp
  rw [hconst,hconst,hconst,adjugate_eq_det_smul_inv _ hD]
  simp only [coe_evalRingHom,eval_X,eval_a,feedback,smul_add,Matrix.mul_smul,Matrix.smul_mul]
  congr 1
  exact smul_comm _ _ _

end ExactFourier.CellPoly

end

section
/-! The real limit used by the boundary comparison argument. Only the fixed real
prices are compared; no continuity of a price functional is used. -/
namespace ExactFourier
open Filter Topology

theorem boundaryError_tendsto : Tendsto boundaryError atTop (𝓝 0) := by
  have h1 : Tendsto (fun m : ℕ => (m:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun m : ℕ => (m:ℝ)+2) atTop atTop :=
    tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  have hi1 : Tendsto (fun m : ℕ => 1/((m:ℝ)+1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h1
  have hi2 : Tendsto (fun m : ℕ => 1/((m:ℝ)+2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop h2
  have hl : Tendsto (fun m : ℕ => Real.log ((m:ℝ)+2)/((m:ℝ)+2)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp h2
  have ha := (hi1.const_mul (Real.log 2)).add
    ((hl.mul ((tendsto_const_nhds (x := (1:ℝ))).add hi1)).const_mul 8)
  have hb := ha.add ((hi2.pow 2).mul hi1)
  simp only [mul_zero,zero_mul,add_zero] at hb
  convert hb using 1
  funext m
  have hn1 : (m:ℝ)+1 ≠ 0 := by positivity
  have hn2 : (m:ℝ)+2 ≠ 0 := by positivity
  dsimp [boundaryError]
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (pow_ne_zero _ hn2),Real.log_pow]
  field_simp
  ring

theorem fixed_price_of_boundary (x y C : ℝ)
    (h : ∀ k t : ℕ, 0 < k → 0 < t →
      (t:ℝ)*k*(x-y) ≤ C*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6)) : x ≤ y := by
  have he (m : ℕ) : x-y ≤ C*boundaryError m := by
    have hh := h (m+1) ((m+2)^8) (by omega) (by positivity)
    push_cast at hh
    have ht : 0 < ((m:ℝ)+2)^8*((m:ℝ)+1) := by positivity
    have hh' : x-y ≤ (C*(((m:ℝ)+2)^8*Real.log (2*((m:ℝ)+2)^8)+((m:ℝ)+2)^6)) / (((m:ℝ)+2)^8*((m:ℝ)+1)) :=
      (le_div_iff₀ ht).mpr (by nlinarith only [hh])
    convert hh' using 1 ; dsimp [boundaryError] ; field_simp
  have hh := ge_of_tendsto (boundaryError_tendsto.const_mul C) (Filter.Eventually.of_forall he)
  have : x-y ≤ 0 := by simpa using hh
  linarith

end ExactFourier

end

section
/-! The literal feedback law; the state block D is not assumed invertible.
The limiting inequalities compare fixed matrix prices, never their continuity. -/
namespace ExactFourier.MatrixPrice
open TensorAxis CoefficientTime Polynomial
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

theorem feedback (p : MatrixPrice) (M : Matrix α α ℂ) (C : Matrix α β ℂ)
    (B : Matrix β α ℂ) (D : Matrix β β ℂ) (s : ℂ)
    (hM : IsUnit M) (hK : IsUnit (Matrix.fromBlocks M C B D))
    (hD : IsUnit (1-s•D)) (hH : IsUnit (CellPoly.feedback M C B D s)) :
    p.value (CellPoly.feedback M C B D s) ≤ p.value (Matrix.fromBlocks M C B D) := by
  by_cases hs : s=0
  · subst s
    simpa [CellPoly.feedback] using p.corner_block M C B D hM hK
  by_cases hn : Fintype.card α=0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    have he : CellPoly.feedback M C B D s=1 := by ext i; exact isEmptyElim i
    rw [he,p.one]
    exact p.nonneg _ hK
  let G := CellPoly.F M C B D
  let q := CellPoly.a D
  let H := CellSeries.transfer M C B D
  have hG0 : IsUnit (G.map (fun f => f.coeff 0)) := by
    have hE : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by funext f; exact coeff_zero_eq_eval_zero f
    rw [hE]
    simpa only [G,CellPoly.eval_F_zero] using hM
  have hq0 : q.coeff 0≠0 := by simp [q,coeff_zero_eq_eval_zero]
  have hqs : q.eval s≠0 := by
    simpa only [q,CellPoly.eval_a] using isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hD)
  have hGs : G.map (eval s)=q.eval s • CellPoly.feedback M C B D s := by
    rw [← coe_evalRingHom]
    exact CellPoly.eval_F M C B D s hD
  have hGu : IsUnit (G.map (eval s)) := by
    rw [hGs]
    exact scalar_unit _ hH _ hqs
  have hpGs : p.value (G.map (eval s))=p.value (CellPoly.feedback M C B D s) := by
    rw [hGs,p.scalar _ hH _ hqs]
  have hH0 : IsUnit (H.map PowerSeries.constantCoeff) := by
    simpa only [H,CellSeries.constant_transfer] using hM
  have hclear : Boundary.seriesMatrix G=(q:PowerSeries ℂ)•H := (CellPoly.cleared_transfer M C B D).symm
  obtain ⟨CB,hCB,hboundary⟩ := Boundary.exists_boundary_bound p G hG0
  obtain ⟨CK,hCK,hcascade⟩ := Cascade.uniform_bound p M C B D hM hK
  let CS : ℝ := 627/Real.log 2
  have hCS : 0≤CS := by dsimp [CS]; positivity
  let E : ℝ := CB+CK+3*CS
  apply fixed_price_of_boundary (p.value (CellPoly.feedback M C B D s))
    (p.value (Matrix.fromBlocks M C B D)) (E*Fintype.card α)
  intro k t hk ht
  let ℓ : Polynomial ℂ := (X-Polynomial.C s)^t
  have hℓ : ℓ.Monic := (monic_X_sub_C s).pow t
  have hℓt : ℓ.natDegree=t := by simp [ℓ]
  have hℓ0 : ℓ.coeff 0≠0 := by
    simp [ℓ,coeff_zero_eq_eval_zero,hs]
  have hmap : (power G k).map (eval s)=power (G.map (eval s)) k := by
    rw [← coe_evalRingHom]
    exact map_power (evalRingHom s) G k
  have hGpu : IsUnit ((power G k).map (eval s)) := by rw [hmap]; exact unit_power _ hGu k
  have hW := Taylor.modulus_unit t ht s (power G k) hGpu
  have hlow := Taylor.modulus_lower p t ht s (power G k) hGpu
  rw [hmap,price_power p _ hGu,hpGs,card_space] at hlow
  push_cast at hlow
  have hb := hboundary k t hk ht ℓ hℓ hℓt hℓ0 hW
  have hb' := (abs_le.mp hb).2
  have hc := Boundary.time_power_clearing_price p G H q hclear hq0 hH0 k t ht
  have hcas := hcascade k t ht
  have hN : 0<(Fintype.card α:ℝ)^k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) k
  have hkn : (k+1:ℝ)^3≤(k+1:ℝ)^6 := pow_le_pow_right₀ (by have := Nat.cast_nonneg k (α := ℝ); linarith : (1:ℝ)≤k+1) (by omega)
  have hlog : 0≤(t:ℝ)*Real.log (2*t) := by
    have htr : (1:ℝ)≤t := by exact_mod_cast ht
    exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hrel : (Fintype.card (Fibers α k):ℝ)*Fintype.card α=(k:ℝ)*(Fintype.card α:ℝ)^k := by
    have hh := Triangular.calls_card_relation (β := α) k
    change Fintype.card (Fibers α k)*Fintype.card α=k*Fintype.card (Space α k) at hh
    rw [card_space] at hh
    exact_mod_cast hh
  have herror : (t:ℝ)*Fintype.card (Fibers α k)*
      (p.value (CellPoly.feedback M C B D s)-p.value (Matrix.fromBlocks M C B D)) ≤
      E*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6) := by
    have hpown := mul_le_mul_of_nonneg_left hkn (mul_nonneg hCK hN.le)
    have hextra : 0≤3*CS*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by positivity
    dsimp only [H] at hc
    dsimp only [ℓ] at hb'
    dsimp only [E,CS] at hpown hextra ⊢
    nlinarith only [hlow,hb',hc,hcas,hpown,hextra]
  have hm := mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg (Fintype.card α) : (0:ℝ)≤_)
  apply (mul_le_mul_iff_right₀ hN).mp
  have ha := congrArg (fun a : ℝ => (t:ℝ)*a*
    (p.value (CellPoly.feedback M C B D s)-p.value (Matrix.fromBlocks M C B D))) hrel
  nlinarith only [hm,ha]

end ExactFourier.MatrixPrice

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.PivotAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.MatrixPrice

theorem pair_le_two_of_entry (p : MatrixPrice) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A) (ha : A 0 0≠0) : p.value A≤2 := by
  let L := Matrix.transvection (1 : Fin 2) 0 (A 1 0/A 0 0)
  let U := Matrix.transvection (0 : Fin 2) 1 (A 0 1/A 0 0)
  let d : Fin 2 → ℂ := ![A 0 0,A.det/A 0 0]
  have hdet : A.det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
  have hd : ∀ i,d i≠0 := by intro i; fin_cases i <;> simp [d,ha,hdet]
  have hL : IsUnit L := transvection_isUnit _ _ (by decide) _
  have hU : IsUnit U := transvection_isUnit _ _ (by decide) _
  have hD : IsUnit (Matrix.diagonal d) := Matrix.isUnit_diagonal.mpr
    (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hd i)))
  have he : A=L*(Matrix.diagonal d*U) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [L,U,d,Matrix.mul_apply,Fin.sum_univ_two,Matrix.diagonal_apply,
        Matrix.transvection,Matrix.single,Matrix.one_apply,Matrix.det_fin_two] <;>
      field_simp ; ring
  have hp := p.mul_le L (Matrix.diagonal d*U) hL (hD.mul hU)
  have hm := p.monomial U (Matrix.diagonal d) 1 hU (MonomialMatrix.diagonal d hd) MonomialMatrix.one
  rw [mul_one] at hm
  rw [← he,hm] at hp
  have hl := p.transvection_le_one (1 : Fin 2) 0 (by decide) (A 1 0/A 0 0)
  have hu := p.transvection_le_one (0 : Fin 2) 1 (by decide) (A 0 1/A 0 0)
  change p.value L≤1 at hl
  change p.value U≤1 at hu
  linarith

theorem pair_le_two (p : MatrixPrice) (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : IsUnit A) : p.value A≤2 := by
  by_cases ha : A 0 0≠0
  · exact p.pair_le_two_of_entry A hA ha
  · have ha0 : A 0 0=0 := not_ne_iff.mp ha
    have hc : A 1 0≠0 := by
      intro hc
      have hd := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hA)
      apply hd
      simp [Matrix.det_fin_two,ha0,hc]
    let e : Equiv.Perm (Fin 2) := Equiv.swap 0 1
    have hB : IsUnit (A.submatrix e (Equiv.refl _)) :=
      (Matrix.isUnit_submatrix_equiv e (Equiv.refl _)).mpr hA
    have hp := p.pair_le_two_of_entry (A.submatrix e (Equiv.refl _)) hB
      (by simpa [e,Matrix.submatrix_apply] using hc)
    rwa [p.submatrix_equiv A hA e (Equiv.refl _)] at hp

end ExactFourier.MatrixPrice

end

section
namespace ExactFourier
open scoped Kronecker
variable {β : Type} [Fintype β] [DecidableEq β]

theorem pairLayer_eq
    {β : Type} [Fintype β] [DecidableEq β] (A : Matrix (Fin 2) (Fin 2) ℂ) :
    pairLayer (β := β) A=Matrix.fromBlocks (A 0 0•1) (A 0 1•1) (A 1 0•1) (A 1 1•1) := by
  ext i j
  cases i <;> cases j <;> rfl

theorem pairLayer_unit (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A) :
    IsUnit (pairLayer (β := β) A) :=
  TensorTools.unit_reindex _ _ (TensorTools.unit_tensor _ _ hA isUnit_one)

namespace MatrixPrice
theorem pair_layer (p : MatrixPrice) (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : IsUnit A) :
    p.value (pairLayer (β := β) A)≤2*Fintype.card β := by
  rw [pairLayer,p.reindex _ _ (TensorTools.unit_tensor _ _ hA isUnit_one),
    p.tensor _ _ hA isUnit_one,p.one,mul_zero,add_zero]
  have h := mul_le_mul_of_nonneg_left (p.pair_le_two A hA) (Nat.cast_nonneg (Fintype.card β) : (0:ℝ)≤_)
  nlinarith only [h]
end MatrixPrice
end ExactFourier

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SignedPrice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier.Similarity
variable {α : Type} [Fintype α] [DecidableEq α]

theorem one (U : Matrix α α ℂ) (hU : IsUnit U) : conj U 1=1 := by
  rw [conj,mul_one,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]

theorem add (U A B : Matrix α α ℂ) : conj U (A+B)=conj U A+conj U B := by
  simp [conj,mul_add,add_mul]
theorem sub (U A B : Matrix α α ℂ) : conj U (A-B)=conj U A-conj U B := by
  simp [conj,mul_sub,sub_mul]
theorem smul (U A : Matrix α α ℂ) (c : ℂ) : conj U (c•A)=c•conj U A := by
  simp [conj]
theorem zero (U : Matrix α α ℂ) : conj U 0=0 := by simp [conj]

theorem mul (U A B : Matrix α α ℂ) (hU : IsUnit U) :
    conj U A*conj U B=conj U (A*B) := by
  calc
    _ = U*A*(U⁻¹*U)*B*U⁻¹ := by simp only [conj]; noncomm_ring
    _ = _ := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]; simp [conj,mul_assoc]

theorem unit (U A : Matrix α α ℂ) (hU : IsUnit U) (hA : IsUnit A) : IsUnit (conj U A) :=
  (hU.mul hA).mul (Matrix.isUnit_nonsing_inv_iff.mpr hU)

theorem diagonal_linear (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) (t : ℂ) :
    1+t•conj U (Matrix.diagonal a)=conj U (Matrix.diagonal (fun i=>1+t*a i)) := by
  have he : Matrix.diagonal (fun i=>1+t*a i)=(1 : Matrix α α ℂ)+t•Matrix.diagonal a := by
    ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]
  rw [he,add,smul,one U hU]

theorem diagonal_linear_sub (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) (t : ℂ) :
    1-t•conj U (Matrix.diagonal a)=conj U (Matrix.diagonal (fun i=>1-t*a i)) := by
  simpa [sub_eq_add_neg] using diagonal_linear U hU a (-t)

end ExactFourier.Similarity

end

section
noncomputable section
namespace ExactFourier.RealMatrix
variable {α : Type} [Fintype α] [DecidableEq α]

theorem map_mul
    {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℝ) : complex (A*B)=complex A*complex B := by
  exact Matrix.map_mul (f := Complex.ofRealHom)

theorem unit (A : Matrix α α ℝ) (h : IsUnit A) : IsUnit (complex A) := by
  obtain ⟨B,hB⟩ := isUnit_iff_exists_inv'.mp h
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨complex B,?_⟩
  rw [← map_mul,hB,map_one]

theorem inv (A : Matrix α α ℝ) (h : IsUnit A) : complex A⁻¹=(complex A)⁻¹ := by
  apply (unit A h).mul_right_cancel
  rw [← map_mul,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h),map_one]
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit A h))]

theorem diagonalization (A : Matrix α α ℝ) (hA : A.IsSymm) :
    ∃ U : Matrix α α ℝ,∃ a : α → ℝ,IsUnit U ∧ U⁻¹=U.transpose ∧
      A=U*Matrix.diagonal a*U⁻¹ := by
  have ha : A.IsHermitian := by
    change A.conjTranspose=A
    ext i j
    simpa [Matrix.conjTranspose] using congrFun (congrFun hA i) j
  let U : Matrix α α ℝ := ha.eigenvectorUnitary
  have ho : U*U.transpose=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self ha.eigenvectorUnitary
  have hU : IsUnit U := isUnit_iff_exists_inv.mpr ⟨U.transpose,ho⟩
  have hi : U⁻¹=U.transpose := by
    apply hU.mul_left_cancel
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]
    exact ho.symm
  refine ⟨U,ha.eigenvalues,hU,hi,?_⟩
  rw [hi]
  simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_real_eq_id, id_eq,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using ha.spectral_theorem

theorem complex_re
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (hA : ∀ i j,star (A i j)=A i j) :
    complex (A.map Complex.re)=A := by
  ext i j
  apply Complex.ext
  · simp [complex]
  · have hh := congrArg Complex.im (hA i j)
    simp only [Complex.star_def,Complex.conj_im] at hh
    simp only [complex,Matrix.map_apply,Complex.ofReal_im]
    linarith

theorem re_symm
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (hA : A.IsSymm) : (A.map Complex.re).IsSymm := by
  ext i j
  exact congrArg Complex.re (congrFun (congrFun hA i) j)

end ExactFourier.RealMatrix

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SymmetricLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

theorem det_ne_zero_of_eval_unit (G : Matrix α α (Polynomial ℂ)) (z0 : ℂ)
    (hG : IsUnit (G.map (eval z0))) : G.det≠0 := by
  intro he
  have hdu := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hG)
  apply hdu
  have hh := RingHom.map_det (evalRingHom z0) G
  rw [he,map_zero] at hh
  exact hh.symm

theorem unit_eval_of_not_mem_roots (G : Matrix α α (Polynomial ℂ)) (hG : G.det≠0)
    (s : ℂ) (hs : s∉G.det.roots.toFinset) : IsUnit (G.map (eval s)) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro he
  apply hs
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_roots hG).mpr
  exact (RingHom.map_det (evalRingHom s) G).trans he

end ExactFourier

end

section
noncomputable section
namespace ExactFourier.LinearProduct
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

@[simp] theorem eval_factor
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (s : ℂ) :
    (factor A).map (evalRingHom s)=1+s•A := by
  rw [factor,Matrix.map_add _ (map_add (evalRingHom s)),CellPoly.map_smul]
  ext i j
  simp [Matrix.one_apply]

@[simp] theorem coeff_zero_factor (A : Matrix α α ℂ) :
    (factor A).map (fun f => f.coeff 0)=1 := by
  have he : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
    funext f; exact coeff_zero_eq_eval_zero f
  rw [he,eval_factor]; simp

@[simp] theorem eval_zero_product (L : List (Matrix α α ℂ)) :
    (product L).map (evalRingHom 0)=1 := by
  induction L with
  | nil => simp [product]
  | cons a L ih => rw [product,Matrix.map_mul,eval_factor,ih]; simp

@[simp] theorem coeff_zero_product (L : List (Matrix α α ℂ)) :
    (product L).map (fun f => f.coeff 0)=1 := by
  have he : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
    funext f; exact coeff_zero_eq_eval_zero f
  rw [he,eval_zero_product]

end ExactFourier.LinearProduct

end
end

section
noncomputable section
namespace ExactFourier.MatrixPrice
open scoped Matrix
variable {α : Type} [Fintype α] [DecidableEq α]

theorem cayley_unit (A : Matrix α α ℂ) (t : ℂ)
    (hp : IsUnit (1+t•A)) (hm : IsUnit (1-t•A)) : IsUnit (cayley A t) :=
  hp.mul (Matrix.isUnit_nonsing_inv_iff.mpr hm)

theorem cayley_denominator
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (e t : ℂ) (het : e+t≠0) :
    1-(t/(e+t))•(1+e•A)=(e/(e+t))•(1-t•A) := by
  ext i j
  simp only [Matrix.sub_apply,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ; ring

theorem cayley_response (A : Matrix α α ℂ) (e t : ℂ)
    (he : e≠0) (het : e+t≠0) (hm : IsUnit (1-t•A)) :
    CellPoly.feedback ((e-t)•1) (1+e•A) ((2*e)•1) (1+e•A) (t/(e+t))=
      (e+t)•cayley A t := by
  let K := 1+e•A
  let W := 1-(t/(e+t))•K
  have heq : W=(e/(e+t))•(1-t•A) := cayley_denominator A e t het
  have hu : IsUnit W := by rw [heq]; exact scalar_unit _ hm _ (div_ne_zero he het)
  have hd := (Matrix.isUnit_iff_isUnit_det _).mp hu
  apply hu.mul_right_cancel
  change CellPoly.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t))*W=_
  have hL : CellPoly.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t))*W=
      (e-t)•W+((t/(e+t))*(2*e))•K := by
    simp only [CellPoly.feedback,add_mul,Matrix.smul_mul,Matrix.mul_smul,mul_one,one_mul,smul_smul]
    change (e-t)•W+((t/(e+t))*(2*e))•(K*W⁻¹*W)=_
    rw [Matrix.nonsing_inv_mul_cancel_right _ _ hd]
  rw [hL,heq,cayley,Matrix.smul_mul,Matrix.mul_smul,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hm),mul_one,smul_smul]
  ext i j
  simp only [K,Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ; ring

theorem cayley_feedback (p : MatrixPrice) (A : Matrix α α ℂ) (e t : ℂ)
    (he : e≠0) (hep : e+t≠0) (hem : e-t≠0)
    (hK : IsUnit (1+e•A)) (hp : IsUnit (1+t•A)) (hm : IsUnit (1-t•A)) :
    p.value (cayley A t)≤p.value (1+e•A)+2*Fintype.card α := by
  let K := 1+e•A
  let P : Matrix (Fin 2) (Fin 2) ℂ := !![e-t,1;2*e,1]
  have hP : IsUnit P := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    have hd : P.det=-(e+t) := by simp [P,Matrix.det_fin_two]; ring
    rw [hd]; exact neg_ne_zero.mpr hep
  let F := Matrix.fromBlocks ((e-t)•(1 : Matrix α α ℂ)) K ((2*e)•1) K
  have hf : F=pairLayer P*Matrix.fromBlocks (1 : Matrix α α ℂ) 0 0 K := by
    simp [F,pairLayer_eq,P,Matrix.fromBlocks_multiply]
  have hF : IsUnit F := by
    rw [hf]; exact (pairLayer_unit P hP).mul (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,hK⟩)
  have hM : IsUnit ((e-t)•(1 : Matrix α α ℂ)) := scalar_unit _ isUnit_one _ hem
  have hW : IsUnit (1-(t/(e+t))•K) := by
    rw [cayley_denominator A e t hep]; exact scalar_unit _ hm _ (div_ne_zero he hep)
  have hr := cayley_response A e t he hep hm
  have hCu := cayley_unit A t hp hm
  have hH : IsUnit (CellPoly.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t))) := by
    rw [hr]; exact scalar_unit _ hCu _ hep
  have hb := p.feedback ((e-t)•1) K ((2*e)•1) K (t/(e+t)) hM hF hW hH
  rw [hr,p.scalar _ hCu _ hep] at hb
  have hc := p.mul_le (pairLayer (β := α) P) (Matrix.fromBlocks 1 0 0 K)
    (pairLayer_unit P hP) (Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,hK⟩)
  rw [← hf,p.directSum _ _ isUnit_one hK,p.one,zero_add] at hc
  have hl := p.pair_layer (β := α) P hP
  linarith

end ExactFourier.MatrixPrice

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.DiagonalBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ExactFourier
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

namespace MatrixPrice

theorem diagonal_blocks (p : MatrixPrice) (t : ℕ) (A : Fin t → Matrix α α ℂ)
    (hA : ∀ i, IsUnit (A i)) :
    IsUnit (diagonalBlocks A) ∧ p.value (diagonalBlocks A)=∑ i, p.value (A i) := by
  have hu := (p.blocks_lower t (diagonalBlocks A) A hA
    (by intros; simp [diagonalBlocks])
    (by intro i j a b hij; simp [diagonalBlocks,ne_of_lt hij])).1
  refine ⟨hu,?_⟩
  induction t with
  | zero =>
    have he : diagonalBlocks A=1 := by ext i j; exact Fin.elim0 i.1
    rw [he,p.one]; simp
  | succ t ih =>
    have hD : IsUnit (diagonalBlocks (fun i : Fin t => A i.succ)) :=
      (p.blocks_lower t _ _ (fun i => hA i.succ)
        (by intros; simp [diagonalBlocks])
        (by intro i j a b hij; simp [diagonalBlocks,ne_of_lt hij])).1
    have he : Matrix.reindex (timeSplit t α) (timeSplit t α) (diagonalBlocks A)=
        Matrix.fromBlocks (A 0) 0 0 (diagonalBlocks (fun i : Fin t => A i.succ)) := by
      ext i j
      rcases i with a|⟨i,a⟩ <;> rcases j with b|⟨j,b⟩ <;>
        simp [Matrix.reindex_apply,Matrix.submatrix_apply,timeSplit,diagonalBlocks,
          Ne.symm (Fin.succ_ne_zero _)]
    rw [← p.reindex (timeSplit t α) _ hu,he,p.directSum _ _ (hA 0) hD,
      ih _ (fun i => hA i.succ) hD,Fin.sum_univ_succ]

end MatrixPrice
end ExactFourier

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped BigOperators Kronecker

theorem fourier_unit (t : ℕ) (ht : 0<t) (ω : ℂ) (hω : IsPrimitiveRoot ω t) :
    IsUnit (fourier t ω) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y h
  rw [fourier_mulVec,fourier_mulVec] at h
  have hh := congrArg (RadixTwo.eval t ω⁻¹) h
  rw [RadixTwo.eval_inverse ht ω hω,RadixTwo.eval_inverse ht ω hω] at hh
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt ht : (t:ℂ)≠0) (congrFun hh i)

theorem fourier_price (p : MatrixPrice) (j : ℕ) (ω : ℂ)
    (hω : IsPrimitiveRoot ω (2^j)) :
    p.value (fourier (2^j) ω) ≤ (26/Real.log 2)*(2^j:ℝ)*Real.log (2*2^j) := by
  obtain ⟨C,hC,hE⟩ := RadixTwo.exists_fft_dag j ω hω
  have hu := fourier_unit (2^j) (by positivity) ω hω
  have hprice := (p.le_shear _ hu).trans (p.rectangularShear_bound C _ hE)
  have hsize : (C.size:ℝ)≤3*(j:ℝ)*2^j := by exact_mod_cast hC
  have hlog : Real.log (2*2^j) = ((j:ℝ)+1)*Real.log 2 := by
    rw [← pow_succ',Real.log_pow]
    push_cast; ring
  rw [hlog]
  have hlog0 : Real.log 2≠0 := ne_of_gt (Real.log_pos (by norm_num))
  have he : (26/Real.log 2)*(2^j:ℝ)*(((j:ℝ)+1)*Real.log 2)=26*2^j*((j:ℝ)+1) := by field_simp
  rw [he]
  push_cast at hprice
  nlinarith [pow_pos (by norm_num : (0:ℝ)<2) j]

theorem matrix_eq (t : ℕ) (ω a : ℂ) :
    matrix t ω a=fourier t ω*Matrix.diagonal (fun j : Fin t => a^j.val) := by
  ext i j
  simp [matrix,fourier,Matrix.mul_diagonal,mul_pow,pow_mul,mul_comm]

theorem matrix_unit (t : ℕ) (ht : 0<t) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω t) (ha : a≠0) : IsUnit (matrix t ω a) := by
  rw [matrix_eq]
  exact (fourier_unit t ht ω hω).mul
    (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun j => isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha))))

theorem matrix_price (p : MatrixPrice) (j : ℕ) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω (2^j)) (ha : a≠0) :
    p.value (matrix (2^j) ω a)≤(26/Real.log 2)*(2^j:ℝ)*Real.log (2*2^j) := by
  rw [matrix_eq,← one_mul (fourier (2^j) ω),p.monomial _ _ _
    (fourier_unit _ (by positivity) ω hω) MonomialMatrix.one
    (MonomialMatrix.diagonal _ (fun i => pow_ne_zero _ ha))]
  exact fourier_price p j ω hω

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation
open Polynomial
open scoped Kronecker BigOperators

theorem coefficient_sum (t : ℕ) (ω a : ℂ) (f : Polynomial ℂ)
    (hf : f.natDegree<t) (i : Fin t) :
    f.eval (a*ω^i.val)=∑ j : Fin t, matrix t ω a i j*f.coeff j.val := by
  conv_lhs => rw [f.as_sum_range_C_mul_X_pow' hf]
  simp only [eval_finsetSum,eval_mul,eval_C,eval_pow,eval_X]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [matrix,mul_comm]

theorem eval_remainder (ℓ f : Polynomial ℂ) (s : ℂ) (hs : ℓ.eval s=0) :
    (f%ₘℓ).eval s=f.eval s := by
  rw [modByMonic_eq_sub_mul_div,eval_sub,eval_mul,hs,zero_mul,sub_zero]

variable {α : Type} [Fintype α] [DecidableEq α]

theorem intertwine (t : ℕ) (ht : 0<t) (ω a : ℂ) (ℓ : Polynomial ℂ)
    (hℓ : ℓ.Monic) (hℓt : ℓ.natDegree=t) (hs : ∀ i : Fin t,ℓ.eval (a*ω^i.val)=0)
    (G : Matrix α α (Polynomial ℂ)) :
    (matrix t ω a ⊗ₖ (1 : Matrix α α ℂ))*Boundary.modulusMatrix t ℓ G =
      diagonalBlocks (fun i : Fin t => G.map (eval (a*ω^i.val)))*
        (matrix t ω a ⊗ₖ (1 : Matrix α α ℂ)) := by
  ext ⟨ai,aj⟩ ⟨bi,bj⟩
  simp only [Matrix.mul_apply,Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply,
    diagonalBlocks,ite_mul,mul_ite,mul_one,mul_zero,zero_mul]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  have hne : ℓ≠1 := by
    intro he
    have hh := congrArg Polynomial.natDegree he
    rw [hℓt] at hh
    simp only [natDegree_one] at hh
    omega
  have hd := natDegree_modByMonic_lt (G aj bj*X^bi.val) hℓ hne
  rw [hℓt] at hd
  simp only [Boundary.modulusMatrix,Finset.sum_ite_irrel,Finset.sum_const_zero,
    Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← coefficient_sum t ω a _ hd ai,eval_remainder _ _ _ (hs ai)]
  simp [eval_mul,eval_pow,eval_X,matrix,mul_comm]

theorem root_modulus (t : ℕ) (ht : 0<t) (ω a : ℂ) (hω : IsPrimitiveRoot ω t)
    (i : Fin t) : (X^t-C (a^t) : Polynomial ℂ).eval (a*ω^i.val)=0 := by
  obtain ⟨size, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  simp only [eval_sub,eval_pow,eval_X,eval_C,mul_pow,← pow_mul]
  rw [Nat.mul_comm i.val size.succ,pow_mul,hω.pow_eq_one,one_pow,mul_one,sub_self]

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation
open Polynomial TensorAxis
open scoped Kronecker BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

theorem modulus_upper (p : MatrixPrice) (j : ℕ) (ω a : ℂ)
    (hω : IsPrimitiveRoot ω (2^j)) (ha : a≠0)
    (G : Matrix α α (Polynomial ℂ))
    (hG : ∀ i : Fin (2^j),IsUnit (G.map (eval (a*ω^i.val)))) :
    IsUnit (Boundary.modulusMatrix (2^j) (X^(2^j)-C (a^(2^j))) G) ∧
      p.value (Boundary.modulusMatrix (2^j) (X^(2^j)-C (a^(2^j))) G) ≤
        (∑ i : Fin (2^j),p.value (G.map (eval (a*ω^i.val))))+
          2*(Fintype.card α:ℝ)*(26/Real.log 2)*(2^j:ℝ)*Real.log (2*2^j) := by
  let t : ℕ := 2^j
  have ht : 0<t := by dsimp [t]; positivity
  let ℓ : Polynomial ℂ := X^t-C (a^t)
  have hℓ : ℓ.Monic := monic_X_pow_sub_C _ (Nat.ne_of_gt ht)
  have hℓt : ℓ.natDegree=t := natDegree_X_pow_sub_C
  let P := matrix t ω a ⊗ₖ (1 : Matrix α α ℂ)
  let W := Boundary.modulusMatrix t ℓ G
  let D := diagonalBlocks (fun i : Fin t => G.map (eval (a*ω^i.val)))
  have hP : IsUnit P := TensorTools.unit_tensor _ _ (matrix_unit t ht ω a hω ha) isUnit_one
  obtain ⟨hDu,hDp⟩ := p.diagonal_blocks t _ hG
  change IsUnit D at hDu
  change p.value D=_ at hDp
  have he : P*W=D*P := intertwine t ht ω a ℓ hℓ hℓt (root_modulus t ht ω a hω) G
  have hW : IsUnit W := by
    have hh : IsUnit (P*W) := by rw [he]; exact hDu.mul hP
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp hh
    rw [Matrix.det_mul] at hd
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (mul_ne_zero_iff.mp (isUnit_iff_ne_zero.mp hd)).2)
  refine ⟨hW,?_⟩
  have hconj : P*W*P⁻¹=D := by
    rw [he,Matrix.mul_assoc,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP),mul_one]
  have hprice := p.le_conjugate P W hP hW
  rw [hconj,hDp] at hprice
  have hp : p.value P=(Fintype.card α:ℝ)*p.value (matrix t ω a) := by
    rw [p.tensor _ _ (matrix_unit t ht ω a hω ha) isUnit_one,p.one,mul_zero,add_zero]
  rw [hp] at hprice
  have hv := matrix_price p j ω a hω ha
  have hv' := mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤Fintype.card α by positivity)
  change p.value W≤_
  dsimp only [t] at hprice
  nlinarith only [hprice,hv']

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier.RootEvaluation

theorem exists_dilation (t : ℕ) (ω : ℂ) (hω : ω≠0) (E : Finset ℂ) :
    ∃ a : ℂ, a≠0 ∧ ∀ i : Fin t, a*ω^i.val ∉ E := by
  classical
  let F : Finset ℂ := insert 0 (Finset.univ.biUnion (fun i : Fin t => E.image (fun s => s/ω^i.val)))
  obtain ⟨a,ha⟩ := F.exists_notMem
  refine ⟨a,?_,?_⟩
  · intro he
    apply ha
    simp [F,he]
  · intro i hi
    apply ha
    apply Finset.mem_insert_of_mem
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨a*ω^i.val,hi,?_⟩⟩
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ hω)

end ExactFourier.RootEvaluation

end

section
namespace ExactFourier
open Filter Topology

theorem exists_dyadic_between (b : ℕ) (hb : 0<b) : ∃ j : ℕ, b≤2^j ∧ 2^j≤2*b := by
  refine ⟨Nat.log 2 b+1,(Nat.lt_pow_succ_log_self (by decide : 1<2) b).le,?_⟩
  have hh := Nat.pow_log_le_self 2 (Nat.ne_of_gt hb)
  rw [pow_succ]
  omega

theorem fixed_price_of_dyadic_boundary (x y C : ℝ) (hC : 0≤C)
    (h : ∀ k j : ℕ, 0<k →
      (2^j:ℝ)*k*(x-y) ≤ C*((2^j:ℝ)*Real.log (2*2^j)+(k+1:ℝ)^6)) : x≤y := by
  have he (m : ℕ) : x-y ≤ (2*C)*boundaryError m := by
    let b : ℕ := (m+2)^8
    have hb : 0<b := by dsimp [b]; positivity
    obtain ⟨j,hlo,hhi⟩ := exists_dyadic_between b hb
    let T : ℕ := 2^j
    have hTr : 0<(T:ℝ) := by exact_mod_cast (pow_pos (by decide : 0<2) j)
    have hbr : (b:ℝ)=((m:ℝ)+2)^8 := by dsimp [b]; push_cast; rfl
    have hk : 0<(m:ℝ)+1 := by positivity
    have hb1 : (1:ℝ)≤b := by exact_mod_cast (hb : 1≤b)
    have hloR : (b:ℝ)≤T := by exact_mod_cast hlo
    have hhiR : (T:ℝ)≤2*b := by exact_mod_cast hhi
    have hln : Real.log (2*(T:ℝ)) ≤ 2*Real.log (2*b) := by
      have harg : 2*(T:ℝ)≤(2*(b:ℝ))^2 := by nlinarith
      have hh := Real.log_le_log (by positivity : (0:ℝ)<2*T) harg
      simpa only [Real.log_pow,Nat.cast_ofNat] using hh
    have hln0 : 0≤Real.log (2*(b:ℝ)) := Real.log_nonneg (by linarith)
    have hr : ((m:ℝ)+2)^6 / ((T:ℝ)*((m:ℝ)+1)) ≤
        ((m:ℝ)+2)^6 / ((b:ℝ)*((m:ℝ)+1)) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right hloR hk.le
    have hlog : Real.log (2*(T:ℝ))/((m:ℝ)+1) ≤
        2*Real.log (2*(b:ℝ))/((m:ℝ)+1) := by exact div_le_div_of_nonneg_right hln hk.le
    have herr : Real.log (2*(T:ℝ))/((m:ℝ)+1)+
        ((m:ℝ)+2)^6/((T:ℝ)*((m:ℝ)+1)) ≤2*boundaryError m := by
      have hfrac : 0≤((m:ℝ)+2)^6/((b:ℝ)*((m:ℝ)+1)) := by positivity
      dsimp only [boundaryError]
      rw [← hbr]
      rw [mul_div_assoc] at hlog
      nlinarith only [hr,hlog,hfrac]
    have hh := h (m+1) j (by omega)
    have hTR : (2^j:ℝ)=(T:ℝ) := by dsimp [T]; norm_cast
    rw [hTR] at hh
    push_cast at hh
    have hnorm : x-y ≤ C*(Real.log (2*(T:ℝ))/((m:ℝ)+1)+
        ((m:ℝ)+2)^6/((T:ℝ)*((m:ℝ)+1))) := by
      have hn : x-y ≤ (C*((T:ℝ)*Real.log (2*T)+((m:ℝ)+2)^6))/((T:ℝ)*((m:ℝ)+1)) :=
        (le_div_iff₀ (mul_pos hTr hk)).mpr (by nlinarith only [hh])
      convert hn using 1 ; field_simp
    calc
      x-y ≤ _ := hnorm
      _ ≤ C*(2*boundaryError m) := mul_le_mul_of_nonneg_left herr hC
      _ = (2*C)*boundaryError m := by ring
  have hh := ge_of_tendsto (boundaryError_tendsto.const_mul (2*C)) (Filter.Eventually.of_forall he)
  have : x-y≤0 := by simpa using hh
  linarith

end ExactFourier

end

section
namespace ExactFourier.MatrixPrice
open TensorAxis Polynomial CoefficientTime
open scoped BigOperators
variable {α : Type} [Fintype α] [DecidableEq α]

theorem specialize_polynomial_zero (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ))
    (hG0 : IsUnit (G.map (eval 0))) (E : Finset ℂ) (C0 : ℝ)
    (hG : ∀ s : ℂ, s∉E → IsUnit (G.map (eval s)) ∧ p.value (G.map (eval s))≤C0) :
    p.value (G.map (eval 0))≤C0 := by
  classical
  obtain ⟨s,hs⟩ := E.exists_notMem
  have hC0 : 0≤C0 := (p.nonneg _ (hG s hs).1).trans (hG s hs).2
  by_cases hn : Fintype.card α=0
  · have : IsEmpty α := Fintype.card_eq_zero_iff.mp hn
    have he : G.map (eval 0)=1 := by ext i; exact isEmptyElim i
    rw [he,p.one]
    exact hC0
  have hcoeff : (fun f : Polynomial ℂ => f.coeff 0)=evalRingHom 0 := by
    funext f; exact coeff_zero_eq_eval_zero f
  have hGu0 : IsUnit (G.map (fun f => f.coeff 0)) := by
    rw [hcoeff,coe_evalRingHom]; exact hG0
  obtain ⟨CB,hCB,hboundary⟩ := Boundary.exists_boundary_bound p G hGu0
  let C : ℝ := CB+52/Real.log 2
  have hC : 0≤C := by dsimp [C]; positivity
  apply fixed_price_of_dyadic_boundary (p.value (G.map (eval 0))) C0
    (C*Fintype.card α) (by positivity)
  intro k j hk
  let t : ℕ := 2^j
  have ht : 0<t := by dsimp [t]; positivity
  let ω := zeta t
  have hω : IsPrimitiveRoot ω t := Complex.isPrimitiveRoot_exp _ (Nat.ne_of_gt ht)
  obtain ⟨a,ha,had⟩ := RootEvaluation.exists_dilation t ω (hω.ne_zero (Nat.ne_of_gt ht)) E
  let ℓ : Polynomial ℂ := X^t-Polynomial.C (a^t)
  have hℓ : ℓ.Monic := monic_X_pow_sub_C _ (Nat.ne_of_gt ht)
  have hℓt : ℓ.natDegree=t := natDegree_X_pow_sub_C
  have hℓ0 : ℓ.coeff 0≠0 := by simp [ℓ,coeff_zero_eq_eval_zero,Nat.ne_of_gt ht,ha]
  have hmap (s : ℂ) : (power G k).map (eval s)=power (G.map (eval s)) k := by
    rw [← coe_evalRingHom]
    exact map_power (evalRingHom s) G k
  have hroots (i : Fin t) : IsUnit ((power G k).map (eval (a*ω^i.val))) := by
    rw [hmap]; exact unit_power _ (hG _ (had i)).1 k
  obtain ⟨hWu,hupper⟩ := RootEvaluation.modulus_upper p j ω a hω ha (power G k) hroots
  have hblocks : (∑ i : Fin t,p.value ((power G k).map (eval (a*ω^i.val))))≤
      (t:ℝ)*Fintype.card (Fibers α k)*C0 := by
    calc
      _ ≤ ∑ i : Fin t,(Fintype.card (Fibers α k):ℝ)*C0 := by
        apply Finset.sum_le_sum
        intro i hi
        rw [hmap,price_power p _ (hG _ (had i)).1]
        exact mul_le_mul_of_nonneg_left (hG _ (had i)).2 (by positivity)
      _ = _ := by simp; ring
  have hb := hboundary k t hk ht ℓ hℓ hℓt hℓ0 hWu
  have hconst : (Boundary.seriesMatrix (power G k)).map PowerSeries.constantCoeff=
      power (G.map (eval 0)) k := by
    have he : (Boundary.seriesMatrix (power G k)).map PowerSeries.constantCoeff=
        (power G k).map (eval 0) := by ext i l; simp [coeff_zero_eq_eval_zero]
    rw [he,hmap]
  have hlow := p.trunc_lower_bound t (Boundary.seriesMatrix (power G k))
    (by rw [hconst]; exact unit_power _ hG0 k)
  rw [hconst,price_power p _ hG0,← Boundary.timeMatrix_eq_trunc] at hlow
  rw [card_space] at hupper
  push_cast at hupper
  have hN : 0<(Fintype.card α:ℝ)^k := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hn) k
  have herror : (t:ℝ)*Fintype.card (Fibers α k)*(p.value (G.map (eval 0))-C0)≤
      C*(Fintype.card α:ℝ)^k*((t:ℝ)*Real.log (2*t)+(k+1:ℝ)^6) := by
    have hb' := (abs_le.mp hb).1
    have hextra : 0≤(52/Real.log 2)*(Fintype.card α:ℝ)^k*(k+1:ℝ)^6 := by positivity
    dsimp only [ℓ,t] at hb' hblocks hlow ⊢
    push_cast at hb' hblocks hlow ⊢
    dsimp only [C]
    simp only [div_eq_mul_inv] at hupper hextra ⊢
    nlinarith only [hb',hupper,hlow,hblocks,hextra]
  have hrel : (Fintype.card (Fibers α k):ℝ)*Fintype.card α=(k:ℝ)*(Fintype.card α:ℝ)^k := by
    have hh := Triangular.calls_card_relation (β := α) k
    change Fintype.card (Fibers α k)*Fintype.card α=k*Fintype.card (Space α k) at hh
    rw [card_space] at hh
    exact_mod_cast hh
  have hm := mul_le_mul_of_nonneg_right herror (Nat.cast_nonneg (Fintype.card α) : (0:ℝ)≤_)
  apply (mul_le_mul_iff_right₀ hN).mp
  have ha := congrArg (fun v : ℝ => (t:ℝ)*v*(p.value (G.map (eval 0))-C0)) hrel
  dsimp only [t] at hm ha
  push_cast at hm ha
  nlinarith only [hm,ha]

end ExactFourier.MatrixPrice

end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.RationalClearing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.MatrixPrice
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

theorem cayley_tangent (p : MatrixPrice) (Q : Matrix α α (Polynomial ℂ))
    (E : Finset ℂ) (C0 : ℝ)
    (hQ : ∀ s : ℂ,s∉E → IsUnit (1+s•Q.map (eval s)) ∧ p.value (1+s•Q.map (eval s))≤C0)
    (t : ℂ) (hp : IsUnit (1+t•Q.map (eval 0))) (hm : IsUnit (1-t•Q.map (eval 0))) :
    p.value (cayley (Q.map (eval 0)) t)≤C0+2*Fintype.card α := by
  classical
  let P : Matrix α α (Polynomial ℂ) := 1+Polynomial.C t•Q
  let M : Matrix α α (Polynomial ℂ) := 1-Polynomial.C t•Q
  have hP (s : ℂ) : P.map (eval s)=1+t•Q.map (eval s) := by
    change P.map (evalRingHom s)=_
    dsimp only [P]
    rw [Matrix.map_add _ (map_add (evalRingHom s)),CellPoly.map_smul]
    simp
  have hM (s : ℂ) : M.map (eval s)=1-t•Q.map (eval s) := by
    change M.map (evalRingHom s)=_
    dsimp only [M]
    rw [Matrix.map_sub _ (map_sub (evalRingHom s)),CellPoly.map_smul]
    simp
  have hp0 : IsUnit (P.map (eval 0)) := by rw [hP]; exact hp
  have hm0 : IsUnit (M.map (eval 0)) := by rw [hM]; exact hm
  have hpd := det_ne_zero_of_eval_unit P 0 hp0
  have hmd := det_ne_zero_of_eval_unit M 0 hm0
  let G : Matrix α α (Polynomial ℂ) := P*M.adjugate
  have he (s : ℂ) (hmu : IsUnit (1-t•Q.map (eval s))) :
      G.map (eval s)=(1-t•Q.map (eval s)).det•cayley (Q.map (eval s)) t := by
    change G.map (evalRingHom s)=_
    dsimp only [G]
    rw [Matrix.map_mul]
    have hh := RingHom.map_adjugate (evalRingHom s) M
    change (M.adjugate).map (evalRingHom s)=(M.map (evalRingHom s)).adjugate at hh
    rw [hh]
    change P.map (eval s)*(M.map (eval s)).adjugate=_
    rw [hP,hM,CellPoly.adjugate_eq_det_smul_inv _ hmu,Matrix.mul_smul]
    rfl
  have hc0 := cayley_unit (Q.map (eval 0)) t hp hm
  have hd0 : (1-t•Q.map (eval 0)).det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hm)
  have hg0 : IsUnit (G.map (eval 0)) := by rw [he 0 hm]; exact scalar_unit _ hc0 _ hd0
  have hprice0 : p.value (G.map (eval 0))=p.value (cayley (Q.map (eval 0)) t) := by
    rw [he 0 hm,p.scalar _ hc0 _ hd0]
  rw [← hprice0]
  apply p.specialize_polynomial_zero G hg0 (E∪P.det.roots.toFinset∪M.det.roots.toFinset∪{0,t,-t})
    (C0+2*Fintype.card α)
  intro s hs
  have hse : s∉E := by intro h; apply hs; simp [h]
  have hsp : s∉P.det.roots.toFinset := by intro h; apply hs; simp [h]
  have hsm : s∉M.det.roots.toFinset := by intro h; apply hs; simp [h]
  have hs0 : s≠0 := by intro h; apply hs; simp [h]
  have hst : s-t≠0 := by intro h; apply hs; simp [sub_eq_zero.mp h]
  have hst' : s+t≠0 := by intro h; apply hs; simp [eq_neg_of_add_eq_zero_left h]
  have hpu : IsUnit (1+t•Q.map (eval s)) := by
    rw [← hP]; exact unit_eval_of_not_mem_roots P hpd s hsp
  have hmu : IsUnit (1-t•Q.map (eval s)) := by
    rw [← hM]; exact unit_eval_of_not_mem_roots M hmd s hsm
  have hcu := cayley_unit (Q.map (eval s)) t hpu hmu
  have hd : (1-t•Q.map (eval s)).det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hmu)
  obtain ⟨hku,hkp⟩ := hQ s hse
  rw [he s hmu]
  refine ⟨scalar_unit _ hcu _ hd,?_⟩
  rw [p.scalar _ hcu _ hd]
  exact (p.cayley_feedback (Q.map (eval s)) s t hs0 hst' hst hku hpu hmu).trans (add_le_add hkp le_rfl)

end ExactFourier.MatrixPrice

end
end

section
noncomputable section
namespace ExactFourier.CayleyLimit
open Polynomial
variable {α : Type} [Fintype α] [DecidableEq α]

theorem denominator_factor (a : α → ℂ) (i : α) (hi : a i≠0) :
    denominator a=(X-Polynomial.C (a i))*except a i := by
  exact (Finset.mul_prod_erase _ _ (by simp [active,hi])).symm

theorem denominator_zero
    {α : Type} [Fintype α] [DecidableEq α] (a : α → ℂ) : (denominator a).eval 0≠0 := by
  rw [denominator,Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have h : a i≠0 := (Finset.mem_filter.mp hi).2
  simpa using neg_ne_zero.mpr h

theorem numerator_zero (a : α → ℂ) (i : α) :
    (numerator a i).eval 0=(denominator a).eval 0*sign a i := by
  by_cases hi : a i=0
  · simp [numerator,sign,hi]
  · rw [numerator,ite_eq_right hi,denominator_factor a i hi]
    simp [sign,hi]

theorem numerator_identity (a : α → ℂ) (i : α) (s : ℂ) (hs : s≠0) :
    (numerator a i).eval s*(1-s⁻¹*a i)=(denominator a).eval s*(1+s⁻¹*a i) := by
  by_cases hi : a i=0
  · simp [numerator,hi]
  · rw [numerator,ite_eq_right hi,denominator_factor a i hi]
    simp only [eval_mul,eval_add,eval_sub,eval_X,eval_C]
    field_simp


theorem eval_polynomial (U : Matrix α α ℂ) (a : α → ℂ) (s : ℂ) :
    (polynomial U a).map (evalRingHom s)=Similarity.conj U (Matrix.diagonal (fun i=>(numerator a i).eval s)) := by
  have hc (V : Matrix α α ℂ) : (V.map Polynomial.C).map (evalRingHom s)=V := by ext i j; simp
  rw [polynomial,Matrix.map_mul,Matrix.map_mul,hc,hc]
  have hd : (Matrix.diagonal (numerator a)).map (evalRingHom s)=Matrix.diagonal (fun i=>(numerator a i).eval s) := by
    ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]
  rw [hd]; rfl

theorem eval_zero (U : Matrix α α ℂ) (a : α → ℂ) :
    (polynomial U a).map (evalRingHom 0)=(denominator a).eval 0•Similarity.conj U (Matrix.diagonal (sign a)) := by
  rw [eval_polynomial]
  simp_rw [numerator_zero]
  rw [← Similarity.smul]
  congr 1
  ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]

theorem eval_as_cayley (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (s : ℂ) (hs : s≠0)
    (hm : IsUnit (1-s⁻¹•Similarity.conj U (Matrix.diagonal a))) :
    (polynomial U a).map (evalRingHom s)=(denominator a).eval s•
      MatrixPrice.cayley (Similarity.conj U (Matrix.diagonal a)) s⁻¹ := by
  apply hm.mul_right_cancel
  rw [eval_polynomial,Similarity.diagonal_linear_sub U hU,Similarity.mul U _ _ hU]
  rw [MatrixPrice.cayley,Matrix.smul_mul,← Similarity.diagonal_linear_sub U hU,Matrix.nonsing_inv_mul_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hm),
    Similarity.diagonal_linear U hU,← Similarity.smul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j; simpa using numerator_identity a i s hs
  · simp [Matrix.diagonal,h]

theorem generic_units (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (s : ℂ) (hs : s∉bad a) : s≠0 ∧ (denominator a).eval s≠0 ∧
    IsUnit (1+s⁻¹•Similarity.conj U (Matrix.diagonal a)) ∧
    IsUnit (1-s⁻¹•Similarity.conj U (Matrix.diagonal a)) := by
  classical
  have hs0 : s≠0 := by intro h; exact hs (by simp [bad,h])
  have hspos (i : α) : s≠a i := by intro h; exact hs (by simp [bad,h])
  have hsneg (i : α) : s≠-a i := by intro h; exact hs (by simp [bad,h])
  have hq : (denominator a).eval s≠0 := by
    rw [denominator,Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simpa using sub_ne_zero.mpr (hspos i))
  have hp (i : α) : 1+s⁻¹*a i≠0 := by
    intro hh
    have he : s+a i=0 := by field_simp [hs0] at hh; simpa using hh
    exact hsneg i (eq_neg_of_add_eq_zero_left he)
  have hm (i : α) : 1-s⁻¹*a i≠0 := by
    intro hh
    have he : s-a i=0 := by field_simp [hs0] at hh; simpa using hh
    exact hspos i (sub_eq_zero.mp he)
  refine ⟨hs0,hq,?_,?_⟩
  · rw [Similarity.diagonal_linear U hU]
    exact Similarity.unit _ _ hU (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i=>isUnit_iff_ne_zero.mpr (hp i))))
  · rw [Similarity.diagonal_linear_sub U hU]
    exact Similarity.unit _ _ hU (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i=>isUnit_iff_ne_zero.mpr (hm i))))

/-- The second specialization; no priced use of the diagonalizing basis is made. -/
theorem price (p : MatrixPrice) (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (C0 : ℝ)
    (hp : ∀ t : ℂ,IsUnit (1+t•Similarity.conj U (Matrix.diagonal a)) →
      IsUnit (1-t•Similarity.conj U (Matrix.diagonal a)) →
      p.value (MatrixPrice.cayley (Similarity.conj U (Matrix.diagonal a)) t)≤C0) :
    p.value (Similarity.conj U (Matrix.diagonal (sign a)))≤C0 := by
  have hR : IsUnit (Similarity.conj U (Matrix.diagonal (sign a))) := by
    apply Similarity.unit _ _ hU
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro i
    simp only [sign]
    split_ifs <;> simp
  have hG0 : IsUnit ((polynomial U a).map (evalRingHom 0)) := by
    rw [eval_zero]; exact MatrixPrice.scalar_unit _ hR _ (denominator_zero a)
  have he0 : p.value ((polynomial U a).map (evalRingHom 0))=p.value (Similarity.conj U (Matrix.diagonal (sign a))) := by
    rw [eval_zero,p.scalar _ hR _ (denominator_zero a)]
  rw [← he0]
  apply p.specialize_polynomial_zero (polynomial U a) hG0 (bad a) C0
  intro s hs
  obtain ⟨hs0,hds,hpu,hmu⟩ := generic_units U hU a s hs
  have hcu := MatrixPrice.cayley_unit _ _ hpu hmu
  change IsUnit ((polynomial U a).map (evalRingHom s)) ∧ p.value ((polynomial U a).map (evalRingHom s))≤C0
  rw [eval_as_cayley U hU a s hs0 hmu]
  exact ⟨MatrixPrice.scalar_unit _ hcu _ hds,by rw [p.scalar _ hcu _ hds]; exact hp s⁻¹ hpu hmu⟩

end ExactFourier.CayleyLimit

end
end

section
noncomputable section
namespace ExactFourier.CayleyLimit
variable {α : Type} [Fintype α] [DecidableEq α]

theorem sign_square (a : α → ℂ) : Matrix.diagonal (sign a)*Matrix.diagonal (sign a)=(1 : Matrix α α ℂ) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j; simp [sign]; split_ifs <;> norm_num
  · simp [Matrix.diagonal,h]

theorem reflection_square (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    Similarity.conj U (Matrix.diagonal (sign a))*Similarity.conj U (Matrix.diagonal (sign a))=1 := by
  rw [Similarity.mul U _ _ hU,sign_square,Similarity.one U hU]

theorem killed_sum (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    Similarity.conj U (Matrix.diagonal a)*(1+Similarity.conj U (Matrix.diagonal (sign a)))=0 := by
  rw [← Similarity.one U hU,← Similarity.add,Similarity.mul U _ _ hU]
  rw [mul_add,mul_one,Matrix.diagonal_mul_diagonal]
  have hh : Matrix.diagonal a+Matrix.diagonal (fun i=>a i*sign a i)=0 := by
    ext i j
    by_cases h : i=j
    · subst j; simp [sign]; split_ifs <;> simp_all
    · simp [Matrix.diagonal,h]
  rw [hh,Similarity.zero]

theorem difference_factor (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    1-Similarity.conj U (Matrix.diagonal (sign a))=
      Similarity.conj U (Matrix.diagonal a)*Similarity.conj U (Matrix.diagonal (reciprocal a)) := by
  rw [Similarity.mul U _ _ hU,← Similarity.one U hU,← Similarity.sub]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j
    by_cases hi : a i=0 <;> simp [sign,reciprocal,hi]
    field_simp
    ring
  · simp [Matrix.diagonal,h]

theorem reflection_symm (U : Matrix α α ℂ) (hi : U⁻¹=U.transpose) (a : α → ℂ) :
    (Similarity.conj U (Matrix.diagonal (sign a))).IsSymm := by
  change (Similarity.conj U (Matrix.diagonal (sign a))).transpose=_
  simp [Similarity.conj,hi,Matrix.transpose_mul,mul_assoc]

end ExactFourier.CayleyLimit

end
end

end OAI
end

section
-- module Solutions.OAIQW_ExactFourier.SparseSpectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [DecidableEq α]

/-- Algebraic certificate for the real orthogonal reflection in the kernel, together
with its uniform sparse price.  Both annihilator equations are retained. -/
theorem spectral_price (p : MatrixPrice) (A : Matrix α α ℝ) (hA : A.IsSymm)
    (d : α → ℂ) (L : List (PairTerm α))
    (hL : RealMatrix.complex A=Matrix.diagonal d+(L.map PairTerm.direction).sum) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧
      RealMatrix.complex A*(1+R)=0 ∧ 1-R=RealMatrix.complex A*T ∧
      p.value R≤(3:ℝ)/2*L.length+2*Fintype.card α := by
  obtain ⟨U,a,hU,hi,he⟩ := RealMatrix.diagonalization A hA
  let V := RealMatrix.complex U
  let b : α → ℂ := fun i => (a i : ℂ)
  have hV : IsUnit V := RealMatrix.unit U hU
  have hec : RealMatrix.complex A=Similarity.conj V (Matrix.diagonal b) := by
    rw [he,RealMatrix.map_mul,RealMatrix.map_mul,RealMatrix.map_diagonal,RealMatrix.inv U hU]
    rfl
  have hiv : V⁻¹=V.transpose := by rw [← RealMatrix.inv U hU,hi,RealMatrix.map_transpose]
  let R := Similarity.conj V (Matrix.diagonal (CayleyLimit.sign b))
  refine ⟨R,Similarity.conj V (Matrix.diagonal (CayleyLimit.reciprocal b)),
    CayleyLimit.reflection_square V hV b,CayleyLimit.reflection_symm V hiv b,?_,?_,?_⟩
  · rw [hec]; exact CayleyLimit.killed_sum V hV b
  · rw [hec]; exact CayleyLimit.difference_factor V hV b
  · apply CayleyLimit.price p V hV b
    intro t hp hm
    obtain ⟨Q,E,hQ0,hQ⟩ := exists_tangent p d L
    have heQ : Q.map (Polynomial.eval 0)=Similarity.conj V (Matrix.diagonal b) := by
      rw [← hec,hL]; exact hQ0
    rw [← heQ] at hp hm ⊢
    exact p.cayley_tangent Q E ((3:ℝ)/2*L.length) hQ t hp hm

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [LinearOrder α]

theorem terms_sum (A : Matrix α α ℂ) (hA : A.IsSymm) :
    ((terms A hA).map PairTerm.direction).sum=
      ∑ ij∈pairs A,(Matrix.single ij.1 ij.2 (A ij.1 ij.2)+Matrix.single ij.2 ij.1 (A ij.2 ij.1)) := by
  simp only [terms,List.map_map,Finset.sum_map_toList,Function.comp_def,term,PairTerm.direction]
  exact Finset.sum_attach (pairs A) (fun ij => (Matrix.single ij.1 ij.2 (A ij.1 ij.2)+Matrix.single ij.2 ij.1 (A ij.2 ij.1)))

theorem decomposition (A : Matrix α α ℂ) (hA : A.IsSymm) :
    A=Matrix.diagonal (fun i=>A i i)+((terms A hA).map PairTerm.direction).sum := by
  rw [terms_sum,Finset.sum_add_distrib]
  ext i j
  have hl : (∑ ij∈pairs A,Matrix.single ij.1 ij.2 (A ij.1 ij.2)) i j=
      if (i,j)∈pairs A then A i j else 0 := by
    simp only [Matrix.sum_apply,Matrix.single_apply,← Prod.mk.injEq,Prod.mk.eta]
    simp
  have hr : (∑ ij∈pairs A,Matrix.single ij.2 ij.1 (A ij.2 ij.1)) i j=
      if (j,i)∈pairs A then A i j else 0 := by
    simp only [Matrix.sum_apply,Matrix.single_apply,and_comm (b := _=j),← Prod.mk.injEq,Prod.mk.eta]
    simp
  simp only [Matrix.add_apply,hl,hr,mem_pairs]
  by_cases hij : i=j
  · subst j; simp
  · rcases lt_or_gt_of_ne hij with hlt|hlt
    · simp [hij,hlt,not_lt_of_ge hlt.le]
    · simp [hij,hlt,not_lt_of_ge hlt.le,hA.apply i j]

theorem twice_pairs_le (A : Matrix α α ℂ) (hA : A.IsSymm) : 2*(pairs A).card≤nnz A := by
  classical
  let e : (α×α) ≃ (α×α) := Equiv.prodComm α α
  have hd : Disjoint (pairs A) ((pairs A).map e.toEmbedding) := by
    apply Finset.disjoint_left.mpr
    intro ij hi hj
    obtain ⟨ji,hji,he⟩ := Finset.mem_map.mp hj
    subst ij
    have h1 := ((mem_pairs A _).mp hi).1
    have h2 := ((mem_pairs A _).mp hji).1
    exact not_lt_of_ge h2.le h1
  have hs : pairs A∪(pairs A).map e.toEmbedding⊆support A := by
    intro ij hij
    rcases Finset.mem_union.mp hij with h|h
    · exact (mem_support A ij).mpr ((mem_pairs A ij).mp h).2
    · obtain ⟨ji,hji,rfl⟩ := Finset.mem_map.mp h
      apply (mem_support A _).mpr
      change A ji.2 ji.1≠0
      rw [show A ji.2 ji.1=A ji.1 ji.2 from congrFun (congrFun hA ji.1) ji.2]
      exact ((mem_pairs A _).mp hji).2
  have hh := Finset.card_le_card hs
  rw [Finset.card_union_of_disjoint hd,Finset.card_map] at hh
  simpa [two_mul,nnz] using hh

end ExactFourier.SparseReflection

end
end

section
noncomputable section
namespace ExactFourier.SparseReflection
variable {α : Type} [Fintype α] [LinearOrder α]

/-- Uniform sparse reflection certificate, with supported unordered pairs counted exactly.
The annihilator identities characterize the reflection when A is real symmetric. -/
theorem exists_reflection (p : MatrixPrice) (A : Matrix α α ℂ) (hA : A.IsSymm)
    (hreal : ∀ i j,star (A i j)=A i j) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧ A*(1+R)=0 ∧ 1-R=A*T ∧
      p.value R≤(3:ℝ)/2*(pairs A).card+2*Fintype.card α := by
  have hre := RealMatrix.complex_re A hreal
  obtain ⟨R,T,hR,hs,hp,hm,hc⟩ := spectral_price p (A.map Complex.re) (RealMatrix.re_symm A hA)
    (fun i=>A i i) (terms A hA) (by rw [hre]; exact decomposition A hA)
  rw [hre] at hp hm
  exact ⟨R,T,hR,hs,hp,hm,by simpa using hc⟩

theorem exists_reflection_nnz_oai (p : MatrixPrice) (A : Matrix α α ℂ) (hA : A.IsSymm)
    (hreal : ∀ i j,star (A i j)=A i j) :
    ∃ R T : Matrix α α ℂ,R*R=1 ∧ R.IsSymm ∧ A*(1+R)=0 ∧ 1-R=A*T ∧
      p.value R≤(3:ℝ)/4*nnz A+2*Fintype.card α := by
  obtain ⟨R,T,hR,hs,hp,hm,hc⟩ := exists_reflection p A hA hreal
  refine ⟨R,T,hR,hs,hp,hm,?_⟩
  have hh : (2:ℝ)*(pairs A).card≤nnz A := by exact_mod_cast twice_pairs_le A hA
  linarith

end ExactFourier.SparseReflection

end
end

end OAI
end

theorem solution : type_of% @OAI.ExactFourier.SparseReflection.exists_reflection_nnz_oai := @OAI.ExactFourier.SparseReflection.exists_reflection_nnz_oai
