-- Prove2me | solution 1 for OAI.Kervaire.perm_euler_inequality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T21:28:39.450724+00:00
-- url     : https://prove2.me/submissions/2b063fc4-4b8a-4931-a58d-973046c01463

import Mathlib
import Definitions.Def_OAIQWKERK000

section
-- module Solutions.OAIQW_Kervaire.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
end

section
-- module Solutions.OAIQW_Kervaire.PermutationCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma sameCycle_map_eq {B : Type*} (σ : Equiv.Perm D) (f : D → B)
    (hf : ∀ d, f (σ d) = f d) {x y : D} (h : σ.SameCycle x y) : f x = f y := by
  obtain ⟨n,_,_,rfl⟩ := h.exists_pow_eq σ
  suffices ∀ n : ℕ, f ((σ^n) x) = f x from (this n).symm
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',mul_apply,hf] using ih

omit [Fintype D] in
lemma formPerm_cut (x y : D) (l m : List D) (h : (x :: (l ++ y :: m)).Nodup) :
    swap x y * (x :: (l ++ y :: m)).formPerm = (x :: l).formPerm * (y :: m).formPerm := by
  induction l generalizing x with
  | nil => simp [List.formPerm_cons_cons]
  | cons a l ih =>
    have hyx : y ≠ x := fun he ↦ h.notMem (by simp [he])
    have hya : y ≠ a := fun he ↦ h.of_cons.notMem (by simp [he])
    have hc : swap x y * swap x a = swap x a * swap a y := by
      rw [swap_mul_eq_mul_swap]
      simp only [swap_inv,swap_apply_left,swap_apply_of_ne_of_ne hyx hya]
    change swap x y * (swap x a * (a :: (l ++ y :: m)).formPerm) =
      (swap x a * (a :: l).formPerm) * (y :: m).formPerm
    rw [← mul_assoc,hc,mul_assoc,ih a h.of_cons,mul_assoc]

omit [Fintype D] [DecidableEq D] in
lemma mem_formPerm_of_fixed (l : List D) (σ : Equiv.Perm D)
    (h : ∀ x ∈ l, σ x = x) (x : D) : σ x ∈ l ↔ x ∈ l := by
  constructor
  · intro hx
    have he := h (σ x) hx
    have hh : σ x = x := σ.injective he
    rwa [hh] at hx
  · intro hx
    rwa [h x hx]

lemma sameCycle_swap_separates (σ : Equiv.Perm D) {x y : D}
    (hne : x ≠ y) (hxy : σ.SameCycle x y) :
    ¬ (swap x y * σ).SameCycle x y := by
  have hx : σ x ≠ x := fun hx ↦ hne (hxy.eq_of_left hx)
  have hs : x ∈ σ.support := Equiv.Perm.mem_support.mpr hx
  have hl : σ.toList x ≠ [] := fun he ↦ (Equiv.Perm.toList_eq_nil_iff.mp he) hs
  obtain ⟨a,t,ht⟩ := List.exists_cons_of_ne_nil hl
  have ha : a = x := by
    have hh := σ.toList_getElem_zero x hs
    simpa only [ht,List.getElem_cons_zero] using hh
  subst a
  have hy : y ∈ t := by
    have hh : y ∈ σ.toList x := Equiv.Perm.mem_toList_iff.mpr ⟨hxy,hs⟩
    simpa only [ht,List.mem_cons,or_iff_right (Ne.symm hne)] using hh
  obtain ⟨l,m,hm⟩ := List.mem_iff_append.mp hy
  subst t
  have hd : (x :: (l ++ y :: m)).Nodup := ht ▸ σ.nodup_toList x
  have hcut := formPerm_cut x y l m hd
  have hL : (x::l).Disjoint (y::m) := by
    intro a ha hb
    exact (List.nodup_append.mp (show ((x::l)++(y::m)).Nodup from hd)).2.2 a ha a hb rfl
  let f : D → Prop := fun d ↦ d ∈ x::l
  have hmem (d : D) : (x::l).formPerm ((y::m).formPerm d) ∈ x::l ↔ d ∈ x::l := by
    rw [List.formPerm_mem_iff_mem]
    exact mem_formPerm_of_fixed (x::l) (y::m).formPerm
      (fun z hz ↦ List.formPerm_apply_of_notMem (fun hzz ↦ hL hz hzz)) d
  have hi (d : D) : f ((swap x y * σ) d) = f d := by
    apply propext
    change (swap x y * σ) d ∈ x::l ↔ d ∈ x::l
    by_cases hc : d ∈ σ.toList x
    · have he : σ d = (x :: (l ++ y :: m)).formPerm d := by
        rw [← ht,σ.formPerm_toList]
        exact (SameCycle.cycleOf_apply (Equiv.Perm.mem_toList_iff.mp hc).1).symm
      change swap x y (σ d) ∈ x::l ↔ _
      rw [he,← Equiv.Perm.mul_apply,hcut]
      exact hmem d
    · have hx' : σ d ≠ x := by
        intro he
        apply hc
        rw [Equiv.Perm.mem_toList_iff]
        exact ⟨(sameCycle_apply_right.mp (he ▸ SameCycle.rfl)),hs⟩
      have hy' : σ d ≠ y := by
        intro he
        apply hc
        rw [Equiv.Perm.mem_toList_iff]
        exact ⟨sameCycle_apply_right.mp (he ▸ hxy),hs⟩
      rw [mul_apply,swap_apply_of_ne_of_ne hx' hy']
      have hdn : d ∉ x::l := fun hd' ↦ hc (ht ▸ (List.mem_append_left (y::m) hd'))
      have hσn : σ d ∉ x::l := by
        intro hh
        apply hc
        rw [Equiv.Perm.mem_toList_iff]
        have hm' : σ d ∈ σ.toList x := ht ▸ (List.mem_append_left (y::m) hh)
        exact ⟨sameCycle_apply_right.mp (Equiv.Perm.mem_toList_iff.mp hm').1,hs⟩
      simp only [hdn,hσn]
  intro hn
  have he := sameCycle_map_eq (swap x y * σ) f hi hn
  have hfx : f x := by simp [f]
  have hfy : ¬ f y := fun hy ↦ hL hy (by simp)
  exact hfy (he ▸ hfx)
end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma sameCycle_swap_merges (σ : Equiv.Perm D) {x y : D}
    (hxy : ¬ σ.SameCycle x y) : (swap x y * σ).SameCycle x y := by
  have hne : x ≠ y := fun he ↦ hxy (he ▸ SameCycle.rfl)
  have hex : ∃ n : ℕ, 0 < n ∧ (σ^n) x = x :=
    ⟨orderOf σ,orderOf_pos σ,by rw [pow_orderOf_eq_one]; rfl⟩
  let n := Nat.find hex
  have hn : 0 < n ∧ (σ^n) x = x := Nat.find_spec hex
  have hmin (i : ℕ) (hi : i < n) (hi0 : 0 < i) : (σ^i) x ≠ x := by
    intro he
    exact Nat.find_min hex hi ⟨hi0,he⟩
  have hyp (i : ℕ) : (σ^i) x ≠ y := fun he ↦ hxy ⟨i,by simpa using he⟩
  have hp (i : ℕ) (hi : i < n) : ((swap x y * σ)^i) x = (σ^i) x := by
    induction i with
    | zero => rfl
    | succ i ih =>
      rw [pow_succ',mul_apply,ih (by omega)]
      change swap x y (σ ((σ^i) x)) = _
      have he : σ ((σ^i) x) = (σ^(i+1)) x := by rw [pow_succ',mul_apply]
      rw [he,swap_apply_of_ne_of_ne (hmin (i+1) hi (by omega)) (hyp (i+1))]
  have hlast : ((swap x y * σ)^n) x = y := by
    obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero hn.1.ne'
    rw [hm,pow_succ',mul_apply,hp m (by omega)]
    change swap x y (σ ((σ^m) x)) = y
    have he : σ ((σ^m) x) = x := by simpa only [hm,pow_succ',mul_apply] using hn.2
    rw [he,swap_apply_left]
  exact ⟨n,by simpa using hlast⟩

omit [Fintype D] in
lemma map_swap_eq {B : Type*} (f : D → B) {x y : D} (hxy : f x = f y) (d : D) :
    f (swap x y d) = f d := by
  by_cases hx : d = x
  · subst d; simpa using hxy.symm
  by_cases hy : d = y
  · subst d; simpa using hxy
  rw [swap_apply_of_ne_of_ne hx hy]

lemma sameCycle_transfer (σ : Equiv.Perm D) {x y : D}
    (hxy : (swap x y * σ).SameCycle x y) {d e : D} (hde : σ.SameCycle d e) :
    (swap x y * σ).SameCycle d e := by
  let τ := swap x y * σ
  let f : D → Cycles τ := Quotient.mk _
  have hfτ (a : D) : f (τ a) = f a := Quotient.sound (SameCycle.rfl.apply_left)
  have hfxy : f x = f y := Quotient.sound hxy
  apply Quotient.exact (s := SameCycle.setoid τ)
  exact sameCycle_map_eq σ f (fun a ↦ by
    have he : σ a = swap x y (τ a) := by simp [τ]
    rw [he,map_swap_eq f hfxy,hfτ]) hde

omit [DecidableEq D] in
lemma numCycles_eq_card {B : Type*} [Fintype B] (σ : Equiv.Perm D) (f : D → B)
    (hfs : Function.Surjective f) (hf : ∀ x y, σ.SameCycle x y ↔ f x = f y) :
    numCycles σ = Fintype.card B := by
  let E : Cycles σ ≃ B := Equiv.ofBijective
    (Quotient.lift f (fun x y h ↦ (hf x y).mp h)) (by
      constructor
      · intro x y
        induction x using Quotient.inductionOn with | h x =>
          induction y using Quotient.inductionOn with | h y =>
            exact fun he ↦ Quotient.sound ((hf x y).mpr he)
      · intro b
        obtain ⟨d,rfl⟩ := hfs b
        exact ⟨Quotient.mk _ d,rfl⟩)
  exact Fintype.card_congr E

lemma numCycles_swap_merge (σ : Equiv.Perm D) {x y : D}
    (hxy : ¬ σ.SameCycle x y) : numCycles (swap x y * σ) + 1 = numCycles σ := by
  let τ := swap x y * σ
  let C := Cycles σ
  let q : D → C := Quotient.mk _
  have hq : q x ≠ q y := fun he ↦ hxy (Quotient.exact he)
  let B := {z : C // z ≠ q y}
  let f : D → B := fun d ↦ if hd : q d = q y then ⟨q x,hq⟩ else ⟨q d,hd⟩
  have hfval (d : D) : (f d).val = if q d = q y then q x else q d := by
    dsimp [f]
    split <;> simp_all
  have hfq (d e : D) (he : q d = q e) : f d = f e := by
    apply Subtype.ext
    simp only [hfval,he]
  have hfσ (d : D) : f (σ d) = f d := hfq _ _ (Quotient.sound SameCycle.rfl.apply_left)
  have hfxy : f x = f y := by
    apply Subtype.ext
    simp [hfval,hq]
  have hfs : Function.Surjective f := by
    intro ⟨z,hz⟩
    refine ⟨z.out,?_⟩
    apply Subtype.ext
    simp only [hfval]
    have he : q z.out = z := z.out_eq
    rw [he,ite_eq_right hz]
  have hτ : τ.SameCycle x y := sameCycle_swap_merges σ hxy
  have hf (d e : D) : τ.SameCycle d e ↔ f d = f e := by
    constructor
    · exact sameCycle_map_eq τ f (fun a ↦ by
        change f (swap x y (σ a)) = f a
        rw [map_swap_eq f hfxy,hfσ])
    · intro he
      have hv := congrArg Subtype.val he
      simp only [hfval] at hv
      by_cases hd : q d = q y <;> by_cases he : q e = q y
      · exact sameCycle_transfer σ hτ (Quotient.exact (hd.trans he.symm))
      · simp only [ite_eq_left hd,ite_eq_right he] at hv
        exact (sameCycle_transfer σ hτ (Quotient.exact hd)).trans
          (hτ.symm.trans (sameCycle_transfer σ hτ (Quotient.exact hv)))
      · simp only [ite_eq_right hd,ite_eq_left he] at hv
        exact (sameCycle_transfer σ hτ (Quotient.exact hv)).trans
          (hτ.trans (sameCycle_transfer σ hτ (Quotient.exact he.symm)))
      · simp only [ite_eq_right hd,ite_eq_right he] at hv
        exact sameCycle_transfer σ hτ (Quotient.exact hv)
  rw [numCycles_eq_card τ f hfs hf]
  change Fintype.card {z : C // z ≠ q y} + 1 = Fintype.card C
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hc : 0 < Fintype.card C := Fintype.card_pos_iff.mpr ⟨q x⟩
  omega

lemma numCycles_swap_split (σ : Equiv.Perm D) {x y : D} (hne : x ≠ y)
    (hxy : σ.SameCycle x y) : numCycles (swap x y * σ) = numCycles σ + 1 := by
  have h := numCycles_swap_merge (swap x y * σ) (sameCycle_swap_separates σ hne hxy)
  simpa only [← mul_assoc,swap_mul_self,one_mul] using h.symm
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_Kervaire.Components
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KervaireRibbon

section
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

lemma cycle_le_of_step (σ : Equiv.Perm D) (r : Setoid D) (h : ∀ d, r (σ d) d) :
    SameCycle.setoid σ ≤ r := by
  intro x y hxy
  apply Quotient.exact (s := r)
  exact sameCycle_map_eq σ (Quotient.mk r) (fun d ↦ Quotient.sound (h d)) hxy

lemma cycle_swap_le (r : Setoid D) (x y : D) (hxy : r x y) :
    SameCycle.setoid (swap x y) ≤ r := by
  apply cycle_le_of_step
  intro d
  by_cases hx : d = x
  · subst d; simpa using r.symm' hxy
  by_cases hy : d = y
  · subst d; simpa using hxy
  rw [swap_apply_of_ne_of_ne hx hy]

lemma joinPair_eq (r : Setoid D) {x y : D} (h : r x y) : joinPair r x y = r :=
  sup_eq_left.mpr (cycle_swap_le r x y h)
omit [Fintype D] in
lemma le_joinPair (r : Setoid D) (x y : D) : r ≤ joinPair r x y := le_sup_left
omit [Fintype D] in
lemma joinPair_rel (r : Setoid D) (x y : D) : joinPair r x y x y := by
  apply (le_sup_right : SameCycle.setoid (swap x y) ≤ joinPair r x y)
  have h : (swap x y).SameCycle x (swap x y x) := SameCycle.rfl.apply_right
  change (swap x y).SameCycle x y
  simpa only [swap_apply_left] using h

lemma classes_joinPair (r : Setoid D) {x y : D} (hxy : ¬ r x y) :
    classes (joinPair r x y) + 1 = classes r := by
  let q : D → Quotient r := Quotient.mk r
  have hq : q x ≠ q y := fun he ↦ hxy (Quotient.exact he)
  let B := {z : Quotient r // z ≠ q y}
  let f : D → B := fun d ↦ if hd : q d = q y then ⟨q x,hq⟩ else ⟨q d,hd⟩
  have hfval (d : D) : (f d).val = if q d = q y then q x else q d := by
    dsimp [f]; split <;> simp_all
  have hfr : r ≤ Setoid.ker f := by
    intro d e h
    apply Subtype.ext
    simp only [hfval,show q d = q e from Quotient.sound h]
  have hfxy : f x = f y := by apply Subtype.ext; simp [hfval,hq]
  have hle : joinPair r x y ≤ Setoid.ker f :=
    sup_le hfr (cycle_swap_le _ x y hfxy)
  have hge : Setoid.ker f ≤ joinPair r x y := by
    intro d e he
    have hv := congrArg Subtype.val he
    simp only [hfval] at hv
    have hr (d e : D) (h : q d = q e) : joinPair r x y d e :=
      le_joinPair r x y (Quotient.exact h)
    have hh := joinPair_rel r x y
    by_cases hd : q d = q y <;> by_cases he : q e = q y
    · exact hr _ _ (hd.trans he.symm)
    · simp only [ite_eq_left hd,ite_eq_right he] at hv
      exact (joinPair r x y).trans' (hr _ _ hd)
        ((joinPair r x y).trans' ((joinPair r x y).symm' hh) (hr _ _ hv))
    · simp only [ite_eq_right hd,ite_eq_left he] at hv
      exact (joinPair r x y).trans' (hr _ _ hv)
        ((joinPair r x y).trans' hh (hr _ _ he.symm))
    · simp only [ite_eq_right hd,ite_eq_right he] at hv
      exact hr _ _ hv
  have hfs : Function.Surjective f := by
    intro ⟨z,hz⟩
    refine ⟨z.out,?_⟩
    apply Subtype.ext
    simp only [hfval]
    have he : q z.out = z := z.out_eq
    rw [he,ite_eq_right hz]
  have hc : classes (joinPair r x y) = Fintype.card B := by
    rw [le_antisymm hle hge]
    exact Fintype.card_congr (Setoid.quotientKerEquivOfSurjective f hfs)
  rw [hc]
  change Fintype.card {z : Quotient r // z ≠ q y} + 1 = Fintype.card (Quotient r)
  rw [Fintype.card_subtype_compl]
  simp only [Fintype.card_unique]
  have hc : 0 < Fintype.card (Quotient r) := Fintype.card_pos_iff.mpr ⟨q x⟩
  omega

lemma cycles_swap_le (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r)
    (x y : D) : SameCycle.setoid (swap x y * σ) ≤ joinPair r x y := by
  apply cycle_le_of_step
  intro d
  exact (joinPair r x y).trans'
    ((le_sup_right : SameCycle.setoid (swap x y) ≤ joinPair r x y)
      (SameCycle.rfl.apply_left : (swap x y).SameCycle (swap x y (σ d)) (σ d)))
    (le_joinPair r x y (h SameCycle.rfl.apply_left))

lemma numCycles_swap_le (σ : Equiv.Perm D) (x y : D) :
    numCycles (swap x y * σ) ≤ numCycles σ + 1 := by
  by_cases he : x = y
  · subst y
    rw [swap_self]
    change numCycles σ ≤ numCycles σ + 1
    omega
  by_cases hc : σ.SameCycle x y
  · rw [numCycles_swap_split σ he hc]
  · have h := numCycles_swap_merge σ hc
    omega

lemma euler_edges (σ : Equiv.Perm D) (r : Setoid D) (h : SameCycle.setoid σ ≤ r)
    (l : List (D × D)) :
    numCycles (edgePerm σ l) + 2*classes r ≤
      numCycles σ + l.length + 2*classes (attachEdges r l) := by
  induction l generalizing σ r with
  | nil => simp [attachEdges,edgePerm]
  | cons p l ih =>
    have hh := ih (swap p.1 p.2 * σ) (joinPair r p.1 p.2) (cycles_swap_le σ r h _ _)
    change numCycles (edgePerm (swap p.1 p.2 * σ) l) + 2*classes r ≤
      numCycles σ + (l.length+1) + 2*classes (attachEdges (joinPair r p.1 p.2) l)
    by_cases hp : r p.1 p.2
    · rw [joinPair_eq r hp] at hh ⊢
      have hn := numCycles_swap_le σ p.1 p.2
      omega
    · have hc := classes_joinPair r hp
      have hn := numCycles_swap_merge σ (fun he ↦ hp (h he))
      omega

end
open Equiv Equiv.Perm
open scoped Classical
variable {D : Type*} [Fintype D] [DecidableEq D]

omit [DecidableEq D] in
lemma numCycles_one : numCycles (1 : Equiv.Perm D) = Fintype.card D := by
  exact numCycles_eq_card 1 id Function.surjective_id (fun _ _ ↦ sameCycle_one)

omit [DecidableEq D] in
lemma numCycles_conj (σ e : Equiv.Perm D) : numCycles (e*σ*e⁻¹) = numCycles σ := by
  apply numCycles_eq_card (e*σ*e⁻¹) (fun d ↦ (Quotient.mk _ (e⁻¹ d) : Cycles σ))
  · intro z
    exact ⟨e z.out,by simp⟩
  · intro x y
    rw [sameCycle_conj]
    exact @Quotient.eq D (SameCycle.setoid σ) _ _ |>.symm

omit [DecidableEq D] in
lemma numCycles_mul_comm (σ θ : Equiv.Perm D) : numCycles (σ*θ) = numCycles (θ*σ) := by
  have h := numCycles_conj (θ*σ) σ
  simpa only [mul_assoc,mul_inv_cancel,mul_one] using h

lemma cycles_swap_sup (σ : Equiv.Perm D) (x y : D) :
    SameCycle.setoid (swap x y * σ) ⊔ SameCycle.setoid (swap x y) =
      SameCycle.setoid σ ⊔ SameCycle.setoid (swap x y) := by
  apply le_antisymm
  · exact sup_le (cycles_swap_le σ _ le_rfl x y) le_sup_right
  · apply sup_le _ le_sup_right
    have h := cycles_swap_le (swap x y * σ) (SameCycle.setoid (swap x y * σ)) le_rfl x y
    simpa only [← mul_assoc,swap_mul_self,one_mul,joinPair] using h

omit [Fintype D] in
lemma edgePerm_append (σ : Equiv.Perm D) (l m : List (D × D)) :
    edgePerm σ (l++m) = edgePerm (edgePerm σ l) m := by simp [edgePerm,List.foldl_append]
omit [Fintype D] in
lemma attachEdges_append (r : Setoid D) (l m : List (D × D)) :
    attachEdges r (l++m) = attachEdges (attachEdges r l) m := by simp [attachEdges,List.foldl_append]

omit [Fintype D] in
lemma edgePerm_mul (σ τ : Equiv.Perm D) (l : List (D × D)) :
    edgePerm (σ*τ) l = edgePerm σ l * τ := by
  induction l generalizing σ with
  | nil => rfl
  | cons p l ih =>
    change edgePerm (swap p.1 p.2 * (σ*τ)) l = edgePerm (swap p.1 p.2 * σ) l * τ
    rw [← mul_assoc,ih]

lemma exists_minimal_edges (θ : Equiv.Perm D) :
    ∃ l : List (D × D), edgePerm 1 l = θ ∧ l.length + numCycles θ = Fintype.card D ∧
      ∀ r : Setoid D, attachEdges r l = r ⊔ SameCycle.setoid θ := by
  generalize hn : θ.support.card = n
  induction n using Nat.strong_induction_on generalizing θ with
  | h n ih =>
    by_cases hθ : θ = 1
    · subst θ
      refine ⟨[],rfl,by simpa only [List.length_nil,zero_add] using numCycles_one,?_⟩
      intro r
      have he : SameCycle.setoid (1 : Equiv.Perm D) = ⊥ := by ext x y; exact sameCycle_one
      simp [attachEdges,he]
    · obtain ⟨x,hx⟩ : ∃ x, θ x ≠ x := by
        by_contra! h
        apply hθ
        ext x
        exact h x
      let τ := swap x (θ x) * θ
      have hτ : τ.support.card < n := hn ▸ card_support_swap_mul hx
      obtain ⟨l,hl,hcard,hjoin⟩ := ih τ.support.card hτ τ rfl
      refine ⟨l++[(x,θ x)],?_,?_,?_⟩
      · rw [edgePerm_append,hl]
        simp [edgePerm,τ,← mul_assoc]
      · have hc := numCycles_swap_split θ (Ne.symm hx) (SameCycle.rfl.apply_right)
        change numCycles τ = numCycles θ + 1 at hc
        simp only [List.length_append,List.length_singleton]
        omega
      · intro r
        rw [attachEdges_append,hjoin]
        change joinPair (r ⊔ SameCycle.setoid τ) x (θ x) = _
        rw [joinPair,sup_assoc,show SameCycle.setoid τ ⊔ SameCycle.setoid (swap x (θ x)) =
          SameCycle.setoid θ ⊔ SameCycle.setoid (swap x (θ x)) from cycles_swap_sup θ _ _]
        have hs : SameCycle.setoid (swap x (θ x)) ≤ SameCycle.setoid θ :=
          cycle_swap_le _ _ _ SameCycle.rfl.apply_right
        rw [sup_eq_left.mpr hs]

/-- The finite combinatorial Euler inequality, including all fixed points and
all components. No surface classification or topological assertion is assumed. -/
lemma euler_inequality_proof (σ θ : Equiv.Perm D) :
    numCycles σ + numCycles θ + numCycles (σ*θ) ≤
      Fintype.card D + 2*classes (SameCycle.setoid σ ⊔ SameCycle.setoid θ) := by
  obtain ⟨l,hl,hcard,hjoin⟩ := exists_minimal_edges θ
  have he : edgePerm σ l = θ*σ := by
    have hh := edgePerm_mul 1 σ l
    simpa only [one_mul,hl] using hh
  have h := euler_edges σ (SameCycle.setoid σ) le_rfl l
  rw [he,hjoin,← numCycles_mul_comm σ θ] at h
  change numCycles (σ*θ) + 2*numCycles σ ≤
    numCycles σ + l.length + 2*classes (SameCycle.setoid σ ⊔ SameCycle.setoid θ) at h
  omega
end KervaireRibbon

end

end OAI
end

section
-- module Solutions.OAIQW_Kervaire.EulerStd
set_option linter.all false

namespace OAI

namespace Kervaire

theorem perm_euler_inequality_oai {α : Type*} [Finite α] (σ θ : Equiv.Perm α) :
    Nat.card (Quotient (Equiv.Perm.SameCycle.setoid σ)) +
        Nat.card (Quotient (Equiv.Perm.SameCycle.setoid θ)) +
        Nat.card (Quotient (Equiv.Perm.SameCycle.setoid (σ * θ))) ≤
      Nat.card α + 2 * Nat.card (Quotient
        (Equiv.Perm.SameCycle.setoid σ ⊔ Equiv.Perm.SameCycle.setoid θ)) := by
  classical
  have := Fintype.ofFinite α
  have h := KervaireRibbon.euler_inequality_proof σ θ
  simp only [KervaireRibbon.numCycles, KervaireRibbon.classes, KervaireRibbon.Cycles,
    Fintype.card_eq_nat_card] at h
  exact h

end Kervaire

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kervaire.perm_euler_inequality_oai.{u_1} := @OAI.Kervaire.perm_euler_inequality_oai.{u_1}
