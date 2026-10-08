-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.lemma23_sublinear_domination
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:52:54.489557+00:00
-- url     : https://prove2.me/submissions/a753dcc7-7776-4ec9-84f9-e7ca7c066811

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

set_option autoImplicit false

namespace L23Aux

open MaxLatticeFree.Inequalities

variable {q : ℕ} {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))}

lemma combo_add (s t : W →₀ ℝ) : combo W (s + t) = combo W s + combo W t := by
  unfold combo
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

lemma combo_single (r : W) (c : ℝ) :
    combo W (Finsupp.single r c) = c • (r : EuclideanSpace ℝ (Fin q)) := by
  unfold combo
  exact Finsupp.sum_single_index (zero_smul _ _)

lemma combo_zero : combo W (0 : W →₀ ℝ) = 0 := by
  unfold combo
  exact Finsupp.sum_zero_index

lemma combo_smul (c : ℝ) (s : W →₀ ℝ) : combo W (c • s) = c • combo W s := by
  unfold combo
  have h := Finsupp.sum_smul_index' (g := s) (b := c)
    (h := fun (r : W) (a : ℝ) => a • (r : EuclideanSpace ℝ (Fin q))) (fun _ => zero_smul _ _)
  rw [h, Finsupp.smul_sum]
  simp only [Finsupp.sum, smul_eq_mul, mul_smul]

lemma linVal_add (ψ : W → ℝ) (s t : W →₀ ℝ) : linVal ψ (s + t) = linVal ψ s + linVal ψ t := by
  unfold linVal
  exact Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _)

lemma linVal_single (ψ : W → ℝ) (r : W) (c : ℝ) : linVal ψ (Finsupp.single r c) = ψ r * c := by
  unfold linVal
  exact Finsupp.sum_single_index (mul_zero _)

lemma linVal_zero (ψ : W → ℝ) : linVal ψ (0 : W →₀ ℝ) = 0 := by
  unfold linVal
  exact Finsupp.sum_zero_index

lemma linVal_smul (ψ : W → ℝ) (c : ℝ) (s : W →₀ ℝ) : linVal ψ (c • s) = c * linVal ψ s := by
  unfold linVal
  rw [Finsupp.sum_smul_index' (fun _ => mul_zero _)]
  simp only [Finsupp.sum, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- nonneg representations of `r` -/
def Reps (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (r : W) : Set (W →₀ ℝ) :=
  {s | (∀ x, 0 ≤ s x) ∧ combo W s = (r : EuclideanSpace ℝ (Fin q))}

noncomputable def hull (ψ : W → ℝ) (r : W) : ℝ := sInf (linVal ψ '' Reps W r)

lemma single_mem (r : W) : Finsupp.single r 1 ∈ Reps W r := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [combo_single, one_smul]

lemma reps_nonempty (ψ : W → ℝ) (r : W) : (linVal ψ '' Reps W r).Nonempty :=
  ⟨_, Set.mem_image_of_mem _ (single_mem r)⟩

section
variable (f : EuclideanSpace ℝ (Fin q)) (ψ : W → ℝ) (α : ℝ)

lemma reps_bdd (hf : (affSpace f W ∩ integralPoints q).Nonempty) (hvalid : IsValid f W ψ α)
    (r : W) : BddBelow (linVal ψ '' Reps W r) := by
  obtain ⟨x0, hx0W, hx0Z⟩ := hf
  have hw0 : x0 - f ∈ W := hx0W
  set w0 : W := ⟨x0 - f, hw0⟩
  refine ⟨α - ψ (-r) - ψ w0, ?_⟩
  rintro _ ⟨s, ⟨hs0, hsc⟩, rfl⟩
  have hmem : s + Finsupp.single (-r) 1 + Finsupp.single w0 1 ∈ Rf f W := by
    refine ⟨?_, fun x => ?_⟩
    · rw [combo_add, combo_add, combo_single, combo_single, hsc]
      have : f + ((r : EuclideanSpace ℝ (Fin q)) + (1:ℝ) • ((-r : W) : EuclideanSpace ℝ (Fin q))
          + (1:ℝ) • (w0 : EuclideanSpace ℝ (Fin q))) = x0 := by
        simp [w0]
      rw [this]; exact hx0Z
    · simp only [Finsupp.add_apply, Finsupp.single_apply]
      have := hs0 x
      split_ifs <;> linarith
  have := hvalid _ hmem
  rw [linVal_add, linVal_add, linVal_single, linVal_single] at this
  linarith

variable (hf : (affSpace f W ∩ integralPoints q).Nonempty) (hvalid : IsValid f W ψ α)
include hf hvalid

lemma hull_le (r : W) (s : W →₀ ℝ) (hs : s ∈ Reps W r) : hull ψ r ≤ linVal ψ s :=
  csInf_le (reps_bdd f ψ α hf hvalid r) (Set.mem_image_of_mem _ hs)

omit hf hvalid in
lemma le_hull (r : W) (a : ℝ) (h : ∀ s ∈ Reps W r, a ≤ linVal ψ s) : a ≤ hull ψ r :=
  le_csInf (reps_nonempty ψ r) (by rintro _ ⟨s, hs, rfl⟩; exact h s hs)

lemma hull_le_self (r : W) : hull ψ r ≤ ψ r := by
  have := hull_le f ψ α hf hvalid r _ (single_mem r)
  rwa [linVal_single, mul_one] at this

lemma hull_zero : hull ψ (0 : W) = 0 := by
  apply le_antisymm
  · have := hull_le f ψ α hf hvalid 0 0 ⟨fun _ => le_rfl, by rw [combo_zero]; rfl⟩
    rwa [linVal_zero] at this
  · apply le_hull
    intro s hs
    by_contra hneg
    push Not at hneg
    obtain ⟨B, hB⟩ := reps_bdd f ψ α hf hvalid 0
    set t : ℝ := (|B| + 1) / (-linVal ψ s)
    have ht : 0 < t := div_pos (by positivity) (by linarith)
    have hmem : t • s ∈ Reps W 0 := by
      refine ⟨fun x => ?_, ?_⟩
      · rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg ht.le (hs.1 x)
      · rw [combo_smul, hs.2]; simp
    have h1 := hB (Set.mem_image_of_mem _ hmem)
    rw [linVal_smul] at h1
    have h2 : t * linVal ψ s = -(|B| + 1) := by
      simp only [t]; rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]; ring
    have := neg_abs_le B
    linarith

lemma hull_smul_le (c : ℝ) (hc : 0 < c) (r : W) : c * hull ψ r ≤ hull ψ (c • r) := by
  apply le_hull
  intro t ht
  have hmem : c⁻¹ • t ∈ Reps W r := by
    refine ⟨fun x => ?_, ?_⟩
    · rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hc.le) (ht.1 x)
    · rw [combo_smul, ht.2, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have := hull_le f ψ α hf hvalid r _ hmem
  rw [linVal_smul] at this
  have h2 := mul_le_mul_of_nonneg_left this hc.le
  rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2

lemma hull_homog : IsPositivelyHomogeneous (hull ψ) := by
  intro r c hc
  rcases hc.lt_or_eq with hc | rfl
  · apply le_antisymm
    · have h := hull_smul_le f ψ α hf hvalid c⁻¹ (inv_pos.2 hc) (c • r)
      rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul] at h
      have h2 := mul_le_mul_of_nonneg_left h hc.le
      rwa [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at h2
    · exact hull_smul_le f ψ α hf hvalid c hc r
  · rw [zero_smul, zero_mul, hull_zero f ψ α hf hvalid]

lemma hull_subadd : IsSubadditive (hull ψ) := by
  intro r₁ r₂
  have key : hull ψ (r₁ + r₂) - hull ψ r₂ ≤ hull ψ r₁ := by
    apply le_hull
    intro s₁ hs₁
    have : hull ψ (r₁ + r₂) - linVal ψ s₁ ≤ hull ψ r₂ := by
      apply le_hull
      intro s₂ hs₂
      have hmem : s₁ + s₂ ∈ Reps W (r₁ + r₂) := by
        refine ⟨fun x => ?_, ?_⟩
        · rw [Finsupp.add_apply]; exact add_nonneg (hs₁.1 x) (hs₂.1 x)
        · rw [combo_add, hs₁.2, hs₂.2, Submodule.coe_add]
      have := hull_le f ψ α hf hvalid _ _ hmem
      rw [linVal_add] at this
      linarith
    linarith
  linarith

lemma hull_jensen (T : Finset W) (c : W → ℝ) (hc : ∀ x, 0 ≤ c x) :
    hull ψ (∑ x ∈ T, c x • x) ≤ ∑ x ∈ T, hull ψ x * c x := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [hull_zero f ψ α hf hvalid]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := hull_subadd f ψ α hf hvalid (c a • a) (∑ x ∈ T, c x • x)
    have h2 := hull_homog f ψ α hf hvalid a (c a) (hc a)
    linarith [mul_comm (c a) (hull ψ a)]

lemma hull_valid : IsValid f W (hull ψ) α := by
  intro s hs
  set w : W := ∑ x ∈ s.support, s x • x
  have hw : (w : EuclideanSpace ℝ (Fin q)) = combo W s := by
    simp only [w, combo, Finsupp.sum, Submodule.coe_sum, Submodule.coe_smul]
  have h1 : α ≤ hull ψ w := by
    apply le_hull
    intro t ht
    apply hvalid
    refine ⟨?_, ht.1⟩
    rw [ht.2, hw]; exact hs.1
  have h2 := hull_jensen f ψ α hf hvalid s.support s hs.2
  have h3 : linVal (hull ψ) s = ∑ x ∈ s.support, hull ψ x * s x := rfl
  linarith

end

end L23Aux

open MaxLatticeFree.Inequalities in
theorem solution {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ) (α : ℝ)
    (hvalid : IsValid f W ψ α) :
    ∃ ψ' : W → ℝ, IsValid f W ψ' α ∧ Dominates ψ' ψ ∧ IsSublinear ψ' := by
  exact ⟨L23Aux.hull ψ, L23Aux.hull_valid f ψ α hf hvalid,
    fun r => L23Aux.hull_le_self f ψ α hf hvalid r,
    L23Aux.hull_homog f ψ α hf hvalid, L23Aux.hull_subadd f ψ α hf hvalid⟩
