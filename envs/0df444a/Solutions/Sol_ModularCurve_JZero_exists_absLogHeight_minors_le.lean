-- Prove2me | solution 1 for ModularCurve.JZero.exists_absLogHeight_minors_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d2324126-2b6e-53aa-9859-e877106622c1

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Theorems.Thm_Height_inv_finrank_mul_logHeight_inclusion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_absLogHeight_minors_le

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open AlgebraicCurve

noncomputable section

namespace P2MWs37Minors

section AbsHeight

theorem normLogHeight_eq_of_le (E E' : IntermediateField ℚ (AlgebraicClosure ℚ)) (h : E ≤ E')
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ E'] {ι : Type} [Fintype ι]
    (x : ι → AlgebraicClosure ℚ) (hx : ∀ i, x i ∈ E) :
    (Module.finrank ℚ E : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hx i⟩ : E))
      = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h (hx i)⟩ : E')) :=
  (Height.inv_finrank_mul_logHeight_inclusion (K := E) (L := E') h (fun i => (⟨x i, hx i⟩ : E))).symm

theorem absLogHeight_eq_of_mem {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ)
    (E' : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ E'] (h : ∀ i, x i ∈ E') :
    absLogHeight x = (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, h i⟩ : E')) := by
  have hle : IntermediateField.adjoin ℚ (Set.range x) ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  haveI := finiteDimensional_adjoin_range x
  exact normLogHeight_eq_of_le _ E' hle x (fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)

theorem absLogHeight_mul_eq_add {ι κ μ : Type} [Fintype ι] [Fintype κ] [Fintype μ]
    (x : ι → AlgebraicClosure ℚ) (y : κ → AlgebraicClosure ℚ) (hx : x ≠ 0) (hy : y ≠ 0)
    (e : μ ≃ ι × κ) :
    absLogHeight (fun m => x (e m).1 * y (e m).2) = absLogHeight x + absLogHeight y := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range y) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hyE : ∀ j, y j ∈ E' := fun j => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)
  have hpE : ∀ m, x (e m).1 * y (e m).2 ∈ E' := fun m => mul_mem (hxE _) (hyE _)
  rw [absLogHeight_eq_of_mem _ E' hpE, absLogHeight_eq_of_mem x E' hxE, absLogHeight_eq_of_mem y E' hyE,
    ← mul_add]
  congr 1
  have hx' : (fun i => (⟨x i, hxE i⟩ : E')) ≠ 0 := by
    intro h; apply hx; funext i; simpa using congrArg Subtype.val (congrFun h i)
  have hy' : (fun j => (⟨y j, hyE j⟩ : E')) ≠ 0 := by
    intro h; apply hy; funext j; simpa using congrArg Subtype.val (congrFun h j)
  have hfun : (fun m => (⟨x (e m).1 * y (e m).2, hpE m⟩ : E'))
      = (fun q : ι × κ => (⟨x q.1, hxE q.1⟩ : E') * (⟨y q.2, hyE q.2⟩ : E')) ∘ e := by
    funext m
    apply Subtype.ext
    rfl
  rw [hfun, Height.logHeight_comp_equiv e, Height.logHeight_fun_mul_eq hx' hy']

theorem absLogHeight_linear_le {ι κ : Type} [Fintype ι] [Fintype κ] [Nonempty ι]
    (M : κ → ι → AlgebraicClosure ℚ) (x : ι → AlgebraicClosure ℚ) :
    absLogHeight (fun j => ∑ i, M j i * x i)
      ≤ Real.log (Fintype.card ι) + absLogHeight (fun q : κ × ι => M q.1 q.2) + absLogHeight x := by
  set E' : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.adjoin ℚ (Set.range x ∪ Set.range (fun q : κ × ι => M q.1 q.2)) with hE'
  haveI : FiniteDimensional ℚ E' :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
  have hxE : ∀ i, x i ∈ E' := fun i => IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
  have hME : ∀ q : κ × ι, M q.1 q.2 ∈ E' := fun q => IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨q, rfl⟩)
  have hyE : ∀ j, (∑ i, M j i * x i) ∈ E' := fun j => sum_mem fun i _ => mul_mem (hME (j, i)) (hxE i)
  rw [absLogHeight_eq_of_mem _ E' hyE, absLogHeight_eq_of_mem _ E' hME, absLogHeight_eq_of_mem x E' hxE]
  have hd : (0 : ℝ) < Module.finrank ℚ E' := by exact_mod_cast Module.finrank_pos
  have hfun : (fun j => (⟨∑ i, M j i * x i, hyE j⟩ : E'))
      = fun j => ∑ i, (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E') := by
    funext j
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    simp only [MulMemClass.coe_mul]
  have key := Height.logHeight_linearMap_apply_le (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
    (fun i => (⟨x i, hxE i⟩ : E'))
  rw [NumberField.totalWeight_eq_finrank, Nat.card_eq_fintype_card] at key
  rw [hfun]
  have hlog : 0 ≤ Real.log (Fintype.card ι : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Fintype.card_pos)
  calc (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun j => ∑ i,
          (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E')) (j, i) * (⟨x i, hxE i⟩ : E'))
      ≤ (Module.finrank ℚ E' : ℝ)⁻¹ * ((Module.finrank ℚ E' : ℝ) * Real.log (Fintype.card ι)
          + Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + Height.logHeight (fun i => (⟨x i, hxE i⟩ : E'))) :=
        mul_le_mul_of_nonneg_left key (inv_nonneg.mpr hd.le)
    _ = Real.log (Fintype.card ι)
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun q : κ × ι => (⟨M q.1 q.2, hME q⟩ : E'))
          + (Module.finrank ℚ E' : ℝ)⁻¹ * Height.logHeight (fun i => (⟨x i, hxE i⟩ : E')) := by
        field_simp

end AbsHeight

theorem absLogHeight_nonneg' {ι : Type} [Fintype ι] (x : ι → AlgebraicClosure ℚ) : 0 ≤ absLogHeight x := by
  haveI := finiteDimensional_adjoin_range x
  unfold absLogHeight
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

theorem absLogHeight_zero' {ι : Type} [Fintype ι] : absLogHeight (0 : ι → AlgebraicClosure ℚ) = 0 := by
  haveI := finiteDimensional_adjoin_range (0 : ι → AlgebraicClosure ℚ)
  unfold absLogHeight
  have h0 : (fun i : ι => (⟨(0 : ι → AlgebraicClosure ℚ) i,
      IntermediateField.subset_adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)) ⟨i, rfl⟩⟩ :
        IntermediateField.adjoin ℚ (Set.range (0 : ι → AlgebraicClosure ℚ)))) = 0 := by
    funext i
    exact Subtype.ext rfl
  rw [h0, Height.logHeight_zero, mul_zero]

def swapMat (r : ℕ) : (Fin r × Fin r) → (Fin r × Fin r) → AlgebraicClosure ℚ :=
  fun p q => (if q = p then 1 else 0) - (if q = p.swap then 1 else 0)

theorem minors_eq_linear {r : ℕ} (x y : Fin r → AlgebraicClosure ℚ) :
    (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1)
      = fun p => ∑ q, swapMat r p q * (x q.1 * y q.2) := by
  funext p
  simp only [swapMat, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp [Prod.swap]

theorem main (r : ℕ) : ∃ C₀ : ℝ, ∀ x y : Fin r → AlgebraicClosure ℚ,
    absLogHeight (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1)
      ≤ absLogHeight x + absLogHeight y + C₀ := by
  classical
  refine ⟨Real.log (Fintype.card (Fin r × Fin r))
    + absLogHeight (fun q : (Fin r × Fin r) × (Fin r × Fin r) => swapMat r q.1 q.2), fun x y => ?_⟩
  have hC : 0 ≤ Real.log (Fintype.card (Fin r × Fin r))
      + absLogHeight (fun q : (Fin r × Fin r) × (Fin r × Fin r) => swapMat r q.1 q.2) := by
    refine add_nonneg ?_ (absLogHeight_nonneg' _)
    rcases Nat.eq_zero_or_pos (Fintype.card (Fin r × Fin r)) with h | h
    · rw [h]; simp
    · exact Real.log_nonneg (by exact_mod_cast h)
  by_cases hx : x = 0
  · subst hx
    have : (fun p : Fin r × Fin r => (0 : Fin r → AlgebraicClosure ℚ) p.1 * y p.2
        - (0 : Fin r → AlgebraicClosure ℚ) p.2 * y p.1) = 0 := by funext p; simp
    rw [this, absLogHeight_zero', absLogHeight_zero']
    linarith [absLogHeight_nonneg' y]
  by_cases hy : y = 0
  · subst hy
    have : (fun p : Fin r × Fin r => x p.1 * (0 : Fin r → AlgebraicClosure ℚ) p.2
        - x p.2 * (0 : Fin r → AlgebraicClosure ℚ) p.1) = 0 := by funext p; simp
    rw [this, absLogHeight_zero', absLogHeight_zero']
    linarith [absLogHeight_nonneg' x]
  have hr : 0 < r := by
    by_contra h
    push Not at h
    interval_cases r
    exact hx (funext fun i => i.elim0)
  haveI : Nonempty (Fin r × Fin r) := ⟨(⟨0, hr⟩, ⟨0, hr⟩)⟩
  have h1 := absLogHeight_linear_le (swapMat r) (fun q : Fin r × Fin r => x q.1 * y q.2)
  have h2 : absLogHeight (fun q : Fin r × Fin r => x q.1 * y q.2) = absLogHeight x + absLogHeight y := by
    simpa using absLogHeight_mul_eq_add x y hx hy (Equiv.refl _)
  rw [minors_eq_linear, ← h2]
  linarith

end P2MWs37Minors

end

theorem solution (r : ℕ) :
    ∃ C₀ : ℝ, ∀ x y : Fin r → AlgebraicClosure ℚ,
      AlgebraicCurve.absLogHeight (fun p : Fin r × Fin r => x p.1 * y p.2 - x p.2 * y p.1)
        ≤ AlgebraicCurve.absLogHeight x + AlgebraicCurve.absLogHeight y + C₀ :=
  P2MWs37Minors.main r

end S_ModularCurve_JZero_exists_absLogHeight_minors_le
end P2MW
export P2MW.S_ModularCurve_JZero_exists_absLogHeight_minors_le (solution)
