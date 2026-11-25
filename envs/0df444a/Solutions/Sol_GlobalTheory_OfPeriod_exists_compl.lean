-- Prove2me | solution 1 for GlobalTheory.OfPeriod.exists_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:31:01.124732+00:00
-- url     : https://prove2.me/submissions/b5cc3da5-1ca5-47a2-accc-ef34b7722de3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEquivOfSumEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_FinrankHomComplex
import Theorems.Thm_GlobalTheory_OfPeriod_reForm_apply
import Theorems.Thm_GlobalTheory_OfPeriod_imPart_eq
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


attribute [local simp] GlobalTheory.OfPeriod.reForm_apply

set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OfPeriod
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open Complex
variable {W : Type} [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
variable {S : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} {R : Submodule ℝ W}
variable (hconj : ∀ z w, starRingEnd ℂ (S z w) = S w z) (hpos : ∀ z, z ≠ 0 → 0 < (S z z).re)
  (hR : ∀ r ∈ R, ∀ r' ∈ R, (S r r').im = 0) {b : W →ₗ[ℝ] W} (hb : ∀ w, b w ∈ R)
  (hb' : ∀ w, ∀ r ∈ R, S (b w) r = (S w r).im)
variable {O : Type} [CommRing O] [StarRing O] {ρ : O →+* Module.End ℂ W}
  (hρ : ∀ a z w, S (ρ a z) w = S z (ρ (star a) w)) (hρR : ∀ a, ∀ r ∈ R, ρ a r ∈ R)
include hpos hb hb' hρ hρR
namespace GlobalTheory.OfPeriod
theorem _root_.solution [FiniteDimensional ℂ W] (Q : ∀ n : ℕ, (O →+* Module.End ℂ (Fin n → ℂ)) → Prop)
    (hQ : ∀ (U : Type) [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] (σ : O →+* Module.End ℂ U),
      ∃ (n : ℕ) (k : U ≃ₗ[ℂ] (Fin n → ℂ)) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧ ∀ a u, k (σ a u) = F a (k u)) :
    ∃ (n : ℕ) (q : W →ₗ[ℂ] (Fin n → ℂ)) (j : (Fin n → ℂ) →ₗ[ℂ] W) (F : O →+* Module.End ℂ (Fin n → ℂ)), Q n F ∧
      (∀ z, q (j z) = z) ∧ (∀ z, ∀ r ∈ R, S (j z) r = 0) ∧ (∀ w, w = b (I • w) + I • b w + j (q w)) ∧
      (∀ w, (∀ r ∈ R, S w r = 0) → j (q w) = w) ∧ ∀ a z, j (F a z) = ρ a (j z) := by
  let U : Submodule ℂ W :=
    { carrier := {u | ∀ r ∈ R, S u r = 0}
      zero_mem' := fun r _ => by simp
      add_mem' := fun {u u'} hu hu' r hr => by simp [hu r hr, hu' r hr]
      smul_mem' := fun c u hu r hr => by simp [hu r hr] }
  have hII : ∀ w : W, I • I • w = -w := fun w => by rw [smul_smul, I_mul_I, neg_smul, one_smul]
  have hsm : ∀ (c : ℂ) (w : W), c • w = c.re • w + c.im • I • w := fun c w => by
    rw [← algebraMap_smul ℂ c.re, ← algebraMap_smul ℂ c.im, smul_smul, ← add_smul]
    congr 1
    exact (re_add_im c).symm
  let p₀ : W →ₗ[ℝ] W := LinearMap.id - b ∘ₗ (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ -
    (I • LinearMap.id : W →ₗ[ℂ] W).restrictScalars ℝ ∘ₗ b
  have hp₀ : ∀ w, p₀ w = w - b (I • w) - I • b w := fun _ => rfl
  have hpI : ∀ w, p₀ (I • w) = I • p₀ w := fun w => by
    simp only [hp₀, hII, smul_sub, map_neg]; abel
  have hpU : ∀ w, p₀ w ∈ U := fun w r hr => by
    simp only [hp₀, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, hb' _ r hr, smul_eq_mul]
    apply Complex.ext <;> simp
  let p : W →ₗ[ℂ] U :=
    { toFun := fun w => ⟨p₀ w, hpU w⟩
      map_add' := fun w w' => Subtype.ext (map_add p₀ w w')
      map_smul' := fun c w => Subtype.ext (by
        show p₀ (c • w) = c • p₀ w
        rw [hsm c w, hsm c (p₀ w), map_add, map_smul, map_smul, hpI]) }
  have hb0 : ∀ u ∈ U, b u = 0 := fun u hu => imPart_eq hpos hb hb' R.zero_mem fun r hr => by simp [hu r hr]
  have hpu : ∀ u : U, p u = u := fun u => Subtype.ext (by
    show p₀ u = u
    rw [hp₀, hb0 _ u.2, hb0 _ (U.smul_mem _ u.2), smul_zero, sub_zero, sub_zero])
  have hρU : ∀ a, ∀ u ∈ U, ρ a u ∈ U := fun a u hu r hr => by rw [hρ]; exact hu _ (hρR _ _ hr)
  let σ : O →+* Module.End ℂ U :=
    { toFun := fun a => (ρ a).restrict (hρU a)
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  obtain ⟨n, k, F, hF, hk⟩ := hQ U σ
  refine ⟨n, k.toLinearMap ∘ₗ p, U.subtype ∘ₗ k.symm.toLinearMap, F, hF, fun z => ?_, fun z => (k.symm z).2,
    fun w => ?_, fun w hw => ?_, fun a z => ?_⟩
  · simp [hpu]
  · have : (U.subtype ∘ₗ k.symm.toLinearMap) ((k.toLinearMap ∘ₗ p) w) = p₀ w := by simp [p]
    rw [this, hp₀]; abel
  · have := hpu ⟨w, hw⟩
    simp only at this
    simp [this]
  · obtain ⟨u, rfl⟩ := k.surjective z
    rw [← hk]
    simp [σ]
end GlobalTheory.OfPeriod
