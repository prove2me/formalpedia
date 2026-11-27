-- Prove2me | solution 1 for GlobalTheory.WeightSubst.weight_subst_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:35:31.16216+00:00
-- url     : https://prove2.me/submissions/b6496104-bad4-4156-becc-ed07ba96f1ed

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_WeightedSumBounds_PeriodValuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WeightSubstNonneg
import Theorems.Thm_GlobalTheory_WeightSubst_wtNonneg_prod
import Theorems.Thm_GlobalTheory_WeightSubst_wtNonneg_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PGsh
open GlobalTheory GlobalTheory.WeightSubst
open MvPowerSeries
variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {σ : Type} [Fintype σ]
  [DecidableEq σ] (ρ : σ → ℝ)
namespace GlobalTheory.WeightSubst
theorem _root_.solution :
  (∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (σ τ : Type) [Fintype σ] [DecidableEq σ] [Fintype τ] (ρ : σ → ℝ) (K : MvPowerSeries τ C) (t : τ → MvPowerSeries σ C),
    MvIsInt v K → (∀ c, MvPowerSeries.constantCoeff (t c) = 0) → (∀ c, (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (t c)))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (MvPowerSeries.subst t K)))) := by
  intro C _ v σ τ _ _ _ ρ K t hK ht0 ht α
  have hs : MvPowerSeries.HasSubst t := MvPowerSeries.hasSubst_of_constantCoeff_zero ht0
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite hs K α)]
  apply AddValuation.map_le_sum
  intro d _
  rw [smul_eq_mul, AddValuation.map_mul]
  have h1 : (0 : WithTop ℝ) ≤ v (MvPowerSeries.coeff d K) := hK d
  have h2 : WtNonneg v ρ (d.prod fun c e => t c ^ e) := by
    unfold Finsupp.prod
    exact wtNonneg_prod v ρ _ _ (fun c _ => wtNonneg_pow v ρ (ht c) _)
  have h3 := add_le_add h1 (h2 α)
  rwa [zero_add] at h3
end GlobalTheory.WeightSubst
