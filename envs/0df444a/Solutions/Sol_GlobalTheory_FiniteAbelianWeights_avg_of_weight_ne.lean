-- Prove2me | solution 1 for GlobalTheory.FiniteAbelianWeights.avg_of_weight_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:32.844841+00:00
-- url     : https://prove2.me/submissions/0ffa3d45-180e-4c3a-8bf8-47736f61930c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CharSumInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteAbelianWeightDecomposition
import Theorems.Thm_GlobalTheory_FiniteAbelianWeights_avg_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open TensorProduct
open GlobalTheory
open GlobalTheory.FiniteAbelianWeights
variable {o : Type} [CommRing o] {T : Type} [CommGroup T]
  {M : Type} [AddCommGroup M] [Module o M]
variable [Fintype T] (ρ : Representation o T M) (u : o)
namespace GlobalTheory.FiniteAbelianWeights
theorem _root_.solution [IsDomain o] (c d : T →* oˣ) (hcd : d ≠ c) (x : M)
    (hx : ∀ t, ρ t x = (d t : o) • x) : avg ρ u c x = 0 := by
  simp only [avg_apply, hx, smul_smul]
  rw [← Finset.sum_smul]
  have h := sum_hom_units_eq_zero ((Units.coeHom o).comp (c⁻¹ * d)) (by
    intro h
    apply hcd
    ext t
    have := DFunLike.congr_fun h t
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.coeHom_apply,
      MonoidHom.one_apply, Units.val_eq_one, inv_mul_eq_one] at this
    rw [this])
  simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.coeHom_apply,
    Units.val_mul] at h
  rw [h, zero_smul, smul_zero]
end GlobalTheory.FiniteAbelianWeights
