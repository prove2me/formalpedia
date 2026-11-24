-- Prove2me | solution 1 for GlobalTheory.AnArc.hermForm_HwMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:43:56.239827+00:00
-- url     : https://prove2.me/submissions/2f4986eb-9ab1-49ef-9458-fbb8cdea6fc3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open GlobalTheory.AnArc
variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)
namespace GlobalTheory.AnArc
theorem _root_.solution (w : ℂ) {g : ℕ} (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (v v' : A.V) :
    hermForm (A.HwMat w h) (h v) (h v') = A.Hw w v v' := by
  have e : ∀ v : A.V, v = ∑ i, h v i • h.symm (Pi.single i 1) := fun v => h.injective <| by
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact pi_eq_sum_univ' _
  conv_rhs => rw [e v, e v']
  simp only [hermForm, HwMat, dotProduct, mulVec, map_sum, map_smul, LinearMap.map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
    RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end GlobalTheory.AnArc
