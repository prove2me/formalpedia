-- Prove2me | solution 1 for GlobalTheory.AdaptedDet.det_eq_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:09:31.346607+00:00
-- url     : https://prove2.me/submissions/dc440ff0-62a1-432e-95d3-7021569e326e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CmUnitPowFourIdempotentModEight
import Theorems.Thm_GlobalTheory_AdaptedDet_isLocalizedModule_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AdaptedDet
variable {E : Type} [Field E] [NumberField E] {L : Type} [AddCommGroup L] [Module (𝓞 E) L] {r : ℕ}
namespace GlobalTheory.AdaptedDet
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ L)
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (hf : Function.Injective φ)
    (hspan : Submodule.span E (Set.range φ) = ⊤) (T : L →ₗ[ℤ] L) (A : Matrix (Fin r) (Fin r) E)
    (hA : ∀ x, A *ᵥ φ x = φ (T x)) :
    (((LinearMap.toMatrix b b T).det : ℤ) : ℚ) = Algebra.norm ℚ A.det := by
  haveI := isLocalizedModule_int φ hf hspan
  let b' := b.ofIsLocalizedModule ℚ ℤ⁰ (φ.restrictScalars ℤ)
  rw [← LinearMap.det_toLin' A, ← LinearMap.det_restrictScalars, ← LinearMap.det_toMatrix b',
    ← eq_intCast (algebraMap ℤ ℚ), RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, b',
    Module.Basis.ofIsLocalizedModule_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
    hA]
  exact (b.ofIsLocalizedModule_repr_apply ℚ ℤ⁰ (φ.restrictScalars ℤ) _ i).symm
end GlobalTheory.AdaptedDet
