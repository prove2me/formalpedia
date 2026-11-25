-- Prove2me | solution 1 for GlobalTheory.T.exists_holomorphicUniformisation_powerThetaKeyDatum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:54:01.627908+00:00
-- url     : https://prove2.me/submissions/76b3fb4e-fd09-4335-89fa-4750949be562

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_KeyRuleOneOfKeyFormula
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsHolomorphicUniformisationPowerThetaKeyDatuStatement
import Theorems.Thm_GlobalTheory_PowUnif_exists_holUnif_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (x y : KeyIn ℂ) (j : ℕ) (u : HolUnif x.P.A x.P.L x.P.g) (θ : (Fin x.P.g → ℂ) → ℂ) (W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ), GlobalTheory.KeyPow.IsKeyPow y x j → u.IsRig x.rig → u.IsFn x.th θ → (∀ i, u.IsDiff (W i) (x.v i)) → ∃ (e : Fin j × Fin x.P.g ≃ Fin y.P.g) (u' : HolUnif y.P.A y.P.L y.P.g), (∀ z, z ∈ u'.Λ ↔ ∀ i, (fun k => z (e (i, k))) ∈ u.Λ) ∧ u'.IsRig y.rig ∧ u'.IsFn y.th (fun z => ∏ i, θ (fun k => z (e (i, k)))) ∧ ∀ p, u'.IsDiff (fun q => if (e.symm p).1 = (e.symm q).1 then W (e.symm p).2 (e.symm q).2 else 0) (y.v p) := by
  first | exact @GlobalTheory.PowUnif.exists_holUnif_pow | exact GlobalTheory.PowUnif.exists_holUnif_pow | (intros; apply GlobalTheory.PowUnif.exists_holUnif_pow <;> assumption)
end _root_.GlobalTheory.T
