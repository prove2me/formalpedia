-- Prove2me | solution 1 for GlobalTheory.JacSer.snd_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:30:57.187817+00:00
-- url     : https://prove2.me/submissions/3cbc6733-2a3d-4b8a-846c-90b7dd49559f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_IsSquareDeterminantComparison
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_OneEqSpTranslZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsLieBasisIffIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MemNonzeroLocusVia
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_JacEqUnitMulDetPderiv
import Theorems.Thm_GlobalTheory_JacSer_isLocalRing_trivSqZeroExt
import Theorems.Thm_GlobalTheory_JacSer_dirPt_fst
import Theorems.Thm_GlobalTheory_JacSer_dirPt_snd
import Theorems.Thm_GlobalTheory_JacSer_dirPt_snd_X
import Theorems.Thm_GlobalTheory_FormalIsogeny_isAdicComplete_maximalIdeal_of_finite
import Theorems.Thm_GlobalTheory_SqZero_IsAway_ext
import Theorems.Thm_GlobalTheory_mvPowerSeries_algHom_ext_of_isHausdorff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.JacSer
open IsLocalRing MvPowerSeries GlobalTheory.SqZero
variable {O : Type} [CommRing O] [IsLocalRing O]
variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
namespace GlobalTheory.JacSer
theorem _root_.solution {n : ℕ} (e : MvPowerSeries (Fin n) O →ₐ[O] O) (he : ∀ i, e (X i) ∈ maximalIdeal O)
    (ψ : MvPowerSeries (Fin n) O →ₐ[O] DualNumber O) (hψ : ∀ a, (ψ a).fst = e a) (a : MvPowerSeries (Fin n) O) :
    (ψ a).snd = ∑ j, (ψ (X j)).snd * e (pderiv O j a) := by
  have := isLocalRing_trivSqZeroExt (O := O) O
  have : Module.Finite O (DualNumber O) := inferInstanceAs (Module.Finite O (O × O))
  have := GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite O (DualNumber O)
  have h : ψ = dirPt e fun j => (ψ (X j)).snd :=
    mvPowerSeries_algHom_ext_of_isHausdorff (maximalIdeal (DualNumber O))
      (fun i h => he i (hψ _ ▸ TrivSqZeroExt.isUnit_iff_isUnit_fst.1 h))
      (fun i => TrivSqZeroExt.ext (by rw [hψ, dirPt_fst]) (by rw [dirPt_snd_X]))
  exact (congrArg (fun q => (q a).snd) h).trans (dirPt_snd _ _ _)
end GlobalTheory.JacSer
