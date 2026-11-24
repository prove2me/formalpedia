-- Prove2me | solution 1 for GlobalTheory.KS.ptDer_iff_dualPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:22:50.120625+00:00
-- url     : https://prove2.me/submissions/1a381e1b-9870-4231-bb95-df38b9b13906

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPoint
import Theorems.Thm_GlobalTheory_KS_PtDual_exists_ptDer
import Theorems.Thm_GlobalTheory_KS_PtDual_existsUnique_point

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (X : Scheme.{0}) (y : Sp ℂ ⟶ X), (∀ δ, PtDer y δ → ∃! v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f) ∧ ∀ v : Sp (DualNumber ℂ) ⟶ X, (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ v = y → ∃ δ, PtDer y δ ∧ ∀ (W : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ W) (f : Γ(X, W)), TrivSqZeroExt.snd (show DualNumber ℂ from (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE W ⊤ h).hom f)) = δ W f :=
  fun _ _ => ⟨fun _ hδ => PtDual.existsUnique_point hδ, fun _ hv => PtDual.exists_ptDer hv⟩
end GlobalTheory.KS
