-- Prove2me | solution 1 for GlobalTheory.lb_gen_iso_descend_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:29:25.29698+00:00
-- url     : https://prove2.me/submissions/ac973bc8-c446-4347-8908-692057aa5047

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsMonHomIffOfIsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_BijectiveAppTopOfSmoothOfIsProperOfGeometrically
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsExtensionAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LineBundleTrivialIsoDescendField
import Theorems.Thm_GlobalTheory_FieldDescentGen_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isLB_div


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
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory
open FieldDescentGen
namespace GlobalTheory
theorem _root_.solution : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  intro K₀ K _ _ i X₀ X p₀ p φ h₁ h₂ h₃ H
  refine ⟨fun M hM ⟨t, ht⟩ => exists_gen i p₀ p φ H M hM t ht, fun M N hM hN ⟨w, hw⟩ => ?_⟩
  exact exists_gen i p₀ p φ H (LB.div N M) (LB.isLB_div hN hM) _
    (GtBaseChange.genPull_isGen (chartDiv M N φ) hw)
end GlobalTheory
