-- Prove2me | solution 1 for GlobalTheory.CoveringCompare.exists_finite_splitOver
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:36.620584+00:00
-- url     : https://prove2.me/submissions/7571f73a-beba-4e06-bfdf-c4906e4f3183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
import Theorems.Thm_GlobalTheory_CoveringCompare_splitOver_of_torusExtension
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UniformizationBase_AbLocusSmooth_smooth
import Theorems.Thm_GlobalTheory_exists_finite_torusExtension


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoveringCompare
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke
namespace GlobalTheory.CoveringCompare
theorem _root_.solution {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩
end GlobalTheory.CoveringCompare
