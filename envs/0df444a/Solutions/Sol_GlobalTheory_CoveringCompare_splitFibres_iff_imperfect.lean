-- Prove2me | solution 1 for GlobalTheory.CoveringCompare.splitFibres_iff_imperfect
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:57:44.759632+00:00
-- url     : https://prove2.me/submissions/6e4c7abc-1e10-4361-8a99-5c0dc2bf7897

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
import Theorems.Thm_GlobalTheory_CoveringCompare_exists_finite_splitOver

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
namespace GlobalTheory.CoveringCompare
theorem _root_.solution (Y : Model Xo c β) :
    Y.SplitFibres ↔ ∀ x : Y.X, ¬ PerfectField (Y.X.residueField x) →
      ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
        FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
          SplitOver Y.t.G x k := by
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  by_cases hx : PerfectField (Y.X.residueField x)
  · obtain ⟨k, _, _, hk, hs⟩ := exists_finite_splitOver Y.t.G Y.t.semi x
    exact ⟨k, inferInstance, inferInstance, hk, inferInstance, hs⟩
  · exact h x hx
end GlobalTheory.CoveringCompare
