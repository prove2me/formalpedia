-- Prove2me | solution 1 for GlobalTheory.ThetaBaseChange.actVal_of_isActOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:16.259868+00:00
-- url     : https://prove2.me/submissions/5a9e4e73-999a-4b2d-b927-580863028ea5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorsionEqOneOfTranslationKeepsRatios
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PowEqOneOfPush
import Theorems.Thm_GlobalTheory_ThetaScalar_translT_snd_left


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar
namespace GlobalTheory.ThetaBaseChange
theorem _root_.solution {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ} {T : Over S}
    {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)} (h : IsActOf A L k θ s s') : ActVal θ s s' := by
  intro Z r z J hJ
  have hJ2 := hJ.mem ![(snd T A).left, (translPt A θ.pt).left] r
  have hJ1 := hJ.mem (fun _ : Fin 1 => (snd T A).left) (r ≫ (translT A θ.pt).left)
  simp only [Category.assoc, translT_snd_left] at hJ1
  have e := congrArg (gs r z _) (h (fun k => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] k)))
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  erw [gs_mul _ _ _ hJ2, gs_res _ _ _ hJ2, gs_res _ _ _ hJ2, gs_unit _ _ _ hJ2,
    gs_pull r (translT A θ.pt).left z _ hJ1] at e
  simp only [secVal, thetaVal, sval, val]
  rw [show ((r ≫ (translT A θ.pt).left) ≫ (snd T A).left) = r ≫ (translPt A θ.pt).left by
    rw [Category.assoc, translT_snd_left]]
  exact e
end GlobalTheory.ThetaBaseChange
