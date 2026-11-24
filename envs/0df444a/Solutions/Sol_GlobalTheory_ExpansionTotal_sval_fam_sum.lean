-- Prove2me | solution 1 for GlobalTheory.ExpansionTotal.sval_fam_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:08:36.977437+00:00
-- url     : https://prove2.me/submissions/3958577d-36b5-4e5b-85f4-18789aca3675

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsSecOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecLinOfSecScal
import Theorems.Thm_P2M_GlobalTheory_FieldBaseChange_gs_zero__47fb152d3439
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_sval_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ExpansionTotal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FieldBaseChange
variable {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
  [Field F'] [Algebra (FractionRing R) F'] (θ : TF (R := R) F ⟶ TF (R := R) F') (D : DegPre R)
omit [Algebra (FractionRing R) F']
namespace GlobalTheory.ExpansionTotal
theorem _root_.solution {k n : ℕ} (c : Fin n → F) (s : Fin n → Fam D F k) (α : D.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J} (hJ : Good D.P.L z J) :
    sval ((∑ i, c i • s i).s α) r z J =
      ∑ i, constVal (r ≫ (fst (TF (R := R) F) D.P.A).left) z (c i) * sval ((s i).s α) r z J := by
  classical
  generalize (Finset.univ : Finset (Fin n)) = S
  induction S using Finset.induction_on with
  | empty => exact gs_zero' r z _ (hJ.mem _ r)
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, sval_add _ _ _ _ z hJ, ih,
      sval_smul _ _ _ _ z hJ]; rfl
end GlobalTheory.ExpansionTotal
