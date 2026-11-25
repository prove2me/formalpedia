-- Prove2me | solution 1 for GlobalTheory.UU.BoxSec.box_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:40:51.52083+00:00
-- url     : https://prove2.me/submissions/b08181f1-c8b4-40a7-ab69-4cc3f0c7d0c3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RepSymInv
import Theorems.Thm_GlobalTheory_UU_BoxSec_prod_famB
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_prod_sum__19c72914c5cb


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.BoxSec
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {Y : Over (Spec (CommRingCat.of R))}
namespace GlobalTheory.UU.BoxSec
theorem _root_.solution (α β : D.X) {U : Type} [CommGroup U] (h : ((D.P.A ⊗ D.P.A).left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4 ⊕ Fin 4, h (Sum.elim (fun i => (fst D.P.A D.P.A).left ≫ D.famφB α i)
      (fun i => (snd D.P.A D.P.A).left ≫ D.famφB β i) k) ^ Sum.elim (DegPre.famε 2) (DegPre.famε 2) k =
    (h (fst D.P.A D.P.A).left ^ (((2 : ℕ) : ℤ) - 1) * h (fst D.P.A D.P.A * cT D _ α).left * (h (cT D _ α).left)⁻¹ *
      h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left) *
    (h (snd D.P.A D.P.A).left ^ (((2 : ℕ) : ℤ) - 1) * h (snd D.P.A D.P.A * cT D _ β).left * (h (cT D _ β).left)⁻¹ *
      h (1 : D.P.A ⊗ D.P.A ⟶ D.P.A).left) :=
  DVR.prod_sum₂ _ (prod_famB D _ α 2 h) (prod_famB D _ β 2 h)
end GlobalTheory.UU.BoxSec
