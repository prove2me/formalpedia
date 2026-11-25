-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue.one_inZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:51:45.0896+00:00
-- url     : https://prove2.me/submissions/36db5bac-1542-4dff-ba14-f46defc3f957

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdmissibleHarmonicLattice
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_NormFactorThetaValue

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
theorem _root_.solution {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} :
    InZ Xo h (fun _ => (1 : T ⟶ Xo.univ.t.G)) := by
  refine ⟨fun _ => one_pow _, fun f i => Finset.prod_eq_one fun j _ => ?_⟩
  haveI := Xo.univ.t.act.hom (f ⟨_, nsmul_single_mem h j⟩ i)
  exact MonObj.one_comp _
end GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
