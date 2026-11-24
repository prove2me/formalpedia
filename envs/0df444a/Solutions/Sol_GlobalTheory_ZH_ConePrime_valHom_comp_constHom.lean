-- Prove2me | solution 1 for GlobalTheory.ZH.ConePrime.valHom_comp_constHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:52.439901+00:00
-- url     : https://prove2.me/submissions/a38961ed-39fc-4dd1-8ece-c4d014219f81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUnitCharts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_RingKrullDimOfEtaleMvPolynomial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_VanishingIdealConePrimeHomogeneous
import Theorems.Thm_GlobalTheory_ZH_ConePrime_valHom_constHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.ConePrime
open GlobalTheory.ZH.CrdCalc GlobalTheory.TangentOrigin
variable {k : Type} [Field k] {X : Scheme.{0}}
namespace GlobalTheory.ZH.ConePrime
theorem _root_.solution (p : X ⟶ Sp k) (x : Sp k ⟶ X) (hx : x ≫ p = 𝟙 _) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : (valHom x U h).comp (constHom p U) = RingHom.id k := by
  ext a
  have e : 𝟙 (Sp k) = spMap (RingHom.id k) := (Spec.map_id _).symm
  rw [RingHom.comp_apply, valHom_constHom]
  simp only [hx, e]
  exact evalPt_spMap _ a
end GlobalTheory.ZH.ConePrime
