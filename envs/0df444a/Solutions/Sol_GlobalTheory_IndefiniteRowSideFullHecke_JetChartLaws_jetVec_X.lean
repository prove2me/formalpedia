-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws.jetVec_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:43:19.18998+00:00
-- url     : https://prove2.me/submissions/aa7023d8-e21f-41bb-ac3b-990a038593a9

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SubConstMemOrig
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetChartLaws

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
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {X₀ : Scheme.{0}} {S : Type} [CommRing S]
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
theorem _root_.solution {σ : Type} (c : σ → S) (i : σ) :
    jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) = c i • (DualNumber.eps : DualNumber S) := by
  have h : jetVec c (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      MvPolynomial.aeval (R := S) (fun i => c i • (DualNumber.eps : DualNumber S)) (MvPolynomial.X i) := rfl
  rw [h, MvPolynomial.aeval_X]
end GlobalTheory.IndefiniteRowSideFullHecke.JetChartLaws
