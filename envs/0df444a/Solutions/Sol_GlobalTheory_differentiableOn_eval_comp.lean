-- Prove2me | solution 1 for GlobalTheory.differentiableOn_eval_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:34:02.586583+00:00
-- url     : https://prove2.me/submissions/b623bd36-c396-490c-9d4f-ba7850ae22c4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_HolFamilyOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AlgebraMapZeroSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsProjectiveModelPolarisedTorusTheta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {σ E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (u : σ → E → ℂ) (S : Set E)
    (hu : ∀ c, DifferentiableOn ℂ (u c) S) (F : MvPolynomial σ ℂ) :
    DifferentiableOn ℂ (fun z => MvPolynomial.eval (fun c => u c z) F) S := by
  induction F using MvPolynomial.induction_on with
  | C a => simpa using differentiableOn_const a
  | add p q hp hq => simp only [map_add]; exact hp.add hq
  | mul_X p c hp => simp only [map_mul, MvPolynomial.eval_X]; exact hp.mul (hu c)
end GlobalTheory
