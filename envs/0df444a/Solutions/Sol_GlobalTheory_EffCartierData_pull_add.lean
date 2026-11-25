-- Prove2me | solution 1 for GlobalTheory.EffCartierData.pull_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:31.422351+00:00
-- url     : https://prove2.me/submissions/93ec2df7-c883-49f6-9e16-872d8aaaf85e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

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
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution (φ : Y ⟶ X) (h : D.KeepsRegular φ) (h' : D'.KeepsRegular φ) :
    (D.add D').pull φ (h.add h') = (D.pull φ h).add (D'.pull φ h') := by
  have key : ∀ (A : EffCartierData Y) (f : ∀ i, Γ(Y, A.U i)) (r) (a), f = A.f →
      EffCartierData.mk A.ι A.U f A.cover r a = A := by
    rintro A f r a rfl
    rfl
  exact key ((D.pull φ h).add (D'.pull φ h')) _ _ _ (funext (D.app_add_f D' φ))
end GlobalTheory.EffCartierData
