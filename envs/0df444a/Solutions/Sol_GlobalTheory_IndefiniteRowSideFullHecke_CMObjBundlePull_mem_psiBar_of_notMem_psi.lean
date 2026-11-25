-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull.mem_psiBar_of_notMem_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:49:45.326498+00:00
-- url     : https://prove2.me/submissions/9918eddd-1b5a-4e03-b2e1-10515a3996c7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasis
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementB
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_CMObjBundlePull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.LamCM
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
attribute [instance] CMObj.field CMObj.numberField CMObj.alg
namespace GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
theorem _root_.solution (H : Host E) (τ : E →+* ℂ) (h : τ ∉ psi H) : τ ∈ psiBar H := by
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    simp only [RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast] at this
    rw [H.sqrt_neg_disc_sq]; exact this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h2 | h2
  · exact absurd h2 h
  · exact h2
end GlobalTheory.IndefiniteRowSideFullHecke.CMObjBundlePull
