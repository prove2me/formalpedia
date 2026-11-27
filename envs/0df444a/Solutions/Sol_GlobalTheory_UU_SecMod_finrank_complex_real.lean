-- Prove2me | solution 1 for GlobalTheory.UU.SecMod.finrank_complex_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:48.94552+00:00
-- url     : https://prove2.me/submissions/4f64ae76-3378-4eb3-8ab8-bda5d189be08

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SmulOneSecEqZeroIff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_FinrankComplexReal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.UU
open GlobalTheory.UU.SecMod
variable {F : Type} [CommRing F] {Y : Scheme.{0}} {p : Y ⟶ Spec (CommRingCat.of F)} {N : LB Y}
namespace GlobalTheory.UU.SecMod
theorem _root_.solution :
    Module.finrank ℝ (SecMod (Spec.map (CommRingCat.ofHom (algebraMap ℝ ℂ)))
      (Inh.trivLB (Spec (CommRingCat.of ℂ)))) = 2 := by
  rw [← (trivEquiv ℝ ℂ).finrank_eq, Complex.finrank_real_complex]
end GlobalTheory.UU.SecMod
