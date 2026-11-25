-- Prove2me | solution 1 for GlobalTheory.Cartier.ratOf_secOnOf_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:35.070563+00:00
-- url     : https://prove2.me/submissions/fe8ce62c-c596-439c-b959-d02fa74531af

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_ne_zero
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_germ


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
open GlobalTheory.Cartier
variable {X : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution [IsIntegral X] {L : LB X} (hL : L.IsLB) {s : L.Sec}
    (hs : IsRegularSec s) (V : X.Opens) [Nonempty V] : ratOf hL s V (secOnOf s V) = 1 := by
  have hm : genericPoint X ∈ V ⊓ L.U (genericChart hL) :=
    ⟨genericPoint_mem V, mem_genericChart hL⟩
  have hne : @id X.functionField
      ((X.presheaf.germ _ _ (mem_genericChart hL)).hom (s.f (genericChart hL))) ≠ 0 :=
    nonZeroDivisors.ne_zero (isRegularFn_iff_germ.1 (hs _) _ _)
  have key : ∀ a b : X.functionField, a = b → b ≠ 0 → a * b⁻¹ = 1 := fun a b e hb => by
    rw [e, mul_inv_cancel₀ hb]
  exact key _ _ (germ_resG inf_le_right _ hm _) hne
end GlobalTheory.Cartier
