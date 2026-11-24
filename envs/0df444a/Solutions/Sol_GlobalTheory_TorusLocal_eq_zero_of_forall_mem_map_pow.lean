-- Prove2me | solution 1 for GlobalTheory.TorusLocal.eq_zero_of_forall_mem_map_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:33:51.29375+00:00
-- url     : https://prove2.me/submissions/56e38771-9d33-4f25-bdfb-f7f6ec40b661

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialLocal
import Theorems.Thm_GlobalTheory_TorusNil_map_mem_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusLocal
namespace GlobalTheory.TorusLocal
theorem _root_.solution {A C : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing C] [Algebra A C] [Module.Free A C] (x : C)
    (hx : ∀ n : ℕ, x ∈ (IsLocalRing.maximalIdeal A ^ (n + 1)).map (algebraMap A C)) : x = 0 := by
  let b := Module.Free.chooseBasis A C
  refine b.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top, Ideal.mem_iInf]
  intro n
  have := TorusNil.map_mem_map _ (b.coord i) (hx n)
  rw [Algebra.algebraMap_self, Ideal.map_id] at this
  exact Ideal.pow_le_pow_right (Nat.le_succ n) this
end GlobalTheory.TorusLocal
