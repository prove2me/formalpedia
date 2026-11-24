-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_eq_prod_mul_tprod_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:42.463918+00:00
-- url     : https://prove2.me/submissions/1332b995-c1af-43d0-b940-51afe7968cf9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_multipliable_of_summable_abs_sub_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsTprod
namespace GlobalTheory.CompanionTheory.SW.AbsTprod
theorem _root_.solution {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (S : Finset ι) :
    Multipliable (fun v : {v // v ∉ S} => a v.1) ∧
      ∏' v, a v = (∏ v ∈ S, a v) * ∏' v : {v // v ∉ S}, a v.1 := by
  have hsub : ∀ p : ι → Prop, Multipliable (fun v : {v // p v} => a v.1) := fun p =>
    GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one (a := fun v : {v // p v} => a v.1)
      (h.comp_injective Subtype.val_injective)
  refine ⟨hsub _, ?_⟩
  have key := Multipliable.tprod_mul_tprod_compl (f := a) (s := (S : Set ι))
    (hsub (· ∈ (S : Set ι))) (hsub (· ∈ (S : Set ι)ᶜ))
  rw [← key, Finset.tprod_subtype']
  rfl
end GlobalTheory.CompanionTheory.SW.AbsTprod
