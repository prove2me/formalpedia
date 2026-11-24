-- Prove2me | solution 1 for GlobalTheory.FunObj.pureTensor_fill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T16:09:56.8418+00:00
-- url     : https://prove2.me/submissions/af5e89a6-ebf3-4f15-8660-c00db2003500

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MeasurePreservingPiProdSplit
import Theorems.Thm_GlobalTheory_FunObj_downMap_last
import Theorems.Thm_GlobalTheory_FunObj_fill_ex
import Theorems.Thm_GlobalTheory_FunObj_fill_theta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable {k : Type*} [Field k] (G : Grid k)
variable {G}
variable (hs : 1 ≤ G.s)
namespace GlobalTheory.FunObj
theorem _root_.solution (hm : 0 < G.m) (φ : ∀ b : Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ)
    (x : ColArgs G) (y : RowArgs G) (e : Vars G) :
    G.lines₂ (oppositePath G.m) φ (fill hs x y e) = (∏ i ∈ Finset.range G.m, φ (.ex i G.m) (y i)ᵀ) *
      φ (.theta G.m (G.m - 1)) (lastMap hs hm x)ᵀ * ∏ j : Fin (G.m - 1), stepDatum hs φ j (stepPt (x j) (e j)) := by
  have h1 : ∀ (m : ℕ) (f : ℕ → ℂ), ((List.range m).map f).prod = ∏ i ∈ Finset.range m, f i := fun m f => rfl
  have h2 : ∀ f : ℕ → ℂ, ∏ i ∈ Finset.range G.m, f i = f (G.m - 1) * ∏ j : Fin (G.m - 1), f j := fun f => by
    rw [mul_comm, ← Finset.prod_range, ← Finset.prod_range_succ, Nat.sub_add_cancel hm]
  rw [Grid.lines₂, oppositePath, List.map_append, List.prod_append, List.map_reverse, List.map_reverse,
    List.prod_reverse, List.map_map, List.map_map, h1, h1, mul_assoc]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => congrArg (φ (.ex i G.m)) (fill_ex hs x y e i)
  · rw [h2]
    simp only [Function.comp_apply, fill_theta, downMap_last hs hm]
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [downMap, dif_pos j.2]; rfl
end GlobalTheory.FunObj
