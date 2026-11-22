-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Projection.oneHotEmbed_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:30.124825+00:00
-- url     : https://prove2.me/submissions/e213cc66-4a7d-4e24-91b2-0480bd27647c

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Projection

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection
namespace HighDimSteinerSpanners.Proofs.Projection
theorem _root_.solution {N q : ℕ} : Function.Injective (@oneHotEmbed N q) := by
  classical
  intro x y hxy
  funext v
  have hk := congrFun hxy (finProdFinEquiv (v, x v))
  dsimp only [oneHotEmbed] at hk
  simp only [Equiv.symm_apply_apply, ↓reduceIte] at hk
  split_ifs at hk with hyx
  · exact hyx.symm
  · norm_num at hk
end HighDimSteinerSpanners.Proofs.Projection
