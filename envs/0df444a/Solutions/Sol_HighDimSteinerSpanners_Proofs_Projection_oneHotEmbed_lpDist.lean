-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Projection.oneHotEmbed_lpDist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:59.006057+00:00
-- url     : https://prove2.me/submissions/016d7f6a-29b4-42d8-b30a-2d090aad08c6

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
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Geometry_oneHotEmbed_lpDist


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Projection
namespace HighDimSteinerSpanners.Proofs.Projection
theorem _root_.solution {N q : ℕ} (p : ℝ) (hp : 1 ≤ p) : ∀ x y : Fin N → Fin q,
    lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p) :=
  Geometry.oneHotEmbed_lpDist p hp
end HighDimSteinerSpanners.Proofs.Projection
