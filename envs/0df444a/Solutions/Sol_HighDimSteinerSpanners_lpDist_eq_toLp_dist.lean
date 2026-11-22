-- Prove2me | solution 1 for HighDimSteinerSpanners.lpDist_eq_toLp_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:50.015892+00:00
-- url     : https://prove2.me/submissions/6fd15c19-a95c-4636-ba52-1ea5bcfccb09

module
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
public import Definitions.Def_LeanPool_SteinerSpanners_Projection
public import Definitions.Def_LeanPool_SteinerSpanners_Combinatorics
public import Definitions.Def_LeanPool_SteinerSpanners_CSP
public import Definitions.Def_LeanPool_SteinerSpanners_Bucketing
public import Definitions.Def_LeanPool_SteinerSpanners_Hamming
public import Definitions.Def_LeanPool_SteinerSpanners_Dvoretzky
public import Definitions.Def_LeanPool_SteinerSpanners
public import Theorems.Thm_HighDimSteinerSpanners_Proofs_Glue_lpDist_eq_toLp_dist_proof


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners
theorem _root_.solution :
    ∀ (p : ℝ), 1 ≤ p →
      ∀ {d : ℕ} (x y : Fin d → ℝ),
        lpDist p x y =
          dist (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y) :=
  HighDimSteinerSpanners.Proofs.Glue.lpDist_eq_toLp_dist_proof
end HighDimSteinerSpanners
