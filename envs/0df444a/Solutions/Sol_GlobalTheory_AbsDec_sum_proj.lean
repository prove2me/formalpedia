-- Prove2me | solution 1 for GlobalTheory.AbsDec.sum_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:53:02.203069+00:00
-- url     : https://prove2.me/submissions/e9fe5966-a0ad-4891-bd99-5f2d7cb00eeb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FixedVectorsIrreducibleSubrepDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Submodule
open GlobalTheory GlobalTheory.AbsDec
namespace GlobalTheory.AbsDec
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} [Fintype ι]
    [DecidableEq ι] (t : ι → Submodule ℂ V) (T : ι → V →ₗ[ℂ] V)
    (hT : ∀ i j, ∀ v ∈ t j, T i v = if i = j then v else 0) {v : V} (hv : v ∈ ⨆ i, t i) :
    ∑ i, T i v = v := by
  refine Submodule.iSup_induction t (motive := fun v => ∑ i, T i v = v) hv
    (fun j x hx => ?_) (by simp) (fun x y hx hy => ?_)
  · simp [hT _ j x hx]
  · simp only [map_add, Finset.sum_add_distrib, hx, hy]
end GlobalTheory.AbsDec
