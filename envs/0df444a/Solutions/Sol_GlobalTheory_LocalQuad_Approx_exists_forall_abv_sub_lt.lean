-- Prove2me | solution 1 for GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:37.076376+00:00
-- url     : https://prove2.me/submissions/29da82d8-f2d7-4eb5-9330-ff84f518d36d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsForallAbvSubLt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix WithZero
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.Approx
open NumberField IsDedekindDomain
open scoped Matrix WithZero
namespace GlobalTheory.LocalQuad.Approx
namespace _root_.GlobalTheory.LocalQuad.Approx
theorem _root_.solution {F : Type*} [Field F] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue F ℝ} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (z : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F, ∀ i, v i (z i - x) < ε := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi h hv).exists_dist_lt
    (fun i ↦ WithAbs.toAbs (v i) (z i)) hε
  refine ⟨x, fun i ↦ ?_⟩
  have hi := (dist_pi_lt_iff hε).1 hx i
  rw [dist_eq_norm, WithAbs.norm_eq_abv] at hi
  convert hi using 2
  rfl
end _root_.GlobalTheory.LocalQuad.Approx
end GlobalTheory.LocalQuad.Approx
