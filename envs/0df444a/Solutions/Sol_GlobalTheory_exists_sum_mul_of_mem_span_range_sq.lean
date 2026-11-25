-- Prove2me | solution 1 for GlobalTheory.exists_sum_mul_of_mem_span_range_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:53:58.77031+00:00
-- url     : https://prove2.me/submissions/3c26eefc-f4c1-4b99-a24a-efdce5580d50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsWitnessesOfFormallySmoothQuotient
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {S : Type} [CommRing S] {r : ℕ} (g : Fin r → S)
    (x : S) (hx : x ∈ Ideal.span (Set.range g) * Ideal.span (Set.range g)) :
    ∃ b : Fin r → Fin r → S, x = ∑ k, ∑ l, b k l * (g k * g l) := by

  have hx' : x ∈ Ideal.span (Set.range fun p : Fin r × Fin r => g p.1 * g p.2) := by
    open Pointwise in
    have hset : Set.range g * Set.range g =
        Set.range fun p : Fin r × Fin r => g p.1 * g p.2 := by
      ext y
      simp [Set.mem_mul]
    open Pointwise in
    rwa [Ideal.span_mul_span', hset] at hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun S).1 hx'
  refine ⟨fun k l => c (k, l), ?_⟩
  rw [← hc, Fintype.sum_prod_type]
  simp only [smul_eq_mul]
end GlobalTheory
