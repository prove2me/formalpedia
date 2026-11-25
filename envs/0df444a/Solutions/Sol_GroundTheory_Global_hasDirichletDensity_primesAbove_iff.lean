-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_primesAbove_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:04.906087+00:00
-- url     : https://prove2.me/submissions/5fb3d974-74f9-4846-bdcd-efa9e33d4e7d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_tendsto_primeIdealZetaSum_univ_div_univ
import Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_primesAbove
import Theorems.Thm_GroundTheory_Global_tendsto_primeIdealZetaSum_univ_atTop


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]
namespace GroundTheory.Global
theorem _root_.solution {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, SplitsCompletely L v) (δ : ℝ) :
    (primesAbove L T).HasDirichletDensity (Module.finrank K L * δ) ↔ T.HasDirichletDensity δ := by
  set n : ℝ := (Module.finrank K L : ℝ) with hndef
  have hn : n ≠ 0 := by
    rw [hndef]
    exact_mod_cast (Module.finrank_pos (R := K) (M := L)).ne'
  have hKL := tendsto_primeIdealZetaSum_univ_div_univ K L
  have hLK := tendsto_primeIdealZetaSum_univ_div_univ L K
  have hKpos := (tendsto_primeIdealZetaSum_univ_atTop K).eventually_gt_atTop 0
  have hLpos := (tendsto_primeIdealZetaSum_univ_atTop L).eventually_gt_atTop 0
  unfold Set.HasDirichletDensity
  constructor
  · intro h
    have := (h.const_mul n⁻¹).mul hLK
    rw [mul_one, ← mul_assoc, inv_mul_cancel₀ hn, one_mul] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hKpos, hLpos] with s hs hK hL
    have hK' := hK.ne'
    have hL' := hL.ne'
    rw [primeIdealZetaSum_primesAbove hT hs]
    field_simp
    rw [hndef]
    try ring
  · intro h
    have := (h.const_mul n).mul hKL
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin, hKpos, hLpos] with s hs hK hL
    have hK' := hK.ne'
    have hL' := hL.ne'
    rw [primeIdealZetaSum_primesAbove hT hs]
    field_simp
    rw [hndef]
    try ring
end GroundTheory.Global
