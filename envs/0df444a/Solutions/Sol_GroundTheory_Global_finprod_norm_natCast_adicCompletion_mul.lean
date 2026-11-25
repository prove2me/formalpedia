-- Prove2me | solution 1 for GroundTheory.Global.finprod_norm_natCast_adicCompletion_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:44.735654+00:00
-- url     : https://prove2.me/submissions/5d5d2c27-6648-41e2-a60b-9d1c366ed145

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IndexProductFormula

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
open NumberField IsDedekindDomain
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(n : v.adicCompletion K)‖) *
      (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := FinitePlace.prod_eq_inv_abs_norm hn'
  simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply, map_natCast] at h
  rw [h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  have hpos : (0 : ℝ) < (n : ℝ) ^ Module.finrank ℚ K := by positivity
  push_cast
  rw [abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']
end GroundTheory.Global
