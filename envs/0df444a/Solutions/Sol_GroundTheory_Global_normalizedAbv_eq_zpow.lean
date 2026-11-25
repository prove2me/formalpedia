-- Prove2me | solution 1 for GroundTheory.Global.normalizedAbv_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:05:00.531876+00:00
-- url     : https://prove2.me/submissions/48ca3e14-7534-425a-a2a0-8c987cffe783

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Theorems.Thm_GroundTheory_Global_normalizedAbv_eq_toNNReal
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
namespace GroundTheory.Global
theorem _root_.solution {x : v.adicCompletion K} (hx : x ≠ 0) :
    normalizedAbv v x = (Ideal.absNorm v.asIdeal : ℝ) ^ log (Valued.v x) := by
  have hx' : Valued.v x ≠ 0 := (Valued.v).ne_zero_iff.2 hx
  have key : ∀ (y : ℤᵐ⁰) (hy : y ≠ 0), Multiplicative.toAdd (unzero hy) = log y := by
    rintro (_ | a) hy
    · exact absurd rfl hy
    · rfl
  rw [normalizedAbv_eq_toNNReal, WithZeroMulInt.toNNReal_neg_apply _ hx', key]
  simp
end GroundTheory.Global
