-- Prove2me | solution 1 for GroundTheory.Global.exists_abs_primeIdealZetaSum_add_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:34:03.537904+00:00
-- url     : https://prove2.me/submissions/702f9f18-adf3-49ea-8def-40266029542d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Theorems.Thm_GroundTheory_Global_tendsto_sub_one_mul_dedekindZetaReal
import Theorems.Thm_GroundTheory_Global_one_le_dedekindZetaReal
import Theorems.Thm_GroundTheory_Global_abs_log_dedekindZetaReal_sub_tsum_le
import Theorems.Thm_GroundTheory_Global_eventually_summable_dedekindZetaTerm
import Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_univ

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
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (K)
namespace GroundTheory.Global
theorem _root_.solution :
    ∃ C : ℝ, ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |(univ : Set (HeightOneSpectrum (𝓞 K))).primeIdealZetaSum s + Real.log (s - 1)| ≤ C := by
  set R := dedekindZeta_residue K
  set Y := ∑' w : HeightOneSpectrum (𝓞 K), (absNorm w.asIdeal : ℝ) ^ (-(2 : ℝ))
  have hlog : Tendsto (fun s : ℝ => Real.log ((s - 1) * dedekindZetaReal K s)) (𝓝[>] 1)
      (𝓝 (Real.log R)) :=
    (tendsto_sub_one_mul_dedekindZetaReal K).log (dedekindZeta_residue_ne_zero K)
  have hnear : ∀ᶠ s in 𝓝[>] (1 : ℝ),
      |Real.log ((s - 1) * dedekindZetaReal K s) - Real.log R| ≤ 1 := by
    filter_upwards [Metric.tendsto_nhds.mp hlog 1 one_pos] with s hs
    rw [Real.dist_eq] at hs
    exact hs.le
  refine ⟨2 * Y + |Real.log R| + 1, ?_⟩
  filter_upwards [hnear, eventually_summable_dedekindZetaTerm K, self_mem_nhdsWithin]
    with s hs hζ hs1
  have hs1' : 1 < s := hs1
  have hζpos : 0 < dedekindZetaReal K s :=
    lt_of_lt_of_le one_pos (one_le_dedekindZetaReal hζ)
  have hsplit : Real.log ((s - 1) * dedekindZetaReal K s) =
      Real.log (s - 1) + Real.log (dedekindZetaReal K s) :=
    Real.log_mul (by linarith) hζpos.ne'
  have hcmp := abs_log_dedekindZetaReal_sub_tsum_le (K := K) hs1' hζ
  rw [hsplit] at hs
  rw [primeIdealZetaSum_univ]
  rw [abs_le] at hs hcmp ⊢
  have h1 := le_abs_self (Real.log R)
  have h2 := neg_abs_le (Real.log R)
  constructor <;> linarith [hs.1, hs.2, hcmp.1, hcmp.2]
end GroundTheory.Global
