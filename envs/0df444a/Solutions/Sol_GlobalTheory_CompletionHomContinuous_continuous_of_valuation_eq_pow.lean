-- Prove2me | solution 1 for GlobalTheory.CompletionHomContinuous.continuous_of_valuation_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:56:18.703664+00:00
-- url     : https://prove2.me/submissions/98b3d825-db44-4608-8cb9-f67e227e786d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ContinuousOfValuationEqPow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter Topology
open scoped WithZeroTopology WithZero
open GlobalTheory GlobalTheory.CompletionHomContinuous
namespace GlobalTheory.CompletionHomContinuous
theorem _root_.solution {A B Γ : Type*} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [hA : Valued A Γ] [hB : Valued B Γ]
    (hs : Function.Surjective hA.v) (g : A →+* B) {e : ℕ} (he : 0 < e)
    (hg : ∀ x, hB.v (g x) = hA.v x ^ e) : Continuous g := by
  refine continuous_of_continuousAt_zero g ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero B Γ).tendsto_right_iff]
  intro γ _
  have hc : Continuous fun x : A => hA.v x ^ e :=
    (Valued.continuous_valuation_of_surjective hs).pow e
  have h0 : Tendsto (fun x : A => hA.v x ^ e) (𝓝 0) (𝓝 0) :=
    hc.tendsto' 0 0 (by simp [he.ne'])
  rw [WithZeroTopology.tendsto_zero] at h0
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  filter_upwards [h0 _ hγ] with x hx
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, hg]
  exact hx
end GlobalTheory.CompletionHomContinuous
