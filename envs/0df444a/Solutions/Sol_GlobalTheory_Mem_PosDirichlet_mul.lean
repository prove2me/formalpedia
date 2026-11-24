-- Prove2me | solution 1 for GlobalTheory.Mem.PosDirichlet.mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:17:05.541702+00:00
-- url     : https://prove2.me/submissions/b25f3219-c06b-40ad-b628-053b97fb1e8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLSeriesEulerProductStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DedekindZetaFactorizationRay
import Theorems.Thm_GlobalTheory_Mem_PosDirichlet_hasSum_mul_of_norm_summable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
open GlobalTheory GlobalTheory.Mem
open GlobalTheory.Mem.PosDirichlet
namespace GlobalTheory.Mem.PosDirichlet
theorem _root_.solution {F G : ℂ → ℂ} (hF : PosDirichlet F) (hG : PosDirichlet G) :
    PosDirichlet (fun s => F s * G s) := by
  obtain ⟨ι, w, N, hw, hN, h⟩ := hF
  obtain ⟨κ, w', N', hw', hN', h'⟩ := hG
  refine ⟨ι × κ, fun p => w p.1 * w' p.2, fun p => N p.1 * N' p.2,
    fun p => mul_nonneg (hw _) (hw' _), fun p => mul_ne_zero (hN _) (hN' _), fun s hs => ?_⟩
  have e : ∀ p : ι × κ, ((w p.1 * w' p.2 : ℝ) : ℂ) * ((N p.1 * N' p.2 : ℕ) : ℂ) ^ (-s) =
      ((w p.1 : ℂ) * (N p.1 : ℂ) ^ (-s)) * ((w' p.2 : ℂ) * (N' p.2 : ℂ) ^ (-s)) := by
    intro p
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]
    ring
  have h1 := hasSum_mul_of_norm_summable (h s hs) (h' s hs)
  beta_reduce at h1 ⊢
  rw [funext e]
  exact h1
end GlobalTheory.Mem.PosDirichlet
