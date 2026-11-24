-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.finite_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:34:00.831316+00:00
-- url     : https://prove2.me/submissions/607f7ed1-3e76-439d-864f-9d8da5c5e3e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Theorems.Thm_GlobalTheory_Mem_PartialZeta_normSq_eq

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
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) : Finite (𝓞 K)ˣ := by
  have hfin := Embeddings.finite_of_norm_le K ℂ 1
  have hone : ∀ (u : (𝓞 K)ˣ) (ψ : K →+* ℂ), ‖ψ ((u : 𝓞 K) : K)‖ = 1 := by
    intro u ψ
    have h := normSq_eq h2 ψ (u : 𝓞 K)
    rw [Ideal.span_singleton_eq_top.2 u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h
  haveI := hfin.to_subtype
  refine Finite.of_injective (fun u : (𝓞 K)ˣ =>
    (⟨((u : 𝓞 K) : K), (u : 𝓞 K).isIntegral_coe, fun ψ => (hone u ψ).le⟩ :
      {x : K | IsIntegral ℤ x ∧ ∀ ψ : K →+* ℂ, ‖ψ x‖ ≤ 1})) ?_
  intro u v huv
  exact Units.ext (RingOfIntegers.ext (by simpa using congrArg Subtype.val huv))
end GlobalTheory.Mem.PartialZeta
