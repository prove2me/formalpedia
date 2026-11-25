-- Prove2me | solution 1 for GlobalTheory.LowerOps.lower_mem_eigK_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:55:36.64772+00:00
-- url     : https://prove2.me/submissions/a1e65460-e458-45d1-9526-f911e7bbc6a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodConjugateIntegral
import Theorems.Thm_GlobalTheory_LowerOps_inK_mem_eigK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
noncomputable section
open GlobalTheory GlobalTheory.LowerOps
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.LowerOps
theorem _root_.solution {I : Type} {φ : I → E →+* K} {ρ : orderC c →+* Module.End O H} {e f : I → H}
    (hG : IsGens φ ρ e f) {i : I} {N : Module.End K (K ⊗[O] H)} (hN : IsLower ρ (φ i) (e i) (f i) N) {y : H}
    (hy : y ∈ eigLat (K := K) ρ (φ i)) : N (inK K H y) ∈ eigK ρ (bar (φ i)) := by
  rw [(hG i).1, Submodule.mem_span_singleton] at hy
  obtain ⟨r, rfl⟩ := hy
  have hf : inK K H (f i) ∈ eigK ρ (bar (φ i)) := by
    have : f i ∈ eigLat (K := K) ρ (bar (φ i)) := by
      rw [(hG i).2]; exact Submodule.mem_span_singleton_self _
    exact inK_mem_eigK this
  rw [map_smul, LinearMap.map_smul_of_tower, hN.1]
  exact Submodule.smul_of_tower_mem _ r hf
end GlobalTheory.LowerOps
