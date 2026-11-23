-- Prove2me | solution 1 for GlobalTheory.RegBound.mem_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:52.774944+00:00
-- url     : https://prove2.me/submissions/316465cd-c2e3-44cf-bfe2-4855a10f9310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniformRegularityBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module MvPolynomial
open GlobalTheory GlobalTheory.RegBound
variable {σ K : Type} [Field K]
namespace GlobalTheory.RegBound
theorem _root_.solution {I : Ideal (MvPolynomial σ K)} {h F : MvPolynomial σ K} :
    F ∈ I ⊔ Ideal.span {h} ↔ ∃ A ∈ I, ∃ B, F = A + h * B := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨A, hA, B, hB, rfl⟩
    obtain ⟨C, rfl⟩ := Ideal.mem_span_singleton.1 hB
    exact ⟨A, hA, C, rfl⟩
  · rintro ⟨A, hA, B, rfl⟩
    exact ⟨A, hA, _, Ideal.mem_span_singleton.2 ⟨B, rfl⟩, rfl⟩
end GlobalTheory.RegBound
