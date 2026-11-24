-- Prove2me | solution 1 for GlobalTheory.RelDimFibCrit.exists_minimal_in_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:55:16.285943+00:00
-- url     : https://prove2.me/submissions/bcd120f5-a07e-4eb2-836d-9d10451fb734

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_TrdegResidueFieldEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsAlgebraicOfEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ResidueFieldIsoInvCompSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_SmoothRelativeDimOfTrdeg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.RelDimFibCrit
namespace GlobalTheory.RelDimFibCrit
theorem _root_.solution {R B : Type} [CommRing R] [CommRing B] (φ : R →+* B)
    (P : Ideal B) (hP : P.IsPrime) :
    ∃ P₀ : Ideal B, P₀.IsPrime ∧ P₀ ≤ P ∧ P₀.comap φ = P.comap φ ∧
      ∀ P' : Ideal B, P'.IsPrime → P' ≤ P₀ → P'.comap φ = P.comap φ → P' = P₀ := by
  let s : Set (Ideal B)ᵒᵈ := {Q | (OrderDual.ofDual Q).IsPrime ∧ OrderDual.ofDual Q ≤ P ∧
    (OrderDual.ofDual Q).comap φ = P.comap φ}
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ s (fun c hcs hc y hy => by
    have hyc : OrderDual.ofDual y ∈ OrderDual.ofDual '' c := Set.mem_image_of_mem _ hy
    refine ⟨OrderDual.toDual (sInf (OrderDual.ofDual '' c)), ⟨?_, ?_, ?_⟩, fun z hz => ?_⟩
    · refine Ideal.sInf_isPrime_of_isChain (s := OrderDual.ofDual '' c) ⟨_, hyc⟩ ?_ ?_
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
        rcases hc ha hb (fun h => hab (congrArg _ h)) with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro _ ⟨a, ha, rfl⟩
        exact (hcs ha).1
    · exact (sInf_le hyc).trans (hcs hy).2.1
    · apply le_antisymm
      · exact (Ideal.comap_mono (sInf_le hyc)).trans (hcs hy).2.2.le
      · intro a ha
        change φ a ∈ sInf (OrderDual.ofDual '' c)
        rw [Submodule.mem_sInf]
        rintro _ ⟨z, hz, rfl⟩
        rw [← Ideal.mem_comap, (hcs hz).2.2]
        exact ha
    · exact (sInf_le (Set.mem_image_of_mem OrderDual.ofDual hz) :
        sInf (OrderDual.ofDual '' c) ≤ OrderDual.ofDual z)) (OrderDual.toDual P) ⟨hP, le_rfl, rfl⟩
  refine ⟨OrderDual.ofDual m, hm.prop.1, hm.prop.2.1, hm.prop.2.2, fun P' h1 h2 h3 => ?_⟩
  have := hm.eq_of_ge (y := OrderDual.toDual P') ⟨h1, h2.trans hm.prop.2.1, h3⟩ h2
  exact congrArg OrderDual.ofDual this
end GlobalTheory.RelDimFibCrit
