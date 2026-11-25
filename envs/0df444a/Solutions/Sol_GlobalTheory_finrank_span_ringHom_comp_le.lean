-- Prove2me | solution 1 for GlobalTheory.finrank_span_ringHom_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:32.576805+00:00
-- url     : https://prove2.me/submissions/67974beb-8f7f-499c-ad25-abf463d5ae5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LinearIndependentRingHomCompIff
import Theorems.Thm_GlobalTheory_linearIndependent_ringHom_comp_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A F F' : Type} [CommRing A] [Field F] [Field F']
    (φ : A →+* F) (ψ : A →+* F') (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    {ι μ : Type} [Finite ι] [Finite μ] (c : ι → μ → A) :
    Module.finrank F (Submodule.span F (Set.range fun i m => φ (c i m))) ≤
      Module.finrank F' (Submodule.span F' (Set.range fun i m => ψ (c i m))) := by
  obtain ⟨κ, a, ha, hs, hl⟩ := exists_linearIndependent' F (fun i m => φ (c i m))
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have h1 : LinearIndependent A (fun k => c (a k)) :=
    (linearIndependent_ringHom_comp_iff φ hφ (fun k => c (a k))).1 hl
  have h2 : LinearIndependent F' (fun k m => ψ (c (a k) m)) :=
    (linearIndependent_ringHom_comp_iff ψ hψ (fun k => c (a k))).2 h1
  rw [← hs, finrank_span_eq_card hl, ← finrank_span_eq_card h2]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨k, rfl⟩
  exact ⟨a k, rfl⟩
end GlobalTheory
