-- Prove2me | solution 1 for GlobalTheory.Cyc.FontW.sum_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:55.39597+00:00
-- url     : https://prove2.me/submissions/4fc134dc-8c6e-4291-9218-642c4cd21006

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TensorRight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.FontW
namespace GlobalTheory.Cyc.FontW
theorem _root_.solution {G X : Type*} [Group G] [AddCommMonoid X] (N : Subgroup G) (S : Finset G)
    (hS : ∀ h, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ N) (f : G → X) (hf : ∀ g, ∀ n ∈ N, f (g * n) = f g) (σ : G) :
    ∑ s ∈ S, f (σ * s) = ∑ s ∈ S, f s := by
  choose π hπ huniq using hS
  refine Finset.sum_nbij' (fun s => π (σ * s)) (fun t => π (σ⁻¹ * t)) (fun s _ => (hπ _).1)
    (fun s _ => (hπ _).1) (fun s hs => ?_) (fun t ht => ?_) (fun s _ => ?_)
  · refine (huniq _ s ⟨hs, ?_⟩).symm
    have := N.inv_mem (hπ (σ * s)).2
    simpa [mul_assoc] using this
  · refine (huniq _ t ⟨ht, ?_⟩).symm
    have := N.inv_mem (hπ (σ⁻¹ * t)).2
    simpa [mul_assoc] using this
  · have := hf (π (σ * s)) _ (hπ (σ * s)).2
    rw [← this]; simp
end GlobalTheory.Cyc.FontW
