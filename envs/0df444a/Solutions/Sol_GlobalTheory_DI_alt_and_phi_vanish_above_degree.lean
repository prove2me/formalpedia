-- Prove2me | solution 1 for GlobalTheory.DI.alt_and_phi_vanish_above_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:11.604077+00:00
-- url     : https://prove2.me/submissions/6a36f7d4-bd21-4f20-a852-d389b8d1f14c

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAntisymmetrizedCupProductVanishAboveDegree
import Theorems.Thm_GlobalTheory_DI_prodL_eq_zero_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K), (∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0) ∧ ∀ (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsPhi p f h Φ → ∀ a, ∀ x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a, ∀ t : Finset ι, a + 1 < t.card → Φ x t = 0 := by
  intro K _ V _ _ ι _ p f h
  have halt : ∀ (a : ℕ) (v : Fin a → V) (t : Finset ι), a + 1 < t.card → alt f h a v t = 0 := by
    intro a v t ht
    simp only [alt, Finset.sum_apply, Pi.smul_apply]
    apply Finset.sum_eq_zero
    intro σ _
    rw [prodL_eq_zero_of_card f h _ t (by simpa using ht), smul_zero]
  refine ⟨halt, ?_⟩
  intro Φ hΦ a x hx t ht
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, -, v, -, rfl⟩ := hx
    rw [hΦ, Pi.smul_apply, halt a v t ht, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | neg x _ hx => simp [hx]
end GlobalTheory.DI
