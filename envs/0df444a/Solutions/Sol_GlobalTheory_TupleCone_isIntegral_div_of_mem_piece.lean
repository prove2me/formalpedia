-- Prove2me | solution 1 for GlobalTheory.TupleCone.isIntegral_div_of_mem_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:09:49.277396+00:00
-- url     : https://prove2.me/submissions/345aeb7b-6c76-4991-bf31-604a7805b0cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteIntegralClosureOfEssFiniteTypeField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIntegralRatioRingIffMemAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TupleCone
open Polynomial
variable (o : Type*) [CommRing o] {L : Type*} [Field L] [Algebra o L] {σ : Type*} (t : σ → L)
variable {o t}
namespace GlobalTheory.TupleCone
theorem _root_.solution (i : σ) {n : ℕ} {a : L} (ha : a ∈ piece o t n) :
    IsIntegral (ratioRing o t i) (a / t i ^ n) := by
  have h1 : ∀ s : cone o t, ((evalRingHom (t i)⁻¹).comp (algebraMap (cone o t) L[X])) s ∈
      ratioRing o t i := by
    rintro ⟨s, hs⟩
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨s, rfl⟩ := hx
      exact Algebra.subset_adjoin ⟨s, by simp [div_eq_mul_inv]⟩
    | algebraMap r => simpa using (ratioRing o t i).algebraMap_mem r
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  have h2 : IsIntegral (ratioRing o t i) (evalRingHom (t i)⁻¹ (C a * X ^ n)) :=
    IsIntegral.map_of_comp_eq (RingHom.codRestrict _ _ h1) (evalRingHom _) rfl ha
  simpa [div_eq_mul_inv] using h2
end GlobalTheory.TupleCone
