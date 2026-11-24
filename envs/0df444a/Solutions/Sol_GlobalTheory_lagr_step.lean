-- Prove2me | solution 1 for GlobalTheory.lagr_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:21:25.32879+00:00
-- url     : https://prove2.me/submissions/4d42a61c-f328-4de6-b720-42bd2b34bd2b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseField
import Theorems.Thm_GlobalTheory_lagr_functional_kills_image
import Theorems.Thm_GlobalTheory_lagrRankOne_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {k : Type} [Field k] (c : k →+* k) {n : ℕ}
    (S : Matrix (Fin n) (Fin n) k) (hSu : IsUnit S.det)
    (A C : Matrix (Fin n) (Fin n) k)
    (hinj : ∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0)
    (hiso : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0)
    (u : Fin n → k) (hu0 : u ≠ 0) (hu : A *ᵥ u = 0) :
    ∃ j : Fin n, (∀ w, (A + lagrRankOne S j * C) *ᵥ w = 0 → A *ᵥ w = 0) ∧
      (A + lagrRankOne S j * C) *ᵥ u ≠ 0 := by
  have hx : C *ᵥ u ≠ 0 := fun h => hu0 (hinj u hu h)
  have hxS : (C *ᵥ u) ᵥ* S ≠ 0 := by
    intro h
    have hI : Function.Injective fun v : Fin n → k => v ᵥ* S :=
      vecMul_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det S).mpr hSu)
    apply hx
    apply hI
    simp only [h, zero_vecMul]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxS
  simp only [Pi.zero_apply] at hj
  refine ⟨j, ?_, ?_⟩
  · intro w hw
    rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec] at hw
    set t := ((C *ᵥ w) ᵥ* S) j with ht
    have hAw : A *ᵥ w = - Pi.single j t := eq_neg_of_add_eq_zero_left hw
    have hφ := lagr_functional_kills_image c S A C hiso u hu w
    have hc : (c ∘ (A *ᵥ w)) = Pi.single j (-(c t)) := by
      rw [hAw]
      funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    rw [hc, dotProduct_single] at hφ
    have hct : c t = 0 := by
      rcases mul_eq_zero.mp hφ with h | h
      · exact absurd h hj
      · exact neg_eq_zero.mp h
    have ht0 : t = 0 := (map_eq_zero c).mp hct
    rw [hAw, ht0, Pi.single_zero, neg_zero]
  · rw [add_mulVec, ← mulVec_mulVec, lagrRankOne_mulVec, hu, zero_add]
    intro h
    have := congrFun h j
    simp only [Pi.single_eq_same, Pi.zero_apply] at this
    exact hj this
end GlobalTheory
