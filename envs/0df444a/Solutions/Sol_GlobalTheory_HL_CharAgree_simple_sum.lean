-- Prove2me | solution 1 for GlobalTheory.HL.CharAgree.simple_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:14:12.752405+00:00
-- url     : https://prove2.me/submissions/54b5aabd-457e-4910-8ca5-19aa0cfe6743

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCharactersAgreeCommonStabiliser
import Theorems.Thm_GlobalTheory_HL_CharAgree_exists_invol
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.CharAgree
open GlobalTheory.HL.Eichler GlobalTheory.HL.FrameOnto
namespace GlobalTheory.HL.CharAgree
theorem _root_.solution {E : Type} [CommRing E] {r : ℕ} (w : Pt E (r + 1))
    (Z A C : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hZ : ∀ a b, Z a b = w.mat a b * (-1) ^ (r - (b : ℕ)))
    (hA : ∀ i j, i < j → A i j = 0) (hC : ∀ i j, j < i → C i j = 0)
    (h : ∀ a b, ∑ i, A a i * Z i b = ∑ i, Z a i * C i b) :
    ∑ j : Fin r, A j.succ j.castSucc = -∑ j : Fin r, C j.castSucc j.succ := by
  obtain ⟨σ₀, t, h1, h2, h3⟩ := exists_invol w.blocks
  rw [w.size] at h1 h2 h3
  let σ' : Fin (r + 1) → Fin (r + 1) := fun a => ⟨σ₀ a, (h1 a a.2).1⟩
  have hinv : Function.Involutive σ' := fun a => Fin.ext (h1 a a.2).2
  let σ : Fin (r + 1) ≃ Fin (r + 1) := hinv.toPerm
  have hσ : ∀ a, (σ a : ℕ) = σ₀ a := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := hinv
  let z : Fin (r + 1) → Eˣ := fun a => t a * (-1) ^ (r - (σ a : ℕ))
  have hZ' : ∀ a b, Z a b = if b = σ a then (z a : E) else 0 := by
    intro a b
    rw [hZ, Pt.mat, h2 _ _ a.2 b.2]
    by_cases hb : b = σ a
    · rw [if_pos hb, if_pos (by rw [hb, hσ]), hb]; simp [z]
    · rw [if_neg hb, if_neg (fun e : (b : ℕ) = σ₀ a => hb (Fin.ext e)), zero_mul]
  have key : ∀ a c, A a c * z c = z a * C (σ a) (σ c) := by
    intro a c
    have := h a (σ c)
    simpa [hZ'] using this
  have term : ∀ a c : Fin (r + 1), (if (a : ℕ) = c + 1 then A a c else 0) =
      -(if (σ c : ℕ) = σ a + 1 then C (σ a) (σ c) else 0) := by
    intro a c
    by_cases hac : (a : ℕ) = c + 1
    · rw [if_pos hac]
      rcases h3 c (hac ▸ a.2) with ⟨h4, h5⟩ | h4
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [← hac] at h5
        rw [if_pos h4]
        have hz : z a = -z c := by
          have := (σ c).2
          have e : r - (σ a : ℕ) = r - (σ c : ℕ) + 1 := by omega
          simp only [z, e, h5, pow_succ]
          simp
        have := key a c
        rw [hz, Units.val_neg, mul_comm, neg_mul, ← mul_neg] at this
        exact (Units.mul_right_inj _).1 this
      · rw [← hac, ← hσ, ← hσ] at h4
        rw [if_neg (by omega), neg_zero]
        have := key a c
        rw [hC _ _ h4, mul_zero] at this
        exact (Units.mul_left_eq_zero _).1 this
    · rw [if_neg hac]
      by_cases h4 : (σ c : ℕ) = σ a + 1
      · rw [if_pos h4]
        have h5 := h3 (σ a) (h4 ▸ (σ c).2)
        rw [← h4, ← hσ, ← hσ, hσσ, hσσ] at h5
        have h6 : a < c := by
          rcases h5 with ⟨h5, -⟩ | h5
          · exact absurd h5 hac
          · exact h5
        have := key a c
        rw [hA _ _ h6, zero_mul] at this
        rw [(Units.mul_right_eq_zero _).1 this.symm, neg_zero]
      · rw [if_neg h4, neg_zero]
  have hs : ∀ M : Fin (r + 1) → Fin (r + 1) → E,
      ∑ a : Fin (r + 1), ∑ c : Fin (r + 1), (if (a : ℕ) = c + 1 then M a c else 0) =
        ∑ j : Fin r, M j.succ j.castSucc := by
    intro M
    rw [Fin.sum_univ_succ]
    rw [Finset.sum_eq_zero (s := Finset.univ) (fun (c : Fin (r + 1)) _ =>
      if_neg (show ¬ ((0 : Fin (r + 1)) : ℕ) = c + 1 by simp)), zero_add]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j.castSucc]
    · simp
    · intro b _ hb
      exact if_neg fun e => hb (Fin.ext (Nat.add_right_cancel e).symm)
    · simp
  rw [← hs A, ← hs (fun a c => C c a)]
  simp only [term, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm, ← σ.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← σ.sum_comp]
  simp only [hσσ]
end GlobalTheory.HL.CharAgree
