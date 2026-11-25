-- Prove2me | solution 1 for GlobalTheory.UTrans.ReflChar0.exists_fix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:11:04.229684+00:00
-- url     : https://prove2.me/submissions/e4087f1a-a8ee-40a7-855d-52c322b496ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryGeneratedByQuasiReflectionsAndWitt
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_exists_prod_mulVec_eq
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_isU_prod
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_prod_fix
import Theorems.Thm_GlobalTheory_UTrans_ReflChar0_hf_span
import Theorems.Thm_GlobalTheory_UTrans_Calc_isU_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.ReflChar0
open GlobalTheory.UTrans.Calc
variable {E : Type} [Field E] {n : ℕ} {σ : E →+* E} {G : Matrix (Fin n) (Fin n) E}
namespace GlobalTheory.UTrans.ReflChar0
theorem _root_.solution [CharZero E] (hG : IsHerm σ G) {γ : Matrix (Fin n) (Fin n) E} (hγ : IsU σ G γ)
    (x : Fin n → Fin n → E) (h1 : ∀ i, hf σ G (x i) (x i) ≠ 0)
    (h2 : ∀ i j, i ≠ j → hf σ G (x i) (x j) = 0) (k : ℕ) :
    ∃ l : List ((Fin n → E) × E), (∀ p ∈ l, hf σ G p.1 p.1 ≠ 0 ∧ p.2 * σ p.2 = 1) ∧
      ∀ i : Fin n, i.val < k →
        ((l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ) *ᵥ x i = x i := by
  induction k with
  | zero => exact ⟨[], by simp, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, hfix⟩ := ih
    by_cases hk : k < n
    · have hU := isU_mul σ G _ _ (isU_prod hG l hl) hγ
      set δ := (l.map fun p => tv σ G p.1 ((p.2 - 1) / hf σ G p.1 p.1)).prod * γ with hδ
      obtain ⟨m, hm, hmx⟩ :=
        exists_prod_mulVec_eq hG (x ⟨k, hk⟩) (δ *ᵥ x ⟨k, hk⟩) (h1 _) (hU _ _)
      refine ⟨m ++ l, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact ⟨(hm p hp).1, (hm p hp).2.1⟩
        · exact hl p hp
      · intro i hi
        rw [List.map_append, List.prod_append, mul_assoc, ← hδ, ← Matrix.mulVec_mulVec]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · have hne : i ≠ ⟨k, hk⟩ := fun h => by simp [h] at hi
          rw [hfix i hi]
          refine prod_fix _ m fun p hp => hf_span (h2 _ _ hne) ?_ (hm p hp).2.2
          rw [← h2 _ _ hne, ← hU (x i) (x ⟨k, hk⟩), hfix i hi]
        · have : i = ⟨k, hk⟩ := Fin.ext hi
          rw [this]
          exact hmx
    · exact ⟨l, hl, fun i _ => hfix i (lt_of_lt_of_le i.2 (not_lt.1 hk))⟩
end GlobalTheory.UTrans.ReflChar0
