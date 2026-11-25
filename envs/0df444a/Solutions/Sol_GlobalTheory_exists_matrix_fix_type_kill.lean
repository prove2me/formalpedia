-- Prove2me | solution 1 for GlobalTheory.exists_matrix_fix_type_kill
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:02:55.366664+00:00
-- url     : https://prove2.me/submissions/4736dd8b-aa2d-4601-900f-8644f4aa485f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsDualFormsOfSeparatedTypes

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
theorem _root_.solution {O A : Type} [CommRing O] {d : ℕ}
    (ρ : A → Matrix (Fin d) (Fin d) O) {T : Type} [DecidableEq T] {r : T → ℕ} (σ : T → A → O)
    (u : (Σ t : T, Fin (r t)) → Fin d → O)
    (hsep : ∀ t t', t ≠ t' → ∃ a, IsUnit (σ t a - σ t' a))
    (heig : ∀ a l, (ρ a).mulVec (u l) = σ l.1 a • u l) (t₀ : T) (S : Finset T) (hS : t₀ ∉ S) :
    ∃ P : Matrix (Fin d) (Fin d) O, (∀ l, l.1 = t₀ → P.mulVec (u l) = u l) ∧
      (∀ l, l.1 ∈ S → P.mulVec (u l) = 0) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun l _ => Matrix.one_mulVec _, fun l hl => absurd hl (by simp)⟩
  | insert t S htS ih =>
    obtain ⟨P, hP1, hP2⟩ := ih (fun h => hS (Finset.mem_insert_of_mem h))
    have hne : t₀ ≠ t := fun h => hS (h ▸ Finset.mem_insert_self t S)
    obtain ⟨a, c, hc⟩ := hsep t₀ t hne
    have key : ∀ l, (P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O)))).mulVec (u l)
        = ((↑c⁻¹ : O) * (σ l.1 a - σ t a)) • P.mulVec (u l) := by
      intro l
      rw [← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
        Matrix.one_mulVec, heig, ← sub_smul, smul_smul, Matrix.mulVec_smul]
    refine ⟨P * ((↑c⁻¹ : O) • (ρ a - σ t a • (1 : Matrix (Fin d) (Fin d) O))),
      fun l hl => ?_, fun l hl => ?_⟩
    · rw [key, hP1 l hl, hl, ← hc, Units.inv_mul, one_smul]
    · rw [key]
      rcases Finset.mem_insert.mp hl with h | h
      · rw [h, sub_self, mul_zero, zero_smul]
      · rw [hP2 l h, smul_zero]
end GlobalTheory
