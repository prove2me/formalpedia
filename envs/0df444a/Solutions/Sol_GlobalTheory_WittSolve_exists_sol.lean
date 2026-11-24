-- Prove2me | solution 1 for GlobalTheory.WittSolve.exists_sol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:27:05.244119+00:00
-- url     : https://prove2.me/submissions/907cfb6b-8168-47f2-9e68-0e549886e727

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WittVectorExistsUniqueSubMatrixFrobeniusEq
import Theorems.Thm_GlobalTheory_WittSolve_F_add
import Theorems.Thm_GlobalTheory_WittSolve_F_zero
import Theorems.Thm_GlobalTheory_WittSolve_F_smul
import Theorems.Thm_GlobalTheory_WittSolve_smod_iff
import Theorems.Thm_GlobalTheory_WittSolve_modp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.WittSolve
open WittVector
variable {p : ℕ} [hp : Fact p.Prime] {R : Type} [CommRing R] [CharP R p] [PerfectRing R p]
  {ι : Type} [Fintype ι]
variable {M : Matrix ι ι (WittVector p R)}
namespace GlobalTheory.WittSolve
theorem _root_.solution
    (hU : ∀ c : ι → R, ∃! x : ι → R, x - (M.map WittVector.constantCoeff).mulVec
      (fun k => frobenius R p (x k)) = c)
    (c : ι → WittVector p R) : ∃ v, F M v = c := by
  choose U E hUE using modp hU
  obtain ⟨seq, seq_zero, seq_succ⟩ : ∃ seq : ℕ → (ι → WittVector p R) × (ι → WittVector p R),
      seq 0 = (0, c) ∧ ∀ n, seq (n + 1) =
        ((seq n).1 + ((p : WittVector p R) ^ n) • U (seq n).2, E (seq n).2) :=
    ⟨fun n => Nat.rec ((0 : ι → WittVector p R), c)
      (fun n q => (q.1 + ((p : WittVector p R) ^ n) • U q.2, E q.2)) n, rfl, fun _ => rfl⟩
  have inv : ∀ n, c = F M (seq n).1 + ((p : WittVector p R) ^ n) • (seq n).2 := by
    intro n
    induction n with
    | zero => rw [seq_zero, F_zero, pow_zero, one_smul, zero_add]
    | succ n ih =>
      have h2 := hUE (seq n).2
      rw [seq_succ, F_add, F_smul]
      funext k
      have a := congrFun ih k
      have b := congrFun h2 k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b ⊢
      linear_combination a + (p : WittVector p R) ^ n * b
  have compat : ∀ m n, m ≤ n → ∀ k, (p : WittVector p R) ^ m ∣ (seq n).1 k - (seq m).1 k := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => intro k; simp
    | succ n hmn ih =>
      intro k
      rw [seq_succ]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have : (seq n).1 k + (p : WittVector p R) ^ n * U (seq n).2 k - (seq m).1 k =
          ((seq n).1 k - (seq m).1 k) + (p : WittVector p R) ^ n * U (seq n).2 k := by ring
      rw [this]
      exact dvd_add (ih k) (dvd_mul_of_dvd_left (pow_dvd_pow _ hmn) _)
  have hlim : ∀ k, ∃ L : WittVector p R, ∀ n, (seq n).1 k ≡ L [SMOD (Ideal.span
      {(p : WittVector p R)}) ^ n • (⊤ : Submodule (WittVector p R) (WittVector p R))] := by
    intro k
    refine IsPrecomplete.prec inferInstance ?_
    intro m n hmn
    rw [smod_iff]
    exact dvd_sub_comm.1 (compat m n hmn k)
  choose L hL using hlim
  refine ⟨L, ?_⟩
  have hdiff : ∀ n, ∃ w : ι → WittVector p R, L - (seq n).1 = ((p : WittVector p R) ^ n) • w := by
    intro n
    have : ∀ k, ∃ w, L k - (seq n).1 k = (p : WittVector p R) ^ n * w := fun k =>
      dvd_sub_comm.1 ((smod_iff _ _ n).1 (hL k n))
    choose w hw using this
    exact ⟨w, funext fun k => by simp [hw k]⟩
  have hzero : F M L - c = 0 := by
    funext k
    show (F M L - c) k = 0
    refine IsHausdorff.haus (I := Ideal.span {(p : WittVector p R)}) inferInstance _ fun n => ?_
    rw [smod_iff, sub_zero]
    obtain ⟨w, hw⟩ := hdiff n
    have e1 : F M L = F M (seq n).1 + ((p : WittVector p R) ^ n) • F M w := by
      rw [← F_smul, ← hw, ← F_add, add_sub_cancel]
    have e2 := inv n
    refine ⟨F M w k - (seq n).2 k, ?_⟩
    have a := congrFun e1 k
    have b := congrFun e2 k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at a b
    simp only [Pi.sub_apply]
    linear_combination a - b
  exact sub_eq_zero.1 hzero
end GlobalTheory.WittSolve
