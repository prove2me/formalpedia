-- Prove2me | solution 1 for GlobalTheory.exists_numerator_of_involution
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:05:09.068813+00:00
-- url     : https://prove2.me/submissions/45a3adb5-b060-43cf-a430-334366154a78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk



set_option autoImplicit false
open Filter PeriodPair Polynomial
open scoped Topology
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {F ι : Type*} [Field F] [CharZero F] [Fintype ι]
    (σ : ι → ι) (hσ : ∀ t, σ (σ t) = t) (p a b : ι → F)
    (hp : ∀ s t, p s = p t ↔ s = t ∨ s = σ t) (hb : ∀ t, b (σ t) = b t)
    (hb0 : ∀ t, b t = 0 ↔ σ t = t) (ha : ∀ t, σ t = t → a t ≠ 0)
    (R : Subring F[X]) (hX : X ∈ R) (hR : ∀ t, C (p t) ∈ R ∧ C (a t) ∈ R ∧ C (b t) ∈ R) :
    ∃ A ∈ R, A.Monic ∧ A.natDegree = Fintype.card ι + 1 ∧ IsCoprime A (∏ t, (X - C (p t))) ∧
      ∀ x, (∀ t, x ≠ p t) → A.eval x =
        (∏ t, (x - p t)) * (x + ∑ t, (a t / (x - p t) + b t / (x - p t) ^ 2)) := by
  classical
  set D : F[X] := ∏ t, (X - C (p t)) with hD
  let E : ι → F[X] := fun t ↦ ∏ s ∈ (Finset.univ.erase t).erase (σ t), (X - C (p s))
  let u : ι → F[X] := fun t ↦ if σ t = t then 1 else X - C (p t)
  have hpσ : ∀ t, p (σ t) = p t := fun t ↦ (hp _ _).mpr (.inr rfl)
  have hDE : ∀ t, D = (X - C (p t)) * (u t * E t) := fun t ↦ by
    rw [hD, ← Finset.mul_prod_erase _ _ (Finset.mem_univ t)]
    congr 1
    by_cases h : σ t = t
    · simp [u, E, h]
    · rw [← Finset.mul_prod_erase _ _ (a := σ t) (by simp [h])]
      simp [u, E, h, hpσ]
  have hDm : D.Monic := monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _
  have hEm : ∀ t, (E t).Monic := fun t ↦ monic_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _
  have hum : ∀ t, (u t).Monic := fun t ↦ by
    simp only [u]; split_ifs; exacts [monic_one, monic_X_sub_C _]
  have hDd : D.natDegree = Fintype.card ι := by
    rw [hD, natDegree_prod_of_monic _ _ fun t _ ↦ monic_X_sub_C _]; simp
  have hXD : (X * D).natDegree = Fintype.card ι + 1 := by
    rw [monic_X.natDegree_mul hDm, hDd, natDegree_X, add_comm]
  have hlt : (∑ t, (C (a t) * u t + C (b t)) * E t).natDegree < (X * D).natDegree := by
    rw [hXD, Nat.lt_succ_iff, ← hDd]
    refine natDegree_sum_le_of_forall_le _ _ fun t _ ↦ natDegree_mul_le.trans ?_
    rw [hDE t, (monic_X_sub_C _).natDegree_mul ((hum t).mul (hEm t)),
      (hum t).natDegree_mul (hEm t), natDegree_add_C]
    have := natDegree_C_mul_le (a t) (u t)
    omega
  refine ⟨X * D + ∑ t, (C (a t) * u t + C (b t)) * E t, ?_,
    (monic_X.mul hDm).add_of_left (degree_lt_degree hlt),
    by rw [natDegree_add_eq_left_of_natDegree_lt hlt, hXD], ?_, fun x hx ↦ ?_⟩
  · refine add_mem (mul_mem hX (prod_mem fun t _ ↦ sub_mem hX (hR t).1))
      (sum_mem fun t _ ↦ mul_mem (add_mem (mul_mem (hR t).2.1 ?_) (hR t).2.2)
        (prod_mem fun t _ ↦ sub_mem hX (hR t).1))
    simp only [u]; split_ifs; exacts [one_mem _, sub_mem hX (hR t).1]
  · refine IsCoprime.prod_right fun t _ ↦
      ((irreducible_X_sub_C (p t)).coprime_iff_not_dvd.mpr ?_).symm
    rw [dvd_iff_isRoot, IsRoot.def]
    have h0 : D.eval (p t) = 0 := by rw [hDE t]; simp
    have h1 : ∀ s, s ≠ t → s ≠ σ t → ((C (a s) * u s + C (b s)) * E s).eval (p t) = 0 :=
      fun s h h' ↦ by
        rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := t), mul_zero]
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨fun e ↦ h' (by rw [e, hσ]), h.symm⟩
        · simp
    have h2 : (E t).eval (p t) ≠ 0 := by
      rw [eval_prod, Finset.prod_ne_zero_iff]
      intro s hs
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hs
      simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
      exact fun e ↦ by have := (hp _ _).mp e.symm; tauto
    rw [eval_add, eval_mul, h0, mul_zero, zero_add, eval_finsetSum]
    by_cases h : σ t = t
    · rw [Finset.sum_eq_single t (fun s _ hs ↦ h1 s hs (by rwa [h])) (by simp)]
      simp [u, h, (hb0 t).mpr h, ha t h, h2]
    · rw [Finset.sum_eq_add t (σ t) (Ne.symm h) (fun s _ hs ↦ h1 s hs.1 hs.2) (by simp) (by simp)]
      have h3 : E (σ t) = E t := by simp only [E, hσ]; rw [Finset.erase_right_comm]
      have h4 : b t ≠ 0 := (hb0 t).not.mpr h
      simp [u, h, hσ, Ne.symm h, hpσ, hb, h3, h4, h2, ← two_mul]
  · have h0 : D.eval x = ∏ t, (x - p t) := by simp [hD, eval_prod]
    rw [← h0, mul_add, eval_add, eval_mul, eval_X, mul_comm, eval_finsetSum, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    have := sub_ne_zero.mpr (hx t)
    rw [hDE t]
    by_cases h : σ t = t
    · simp [u, h, (hb0 t).mpr h]
      field_simp
    · simp [u, h]
      field_simp
end GlobalTheory
