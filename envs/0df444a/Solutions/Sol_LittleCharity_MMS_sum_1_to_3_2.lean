-- Prove2me | solution 2 for LittleCharity.MMS.sum_1_to_3
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:47:56.036159+00:00
-- url     : https://prove2.me/submissions/0dd9e7f8-9440-4d99-a51e-c230e54805cf

import Mathlib
import Definitions.Def_LittleCharity_MMS_Setting

set_option autoImplicit false
open LittleCharity.MMS

theorem lcm_efx_half {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X) (i j : Fin n)
    (hj : 2 ≤ (X j).card) : v i (X j) ≤ 2 * v i (X i) := by
  classical
  have hc : (2 : ℝ) ≤ ((X j).card : ℝ) := by exact_mod_cast hj
  have hcpos : (0 : ℝ) < ((X j).card : ℝ) := by linarith
  have hg : ∀ g ∈ X j, v i (X j) - v i {g} ≤ v i (X i) := by
    intro g hg
    have h1 := hEFX i j g hg
    have h2 : v i ((X j).erase g) = v i (X j) - v i {g} := by
      rw [hadd.1 i ((X j).erase g), hadd.1 i (X j), Finset.sum_erase_eq_sub hg]
    linarith
  have hsum : ((X j).card : ℝ) * v i (X j) - v i (X j) ≤ ((X j).card : ℝ) * v i (X i) := by
    have h3 : ∑ g ∈ X j, (v i (X j) - v i {g}) ≤ ∑ _g ∈ X j, v i (X i) :=
      Finset.sum_le_sum hg
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul,
      ← hadd.1 i (X j)] at h3
    exact h3
  have hV : 0 ≤ v i (X j) := hadd.2 i _
  have hW : 0 ≤ v i (X i) := hadd.2 i _
  -- (c-1) V ≤ c W  and c ≥ 2  ⇒  V ≤ 2 W
  nlinarith

theorem lcm_union_le {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hadd : IsAdditive v) (i : Fin n)
    (A B : Finset (Fin m)) : v i (A ∪ B) ≤ v i A + v i B := by
  classical
  have h := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := fun g => v i {g})
  have h0 : 0 ≤ ∑ g ∈ A ∩ B, v i {g} := Finset.sum_nonneg (fun g _ => hadd.2 i {g})
  rw [hadd.1 i (A ∪ B), hadd.1 i A, hadd.1 i B]
  linarith

theorem lcm_biUnion_le {n m : ℕ} {v : Fin n → Finset (Fin m) → ℝ} (hadd : IsAdditive v) (i : Fin n)
    (X : Fin n → Finset (Fin m)) (T : Finset (Fin n)) :
    v i (T.biUnion X) ≤ ∑ j ∈ T, v i (X j) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.sum_empty]
    rw [hadd.1 i ∅]; simp
  | insert a T ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    exact le_trans (lcm_union_le hadd i _ _) (by linarith)

theorem lcm_sum {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n)
    (N' : Finset (Fin n))
    (hN' : N' = LittleCharity.EFX.sources v X ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card)) :
    v i (N'.biUnion X ∪ LittleCharity.EFX.pool X) ≤
      (2 * (N'.card : ℝ) - ((LittleCharity.EFX.pool X).card : ℝ)) * v i (X i) := by
  classical
  set src := LittleCharity.EFX.sources v X with hsrcdef
  set V := v i (X i) with hV
  have hV0 : 0 ≤ V := hadd.2 i _
  have hsrcN : src ⊆ N' := by
    intro x hx; rw [hN']; simp [hx]
  -- per-term bound
  have hterm : ∀ j ∈ N', v i (X j) ≤ 2 * V - (if j ∈ src then V else 0) := by
    intro j hj
    by_cases hjs : j ∈ src
    · have hsj : LittleCharity.EFX.IsSource v X j := by
        simpa [hsrcdef, LittleCharity.EFX.sources] using hjs
      have := hsj i
      simp only [LittleCharity.EFX.Envies, not_lt] at this
      simp only [hjs, if_true]
      linarith
    · simp only [hjs, if_false, sub_zero]
      rw [hN'] at hj
      simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_filter, Finset.mem_univ,
        true_and] at hj
      rcases hj with (hj | hj) | hj
      · exact absurd hj hjs
      · subst hj; linarith
      · exact lcm_efx_half v hadd X hEFX i j hj
  have h1 := lcm_union_le hadd i (N'.biUnion X) (LittleCharity.EFX.pool X)
  have h2 := lcm_biUnion_le hadd i X N'
  have h3 : ∑ j ∈ N', v i (X j) ≤ ∑ j ∈ N', (2 * V - (if j ∈ src then V else 0)) :=
    Finset.sum_le_sum hterm
  have h4 : ∑ j ∈ N', (2 * V - (if j ∈ src then V else 0)) = 2 * V * N'.card - V * src.card := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have : ∑ j ∈ N', (if j ∈ src then V else 0) = V * src.card := by
      have hf : N'.filter (fun j => j ∈ src) = src := by
        ext x; simp only [Finset.mem_filter]
        exact ⟨fun h => h.2, fun h => ⟨hsrcN h, h⟩⟩
      rw [← Finset.sum_filter, Finset.sum_const, hf, nsmul_eq_mul, mul_comm]
    rw [this]; ring
  have h5 : v i (LittleCharity.EFX.pool X) ≤ V := hpool i
  have hk : ((LittleCharity.EFX.pool X).card : ℝ) + 1 ≤ (src.card : ℝ) := by exact_mod_cast hsrc
  nlinarith

theorem solution {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (hadd : IsAdditive v)
    (X : Fin n → Finset (Fin m)) (hX : LittleCharity.EFX.IsPartialAllocation X) (hEFX : IsEFX v X)
    (hpool : ∀ i, v i (LittleCharity.EFX.pool X) ≤ v i (X i))
    (hsrc : (LittleCharity.EFX.pool X).card < (LittleCharity.EFX.sources v X).card) (i : Fin n)
    (N' : Finset (Fin n))
    (hN' : N' = LittleCharity.EFX.sources v X ∪ {i} ∪ Finset.univ.filter (fun j => 2 ≤ (X j).card)) :
    v i (N'.biUnion X ∪ LittleCharity.EFX.pool X) ≤
      (2 * (N'.card : ℝ) - ((LittleCharity.EFX.pool X).card : ℝ)) * v i (X i) :=
  lcm_sum v hadd X hEFX hpool hsrc i N' hN'
