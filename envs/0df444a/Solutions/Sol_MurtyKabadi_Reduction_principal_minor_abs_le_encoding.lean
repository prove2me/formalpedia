-- Prove2me | solution 1 for MurtyKabadi.Reduction.principal_minor_abs_le_encoding
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T09:07:29.255062+00:00
-- url     : https://prove2.me/submissions/f0c513bd-09ba-4a5a-9d2b-0273d3d53f70

import Definitions.Def_MurtyKabadi_Reduction_encSize

open MurtyKabadi.Reduction

private lemma sum_subset_le {m : ℕ} (S : Finset (Fin m)) (f : Fin m → ℕ) :
    (∑ i : S, f i.1) ≤ ∑ i, f i := by
  classical
  rw [Finset.sum_coe_sort]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ S)

theorem solution {m : ℕ} (D : Matrix (Fin m) (Fin m) ℤ) (S : Finset (Fin m)) :
    |(D.submatrix (fun i : S => i.1) (fun i : S => i.1)).det| ≤
      (2 : ℤ) ^ encSize D := by
  classical
  let w : Fin m → Fin m → ℕ := fun i j => 1 + Nat.clog 2 ((D i j).natAbs + 1)
  let W : ℕ := ∑ i, ∑ j, w j i
  let A : Matrix S S ℤ := D.submatrix (fun i : S => i.1) (fun i : S => i.1)
  have hentry (i j : S) : |A j i| ≤ (2 : ℤ) ^ (∑ k, w k i.1) := by
    have he : Nat.clog 2 ((D j.1 i.1).natAbs + 1) ≤ ∑ k, w k i.1 :=
      le_trans (by dsimp [w]; omega)
        (Finset.single_le_sum (fun k _ => Nat.zero_le (w k i.1)) (Finset.mem_univ j.1))
    have hab : (D j.1 i.1).natAbs ≤ 2 ^ (∑ k, w k i.1) :=
      le_trans (Nat.le_succ _)
        ((Nat.le_pow_clog (by decide : 1 < 2) _).trans
          (Nat.pow_le_pow_right (by decide : 0 < 2) he))
    have hab' : ((D j.1 i.1).natAbs : ℤ) ≤ (2 : ℤ) ^ (∑ k, w k i.1) := by
      exact_mod_cast hab
    simpa [A, Matrix.submatrix, Int.natCast_natAbs] using hab'
  have hterms (σ : Equiv.Perm S) : (∏ i : S, |A (σ i) i|) ≤ (2 : ℤ) ^ W := by
    calc
      _ ≤ ∏ i : S, (2 : ℤ) ^ (∑ k, w k i.1) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hentry i (σ i))
      _ = (2 : ℤ) ^ (∑ i : S, ∑ k, w k i.1) := by rw [Finset.prod_pow_eq_pow_sum]
      _ ≤ (2 : ℤ) ^ W :=
        pow_le_pow_right₀ (by norm_num) (sum_subset_le S (fun i => ∑ k, w k i))
  have hdet : |A.det| ≤ (Nat.factorial (Fintype.card S) : ℤ) * (2 : ℤ) ^ W := by
    calc
      |A.det| = (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) A.det := rfl
      _ ≤ ∑ σ : Equiv.Perm S,
          (AbsoluteValue.abs : AbsoluteValue ℤ ℤ) (Equiv.Perm.sign σ • ∏ i : S, A (σ i) i) := by
        rw [Matrix.det_apply]
        exact AbsoluteValue.sum_le _ _ _
      _ = ∑ σ : Equiv.Perm S, ∏ i : S, |A (σ i) i| := by
        apply Finset.sum_congr rfl
        intro σ _
        rw [AbsoluteValue.map_units_int_smul, AbsoluteValue.map_prod]
        rfl
      _ ≤ ∑ _σ : Equiv.Perm S, (2 : ℤ) ^ W := Finset.sum_le_sum (fun σ _ => hterms σ)
      _ = _ := by simp [Fintype.card_perm]
  have hcard : Fintype.card S ≤ m := by
    simpa using Fintype.card_subtype_le (fun i : Fin m => i ∈ S)
  have hfactorial : Nat.factorial (Fintype.card S) ≤ 2 ^ (m * m) := by
    calc
      _ ≤ (Fintype.card S) ^ (Fintype.card S) := Nat.factorial_le_pow _
      _ ≤ (2 ^ (Fintype.card S)) ^ (Fintype.card S) :=
        Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
      _ = 2 ^ (Fintype.card S * Fintype.card S) := by rw [pow_mul]
      _ ≤ 2 ^ (m * m) := Nat.pow_le_pow_right (by decide) (Nat.mul_self_le_mul_self hcard)
  have hfactorial' : (Nat.factorial (Fintype.card S) : ℤ) ≤ (2 : ℤ) ^ (m * m) := by
    exact_mod_cast hfactorial
  have hsize : encSize D = m * m + W := by
    dsimp [encSize, W, w]
    rw [Finset.sum_comm]
  calc
    _ = |A.det| := rfl
    _ ≤ (Nat.factorial (Fintype.card S) : ℤ) * (2 : ℤ) ^ W := hdet
    _ ≤ (2 : ℤ) ^ (m * m) * (2 : ℤ) ^ W :=
      mul_le_mul_of_nonneg_right hfactorial' (by positivity)
    _ = (2 : ℤ) ^ encSize D := by rw [← pow_add, hsize]
