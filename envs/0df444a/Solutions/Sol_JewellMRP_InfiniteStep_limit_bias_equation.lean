-- Prove2me | solution 1 for JewellMRP.InfiniteStep.limit_bias_equation
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:10:44.574442+00:00
-- url     : https://prove2.me/submissions/8df90cc5-3d0b-4aaf-b3fe-6dba1f17f0fd

import Definitions.Def_JewellMRP_InfiniteStep_Model
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open JewellMRP.InfiniteStep Matrix Finset

namespace CInfinite

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem superharmonic_constant (P : Matrix (S) (S) ℝ)
    (hn : ∀ i j, 0 ≤ P i j) (hrow : ∀ i, ∑ j, P i j = 1) (hP : P.IsIrreducible)
    (v : S → ℝ) (hv : ∀ i, (P *ᵥ v) i ≤ v i) : ∀ i j, v i = v j := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image Finset.univ v Finset.univ_nonempty
  have hp1 (n : ℕ) : P^n *ᵥ (fun _ => (1:ℝ)) = fun _ => 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih]
      ext k
      simpa [Matrix.mulVec, dotProduct] using hrow k
  have hpow (n : ℕ) : ∀ j, (P^n *ᵥ v) j ≤ v j := by
    induction n with
    | zero => simp
    | succ n ih =>
      intro j
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact (Finset.sum_le_sum (s := Finset.univ) (fun k _ => mul_le_mul_of_nonneg_left (ih k) (hn j k))).trans (hv j)
  have heq (j : S) : v i = v j := by
    obtain ⟨n, hn0, hnpos⟩ := (Matrix.isIrreducible_iff_exists_pow_pos hn).mp hP i j
    have hnon (k : S) : 0 ≤ (P^n) i k * (v k-v i) :=
      mul_nonneg (Matrix.pow_apply_nonneg hn n i k) (sub_nonneg.mpr (hmin k (Finset.mem_univ _)))
    have hr : ∑ k, (P^n) i k = 1 := by
      simpa [Matrix.mulVec, dotProduct] using congrFun (hp1 n) i
    have hs : ∑ k, (P^n) i k * (v k-v i) ≤ 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hr, one_mul]
      exact sub_nonpos.mpr (hpow n i)
    have hj := (Finset.single_le_sum (fun k _ => hnon k) (Finset.mem_univ j)).trans hs
    have hz := le_antisymm hj (hnon j)
    have := (mul_eq_zero.mp hz).resolve_left hnpos.ne'
    linarith
  exact fun k j => (heq k).symm.trans (heq j)


theorem constant_fixed (P : Matrix S S ℝ) (hP : IsErgodic P)
    (v : S → ℝ) (hv : ∀ i j, v i = v j) : P *ᵥ v = v := by
  ext i
  change ∑ j, P i j * v j = v i
  simp_rw [hv _ i]
  rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hP.1, one_mul]

theorem pow_constant_fixed (P : Matrix S S ℝ) (hP : IsErgodic P)
    (v : S → ℝ) (hv : ∀ i j, v i = v j) (n : ℕ) : P^n *ᵥ v = v := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', ← Matrix.mulVec_mulVec, ih, constant_fixed P hP v hv]

theorem return_closed (P : Matrix S S ℝ) (ρ V0 : S → ℝ) (n : ℕ) :
    stepReturn P ρ V0 n = (∑ k ∈ Finset.range n, P^k *ᵥ ρ) + P^n *ᵥ V0 := by
  induction n with
  | zero => simp [stepReturn]
  | succ n ih =>
    rw [stepReturn, ih, Matrix.mulVec_add, Matrix.mulVec_sum, Finset.sum_range_succ']
    simp_rw [Matrix.mulVec_mulVec, ← pow_succ']
    simp
    abel

theorem return_increment (P : Matrix S S ℝ) (hP : IsErgodic P) (ρ V0 : S → ℝ)
    (hV0 : ∀ i j, V0 i = V0 j) (n : ℕ) (hn : 1 ≤ n) :
    stepReturn P ρ V0 n - stepReturn P ρ V0 (n-1) = P^(n-1) *ᵥ ρ := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k+1 := ⟨n-1, by omega⟩
  simp only [Nat.add_sub_cancel, return_closed, pow_constant_fixed P hP V0 hV0,
    Finset.sum_range_succ]
  abel

theorem limit_mul_vec (π ρ : S → ℝ) : limitMatrix π *ᵥ ρ = fun _ => gain π ρ := rfl

theorem bias_closed (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (ρ V0 : S → ℝ) (hV0 : ∀ i j, V0 i = V0 j) (n : ℕ) (hn : 1 ≤ n) :
    biasSeq P π ρ V0 n =
      (1 + ∑ j ∈ Finset.Ico 1 n, (P^j-limitMatrix π)-limitMatrix π) *ᵥ ρ + V0 := by
  have hr : (∑ k ∈ Finset.range n, P^k) = 1 + ∑ k ∈ Finset.Ico 1 n, P^k := by
    rw [← Finset.sum_range_add_sum_Ico _ hn]
    simp
  have hc : (Finset.Ico 1 n).card = n-1 := by simp
  unfold biasSeq
  rw [return_closed, pow_constant_fixed P hP V0 hV0, ← Matrix.sum_mulVec, hr]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, hc, Matrix.sub_mulVec,
    Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, limit_mul_vec]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  have hncast : ((n-1 : ℕ) : ℝ) = (n:ℝ)-1 := by norm_cast
  rw [hncast]
  ring

end CInfinite



open JewellMRP.InfiniteStep Matrix Finset

namespace CInfinite

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem P_limit (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) :
    P * limitMatrix π = limitMatrix π := by
  ext i j
  simp only [Matrix.mul_apply, limitMatrix, Matrix.of_apply, ← Finset.sum_mul]
  rw [Matrix.sum_row_of_mem_rowStochastic hP.1, one_mul]

theorem limit_P (P : Matrix S S ℝ) (π : S → ℝ) (hπ : IsStationary P π) :
    limitMatrix π * P = limitMatrix π := by
  ext i j
  exact congrFun hπ.2.2 j

theorem pi_limit (P : Matrix S S ℝ) (π : S → ℝ) (hπ : IsStationary P π) :
    π ᵥ* limitMatrix π = π := by
  ext j
  change ∑ i, π i * π j = π j
  rw [← Finset.sum_mul, hπ.2.1, one_mul]

theorem pi_fundamental_base (P : Matrix S S ℝ) (π : S → ℝ) (hπ : IsStationary P π) :
    π ᵥ* (1-P+limitMatrix π) = π := by
  rw [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_one, hπ.2.2, pi_limit P π hπ]
  simp

theorem fundamental_unit (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) : IsUnit (1-P+limitMatrix π) := by
  have hker (v : S → ℝ) (hv : (1-P+limitMatrix π) *ᵥ v = 0) : v = 0 := by
    have hg : gain π v = 0 := by
      change π ⬝ᵥ v = 0
      rw [← pi_fundamental_base P π hπ, ← Matrix.dotProduct_mulVec, hv]
      simp
    have he : P *ᵥ v = v := by
      simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, limit_mul_vec, hg] at hv
      ext i
      have hh := congrFun hv i
      change v i - (P *ᵥ v) i + 0 = 0 at hh
      linarith
    have hc := superharmonic_constant P (fun i j => Matrix.nonneg_of_mem_rowStochastic hP.1)
      (Matrix.sum_row_of_mem_rowStochastic hP.1) hP.2 v (fun i => (congrFun he i).le)
    ext i
    have hh : gain π v = v i := by
      unfold gain
      simp_rw [hc _ i]
      rw [← Finset.sum_mul, hπ.2.1, one_mul]
    simpa [hg] using hh.symm
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro v w heq
  apply sub_eq_zero.mp
  apply hker
  rw [Matrix.mulVec_sub, heq, sub_self]

theorem fundamental_relations (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) :
    IsUnit (1-(P-limitMatrix π)) ∧
      P * fundamentalMatrix P π = fundamentalMatrix P π * P ∧
      π ᵥ* fundamentalMatrix P π = π ∧
      1-fundamentalMatrix P π = limitMatrix π-P*fundamentalMatrix P π := by
  let A := 1-P+limitMatrix π
  let Z := fundamentalMatrix P π
  have hA : IsUnit A := fundamental_unit P hP π hπ
  have hAZ : A*Z=1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hZA : Z*A=1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hcomm : A*P=P*A := by
    dsimp [A]
    rw [add_mul, sub_mul, one_mul, limit_P P π hπ, mul_add, mul_sub, mul_one, P_limit P hP π]
  have hPZ : P*Z=Z*P := by
    calc
      P*Z = (Z*A)*(P*Z) := by rw [hZA, one_mul]
      _ = Z*(A*P)*Z := by noncomm_ring
      _ = Z*(P*A)*Z := by rw [hcomm]
      _ = (Z*P)*(A*Z) := by noncomm_ring
      _ = Z*P := by rw [hAZ, mul_one]
  have hpi : π ᵥ* Z=π := by
    have h := congrArg (fun v : S → ℝ => v ᵥ* Z) (pi_fundamental_base P π hπ)
    change (π ᵥ* A) ᵥ* Z = π ᵥ* Z at h
    rw [Matrix.vecMul_vecMul, hAZ, Matrix.vecMul_one] at h
    exact h.symm
  have hLZ : limitMatrix π*Z=limitMatrix π := by
    ext i j
    exact congrFun hpi j
  refine ⟨by convert! hA using 1 <;> dsimp [A] <;> abel, hPZ, hpi, ?_⟩
  change 1-Z=limitMatrix π-P*Z
  have h := hAZ
  change (1-P+limitMatrix π)*Z=1 at h
  rw [add_mul, sub_mul, one_mul, hLZ] at h
  rw [← h]
  abel

theorem limit_bias (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) (ρ V0 : S → ℝ) :
    let W := (fundamentalMatrix P π-limitMatrix π)*ᵥρ+limitMatrix π*ᵥV0
    ∀ i, W i+gain π ρ=ρ i+∑ j, P i j*W j := by
  dsimp only
  have hz := congrArg (fun A : Matrix S S ℝ => A *ᵥ ρ)
    (fundamental_relations P hP π hπ).2.2.2
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, limit_mul_vec,
    ← Matrix.mulVec_mulVec] at hz
  intro i
  have h := congrFun hz i
  change ((fundamentalMatrix P π-limitMatrix π)*ᵥρ+limitMatrix π*ᵥV0) i +gain π ρ =
    ρ i+(P*ᵥ((fundamentalMatrix P π-limitMatrix π)*ᵥρ+limitMatrix π*ᵥV0)) i
  simp only [Matrix.sub_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, P_limit P hP π, limit_mul_vec, Pi.add_apply, Pi.sub_apply] at h ⊢
  rw [constant_fixed P hP (fun _ => gain π ρ) (fun _ _ => rfl),
    constant_fixed P hP (fun _ => gain π V0) (fun _ _ => rfl)]
  linarith

end CInfinite

theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π)
    (ρ V0 : S → ℝ) :
    let W := (fundamentalMatrix P π - limitMatrix π) *ᵥ ρ + limitMatrix π *ᵥ V0
    ∀ i, W i + gain π ρ = ρ i + ∑ j, P i j * W j := by
  exact CInfinite.limit_bias P hP π hπ ρ V0

