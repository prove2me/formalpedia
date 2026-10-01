-- Prove2me | solution 1 for JewellMRP.InfiniteStep.fundamental_matrix_cesaro
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:30:27.224497+00:00
-- url     : https://prove2.me/submissions/a2bddc86-a00c-41d4-9659-c61a73361903

import Definitions.Def_JewellMRP_InfiniteStep_Model
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecificLimits.Basic

section

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
end

section

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
end

section

open JewellMRP.InfiniteStep Matrix Finset Filter
open scoped Topology

namespace CInfinite

variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem pow_limit (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (n : ℕ) :
    P^n * limitMatrix π = limitMatrix π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', Matrix.mul_assoc, ih, P_limit P hP π]

theorem limit_fundamental (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) : limitMatrix π * fundamentalMatrix P π = limitMatrix π := by
  ext i j
  exact congrFun (fundamental_relations P hP π hπ).2.2.1 j

theorem sum_power_formula (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) (n : ℕ) :
    (∑ k ∈ Finset.range n, P^k) = n • limitMatrix π + (1-P^n)*fundamentalMatrix P π := by
  have hAZ : (1-P+limitMatrix π)*fundamentalMatrix P π=1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (fundamental_unit P hP π hπ))
  have hs : (∑ k ∈ Finset.range n, P^k) * (1-P+limitMatrix π) =
      (1-P^n)+n • limitMatrix π := by
    rw [mul_add, geom_sum_mul_neg, Finset.sum_mul]
    simp_rw [pow_limit P hP π]
    simp
  calc
    (∑ k ∈ Finset.range n, P^k) = ((∑ k ∈ Finset.range n, P^k)*(1-P+limitMatrix π))*
        fundamentalMatrix P π := by rw [Matrix.mul_assoc, hAZ, mul_one]
    _ = n • limitMatrix π+(1-P^n)*fundamentalMatrix P π := by
      rw [hs, add_mul, smul_mul_assoc, limit_fundamental P hP π hπ]
      abel

theorem inverse_nat_tendsto : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

theorem scaled_pow_tendsto (P : Matrix S S ℝ) (hP : IsErgodic P) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • P^n) atTop (𝓝 0) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hn (n : ℕ) : 0 ≤ (P^n) i j :=
    Matrix.nonneg_of_mem_rowStochastic (Submonoid.pow_mem _ hP.1 n)
  have hu (n : ℕ) : (P^n) i j ≤ 1 :=
    Matrix.le_one_of_mem_rowStochastic (Submonoid.pow_mem _ hP.1 n)
  apply squeeze_zero (fun n => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (hn n))
    (fun n => ?_) inverse_nat_tendsto
  simpa using mul_le_mul_of_nonneg_left (hu n) (inv_nonneg.mpr (Nat.cast_nonneg n))

theorem matrix_cesaro_tendsto (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ∑ k ∈ Finset.range n, P^k) atTop (𝓝 (limitMatrix π)) := by
  have hz : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ • ((1-P^n)*fundamentalMatrix P π)) atTop (𝓝 0) := by
    have h := ((inverse_nat_tendsto.smul_const (1 : Matrix S S ℝ)).sub (scaled_pow_tendsto P hP)).mul_const
      (fundamentalMatrix P π)
    simpa only [zero_smul, sub_zero, zero_mul, ← smul_sub, ← smul_mul_assoc] using h
  have hh : Tendsto (fun n : ℕ => limitMatrix π + (n : ℝ)⁻¹ • ((1-P^n)*fundamentalMatrix P π))
      atTop (𝓝 (limitMatrix π)) := by simpa using (tendsto_const_nhds.add hz)
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [sum_power_formula P hP π hπ, smul_add]
  congr 1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ hn0, one_smul]


theorem sum_Icc_differences {V : Type*} [AddCommGroup V] (f : ℕ → V) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, (f m-f (m-1)))=f n-f 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    abel

theorem sum_Icc_shift {V : Type*} [AddCommMonoid V] (f : ℕ → V) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, f m)=∑ m ∈ Finset.range n, f (m+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem sum_shift_power (P : Matrix S S ℝ) (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, P^m)=P*(∑ m ∈ Finset.range n, P^m) := by
  rw [sum_Icc_shift, Finset.mul_sum]
  simp_rw [pow_succ']

theorem tendsto_mulVec_const {f : ℕ → Matrix S S ℝ} {A : Matrix S S ℝ}
    (hf : Tendsto f atTop (𝓝 A)) (v : S → ℝ) :
    Tendsto (fun n => f n *ᵥ v) atTop (𝓝 (A*ᵥv)) :=
  ((continuous_id.matrix_mulVec continuous_const).tendsto A).comp hf

theorem return_increment_cesaro (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) (ρ V0 : S → ℝ) :
    Tendsto (cesaroMean (fun m => stepReturn P ρ V0 m-stepReturn P ρ V0 (m-1))) atTop
      (𝓝 (limitMatrix π*ᵥρ)) := by
  have h1 := tendsto_mulVec_const (matrix_cesaro_tendsto P hP π hπ) ρ
  have h2 := tendsto_mulVec_const (scaled_pow_tendsto P hP) V0
  have h3 := inverse_nat_tendsto.smul_const V0
  have h : Tendsto (fun n : ℕ => ((n:ℝ)⁻¹ • ∑ k ∈ Finset.range n, P^k)*ᵥρ +
      ((n:ℝ)⁻¹ • P^n)*ᵥV0-(n:ℝ)⁻¹ • V0) atTop (𝓝 (limitMatrix π*ᵥρ)) := by
    simpa using (h1.add h2).sub h3
  convert! h using 1
  ext n i
  simp only [cesaroMean, sum_Icc_differences, return_closed, stepReturn,
    Matrix.smul_mulVec, Matrix.sum_mulVec, smul_sub, smul_add]
  simp

theorem shifted_matrix_cesaro (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) :
    Tendsto (cesaroMean (fun m : ℕ => P^m)) atTop (𝓝 (limitMatrix π)) := by
  have h := (matrix_cesaro_tendsto P hP π hπ).const_mul P
  rw [P_limit P hP π] at h
  convert! h using 1
  ext n i j
  simp only [cesaroMean, sum_shift_power, mul_smul_comm]

end CInfinite
end

section

open JewellMRP.InfiniteStep Matrix Finset Filter
open scoped Topology
namespace CInfinite
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]

theorem bias_power (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) (ρ V0 : S → ℝ) (n : ℕ) :
    biasSeq P π ρ V0 n = fundamentalMatrix P π*ᵥρ + P^n*ᵥ(V0-fundamentalMatrix P π*ᵥρ) := by
  unfold biasSeq
  rw [return_closed, ← Matrix.sum_mulVec, sum_power_formula P hP π hπ]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec,
    Matrix.sub_mulVec, Matrix.one_mulVec, limit_mul_vec, Matrix.mulVec_sub,
    sub_mul, one_mul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
  ring

theorem cesaro_const_add {V : Type*} [AddCommGroup V] [Module ℝ V]
    (v : V) (f : ℕ → V) (n : ℕ) (hn : 1 ≤ n) :
    cesaroMean (fun m => v+f m) n = v+cesaroMean f n := by
  unfold cesaroMean
  rw [Finset.sum_add_distrib, smul_add, Finset.sum_const]
  congr 1
  have hc : (Finset.Icc 1 n).card = n := by simp
  rw [hc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (show n ≠ 0 by omega)

theorem bias_cesaro (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) (ρ V0 : S → ℝ) :
    Tendsto (cesaroMean (biasSeq P π ρ V0)) atTop
      (𝓝 ((fundamentalMatrix P π-limitMatrix π)*ᵥρ+limitMatrix π*ᵥV0)) := by
  have ht := (tendsto_mulVec_const (shifted_matrix_cesaro P hP π hπ) (V0-fundamentalMatrix P π*ᵥρ)).const_add (fundamentalMatrix P π*ᵥρ)
  have hl : fundamentalMatrix P π*ᵥρ + limitMatrix π*ᵥ(V0-fundamentalMatrix P π*ᵥρ) =
      (fundamentalMatrix P π-limitMatrix π)*ᵥρ+limitMatrix π*ᵥV0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, limit_fundamental P hP π hπ, Matrix.sub_mulVec]
    abel
  rw [hl] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change fundamentalMatrix P π*ᵥρ + cesaroMean (fun m => P^m) n*ᵥ(V0-fundamentalMatrix P π*ᵥρ) = cesaroMean (fun m => biasSeq P π ρ V0 m) n
  simp_rw [bias_power P hP π hπ]
  rw [cesaro_const_add _ _ n hn]
  congr 1
  simp only [cesaroMean, Matrix.smul_mulVec, Matrix.sum_mulVec]

theorem partial_deviation (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) (n : ℕ) (hn : 1 ≤ n) :
    1 + ∑ j ∈ Finset.Ico 1 n, (P^j-limitMatrix π) =
      limitMatrix π+fundamentalMatrix P π-P^n*fundamentalMatrix P π := by
  have hr : (∑ k ∈ Finset.range n, P^k) = 1 + ∑ k ∈ Finset.Ico 1 n, P^k := by
    rw [← Finset.sum_range_add_sum_Ico _ hn]
    simp
  have hs := sum_power_formula P hP π hπ n
  rw [hr, sub_mul, one_mul] at hs
  rw [Finset.sum_sub_distrib, Finset.sum_const]
  have hc : (Finset.Ico 1 n).card = n-1 := by simp
  rw [hc]
  have hns : n • limitMatrix π = (n-1) • limitMatrix π+limitMatrix π := by
    conv_lhs => rw [show n = (n-1)+1 by omega]
    rw [add_smul, one_smul]
  rw [hns] at hs
  calc
    1 + ((∑ j ∈ Finset.Ico 1 n, P^j) - (n-1) • limitMatrix π) =
      (1+∑ j ∈ Finset.Ico 1 n, P^j) - (n-1) • limitMatrix π := by abel
    _ = _ := by rw [hs]; abel

theorem fundamental_cesaro (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ)
    (hπ : IsStationary P π) :
    Tendsto (cesaroMean (fun n : ℕ => 1+∑ j ∈ Finset.Ico 1 n, (P^j-limitMatrix π)))
      atTop (𝓝 (fundamentalMatrix P π)) := by
  have ht := ((shifted_matrix_cesaro P hP π hπ).mul_const (fundamentalMatrix P π)).const_sub (limitMatrix π+fundamentalMatrix P π)
  have hl : limitMatrix π+fundamentalMatrix P π-limitMatrix π*fundamentalMatrix P π =
      fundamentalMatrix P π := by rw [limit_fundamental P hP π hπ]; abel
  rw [hl] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have he : cesaroMean (fun m : ℕ => 1+∑ j ∈ Finset.Ico 1 m, (P^j-limitMatrix π)) n =
      cesaroMean (fun m : ℕ => (limitMatrix π+fundamentalMatrix P π) + -(P^m*fundamentalMatrix P π)) n := by
    unfold cesaroMean
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    exact partial_deviation P hP π hπ m (Finset.mem_Icc.mp hm).1
  rw [he, cesaro_const_add _ _ n hn]
  simp only [cesaroMean, Finset.sum_neg_distrib, smul_neg, ← Finset.sum_mul, ← smul_mul_assoc, sub_eq_add_neg]

end CInfinite
end

open JewellMRP.InfiniteStep Matrix Filter Topology


theorem solution {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (P : Matrix S S ℝ) (hP : IsErgodic P) (π : S → ℝ) (hπ : IsStationary P π) :
    Tendsto (cesaroMean (fun n : ℕ => 1 + ∑ j ∈ Finset.Ico 1 n, (P ^ j - limitMatrix π)))
      atTop (𝓝 (fundamentalMatrix P π)) := by
  exact CInfinite.fundamental_cesaro P hP π hπ


