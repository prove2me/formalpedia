-- Prove2me | solution 1 for OAI.SevenEighths.CubicSieve.HasCubicExponent.frequencyCost_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T23:57:32.264282+00:00
-- url     : https://prove2.me/submissions/af80125d-d171-4877-bf75-a9564bd0e2a5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIHecke78B010

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicDyadicDecay
namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

theorem two_power_majorant (B : ℝ → ℝ) (C P Q t α β : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hα : 0 < α) (hα3 : α < 3) (hβ : 0 < β) (hβ3 : β < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ C * (P*K^α + Q*K^β)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ≤
      C * (P*decayConstant α*t^(-α) + Q*decayConstant β*t^(-β)) := by
  let f (γ : ℝ) (j : ℕ) := ((2 : ℝ)^j)^γ / (1+t*(2 : ℝ)^j)^3
  have hsα : Summable (f α) := decay_summable t α ht hα3
  have hsβ : Summable (f β) := decay_summable t β ht hβ3
  have hs : Summable (fun j => C*(P*f α j+Q*f β j)) :=
    ((hsα.mul_left P).add (hsβ.mul_left Q)).mul_left C
  have hle (j : ℕ) : B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3 ≤
      C*(P*f α j+Q*f β j) := by
    have hi := div_le_div_of_nonneg_right (hB ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num))) (by positivity : 0 ≤ (1+t*(2 : ℝ)^j)^3)
    dsimp [f]
    convert (preTransparency := .instances) hi using 1
    ring
  have hsum := hs.of_nonneg_of_le
    (fun j => div_nonneg (hB0 _ (one_le_pow₀ (by norm_num))) (by positivity)) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs).trans ?_⟩
  rw [tsum_mul_left, (hsα.mul_left P).tsum_add (hsβ.mul_left Q), tsum_mul_left,
    tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC
  have h₁ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t α ht hα hα3) hP
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t β ht hβ hβ3) hQ
  dsimp [f] at *
  nlinarith

theorem sieve_growth_majorant (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by
  have hh := two_power_majorant B (A*N^δ) N 1 t (1/3+δ) (ξ+δ)
    (by positivity) hN.le (by norm_num) ht hα hα3 hβ hβ3 hB0
  simp only [one_mul] at hh
  apply hh
  intro K hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  apply (hB K hK).trans_eq
  rw [Real.mul_rpow hK0.le hN.le, Real.rpow_add hK0, Real.rpow_add hK0]
  ring

lemma poisson_scale_identity (M N α : ℝ) (hM : 0 < M) (hN : 0 < N) :
    M/N * (M/N^2)^(-α) = M^(1-α) * N^(2*α-1) := by
  rw [Real.div_rpow hM.le (sq_nonneg N), Real.rpow_neg hM.le,
    Real.rpow_neg (sq_nonneg N), div_inv_eq_mul,
    ← Real.rpow_natCast_mul hN.le 2 α, Real.rpow_sub hM,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_one]
  norm_num
  ring

lemma poisson_small_power_identity (M N δ β : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^δ * (M/N) * (M/N^2)^(-(β+δ)) =
      N^(3*δ)*M^(-δ)*M^(1-β)*N^(2*β-1) := by
  rw [mul_assoc, poisson_scale_identity M N (β+δ) hM hN]
  calc
    _ = M^(1-(β+δ)) * (N^δ*N^(2*(β+δ)-1)) := by ring
    _ = M^(-δ+(1-β)) * N^(3*δ+(2*β-1)) := by
      rw [← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.rpow_add hM, Real.rpow_add hN]; ring

theorem sieve_poisson_bound (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by
  have ht : 0 < M/N^2 := by positivity
  have hh := (sieve_growth_majorant B A N (M/N^2) δ ξ hA hN ht
    hα hα3 hβ hβ3 hB0 hB).2
  have hden : (fun j : ℕ => B ((2 : ℝ)^j)/(1+(M/N^2)*(2 : ℝ)^j)^3) =
      (fun j : ℕ => B ((2 : ℝ)^j)/(1+M*(2 : ℝ)^j/N^2)^3) := by
    funext j
    congr 2
    ring
  rw [hden] at hh
  apply (mul_le_mul_of_nonneg_left hh (div_pos hM hN).le).trans_eq
  have hid₁ := poisson_small_power_identity M N δ (1/3) hM hN
  have hid₂ := poisson_small_power_identity M N δ ξ hM hN
  have hmix : N * M^(1-(1/3 : ℝ)) * N^(2*(1/3 : ℝ)-1) =
      (M*N)^(2/3 : ℝ) := by
    norm_num
    rw [Real.mul_rpow hM.le hN.le]
    have hn' : N * N^(- (1/3 : ℝ)) = N^(2/3 : ℝ) := by
      calc
        _ = N^(1 : ℝ) * N^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    nlinarith [congrArg (fun x => M^(2/3 : ℝ)*x) hn']
  calc
    _ = A*N*decayConstant (1/3+δ)*(N^δ*(M/N)*(M/N^2)^(-(1/3+δ))) +
        A*decayConstant (ξ+δ)*(N^δ*(M/N)*(M/N^2)^(-(ξ+δ))) := by ring
    _ = _ := by
      rw [hid₁, hid₂]
      have he := congrArg (fun x => A*N^(3*δ)*M^(-δ)*decayConstant (1/3+δ)*x) hmix
      nlinarith [he]

end
end SevenEighths.CubicDyadicDecay

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Algebra
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Operator
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
theorem operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem operator_conjugate_norm_le (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)

omit [DecidableEq m] in
theorem operator_conjugate_norm (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le A)
  simpa only [star_star] using operator_conjugate_norm_le (fun i j => star (A i j))

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  have heq : operator A.conjTranspose = (operator A).adjoint := by
    unfold operator
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [heq]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem squaredNorm_transpose (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm

theorem squaredNorm_reciprocity (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hrecip : ∀ i j, A i j = B j i) : squaredNorm A = squaredNorm B := by
  have h : A = B.transpose := by ext i j; exact hrecip i j
  rw [h, squaredNorm_transpose]

omit [DecidableEq m] in
theorem energy_le_squaredNorm (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 c
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [squaredNorm, mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x] using hs

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Blocks
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem squaredNorm_nonneg (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := sq_nonneg _

theorem masked_energy_le (A : Matrix a n ℂ) (coef phase : n → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) :
    (∑ i, ‖∑ j, A i j * (coef j * phase j)‖ ^ 2) ≤
      squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
  apply (energy_le_squaredNorm A (fun j => coef j * phase j)).trans
  apply mul_le_mul_of_nonneg_left _ (squaredNorm_nonneg A)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase j)

theorem rectangular_block_energy_le
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  have hleft :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card b : ℝ) * squaredNorm A) * ∑ j, ‖coef j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : b, squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := masked_energy_le A coef (fun j => star (B k j) * mask j) (by
          intro j
          rw [norm_mul, norm_star]
          exact (mul_le_mul_of_nonneg_right (hB k j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp [mul_assoc]
  have hright :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : a, squaredNorm (fun k j => star (B k j)) * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := masked_energy_le (fun k j => star (B k j)) coef
          (fun j => A i j * mask j) (by
            intro j
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        have hn : squaredNorm (fun k j => star (B k j)) = squaredNorm B := by
          unfold squaredNorm
          rw [operator_conjugate_norm]
        rw [hn]
        simp [mul_assoc]
  rcases le_total ((Fintype.card b : ℝ) * squaredNorm A)
      ((Fintype.card a : ℝ) * squaredNorm B) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright

theorem cube_family_block_energy_le {c : Type*} [Fintype c]
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef : n → ℂ) (mask : c → n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ l j, ‖mask l j‖ ≤ 1) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask l j‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm A)
          ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  calc
    _ ≤ ∑ l : c, min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact rectangular_block_energy_le A B coef (mask l) hA hB (hmask l)
    _ = _ := by simp [mul_assoc]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Factorization
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.IdealQuotients
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

section
open ConcretePrimeRowBridge ActualEisensteinCubic CompletedGauss ConcreteTraceCRT

theorem primaryGenerator_admissible (I : Ideal O) (hI : Admissible I) : primaryGenerator I ≠ 0 :=
  PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors I hI.1
    (fun P hP => (hI.2.2 P hP).1)

end

open ActualEisensteinCubic CompletedGauss

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.ConstantTermSupport
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic ConcreteTraceCRT CompletedGauss ConcretePrimeRowBridge
open EisensteinSchwartzPoisson GaussGeneratorTransport PrimaryIdealUnitReindex

theorem badPrime_injective : Function.Injective badPrime := by
  have hgood : lambda ∉ (Ideal.span {(2 : O)} : Ideal O) := by
    have hg := cubicTwoIdeal_good
    change lambda ∉ cubicTwoIdeal at hg
    simpa only [cubicTwoIdeal, Ideal.span_singleton_neg] using hg
  intro i j hij
  cases i <;> cases j
  · rfl
  · exfalso
    apply hgood
    have he : (Ideal.span {lambda} : Ideal O) = Ideal.span {(2 : O)} := hij
    rw [← he]
    exact Ideal.subset_span (by simp)
  · exfalso
    apply hgood
    have he : (Ideal.span {(2 : O)} : Ideal O) = Ideal.span {lambda} := hij
    rw [he]
    exact Ideal.subset_span (by simp)
  · rfl

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.UnrestrictedCharacters
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators Classical

namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open IdealMobiusDivisorSum

theorem goodSquarefreePart_admissible (I : Ideal O) : Admissible (goodSquarefreePart I) := by
  have hs : goodPrimeSupport I ⊆ IdealMobiusDivisorSum.primeSupport I := Finset.sdiff_subset
  refine ⟨support_product_ne_zero hs, squarefree_support_product hs, ?_⟩
  intro P hP
  change P ∈ UniqueFactorizationMonoid.normalizedFactors (∏ Q ∈ goodPrimeSupport I, Q) at hP
  rw [factors_support_product hs] at hP
  have hp : P ∈ goodPrimeSupport I := hP
  have hprime := support_prime (hs hp)
  let : P.IsMaximal := (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  exact (prime_good_iff_not_bad P).mpr (Finset.mem_sdiff.mp hp).2

theorem squarefree_bad_good_product (I : Ideal O) (hI : Squarefree I) :
    (∏ P ∈ badPrimeSupport I, P) * goodSquarefreePart I = I := by
  have hu : badPrimeSupport I ∪ goodPrimeSupport I = IdealMobiusDivisorSum.primeSupport I := by
    ext P
    simp only [badPrimeSupport, goodPrimeSupport, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hd : Disjoint (badPrimeSupport I) (goodPrimeSupport I) := by
    apply Finset.disjoint_left.mpr
    intro P hp hq
    exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_inter.mp hp).2
  rw [goodSquarefreePart, ← Finset.prod_union hd, hu]
  exact squarefree_support_product_self hI

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge

theorem fixedBadPrimes_card : fixedBadPrimes.card = 2 := by
  have hn : (Ideal.span {lambda} : Ideal O) ≠ Ideal.span {(2 : O)} := by
    intro h
    have hb : badPrime false = badPrime true := h
    have := badPrime_injective hb
    cases this
  simp [fixedBadPrimes, hn]

theorem fixedBadPrimes_powerset_card : fixedBadPrimes.powerset.card = 4 := by
  rw [Finset.card_powerset, fixedBadPrimes_card]
  norm_num

theorem goodSquarefreePart_norm_le (I : Ideal O) (hI : Squarefree I) :
    Ideal.absNorm (goodSquarefreePart I) ≤ Ideal.absNorm I := by
  have hd : goodSquarefreePart I ∣ I := by
    exact ⟨∏ P ∈ badPrimeSupport I, P, (squarefree_bad_good_product I hI).symm.trans (mul_comm _ _)⟩
  apply Nat.le_of_dvd
  · exact Nat.pos_iff_ne_zero.mpr (fun hn => hI.ne_zero (Ideal.absNorm_eq_zero_iff.mp hn))
  · exact map_dvd Ideal.absNorm hd

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open QuadraticSquarefreeKernel UnrestrictedIdealReindex

end CanonicalQuadraticSieve

open MeasureTheory
open scoped BigOperators Classical SchwartzMap FourierTransform

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.QuadraticSieve.DyadicColumns
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem columnDyadicLength_small_power (ε : ℝ) (hε : 0 < ε) (N : ℝ) (hN : 1 ≤ N) :
    (columnDyadicLength N + 1 : ℝ) ≤ (2 + 1 / (ε * Real.log 2)) * N ^ ε := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0 ≤ Real.log N / Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  have hL : (columnDyadicLength N + 1 : ℝ) ≤ 2 + Real.log N / Real.log 2 := by
    dsimp only [columnDyadicLength]
    linarith
  have hr : 1 ≤ N ^ ε := Real.one_le_rpow hN hε.le
  have hb : Real.log N / Real.log 2 ≤ (N ^ ε / ε) / Real.log 2 :=
    div_le_div_of_nonneg_right (Real.log_le_rpow_div (by linarith) hε) hlog.le
  calc
    _ ≤ 2 + Real.log N / Real.log 2 := hL
    _ ≤ 2 * N ^ ε + (N ^ ε / ε) / Real.log 2 := add_le_add (by linarith) hb
    _ = _ := by field_simp

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge CompletedGauss
open EisensteinSchwartzPoisson UnrestrictedIdealReindex QuadraticSquarefreeKernel

end CanonicalQuadraticSieve

open scoped BigOperators Classical

open scoped BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Eisenstein.SmoothSummands
namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators

open scoped BigOperators Classical SchwartzMap ContDiff

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

lemma divisorDyadicLabel_bounds (N : ℝ) (D : Ideal O)
    (hD : 1 ≤ (Ideal.absNorm D : ℝ)) (hDN : (Ideal.absNorm D : ℝ) ≤ N) :
    (2 : ℝ)^(divisorDyadicLabel N D).val/2 < (Ideal.absNorm D : ℝ) ∧
      (Ideal.absNorm D : ℝ) ≤ (2 : ℝ)^(divisorDyadicLabel N D).val := by
  unfold divisorDyadicLabel
  rw [dif_pos ⟨hD,hDN⟩]
  exact (positive_ideal_dyadic_exists N D hD hDN).choose_spec.2

lemma divisorDyadicScale_ge_one (j : ℕ) : 1 ≤ divisorDyadicScale j := le_max_left _ _

end CanonicalQuadraticSieve

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Ideal
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem idealKernel_reciprocity (I J : Ideal Eis)
    (hI : primaryGenerator I ≠ 0) (hJ : primaryGenerator J ≠ 0) :
    idealKernel I J = idealKernel J I :=
  congrArg eisEmbedding (CubicJacobiGlobal.idealSymbol_reciprocity I J hI hJ)

theorem idealKernel_norm_le_one (I J : Ideal Eis) : ‖idealKernel I J‖ ≤ 1 := by
  rw [idealKernel, ← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm (primaryGenerator J) I) 2).trans_eq (by norm_num)

theorem idealSymbol_fourth (I : Ideal Eis) (x : Eis) :
    (eisEmbedding (CubicJacobiGlobal.idealSymbol I x)) ^ 4 =
      eisEmbedding (CubicJacobiGlobal.idealSymbol I x) := by
  have hlocal (P : Ideal Eis) :
      (eisEmbedding (CubicJacobiGlobal.primeValue P x)) ^ 4 =
        eisEmbedding (CubicJacobiGlobal.primeValue P x) := by
    unfold CubicJacobiGlobal.primeValue
    split_ifs with h
    · let : P.IsMaximal := h.1
      let χ := actualSextic P h.2 ^ 2
      have hχ : χ ^ 3 = 1 := by
        dsimp [χ]
        rw [canonicalSextic_pow_two, MulChar.ringHomComp_pow, cubicChar_pow_three, MulChar.ringHomComp_one]
      simpa only [χ, canonicalSextic_pow_two, MulChar.ringHomComp_apply] using
        cubic_fourth_eq χ hχ (Ideal.Quotient.mk P x)
    · simp
  have hprod (S : Multiset (Ideal Eis)) :
      (eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod)) ^ 4 =
        eisEmbedding ((S.map (fun P => CubicJacobiGlobal.primeValue P x)).prod) := by
    induction S using Multiset.induction_on with
    | empty => simp
    | @cons P S ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons, map_mul, mul_pow, hlocal, ih]
  by_cases hI : I = 0
  · simp [hI]
  · simpa only [CubicJacobiGlobal.idealSymbol, if_neg hI] using
      hprod (UniqueFactorizationMonoid.normalizedFactors I)

theorem idealKernel_square_eq_star (I J : Ideal Eis) :
    idealKernel I J ^ 2 = star (idealKernel I J) :=
  square_eq_star_of_fourth_eq _ (idealSymbol_fourth I (primaryGenerator J))

theorem mem_idealRange {X : ℝ} {I : Ideal Eis} :
    I ∈ idealRange X ↔ Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
  rw [idealRange, Finset.mem_filter, mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hp, hN⟩, ha⟩
    refine ⟨ha, ?_⟩
    have hX : 0 ≤ X := by
      by_contra hn
      have hz : ⌊X⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
      omega
    exact (Nat.cast_le.mpr hN).trans (Nat.floor_le hX)
  · rintro ⟨ha, hN⟩
    refine ⟨⟨Nat.one_le_iff_ne_zero.mpr ?_, Nat.le_floor hN⟩, ha⟩
    intro hz
    exact (primaryGenerator_ne_zero_ideal I ha.2) (Ideal.absNorm_eq_zero_iff.mp hz)

theorem sieveNorm_reciprocity (M N : ℝ) : sieveNorm M N = sieveNorm N M := by
  apply squaredNorm_reciprocity
  intro I J
  exact idealKernel_reciprocity J.val I.val
    (mem_idealRange.mp J.property).1.2 (mem_idealRange.mp I.property).1.2

theorem family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal Eis) (cols : n → Ideal Eis)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i) : ℝ) ≤ M)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) :
    squaredNorm (fun i j => idealKernel (cols j) (rows i)) ≤ sieveNorm M N := by
  let r : m → idealRange M := fun i => ⟨rows i, mem_idealRange.mpr (hrows i)⟩
  let c : n → idealRange N := fun j => ⟨cols j, mem_idealRange.mpr (hcols j)⟩
  have hri : Function.Injective r := fun i j h => hr (congrArg Subtype.val h)
  have hci : Function.Injective c := fun i j h => hc (congrArg Subtype.val h)
  have h := FiniteSieveRestriction.submatrix_norm_le r hri c hci (idealMatrix M N)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Extraction
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem extracted_norm_product (I : Ideal O) (hI : I ≠ 0) :
    (Ideal.absNorm I : ℝ) = (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 * (Ideal.absNorm (cubePart I) : ℝ) ^ 3 := by
  conv_lhs => rw [cubic_factorization I hI]
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Elements
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementCharacter_norm_le_one (I : Ideal O) (hI : primaryGenerator I ≠ 0) (x : O) :
    ‖elementCharacter I hI x‖ ≤ 1 := by
  change ‖eisEmbedding (CubicJacobiGlobal.idealSymbol I x)‖ ≤ 1
  rw [← CanonicalRowCompletion.idealRowHom_square, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (CanonicalRowCompletion.idealRowHom_norm x I) 2).trans_eq (by norm_num)

theorem element_block_energy_le {a b c n : Type*}
    [Fintype a] [Fintype b] [Fintype c] [Fintype n]
    [DecidableEq a] [DecidableEq b] [DecidableEq n]
    (A : a → Ideal O) (B : b → Ideal O) (D : c → O)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, coef j * elementCharacter (cols j) (hc j)
      (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm (fun i j => idealKernel (cols j) (A i)))
          ((Fintype.card a : ℝ) * squaredNorm (fun k j => idealKernel (cols j) (B k))) *
        ∑ j, ‖coef j‖ ^ 2 := by
  have he (i : a) (k : b) (l : c) :
      (∑ j, coef j * elementCharacter (cols j) (hc j)
        (primaryGenerator (A i) * primaryGenerator (B k) ^ 2 * D l)) =
      ∑ j, idealKernel (cols j) (A i) * star (idealKernel (cols j) (B k)) *
        coef j * elementCharacter (cols j) (hc j) (D l) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, map_mul, map_pow]
    change coef j * (idealKernel (cols j) (A i) * idealKernel (cols j) (B k) ^ 2 *
      elementCharacter (cols j) (hc j) (D l)) = _
    rw [idealKernel_square_eq_star]
    ring
  simp_rw [he]
  apply cube_family_block_energy_le
  · exact fun i j => idealKernel_norm_le_one _ _
  · exact fun k j => idealKernel_norm_le_one _ _
  · exact fun l j => elementCharacter_norm_le_one _ _ _

theorem goodPart_admissible (I : Ideal O) : Admissible (goodPart I) := by
  have h := CanonicalQuadraticSieve.goodSquarefreePart_admissible I
  exact ⟨h.2.1, CanonicalQuadraticSieve.primaryGenerator_admissible _ h⟩

theorem badPart_mul_goodPart (I : Ideal O) (hI : Squarefree I) :
    badPart I * goodPart I = I := CanonicalQuadraticSieve.squarefree_bad_good_product I hI

theorem span_extractedGenerator (I : Ideal O) (hI : I ≠ 0) :
    Ideal.span {extractedGenerator I} = I := by
  change CanonicalRowCompletion.principalIdealHom (extractedGenerator I) = I
  unfold extractedGenerator
  simp only [map_mul, map_pow]
  change Ideal.span {primaryGenerator (goodPart (firstPart I))} *
    Ideal.span {primaryGenerator (goodPart (secondPart I))} ^ 2 *
    Ideal.span {idealGenerator (cubePart I)} ^ 3 *
    (Ideal.span {idealGenerator (badPart (firstPart I))} *
      Ideal.span {idealGenerator (badPart (secondPart I))} ^ 2) = I
  rw [(primaryGenerator_spec _ (goodPart_admissible (firstPart I)).2).1,
    (primaryGenerator_spec _ (goodPart_admissible (secondPart I)).2).1,
    span_idealGenerator, span_idealGenerator, span_idealGenerator]
  calc
    _ = (badPart (firstPart I) * goodPart (firstPart I)) *
        (badPart (secondPart I) * goodPart (secondPart I)) ^ 2 * cubePart I ^ 3 := by
      rw [mul_pow]
      simp only [mul_assoc, mul_left_comm, mul_comm]
    _ = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := by
      rw [badPart_mul_goodPart _ (firstPart_squarefree I),
        badPart_mul_goodPart _ (secondPart_squarefree I)]
    _ = I := (cubic_factorization I hI).symm

theorem element_cubic_extraction (z : O) (hz : z ≠ 0) :
    ∃ u : Oˣ, z = u.val * extractedGenerator (Ideal.span {z}) := by
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hz
  have ha : Associated (extractedGenerator (Ideal.span {z})) z :=
    Ideal.span_singleton_eq_span_singleton.mp (span_extractedGenerator _ hI)
  obtain ⟨u, hu⟩ := ha
  exact ⟨u, by simpa only [mul_comm] using hu.symm⟩

theorem badPart_sector (I : Ideal O) :
    ∃ E : CanonicalQuadraticSieve.fixedBadPrimes.powerset, badPart I = ∏ P ∈ E.val, P := by
  exact ⟨⟨CanonicalQuadraticSieve.badPrimeSupport I,
    Finset.mem_powerset.mpr (CanonicalQuadraticSieve.badPrimeSupport_subset I)⟩, rfl⟩

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FullExtraction
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_element_extraction_energy {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (cols : n → Ideal O) (hc : ∀ j, primaryGenerator (cols j) ≠ 0) (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2) ≤
      (96 : ℝ) * (cubeImage R).card *
        min ((secondImage R).card * squaredNorm
            (fun (i : firstImage R) j => idealKernel (cols j) i.val))
          ((firstImage R).card * squaredNorm
            (fun (k : secondImage R) j => idealKernel (cols j) k.val)) *
        ∑ j, ‖coef j‖ ^ 2 := by
  let : Finite Oˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Oˣ := Fintype.ofFinite _
  let D := Oˣ × CanonicalQuadraticSieve.fixedBadPrimes.powerset ×
    CanonicalQuadraticSieve.fixedBadPrimes.powerset × cubeImage R
  let T := D × secondImage R × firstImage R
  let reconstruct : T → O := fun p => primaryGenerator p.2.2.val *
    primaryGenerator p.2.1.val ^ 2 * sourceFactor R p.1
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hc j) z‖ ^ 2
  have hcover : R ⊆ Finset.univ.image reconstruct := by
    intro z hz
    let I : Ideal O := Ideal.span {z}
    obtain ⟨u, hu⟩ := element_cubic_extraction z (hR z hz)
    obtain ⟨e, he⟩ := badPart_sector (firstPart I)
    obtain ⟨f, hf⟩ := badPart_sector (secondPart I)
    let a : firstImage R := ⟨goodPart (firstPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let b : secondImage R := ⟨goodPart (secondPart I), Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    let c : cubeImage R := ⟨cubePart I, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
    refine Finset.mem_image.mpr ⟨((u, e, f, c), b, a), Finset.mem_univ _, ?_⟩
    change primaryGenerator (goodPart (firstPart I)) *
      primaryGenerator (goodPart (secondPart I)) ^ 2 *
        (u.val * idealGenerator (cubePart I) ^ 3 *
          (idealGenerator (∏ P ∈ e.val, P) * idealGenerator (∏ P ∈ f.val, P) ^ 2)) = z
    rw [hu]
    change _ = u.val * extractedGenerator I
    unfold extractedGenerator
    rw [he, hf]
    ring
  have hsum : (∑ z ∈ R, E z) ≤ ∑ p : T, E (reconstruct p) := by
    calc
      _ ≤ ∑ z ∈ Finset.univ.image reconstruct, E z :=
        Finset.sum_le_sum_of_subset_of_nonneg hcover (fun _ _ _ => sq_nonneg _)
      _ ≤ _ := Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)
  have hb := element_block_energy_le
    (fun i : firstImage R => i.val) (fun k : secondImage R => k.val)
    (sourceFactor R) cols hc coef
  have hcard : Fintype.card D = 96 * (cubeImage R).card := by
    have hu : Fintype.card Oˣ = 6 := by
      simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
    simp only [D, Fintype.card_prod, Fintype.card_coe, hu,
      CanonicalQuadraticSieve.fixedBadPrimes_powerset_card]
    omega
  have heq : (∑ p : T, E (reconstruct p)) =
      ∑ l : D, ∑ k : secondImage R, ∑ i : firstImage R,
        ‖∑ j, coef j * elementCharacter (cols j) (hc j)
          (primaryGenerator i.val * primaryGenerator k.val ^ 2 * sourceFactor R l)‖ ^ 2 := by
    simp only [T, Fintype.sum_prod_type, E, reconstruct]
  rw [heq] at hsum
  apply hsum.trans
  dsimp only [D] at hcard
  convert (preTransparency := .instances) hb using 1
  simp only [hcard, Nat.cast_mul, Nat.cast_ofNat, Fintype.card_coe]

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ExtractionBounds
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem extracted_parts_ne_zero (I : Ideal O) (hI : I ≠ 0) :
    firstPart I ≠ 0 ∧ secondPart I ≠ 0 ∧ cubePart I ≠ 0 := by
  have he := cubic_factorization I hI
  rw [he, mul_ne_zero_iff, mul_ne_zero_iff,
    pow_ne_zero_iff (by decide : (2 : ℕ) ≠ 0),
    pow_ne_zero_iff (by decide : (3 : ℕ) ≠ 0)] at hI
  exact ⟨hI.1.1, hI.1.2, hI.2⟩

theorem goodPart_norm_le (I : Ideal O) (hI : Squarefree I) :
    (Ideal.absNorm (goodPart I) : ℝ) ≤ Ideal.absNorm I := by
  exact_mod_cast CanonicalQuadraticSieve.goodSquarefreePart_norm_le I hI

theorem full_element_extraction_norm_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (X Y H N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hH : 1 ≤ H)
    (hfirst : ∀ z ∈ R, (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ X)
    (hsecond : ∀ z ∈ R, (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ Y)
    (hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤ H)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (96 * 128 ^ 2 : ℝ) * H *
        min (Y * sieveNorm X N) (X * sieveNorm Y N) * ∑ j, ‖coef j‖ ^ 2 := by
  have ha : ∀ I ∈ firstImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ X := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (firstPart_squarefree _)).trans (hfirst z hz)⟩
  have hb : ∀ I ∈ secondImage R, Admissible I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    intro I hI
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
    exact ⟨goodPart_admissible _, (goodPart_norm_le _ (secondPart_squarefree _)).trans (hsecond z hz)⟩
  have hca : ((firstImage R).card : ℝ) ≤ 128 * X :=
    DescentFiberCost.finite_ideal_count_real _ X hX
      (fun I hI => primaryGenerator_ne_zero_ideal I (ha I hI).1.2) (fun I hI => (ha I hI).2)
  have hcb : ((secondImage R).card : ℝ) ≤ 128 * Y :=
    DescentFiberCost.finite_ideal_count_real _ Y hY
      (fun I hI => primaryGenerator_ne_zero_ideal I (hb I hI).1.2) (fun I hI => (hb I hI).2)
  have hcc : ((cubeImage R).card : ℝ) ≤ 128 * H := by
    apply DescentFiberCost.finite_ideal_count_real _ H hH
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact (extracted_parts_ne_zero _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))).2.2
    · intro I hI
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hI
      exact hcube z hz
  have hna := family_squared_norm_le (fun I : firstImage R => I.val) cols
    Subtype.val_injective hinj X N (fun I => ha I.val I.property) hcols
  have hnb := family_squared_norm_le (fun I : secondImage R => I.val) cols
    Subtype.val_injective hinj Y N (fun I => hb I.val I.property) hcols
  have hmin : min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) ≤
      128 * min (Y * sieveNorm X N) (X * sieveNorm Y N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 128)]
    apply min_le_min
    · calc
        _ ≤ (128 * Y) * sieveNorm X N := mul_le_mul hcb hna (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
    · calc
        _ ≤ (128 * X) * sieveNorm Y N := mul_le_mul hca hnb (squaredNorm_nonneg _) (by positivity)
        _ = _ := by ring
  have hn : 0 ≤ min ((secondImage R).card * squaredNorm
      (fun (i : firstImage R) j => idealKernel (cols j) i.val))
      ((firstImage R).card * squaredNorm
      (fun (k : secondImage R) j => idealKernel (cols j) k.val)) := by
    exact le_min (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (squaredNorm_nonneg _))
  calc
    _ ≤ _ := full_element_extraction_energy R hR cols (fun j => (hcols j).1.2) coef
    _ ≤ (96 * (128 * H)) * (128 * min (Y * sieveNorm X N) (X * sieveNorm Y N)) *
        ∑ j, ‖coef j‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcc (by norm_num)) hmin hn (by positivity)
    _ = _ := by ring

theorem cubePart_norm_le_of_block (I : Ideal O) (hI : I ≠ 0)
    (X Y H : ℝ) (hX : 0 < X) (hY : 0 < Y) (hH : 0 ≤ H)
    (hx : X ≤ (Ideal.absNorm (firstPart I) : ℝ))
    (hy : Y ≤ (Ideal.absNorm (secondPart I) : ℝ))
    (hN : (Ideal.absNorm I : ℝ) ≤ X * Y ^ 2 * H ^ 3) :
    (Ideal.absNorm (cubePart I) : ℝ) ≤ H := by
  have hp := extracted_norm_product I hI
  have hxy : X * Y ^ 2 ≤ (Ideal.absNorm (firstPart I) : ℝ) *
      (Ideal.absNorm (secondPart I) : ℝ) ^ 2 :=
    mul_le_mul hx (pow_le_pow_left₀ hY.le hy 2) (sq_nonneg _) (Nat.cast_nonneg _)
  apply le_of_pow_le_pow_left₀ (by decide : (3 : ℕ) ≠ 0) hH
  apply (mul_le_mul_iff_right₀ (mul_pos hX (sq_pos_of_pos hY))).mp
  calc
    _ ≤ (Ideal.absNorm (firstPart I) : ℝ) *
        (Ideal.absNorm (secondPart I) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart I) : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hxy (by positivity)
    _ = Ideal.absNorm I := hp.symm
    _ ≤ _ := hN

theorem full_element_dyadic_block_bound {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hR : ∀ z ∈ R, z ≠ 0)
    (M X Y N : ℝ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X * Y ^ 2 ≤ M)
    (hfirst : ∀ z ∈ R, X ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤ 2 * X)
    (hsecond : ∀ z ∈ R, Y ≤ (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤ 2 * Y)
    (hnorm : ∀ z ∈ R, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
      (192 * 128 ^ 2 : ℝ) * (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
        min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) * ∑ j, ‖coef j‖ ^ 2 := by
  have hp : 0 < X * Y ^ 2 := by positivity
  have hq : 1 ≤ M / (X * Y ^ 2) := (le_div_iff₀ hp).mpr (by simpa using hXY)
  have hH : 1 ≤ (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hq (by norm_num)
  have hpow : ((M / (X * Y ^ 2)) ^ (1 / 3 : ℝ)) ^ 3 = M / (X * Y ^ 2) := by
    simpa only [one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (by linarith : 0 ≤ M / (X * Y ^ 2)) (by decide : (3 : ℕ) ≠ 0)
  have hcube : ∀ z ∈ R, (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ≤
      (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) := by
    intro z hz
    apply cubePart_norm_le_of_block _ (Ideal.span_singleton_eq_bot.not.mpr (hR z hz))
      X Y _ (by linarith) (by linarith) (by linarith) (hfirst z hz).1 (hsecond z hz).1
    rw [hpow, mul_div_cancel₀ _ hp.ne']
    exact hnorm z hz
  have hb := full_element_extraction_norm_bound R hR (2 * X) (2 * Y) _ N
    (by linarith) (by linarith) hH (fun z hz => (hfirst z hz).2)
    (fun z hz => (hsecond z hz).2) hcube cols hinj hcols coef
  convert (preTransparency := .instances) hb using 1
  have hm : min (2 * Y * sieveNorm (2 * X) N) (2 * X * sieveNorm (2 * Y) N) =
      2 * min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) := by
    rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1 <;> ring
  rw [hm]
  ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Dyadic
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma extracted_norm_bounds (I : Ideal O) (hI : I ≠ 0) :
    (1 ≤ (Ideal.absNorm (firstPart I) : ℝ) ∧
      (Ideal.absNorm (firstPart I) : ℝ) ≤ Ideal.absNorm I) ∧
    (1 ≤ (Ideal.absNorm (secondPart I) : ℝ) ∧
      (Ideal.absNorm (secondPart I) : ℝ) ≤ Ideal.absNorm I) := by
  have hn : 0 < Ideal.absNorm I := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp := extracted_parts_ne_zero I hI
  have ha : 1 ≤ Ideal.absNorm (firstPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.1)
  have hb : 1 ≤ Ideal.absNorm (secondPart I) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.2.1)
  have hda : firstPart I ∣ I := ⟨secondPart I ^ 2 * cubePart I ^ 3, by
    simpa only [mul_assoc] using cubic_factorization I hI⟩
  have hdb : secondPart I ∣ I := ⟨firstPart I * secondPart I * cubePart I ^ 3, by
    calc
      I = firstPart I * secondPart I ^ 2 * cubePart I ^ 3 := cubic_factorization I hI
      _ = _ := by ring⟩
  exact ⟨⟨by exact_mod_cast ha, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hda)⟩,
    ⟨by exact_mod_cast hb, by exact_mod_cast Nat.le_of_dvd hn (map_dvd Ideal.absNorm hdb)⟩⟩

lemma sum_extractionBins {A : Type*} [AddCommMonoid A] (R : Finset O) (M : ℝ) (f : O → A) :
    (∑ z ∈ R, f z) = ∑ j, ∑ z ∈ extractionBin R M j, f z := by
  simp only [extractionBin, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  simp

lemma extractionBin_bounds (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (z : O) (hz : z ∈ extractionBin R M j) :
    (CanonicalQuadraticSieve.divisorDyadicScale j.1.val ≤
        (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.1.val) ∧
    (CanonicalQuadraticSieve.divisorDyadicScale j.2.val ≤
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ∧
      (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ≤
        2 * CanonicalQuadraticSieve.divisorDyadicScale j.2.val) := by
  obtain ⟨hzR, hj⟩ := Finset.mem_filter.mp hz
  have hparts := extracted_norm_bounds (Ideal.span {z})
    (Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1)
  have hx := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.1.1
    (hparts.1.2.trans (hR z hzR).2)
  have hy := CanonicalQuadraticSieve.divisorDyadicLabel_bounds M _ hparts.2.1
    (hparts.2.2.trans (hR z hzR).2)
  have hj1 := congrArg Prod.fst hj
  have hj2 := congrArg Prod.snd hj
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.1 at hj1
  change CanonicalQuadraticSieve.divisorDyadicLabel M _ = j.2 at hj2
  rw [hj1] at hx
  rw [hj2] at hy
  refine ⟨⟨max_le hparts.1.1 hx.1.le, ?_⟩, ⟨max_le hparts.2.1 hy.1.le, ?_⟩⟩
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.1.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hx.2]
  · have hm := le_max_right (1 : ℝ) ((2 : ℝ)^j.2.val/2)
    change _ ≤ 2 * max 1 _
    linarith [hy.2]

lemma extractionBin_scale_product (R : Finset O) (M : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (j : Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
      Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1))
    (hj : (extractionBin R M j).Nonempty) :
    CanonicalQuadraticSieve.divisorDyadicScale j.1.val *
      CanonicalQuadraticSieve.divisorDyadicScale j.2.val ^ 2 ≤ M := by
  obtain ⟨z, hz⟩ := hj
  have hzR := (Finset.mem_filter.mp hz).1
  have hI : (Ideal.span {z} : Ideal O) ≠ 0 :=
    Ideal.span_singleton_eq_bot.not.mpr (hR z hzR).1
  have hh := extractionBin_bounds R M hR j z hz
  have hcube : 1 ≤ (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (extracted_parts_ne_zero _ hI).2.2)
  calc
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 :=
      mul_le_mul hh.1.1 (pow_le_pow_left₀
        (le_trans (by norm_num) (CanonicalQuadraticSieve.divisorDyadicScale_ge_one _)) hh.2.1 2)
        (sq_nonneg _) (Nat.cast_nonneg _)
    _ ≤ (Ideal.absNorm (firstPart (Ideal.span {z})) : ℝ) *
        (Ideal.absNorm (secondPart (Ideal.span {z})) : ℝ) ^ 2 *
        (Ideal.absNorm (cubePart (Ideal.span {z})) : ℝ) ^ 3 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ hcube)
    _ = Ideal.absNorm (Ideal.span {z}) := (extracted_norm_product _ hI).symm
    _ ≤ M := (hR z hzR).2

theorem full_element_dyadic_extraction {n : Type*} [Fintype n] [DecidableEq n]
    (R : Finset O) (hRne : R.Nonempty) (M N : ℝ)
    (hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M)
    (cols : n → Ideal O) (hinj : Function.Injective cols)
    (hcols : ∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (coef : n → ℂ) :
    ∃ X Y : ℝ, 1 ≤ X ∧ 1 ≤ Y ∧ X * Y ^ 2 ≤ M ∧
      (∑ z ∈ R, ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2) ≤
        (192 * 128 ^ 2 : ℝ) *
          (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ) ^ 2 *
          (M / (X * Y ^ 2)) ^ (1 / 3 : ℝ) *
          min (Y * sieveNorm (2 * X) N) (X * sieveNorm (2 * Y) N) *
          ∑ j, ‖coef j‖ ^ 2 := by
  let J := Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1) ×
    Fin (CanonicalQuadraticSieve.columnDyadicLength M + 1)
  let active : Finset J := Finset.univ.filter (fun j => (extractionBin R M j).Nonempty)
  let E : O → ℝ := fun z => ‖∑ j, coef j * elementCharacter (cols j) (hcols j).1.2 z‖ ^ 2
  let b : J → ℝ := fun j => ∑ z ∈ extractionBin R M j, E z
  have hactive : active.Nonempty := by
    obtain ⟨z, hz⟩ := hRne
    refine ⟨extractionLabel M z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨z, Finset.mem_filter.mpr ⟨hz, rfl⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image active b hactive
  have hjne : (extractionBin R M j).Nonempty := (Finset.mem_filter.mp hj).2
  have hbnonneg : 0 ≤ b j := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsum : (∑ z ∈ R, E z) ≤ (Fintype.card J : ℝ) * b j := by
    rw [sum_extractionBins R M E]
    calc
      _ ≤ ∑ k : J, b j := by
        apply Finset.sum_le_sum
        intro k hk
        by_cases hka : k ∈ active
        · exact hmax k hka
        · have hempty : extractionBin R M k = ∅ := by
            have hh : ¬ (extractionBin R M k).Nonempty := by
              simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hka
            exact Finset.not_nonempty_iff_eq_empty.mp hh
          simpa only [hempty, Finset.sum_empty] using hbnonneg
      _ = _ := by simp
  let X := CanonicalQuadraticSieve.divisorDyadicScale j.1.val
  let Y := CanonicalQuadraticSieve.divisorDyadicScale j.2.val
  have hX : 1 ≤ X := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hY : 1 ≤ Y := CanonicalQuadraticSieve.divisorDyadicScale_ge_one _
  have hXY : X * Y ^ 2 ≤ M := extractionBin_scale_product R M hR j hjne
  refine ⟨X, Y, hX, hY, hXY, ?_⟩
  have hb := full_element_dyadic_block_bound (extractionBin R M j)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).1) M X Y N hX hY hXY
    (fun z hz => (extractionBin_bounds R M hR j z hz).1)
    (fun z hz => (extractionBin_bounds R M hR j z hz).2)
    (fun z hz => (hR z (Finset.mem_filter.mp hz).1).2) cols hinj hcols coef
  calc
    _ ≤ (Fintype.card J : ℝ) * b j := hsum
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by
      simp only [J, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.FullNorm
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

lemma elementSieveNorm_nonneg (M N : ℝ) : 0 ≤ elementSieveNorm M N := squaredNorm_nonneg _

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.ExtractionOptimization
namespace OAI

namespace SevenEighths.CubicSieve
noncomputable section

lemma cube_scale_power (M T a : ℝ) (hT : 0 < T) (hTM : T ≤ M) (ha : (1/3 : ℝ) ≤ a) :
    (M/T)^(1/3 : ℝ) * T^a ≤ M^a := by
  have hM : 0 < M := hT.trans_le hTM
  have hbase : 1 ≤ M/T := (one_le_div hT).mpr hTM
  calc
    _ ≤ (M/T)^a * T^a := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hbase ha) (Real.rpow_nonneg hT.le _)
    _ = M^a := by
      rw [Real.div_rpow hM.le hT.le, div_mul_cancel₀ _ (Real.rpow_pos_of_pos hT a).ne']

lemma extracted_monomial_le (W U T a : ℝ) (hW : 1 ≤ W) (hU : 0 ≤ U)
    (hWT : W^2*U ≤ T) (ha : (1/2 : ℝ) ≤ a) : W*U^a ≤ T^a := by
  have hW0 : 0 ≤ W := by linarith
  have hw : W ≤ (W^2)^a := by
    rw [← Real.rpow_natCast_mul hW0]
    conv_lhs => rw [← Real.rpow_one W]
    exact Real.rpow_le_rpow_of_exponent_le hW (by norm_num; linarith)
  calc
    _ ≤ (W^2)^a * U^a := mul_le_mul_of_nonneg_right hw (Real.rpow_nonneg hU _)
    _ = (W^2*U)^a := (Real.mul_rpow (sq_nonneg _) hU).symm
    _ ≤ T^a := Real.rpow_le_rpow (mul_nonneg (sq_nonneg _) hU) hWT (by linarith)

lemma extracted_linear_le (W T : ℝ) (hW : 0 ≤ W) (hWT : W^3 ≤ T) :
    W ≤ T^(1/3 : ℝ) := by
  have hh := Real.rpow_le_rpow (pow_nonneg hW 3) hWT (by norm_num : (0 : ℝ) ≤ 1/3)
  rw [← Real.rpow_natCast_mul hW] at hh
  norm_num at hh
  exact hh

lemma extraction_selected_shape (M N W U T ξ : ℝ) (hN : 0 ≤ N)
    (hW : 1 ≤ W) (hU : 0 ≤ U) (hT : 0 < T) (hTM : T ≤ M)
    (hWT : W^2*U ≤ T) (hWcube : W^3 ≤ T) (hξ : 1 ≤ ξ) :
    (M/T)^(1/3 : ℝ) * W * (U^ξ + N + (U*N)^(2/3 : ℝ)) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hM0 : 0 < M := hT.trans_le hTM
  have hH : 0 ≤ (M/T)^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hp : (M/T)^(1/3 : ℝ)*W*U^ξ ≤ M^ξ := by
    calc
      _ = (M/T)^(1/3 : ℝ)*(W*U^ξ) := by ring
      _ ≤ (M/T)^(1/3 : ℝ)*T^ξ := mul_le_mul_of_nonneg_left
        (extracted_monomial_le W U T ξ hW hU hWT (by linarith)) hH
      _ ≤ _ := cube_scale_power M T ξ hT hTM (by linarith)
  have hn : (M/T)^(1/3 : ℝ)*W*N ≤ M^(1/3 : ℝ)*N := by
    apply mul_le_mul_of_nonneg_right _ hN
    calc
      _ ≤ (M/T)^(1/3 : ℝ)*T^(1/3 : ℝ) := mul_le_mul_of_nonneg_left
        (extracted_linear_le W T (by linarith) hWcube) hH
      _ ≤ _ := cube_scale_power M T (1/3) hT hTM le_rfl
  have hc : (M/T)^(1/3 : ℝ)*W*(U*N)^(2/3 : ℝ) ≤ (M*N)^(2/3 : ℝ) := by
    rw [Real.mul_rpow hU hN, Real.mul_rpow (hT.le.trans hTM) hN]
    calc
      _ = ((M/T)^(1/3 : ℝ)*(W*U^(2/3 : ℝ)))*N^(2/3 : ℝ) := by ring
      _ ≤ ((M/T)^(1/3 : ℝ)*T^(2/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (extracted_monomial_le W U T (2/3) hW hU hWT (by norm_num)) hH)
          (Real.rpow_nonneg hN _)
      _ ≤ _ := mul_le_mul_of_nonneg_right (cube_scale_power M T (2/3) hT hTM (by norm_num))
        (Real.rpow_nonneg hN _)
  nlinarith

theorem extraction_min_shape (M N X Y ξ : ℝ) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : 1 ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      M^ξ + M^(1/3 : ℝ)*N + (M*N)^(2/3 : ℝ) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hT : 0 < X*Y^2 := by positivity
  have hM0 : 0 < M := hT.trans_le hXY
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  by_cases hyx : Y ≤ X
  · apply (mul_le_mul_of_nonneg_left (min_le_left _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N Y X (X*Y^2) ξ hN hY hX0.le hT hXY
      (by nlinarith) (by nlinarith [mul_nonneg (sub_nonneg.mpr hyx) (sq_nonneg Y)]) hξ
  · have hxy : X ≤ Y := (lt_of_not_ge hyx).le
    apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hH).trans
    rw [← mul_assoc]
    exact extraction_selected_shape M N X Y (X*Y^2) ξ hN hX hY0.le hT hXY
      (by nlinarith [mul_nonneg (sub_nonneg.mpr hxy) (mul_nonneg hX0.le hY0.le)])
      (by nlinarith [sq_le_sq₀ hX0.le hY0.le |>.mpr hxy]) hξ

lemma cubic_cross_shape_absorb (M N ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hξ : (4/3 : ℝ) ≤ ξ) :
    (M*N)^(2/3 : ℝ) ≤ M^(1/3 : ℝ)*N + M^ξ := by
  have hM0 : 0 < M := by linarith
  have hfirst : 0 ≤ M^(1/3 : ℝ)*N := mul_nonneg (Real.rpow_nonneg hM0.le _) hN
  have hsecond : 0 ≤ M^ξ := Real.rpow_nonneg hM0.le _
  by_cases hMN : M ≤ N
  · have hN0 : 0 < N := hM0.trans_le hMN
    have hh := Real.rpow_le_rpow hM0.le hMN (by norm_num : (0 : ℝ) ≤ 1/3)
    have hm : M^(2/3 : ℝ) = M^(1/3 : ℝ)*M^(1/3 : ℝ) := by
      rw [← Real.rpow_add hM0]
      congr 1
      ring
    have hn : N^(1/3 : ℝ)*N^(2/3 : ℝ) = N := by
      rw [← Real.rpow_add hN0]
      norm_num
    apply le_trans _ (le_add_of_nonneg_right hsecond)
    rw [Real.mul_rpow hM0.le hN, hm]
    calc
      _ ≤ (M^(1/3 : ℝ)*N^(1/3 : ℝ))*N^(2/3 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hM0.le _))
          (Real.rpow_nonneg hN _)
      _ = _ := by rw [mul_assoc, hn]
  · have hNM : N ≤ M := (lt_of_not_ge hMN).le
    apply le_trans _ (le_add_of_nonneg_left hfirst)
    calc
      _ ≤ (M*M)^(2/3 : ℝ) := Real.rpow_le_rpow (mul_nonneg hM0.le hN)
        (mul_le_mul_of_nonneg_left hNM hM0.le) (by norm_num)
      _ = M^(4/3 : ℝ) := by
        rw [Real.mul_rpow hM0.le hM0.le, ← Real.rpow_add hM0]
        congr 1
        ring
      _ ≤ M^ξ := Real.rpow_le_rpow_of_exponent_le hM hξ

theorem extraction_min_two_power (M N X Y ξ : ℝ) (hM : 1 ≤ M) (hN : 0 ≤ N)
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hXY : X*Y^2 ≤ M) (hξ : (4/3 : ℝ) ≤ ξ) :
    (M/(X*Y^2))^(1/3 : ℝ) *
      min (Y*(X^ξ + N + (X*N)^(2/3 : ℝ))) (X*(Y^ξ + N + (Y*N)^(2/3 : ℝ))) ≤
      2*(M^(1/3 : ℝ)*N + M^ξ) := by
  have hh := extraction_min_shape M N X Y ξ hN hX hY hXY (by linarith)
  have hc := cubic_cross_shape_absorb M N ξ hM hN hξ
  linarith

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.Growth
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

lemma HasCubicExponent.swapped {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
        sieveNorm M N ≤ C*(M*N)^ε*(M^ξ + N + (M*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN
  rw [sieveNorm_reciprocity]
  simpa only [mul_comm, add_comm, add_left_comm, add_assoc] using hb N M hN hM

lemma HasCubicExponent.doubled {ξ : ℝ} (h : HasCubicExponent ξ)
    (ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, 0 < C ∧
      ∀ X N : ℝ, 1 ≤ X → 1 ≤ N →
        sieveNorm (2*X) N ≤ C*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ)) := by
  obtain ⟨C,hC,hb⟩ := h.swapped ε hε
  let A : ℝ := 1 + (2:ℝ)^ξ + (2:ℝ)^(2/3 : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨C*(2:ℝ)^ε*A, by positivity, ?_⟩
  intro X N hX hN
  have hX0 : 0 ≤ X := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hxξ := Real.rpow_nonneg hX0 ξ
  have hcross := Real.rpow_nonneg (mul_nonneg hX0 hN0) (2/3 : ℝ)
  have hshape : (2*X)^ξ + N + ((2*X)*N)^(2/3 : ℝ) ≤
      A*(X^ξ+N+(X*N)^(2/3 : ℝ)) := by
    rw [Real.mul_rpow (by norm_num) hX0]
    rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
    dsimp only [A]
    nlinarith [mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) ξ) hcross,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hN0,
      mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) (2/3 : ℝ)) hxξ]
  calc
    _ ≤ C*((2*X)*N)^ε*((2*X)^ξ+N+((2*X)*N)^(2/3 : ℝ)) := hb (2*X) N (by linarith) hN
    _ ≤ C*((2*X)*N)^ε*(A*(X^ξ+N+(X*N)^(2/3 : ℝ))) :=
      mul_le_mul_of_nonneg_left hshape (by positivity)
    _ = _ := by
      rw [show (2*X)*N = 2*(X*N) by ring, Real.mul_rpow (by norm_num) (mul_nonneg hX0 hN0)]
      ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.B2Growth
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem elementSieveNorm_two_power_log (ξ ε A M N : ℝ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hε : 0 ≤ ε) (hA : 0 ≤ A) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hB1 : ∀ X : ℝ, 1 ≤ X → sieveNorm (2*X) N ≤
      A*(X*N)^ε*(X^ξ + N + (X*N)^(2/3 : ℝ))) :
    elementSieveNorm M N ≤ (384*128^2 : ℝ) * A *
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
      (M*N)^ε * (M^(1/3 : ℝ)*N + M^ξ) := by
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  let R := elementRange M
  have hRne : R.Nonempty := by
    refine ⟨1, ?_⟩
    rw [mem_elementRange]
    refine ⟨one_ne_zero, ?_⟩
    simpa using hM
  have hR : ∀ z ∈ R, z ≠ 0 ∧ (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ M :=
    fun z hz => (mem_elementRange M z).mp hz
  apply FiniteSieveOperator.squared_norm_le_of_energy (elementMatrix M N)
  · positivity
  intro a
  obtain ⟨X,Y,hX,hY,hXY,he⟩ := full_element_dyadic_extraction R hRne M N hR
    (fun j : idealRange N => j.val) Subtype.val_injective
    (fun j => mem_idealRange.mp j.property) a
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hXM : X ≤ M := by nlinarith [sq_nonneg (Y-1)]
  have hYM : Y ≤ M := by nlinarith [sq_nonneg (Y-1)]
  let B := A*(M*N)^ε
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb (U : ℝ) (hU : 1 ≤ U) (hUM : U ≤ M) :
      sieveNorm (2*U) N ≤ B*(U^ξ+N+(U*N)^(2/3 : ℝ)) := by
    apply (hB1 U hU).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (mul_le_mul_of_nonneg_right hUM hN0.le) hε) hA
  have hmin : min (Y*sieveNorm (2*X) N) (X*sieveNorm (2*Y) N) ≤
      B*min (Y*(X^ξ+N+(X*N)^(2/3 : ℝ))) (X*(Y^ξ+N+(Y*N)^(2/3 : ℝ))) := by
    rw [mul_min_of_nonneg _ _ hB]
    apply min_le_min
    · convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (hb X hX hXM) hY0.le using 1; ring
    · convert (preTransparency := .instances) mul_le_mul_of_nonneg_left (hb Y hY hYM) hX0.le using 1; ring
  have hopt := extraction_min_two_power M N X Y ξ hM hN0.le hX hY hXY hξ
  have hH : 0 ≤ (M/(X*Y^2))^(1/3 : ℝ) := Real.rpow_nonneg (by positivity) _
  have hi (z : O) : (∑ j : idealRange N, a j * elementCharacter j.val (mem_idealRange.mp j.property).1.2 z) =
      ∑ j : idealRange N, cubicRow j.val z * a j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  simp_rw [hi] at he
  have hE : 0 ≤ ∑ j : idealRange N, ‖a j‖^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmin (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M/(X*Y^2))^(1/3 : ℝ) by positivity)) hE
  have hbnd := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hopt (show 0 ≤ (192*128^2 : ℝ)*
      (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*B by positivity)) hE
  have he' := he.trans hh
  rw [← Finset.sum_coe_sort] at he'
  change (∑ z : elementRange M, ‖∑ j : idealRange N, cubicRow j.val z.val * a j‖^2) ≤ _
  apply he'.trans
  convert (preTransparency := .instances) hbnd using 1 <;> dsimp only [B] <;> ring

theorem HasCubicExponent.full_element_bound {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
      elementSieveNorm M N ≤ C*(M*N)^ε*(M^(1/3 : ℝ)*N + M^ξ) := by
  obtain ⟨A,hA,hb⟩ := h.doubled (ε/2) (by positivity)
  let D : ℝ := 2 + 1/((ε/4)*Real.log 2)
  have hD : 0 < D := by
    dsimp [D]
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  refine ⟨(384*128^2 : ℝ)*A*D^2, by positivity, ?_⟩
  intro M N hM hN
  have hM0 : 0 < M := by linarith
  have hN0 : 0 < N := by linarith
  have hlog := CanonicalQuadraticSieve.columnDyadicLength_small_power (ε/4) (by positivity) M hM
  have hLP : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 ≤ D^2*M^(ε/2) := by
    have hh := pow_le_pow_left₀ (by positivity) hlog 2
    rw [mul_pow, ← Real.rpow_mul_natCast hM0.le] at hh
    have he : (ε/4)*(2:ℕ) = ε/2 := by push_cast; ring
    rw [he] at hh
    exact hh
  have hMP : M^(ε/2) ≤ (M*N)^(ε/2) := Real.rpow_le_rpow hM0.le
    (by nlinarith) (by positivity)
  have hprod : (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 * (M*N)^(ε/2) ≤
      D^2*(M*N)^ε := by
    calc
      _ ≤ (D^2*M^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right hLP (Real.rpow_nonneg (by positivity) _)
      _ ≤ (D^2*(M*N)^(ε/2))*(M*N)^(ε/2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMP (sq_nonneg _))
          (Real.rpow_nonneg (by positivity) _)
      _ = _ := by
        rw [mul_assoc, ← Real.rpow_add (mul_pos hM0 hN0)]
        congr 2
        ring
  have he := elementSieveNorm_two_power_log ξ (ε/2) A M N hξ (by positivity) hA.le hM hN
    (fun X hX => hb X N hX hN)
  calc
    _ ≤ (384*128^2 : ℝ)*A*
        (CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2 *
        (M*N)^(ε/2)*(M^(1/3 : ℝ)*N+M^ξ) := he
    _ = ((384*128^2 : ℝ)*A)*
        ((CanonicalQuadraticSieve.columnDyadicLength M + 1 : ℝ)^2*(M*N)^(ε/2))*
        (M^(1/3 : ℝ)*N+M^ξ) := by ring
    _ ≤ ((384*128^2 : ℝ)*A)*(D^2*(M*N)^ε)*(M^(1/3 : ℝ)*N+M^ξ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) (by positivity)
    _ = _ := by ring

end
end SevenEighths.CubicSieve

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.CubicSieve.CostGrowth
namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open SecondPassArithmetic EisensteinSchwartzPoisson SevenEighths.CubicDyadicDecay
noncomputable section

theorem HasCubicExponent.frequencyCost_bound_oai {ξ : ℝ} (h : HasCubicExponent ξ)
    (hξ : (4/3 : ℝ) ≤ ξ) (hξ2 : ξ ≤ 2) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1/2) :
    ∃ A : ℝ, 0 < A ∧ ∀ C ε : ℝ, 0 ≤ C → ∀ hε : 0 < ε,
      ∀ X Y : ℝ, 0 < X → 1 ≤ Y →
        frequencyCost C ε hε X Y ≤
          (X*(2/Y))*‖paperRadialFourier rowMajorant 0‖ +
          (2*C*IdealCoprimeSieveOperator.supportConstant ε hε*A) * Y^ε *
            (Y^(3*δ)*X^(-δ) * (decayConstant (1/3+δ)*(X*Y)^(2/3 : ℝ) +
              decayConstant (ξ+δ)*X^(1-ξ)*Y^(2*ξ-1))) := by
  obtain ⟨A,hA,hb⟩ := h.full_element_bound hξ δ hδ
  refine ⟨A,hA,?_⟩
  intro C ε hC hε X Y hX hY
  have hY0 : 0 < Y := by linarith
  have hs := sieve_poisson_bound (fun K => elementSieveNorm K Y) A X Y δ ξ hA.le hX hY0
    (by linarith) (by linarith) (by linarith) (by linarith)
    (fun K hK => elementSieveNorm_nonneg K Y)
    (fun K hK => by simpa only [mul_comm Y (K^(1/3 : ℝ))] using hb K Y hK hY)
  have hfac : 0 ≤ 2*C*IdealCoprimeSieveOperator.supportConstant ε hε*Y^ε := by
    have hp := (IdealCoprimeSieveOperator.supportConstant_pos ε hε).le
    positivity
  have hh := mul_le_mul_of_nonneg_left hs hfac
  have he := add_le_add_left hh ((X*(2/Y))*‖paperRadialFourier rowMajorant 0‖)
  convert (preTransparency := .instances) he using 1 <;> try dsimp only [frequencyCost, frequencyMajorant]
  all_goals ring

end
end SevenEighths.CubicSieve

end OAI
end

theorem solution : type_of% @OAI.SevenEighths.CubicSieve.HasCubicExponent.frequencyCost_bound_oai := @OAI.SevenEighths.CubicSieve.HasCubicExponent.frequencyCost_bound_oai
