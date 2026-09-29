-- Prove2me | solution 1 for MvPolynomial.squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0f163232-a02c-551f-8e8b-8367a08fb0a8

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one

namespace MvPolynomial
p2m_export "MvPolynomial" "C_0 X isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero map weightedTotalDegree_coe coeff_C constantCoeff_X coeff constantCoeff R pderiv_C aeval_X ringKrullDim_of_isNoetherianRing ext support weightedHomogeneousComponent isUnit_iff_eq_C_of_isReduced coeff_mul expand support_nonempty algHom_C C le_weightedTotalDegree coeff_weightedHomogeneousComponent monomial isWeightedHomogeneous_C coeff_zero pderiv_X_self isWeightedHomogeneous_X pderiv_X_of_ne mem_support_iff pderiv IsWeightedHomogeneous.add weightedTotalDegree weightedHomogeneousComponent_isWeightedHomogeneous IsWeightedHomogeneous isWeightedHomogeneous_one induction_on aeval"
namespace SquarefreeIsobaricProof
p2m_open "MvPolynomial"

p2m_open "MvPolynomial P2MW.S_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one.MvPolynomial Finsupp"

section Top

variable {σ K : Type*} [CommRing K] (w : σ → ℕ)

lemma weight_le_of_coeff_ne_zero {φ : MvPolynomial σ K} {d : σ →₀ ℕ} (h : coeff d φ ≠ 0) :
    weight w d ≤ weightedTotalDegree w φ :=
  le_weightedTotalDegree w (mem_support_iff.2 h)

lemma weightedTotalDegree_le_iff {φ : MvPolynomial σ K} {n : ℕ} :
    weightedTotalDegree w φ ≤ n ↔ ∀ d, coeff d φ ≠ 0 → weight w d ≤ n := by
  rw [weightedTotalDegree, Finset.sup_le_iff]
  exact ⟨fun h d hd => h d (mem_support_iff.2 hd), fun h d hd => h d (mem_support_iff.1 hd)⟩

noncomputable def top (φ : MvPolynomial σ K) : MvPolynomial σ K :=
  weightedHomogeneousComponent w (weightedTotalDegree w φ) φ

lemma coeff_top (φ : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (top w φ) = if weight w d = weightedTotalDegree w φ then coeff d φ else 0 :=
  coeff_weightedHomogeneousComponent _ _ _

lemma top_isWeightedHomogeneous (φ : MvPolynomial σ K) :
    (top w φ).IsWeightedHomogeneous w (weightedTotalDegree w φ) :=
  weightedHomogeneousComponent_isWeightedHomogeneous _ _

lemma top_ne_zero {φ : MvPolynomial σ K} (hφ : φ ≠ 0) : top w φ ≠ 0 := by
  classical
  obtain ⟨d, hd, hdeg⟩ :=
    Finset.exists_mem_eq_sup φ.support (support_nonempty.2 hφ) (fun s => weight w s)
  intro h
  have h1 := congrArg (coeff d) h
  rw [coeff_top, coeff_zero, if_pos (by rw [weightedTotalDegree]; exact hdeg.symm)] at h1
  exact (mem_support_iff.1 hd) h1

lemma weightedTotalDegree_eq_of_isWeightedHomogeneous {φ : MvPolynomial σ K} {n : ℕ}
    (h : φ.IsWeightedHomogeneous w n) (hφ : φ ≠ 0) : weightedTotalDegree w φ = n := by
  have h1 := h.weighted_total_degree hφ
  rw [weightedTotalDegree_coe w φ hφ] at h1
  exact_mod_cast h1

lemma weightedTotalDegree_mul_le (φ ψ : MvPolynomial σ K) :
    weightedTotalDegree w (φ * ψ) ≤ weightedTotalDegree w φ + weightedTotalDegree w ψ := by
  classical
  rw [weightedTotalDegree_le_iff]
  intro d hd
  rw [coeff_mul] at hd
  obtain ⟨p, hp, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  have h1 : coeff p.1 φ ≠ 0 := left_ne_zero_of_mul hne
  have h2 : coeff p.2 ψ ≠ 0 := right_ne_zero_of_mul hne
  rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, map_add]
  exact add_le_add (weight_le_of_coeff_ne_zero w h1) (weight_le_of_coeff_ne_zero w h2)

lemma coeff_mul_of_weight_eq (φ ψ : MvPolynomial σ K) {d : σ →₀ ℕ}
    (hd : weight w d = weightedTotalDegree w φ + weightedTotalDegree w ψ) :
    coeff d (φ * ψ) = coeff d (top w φ * top w ψ) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_top, coeff_top]
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h1 : coeff p.1 φ = 0
  · simp [h1]
  by_cases h2 : coeff p.2 ψ = 0
  · simp [h2]
  have hw1 := weight_le_of_coeff_ne_zero w h1
  have hw2 := weight_le_of_coeff_ne_zero w h2
  have hadd : weight w p.1 + weight w p.2 = weightedTotalDegree w φ + weightedTotalDegree w ψ := by
    rw [← map_add, hsum, hd]
  rw [if_pos (by omega), if_pos (by omega)]

lemma coeff_mul_of_weight_eq_bot (φ ψ : MvPolynomial σ K) {m₁ m₂ : ℕ}
    (hφ : ∀ a, coeff a φ ≠ 0 → m₁ ≤ weight w a) (hψ : ∀ b, coeff b ψ ≠ 0 → m₂ ≤ weight w b)
    {d : σ →₀ ℕ} (hd : weight w d = m₁ + m₂) :
    coeff d (φ * ψ) =
      coeff d (weightedHomogeneousComponent w m₁ φ * weightedHomogeneousComponent w m₂ ψ) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [coeff_weightedHomogeneousComponent, coeff_weightedHomogeneousComponent]
  have hsum := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  by_cases h1 : coeff p.1 φ = 0
  · simp [h1]
  by_cases h2 : coeff p.2 ψ = 0
  · simp [h2]
  have hw1 := hφ _ h1
  have hw2 := hψ _ h2
  have hadd : weight w p.1 + weight w p.2 = m₁ + m₂ := by rw [← map_add, hsum, hd]
  rw [if_pos (by omega), if_pos (by omega)]

variable [IsDomain K]

lemma weightedTotalDegree_mul {φ ψ : MvPolynomial σ K} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    weightedTotalDegree w (φ * ψ) = weightedTotalDegree w φ + weightedTotalDegree w ψ := by
  classical
  refine le_antisymm (weightedTotalDegree_mul_le w φ ψ) ?_
  have hne : top w φ * top w ψ ≠ 0 := mul_ne_zero (top_ne_zero w hφ) (top_ne_zero w hψ)
  obtain ⟨d, hd⟩ : ∃ d, coeff d (top w φ * top w ψ) ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (MvPolynomial.ext _ _ (by simpa using h))
  have hwd : weight w d = weightedTotalDegree w φ + weightedTotalDegree w ψ :=
    ((top_isWeightedHomogeneous w φ).mul (top_isWeightedHomogeneous w ψ)) hd
  rw [← coeff_mul_of_weight_eq w φ ψ hwd] at hd
  rw [← hwd]
  exact weight_le_of_coeff_ne_zero w hd

lemma weightedTotalDegree_pow {φ : MvPolynomial σ K} (hφ : φ ≠ 0) (n : ℕ) :
    weightedTotalDegree w (φ ^ n) = n * weightedTotalDegree w φ := by
  induction n with
  | zero =>
    rw [pow_zero, zero_mul]
    exact (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero).1
      (isWeightedHomogeneous_one _ _)
  | succ n ih =>
    rw [pow_succ, weightedTotalDegree_mul w (pow_ne_zero _ hφ) hφ, ih, Nat.succ_mul]

lemma isWeightedHomogeneous_of_mul_eq {φ ψ : MvPolynomial σ K} {n : ℕ}
    (h : (φ * ψ).IsWeightedHomogeneous w n) (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    φ.IsWeightedHomogeneous w (weightedTotalDegree w φ) := by
  classical
  by_contra hn
  have hn' : ∃ d₀, coeff d₀ φ ≠ 0 ∧ weight w d₀ < weightedTotalDegree w φ := by
    by_contra h'
    push Not at h'
    exact hn fun d hd => le_antisymm (weight_le_of_coeff_ne_zero w hd) (h' d hd)
  obtain ⟨d₀, hd₀, hlt⟩ := hn'
  obtain ⟨d₁, hd₁, hmin₁⟩ :=
    Finset.exists_min_image φ.support (weight w) (support_nonempty.2 hφ)
  obtain ⟨d₂, hd₂, hmin₂⟩ :=
    Finset.exists_min_image ψ.support (weight w) (support_nonempty.2 hψ)
  set m₁ := weight w d₁
  set m₂ := weight w d₂
  have hφ' : ∀ a, coeff a φ ≠ 0 → m₁ ≤ weight w a := fun a ha => hmin₁ a (mem_support_iff.2 ha)
  have hψ' : ∀ b, coeff b ψ ≠ 0 → m₂ ≤ weight w b := fun b hb => hmin₂ b (mem_support_iff.2 hb)
  have hm₁ : m₁ < weightedTotalDegree w φ :=
    lt_of_le_of_lt (hmin₁ d₀ (mem_support_iff.2 hd₀)) hlt
  have hm₂ : m₂ ≤ weightedTotalDegree w ψ := weight_le_of_coeff_ne_zero w (mem_support_iff.1 hd₂)
  have hc₁ : weightedHomogeneousComponent w m₁ φ ≠ 0 := by
    intro h0
    have := congrArg (coeff d₁) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact (mem_support_iff.1 hd₁) this
  have hc₂ : weightedHomogeneousComponent w m₂ ψ ≠ 0 := by
    intro h0
    have := congrArg (coeff d₂) h0
    rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
    exact (mem_support_iff.1 hd₂) this
  have hne : weightedHomogeneousComponent w m₁ φ * weightedHomogeneousComponent w m₂ ψ ≠ 0 :=
    mul_ne_zero hc₁ hc₂
  obtain ⟨d, hd⟩ : ∃ d, coeff d
      (weightedHomogeneousComponent w m₁ φ * weightedHomogeneousComponent w m₂ ψ) ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hne (MvPolynomial.ext _ _ (by simpa using h'))
  have hwd : weight w d = m₁ + m₂ :=
    ((weightedHomogeneousComponent_isWeightedHomogeneous (w := w) (n := m₁) (φ := φ)).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) (n := m₂) (φ := ψ))) hd
  rw [← coeff_mul_of_weight_eq_bot w φ ψ hφ' hψ' hwd] at hd
  have h1 : weight w d = n := h hd
  have h2 : weightedTotalDegree w (φ * ψ) = n :=
    weightedTotalDegree_eq_of_isWeightedHomogeneous w h (mul_ne_zero hφ hψ)
  rw [weightedTotalDegree_mul w hφ hψ] at h2
  omega

end Top

section Fin2

variable {K : Type*} [Field K]

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)

lemma weight_fin_two (d : Fin 2 →₀ ℕ) : weight 𝔴 d = 4 * d 0 + 6 * d 1 := by
  rw [weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

lemma weight_eq_zero_iff (d : Fin 2 →₀ ℕ) : weight 𝔴 d = 0 ↔ d = 0 := by
  constructor
  · intro h
    rw [weight_fin_two] at h
    ext i
    fin_cases i <;> simp <;> omega
  · rintro rfl
    simp

lemma weight_ne_two (d : Fin 2 →₀ ℕ) : weight 𝔴 d ≠ 2 := by
  rw [weight_fin_two]; omega

lemma eq_C_of_weightedTotalDegree_eq_zero {φ : MvPolynomial (Fin 2) K}
    (h : weightedTotalDegree 𝔴 φ = 0) : φ = C (constantCoeff φ) := by
  classical
  have h0 : φ.IsWeightedHomogeneous 𝔴 0 :=
    (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero).2 h
  ext d
  rw [coeff_C]
  split_ifs with hd
  · rw [← hd]; rfl
  · apply h0.coeff_eq_zero
    rw [Ne, weight_eq_zero_iff]
    exact Ne.symm hd

lemma isWeightedHomogeneous_int_iff {φ : MvPolynomial (Fin 2) K} {n : ℕ} :
    φ.IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) (n : ℤ) ↔ φ.IsWeightedHomogeneous 𝔴 n := by
  have hw : ∀ d : Fin 2 →₀ ℕ, weight (fun i => (𝔴 i : ℤ)) d = ((weight 𝔴 d : ℕ) : ℤ) := by
    intro d
    rw [weight_apply, weight_apply, Finsupp.sum_fintype _ _ (by simp),
      Finsupp.sum_fintype _ _ (by simp)]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
    push_cast
    ring
  constructor
  · intro h d hd
    have := h hd
    rw [hw] at this
    exact_mod_cast this
  · intro h d hd
    rw [hw, h hd]

noncomputable def D : Derivation K (MvPolynomial (Fin 2) K) (MvPolynomial (Fin 2) K) :=
  (-4 * X 1 : MvPolynomial (Fin 2) K) • pderiv 0 + (-6 * X 0 ^ 2 : MvPolynomial (Fin 2) K) • pderiv 1

lemma D_apply (Φ : MvPolynomial (Fin 2) K) :
    D Φ = (-4 * X 1) * pderiv 0 Φ + (-6 * X 0 ^ 2) * pderiv 1 Φ := by
  simp [D, smul_eq_mul]

lemma D_X0 : D (X 0 : MvPolynomial (Fin 2) K) = -4 * X 1 := by
  rw [D_apply, pderiv_X_self, pderiv_X_of_ne (by decide)]; ring

lemma D_X1 : D (X 1 : MvPolynomial (Fin 2) K) = -6 * X 0 ^ 2 := by
  rw [D_apply, pderiv_X_self, pderiv_X_of_ne (by decide)]; ring

lemma isWeightedHomogeneous_D {Φ : MvPolynomial (Fin 2) K} {k : ℕ}
    (h : Φ.IsWeightedHomogeneous 𝔴 k) : (D Φ).IsWeightedHomogeneous 𝔴 (k + 2) := by
  rw [← isWeightedHomogeneous_int_iff] at h ⊢
  have h0 : (pderiv 0 Φ).IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) ((k : ℤ) - 4) :=
    h.pderiv (by simp)
  have h1 : (pderiv 1 Φ).IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) ((k : ℤ) - 6) :=
    h.pderiv (by simp)
  have hX0 : (X 0 : MvPolynomial (Fin 2) K).IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) 4 := by
    simpa using isWeightedHomogeneous_X K (fun i => (𝔴 i : ℤ)) 0
  have hX1 : (X 1 : MvPolynomial (Fin 2) K).IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) 6 := by
    simpa using isWeightedHomogeneous_X K (fun i => (𝔴 i : ℤ)) 1
  have hc4 : (-4 : MvPolynomial (Fin 2) K).IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) 0 := by
    have h__af := (isWeightedHomogeneous_C (fun i => (𝔴 i : ℤ)) (-4 : K))
    simp at h__af
    exact h__af
  have hc6 : (-6 : MvPolynomial (Fin 2) K).IsWeightedHomogeneous (fun i => (𝔴 i : ℤ)) 0 := by
    have h__af := (isWeightedHomogeneous_C (fun i => (𝔴 i : ℤ)) (-6 : K))
    simp at h__af
    exact h__af
  rw [D_apply]
  have e1 : ((k + 2 : ℕ) : ℤ) = (0 + 6) + ((k : ℤ) - 4) := by push_cast; ring
  have e2 : ((k + 2 : ℕ) : ℤ) = (0 + (4 + 4)) + ((k : ℤ) - 6) := by push_cast; ring
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [e1]; exact (hc4.mul hX1).mul h0
  · rw [e2, pow_two]; exact (hc6.mul (hX0.mul hX0)).mul h1

lemma euler {Φ : MvPolynomial (Fin 2) K} {k : ℕ} (h : Φ.IsWeightedHomogeneous 𝔴 k) :
    4 * (X 0 * pderiv 0 Φ) + 6 * (X 1 * pderiv 1 Φ) = (k : MvPolynomial (Fin 2) K) * Φ := by
  have := h.sum_weight_X_mul_pderiv
  simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, nsmul_eq_mul,
    Nat.cast_ofNat] using this

end Fin2

section Compat

variable {K : Type*} [Field K] {P Q R : PowerSeries K}

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)
local notation "ε" => MvPolynomial.aeval (R := K) (![Q, R] : Fin 2 → PowerSeries K)
local notation "θ" F => (PowerSeries.X : PowerSeries K) * PowerSeries.derivative K F

lemma theta_mul (F G : PowerSeries K) : (θ (F * G)) = F * (θ G) + G * (θ F) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

lemma theta_algebraMap (a : K) : (θ (algebraMap K (PowerSeries K) a)) = 0 := by
  rw [Derivation.map_algebraMap, mul_zero]

lemma compat (hQ : 3 * (θ Q) = P * Q - R) (hR : 2 * (θ R) = P * R - Q ^ 2)
    (Φ : MvPolynomial (Fin 2) K) :
    12 * (θ (ε Φ)) - ε (D Φ) = P * ε (4 * (X 0 * pderiv 0 Φ) + 6 * (X 1 * pderiv 1 Φ)) := by
  have εX0 : ε (X 0) = Q := by rw [aeval_X]; rfl
  have εX1 : ε (X 1) = R := by rw [aeval_X]; rfl

  suffices H : 12 * (θ (ε Φ)) - (-4 * R * ε (pderiv 0 Φ) + -6 * Q ^ 2 * ε (pderiv 1 Φ)) =
      P * (4 * (Q * ε (pderiv 0 Φ)) + 6 * (R * ε (pderiv 1 Φ))) by
    rw [D_apply]
    simp only [map_add, map_mul, map_neg, map_pow, εX0, εX1, map_ofNat]
    exact H
  induction Φ using MvPolynomial.induction_on with
  | C a =>
    rw [pderiv_C, pderiv_C, algHom_C, theta_algebraMap]
    simp
  | add p q hp hq =>
    simp only [map_add, mul_add] at hp hq ⊢
    linear_combination hp + hq
  | mul_X p n ih =>
    fin_cases n
    · have e0 : pderiv 0 (p * X (0 : Fin 2)) = pderiv 0 p * X 0 + p := by
        rw [Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one, mul_comm (X 0),
          add_comm]
      have e1 : pderiv 1 (p * X (0 : Fin 2)) = pderiv 1 p * X 0 := by
        rw [Derivation.leibniz, pderiv_X_of_ne (by decide), smul_zero, zero_add, smul_eq_mul,
          mul_comm]
      simp only [Fin.zero_eta]
      rw [e0, e1]
      simp only [map_mul, map_add, εX0]
      rw [theta_mul]
      linear_combination Q * ih + 4 * (ε p) * hQ
    · have e0 : pderiv 0 (p * X (1 : Fin 2)) = pderiv 0 p * X 1 := by
        rw [Derivation.leibniz, pderiv_X_of_ne (by decide), smul_zero, zero_add, smul_eq_mul,
          mul_comm]
      have e1 : pderiv 1 (p * X (1 : Fin 2)) = pderiv 1 p * X 1 + p := by
        rw [Derivation.leibniz, pderiv_X_self, smul_eq_mul, smul_eq_mul, mul_one, mul_comm (X 1),
          add_comm]
      simp only [Fin.mk_one]
      rw [e0, e1]
      simp only [map_mul, map_add, εX1]
      rw [theta_mul]
      linear_combination R * ih + 6 * (ε p) * hR

lemma aeval_D (hQ : 3 * (θ Q) = P * Q - R) (hR : 2 * (θ R) = P * R - Q ^ 2)
    {Φ : MvPolynomial (Fin 2) K} {k : ℕ} (h : Φ.IsWeightedHomogeneous 𝔴 k) :
    ε (D Φ) = 12 * (θ (ε Φ)) - (k : PowerSeries K) * P * ε Φ := by
  have h1 := compat hQ hR Φ
  rw [euler h, map_mul, map_natCast] at h1
  linear_combination -h1

end Compat

section Kernel

variable {K : Type*} [Field K] {Q R : PowerSeries K}

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)
local notation "ε" => MvPolynomial.aeval (R := K) (![Q, R] : Fin 2 → PowerSeries K)

lemma ker_not_isMaximal (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2) :
    ¬ (RingHom.ker (ε).toRingHom).IsMaximal := by
  intro hmax
  have hx : (X 0 ^ 3 - X 1 ^ 2 : MvPolynomial (Fin 2) K) ∉ RingHom.ker (ε).toRingHom := by
    rw [RingHom.mem_ker]
    change ε (X 0 ^ 3 - X 1 ^ 2) ≠ 0
    rw [map_sub, map_pow, map_pow, aeval_X, aeval_X]
    simpa [sub_eq_zero] using hQR
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hx
  have hi' : ε i = 0 := by rwa [RingHom.mem_ker] at hi
  have h1 := congrArg (fun p => PowerSeries.constantCoeff (ε p)) hyi
  simp only [map_add, map_mul, map_sub, map_pow, hi', map_one, add_zero] at h1
  rw [aeval_X, aeval_X] at h1
  simp [hQ0, hR0] at h1

lemma eq_zero_of_isWeightedHomogeneous_of_aeval_eq_zero (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    {A : MvPolynomial (Fin 2) K} {N : ℕ} (hN : 0 < N) (hA : A.IsWeightedHomogeneous 𝔴 N)
    (hA1 : ε A = 1)
    {G : MvPolynomial (Fin 2) K} {k : ℕ} (hG : G.IsWeightedHomogeneous 𝔴 k)
    (hG0 : ε G = 0) : G = 0 := by
  classical
  by_contra hGne
  set 𝔭 := RingHom.ker (ε).toRingHom with h𝔭
  have h𝔭p : 𝔭.IsPrime := RingHom.ker_isPrime _
  have hG𝔭 : G ∈ 𝔭 := by rw [RingHom.mem_ker]; exact hG0
  have h𝔭ne : 𝔭 ≠ ⊥ := fun h => hGne (by rwa [h, Ideal.mem_bot] at hG𝔭)

  obtain ⟨π, hπ𝔭, hπ⟩ := h𝔭p.exists_mem_prime_of_ne_bot h𝔭ne
  have hsp : (Ideal.span {π}).IsPrime := (Ideal.span_singleton_prime hπ.ne_zero).2 hπ
  have hle : Ideal.span {π} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hπ𝔭

  have heq : Ideal.span {π} = 𝔭 := by
    by_contra hne
    have hlt : Ideal.span {π} < 𝔭 := lt_of_le_of_ne hle hne
    obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal _ h𝔭p.ne_top
    have hkM' : 𝔭 < M :=
      lt_of_le_of_ne hkM (fun h => ker_not_isMaximal hQ0 hR0 hQR (h𝔭 ▸ h ▸ hM))
    have hbot : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < Ideal.span {π} :=
      bot_lt_iff_ne_bot.2 (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hπ.ne_zero)
    let c : Fin 4 → PrimeSpectrum (MvPolynomial (Fin 2) K) :=
      ![⟨⊥, Ideal.isPrime_bot⟩, ⟨Ideal.span {π}, hsp⟩, ⟨𝔭, h𝔭p⟩, ⟨M, hM.isPrime⟩]
    have hc : StrictMono c := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hbot
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hlt
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hkM'
    have h3 := Order.LTSeries.length_le_krullDim (LTSeries.mk 3 c hc)
    change ((3 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 2) K) at h3
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h3
    have : ¬ ((3 : ℕ) : WithBot ℕ∞) ≤ (2 : ℕ) := by decide
    exact this (by exact_mod_cast h3)

  have hA1𝔭 : A - 1 ∈ 𝔭 := by
    rw [RingHom.mem_ker]
    change ε (A - 1) = 0
    rw [map_sub, hA1, map_one, sub_self]
  rw [← heq, Ideal.mem_span_singleton] at hA1𝔭 hG𝔭
  obtain ⟨τ, hτ⟩ := hA1𝔭
  obtain ⟨ρ, hρ⟩ := hG𝔭
  have hcA : constantCoeff A = 0 := by
    show coeff 0 A = 0
    exact hA.coeff_eq_zero 0 (by rw [(weight_eq_zero_iff 0).2 rfl]; exact hN.ne)
  have hcπ : constantCoeff π ≠ 0 := by
    intro h0
    have := congrArg constantCoeff hτ
    rw [map_sub, map_one, hcA, map_mul, h0, zero_mul] at this
    norm_num at this

  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hρ0 : ρ ≠ 0 := by rintro rfl; rw [mul_zero] at hρ; exact hGne hρ
  have hπiso : π.IsWeightedHomogeneous 𝔴 (weightedTotalDegree 𝔴 π) :=
    isWeightedHomogeneous_of_mul_eq 𝔴 (hρ ▸ hG) hπ0 hρ0
  have hdeg : weightedTotalDegree 𝔴 π = 0 := by
    have := hπiso (d := 0) hcπ
    rw [(weight_eq_zero_iff 0).2 rfl] at this
    exact this.symm
  have hπC := eq_C_of_weightedTotalDegree_eq_zero hdeg
  exact hπ.not_unit (hπC ▸ (isUnit_iff_eq_C_of_isReduced).2 ⟨_, isUnit_iff_ne_zero.2 hcπ, rfl⟩)

end Kernel

section Main

variable {K : Type*} [Field K]

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)

theorem main {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (h5 : 5 ≤ ℓ)
    {P Q R : PowerSeries K}
    (hP0 : PowerSeries.constantCoeff P = 1) (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    (hP : 12 * (PowerSeries.X * PowerSeries.derivative K P) = P ^ 2 - Q)
    (hQ : 3 * (PowerSeries.X * PowerSeries.derivative K Q) = P * Q - R)
    (hR : 2 * (PowerSeries.X * PowerSeries.derivative K R) = P * R - Q ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (ℓ - 1))
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    Squarefree A := by
  classical
  set ε := MvPolynomial.aeval (R := K) (![Q, R] : Fin 2 → PowerSeries K) with hε
  have hℓp : ℓ.Prime := Fact.out
  have hℓ1 : 0 < ℓ - 1 := by omega
  have hA0 : A ≠ 0 := by rintro rfl; rw [map_zero] at hA1; exact zero_ne_one hA1

  have hℓK : ((ℓ : ℕ) : PowerSeries K) = 0 := by
    rw [← map_natCast (algebraMap K (PowerSeries K)), CharP.cast_eq_zero, map_zero]
  have hcast1 : ((ℓ - 1 : ℕ) : PowerSeries K) = -1 := by
    rw [Nat.cast_sub hℓp.one_le, hℓK, Nat.cast_one, zero_sub]
  have hcast2 : ((ℓ - 1 + 2 : ℕ) : PowerSeries K) = 1 := by
    rw [show ℓ - 1 + 2 = ℓ + 1 by omega, Nat.cast_add, hℓK, Nat.cast_one, zero_add]
  have hneK : ∀ j : ℕ, 0 < j → j < ℓ → ((j : ℕ) : K) ≠ 0 := fun j hj hjℓ h => by
    rw [CharP.cast_eq_zero_iff K ℓ] at h
    exact Nat.not_dvd_of_pos_of_lt hj hjℓ h

  have hεDA : ε (D A) = P := by
    rw [hε, aeval_D hQ hR hA, hA1, hcast1, Derivation.map_one_eq_zero]; ring
  have hDAiso : (D A).IsWeightedHomogeneous 𝔴 (ℓ - 1 + 2) := isWeightedHomogeneous_D hA
  have hGiso : (D (D A) + X 0 * A).IsWeightedHomogeneous 𝔴 (ℓ - 1 + 2 + 2) := by
    refine (isWeightedHomogeneous_D hDAiso).add ?_
    have h1 := (isWeightedHomogeneous_X K 𝔴 0).mul hA
    have e : 𝔴 0 + (ℓ - 1) = ℓ - 1 + 2 + 2 := by simp; omega
    rwa [e] at h1
  have hεG : ε (D (D A) + X 0 * A) = 0 := by
    rw [map_add, map_mul, hε, aeval_D hQ hR hDAiso, aeval_X, ← hε, hεDA, hA1, hcast2]
    simp only [Matrix.cons_val_zero]
    linear_combination hP
  have hG : D (D A) + X 0 * A = 0 :=
    eq_zero_of_isWeightedHomogeneous_of_aeval_eq_zero hQ0 hR0 hQR hℓ1 hA hA1 hGiso hεG

  intro x hx
  by_contra hxu
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_mul, zero_dvd_iff] at hx
    exact hA0 hx
  obtain ⟨π, hπirr, hπx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
  have hππ : π * π ∣ A := (mul_dvd_mul hπx hπx).trans hx
  have hπ0 : π ≠ 0 := hπirr.ne_zero
  have hprime : Prime π := hπirr.prime
  obtain ⟨n, Γ, hnC, hAeq⟩ := WfDvdMonoid.max_power_factor hA0 hπirr
  have hn2 : 2 ≤ n := by
    by_contra hn
    interval_cases n
    · rw [pow_zero, one_mul] at hAeq
      exact hnC ((dvd_mul_right π π).trans (hAeq ▸ hππ))
    · rw [pow_one] at hAeq
      rw [hAeq] at hππ
      exact hnC ((mul_dvd_mul_iff_left hπ0).1 hππ)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have hC0 : Γ ≠ 0 := by rintro rfl; rw [mul_zero] at hAeq; exact hA0 hAeq
  have hA' : π * (π ^ (m + 1) * Γ) = A := by rw [hAeq]; ring

  set d := weightedTotalDegree 𝔴 π with hd
  have hπiso : π.IsWeightedHomogeneous 𝔴 d := by
    have h1 : (π * (π ^ (m + 1) * Γ)).IsWeightedHomogeneous 𝔴 (ℓ - 1) := by rwa [hA']
    exact isWeightedHomogeneous_of_mul_eq 𝔴 h1 hπ0 (mul_ne_zero (pow_ne_zero _ hπ0) hC0)
  have hdegA : weightedTotalDegree 𝔴 A = ℓ - 1 :=
    weightedTotalDegree_eq_of_isWeightedHomogeneous 𝔴 hA hA0
  have hdegsum : (m + 1 + 1) * d + weightedTotalDegree 𝔴 Γ = ℓ - 1 := by
    rw [← hdegA, hAeq, weightedTotalDegree_mul 𝔴 (pow_ne_zero _ hπ0) hC0,
      weightedTotalDegree_pow 𝔴 hπ0]
  have hd0 : 0 < d := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    have hπC := eq_C_of_weightedTotalDegree_eq_zero h0
    by_cases hc : constantCoeff π = 0
    · exact hπ0 (by rw [hπC, hc, C_0])
    · exact hπirr.not_isUnit
        (hπC ▸ (isUnit_iff_eq_C_of_isReduced).2 ⟨_, isUnit_iff_ne_zero.2 hc, rfl⟩)
  have hm2 : m + 1 + 1 < ℓ := by
    have := Nat.le_mul_of_pos_right (m + 1 + 1) hd0
    omega
  have hdℓ : d < ℓ := by
    have := Nat.le_mul_of_pos_left d (show 0 < m + 1 + 1 by omega)
    omega

  have hDpow : ∀ j : ℕ, D (π ^ (j + 1)) = ((j + 1 : ℕ) : MvPolynomial (Fin 2) K) * π ^ j * D π := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Derivation.leibniz, ih, smul_eq_mul, smul_eq_mul]
      push_cast
      ring
  have hDN : D ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) = 0 := Derivation.map_natCast _ _
  have hDA : D A = π ^ (m + 1) * (π * D Γ + ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * Γ * D π) := by
    rw [hAeq, Derivation.leibniz, smul_eq_mul, smul_eq_mul, hDpow]
    push_cast
    ring
  have hDDA : D (D A) = π ^ m * (π ^ 2 * D (D Γ) + 2 * ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * π * D π * D Γ +
      ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * Γ * π * D (D π) + ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * ((m + 1 : ℕ) : MvPolynomial (Fin 2) K) * Γ * D π ^ 2) := by
    rw [hDA, Derivation.leibniz, Derivation.map_add, Derivation.leibniz, Derivation.leibniz,
      Derivation.leibniz, hDN, hDpow]
    simp only [smul_eq_mul]
    push_cast
    ring
  have hkey : π ^ m * (π * (π * D (D Γ) + 2 * ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * D π * D Γ + ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * Γ * D (D π) + X 0 * π * Γ) +
      ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * ((m + 1 : ℕ) : MvPolynomial (Fin 2) K) * Γ * D π ^ 2) = 0 := by
    rw [← hG, hDDA, hAeq]; push_cast; ring
  have hkey' := (mul_eq_zero.1 hkey).resolve_left (pow_ne_zero _ hπ0)
  have hdvd : π ∣ ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * ((m + 1 : ℕ) : MvPolynomial (Fin 2) K) * (Γ * D π ^ 2) := by
    refine ⟨-(π * D (D Γ) + 2 * ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * D π * D Γ + ((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * Γ * D (D π) + X 0 * π * Γ), ?_⟩
    linear_combination hkey'
  have hunit : IsUnit (((m + 1 + 1 : ℕ) : MvPolynomial (Fin 2) K) * ((m + 1 : ℕ) : MvPolynomial (Fin 2) K)) := by
    rw [← map_natCast (C : K →+* MvPolynomial (Fin 2) K),
      ← map_natCast (C : K →+* MvPolynomial (Fin 2) K), ← map_mul]
    exact IsUnit.map C (isUnit_iff_ne_zero.2 (mul_ne_zero (hneK _ (by omega) hm2)
      (hneK _ (by omega) (by omega))))
  rw [IsUnit.dvd_mul_left hunit] at hdvd
  have hπD : π ∣ D π := by
    rcases hprime.dvd_or_dvd hdvd with h | h
    · exact absurd h hnC
    · exact hprime.dvd_of_dvd_pow h

  have hDπiso : (D π).IsWeightedHomogeneous 𝔴 (d + 2) := isWeightedHomogeneous_D hπiso
  have hDπ0 : D π = 0 := by
    by_contra hne
    obtain ⟨η, hη⟩ := hπD
    have hη0 : η ≠ 0 := by rintro rfl; rw [mul_zero] at hη; exact hne hη
    have h1 : weightedTotalDegree 𝔴 (D π) = d + 2 :=
      weightedTotalDegree_eq_of_isWeightedHomogeneous 𝔴 hDπiso hne
    rw [hη, weightedTotalDegree_mul 𝔴 hπ0 hη0] at h1
    obtain ⟨δ, -, hδw⟩ :=
      Finset.exists_mem_eq_sup η.support (support_nonempty.2 hη0) (fun s => weight 𝔴 s)
    have h3 : weight 𝔴 δ = weightedTotalDegree 𝔴 η := by rw [weightedTotalDegree]; exact hδw.symm
    exact weight_ne_two δ (by omega)

  have hc := aeval_D hQ hR hπiso
  rw [hDπ0, map_zero] at hc
  have hπA : π ∣ A := ⟨_, hA'.symm⟩
  have hu : IsUnit (PowerSeries.constantCoeff (ε π)) := by
    refine (isUnit_of_dvd_one ?_).map _
    rw [← hA1]
    exact map_dvd ε hπA
  have hc0 := congrArg PowerSeries.constantCoeff hc
  simp only [map_zero, map_sub, map_mul, map_natCast, map_ofNat, PowerSeries.constantCoeff_X,
    zero_mul, mul_zero, hP0, mul_one, zero_sub, zero_eq_neg] at hc0
  rcases mul_eq_zero.1 hc0 with h | h
  · exact hneK d hd0 hdℓ h
  · exact hu.ne_zero h

end Main

end MvPolynomial.SquarefreeIsobaricProof

theorem solution
    {K : Type*} [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (h5 : 5 ≤ ℓ)
    {P Q R : PowerSeries K}
    (hP0 : PowerSeries.constantCoeff P = 1) (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    (hP : 12 * (PowerSeries.X * PowerSeries.derivative K P) = P ^ 2 - Q)
    (hQ : 3 * (PowerSeries.X * PowerSeries.derivative K Q) = P * Q - R)
    (hR : 2 * (PowerSeries.X * PowerSeries.derivative K R) = P * R - Q ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) (ℓ - 1))
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    Squarefree A :=
  MvPolynomial.SquarefreeIsobaricProof.main h5 hP0 hQ0 hR0 hQR hP hQ hR hA hA1

end S_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one
end P2MW
export P2MW.S_MvPolynomial_squarefree_of_isWeightedHomogeneous_of_aeval_eq_one (solution)
