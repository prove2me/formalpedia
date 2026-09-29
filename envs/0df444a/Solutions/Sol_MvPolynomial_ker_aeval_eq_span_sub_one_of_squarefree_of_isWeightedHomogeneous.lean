-- Prove2me | solution 1 for MvPolynomial.ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d9d3e0c7-f5a5-5a71-b5f8-7a240bed2b32

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous

namespace MvPolynomial
p2m_export "MvPolynomial" "X isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero weightedTotalDegree_zero weightedTotalDegree_coe coeff_C coeff constantCoeff R coeff_monomial aeval_X ringKrullDim_of_isNoetherianRing ext induction_on' degrees support coeff_C_mul prod_X_pow_eq_monomial weightedHomogeneousComponent isUnit_iff_eq_C_of_isReduced coeff_mul aeval_monomial support_nonempty algebraMap_eq C le_weightedTotalDegree coeff_weightedHomogeneousComponent monomial isWeightedHomogeneous_C coeff_zero mem_support_iff C_1 coeff_sub C_mul_monomial weightedTotalDegree weightedHomogeneousComponent_isWeightedHomogeneous coeff_add IsWeightedHomogeneous coeff_one aeval C_inj"
namespace KerAevalIsobaricProof
p2m_open "MvPolynomial"

p2m_open "MvPolynomial P2MW.S_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous.MvPolynomial Finsupp"

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

lemma top_eq_self_of_isWeightedHomogeneous {φ : MvPolynomial σ K} {n : ℕ}
    (h : φ.IsWeightedHomogeneous w n) (hφ : φ ≠ 0) : top w φ = φ := by
  rw [top, weightedTotalDegree_eq_of_isWeightedHomogeneous w h hφ]
  exact h.weightedHomogeneousComponent_same

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

lemma top_mul {φ ψ : MvPolynomial σ K} (hφ : φ ≠ 0) (hψ : ψ ≠ 0) :
    top w (φ * ψ) = top w φ * top w ψ := by
  classical
  ext d
  rw [coeff_top, weightedTotalDegree_mul w hφ hψ]
  split_ifs with h
  · exact coeff_mul_of_weight_eq w φ ψ h
  · exact (((top_isWeightedHomogeneous w φ).mul (top_isWeightedHomogeneous w ψ)).coeff_eq_zero d
      h).symm

end Top

section Rot

variable {σ K : Type*} [CommRing K] (w : σ → ℕ) (ζ : K)

noncomputable def rot : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  aeval fun i => C (ζ ^ w i) * X i

lemma rot_monomial (d : σ →₀ ℕ) (c : K) :
    rot w ζ (monomial d c) = monomial d (c * ζ ^ weight w d) := by
  classical
  rw [rot, aeval_monomial, algebraMap_eq]
  have h1 : (d.prod fun i e => (C (ζ ^ w i) * X i : MvPolynomial σ K) ^ e) =
      C (ζ ^ weight w d) * monomial d 1 := by
    simp_rw [mul_pow, Finsupp.prod_mul]
    rw [← prod_X_pow_eq_monomial, Finsupp.prod, Finsupp.prod]
    congr 1
    simp_rw [← map_pow]
    rw [← map_prod]
    congr 1
    rw [weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_mul, smul_eq_mul, mul_comm]
  rw [h1, ← mul_assoc, ← map_mul, C_mul_monomial, mul_one]

lemma coeff_rot (φ : MvPolynomial σ K) (d : σ →₀ ℕ) :
    coeff d (rot w ζ φ) = ζ ^ weight w d * coeff d φ := by
  classical
  induction φ using MvPolynomial.induction_on' with
  | monomial s a =>
    rw [rot_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · rw [h, mul_comm]
    · rw [mul_zero]
  | add p q hp hq => rw [map_add, coeff_add, coeff_add, hp, hq, mul_add]

lemma rot_of_isWeightedHomogeneous {φ : MvPolynomial σ K} {n : ℕ}
    (h : φ.IsWeightedHomogeneous w n) : rot w ζ φ = C (ζ ^ n) * φ := by
  classical
  ext d
  rw [coeff_rot, coeff_C_mul]
  by_cases hd : coeff d φ = 0
  · simp [hd]
  · rw [h hd]

lemma constantCoeff_rot (φ : MvPolynomial σ K) :
    constantCoeff (rot w ζ φ) = constantCoeff φ := by
  show coeff 0 (rot w ζ φ) = coeff 0 φ
  rw [coeff_rot, map_zero, pow_zero, one_mul]

variable [IsDomain K]

lemma support_rot (hζ : ζ ≠ 0) (φ : MvPolynomial σ K) : (rot w ζ φ).support = φ.support := by
  classical
  ext d
  rw [mem_support_iff, mem_support_iff, coeff_rot, mul_ne_zero_iff]
  exact ⟨fun h => h.2, fun h => ⟨pow_ne_zero _ hζ, h⟩⟩

lemma weightedTotalDegree_rot (hζ : ζ ≠ 0) (φ : MvPolynomial σ K) :
    weightedTotalDegree w (rot w ζ φ) = weightedTotalDegree w φ := by
  simp only [weightedTotalDegree, support_rot w ζ hζ]

lemma top_rot (hζ : ζ ≠ 0) (φ : MvPolynomial σ K) :
    top w (rot w ζ φ) = C (ζ ^ weightedTotalDegree w φ) * top w φ := by
  classical
  ext d
  rw [coeff_top, weightedTotalDegree_rot w ζ hζ, coeff_C_mul, coeff_top, coeff_rot]
  split_ifs with h
  · rw [h]
  · rw [mul_zero]

end Rot

section Irred

variable {K : Type*} [Field K]

local notation "𝔴" => (![4, 6] : Fin 2 → ℕ)

lemma weight_eq_zero_iff (d : Fin 2 →₀ ℕ) : weight 𝔴 d = 0 ↔ d = 0 := by
  constructor
  · intro h
    rw [weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul] at h
    ext i
    fin_cases i <;> simp <;> omega
  · rintro rfl
    simp

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

theorem irreducible_sub_one {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    {A : MvPolynomial (Fin 2) K} (hA : A.IsWeightedHomogeneous 𝔴 N) (hsq : Squarefree A)
    (hA0 : A ≠ 0) : Irreducible (A - 1) := by
  classical
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN.ne'

  have hcA : constantCoeff A = 0 := by
    show coeff 0 A = 0
    exact hA.coeff_eq_zero 0 (by rw [(weight_eq_zero_iff 0).2 rfl]; exact hN.ne)
  have hcA1 : constantCoeff (A - 1) = -1 := by rw [map_sub, map_one, hcA, zero_sub]
  have hA10 : A - 1 ≠ 0 := by
    intro h; rw [h, map_zero] at hcA1; norm_num at hcA1

  have hdegA : weightedTotalDegree 𝔴 A = N := weightedTotalDegree_eq_of_isWeightedHomogeneous _ hA hA0
  have hdegA1 : weightedTotalDegree 𝔴 (A - 1) = N := by
    refine le_antisymm ?_ ?_
    · rw [weightedTotalDegree_le_iff]
      intro d hd
      rw [coeff_sub, coeff_one] at hd
      by_cases hd0 : 0 = d
      · rw [← hd0, (weight_eq_zero_iff 0).2 rfl]; exact Nat.zero_le _
      · rw [if_neg hd0, sub_zero] at hd
        exact (hA hd).le
    · obtain ⟨d, hd⟩ : ∃ d, coeff d A ≠ 0 := by
        by_contra h
        push Not at h
        exact hA0 (MvPolynomial.ext _ _ (by simpa using h))
      have hwd : weight 𝔴 d = N := hA hd
      have hd0 : (0 : Fin 2 →₀ ℕ) ≠ d := by
        rintro rfl
        rw [(weight_eq_zero_iff 0).2 rfl] at hwd
        exact hN.ne' hwd.symm
      rw [← hwd]
      apply weight_le_of_coeff_ne_zero
      rwa [coeff_sub, coeff_one, if_neg hd0, sub_zero]
  have htopA1 : top 𝔴 (A - 1) = A := by
    ext d
    rw [coeff_top, hdegA1, coeff_sub, coeff_one]
    split_ifs with h1 h2
    · exfalso
      rw [← h2, (weight_eq_zero_iff 0).2 rfl] at h1
      omega
    · rw [sub_zero]
    · exact (hA.coeff_eq_zero d h1).symm

  have hnu : ¬ IsUnit (A - 1) := by
    intro hu
    obtain ⟨r, -, hr⟩ := (isUnit_iff_eq_C_of_isReduced).1 hu
    have h1 : weightedTotalDegree 𝔴 (A - 1) = 0 := by
      rw [hr]
      exact (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero).1
        (isWeightedHomogeneous_C _ r)
    rw [hdegA1] at h1
    exact hN.ne' h1
  obtain ⟨φ, hφirr, ψ, hφψ⟩ := WfDvdMonoid.exists_irreducible_factor hnu hA10
  by_cases hψu : IsUnit ψ
  · rw [hφψ]
    exact (irreducible_mul_isUnit hψu).2 hφirr
  exfalso
  have hφ0 : φ ≠ 0 := hφirr.ne_zero
  have hψ0 : ψ ≠ 0 := by rintro rfl; rw [mul_zero] at hφψ; exact hA10 hφψ

  have hcφψ : constantCoeff φ * constantCoeff ψ = -1 := by rw [← map_mul, ← hφψ, hcA1]
  have hcφ : constantCoeff φ ≠ 0 := fun h => by rw [h, zero_mul] at hcφψ; norm_num at hcφψ

  have hdegφ : 0 < weightedTotalDegree 𝔴 φ := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    have h1 := eq_C_of_weightedTotalDegree_eq_zero h
    exact hφirr.not_isUnit (h1 ▸ (isUnit_iff_eq_C_of_isReduced).2 ⟨_, isUnit_iff_ne_zero.2 hcφ, rfl⟩)
  have hdegψ : 0 < weightedTotalDegree 𝔴 ψ := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    have h1 := eq_C_of_weightedTotalDegree_eq_zero h
    have hcψ : constantCoeff ψ ≠ 0 := fun h' => by rw [h', mul_zero] at hcφψ; norm_num at hcφψ
    exact hψu (h1 ▸ (isUnit_iff_eq_C_of_isReduced).2 ⟨_, isUnit_iff_ne_zero.2 hcψ, rfl⟩)
  have hdegsum : weightedTotalDegree 𝔴 φ + weightedTotalDegree 𝔴 ψ = N := by
    rw [← weightedTotalDegree_mul _ hφ0 hψ0, ← hφψ, hdegA1]
  have hdegφN : weightedTotalDegree 𝔴 φ < N := by omega
  have hndvd : ¬ N ∣ weightedTotalDegree 𝔴 φ := fun h => by
    have := Nat.le_of_dvd hdegφ h; omega

  set s := rot 𝔴 ζ with hs
  have hsA : s (A - 1) = A - 1 := by
    rw [map_sub, map_one, rot_of_isWeightedHomogeneous 𝔴 ζ hA, hζ.pow_eq_one, C_1, one_mul]
  have hprime : Prime φ := hφirr.prime
  have hdvd : φ ∣ s φ * s ψ := by
    rw [← map_mul, ← hφψ, hsA, hφψ]
    exact dvd_mul_right _ _
  have htopφ0 : top 𝔴 φ ≠ 0 := top_ne_zero _ hφ0
  rcases hprime.dvd_or_dvd hdvd with h1 | h2
  ·
    obtain ⟨u, hu⟩ := h1
    have hsφ0 : s φ ≠ 0 := by
      intro h
      have := congrArg (weightedTotalDegree 𝔴) h
      rw [weightedTotalDegree_rot _ _ hζ0, weightedTotalDegree_zero, Nat.bot_eq_zero] at this
      omega
    have hu0 : u ≠ 0 := by rintro rfl; rw [mul_zero] at hu; exact hsφ0 hu
    have hdegu : weightedTotalDegree 𝔴 u = 0 := by
      have := congrArg (weightedTotalDegree 𝔴) hu
      rw [weightedTotalDegree_rot _ _ hζ0, weightedTotalDegree_mul _ hφ0 hu0] at this
      omega
    have hu1 := eq_C_of_weightedTotalDegree_eq_zero hdegu
    have hcu : constantCoeff u = 1 := by
      have := congrArg constantCoeff hu
      rw [constantCoeff_rot, map_mul] at this

      have h' : constantCoeff φ * (constantCoeff u - 1) = 0 := by rw [mul_sub, mul_one, ← this, sub_self]
      rcases mul_eq_zero.1 h' with h'' | h''
      · exact absurd h'' hcφ
      · exact sub_eq_zero.1 h''
    rw [hu1, hcu, C_1, mul_one] at hu

    have htop := congrArg (top 𝔴) hu
    rw [top_rot _ _ hζ0] at htop
    have h' : (C (ζ ^ weightedTotalDegree 𝔴 φ) - 1) * top 𝔴 φ = 0 := by
      rw [sub_mul, one_mul, htop, sub_self]
    rcases mul_eq_zero.1 h' with h'' | h''
    · rw [sub_eq_zero, ← C_1, C_inj, hζ.pow_eq_one_iff_dvd] at h''
      exact hndvd h''
    · exact htopφ0 h''
  ·
    obtain ⟨χ, hχ⟩ := h2
    have hsψ0 : s ψ ≠ 0 := by
      intro h
      have := congrArg (weightedTotalDegree 𝔴) h
      rw [weightedTotalDegree_rot _ _ hζ0, weightedTotalDegree_zero, Nat.bot_eq_zero] at this
      omega
    have hχ0 : χ ≠ 0 := by rintro rfl; rw [mul_zero] at hχ; exact hsψ0 hχ
    have hsφ0 : s φ ≠ 0 := by
      intro h
      have := congrArg (weightedTotalDegree 𝔴) h
      rw [weightedTotalDegree_rot _ _ hζ0, weightedTotalDegree_zero, Nat.bot_eq_zero] at this
      omega
    have hfact : A - 1 = s φ * (φ * χ) := by rw [← hχ, ← map_mul, ← hφψ, hsA]
    have htop : A = C (ζ ^ weightedTotalDegree 𝔴 φ) * top 𝔴 φ * (top 𝔴 φ * top 𝔴 χ) := by
      rw [← htopA1, hfact, top_mul _ hsφ0 (mul_ne_zero hφ0 hχ0), top_mul _ hφ0 hχ0,
        top_rot _ _ hζ0]
    have hdvd2 : top 𝔴 φ * top 𝔴 φ ∣ A :=
      ⟨C (ζ ^ weightedTotalDegree 𝔴 φ) * top 𝔴 χ, by rw [htop]; ring⟩
    have hunit := hsq _ hdvd2
    obtain ⟨r, hr, hr'⟩ := (isUnit_iff_eq_C_of_isReduced).1 hunit
    have h1 : weightedTotalDegree 𝔴 (top 𝔴 φ) = 0 := by
      rw [hr']
      exact (isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero).1
        (isWeightedHomogeneous_C _ r)
    rw [weightedTotalDegree_eq_of_isWeightedHomogeneous _ (top_isWeightedHomogeneous 𝔴 φ) htopφ0]
      at h1
    omega

end Irred

theorem main {K : Type*} [Field K] {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    {Q R : PowerSeries K} (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) N) (hsq : Squarefree A)
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    RingHom.ker (MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K)).toRingHom =
      Ideal.span {A - 1} := by
  classical
  set ε := MvPolynomial.aeval (R := K) (![Q, R] : Fin 2 → PowerSeries K) with hε
  have hA0 : A ≠ 0 := by rintro rfl; rw [map_zero] at hA1; exact zero_ne_one hA1
  have hirr := irreducible_sub_one hN hζ hA hsq hA0
  have hA10 : A - 1 ≠ 0 := hirr.ne_zero
  have hprime : Prime (A - 1) := hirr.prime
  have hle : Ideal.span {A - 1} ≤ RingHom.ker ε.toRingHom := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    change ε (A - 1) = 0
    rw [map_sub, hA1, map_one, sub_self]
  by_contra hne
  have hlt : Ideal.span {A - 1} < RingHom.ker ε.toRingHom := lt_of_le_of_ne hle (Ne.symm hne)
  have hkp : (RingHom.ker ε.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hsp : (Ideal.span {A - 1}).IsPrime := (Ideal.span_singleton_prime hA10).2 hprime

  have hmax : (RingHom.ker ε.toRingHom).IsMaximal := by
    by_contra hnm
    obtain ⟨M, hM, hkM⟩ := Ideal.exists_le_maximal _ hkp.ne_top
    have hkM' : RingHom.ker ε.toRingHom < M := lt_of_le_of_ne hkM (fun h => hnm (h ▸ hM))
    have hbot : (⊥ : Ideal (MvPolynomial (Fin 2) K)) < Ideal.span {A - 1} :=
      bot_lt_iff_ne_bot.2 (by rwa [Ne, Ideal.span_singleton_eq_bot])
    let P : Fin 4 → PrimeSpectrum (MvPolynomial (Fin 2) K) :=
      ![⟨⊥, Ideal.isPrime_bot⟩, ⟨Ideal.span {A - 1}, hsp⟩, ⟨RingHom.ker ε.toRingHom, hkp⟩,
        ⟨M, hM.isPrime⟩]
    have hP : StrictMono P := by
      refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
      fin_cases i
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hbot
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hlt
      · exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).1 hkM'
    have h3 := Order.LTSeries.length_le_krullDim (LTSeries.mk 3 P hP)
    change ((3 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin 2) K) at h3
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add] at h3
    have : ¬ ((3 : ℕ) : WithBot ℕ∞) ≤ (2 : ℕ) := by decide
    exact this (by exact_mod_cast h3)

  have hx : (X 0 ^ 3 - X 1 ^ 2 : MvPolynomial (Fin 2) K) ∉ RingHom.ker ε.toRingHom := by
    rw [RingHom.mem_ker]
    change ε (X 0 ^ 3 - X 1 ^ 2) ≠ 0
    rw [map_sub, map_pow, map_pow, hε, aeval_X, aeval_X]
    simpa [sub_eq_zero] using hQR
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hx
  have hi' : ε i = 0 := by rwa [RingHom.mem_ker] at hi
  have h1 := congrArg (fun p => PowerSeries.constantCoeff (ε p)) hyi
  simp only [map_add, map_mul, map_sub, map_pow, hi', map_one, add_zero] at h1
  rw [hε, aeval_X, aeval_X] at h1
  simp [hQ0, hR0] at h1

end MvPolynomial.KerAevalIsobaricProof

theorem solution
    {K : Type*} [Field K] {N : ℕ} (hN : 0 < N) {ζ : K} (hζ : IsPrimitiveRoot ζ N)
    {Q R : PowerSeries K} (hQ0 : PowerSeries.constantCoeff Q = 1)
    (hR0 : PowerSeries.constantCoeff R = 1) (hQR : Q ^ 3 ≠ R ^ 2)
    {A : MvPolynomial (Fin 2) K}
    (hA : A.IsWeightedHomogeneous (![4, 6] : Fin 2 → ℕ) N) (hsq : Squarefree A)
    (hA1 : MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K) A = 1) :
    RingHom.ker (MvPolynomial.aeval (![Q, R] : Fin 2 → PowerSeries K)).toRingHom =
      Ideal.span {A - 1} :=
  MvPolynomial.KerAevalIsobaricProof.main hN hζ hQ0 hR0 hQR hA hsq hA1

end S_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous
end P2MW
export P2MW.S_MvPolynomial_ker_aeval_eq_span_sub_one_of_squarefree_of_isWeightedHomogeneous (solution)
