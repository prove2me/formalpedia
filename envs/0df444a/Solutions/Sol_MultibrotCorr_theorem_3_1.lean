-- Prove2me | solution 1 for MultibrotCorr.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T18:03:08.755806+00:00
-- url     : https://prove2.me/submissions/366398b2-a3f9-4589-92d5-93e0b3290b2e

import Mathlib
import Definitions.Def_mcorr_branches

open Set Filter Topology Finset

namespace MultibrotCorr

section Alg
open Polynomial

noncomputable def pp (ε : ℕ → ℤ) : ℕ → ℤ[X]
  | 0 => X
  | j + 1 => C (ε j) * pp ε j ^ 2 + X

lemma pp_deg (ε : ℕ → ℤ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) (j : ℕ) :
    (pp ε j).natDegree = 2 ^ j ∧ IsUnit (pp ε j).leadingCoeff := by
  induction j with
  | zero => simp [pp]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have hu : IsUnit (ε j) := by rcases hε j with h | h <;> simp [h]
    have hne : ε j ≠ 0 := by rcases hε j with h | h <;> simp [h]
    have hd : (C (ε j) * pp ε j ^ 2).natDegree = 2 ^ (j + 1) := by
      rw [natDegree_C_mul hne, natDegree_pow, h1]; ring
    have hl : (C (ε j) * pp ε j ^ 2).leadingCoeff = ε j * (pp ε j).leadingCoeff ^ 2 := by
      rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow]
    have hlt : (X : ℤ[X]).natDegree < (C (ε j) * pp ε j ^ 2).natDegree := by
      rw [hd, natDegree_X]; exact Nat.one_lt_two_pow (by omega)
    rw [pp]
    refine ⟨?_, ?_⟩
    · rw [natDegree_add_eq_left_of_natDegree_lt hlt, hd]
    · rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree hlt), hl]
      exact hu.mul (h2.pow 2)

lemma pp_succ_aeval (ε : ℕ → ℤ) (a : ℂ) (j : ℕ) :
    aeval a (pp ε (j + 1)) = (ε j : ℂ) * aeval a (pp ε j) ^ 2 + a := by
  simp [pp]

lemma pp_succ_deriv (ε : ℕ → ℤ) (a : ℂ) (j : ℕ) :
    aeval a (derivative (pp ε (j + 1))) =
      2 * (ε j : ℂ) * aeval a (pp ε j) * aeval a (derivative (pp ε j)) + 1 := by
  simp [pp, derivative_mul, derivative_pow, map_ofNat]
  ring

lemma pp_zero_deriv (ε : ℕ → ℤ) (a : ℂ) : aeval a (derivative (pp ε 0)) = 1 := by
  simp [pp]

lemma integral_aeval (a : ℂ) (ha : IsIntegral ℤ a) (p : ℤ[X]) : IsIntegral ℤ (aeval a p) := by
  have : aeval a p ∈ Algebra.adjoin ℤ {a} := aeval_mem_adjoin_singleton ℤ a (p := p)
  exact (adjoin_le_integralClosure ha) this

lemma a_integral (ε : ℕ → ℤ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) (a : ℂ) (ℓ n : ℕ) (hn : 0 < n)
    (h : aeval a (pp ε (ℓ + n)) = aeval a (pp ε ℓ)) : IsIntegral ℤ a := by
  obtain ⟨d1, u1⟩ := pp_deg ε hε (ℓ + n)
  obtain ⟨d2, u2⟩ := pp_deg ε hε ℓ
  have hlt : (pp ε ℓ).natDegree < (pp ε (ℓ + n)).natDegree := by
    rw [d1, d2]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlc : (pp ε (ℓ + n) - pp ε ℓ).leadingCoeff = (pp ε (ℓ + n)).leadingCoeff :=
    leadingCoeff_sub_of_degree_lt (degree_lt_degree hlt)
  have hu : IsUnit (pp ε (ℓ + n) - pp ε ℓ).leadingCoeff := by rw [hlc]; exact u1
  have hm := monic_of_isUnit_leadingCoeff_inv_smul hu
  refine ⟨_, hm, ?_⟩
  rw [← aeval_def]
  simp [h]

lemma integral_x (ε : ℕ → ℤ) (a : ℂ) (ha : IsIntegral ℤ a) (j : ℕ) :
    IsIntegral ℤ (aeval a (pp ε j)) ∧ IsIntegral ℤ (aeval a (derivative (pp ε j))) :=
  ⟨integral_aeval a ha _, integral_aeval a ha _⟩

lemma not_half (t : ℂ) (ht : IsIntegral ℤ t) (h : 2 * t = 1) : False := by
  have h2 : IsIntegral ℤ ((1 / 2 : ℚ) : ℂ) := by
    have : ((1 / 2 : ℚ) : ℂ) = t := by
      have : (2 : ℂ) ≠ 0 := by norm_num
      push_cast
      field_simp
      linear_combination -h
    rw [this]; exact ht
  have h3 : IsIntegral ℤ (1 / 2 : ℚ) := by
    rwa [← isIntegral_algebraMap_iff (A := ℚ) (B := ℂ) (RingHom.injective (algebraMap ℚ ℂ))]
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp h3
  have : ((m : ℚ)) = 1 / 2 := by simpa using hm
  have h4 : (2 : ℚ) * m = 1 := by rw [this]; norm_num
  have h5 : (2 : ℤ) * m = 1 := by exact_mod_cast h4
  omega


lemma int_two : IsIntegral ℤ (2 : ℂ) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ 2))

lemma int_sign (e : ℤ) (he : e = 1 ∨ e = -1) : IsIntegral ℤ ((e : ℤ) : ℂ) := by
  simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ e))

lemma half_contra (δ m t : ℂ) (hm : IsIntegral ℤ m) (ht : IsIntegral ℤ t)
    (h : 1 + δ + 2 * m = 0) (hδ : δ ^ 2 = 2 * t) : False := by
  refine not_half (t - 2 * m - 2 * m ^ 2) ?_ ?_
  · exact (ht.sub (int_two.mul hm)).sub (int_two.mul (hm.pow 2))
  · have : δ = -(1 + 2 * m) := by linear_combination h
    rw [this] at hδ
    linear_combination -hδ

/-- sum of two signed squares being `-2a` makes the signed sum square an even integer -/
lemma sq_even (s t : ℤ) (hs : s = 1 ∨ s = -1) (ht : t = 1 ∨ t = -1) (p q a : ℂ)
    (hp : IsIntegral ℤ p) (hq : IsIntegral ℤ q) (ha : IsIntegral ℤ a)
    (h : (s : ℂ) * p ^ 2 + (t : ℂ) * q ^ 2 = -2 * a) :
    ∃ u : ℂ, IsIntegral ℤ u ∧ ((s : ℂ) * p + (t : ℂ) * q) ^ 2 = 2 * u := by
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> push_cast at h ⊢
  · exact ⟨-a + p * q, (ha.neg).add (hp.mul hq), by linear_combination h⟩
  · exact ⟨p ^ 2 + a - p * q, ((hp.pow 2).add ha).sub (hp.mul hq), by linear_combination -h⟩
  · exact ⟨q ^ 2 + a - p * q, ((hq.pow 2).add ha).sub (hp.mul hq), by linear_combination -h⟩
  · exact ⟨a + p * q, ha.add (hp.mul hq), by linear_combination -h⟩

lemma d_form (ε : ℕ → ℤ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) (a : ℂ) (ha : IsIntegral ℤ a) (j : ℕ) :
    ∃ g : ℂ, IsIntegral ℤ g ∧ aeval a (derivative (pp ε j)) = 1 + 2 * g := by
  cases j with
  | zero => exact ⟨0, isIntegral_zero, by simp [pp_zero_deriv]⟩
  | succ j =>
    refine ⟨(ε j : ℂ) * aeval a (pp ε j) * aeval a (derivative (pp ε j)),
      ((int_sign _ (hε j)).mul (integral_x ε a ha j).1).mul (integral_x ε a ha j).2, ?_⟩
    rw [pp_succ_deriv]; ring

lemma same_case (σ P Q pP q2 mP mq : ℂ) (hσ : σ ≠ 0) (hsq : P ^ 2 = Q ^ 2) (hne : Q ≠ P)
    (hQ : Q ≠ 0) (hd : σ * P * (1 + 2 * pP + 4 * mP) = σ * Q * (1 + 2 * q2 + 4 * mq))
    (hmP : IsIntegral ℤ mP) (hmq : IsIntegral ℤ mq)
    (hsqe : P + Q = 0 → ∃ u : ℂ, IsIntegral ℤ u ∧ (pP + q2) ^ 2 = 2 * u) : False := by
  have hPQ : P + Q = 0 := by
    have : (P - Q) * (P + Q) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (by linear_combination -h) hne
    · exact h
  obtain ⟨u, hu, hu2⟩ := hsqe hPQ
  have hP : P = -Q := by linear_combination hPQ
  rw [hP] at hd
  have h1 : σ * Q * (2 + 2 * pP + 2 * q2 + 4 * mP + 4 * mq) = 0 := by linear_combination -hd
  have h2 : 1 + (pP + q2) + 2 * (mP + mq) = 0 := by
    have := mul_eq_zero.mp h1
    rcases this with h | h
    · exact absurd h (mul_ne_zero hσ hQ)
    · linear_combination h / 2
  exact half_contra (pP + q2) (mP + mq) u (hmP.add hmq) hu h2 hu2

lemma opp_case (σ P Q gP gQ : ℂ) (hσ : σ ≠ 0) (hsq : σ * P ^ 2 = -σ * Q ^ 2) (hQ : Q ≠ 0)
    (hd : σ * P * (1 + 2 * gP) = -σ * Q * (1 + 2 * gQ))
    (hgP : IsIntegral ℤ gP) (hgQ : IsIntegral ℤ gQ) : False := by
  set r := P / Q with hr
  have hPr : P = r * Q := by rw [hr]; field_simp
  have hr2 : r ^ 2 = -1 := by
    rw [hPr] at hsq
    have : σ * Q ^ 2 * (r ^ 2 + 1) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (mul_ne_zero hσ (pow_ne_zero 2 hQ))
    · linear_combination h
  have hrint : IsIntegral ℤ r := IsIntegral.of_pow (n := 2) (by norm_num) (by
    rw [hr2]; simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ (-1))))
  rw [hPr] at hd
  have h1 : σ * Q * (r * (1 + 2 * gP) + (1 + 2 * gQ)) = 0 := by linear_combination hd
  have h2 : r * (1 + 2 * gP) + (1 + 2 * gQ) = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (mul_ne_zero hσ hQ)
    · exact h
  set y := -(r * gP + gQ) with hy
  have hyint : IsIntegral ℤ y := ((hrint.mul hgP).add hgQ).neg
  have hy2 : 2 * y = 1 + r := by rw [hy]; linear_combination -h2
  refine not_half (y - y ^ 2) (hyint.sub (hyint.pow 2)) ?_
  linear_combination (-1/2 : ℂ) * hr2 + (-r/2 - y + 1/2) * hy2

lemma core (ε : ℕ → ℤ) (hε : ∀ j, ε j = 1 ∨ ε j = -1) (a : ℂ) (ha : IsIntegral ℤ a)
    (L N : ℕ)
    (hx : aeval a (pp ε (L + N + 1 + 1)) = aeval a (pp ε (L + 1)))
    (hne : aeval a (pp ε L) ≠ aeval a (pp ε (L + N + 1)))
    (hQ : aeval a (pp ε L) ≠ 0) :
    aeval a (derivative (pp ε (L + N + 1 + 1))) ≠ aeval a (derivative (pp ε (L + 1))) := by
  intro hd
  obtain ⟨K, hK⟩ : ∃ K, K = L + N := ⟨_, rfl⟩
  have hKe : L + N + 1 + 1 = K + 1 + 1 := by omega
  have hKe2 : L + N + 1 = K + 1 := by omega
  rw [hKe] at hx hd
  rw [hKe2] at hne
  have hPint : IsIntegral ℤ (aeval a (pp ε (K + 1))) := (integral_x ε a ha _).1
  have hQint : IsIntegral ℤ (aeval a (pp ε L)) := (integral_x ε a ha _).1
  have hxK := (integral_x ε a ha K).1
  rw [pp_succ_aeval, pp_succ_aeval ε a L] at hx
  rw [pp_succ_deriv ε a (K + 1), pp_succ_deriv ε a L] at hd
  obtain ⟨gP, hgP, hDP⟩ := d_form ε hε a ha (K + 1)
  obtain ⟨gQ, hgQ, hDQ⟩ := d_form ε hε a ha L
  obtain ⟨gK, hgK, hDK⟩ := d_form ε hε a ha K
  have hPeq := pp_succ_aeval ε a K
  have hDPe := pp_succ_deriv ε a K
  have hDP2 : aeval a (derivative (pp ε (K + 1))) =
      1 + 2 * ((ε K : ℂ) * aeval a (pp ε K)) + 4 * ((ε K : ℂ) * aeval a (pp ε K) * gK) := by
    rw [hDPe, hDK]; ring
  have hmP : IsIntegral ℤ ((ε K : ℂ) * aeval a (pp ε K) * gK) :=
    ((int_sign _ (hε K)).mul hxK).mul hgK
  -- data on the Q side
  obtain ⟨q2, mq, hmq, hDQ2, hsqe⟩ : ∃ q2 mq : ℂ, IsIntegral ℤ mq ∧
      aeval a (derivative (pp ε L)) = 1 + 2 * q2 + 4 * mq ∧
      (aeval a (pp ε (K + 1)) + aeval a (pp ε L) = 0 →
        ∃ u : ℂ, IsIntegral ℤ u ∧ ((ε K : ℂ) * aeval a (pp ε K) + q2) ^ 2 = 2 * u) := by
    cases L with
    | zero =>
      refine ⟨0, 0, isIntegral_zero, by simp [pp_zero_deriv], ?_⟩
      intro h
      have h' : (ε K : ℂ) * aeval a (pp ε K) ^ 2 + a + aeval a (pp ε 0) = 0 := by
        rw [← hPeq]; exact h
      have h'' : (ε K : ℂ) * aeval a (pp ε K) ^ 2 + ((1 : ℤ) : ℂ) * (0 : ℂ) ^ 2 = -2 * a := by
        simp [pp] at h' ⊢; linear_combination h'
      obtain ⟨u, hu, hu2⟩ := sq_even (ε K) 1 (hε K) (Or.inl rfl) _ 0 a hxK isIntegral_zero ha h''
      exact ⟨u, hu, by simpa using hu2⟩
    | succ L' =>
      obtain ⟨g', hg', hD'⟩ := d_form ε hε a ha L'
      have hx' := (integral_x ε a ha L').1
      refine ⟨(ε L' : ℂ) * aeval a (pp ε L'), (ε L' : ℂ) * aeval a (pp ε L') * g',
        ((int_sign _ (hε L')).mul hx').mul hg', ?_, ?_⟩
      · rw [pp_succ_deriv, hD']; ring
      · intro h
        have h' : (ε K : ℂ) * aeval a (pp ε K) ^ 2 + (ε L' : ℂ) * aeval a (pp ε L') ^ 2
            = -2 * a := by
          rw [hPeq, pp_succ_aeval] at h; linear_combination h
        obtain ⟨u, hu, hu2⟩ := sq_even (ε K) (ε L') (hε K) (hε L') _ _ a hxK hx' ha h'
        exact ⟨u, hu, hu2⟩
  have hσ : ((ε (K + 1) : ℤ) : ℂ) ≠ 0 := by
    rcases hε (K + 1) with h | h <;> simp [h]
  by_cases hs : ε (K + 1) = ε L
  · have hs' : ((ε L : ℤ) : ℂ) = ((ε (K + 1) : ℤ) : ℂ) := by rw [hs]
    rw [hs'] at hx hd
    rw [hDP2, hDQ2] at hd
    refine same_case ((ε (K + 1) : ℤ) : ℂ) _ _ _ q2 _ mq hσ ?_ hne hQ ?_ hmP hmq hsqe
    · have : (ε (K + 1) : ℂ) * (aeval a (pp ε (K + 1)) ^ 2 - aeval a (pp ε L) ^ 2) = 0 := by
        linear_combination hx
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hσ
      · linear_combination h
    · linear_combination hd / 2
  · have hs' : ((ε L : ℤ) : ℂ) = -((ε (K + 1) : ℤ) : ℂ) := by
      rcases hε (K + 1) with h | h <;> rcases hε L with h' | h' <;> simp_all
    rw [hs'] at hx hd
    rw [hDP, hDQ] at hd
    refine opp_case ((ε (K + 1) : ℤ) : ℂ) (aeval a (pp ε (K + 1))) (aeval a (pp ε L)) gP gQ hσ ?_ hQ ?_ hgP hgQ
    · linear_combination hx
    · linear_combination hd / 2



lemma pc_succ (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ) (s len : ℕ) (c z : ℂ) :
    perturbedComp e φ s (len + 1) c z = φ (s + len) (perturbedComp e φ s len c z) + c := by
  simp [perturbedComp, List.range_succ, List.foldl_append]

lemma pc_comp (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ) (ℓ n : ℕ) (c z : ℂ) :
    perturbedComp e φ ℓ n c (perturbedComp e φ 0 ℓ c z) = perturbedComp e φ 0 (ℓ + n) c z := by
  induction n with
  | zero => simp [perturbedComp]
  | succ n ih =>
    rw [pc_succ, ih, show ℓ + (n + 1) = ℓ + n + 1 from rfl, pc_succ]
    simp

lemma branch_sign (a : ℂ) (zj : ℂ) (hz : zj ≠ 0) (U : Set ℂ) (f : ℂ → ℂ) (hU : IsOpen U)
    (hzU : zj ∈ U) (hd : DifferentiableOn ℂ f U) (hf : ∀ z ∈ U, (f z - 0) ^ 2 = z ^ 4) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ᶠ w in 𝓝 zj, f w = (s : ℂ) * w ^ 2 := by
  have h0 : (f zj - zj ^ 2) * (f zj + zj ^ 2) = 0 := by
    have := hf zj hzU; linear_combination this
  have hz2 : zj ^ 2 ≠ 0 := pow_ne_zero 2 hz
  obtain ⟨s, hs, hfs⟩ : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ f zj = (s : ℂ) * zj ^ 2 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact ⟨1, Or.inl rfl, by push_cast; linear_combination h⟩
    · exact ⟨-1, Or.inr rfl, by push_cast; linear_combination h⟩
  refine ⟨s, hs, ?_⟩
  have hcont : ContinuousAt f zj := (hd.differentiableAt (hU.mem_nhds hzU)).continuousAt
  have hne : (f zj + (s : ℂ) * zj ^ 2) ≠ 0 := by
    rw [hfs]
    have : (s : ℂ) ≠ 0 := by rcases hs with h | h <;> simp [h]
    intro h
    have : (s : ℂ) * zj ^ 2 = 0 := by linear_combination h / 2
    exact mul_ne_zero ‹(s : ℂ) ≠ 0› hz2 this
  have h1 : ∀ᶠ w in 𝓝 zj, f w + (s : ℂ) * w ^ 2 ≠ 0 := by
    have hc : ContinuousAt (fun w => f w + (s : ℂ) * w ^ 2) zj := by fun_prop
    exact hc.eventually_ne hne
  filter_upwards [h1, hU.mem_nhds hzU] with w hw hwU
  have := hf w hwU
  have hs2 : (s : ℂ) ^ 2 = 1 := by rcases hs with h | h <;> simp [h]
  have h3 : (f w - (s : ℂ) * w ^ 2) * (f w + (s : ℂ) * w ^ 2) = 0 := by
    linear_combination this - w ^ 4 * hs2
  rcases mul_eq_zero.mp h3 with h | h
  · linear_combination h
  · exact absurd h hw

lemma motion (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ) (z : ℕ → ℂ) (a : ℂ) (ε : ℕ → ℤ)
    (hz0 : z 0 = a)
    (hstep : ∀ j, φ j (z j) + a = z (j + 1))
    (hev : ∀ j, ∀ᶠ w in 𝓝 (z j), φ j w = ((ε j : ℤ) : ℂ) * w ^ 2) (j : ℕ) :
    aeval a (pp ε j) = z j ∧
      ∀ᶠ c in 𝓝 a, perturbedComp e φ 0 j c c = aeval c (pp ε j) := by
  induction j with
  | zero => simp [pp, perturbedComp, hz0]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · rw [pp_succ_aeval, h1, ← hstep j, (hev j).self_of_nhds]
    · have hc : Tendsto (fun c : ℂ => aeval c (pp ε j)) (𝓝 a) (𝓝 (z j)) := by
        rw [← h1]
        exact ((pp ε j).continuous_aeval).continuousAt.tendsto
      filter_upwards [h2, hc.eventually (hev j)] with c hc1 hc2
      rw [pc_succ, hc1, zero_add, hc2, pp_succ_aeval]

lemma deriv_w (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ) (z : ℕ → ℂ) (a : ℂ) (ε : ℕ → ℤ) (ℓ n : ℕ)
    (hz0 : z 0 = a)
    (hstep : ∀ j, φ j (z j) + a = z (j + 1))
    (hev : ∀ j, ∀ᶠ w in 𝓝 (z j), φ j w = ((ε j : ℤ) : ℂ) * w ^ 2) :
    deriv (wFun e ℓ n φ) a =
      aeval a (derivative (pp ε (ℓ + n))) - aeval a (derivative (pp ε ℓ)) := by
  have h1 := (motion e φ z a ε hz0 hstep hev ℓ).2
  have h2 := (motion e φ z a ε hz0 hstep hev (ℓ + n)).2
  have heq : wFun e ℓ n φ =ᶠ[𝓝 a] fun c => aeval c (pp ε (ℓ + n)) - aeval c (pp ε ℓ) := by
    filter_upwards [h1, h2] with c hc1 hc2
    simp only [wFun, hFun, gFun]
    rw [pc_comp, hc1, hc2]
  rw [heq.deriv_eq]
  exact ((Polynomial.hasDerivAt_aeval (pp ε (ℓ + n)) a).sub
    (Polynomial.hasDerivAt_aeval (pp ε ℓ) a)).deriv

theorem theorem_3_1 (a : ℂ) (ha : IsMisiurewicz quadCorrExponent a) :
    TransversalAt quadCorrExponent a := by
  refine ⟨ha, ?_⟩
  intro ℓ n z φ U hD
  obtain ⟨hℓ, hn, hz0, hcorr, hz0ne, hbr, -, -, -, -, hper, -, hmin, -, -⟩ := hD
  have hsg : ∀ j, ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ᶠ w in 𝓝 (z j), φ j w = (s : ℂ) * w ^ 2 := by
    intro j
    obtain ⟨hUo, hzU, ⟨-, hdiff, -, hf⟩, -⟩ := hbr j
    exact branch_sign a (z j) (hz0ne j) (U j) (φ j) hUo hzU hdiff (by simpa [quadCorrExponent] using hf)
  choose ε hε hev using hsg
  have hstep : ∀ j, φ j (z j) + a = z (j + 1) := fun j => (hbr j).2.2.2
  rw [deriv_w quadCorrExponent φ z a ε ℓ n hz0 hstep hev]
  have hx : ∀ j, aeval a (pp ε j) = z j := fun j => (motion quadCorrExponent φ z a ε hz0 hstep hev j).1
  obtain ⟨L, rfl⟩ : ∃ L, ℓ = L + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hper' : z (L + 1 + (N + 1)) = z (L + 1) := hper (L + 1) (by omega)
  have hint : IsIntegral ℤ a :=
    a_integral ε hε a (L + 1) (N + 1) hn (by rw [hx, hx]; exact hper')
  have hcore := core ε hε a hint L N
    (by rw [hx, hx, show L + N + 1 + 1 = L + 1 + (N + 1) by omega]; exact hper')
    (by rw [hx, hx]; exact hmin L (by omega) (L + N + 1) (by omega))
    (by rw [hx]; exact hz0ne L)
  rw [show L + 1 + (N + 1) = L + N + 1 + 1 by omega]
  exact sub_ne_zero.mpr hcore

end Alg

end MultibrotCorr

open MultibrotCorr in
theorem solution (a : ℂ) (ha : IsMisiurewicz quadCorrExponent a) :
    TransversalAt quadCorrExponent a := theorem_3_1 a ha
