-- Prove2me | solution 1 for InconsistentDR.Shadow.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T00:13:45.200014+00:00
-- url     : https://prove2.me/submissions/8a0f64d7-1b3e-4fe8-977b-19a27cd0adcb

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_ThreeOpSplitting_Convergence_WeakConvergence
import Definitions.Def_InconsistentDR_Shadow_Operators
import Theorems.Thm_InconsistentDR_Shadow_convex_closure_dom
import Theorems.Thm_QuasiFejerOpial_exists_weak_subsequence

open scoped InnerProductSpace Topology Pointwise
open Filter ThreeOpSplitting.Convergence

namespace DR32Aux

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma res_mem (A : X → Set X) (J : X → X) (hJ : IsResolvent 1 A J) (x : X) :
    x - J x ∈ A (J x) := by
  have := hJ x; rwa [inv_one, one_smul] at this

/-- Resolvents of monotone operators are nonexpansive. -/
lemma res_nonexp (A : X → Set X) (hA : IsMonotoneOp A) (μ : ℝ) (hμ : 0 < μ) (J : X → X)
    (hJ : IsResolvent μ A J) (x y : X) : ‖J x - J y‖ ≤ ‖x - y‖ := by
  have h := hA _ _ _ _ (hJ x) (hJ y)
  rw [← smul_sub, real_inner_smul_right] at h
  have h' : 0 ≤ ⟪J x - J y, (x - J x) - (y - J y)⟫_ℝ := by
    have := (mul_nonneg_iff_of_pos_left (inv_pos.mpr hμ)).mp h
    exact this
  have e : (x - J x) - (y - J y) = (x - y) - (J x - J y) := by abel
  rw [e, inner_sub_right, real_inner_self_eq_norm_sq] at h'
  have h2 : ‖J x - J y‖ ^ 2 ≤ ‖J x - J y‖ * ‖x - y‖ :=
    (by linarith : ‖J x - J y‖ ^ 2 ≤ ⟪J x - J y, x - y⟫_ℝ).trans (real_inner_le_norm _ _)
  by_cases h0 : ‖J x - J y‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖J x - J y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/-- From the resolvent of `μ A` to that of `(3/4) μ A` (Banach fixed point). -/
lemma res_step [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (μ : ℝ) (hμ : 0 < μ)
    (J : X → X) (hJ : IsResolvent μ A J) : ∃ J' : X → X, IsResolvent (3 / 4 * μ) A J' := by
  have hK0 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have key : ∀ x : X, ∃ y : X, J ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • y) = y := by
    intro x
    let Φ : X → X := fun y => J ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • y)
    have hlip : LipschitzWith ⟨1 / 3, hK0⟩ Φ := by
      refine LipschitzWith.of_dist_le_mul fun a b => ?_
      simp only [Φ, dist_eq_norm]
      show _ ≤ (1 / 3 : ℝ) * _
      refine (res_nonexp A hA μ hμ J hJ _ _).trans (le_of_eq ?_)
      have e : (4 / 3 : ℝ) • x - (1 / 3 : ℝ) • a - ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • b) =
          (-(1 / 3 : ℝ)) • (a - b) := by module
      rw [e, norm_smul]; norm_num
    have hcon : ContractingWith ⟨1 / 3, hK0⟩ Φ :=
      ⟨by exact_mod_cast (by norm_num : (1 / 3 : ℝ) < 1), hlip⟩
    exact ⟨_, hcon.fixedPoint_isFixedPt⟩
  choose J' hJ' using key
  refine ⟨J', fun x => ?_⟩
  have h := hJ ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • J' x)
  rw [hJ' x] at h
  have e : μ⁻¹ • ((4 / 3 : ℝ) • x - (1 / 3 : ℝ) • J' x - J' x) = (3 / 4 * μ)⁻¹ • (x - J' x) := by
    rw [show (4 / 3 : ℝ) • x - (1 / 3 : ℝ) • J' x - J' x = (4 / 3 : ℝ) • (x - J' x) by module,
      smul_smul]
    congr 1
    field_simp
  rw [e] at h
  exact h

lemma res_pow [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) : ∀ k : ℕ, ∃ J' : X → X, IsResolvent ((3 / 4 : ℝ) ^ k) A J' := by
  intro k
  induction k with
  | zero => exact ⟨J, by simpa using hJ⟩
  | succ k ih =>
    obtain ⟨J', hJ'⟩ := ih
    obtain ⟨J'', hJ''⟩ := res_step A hA _ (by positivity) J' hJ'
    exact ⟨J'', by rw [pow_succ, mul_comm]; exact hJ''⟩

/-- The inverse operator `A⁻¹`. -/
def opInv (A : X → Set X) : X → Set X := fun u => {x | u ∈ A x}

lemma opInv_mono (A : X → Set X) (hA : IsMonotoneOp A) : IsMonotoneOp (opInv A) := by
  intro x y u w hu hw
  have := hA _ _ _ _ hu hw
  rwa [real_inner_comm] at this

lemma opInv_res (A : X → Set X) (J : X → X) (hJ : IsResolvent 1 A J) :
    IsResolvent 1 (opInv A) (fun x => x - J x) := by
  intro x
  rw [inv_one, one_smul]
  show x - J x ∈ A (x - (x - J x))
  rw [sub_sub_cancel]
  exact res_mem A J hJ x


/-- Closed convex sets are weakly sequentially closed. -/
lemma weak_closed [CompleteSpace X] {C : Set X} (hC : IsClosed C) (hcv : Convex ℝ C)
    (z : ℕ → X) (hz : ∀ k, z k ∈ C) (w : X)
    (hw : ∀ y, Tendsto (fun k => ⟪z k, y⟫_ℝ) atTop (𝓝 ⟪w, y⟫_ℝ)) : w ∈ C := by
  have hne : C.Nonempty := ⟨z 0, hz 0⟩
  obtain ⟨c, hcC, hc⟩ := exists_norm_eq_iInf_of_complete_convex hne hC.isComplete hcv w
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hcv hcC).mp hc
  have h1 : ∀ k, ⟪z k, w - c⟫_ℝ ≤ ⟪c, w - c⟫_ℝ := by
    intro k
    have := hvi _ (hz k)
    rw [real_inner_comm, inner_sub_left] at this
    linarith
  have h3 : ⟪w, w - c⟫_ℝ ≤ ⟪c, w - c⟫_ℝ := le_of_tendsto' (hw (w - c)) h1
  have h4 : ‖w - c‖ ^ 2 ≤ 0 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left]; linarith
  have h5 : w = c := by
    have : ‖w - c‖ = 0 := by nlinarith [norm_nonneg (w - c)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  rw [h5]; exact hcC

/-- An element of the polar of the recession cone is, up to `ε‖·‖`, bounded above on `C`
(the closure of the barrier cone is the polar of the recession cone, [36, Theorem 3.1]). -/
lemma barrier [CompleteSpace X] {C : Set X} (hC : IsClosed C) (hcv : Convex ℝ C)
    (hne : C.Nonempty) (u : X)
    (hu : ∀ d, (∀ c ∈ C, ∀ t : ℝ, 0 ≤ t → c + t • d ∈ C) → ⟪d, u⟫_ℝ ≤ 0)
    (ε : ℝ) (hε : 0 < ε) : ∃ K : ℝ, ∀ y ∈ C, ⟪y, u⟫_ℝ ≤ K + ε * ‖y‖ := by
  by_cases hsmall : ‖u‖ ≤ ε
  · refine ⟨0, fun y _ => ?_⟩
    have := real_inner_le_norm y u
    have : ‖y‖ * ‖u‖ ≤ ‖y‖ * ε := mul_le_mul_of_nonneg_left hsmall (norm_nonneg _)
    linarith
  push Not at hsmall
  by_contra H
  push Not at H
  choose y hyC hy using fun n : ℕ => H n
  obtain ⟨c0, hc0⟩ := hne
  set δ := ‖u‖ - ε with hδ
  have hδ0 : 0 < δ := by linarith
  set M0 := ε * ‖c0‖ + ‖c0‖ * ‖u‖ with hM0
  set ρ : ℕ → ℝ := fun n => ‖y n - c0‖ with hρ
  have hρlow : ∀ n : ℕ, (n : ℝ) - M0 < ρ n * δ := by
    intro n
    have h1 := hy n
    have h2 : ⟪y n - c0, u⟫_ℝ ≤ ρ n * ‖u‖ := real_inner_le_norm _ _
    have h3 : ρ n - ‖c0‖ ≤ ‖y n‖ := by
      have := norm_sub_le (y n) c0
      simp only [hρ]; linarith
    have h4 : -(‖c0‖ * ‖u‖) ≤ ⟪c0, u⟫_ℝ := by
      have := abs_real_inner_le_norm c0 u
      linarith [neg_abs_le ⟪c0, u⟫_ℝ]
    have h5 : ⟪c0, u⟫_ℝ ≤ ‖c0‖ * ‖u‖ := real_inner_le_norm _ _
    rw [inner_sub_left] at h2
    have : ε * (ρ n - ‖c0‖) ≤ ε * ‖y n‖ := mul_le_mul_of_nonneg_left h3 hε.le
    simp only [hδ, hM0]
    nlinarith
  -- normalized directions
  set d : ℕ → X := fun n => (ρ n)⁻¹ • (y n - c0) with hd
  have hdb : ∀ n, ‖d n‖ ≤ 1 := by
    intro n
    have ha : |ρ n| = ‖y n - c0‖ := abs_of_nonneg (norm_nonneg _)
    simp only [hd, norm_smul, norm_inv, Real.norm_eq_abs]
    rw [ha]
    by_cases h0 : ‖y n - c0‖ = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  obtain ⟨r, hr, p, hp⟩ := QuasiFejerOpial.exists_weak_subsequence d 1 hdb
  -- `⟪p, u⟫ ≥ ε`
  have hNat : ∃ N : ℕ, M0 + 1 ≤ N := exists_nat_ge _
  obtain ⟨N, hN⟩ := hNat
  have hρpos : ∀ n : ℕ, N ≤ n → 0 < ρ n := by
    intro n hn
    have := hρlow n
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    have : 0 < ρ n * δ := by linarith
    exact pos_of_mul_pos_left this hδ0.le
  have hdu : ∀ n : ℕ, N ≤ n → ε ≤ ⟪d n, u⟫_ℝ := by
    intro n hn
    have hpos := hρpos n hn
    have h1 := hy n
    have h3 : ρ n - ‖c0‖ ≤ ‖y n‖ := by
      have := norm_sub_le (y n) c0
      simp only [hρ]; linarith
    have h5 : ⟪c0, u⟫_ℝ ≤ ‖c0‖ * ‖u‖ := real_inner_le_norm _ _
    have : ε * (ρ n - ‖c0‖) ≤ ε * ‖y n‖ := mul_le_mul_of_nonneg_left h3 hε.le
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have key : ε * ρ n ≤ ⟪y n - c0, u⟫_ℝ := by
      rw [inner_sub_left]; nlinarith
    simp only [hd, real_inner_smul_left]
    rw [le_inv_mul_iff₀ hpos]
    linarith
  have hpu : ε ≤ ⟪p, u⟫_ℝ := by
    have hlim := hp u
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with k hk
    exact hdu (r k) (hk.trans (hr.id_le k))
  -- `p` is a recession direction of `C`
  have hrec : ∀ c ∈ C, ∀ t : ℝ, 0 ≤ t → c + t • p ∈ C := by
    intro c hc t ht
    obtain ⟨N2, hN2⟩ : ∃ N2 : ℕ, (t * δ + M0 + 1 : ℝ) ≤ N2 := exists_nat_ge _
    set m : ℕ → ℕ := fun k => r (k + (N + N2)) with hm
    have hmge : ∀ k, k + (N + N2) ≤ m k := fun k => hr.id_le _
    have hmN : ∀ k, N ≤ m k := fun k => le_trans (by omega) (hmge k)
    have hρm : ∀ k : ℕ, (k : ℝ) + t * δ + 1 < ρ (m k) * δ := by
      intro k
      have h1 := hρlow (m k)
      have h2 : ((k + (N + N2) : ℕ) : ℝ) ≤ (m k : ℝ) := by exact_mod_cast hmge k
      push_cast at h2
      have h3 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
      linarith
    have hρmpos : ∀ k, 0 < ρ (m k) := fun k => hρpos _ (hmN k)
    set θ : ℕ → ℝ := fun k => t / ρ (m k) with hθ
    have hθ0 : ∀ k, 0 ≤ θ k := fun k => div_nonneg ht (hρmpos k).le
    have hθ1 : ∀ k, θ k ≤ 1 := by
      intro k
      rw [hθ, div_le_one (hρmpos k)]
      have := hρm k
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
      by_contra hcon
      push Not at hcon
      have : t * δ > ρ (m k) * δ := by nlinarith
      linarith
    have hθle : ∀ k, θ k ≤ t * δ / ((k : ℝ) + 1) := by
      intro k
      rw [hθ, div_le_div_iff₀ (hρmpos k) (by positivity)]
      have := hρm k
      have h' : (k : ℝ) + 1 ≤ ρ (m k) * δ := by nlinarith [mul_nonneg ht hδ0.le]
      nlinarith [mul_le_mul_of_nonneg_left h' ht]
    have hθlim : Tendsto θ atTop (𝓝 0) := by
      refine squeeze_zero hθ0 hθle ?_
      have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (t * δ)
      rw [mul_zero] at h
      refine h.congr (fun k => ?_)
      ring
    set z : ℕ → X := fun k => c + θ k • (y (m k) - c) with hz
    have hzC : ∀ k, z k ∈ C := by
      intro k
      have e : z k = (1 - θ k) • c + θ k • y (m k) := by simp only [hz]; module
      rw [e]
      exact hcv hc (hyC _) (by linarith [hθ1 k]) (hθ0 k) (by ring)
    have hzd : ∀ k, z k = c + t • d (m k) + θ k • (c0 - c) := by
      intro k
      have hne : ρ (m k) ≠ 0 := (hρmpos k).ne'
      simp only [hz, hd, hθ]
      rw [smul_smul, div_eq_mul_inv]
      module
    apply weak_closed hC hcv z hzC
    intro w
    have h1 : Tendsto (fun k => ⟪d (m k), w⟫_ℝ) atTop (𝓝 ⟪p, w⟫_ℝ) :=
      (hp w).comp (tendsto_add_atTop_nat (N + N2))
    have h2 : Tendsto (fun k => ⟪c, w⟫_ℝ + t * ⟪d (m k), w⟫_ℝ + θ k * ⟪c0 - c, w⟫_ℝ) atTop
        (𝓝 (⟪c, w⟫_ℝ + t * ⟪p, w⟫_ℝ + 0 * ⟪c0 - c, w⟫_ℝ)) :=
      (tendsto_const_nhds.add (h1.const_mul t)).add (hθlim.mul_const _)
    rw [zero_mul, add_zero] at h2
    have e1 : ⟪c + t • p, w⟫_ℝ = ⟪c, w⟫_ℝ + t * ⟪p, w⟫_ℝ := by
      rw [inner_add_left, real_inner_smul_left]
    rw [e1]
    refine h2.congr (fun k => ?_)
    rw [hzd k, inner_add_left, inner_add_left]
    simp only [hd, real_inner_smul_left]
  have := hu p hrec
  linarith

/-- Core of Lemma 3.2(i): `(rec cl dom A)^⊖ + ran A ⊆ cl ran A`. -/
lemma core [CompleteSpace X] (A : X → Set X) (hA : IsMonotoneOp A) (J : X → X)
    (hJ : IsResolvent 1 A J) (hcv : Convex ℝ (closure (dom A))) (u : X)
    (hu : ∀ d : X, (∀ c ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (dom A)) →
        ⟪d, u⟫_ℝ ≤ 0)
    (a as : X) (has : as ∈ A a) : as + u ∈ closure (InconsistentDR.Shadow.ran A) := by
  have hne : (closure (dom A)).Nonempty := ⟨J 0, subset_closure ⟨_, res_mem A J hJ 0⟩⟩
  set w := as + u with hw
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨K, hK⟩ := barrier isClosed_closure hcv hne u hu (δ / 4) (by positivity)
  set K' := |K| + ‖a‖ * ‖u‖ with hK'
  have hK'0 : 0 ≤ K' := by positivity
  set mm := min (δ / (4 * (‖a‖ + 1))) (δ ^ 2 / (4 * (K' + 1))) with hmm
  have hmm0 : 0 < mm := lt_min (by positivity) (by positivity)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hmm0 (by norm_num : (3 / 4 : ℝ) < 1)
  set lam := (3 / 4 : ℝ) ^ k with hlam
  have hlam0 : 0 < lam := by positivity
  have hl1 : lam * (‖a‖ + 1) ≤ δ / 4 := by
    have : lam ≤ δ / (4 * (‖a‖ + 1)) := hk.le.trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hl2 : lam * (K' + 1) ≤ δ ^ 2 / 4 := by
    have : lam ≤ δ ^ 2 / (4 * (K' + 1)) := hk.le.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  obtain ⟨Jl, hJl⟩ := res_pow (opInv A) (opInv_mono A hA) _ (opInv_res A J hJ) k
  set p := Jl w with hp
  have hpy : p ∈ A (lam⁻¹ • (w - p)) := hJl w
  generalize hy : lam⁻¹ • (w - p) = y at hpy
  refine ⟨p, ⟨y, hpy⟩, ?_⟩
  rw [dist_eq_norm]
  have hwp : w - p = lam • y := by rw [← hy, smul_smul, mul_inv_cancel₀ hlam0.ne', one_smul]
  have hyC : y ∈ closure (dom A) := subset_closure ⟨p, hpy⟩
  have hbar := hK y hyC
  have hm := hA _ _ _ _ hpy has
  have e1 : p - as = u - lam • y := by
    have : p = w - lam • y := by rw [← hwp]; abel
    rw [this, hw]; abel
  rw [e1, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq] at hm
  have i1 : ⟪a, y⟫_ℝ ≤ ‖a‖ * ‖y‖ := real_inner_le_norm _ _
  have i2 : -⟪a, u⟫_ℝ ≤ ‖a‖ * ‖u‖ := by
    have := abs_real_inner_le_norm a u
    linarith [neg_abs_le ⟪a, u⟫_ℝ]
  have hKabs : K ≤ |K| := le_abs_self K
  -- `λ ‖y‖² ≤ K' + (δ/4 + λ ‖a‖) ‖y‖`
  have hmain : lam * ‖y‖ ^ 2 ≤ K' + (δ / 4 + lam * ‖a‖) * ‖y‖ := by
    rw [hK']; nlinarith [norm_nonneg y, norm_nonneg a]
  set s := lam * ‖y‖ with hs
  have hs0 : 0 ≤ s := by positivity
  have hnorm : ‖w - p‖ = s := by rw [hwp, norm_smul, Real.norm_of_nonneg hlam0.le]
  rw [hnorm]
  have hs2 : s ^ 2 ≤ lam * K' + (δ / 4 + lam * ‖a‖) * s := by
    have := mul_le_mul_of_nonneg_left hmain hlam0.le
    rw [hs]; nlinarith
  have hla : lam * ‖a‖ ≤ δ / 4 := by nlinarith
  have hlK : lam * K' ≤ δ ^ 2 / 4 := by nlinarith
  by_contra hcon
  push Not at hcon
  have : (δ / 4 + lam * ‖a‖) * s ≤ δ / 2 * s := by nlinarith
  nlinarith

end DR32Aux

theorem solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
    (A : X → Set X) (hA : IsMaximalMonotone A) (J : X → X) (hJ : IsResolvent 1 A J) :
    (∀ u : X, (∀ d : X, (∀ c ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → c + t • d ∈ closure (dom A)) →
        ⟪d, u⟫_ℝ ≤ 0) →
      ∀ r ∈ closure (InconsistentDR.Shadow.ran A), ∀ t : ℝ, 0 ≤ t →
        r + t • u ∈ closure (InconsistentDR.Shadow.ran A)) ∧
    (∀ u : X, (∀ d : X, (∀ c ∈ closure (InconsistentDR.Shadow.ran A), ∀ t : ℝ, 0 ≤ t →
          c + t • d ∈ closure (InconsistentDR.Shadow.ran A)) →
        ⟪d, u⟫_ℝ ≤ 0) →
      ∀ r ∈ closure (dom A), ∀ t : ℝ, 0 ≤ t → r + t • u ∈ closure (dom A)) := by
  -- a generic version for any monotone operator with a resolvent
  have gen : ∀ (B : X → Set X), IsMonotoneOp B → ∀ JB : X → X, IsResolvent 1 B JB →
      ∀ u : X, (∀ d : X, (∀ c ∈ closure (dom B), ∀ t : ℝ, 0 ≤ t →
          c + t • d ∈ closure (dom B)) → ⟪d, u⟫_ℝ ≤ 0) →
      ∀ r ∈ closure (InconsistentDR.Shadow.ran B), ∀ t : ℝ, 0 ≤ t →
        r + t • u ∈ closure (InconsistentDR.Shadow.ran B) := by
    intro B hB JB hJB u hu r hr t ht
    have hcv := InconsistentDR.Shadow.convex_closure_dom B hB JB hJB
    have hu' : ∀ d : X, (∀ c ∈ closure (dom B), ∀ t : ℝ, 0 ≤ t →
        c + t • d ∈ closure (dom B)) → ⟪d, t • u⟫_ℝ ≤ 0 := by
      intro d hd
      rw [real_inner_smul_right]
      exact mul_nonpos_of_nonneg_of_nonpos ht (hu d hd)
    have := map_mem_closure (f := fun z => z + t • u) (t := closure (InconsistentDR.Shadow.ran B))
      (by fun_prop) hr (fun z hz => by
        obtain ⟨x, hx⟩ := hz
        exact DR32Aux.core B hB JB hJB hcv (t • u) hu' x z hx)
    rwa [closure_closure] at this
  refine ⟨gen A hA.1 J hJ, ?_⟩
  intro u hu r hr t ht
  have e1 : InconsistentDR.Shadow.ran A = dom (DR32Aux.opInv A) := Set.ext fun _ => Iff.rfl
  have e2 : dom A = InconsistentDR.Shadow.ran (DR32Aux.opInv A) := Set.ext fun _ => Iff.rfl
  rw [e1] at hu
  rw [e2] at hr ⊢
  exact gen (DR32Aux.opInv A) (DR32Aux.opInv_mono A hA.1) _ (DR32Aux.opInv_res A J hJ) u hu r hr t ht
