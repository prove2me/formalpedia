-- Prove2me | solution 1 for MDPFinance.MeanVariance.mv_eq_mveq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T18:17:53.696785+00:00
-- url     : https://prove2.me/submissions/d4905bfc-59b7-488d-a1ac-ff70d3358cb8

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket

open MeasureTheory ProbabilityTheory

namespace S99MVEq

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- Lemma A: a linear combination of `R` that is a.s. constant has zero coefficients. -/
lemma coeff_zero (P : Measure Ω) [IsProbabilityMeasure P] {R : Ω → Fin d → ℝ}
    (hRL2 : ∀ k, MemLp (fun ω => R ω k) 2 P)
    (hcov : Matrix.PosDef (Matrix.of (fun j k =>
      ∫ ω, (R ω j - ∫ ω', R ω' j ∂P) * (R ω k - ∫ ω', R ω' k ∂P) ∂P)))
    (b : Fin d → ℝ) (c : ℝ) (h : ∀ᵐ ω ∂P, ∑ j, b j * R ω j = c) : b = 0 := by
  set m : Fin d → ℝ := fun j => ∫ ω', R ω' j ∂P with hm
  have hint : ∀ j, Integrable (fun ω => R ω j) P := fun j => (hRL2 j).integrable one_le_two
  have hc : c = ∑ j, b j * m j := by
    have h1 : ∫ ω, (∑ j, b j * R ω j) ∂P = ∫ ω, c ∂P := integral_congr_ae h
    rw [integral_finsetSum _ (fun j _ => (hint j).const_mul (b j))] at h1
    simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at h1
    rw [← h1]
  have h0 : ∀ᵐ ω ∂P, ∑ j, b j * (R ω j - m j) = 0 := by
    filter_upwards [h] with ω hω
    simp only [mul_sub, Finset.sum_sub_distrib, hω, hc, sub_self]
  have hL2 : ∀ j, MemLp (fun ω => R ω j - m j) 2 P := fun j => (hRL2 j).sub (memLp_const _)
  have hmv : Matrix.mulVec (Matrix.of (fun j k =>
      ∫ ω, (R ω j - ∫ ω', R ω' j ∂P) * (R ω k - ∫ ω', R ω' k ∂P) ∂P)) b = 0 := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    show ∑ i, (∫ ω, (R ω k - m k) * (R ω i - m i) ∂P) * b i = 0
    simp_rw [← integral_mul_const]
    have hI : ∀ j, Integrable (fun ω => (R ω k - m k) * (R ω j - m j) * b j) P :=
      fun j => ((hL2 k).integrable_mul (hL2 j)).mul_const (b j)
    rw [← integral_finsetSum _ (fun j _ => hI j)]
    have : ∀ᵐ ω ∂P, ∑ j, (R ω k - m k) * (R ω j - m j) * b j = 0 := by
      filter_upwards [h0] with ω hω
      have : ∑ j, (R ω k - m k) * (R ω j - m j) * b j
          = (R ω k - m k) * ∑ j, b j * (R ω j - m j) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring
      rw [this, hω, mul_zero]
    rw [integral_congr_ae this]; simp
  by_contra hb
  have := hcov.dotProduct_mulVec_pos hb
  rw [hmv, dotProduct_zero] at this
  exact lt_irrefl _ this

/-- Lemma B: independence + a.s. constant wealth after one step forces the wealth constant. -/
lemma step_const (P : Measure Ω) [IsProbabilityMeasure P] {Y : Ω → ℝ} {R : Ω → Fin d → ℝ}
    (hY : Measurable Y) (hRm : Measurable R) (hind : IndepFun Y R P)
    (hRL2 : ∀ k, MemLp (fun ω => R ω k) 2 P)
    (hcov : Matrix.PosDef (Matrix.of (fun j k =>
      ∫ ω, (R ω j - ∫ ω', R ω' j ∂P) * (R ω k - ∫ ω', R ω' k ∂P) ∂P)))
    (f : ℝ → Fin d → ℝ) (hf : Measurable f) (c : ℝ)
    (h : ∀ᵐ ω ∂P, Y ω + ∑ j, f (Y ω) j * R ω j = c) : ∀ᵐ ω ∂P, Y ω = c := by
  set S : Set (ℝ × (Fin d → ℝ)) := {p | p.1 + ∑ j, f p.1 j * p.2 j ≠ c} with hSdef
  have hFm : Measurable (fun p : ℝ × (Fin d → ℝ) => p.1 + ∑ j, f p.1 j * p.2 j) :=
    measurable_fst.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (hf.comp measurable_fst)).mul
        ((measurable_pi_apply j).comp measurable_snd))
  have hS : MeasurableSet S := (measurableSet_eq_fun hFm measurable_const).compl
  have h1 : P.map (fun ω => (Y ω, R ω)) S = 0 := by
    rw [Measure.map_apply (hY.prodMk hRm) hS]
    rw [ae_iff] at h
    simpa [hSdef] using h
  rw [hind.map_prod_eq_prod_map_map hY.aemeasurable hRm.aemeasurable,
    Measure.measure_prod_null hS] at h1
  have h2 : ∀ᵐ y ∂P.map Y, y = c := by
    filter_upwards [h1] with y hy
    have hy' : P.map R (Prod.mk y ⁻¹' S) = 0 := hy
    have hpre : MeasurableSet (Prod.mk y ⁻¹' S) := measurable_prodMk_left hS
    rw [Measure.map_apply hRm hpre] at hy'
    have hae : ∀ᵐ ω ∂P, ∑ j, f y j * R ω j = c - y := by
      rw [ae_iff]
      refine measure_mono_null (fun ω hω => ?_) hy'
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, hSdef] at hω ⊢
      intro h'; apply hω; rw [← h']; ring
    have hb := coeff_zero P hRL2 hcov (f y) (c - y) hae
    have hne : (∀ᵐ ω ∂P, ∑ j, f y j * R ω j = c - y) := hae
    obtain ⟨ω, hω⟩ := hne.exists
    simp [hb] at hω
    linarith
  exact ae_of_ae_map hY.aemeasurable h2


open MDPFinance.MeanVariance

lemma S0_succ (M : MVMarket Ω d) (n : ℕ) : M.S0 (n+1) = M.S0 n * (1 + M.i (n+1)) := by
  simp [MVMarket.S0, Finset.prod_range_succ]

lemma S0_zero (M : MVMarket Ω d) : M.S0 0 = 1 := by simp [MVMarket.S0]

lemma S0_pos (M : MVMarket Ω d) : ∀ n, n ≤ M.N → 0 < M.S0 n
  | 0, _ => by simp [MVMarket.S0]
  | n+1, h => by
    rw [S0_succ]; exact mul_pos (S0_pos M n (by omega)) (M.hi_pos (n+1) (by omega) h)

lemma tw_succ (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (ω : Ω) :
    ∀ k n x, M.terminalWealth π (k+1) n x ω = (1 + M.i (n+k+1)) *
      (M.terminalWealth π k n x ω +
        ∑ j, π (n+k) (M.terminalWealth π k n x ω) j * M.R (n+k+1) ω j)
  | 0, n, x => by simp [MVMarket.terminalWealth]
  | k+1, n, x => by
    show M.terminalWealth π (k+1) (n+1) _ ω = _
    rw [tw_succ M π ω k (n+1)]
    have e : n + 1 + k = n + (k+1) := by omega
    rw [e]
    rfl

abbrev mS (M : MVMarket Ω d) (k : ℕ) : MeasurableSpace Ω :=
  ⨆ j ∈ {j : Fin M.N | j.val < k},
    (inferInstance : MeasurableSpace (Fin d → ℝ)).comap (M.R (j.val + 1))

lemma mS_mono (M : MVMarket Ω d) {k k' : ℕ} (h : k ≤ k') : mS M k ≤ mS M k' :=
  biSup_mono fun j (hj : j.val < k) => (show j.val < k' by omega)

lemma mS_le (M : MVMarket Ω d) (k : ℕ) : mS M k ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun j _ => (M.hR_meas (j.val+1) (by omega) (Nat.succ_le_of_lt j.isLt)).comap_le

lemma X_meas (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k, k < M.N → Measurable (π k)) :
    ∀ k, k ≤ M.N → Measurable[mS M k] (fun ω => M.terminalWealth π k 0 M.x0 ω)
  | 0, _ => by
    show Measurable[mS M 0] (fun _ => M.x0)
    exact measurable_const
  | k+1, hk => by
    have hR : Measurable[mS M (k+1)] (M.R (k+1)) := by
      have := comap_measurable (m := (inferInstance : MeasurableSpace (Fin d → ℝ))) (M.R (k+1))
      refine this.mono ?_ le_rfl
      exact le_iSup₂ (f := fun (j : Fin M.N) (_ : j ∈ {j : Fin M.N | j.val < k+1}) =>
        (inferInstance : MeasurableSpace (Fin d → ℝ)).comap (M.R (j.val + 1)))
        (⟨k, hk⟩ : Fin M.N) (show k < k + 1 by omega)
    have hX : Measurable[mS M (k+1)] (fun ω => M.terminalWealth π k 0 M.x0 ω) :=
      (X_meas M π hπ k (by omega)).mono (mS_mono M (by omega)) le_rfl
    have e : (fun ω => M.terminalWealth π (k+1) 0 M.x0 ω) = fun ω => (1 + M.i (k+1)) *
        (M.terminalWealth π k 0 M.x0 ω +
          ∑ j, π k (M.terminalWealth π k 0 M.x0 ω) j * M.R (k+1) ω j) := by
      funext ω; rw [tw_succ]; simp only [zero_add]
    rw [e]
    exact measurable_const.mul (hX.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((hπ k (by omega)).comp hX)).mul
        ((measurable_pi_apply j).comp hR)))

lemma X_indep (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k, k < M.N → Measurable (π k)) (k : ℕ) (hk : k < M.N) :
    IndepFun (fun ω => M.terminalWealth π k 0 M.x0 ω) (M.R (k+1)) M.measIP := by
  have hI := (iIndepFun_iff_iIndep (fun _ => (inferInstance : MeasurableSpace (Fin d → ℝ)))
    _ _).1 M.hR_indep
  have h := indep_iSup_of_disjoint
    (fun j => (M.hR_meas (j.val+1) (by omega) (Nat.succ_le_of_lt j.isLt)).comap_le) hI
    (S := {j : Fin M.N | j.val < k}) (T := {⟨k, hk⟩})
    (by rw [Set.disjoint_singleton_right]; simp)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right
    (indep_of_indep_of_le_left h ((X_meas M π hπ k hk.le).comap_le)) ?_
  exact le_iSup₂ (f := fun (j : Fin M.N) (_ : j ∈ ({⟨k, hk⟩} : Set (Fin M.N))) =>
    (inferInstance : MeasurableSpace (Fin d → ℝ)).comap (M.R (j.val + 1))) ⟨k, hk⟩ rfl

lemma no_arb (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k, k < M.N → Measurable (π k)) (C : ℝ)
    (h : ∀ᵐ ω ∂M.measIP, M.terminalWealth π M.N 0 M.x0 ω = C) : C = M.x0 * M.S0 M.N := by
  have := M.isProb
  have hSN := S0_pos M M.N le_rfl
  have key : ∀ j, j ≤ M.N → ∀ᵐ ω ∂M.measIP,
      M.terminalWealth π (M.N - j) 0 M.x0 ω = C * M.S0 (M.N - j) / M.S0 M.N := by
    intro j
    induction j with
    | zero =>
      intro _
      filter_upwards [h] with ω hω
      rw [Nat.sub_zero, hω, mul_div_cancel_right₀ _ hSN.ne']
    | succ j ih =>
      intro hj
      have hk : M.N - j = (M.N - (j+1)) + 1 := by omega
      have h1 := ih (by omega)
      rw [hk] at h1
      rw [show M.N - (j+1) = M.N - (j+1) from rfl] at h1 ⊢
      generalize hkdef : M.N - (j+1) = k at h1 ⊢
      have hkN : k < M.N := by omega
      have hpos := M.hi_pos (k+1) (by omega) (by omega)
      apply step_const M.measIP ((X_meas M π hπ k hkN.le).mono (mS_le M k) le_rfl)
        (M.hR_meas (k+1) (by omega) (by omega)) (X_indep M π hπ k hkN)
        (M.hR_L2 (k+1) (by omega) (by omega)) (M.hCov_posdef (k+1) (by omega) (by omega))
        (π k) (hπ k hkN)
      filter_upwards [h1] with ω hω
      rw [tw_succ, S0_succ] at hω
      simp only [zero_add] at hω
      apply mul_left_cancel₀ hpos.ne'
      rw [hω]; ring
  obtain ⟨ω, hω⟩ := (key M.N le_rfl).exists
  rw [Nat.sub_self, S0_zero] at hω
  simp only [MVMarket.terminalWealth] at hω
  rw [hω]; field_simp

noncomputable def scale (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (α : ℝ) :
    ℕ → ℝ → (Fin d → ℝ) :=
  fun n x' => α • π n (M.x0 * M.S0 n + (x' - M.x0 * M.S0 n) / α)

lemma tw_scale (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) {α : ℝ} (hα : α ≠ 0) (ω : Ω) :
    ∀ k n x x', x' - M.x0 * M.S0 n = α * (x - M.x0 * M.S0 n) →
    M.terminalWealth (scale M π α) k n x' ω - M.x0 * M.S0 (n+k) =
      α * (M.terminalWealth π k n x ω - M.x0 * M.S0 (n+k))
  | 0, n, x, x', h => by simpa [MVMarket.terminalWealth] using h
  | k+1, n, x, x', h => by
    simp only [MVMarket.terminalWealth]
    rw [show n + (k+1) = n + 1 + k by omega]
    apply tw_scale M π hα ω k (n+1)
    have hx : M.x0 * M.S0 n + (x' - M.x0 * M.S0 n) / α = x := by
      rw [h, mul_div_cancel_left₀ _ hα]; ring
    simp only [scale, hx, Pi.smul_apply, smul_eq_mul, S0_succ]
    have : ∑ j, α * π n x j * M.R (n+1) ω j = α * ∑ j, π n x j * M.R (n+1) ω j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this]; linear_combination (1 + M.i (n+1)) * h

lemma tw_scale0 (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) {α : ℝ} (hα : α ≠ 0) (ω : Ω) :
    M.terminalWealth (scale M π α) M.N 0 M.x0 ω = M.x0 * M.S0 M.N +
      α * (M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N) := by
  have := tw_scale M π hα ω M.N 0 M.x0 M.x0 (by rw [S0_zero]; ring)
  rw [zero_add] at this; linarith

lemma var_eq (P : Measure Ω) [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P) :
    ∫ ω, X ω ^ 2 ∂P - (∫ ω, X ω ∂P) ^ 2 = ∫ ω, (X ω - ∫ ω', X ω' ∂P) ^ 2 ∂P := by
  have hi : Integrable X P := hX.integrable one_le_two
  have hi2 := hX.integrable_sq
  set m := ∫ ω', X ω' ∂P
  have : (fun ω => (X ω - m) ^ 2) = fun ω => X ω ^ 2 - (2 * m) * X ω + m ^ 2 := by
    funext ω; ring
  have hA : Integrable (fun ω => X ω ^ 2 - (2 * m) * X ω) P := hi2.sub (hi.const_mul _)
  have hB : Integrable (fun ω => (2 * m) * X ω) P := hi.const_mul _
  rw [this, integral_add hA (integrable_const _), integral_sub hi2 hB, integral_const_mul,
    integral_const]
  simp; ring

lemma adm_memLp (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π) :
    MemLp (fun ω => M.terminalWealth π M.N 0 M.x0 ω) 2 M.measIP := by
  have := h.2; simpa using this

lemma adm_meas (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π) :
    ∀ k, k < M.N → Measurable (π k) := fun k hk => h.1 k (Nat.zero_le _) hk

lemma varXN_eq (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π) :
    M.varXN π = ∫ ω, (M.terminalWealth π M.N 0 M.x0 ω - M.meanXN π) ^ 2 ∂M.measIP := by
  have := M.isProb
  exact var_eq M.measIP (adm_memLp M h)

lemma varXN_nonneg (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π) :
    0 ≤ M.varXN π := by
  rw [varXN_eq M h]; exact integral_nonneg fun _ => sq_nonneg _

lemma adm_scale (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π)
    {α : ℝ} (hα : α ≠ 0) : M.IsAdmissible 0 (scale M π α) := by
  refine ⟨fun k _ hk => ?_, ?_⟩
  · have := adm_meas M h k hk
    show Measurable (fun x' => α • π k (M.x0 * M.S0 k + (x' - M.x0 * M.S0 k) / α))
    have hg : Measurable (fun x' : ℝ => M.x0 * M.S0 k + (x' - M.x0 * M.S0 k) / α) := by fun_prop
    exact (this.comp hg).const_smul α
  · have := M.isProb
    have h2 := adm_memLp M h
    have hs : MemLp (fun ω => M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N) 2 M.measIP :=
      h2.sub (memLp_const _)
    have hm : MemLp (fun ω => α * (M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N)) 2
      M.measIP := hs.const_mul α
    have h3 : MemLp (fun ω => M.x0 * M.S0 M.N +
        α * (M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N)) 2 M.measIP :=
      (MemLp.add (memLp_const (M.x0 * M.S0 M.N) : MemLp (fun _ : Ω => M.x0 * M.S0 M.N) 2 M.measIP) hm :)
    have e : (fun ω => M.terminalWealth (scale M π α) (M.N - 0) 0 M.x0 ω) = fun ω =>
        M.x0 * M.S0 M.N + α * (M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N) := by
      funext ω; rw [Nat.sub_zero, tw_scale0 M π hα]
    show MemLp (fun ω => M.terminalWealth (scale M π α) (M.N - 0) 0 M.x0 ω) 2 M.measIP
    rw [e]; exact h3

lemma mean_scale (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π)
    {α : ℝ} (hα : α ≠ 0) : M.meanXN (scale M π α) =
      M.x0 * M.S0 M.N + α * (M.meanXN π - M.x0 * M.S0 M.N) := by
  have := M.isProb
  have hi := (adm_memLp M h).integrable one_le_two
  unfold MVMarket.meanXN
  simp_rw [tw_scale0 M π hα]
  have hA : Integrable (fun ω => α * (M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N))
    M.measIP := (hi.sub (integrable_const _)).const_mul _
  have hB : Integrable (fun ω => M.terminalWealth π M.N 0 M.x0 ω - M.x0 * M.S0 M.N)
    M.measIP := hi.sub (integrable_const _)
  rw [integral_add (integrable_const _) hA, integral_const, integral_const_mul α,
    integral_sub hi (integrable_const _), integral_const]
  simp

lemma var_scale (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π)
    {α : ℝ} (hα : α ≠ 0) : M.varXN (scale M π α) = α ^ 2 * M.varXN π := by
  rw [varXN_eq M (adm_scale M h hα), varXN_eq M h, mean_scale M h hα]
  simp_rw [tw_scale0 M π hα]
  rw [← integral_const_mul]
  congr 1; funext ω; ring

lemma var_zero_ae (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π)
    (hv : M.varXN π = 0) :
    ∀ᵐ ω ∂M.measIP, M.terminalWealth π M.N 0 M.x0 ω = M.meanXN π := by
  have := M.isProb
  rw [varXN_eq M h] at hv
  have hint : Integrable (fun ω => (M.terminalWealth π M.N 0 M.x0 ω - M.meanXN π) ^ 2)
      M.measIP := ((adm_memLp M h).sub (memLp_const _)).integrable_sq
  rw [integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint] at hv
  filter_upwards [hv] with ω hω
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero] at hω
  exact hω

/-- Scaling a policy with mean above `μ` down to mean exactly `μ`. -/
lemma scale_down (M : MVMarket Ω d) {π : ℕ → ℝ → (Fin d → ℝ)} (h : M.IsAdmissible 0 π)
    (hm : M.μ < M.meanXN π) : ∃ α : ℝ, 0 < α ∧ α < 1 ∧ M.IsAdmissible 0 (scale M π α) ∧
      M.meanXN (scale M π α) = M.μ ∧ M.varXN (scale M π α) = α ^ 2 * M.varXN π := by
  have hc : M.x0 * M.S0 M.N < M.μ := M.hμ
  have hpos : 0 < M.meanXN π - M.x0 * M.S0 M.N := by linarith
  refine ⟨(M.μ - M.x0 * M.S0 M.N) / (M.meanXN π - M.x0 * M.S0 M.N), div_pos (by linarith) hpos,
    (div_lt_one hpos).2 (by linarith), ?_⟩
  have hα : (M.μ - M.x0 * M.S0 M.N) / (M.meanXN π - M.x0 * M.S0 M.N) ≠ 0 :=
    (div_pos (by linarith) hpos).ne'
  refine ⟨adm_scale M h hα, ?_, var_scale M h hα⟩
  rw [mean_scale M h hα, div_mul_cancel₀ _ hpos.ne']; ring

end S99MVEq

open MeasureTheory ProbabilityTheory in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (M : MDPFinance.MeanVariance.MVMarket Ω d) (πstar : ℕ → ℝ → (Fin d → ℝ)) :
    M.IsOptimalMV πstar ↔ M.IsOptimalMVeq πstar := by
  constructor
  · rintro ⟨hadm, hmean, hopt⟩
    refine ⟨hadm, ?_, fun π hπ hm => hopt π hπ hm.ge⟩
    by_contra hne
    have hlt : M.μ < M.meanXN πstar := lt_of_le_of_ne hmean (Ne.symm hne)
    obtain ⟨α, hα0, hα1, hadm', hm', hv'⟩ := S99MVEq.scale_down M hadm hlt
    have h1 := hopt _ hadm' hm'.ge
    rw [hv'] at h1
    have hnn := S99MVEq.varXN_nonneg M hadm
    have hα2 : α ^ 2 < 1 := by nlinarith
    have hv0 : M.varXN πstar = 0 := by nlinarith
    have hae := S99MVEq.var_zero_ae M hadm hv0
    have := S99MVEq.no_arb M πstar (S99MVEq.adm_meas M hadm) _ hae
    have hc : M.x0 * M.S0 M.N < M.μ := M.hμ
    linarith
  · rintro ⟨hadm, hmean, hopt⟩
    refine ⟨hadm, hmean.ge, fun π hπ hm => ?_⟩
    rcases hm.lt_or_eq with hlt | heq
    · obtain ⟨α, hα0, hα1, hadm', hm', hv'⟩ := S99MVEq.scale_down M hπ hlt
      have h1 := hopt _ hadm' hm'
      have hnn := S99MVEq.varXN_nonneg M hπ
      have ha2 : α ^ 2 ≤ 1 := by nlinarith
      have : α ^ 2 * M.varXN π ≤ M.varXN π := by nlinarith [mul_le_mul_of_nonneg_right ha2 hnn]
      linarith
    · exact hopt π hπ heq.symm
