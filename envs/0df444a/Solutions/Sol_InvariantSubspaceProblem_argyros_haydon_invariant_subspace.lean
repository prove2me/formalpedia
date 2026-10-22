-- Prove2me | solution 1 for InvariantSubspaceProblem.argyros_haydon_invariant_subspace
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:41:04.133102+00:00
-- url     : https://prove2.me/submissions/5ae0d9d5-1c12-4471-bb2a-6587032c5068
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InvariantSubspaceProblem_Defs
import Theorems.Thm_InvariantSubspaceProblem_argyros_haydon_scalar_plus_compact

set_option linter.all false

namespace InvariantSubspaceProblem

open Filter Topology

section Hilden

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- Quasinilpotent case (Hilden's argument). -/
lemma hyper_of_quasinilpotent' (K : E →L[𝕜] E) (hK : IsCompactOperator K) (hK0 : K ≠ 0)
    (hq : Tendsto (fun n : ℕ => ‖K ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 0)) : HasNontrivialClosedHyperinvariantSubspace K := by
  by_contra hno
  -- density of commutant orbits
  have hdense : ∀ y : E, y ≠ 0 → ∀ x : E, ∀ ε > 0,
      ∃ A : E →L[𝕜] E, A * K = K * A ∧ ‖A y - x‖ < ε := by
    intro y hy x ε hε
    let N : Submodule 𝕜 E :=
      { carrier := {z | ∃ A : E →L[𝕜] E, A * K = K * A ∧ A y = z}
        add_mem' := by
          rintro _ _ ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩
          exact ⟨A + B, by rw [add_mul, mul_add, hA, hB], by simp⟩
        zero_mem' := ⟨0, by simp, by simp⟩
        smul_mem' := by
          rintro c _ ⟨A, hA, rfl⟩
          exact ⟨c • A, by rw [smul_mul_assoc, mul_smul_comm, hA], by simp⟩ }
    have hyN : y ∈ N := ⟨1, by simp, by simp⟩
    have hS : N.topologicalClosure = ⊤ := by
      by_contra hS
      apply hno
      refine ⟨N.topologicalClosure, N.isClosed_topologicalClosure, ?_, hS, ?_⟩
      · intro h
        have : y ∈ N.topologicalClosure := N.le_topologicalClosure hyN
        rw [h] at this
        exact hy ((Submodule.mem_bot 𝕜).1 this)
      · intro B hB z hz
        have hmap : Set.MapsTo B (N : Set E) (N : Set E) := by
          rintro _ ⟨A, hA, rfl⟩
          refine ⟨B * A, ?_, rfl⟩
          rw [mul_assoc, hA, ← mul_assoc, hB, mul_assoc]
        have hz' : z ∈ closure (N : Set E) := by
          rw [← N.topologicalClosure_coe]; exact hz
        have := map_mem_closure B.continuous hz' hmap
        rw [← N.topologicalClosure_coe] at this
        exact this
    have hx : x ∈ closure (N : Set E) := by
      rw [← N.topologicalClosure_coe, hS]; trivial
    obtain ⟨b, ⟨A, hA, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hx ε hε
    exact ⟨A, hA, by rw [← dist_eq_norm, dist_comm]; exact hb⟩
  -- choose the base point
  obtain ⟨x0, hx0⟩ : ∃ x0, K x0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hK0 (ContinuousLinearMap.ext h)
  have hx0n : x0 ≠ 0 := fun h => hx0 (by simp [h])
  have hr : 0 < ‖K‖ := norm_pos_iff.2 hK0
  have hnx0 : 0 < ‖x0‖ := norm_pos_iff.2 hx0n
  have hnKx0 : 0 < ‖K x0‖ := norm_pos_iff.2 hx0
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = min ‖x0‖ (‖K x0‖ / ‖K‖) / 2 := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hρ1 : ρ ≤ ‖x0‖ / 2 := by
    rw [hρdef]; have := min_le_left ‖x0‖ (‖K x0‖ / ‖K‖); linarith
  have hρ2 : ‖K‖ * ρ ≤ ‖K x0‖ / 2 := by
    rw [hρdef]
    have := min_le_right ‖x0‖ (‖K x0‖ / ‖K‖)
    have h3 : ‖K‖ * (‖K x0‖ / ‖K‖) = ‖K x0‖ := by field_simp
    nlinarith
  -- the compact set C
  set C := closure (K '' Metric.closedBall x0 ρ) with hCdef
  have hCc : IsCompact C := by
    refine (hK.isCompact_closure_image_closedBall (‖x0‖ + ρ)).of_isClosed_subset isClosed_closure ?_
    apply closure_mono
    apply Set.image_mono
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    rw [dist_zero_right]
    have := norm_le_norm_add_norm_sub' z x0
    rw [dist_eq_norm] at hz
    linarith
  have hC0 : ∀ c ∈ C, c ≠ 0 := by
    have hsub : C ⊆ {z : E | ‖K x0‖ / 2 ≤ ‖z‖} := by
      apply closure_minimal _ (isClosed_le continuous_const continuous_norm)
      rintro _ ⟨z, hz, rfl⟩
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      show ‖K x0‖ / 2 ≤ ‖K z‖
      have h1 : ‖K x0 - K z‖ ≤ ‖K‖ * ρ := by
        rw [← map_sub]
        calc ‖K (x0 - z)‖ ≤ ‖K‖ * ‖x0 - z‖ := K.le_opNorm _
          _ ≤ ‖K‖ * ρ := by rw [norm_sub_rev]; exact mul_le_mul_of_nonneg_left hz hr.le
      have := norm_sub_norm_le (K x0) (K z)
      linarith
    intro c hc h0
    have := hsub hc
    simp only [Set.mem_ofPred_eq, h0, norm_zero] at this
    linarith
  -- finite subcover
  let ι := {A : E →L[𝕜] E // A * K = K * A}
  let U : ι → Set E := fun A => {z | ‖(A : E →L[𝕜] E) z - x0‖ < ρ}
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt (continuous_norm.comp (i.1.continuous.sub continuous_const)) continuous_const
  have hCU : C ⊆ ⋃ i, U i := by
    intro c hc
    obtain ⟨A, hA, hAc⟩ := hdense c (hC0 c hc) x0 ρ hρ
    exact Set.mem_iUnion.2 ⟨⟨A, hA⟩, hAc⟩
  obtain ⟨t, ht⟩ := hCc.elim_finite_subcover U hUo hCU
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + ∑ i ∈ t, ‖(i : E →L[𝕜] E)‖ := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hMdef]; have := Finset.sum_nonneg (fun i (_ : i ∈ t) => norm_nonneg (i : E →L[𝕜] E))
    linarith
  have hMi : ∀ i ∈ t, ‖(i : E →L[𝕜] E)‖ ≤ M := by
    intro i hi
    rw [hMdef]
    have := Finset.single_le_sum (f := fun i : ι => ‖(i : E →L[𝕜] E)‖)
      (fun i _ => norm_nonneg _) hi
    linarith
  -- the iteration
  have hiter : ∀ n : ℕ, ∃ P : E →L[𝕜] E, P * K = K * P ∧ ‖P‖ ≤ M ^ n ∧
      ‖P ((K ^ n) x0) - x0‖ < ρ := by
    intro n
    induction n with
    | zero =>
      refine ⟨1, by simp, ?_, by simpa using hρ⟩
      rw [pow_zero]; exact ContinuousLinearMap.norm_id_le
    | succ n ih =>
      obtain ⟨P, hPK, hPn, hPd⟩ := ih
      set xn := P ((K ^ n) x0) with hxn
      have hKxn : K xn ∈ C := by
        apply subset_closure
        refine ⟨xn, ?_, rfl⟩
        rw [Metric.mem_closedBall, dist_eq_norm]; exact hPd.le
      obtain ⟨i, hi, hiU⟩ := Set.mem_iUnion₂.1 (ht hKxn)
      refine ⟨(i : E →L[𝕜] E) * P, ?_, ?_, ?_⟩
      · rw [mul_assoc, hPK, ← mul_assoc, i.2, mul_assoc]
      · calc ‖(i : E →L[𝕜] E) * P‖ ≤ ‖(i : E →L[𝕜] E)‖ * ‖P‖ := norm_mul_le _ _
          _ ≤ M * M ^ n := mul_le_mul (hMi i hi) hPn (norm_nonneg _) (by positivity)
          _ = M ^ (n + 1) := by ring
      · have hcomm : P (K ((K ^ n) x0)) = K (P ((K ^ n) x0)) := by
          have := congrArg (fun F : E →L[𝕜] E => F ((K ^ n) x0)) hPK
          simpa only [ContinuousLinearMap.mul_apply] using this
        have : ((i : E →L[𝕜] E) * P) ((K ^ (n + 1)) x0) = (i : E →L[𝕜] E) (K xn) := by
          rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm]
        rw [this]; exact hiU
  obtain ⟨n, hn', hn1⟩ :=
    ((hq.eventually (gt_mem_nhds (show (0:ℝ) < 1 / (2 * M) by positivity))).and
      (eventually_ge_atTop 1)).exists
  have hn0 : n ≠ 0 := by omega
  have hKn : ‖K ^ n‖ ≤ (1 / (2 * M)) ^ n := by
    have h1 : (‖K ^ n‖ ^ (1 / n : ℝ)) ^ n = ‖K ^ n‖ := by
      rw [one_div]; exact Real.rpow_inv_natCast_pow (norm_nonneg _) hn0
    rw [← h1]
    exact pow_le_pow_left₀ (by positivity) hn'.le n
  obtain ⟨P, -, hPn, hPd⟩ := hiter n
  have hup : ‖P ((K ^ n) x0)‖ ≤ (1 / 2) ^ n * ‖x0‖ := by
    calc ‖P ((K ^ n) x0)‖ ≤ ‖P‖ * ‖(K ^ n) x0‖ := P.le_opNorm _
      _ ≤ ‖P‖ * (‖K ^ n‖ * ‖x0‖) := mul_le_mul_of_nonneg_left ((K ^ n).le_opNorm _) (norm_nonneg _)
      _ ≤ M ^ n * ((1 / (2 * M)) ^ n * ‖x0‖) := by
          apply mul_le_mul hPn (mul_le_mul_of_nonneg_right hKn hnx0.le) (by positivity)
            (by positivity)
      _ = (M * (1 / (2 * M))) ^ n * ‖x0‖ := by rw [mul_pow]; ring
      _ = (1 / 2) ^ n * ‖x0‖ := by
          congr 2; field_simp
  have hhalf : (1 / 2 : ℝ) ^ n ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn1
      _ = 1 / 2 := by norm_num
  have hlow := norm_sub_norm_le x0 (P ((K ^ n) x0))
  rw [norm_sub_rev] at hlow
  have : (1 / 2 : ℝ) ^ n * ‖x0‖ ≤ 1 / 2 * ‖x0‖ := mul_le_mul_of_nonneg_right hhalf hnx0.le
  linarith

end Hilden

section Cx

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Precomposition on complex-valued real functionals: a complex operator. -/
noncomputable def cxOp (T : E →L[ℝ] E) : (E →L[ℝ] ℂ) →L[ℂ] (E →L[ℝ] ℂ) :=
  LinearMap.mkContinuous
    { toFun := fun φ => φ.comp T
      map_add' := fun φ ψ => ContinuousLinearMap.add_comp φ ψ T
      map_smul' := fun c φ => ContinuousLinearMap.smul_comp c φ T }
    ‖T‖ (fun φ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [mul_comm]; exact φ.opNorm_comp_le T)

lemma cxOp_apply (T : E →L[ℝ] E) (φ : E →L[ℝ] ℂ) : cxOp T φ = φ.comp T := rfl

lemma cxOp_mul (S T : E →L[ℝ] E) : cxOp (S * T) = cxOp T * cxOp S := by
  ext φ x; rfl

lemma cxOp_one : cxOp (1 : E →L[ℝ] E) = 1 := by
  ext φ x; rfl

lemma cxOp_add (S T : E →L[ℝ] E) : cxOp (S + T) = cxOp S + cxOp T := by
  ext φ x; simp [cxOp_apply]

lemma cxOp_sub (S T : E →L[ℝ] E) : cxOp (S - T) = cxOp S - cxOp T := by
  ext φ x; simp [cxOp_apply]

lemma cxOp_smul (a : ℝ) (T : E →L[ℝ] E) : cxOp (a • T) = (a : ℂ) • cxOp T := by
  ext φ x; simp [cxOp_apply, Complex.real_smul]

lemma cxOp_pow (T : E →L[ℝ] E) (n : ℕ) : cxOp (T ^ n) = cxOp T ^ n := by
  induction n with
  | zero => simp [cxOp_one]
  | succ n ih => rw [pow_succ, cxOp_mul, ih, pow_succ']

lemma cxOp_isUnit {T : E →L[ℝ] E} (h : IsUnit T) : IsUnit (cxOp T) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨cxOp u, cxOp ↑u⁻¹, ?_, ?_⟩, rfl⟩
  · rw [← cxOp_mul, u.inv_mul, cxOp_one]
  · rw [← cxOp_mul, u.mul_inv, cxOp_one]

lemma norm_le_cxOp (T : E →L[ℝ] E) : ‖T‖ ≤ ‖cxOp T‖ := by
  refine T.opNorm_le_bound (norm_nonneg (cxOp T)) (fun x => ?_)
  obtain ⟨g, hg, hgx⟩ := exists_dual_vector'' ℝ (T x)
  let φ : E →L[ℝ] ℂ := Complex.ofRealCLM.comp g
  have hφ : ‖φ‖ ≤ 1 := by
    calc ‖φ‖ ≤ ‖Complex.ofRealCLM‖ * ‖g‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * 1 := by rw [Complex.ofRealCLM_norm]; exact mul_le_mul_of_nonneg_left hg zero_le_one
      _ = 1 := by norm_num
  have h1 : ‖T x‖ = ‖(cxOp T φ) x‖ := by
    rw [cxOp_apply, ContinuousLinearMap.comp_apply]
    simp only [φ, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, hgx, Complex.norm_real,
      Real.norm_eq_abs, abs_norm]
    simp
  rw [h1]
  calc ‖(cxOp T φ) x‖ ≤ ‖cxOp T φ‖ * ‖x‖ := (cxOp T φ).le_opNorm x
    _ ≤ (‖cxOp T‖ * ‖φ‖) * ‖x‖ := mul_le_mul_of_nonneg_right ((cxOp T).le_opNorm φ) (norm_nonneg _)
    _ ≤ (‖cxOp T‖ * 1) * ‖x‖ := by gcongr
    _ = ‖cxOp T‖ * ‖x‖ := by ring

end Cx

section General

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

lemma restrictScalars_pow (K : E →L[𝕜] E) (n : ℕ) :
    (K ^ n).restrictScalars ℝ = (K.restrictScalars ℝ) ^ n := by
  induction n with
  | zero => ext x; rfl
  | succ n ih => rw [pow_succ, pow_succ, ← ih]; ext x; rfl

lemma isUnit_restrictScalars {Q : E →L[𝕜] E} (h : IsUnit Q) : IsUnit (Q.restrictScalars ℝ) := by
  obtain ⟨u, rfl⟩ := h
  refine ⟨⟨(u : E →L[𝕜] E).restrictScalars ℝ, (↑u⁻¹ : E →L[𝕜] E).restrictScalars ℝ, ?_, ?_⟩, rfl⟩
  · ext x
    show (u : E →L[𝕜] E) ((↑u⁻¹ : E →L[𝕜] E) x) = x
    rw [← ContinuousLinearMap.mul_apply, u.mul_inv]; rfl
  · ext x
    show (↑u⁻¹ : E →L[𝕜] E) ((u : E →L[𝕜] E) x) = x
    rw [← ContinuousLinearMap.mul_apply, u.inv_mul]; rfl

theorem hyper_general (hinf : ¬ FiniteDimensional 𝕜 E) (K : E →L[𝕜] E)
    (hK : IsCompactOperator K) (hK0 : K ≠ 0) : HasNontrivialClosedHyperinvariantSubspace K := by
  set Kr := K.restrictScalars ℝ with hKr
  set Kt := cxOp Kr with hKt
  by_cases hsr : spectralRadius ℂ Kt = 0
  · apply hyper_of_quasinilpotent' K hK hK0
    have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius Kt
    rw [hsr] at hG
    have hG' : Tendsto (fun n : ℕ => ‖Kt ^ n‖ ^ (1 / n : ℝ)) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hG
      refine this.congr (fun n => ?_)
      simp only [Function.comp_apply]
      exact ENNReal.toReal_ofReal (by positivity)
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hG'
    apply Real.rpow_le_rpow (norm_nonneg _) _ (by positivity)
    calc ‖K ^ n‖ = ‖(K ^ n).restrictScalars ℝ‖ := (ContinuousLinearMap.norm_restrictScalars _).symm
      _ = ‖Kr ^ n‖ := by rw [restrictScalars_pow]
      _ ≤ ‖cxOp (Kr ^ n)‖ := norm_le_cxOp _
      _ = ‖Kt ^ n‖ := by rw [cxOp_pow]
  · obtain ⟨l, hl, hl0⟩ : ∃ l ∈ spectrum ℂ Kt, l ≠ 0 := by
      by_contra h
      push Not at h
      apply hsr
      refine le_antisymm (iSup₂_le fun μ hμ => by simp [h μ hμ]) bot_le
    set s : ℝ := 2 * l.re with hs
    set p : ℝ := Complex.normSq l with hp
    have hp0 : 0 < p := Complex.normSq_pos.2 hl0
    set K' : E →L[𝕜] E := K * K - ((s : ℝ) : 𝕜) • K with hK'
    set Q : E →L[𝕜] E := K' + ((p : ℝ) : 𝕜) • 1 with hQ
    -- Q is not invertible
    have hQu : ¬ IsUnit Q := by
      intro hu
      have h1 := cxOp_isUnit (isUnit_restrictScalars hu)
      have h2 : cxOp (Q.restrictScalars ℝ) = Kt * Kt - (s : ℂ) • Kt + (p : ℂ) • 1 := by
        have : Q.restrictScalars ℝ = Kr * Kr - s • Kr + p • 1 := by
          ext x
          simp only [hQ, hK', Kr, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.add_apply,
            ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.mul_apply,
            ContinuousLinearMap.one_apply, RCLike.real_smul_eq_coe_smul (K := 𝕜)]
        rw [this, cxOp_add, cxOp_sub, cxOp_smul, cxOp_smul, cxOp_mul, cxOp_one]
      have h3 : Kt * Kt - (s : ℂ) • Kt + (p : ℂ) • 1 =
          (l • (1 : (E →L[ℝ] ℂ) →L[ℂ] (E →L[ℝ] ℂ)) - Kt) *
            ((starRingEnd ℂ l) • (1 : (E →L[ℝ] ℂ) →L[ℂ] (E →L[ℝ] ℂ)) - Kt) := by
        have hs' : (s : ℂ) = l + starRingEnd ℂ l := by
          apply Complex.ext <;> simp [hs, two_mul]
        have hp' : (p : ℂ) = l * starRingEnd ℂ l := by
          rw [Complex.mul_conj]
        rw [hs', hp']
        refine ContinuousLinearMap.ext fun φ => ?_
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply, map_sub, map_smul]
        module
      rw [h2, h3] at h1
      have hc : Commute (l • (1 : (E →L[ℝ] ℂ) →L[ℂ] (E →L[ℝ] ℂ)) - Kt)
          ((starRingEnd ℂ l) • (1 : (E →L[ℝ] ℂ) →L[ℂ] (E →L[ℝ] ℂ)) - Kt) := by
        refine ContinuousLinearMap.ext fun φ => ?_
        simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, map_sub, map_smul]
        module
      have h4 := ((hc.isUnit_mul_iff).1 h1).1
      apply spectrum.mem_iff.1 hl
      rw [Algebra.algebraMap_eq_smul_one]
      exact h4
    have hK'c : IsCompactOperator K' := by
      have h1 : IsCompactOperator (K * K) := by
        have := hK.comp_clm K
        simpa [ContinuousLinearMap.coe_mul] using this
      have := h1.sub (hK.smul ((s : ℝ) : 𝕜))
      simpa [hK'] using this
    have hμ : -((p : ℝ) : 𝕜) ≠ 0 := by
      simpa using hp0.ne'
    rcases hK'c.hasEigenvalue_or_mem_resolventSet hμ with he | hres
    · obtain ⟨v, hv⟩ := he.exists_hasEigenvector
      have hKv : K' v = -((p : ℝ) : 𝕜) • v := Module.End.mem_eigenspace_iff.1 hv.1
      refine ⟨LinearMap.ker (Q : E →ₗ[𝕜] E), Q.isClosed_ker, ?_, ?_, ?_⟩
      · intro h
        have hmem : v ∈ LinearMap.ker (Q : E →ₗ[𝕜] E) := by
          rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hQ, ContinuousLinearMap.add_apply,
            hKv]
          simp
        rw [h] at hmem
        exact hv.2 ((Submodule.mem_bot 𝕜).1 hmem)
      · intro h
        apply hinf
        have hall : ∀ x, K' x = -((p : ℝ) : 𝕜) • x := by
          intro x
          have : x ∈ LinearMap.ker (Q : E →ₗ[𝕜] E) := by rw [h]; trivial
          rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hQ, ContinuousLinearMap.add_apply] at this
          simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
          rw [neg_smul]; exact eq_neg_of_add_eq_zero_left this
        have hid : (id : E → E) = (-((p : ℝ) : 𝕜))⁻¹ • (K' : E → E) := by
          funext x
          simp only [id, Pi.smul_apply, hall x, smul_smul, inv_mul_cancel₀ hμ, one_smul]
        have : IsCompactOperator (id : E → E) := by
          rw [hid]; exact hK'c.smul _
        exact FiniteDimensional.of_isCompactOperator_id this
      · intro A hA x hx
        rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
        have hAK : Commute A K := hA
        have hAQ : Commute A Q :=
          ((hAK.mul_right hAK).sub_right (hAK.smul_right _)).add_right
            ((Commute.one_right A).smul_right _)
        have := congrArg (fun F : E →L[𝕜] E => F x) hAQ.eq
        simp only [ContinuousLinearMap.mul_apply, hx, map_zero] at this
        exact this.symm
    · exfalso
      apply hQu
      rw [spectrum.mem_resolventSet_iff, Algebra.algebraMap_eq_smul_one] at hres
      have : -Q = -((p : ℝ) : 𝕜) • 1 - K' := by
        rw [hQ]; simp only [neg_smul]; abel
      rw [← this] at hres
      simpa using hres.neg

end General

end InvariantSubspaceProblem

open InvariantSubspaceProblem in
theorem aronszajn_smith_aux {𝕜 : Type*} [RCLike 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace E] (hinf : ¬ FiniteDimensional 𝕜 E)
    (K : E →L[𝕜] E) (hK : IsCompactOperator K) :
    HasNontrivialClosedInvariantSubspace K := by
  by_cases hK0 : K = 0
  · subst hK0
    have hnt : Nontrivial E := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      exact hinf inferInstance
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    refine ⟨Submodule.span 𝕜 {v}, Submodule.closed_of_finiteDimensional _, ?_, ?_, ?_⟩
    · intro h
      have : v ∈ Submodule.span 𝕜 {v} := Submodule.mem_span_singleton_self v
      rw [h] at this
      exact hv ((Submodule.mem_bot 𝕜).1 this)
    · intro h
      apply hinf
      haveI : FiniteDimensional 𝕜 (⊤ : Submodule 𝕜 E) := by rw [← h]; infer_instance
      exact LinearEquiv.finiteDimensional Submodule.topEquiv
    · intro x _
      simp
  · letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    haveI : IsScalarTower ℝ 𝕜 E := ⟨fun r c x => by
      show (r • c) • x = (algebraMap ℝ 𝕜 r) • (c • x)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨S, hS1, hS2, hS3, hS4⟩ := hyper_general hinf K hK hK0
    exact ⟨S, hS1, hS2, hS3, hS4 K rfl⟩

open InvariantSubspaceProblem in
theorem solution :
    ∃ (E : Type) (_ : NormedAddCommGroup E) (_ : NormedSpace ℝ E) (_ : CompleteSpace E),
      TopologicalSpace.SeparableSpace E ∧ ¬ FiniteDimensional ℝ E ∧
      ∀ T : E →L[ℝ] E, HasNontrivialClosedInvariantSubspace T := by
  obtain ⟨E, i1, i2, i3, hsep, hinf, hT⟩ := argyros_haydon_scalar_plus_compact
  refine ⟨E, i1, i2, i3, hsep, hinf, fun T => ?_⟩
  obtain ⟨c, K, hK, rfl⟩ := hT T
  obtain ⟨S, hS1, hS2, hS3, hS4⟩ := aronszajn_smith_aux E hinf K hK
  refine ⟨S, hS1, hS2, hS3, fun x hx => ?_⟩
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]
  exact S.add_mem (S.smul_mem c hx) (hS4 x hx)
