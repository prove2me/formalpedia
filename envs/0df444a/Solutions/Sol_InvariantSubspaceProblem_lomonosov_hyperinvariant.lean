-- Prove2me | solution 1 for InvariantSubspaceProblem.lomonosov_hyperinvariant
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T04:27:54.69499+00:00
-- url     : https://prove2.me/submissions/0841294e-31a5-4b48-ae29-db5db95be36b

import Mathlib
import Definitions.Def_InvariantSubspaceProblem_Defs

set_option linter.all false

namespace InvariantSubspaceProblem

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- Eigenvalue case: the eigenspace of a nonzero eigenvalue is hyperinvariant. -/
lemma hyper_of_eigen (hinf : ¬ FiniteDimensional ℂ E) (K : E →L[ℂ] E) (hK : IsCompactOperator K)
    (μ : ℂ) (hμ : μ ≠ 0) (he : Module.End.HasEigenvalue (K : Module.End ℂ E) μ) :
    HasNontrivialClosedHyperinvariantSubspace K := by
  refine ⟨LinearMap.ker ((K - μ • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E), (K - μ • (1 : E →L[ℂ] E)).isClosed_ker, ?_, ?_, ?_⟩
  · obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    intro h
    have hmem : v ∈ LinearMap.ker ((K - μ • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      have := Module.End.mem_eigenspace_iff.1 hv.1
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      rw [show K v = (K : Module.End ℂ E) v from rfl, this, sub_self]
    rw [h] at hmem
    exact hv.2 ((Submodule.mem_bot ℂ).1 hmem)
  · intro h
    apply hinf
    have hall : ∀ x, K x = μ • x := by
      intro x
      have : x ∈ LinearMap.ker ((K - μ • (1 : E →L[ℂ] E) : E →L[ℂ] E) : E →ₗ[ℂ] E) := by rw [h]; trivial
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
      simpa [sub_eq_zero] using this
    have hid : (id : E → E) = μ⁻¹ • (K : E → E) := by
      funext x
      simp [hall x, smul_smul, inv_mul_cancel₀ hμ]
    have : IsCompactOperator (id : E → E) := by
      rw [hid]; exact hK.smul μ⁻¹
    exact FiniteDimensional.of_isCompactOperator_id this
  · intro A hA x hx
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hx ⊢
    have h1 : (A * K) x = (K * A) x := by rw [hA]
    simp only [ContinuousLinearMap.mul_apply] at h1
    have h2 : A ((K - μ • (1 : E →L[ℂ] E)) x) = 0 := by rw [hx, map_zero]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, map_sub, map_smul] at h2 ⊢
    rw [← h1]; exact h2

/-- Quasinilpotent case (Hilden's argument). -/
lemma hyper_of_quasinilpotent (K : E →L[ℂ] E) (hK : IsCompactOperator K) (hK0 : K ≠ 0)
    (hq : spectralRadius ℂ K = 0) : HasNontrivialClosedHyperinvariantSubspace K := by
  by_contra hno
  -- density of commutant orbits
  have hdense : ∀ y : E, y ≠ 0 → ∀ x : E, ∀ ε > 0,
      ∃ A : E →L[ℂ] E, A * K = K * A ∧ ‖A y - x‖ < ε := by
    intro y hy x ε hε
    let N : Submodule ℂ E :=
      { carrier := {z | ∃ A : E →L[ℂ] E, A * K = K * A ∧ A y = z}
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
        exact hy ((Submodule.mem_bot ℂ).1 this)
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
  let ι := {A : E →L[ℂ] E // A * K = K * A}
  let U : ι → Set E := fun A => {z | ‖(A : E →L[ℂ] E) z - x0‖ < ρ}
  have hUo : ∀ i, IsOpen (U i) := fun i =>
    isOpen_lt (continuous_norm.comp (i.1.continuous.sub continuous_const)) continuous_const
  have hCU : C ⊆ ⋃ i, U i := by
    intro c hc
    obtain ⟨A, hA, hAc⟩ := hdense c (hC0 c hc) x0 ρ hρ
    exact Set.mem_iUnion.2 ⟨⟨A, hA⟩, hAc⟩
  obtain ⟨t, ht⟩ := hCc.elim_finite_subcover U hUo hCU
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 1 + ∑ i ∈ t, ‖(i : E →L[ℂ] E)‖ := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hMdef]; have := Finset.sum_nonneg (fun i (_ : i ∈ t) => norm_nonneg (i : E →L[ℂ] E))
    linarith
  have hMi : ∀ i ∈ t, ‖(i : E →L[ℂ] E)‖ ≤ M := by
    intro i hi
    rw [hMdef]
    have := Finset.single_le_sum (f := fun i : ι => ‖(i : E →L[ℂ] E)‖)
      (fun i _ => norm_nonneg _) hi
    linarith
  -- the iteration
  have hiter : ∀ n : ℕ, ∃ P : E →L[ℂ] E, P * K = K * P ∧ ‖P‖ ≤ M ^ n ∧
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
      refine ⟨(i : E →L[ℂ] E) * P, ?_, ?_, ?_⟩
      · rw [mul_assoc, hPK, ← mul_assoc, i.2, mul_assoc]
      · calc ‖(i : E →L[ℂ] E) * P‖ ≤ ‖(i : E →L[ℂ] E)‖ * ‖P‖ := norm_mul_le _ _
          _ ≤ M * M ^ n := mul_le_mul (hMi i hi) hPn (norm_nonneg _) (by positivity)
          _ = M ^ (n + 1) := by ring
      · have hcomm : P (K ((K ^ n) x0)) = K (P ((K ^ n) x0)) := by
          have := congrArg (fun F : E →L[ℂ] E => F ((K ^ n) x0)) hPK
          simpa only [ContinuousLinearMap.mul_apply] using this
        have : ((i : E →L[ℂ] E) * P) ((K ^ (n + 1)) x0) = (i : E →L[ℂ] E) (K xn) := by
          rw [pow_succ', ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hcomm]
        rw [this]; exact hiU
  -- Gelfand's formula
  have hG := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius K
  rw [hq] at hG
  have hpos : (0 : ENNReal) < ENNReal.ofReal (1 / (2 * M)) :=
    ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn, hn1⟩ := ((hG.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop 1)).exists
  have hn' : ‖K ^ n‖ ^ (1 / n : ℝ) < 1 / (2 * M) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).1 hn
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

theorem lomonosov_hyperinvariant_aux (hinf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (hK0 : K ≠ 0) :
    HasNontrivialClosedHyperinvariantSubspace K := by
  by_cases h : ∃ μ : ℂ, μ ≠ 0 ∧ Module.End.HasEigenvalue (K : Module.End ℂ E) μ
  · obtain ⟨μ, hμ, he⟩ := h
    exact hyper_of_eigen hinf K hK μ hμ he
  · push Not at h
    apply hyper_of_quasinilpotent K hK hK0
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun μ hμ => ?_
    by_cases h0 : μ = 0
    · simp [h0]
    · exact absurd ((hK.hasEigenvalue_iff_mem_spectrum h0).2 hμ) (h μ h0)

end InvariantSubspaceProblem

open InvariantSubspaceProblem in
theorem solution (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (hinf : ¬ FiniteDimensional ℂ E)
    (K : E →L[ℂ] E) (hK : IsCompactOperator K) (hK0 : K ≠ 0) :
    HasNontrivialClosedHyperinvariantSubspace K :=
  lomonosov_hyperinvariant_aux hinf K hK hK0
