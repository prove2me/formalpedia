-- Prove2me | solution 1 for HighDimProb.RandomProcesses.slepian_finite_dim_all_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-02T09:42:16.006893+00:00
-- url     : https://prove2.me/submissions/1f029d47-20ff-4a09-8944-043b91002c08

import Mathlib

-- Inlined module: SlepianSmoothCutoff
section

open Filter Set MeasureTheory
open scoped Topology

namespace SlepianProof

noncomputable def cutoff (τ : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.smoothTransition (((N : ℝ) + 1) * (τ - x))

lemma cutoff_contDiff (τ : ℝ) (N : ℕ) : ContDiff ℝ 2 (cutoff τ N) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id))

lemma cutoff_nonneg (τ : ℝ) (N : ℕ) (x : ℝ) : 0 ≤ cutoff τ N x :=
  Real.smoothTransition.nonneg _

lemma cutoff_le_one (τ : ℝ) (N : ℕ) (x : ℝ) : cutoff τ N x ≤ 1 :=
  Real.smoothTransition.le_one _

lemma cutoff_antitone (τ : ℝ) (N : ℕ) : Antitone (cutoff τ N) := by
  intro x y hxy
  apply Real.smoothTransition.monotone
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (N : ℝ) + 1)
  linarith

lemma cutoff_zero_of_ge {τ x : ℝ} (N : ℕ) (hx : τ ≤ x) : cutoff τ N x = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ (N : ℝ) + 1)
  linarith

lemma cutoff_eventually_one {τ x : ℝ} (hx : x < τ) :
    ∀ᶠ N : ℕ in atTop, cutoff τ N x = 1 := by
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (τ - x))
  refine eventually_atTop.2 ⟨K, fun N hN => ?_⟩
  apply Real.smoothTransition.one_of_one_le
  rw [← div_le_iff₀ (sub_pos.mpr hx)]
  have hKN : (K : ℝ) ≤ N := by exact_mod_cast hN
  linarith

noncomputable def cutoffProd {ι : Type*} [Fintype ι] (τ : ℝ) (N : ℕ) (x : ι → ℝ) : ℝ :=
  ∏ i : ι, cutoff τ N (x i)

lemma cutoffProd_contDiff {ι : Type*} [Fintype ι] (τ : ℝ) (N : ℕ) :
    ContDiff ℝ 2 (cutoffProd τ N : (ι → ℝ) → ℝ) := by
  apply contDiff_prod
  intro i _
  exact (cutoff_contDiff τ N).comp
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff

lemma cutoffProd_nonneg {ι : Type*} [Fintype ι] (τ : ℝ) (N : ℕ) (x : ι → ℝ) :
    0 ≤ cutoffProd τ N x := Finset.prod_nonneg (fun _ _ => cutoff_nonneg _ _ _)

lemma cutoffProd_le_one {ι : Type*} [Fintype ι] (τ : ℝ) (N : ℕ) (x : ι → ℝ) :
    cutoffProd τ N x ≤ 1 :=
  Finset.prod_le_one (fun _ _ => cutoff_nonneg _ _ _) (fun _ _ => cutoff_le_one _ _ _)

lemma cutoffProd_eventually_indicator {ι : Type*} [Fintype ι] (τ : ℝ) (x : ι → ℝ) :
    ∀ᶠ N : ℕ in atTop,
      cutoffProd τ N x = indicator {y : ι → ℝ | ∀ i, y i < τ} (fun _ => (1 : ℝ)) x := by
  classical
  by_cases hx : ∀ i, x i < τ
  · have he : ∀ᶠ N : ℕ in atTop, ∀ i, cutoff τ N (x i) = 1 :=
      eventually_all.2 (fun i => cutoff_eventually_one (hx i))
    filter_upwards [he] with N hN
    simp [cutoffProd, hN, hx]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hxi : τ ≤ x i := le_of_not_gt hi
    apply Eventually.of_forall
    intro N
    have hz : cutoffProd τ N x = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (cutoff_zero_of_ge N hxi)
    simp [hz, hx]

lemma cutoffProd_integral_tendsto {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : AEMeasurable X P) (τ : ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, cutoffProd τ N (X ω) ∂P) atTop
      (𝓝 (∫ ω, indicator {z : ι → ℝ | ∀ i, z i < τ} (fun _ => (1 : ℝ)) (X ω) ∂P)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro N
    exact ((cutoffProd_contDiff τ N).continuous.measurable.comp_aemeasurable hX).aestronglyMeasurable
  · exact integrable_const 1
  · intro N
    exact ae_of_all P (fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (cutoffProd_nonneg τ N (X ω))]
      exact cutoffProd_le_one τ N (X ω))
  · apply Eventually.of_forall
    intro ω
    exact tendsto_const_nhds.congr'
      (Filter.EventuallyEq.symm (cutoffProd_eventually_indicator τ (X ω)))

end SlepianProof
end

-- Inlined module: SlepianCutoffBounds
section

open Filter Set
open scoped Topology

namespace SlepianProof

lemma cutoff_one_of_le {τ x : ℝ} (N : ℕ)
    (hx : x ≤ τ - 1 / ((N : ℝ) + 1)) : cutoff τ N x = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hN : 0 < (N : ℝ) + 1 := by positivity
  have h : 1 / ((N : ℝ) + 1) ≤ τ - x := by linarith
  have h' := (div_le_iff₀ hN).mp h
  nlinarith

lemma cutoff_deriv_compact (τ : ℝ) (N : ℕ) : HasCompactSupport (deriv (cutoff τ N)) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (K := Icc (τ - 1 / ((N : ℝ) + 1)) τ)
  intro x hx
  by_contra hnot
  have hzero : deriv (cutoff τ N) x = 0 := by
    have hout : x < τ - 1 / ((N : ℝ) + 1) ∨ τ < x := by
      simpa only [mem_Icc, not_and_or, not_le] using hnot
    rcases hout with hl | hr
    · have he : cutoff τ N =ᶠ[𝓝 x] (fun _ : ℝ => 1) := by
        filter_upwards [Iio_mem_nhds hl] with y hy
        exact cutoff_one_of_le N hy.le
      rw [he.deriv_eq]
      simp
    · have he : cutoff τ N =ᶠ[𝓝 x] (fun _ : ℝ => 0) := by
        filter_upwards [Ioi_mem_nhds hr] with y hy
        exact cutoff_zero_of_ge N hy.le
      rw [he.deriv_eq]
      simp
  exact hx hzero

lemma cutoff_deriv_bounds (τ : ℝ) (N : ℕ) :
    ∃ D H : ℝ, 0 ≤ D ∧ 0 ≤ H ∧
      (∀ x, ‖deriv (cutoff τ N) x‖ ≤ D) ∧
      (∀ x, ‖deriv (deriv (cutoff τ N)) x‖ ≤ H) := by
  have h1 : ContDiff ℝ 1 (deriv (cutoff τ N)) := (cutoff_contDiff τ N).deriv'
  have h2 : ContDiff ℝ 0 (deriv (deriv (cutoff τ N))) := h1.deriv'
  obtain ⟨D, hD⟩ := h1.continuous.bounded_above_of_compact_support (cutoff_deriv_compact τ N)
  obtain ⟨H, hH⟩ := h2.continuous.bounded_above_of_compact_support (cutoff_deriv_compact τ N).deriv
  exact ⟨D, H, (norm_nonneg _).trans (hD 0), (norm_nonneg _).trans (hH 0), hD, hH⟩

lemma cutoff_deriv_nonpos (τ : ℝ) (N : ℕ) (x : ℝ) : deriv (cutoff τ N) x ≤ 0 :=
  (cutoff_antitone τ N).deriv_nonpos

end SlepianProof
end

-- Inlined module: SlepianProductCalculus
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def scalarProd (g : ℝ → ℝ) (s : Finset ι) (x : ι → ℝ) : ℝ :=
  ∏ i ∈ s, g (x i)

noncomputable def scalarProdGrad (g : ℝ → ℝ) (s : Finset ι) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ s, (deriv g (x i) * scalarProd g (s.erase i) x) • ContinuousLinearMap.proj i

noncomputable def scalarProdCoeffDeriv (g : ℝ → ℝ) (s : Finset ι) (i : ι) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] ℝ :=
  deriv g (x i) • scalarProdGrad g (s.erase i) x +
    scalarProd g (s.erase i) x • (deriv (deriv g) (x i) • ContinuousLinearMap.proj i)

noncomputable def scalarProdHess (g : ℝ → ℝ) (s : Finset ι) (x : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i ∈ s, (scalarProdCoeffDeriv g s i x).smulRight (ContinuousLinearMap.proj i)

set_option backward.isDefEq.respectTransparency false in
lemma scalarProd_hasFDerivAt (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (s : Finset ι) (x : ι → ℝ) : HasFDerivAt (scalarProd g s) (scalarProdGrad g s x) x := by
  have hi (i : ι) : HasFDerivAt (fun y : ι → ℝ => g (y i))
      (deriv g (x i) • ContinuousLinearMap.proj i) x :=
    (hg (x i)).hasDerivAt.comp_hasFDerivAt x
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt
  have h := HasFDerivAt.finsetProd (u := s) (fun i _ => hi i)
  simpa only [scalarProd, scalarProdGrad, smul_smul, mul_comm] using! h

lemma scalarProd_fderiv (g : ℝ → ℝ) (hg : Differentiable ℝ g)
    (s : Finset ι) (x : ι → ℝ) : fderiv ℝ (scalarProd g s) x = scalarProdGrad g s x :=
  (scalarProd_hasFDerivAt g hg s x).fderiv

lemma scalarProdCoeff_hasFDerivAt (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (s : Finset ι) (i : ι) (x : ι → ℝ) :
    HasFDerivAt (fun y : ι → ℝ => deriv g (y i) * scalarProd g (s.erase i) y)
      (scalarProdCoeffDeriv g s i x) x := by
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd' : Differentiable ℝ (deriv g) := (hg.deriv' : ContDiff ℝ 1 (deriv g)).differentiable_one
  exact ((hd' (x i)).hasDerivAt.comp_hasFDerivAt x
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt).mul
      (scalarProd_hasFDerivAt g hd (s.erase i) x)

lemma scalarProdGrad_hasFDerivAt (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (s : Finset ι) (x : ι → ℝ) :
    HasFDerivAt (scalarProdGrad g s) (scalarProdHess g s x) x := by
  exact HasFDerivAt.fun_sum (u := s)
    (fun i _ => (scalarProdCoeff_hasFDerivAt g hg s i x).smul_const
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

lemma scalarProd_fderiv_fderiv (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    (s : Finset ι) (x : ι → ℝ) :
    fderiv ℝ (fderiv ℝ (scalarProd g s)) x = scalarProdHess g s x := by
  have he : fderiv ℝ (scalarProd g s) = scalarProdGrad g s :=
    funext (scalarProd_fderiv g (hg.differentiable (by norm_num)) s)
  rw [he]
  exact (scalarProdGrad_hasFDerivAt g hg s x).fderiv

lemma scalarProd_between_zero_one (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (s : Finset ι) (x : ι → ℝ) : 0 ≤ scalarProd g s x ∧ scalarProd g s x ≤ 1 :=
  ⟨Finset.prod_nonneg (fun i _ => hg0 (x i)),
    Finset.prod_le_one (fun i _ => hg0 (x i)) (fun i _ => hg1 (x i))⟩

lemma scalarProd_norm_le_one (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (s : Finset ι) (x : ι → ℝ) : ‖scalarProd g s x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (scalarProd_between_zero_one g hg0 hg1 s x).1]
  exact (scalarProd_between_zero_one g hg0 hg1 s x).2

lemma scalar_proj_norm_le_one (i : ι) :
    ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa using norm_le_pi_norm x i

lemma scalarProdGrad_norm_le (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    {D : ℝ} (hD : 0 ≤ D) (hgd : ∀ z, ‖deriv g z‖ ≤ D) (s : Finset ι) (x : ι → ℝ) :
    ‖scalarProdGrad g s x‖ ≤ (s.card : ℝ) * D := by
  unfold scalarProdGrad
  calc
    ‖∑ i ∈ s, (deriv g (x i) * scalarProd g (s.erase i) x) • ContinuousLinearMap.proj i‖
        ≤ ∑ i ∈ s, ‖(deriv g (x i) * scalarProd g (s.erase i) x) •
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, D := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, norm_mul]
      have hc : ‖deriv g (x i)‖ * ‖scalarProd g (s.erase i) x‖ ≤ D := by
        simpa using mul_le_mul (hgd (x i)) (scalarProd_norm_le_one g hg0 hg1 (s.erase i) x)
          (norm_nonneg _) hD
      simpa using mul_le_mul hc (scalar_proj_norm_le_one i) (norm_nonneg _) hD
    _ = (s.card : ℝ) * D := by simp

end SlepianProof
end

-- Inlined module: SlepianProductBounds
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma scalarProdCoeffDeriv_norm_le (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgd : ∀ z, ‖deriv g z‖ ≤ D) (hgdd : ∀ z, ‖deriv (deriv g) z‖ ≤ E)
    (s : Finset ι) (i : ι) (x : ι → ℝ) :
    ‖scalarProdCoeffDeriv g s i x‖ ≤ D * ((s.card : ℝ) * D) + E := by
  have hcard : ((s.erase i).card : ℝ) ≤ s.card := by exact_mod_cast Finset.card_erase_le
  have hgrad : ‖scalarProdGrad g (s.erase i) x‖ ≤ (s.card : ℝ) * D :=
    (scalarProdGrad_norm_le g hg0 hg1 hD hgd (s.erase i) x).trans
      (mul_le_mul_of_nonneg_right hcard hD)
  unfold scalarProdCoeffDeriv
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_smul]
    exact mul_le_mul (hgd (x i)) hgrad (norm_nonneg _) hD
  · rw [norm_smul, norm_smul]
    have he : ‖deriv (deriv g) (x i)‖ *
        ‖(ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ ≤ E := by
      simpa using mul_le_mul (hgdd (x i)) (scalar_proj_norm_le_one i) (norm_nonneg _) hE
    simpa using mul_le_mul (scalarProd_norm_le_one g hg0 hg1 (s.erase i) x) he (by positivity) zero_le_one

lemma scalarProdHess_norm_le (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    {D E : ℝ} (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgd : ∀ z, ‖deriv g z‖ ≤ D) (hgdd : ∀ z, ‖deriv (deriv g) z‖ ≤ E)
    (s : Finset ι) (x : ι → ℝ) :
    ‖scalarProdHess g s x‖ ≤ (s.card : ℝ) * (D * ((s.card : ℝ) * D) + E) := by
  unfold scalarProdHess
  calc
    ‖∑ i ∈ s, (scalarProdCoeffDeriv g s i x).smulRight (ContinuousLinearMap.proj i)‖
        ≤ ∑ i ∈ s, ‖(scalarProdCoeffDeriv g s i x).smulRight
          (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, (D * ((s.card : ℝ) * D) + E) := by
      apply Finset.sum_le_sum
      intro i _
      rw [ContinuousLinearMap.norm_smulRight_apply]
      simpa using mul_le_mul (scalarProdCoeffDeriv_norm_le g hg0 hg1 hD hE hgd hgdd s i x)
        (scalar_proj_norm_le_one i) (norm_nonneg _) (by positivity : 0 ≤ D * ((s.card : ℝ) * D) + E)
    _ = (s.card : ℝ) * (D * ((s.card : ℝ) * D) + E) := by simp [mul_add]

lemma scalarProdGrad_single (g : ℝ → ℝ) (s : Finset ι) (x : ι → ℝ) (i : ι) :
    scalarProdGrad g s x (Pi.single i 1) =
      if i ∈ s then deriv g (x i) * scalarProd g (s.erase i) x else 0 := by
  simp [scalarProdGrad, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    Pi.single_apply, eq_comm]

lemma scalarProdHess_offdiag_nonneg (g : ℝ → ℝ) (hg0 : ∀ z, 0 ≤ g z)
    (hgd : ∀ z, deriv g z ≤ 0) (s : Finset ι) (x : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    0 ≤ scalarProdHess g s x (Pi.single i 1) (Pi.single j 1) := by
  simp only [scalarProdHess, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    smul_eq_mul]
  apply Finset.sum_nonneg
  intro k _
  by_cases hkj : k = j
  · subst k
    have hji : j ≠ i := Ne.symm hij
    simp only [scalarProdCoeffDeriv, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    simp only [ContinuousLinearMap.proj_apply, Pi.single_apply, if_pos rfl, if_neg hij,
      if_neg hji, mul_one, mul_zero, add_zero]
    rw [scalarProdGrad_single]
    split_ifs with hi
    · have hb : 0 ≤ deriv g (x j) *
          (deriv g (x i) * scalarProd g ((s.erase j).erase i) x) :=
        mul_nonneg_of_nonpos_of_nonpos (hgd _) (mul_nonpos_of_nonpos_of_nonneg (hgd _)
          (Finset.prod_nonneg (fun l _ => hg0 (x l))))
      simpa using hb
    · simp
  · simp [Pi.single_apply, hkj, Ne.symm hkj]

end SlepianProof
end

-- Inlined module: SlepianCutoffAdmissible
section

namespace SlepianProof

lemma cutoffProd_admissible {ι : Type*} [Fintype ι] [DecidableEq ι] (τ : ℝ) (N : ℕ) :
    ∃ D H : ℝ,
      (∀ x : ι → ℝ, ‖fderiv ℝ (cutoffProd τ N) x‖ ≤ D) ∧
      (∀ x : ι → ℝ, ‖fderiv ℝ (fderiv ℝ (cutoffProd τ N)) x‖ ≤ H) ∧
      (∀ (x : ι → ℝ) (i j : ι), i ≠ j →
        0 ≤ fderiv ℝ (fderiv ℝ (cutoffProd τ N)) x (Pi.single i 1) (Pi.single j 1)) := by
  obtain ⟨D, E, hD, hE, hd, he⟩ := cutoff_deriv_bounds τ N
  refine ⟨(Fintype.card ι : ℝ) * D,
    (Fintype.card ι : ℝ) * (D * ((Fintype.card ι : ℝ) * D) + E), ?_, ?_, ?_⟩
  · intro x
    change ‖fderiv ℝ (scalarProd (cutoff τ N) Finset.univ) x‖ ≤ _
    rw [scalarProd_fderiv _ ((cutoff_contDiff τ N).differentiable (by norm_num))]
    simpa using scalarProdGrad_norm_le (cutoff τ N) (cutoff_nonneg τ N) (cutoff_le_one τ N)
      hD hd Finset.univ x
  · intro x
    change ‖fderiv ℝ (fderiv ℝ (scalarProd (cutoff τ N) Finset.univ)) x‖ ≤ _
    rw [scalarProd_fderiv_fderiv _ (cutoff_contDiff τ N)]
    simpa using scalarProdHess_norm_le (cutoff τ N) (cutoff_nonneg τ N) (cutoff_le_one τ N)
      hD hE hd he Finset.univ x
  · intro x i j hij
    change 0 ≤ fderiv ℝ (fderiv ℝ (scalarProd (cutoff τ N) Finset.univ)) x
      (Pi.single i 1) (Pi.single j 1)
    rw [scalarProd_fderiv_fderiv _ (cutoff_contDiff τ N)]
    exact scalarProdHess_offdiag_nonneg (cutoff τ N) (cutoff_nonneg τ N)
      (cutoff_deriv_nonpos τ N) Finset.univ x i j hij

end SlepianProof
end

-- Inlined module: SlepianCutoffProbability
section

open Filter Set MeasureTheory ProbabilityTheory
open scoped Topology

namespace SlepianProof

lemma cutoff_event_nullMeasurable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : Ω → (ι → ℝ)) (hX : AEMeasurable X P) (τ : ℝ) :
    NullMeasurableSet {ω | ∀ i, X ω i < τ} P := by
  have he : {ω | ∀ i, X ω i < τ} = ⋂ i, {ω | X ω i < τ} := by ext ω; simp
  rw [he]
  exact NullMeasurableSet.iInter (fun i => nullMeasurableSet_lt (hX.eval i) aemeasurable_const)

lemma cutoffProd_integral_tendsto_probability {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → (ι → ℝ))
    (hX : AEMeasurable X P) (τ : ℝ) :
    Tendsto (fun N : ℕ => ∫ ω, cutoffProd τ N (X ω) ∂P) atTop
      (𝓝 (P.real {ω | ∀ i, X ω i < τ})) := by
  have h := cutoffProd_integral_tendsto P X hX τ
  have he : (fun ω => indicator {z : ι → ℝ | ∀ i, z i < τ} (fun _ => (1 : ℝ)) (X ω)) =
      indicator {ω | ∀ i, X ω i < τ} (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [indicator, mem_setOf_eq]
  rw [he, integral_indicator₀ (cutoff_event_nullMeasurable P X hX τ), setIntegral_const] at h
  simpa using h

lemma tail_comparison_of_cutoff_comparison {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → (ι → ℝ))
    (hX : AEMeasurable X P) (hY : AEMeasurable Y P) (τ : ℝ)
    (hcut : ∀ N : ℕ, (∫ ω, cutoffProd τ N (Y ω) ∂P) ≤ ∫ ω, cutoffProd τ N (X ω) ∂P) :
    P.real {ω | ∃ i, τ ≤ X ω i} ≤ P.real {ω | ∃ i, τ ≤ Y ω i} := by
  have h := le_of_tendsto_of_tendsto'
    (cutoffProd_integral_tendsto_probability P Y hY τ)
    (cutoffProd_integral_tendsto_probability P X hX τ) hcut
  have he (Z : Ω → (ι → ℝ)) :
      {ω | ∃ i, τ ≤ Z ω i} = ({ω | ∀ i, Z ω i < τ})ᶜ := by
    ext ω
    simp
  rw [he X, he Y, probReal_compl_eq_one_sub₀ (cutoff_event_nullMeasurable P X hX τ),
    probReal_compl_eq_one_sub₀ (cutoff_event_nullMeasurable P Y hY τ)]
  linarith

end SlepianProof
end

-- Inlined module: SlepianGaussianRepresentation
section

open MeasureTheory ProbabilityTheory Matrix
open scoped MatrixOrder

namespace SlepianProof

lemma gaussian_eq_multivariate_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ] :
    μ = multivariateGaussian (∫ x, x ∂μ)
      (LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
        (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm) := by
  let b := (EuclideanSpace.basisFun ι ℝ).toBasis
  let S := LinearMap.toMatrix₂ b b (covarianceBilin μ).toBilinForm
  have hS : S.PosSemidef :=
    (LinearMap.isPosSemidef_iff_posSemidef_toMatrix b).mp
      (LinearMap.BilinForm.isPosSemidef_iff.mp (isPosSemidef_covarianceBilin (μ := μ)))
  have hr (z : EuclideanSpace ℝ ι) : (⇑(b.repr z) : ι → ℝ) = z.ofLp := by
    funext i
    simp [b, OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr]
  apply IsGaussian.ext
  · simp
  · ext x y
    rw [covarianceBilin_multivariateGaussian hS]
    have h := apply_eq_dotProduct_toMatrix₂_mulVec b b
      (covarianceBilin μ).toBilinForm x y
    simpa [S, hr, Function.comp_def] using h

lemma centered_gaussian_eq_map_pi_euclidean {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (EuclideanSpace ℝ ι)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] EuclideanSpace ℝ ι,
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  let S := LinearMap.toMatrix₂ (EuclideanSpace.basisFun ι ℝ).toBasis
    (EuclideanSpace.basisFun ι ℝ).toBasis (covarianceBilin μ).toBilinForm
  let A := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S)
  let e := (EuclideanSpace.equiv ι ℝ).symm
  refine ⟨A.comp e.toContinuousLinearMap, ?_⟩
  rw [gaussian_eq_multivariate_covariance μ, hmean]
  change (stdGaussian (EuclideanSpace ℝ ι)).map (fun x => 0 + A x) = _
  simp only [zero_add]
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

lemma centered_gaussian_eq_map_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hmean : (∫ x, x ∂μ) = 0) :
    ∃ L : (ι → ℝ) →L[ℝ] (ι → ℝ),
      μ = (Measure.pi (fun _ : ι => gaussianReal 0 1)).map L := by
  let e := EuclideanSpace.equiv ι ℝ
  let ν := μ.map e.symm
  have hm : (∫ x, x ∂ν) = 0 := by
    change (∫ x, x ∂μ.map e.symm) = 0
    rw [ContinuousLinearEquiv.integral_id_map, hmean, map_zero]
  obtain ⟨A, hA⟩ := centered_gaussian_eq_map_pi_euclidean ν hm
  refine ⟨e.toContinuousLinearMap.comp A, ?_⟩
  have he : ν.map e = μ := by
    change (μ.map e.symm).map e = μ
    rw [Measure.map_map e.continuous.measurable e.symm.continuous.measurable]
    have hc : (⇑e ∘ ⇑e.symm) = id := by
      funext x
      exact e.apply_symm_apply x
    rw [hc, Measure.map_id]
  rw [← he, hA, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

end SlepianProof
end

-- Inlined module: SlepianLinearCovariance
section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace SlepianProof

lemma gaussian_pi_covariance_eval {κ : Type*} [Fintype κ] [DecidableEq κ] (i j : κ) :
    cov[fun x : κ → ℝ => x i, fun x : κ → ℝ => x j;
      Measure.pi (fun _ : κ => gaussianReal 0 1)] = if i = j then 1 else 0 := by
  have hG (k : κ) : MemLp (fun x : κ → ℝ => x k) 2
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving
      (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)
  rw [← covarianceBilin_apply_basisFun hG i j]
  change covarianceBilin ((Measure.pi (fun _ : κ => gaussianReal 0 1)).map (WithLp.toLp 2))
    (EuclideanSpace.basisFun κ ℝ i) (EuclideanSpace.basisFun κ ℝ j) = _
  rw [map_pi_eq_stdGaussian, covarianceBilin_stdGaussian]
  rw [innerSL_apply_apply, EuclideanSpace.basisFun_inner]
  simp

lemma gaussian_pi_covariance_linear {κ ι : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] (L : (κ → ℝ) →L[ℝ] (ι → ℝ)) (i j : ι) :
    cov[fun x => L x i, fun x => L x j; Measure.pi (fun _ : κ => gaussianReal 0 1)] =
      ∑ k : κ, L (Pi.single k 1) i * L (Pi.single k 1) j := by
  have hG (k : κ) : MemLp (fun x : κ → ℝ => x k) 2
      (Measure.pi (fun _ : κ => gaussianReal 0 1)) :=
    IsGaussian.memLp_two_id.comp_measurePreserving
      (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) k)
  have hL (x : κ → ℝ) (r : ι) : L x r = ∑ k : κ, L (Pi.single k 1) r * x k := by
    have h := congrArg (fun z => L z r) (pi_eq_sum_univ' x)
    simpa [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, mul_comm] using h
  have hfun (r : ι) : (fun x => L x r) =
      (fun x => ∑ k : κ, L (Pi.single k 1) r * x k) := funext (fun x => hL x r)
  rw [hfun i, hfun j]
  rw [covariance_fun_sum_fun_sum (fun k => (hG k).const_mul _)
    (fun k => (hG k).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right, gaussian_pi_covariance_eval]
  simp

end SlepianProof
end

-- Inlined module: SlepianRotationDerivative
section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace SlepianProof

/-- Differentiation under the Gaussian expectation along a rotation of linear images.
The uniform derivative bound supplies an explicit integrable envelope. -/
lemma gaussian_rotation_hasDerivAt {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin n → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (∫ x, fderiv ℝ f (Real.cos θ • L x + Real.sin θ • M x)
        (-Real.sin θ • L x + Real.cos θ • M x)
        ∂Measure.pi (fun _ : Fin n => gaussianReal 0 1)) θ := by
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let Z (u : ℝ) (x : Fin n → ℝ) := Real.cos u • L x + Real.sin u • M x
  let V (u : ℝ) (x : Fin n → ℝ) := -Real.sin u • L x + Real.cos u • M x
  have hD : 0 ≤ D := le_trans (norm_nonneg _) (hdf_bound 0)
  have hid : Integrable (fun x : Fin n → ℝ => x) μ :=
    Integrable.of_eval fun i => integrable_eval IsGaussian.integrable_id
  have hb : Integrable (fun x => D * (‖L x‖ + ‖M x‖)) μ :=
    ((L.integrable_comp hid).norm.add (M.integrable_comp hid).norm).const_mul D
  have hz (u : ℝ) : Continuous (Z u) :=
    (L.continuous.const_smul _).add (M.continuous.const_smul _)
  have hv (u : ℝ) : Continuous (V u) :=
    (L.continuous.const_smul _).add (M.continuous.const_smul _)
  have hdc (u : ℝ) : Continuous (fun x => fderiv ℝ f (Z u x) (V u x)) :=
    ((hf.continuous_fderiv one_ne_zero).comp (hz u)).clm_apply (hv u)
  have hfi : Integrable (fun x => f (Z θ x)) μ := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul
      (hf.continuous.comp (hz θ)).aestronglyMeasurable (ae_of_all _ fun x => hf_bound _)
  have hbound (u : ℝ) (x : Fin n → ℝ) :
      ‖fderiv ℝ f (Z u x) (V u x)‖ ≤ D * (‖L x‖ + ‖M x‖) := by
    have hV : ‖V u x‖ ≤ ‖L x‖ + ‖M x‖ := by
      dsimp [V]
      apply le_trans (norm_add_le _ _)
      apply add_le_add
      · rw [norm_smul, Real.norm_eq_abs, abs_neg]
        exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one u) (norm_nonneg _)).trans_eq
          (one_mul _)
      · rw [norm_smul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one u) (norm_nonneg _)).trans_eq
          (one_mul _)
    calc ‖fderiv ℝ f (Z u x) (V u x)‖
        ≤ ‖fderiv ℝ f (Z u x)‖ * ‖V u x‖ := (fderiv ℝ f (Z u x)).le_opNorm _
      _ ≤ D * ‖V u x‖ := mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _)
      _ ≤ D * (‖L x‖ + ‖M x‖) := mul_le_mul_of_nonneg_left hV hD
  have hd (u : ℝ) (x : Fin n → ℝ) : HasDerivAt (fun v => f (Z v x))
      (fderiv ℝ f (Z u x) (V u x)) u := by
    apply ((hf.differentiable_one (Z u x)).hasFDerivAt).comp_hasDerivAt u
    exact ((Real.hasDerivAt_cos u).smul_const (L x)).add
      ((Real.hasDerivAt_sin u).smul_const (M x))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (s := Set.univ) (F := fun u x => f (Z u x))
    (F' := fun u x => fderiv ℝ f (Z u x) (V u x)) (bound := fun x => D * (‖L x‖ + ‖M x‖))
    (Filter.univ_mem : Set.univ ∈ 𝓝 θ)
    (Eventually.of_forall fun u => (hf.continuous.comp (hz u)).aestronglyMeasurable)
    hfi (hdc θ).aestronglyMeasurable
    (ae_of_all _ fun x u _ => hbound u x) hb (ae_of_all _ fun x u _ => hd u x)
  exact h.2

end SlepianProof
end

-- Inlined module: SlepianIBP
section

open MeasureTheory ProbabilityTheory Filter

namespace SlepianProof

/-- The standard Gaussian density has derivative `-x ρ(x)`. -/
lemma gaussianPDF_hasDerivAt (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 1) (-x * gaussianPDFReal 0 1 x) x := by
  have h := ((((hasDerivAt_id x).pow 2).neg.div_const 2).exp).const_mul
    (Real.sqrt (2 * Real.pi))⁻¹
  have heq : gaussianPDFReal 0 1 = fun y : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
      Real.exp (-(y ^ 2) / 2) := by
    ext y
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  rw [heq]
  convert h using 1 <;> (try simp only [id_eq, Pi.pow_apply, Pi.neg_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]) <;> (first | ring | rfl)


/-- Transfer absolute integrability to the density-weighted Lebesgue integral. -/
lemma gaussian_weight_integrable {f : ℝ → ℝ}
    (hf : Integrable f (gaussianReal 0 1)) :
    Integrable (fun x => gaussianPDFReal 0 1 x * f x) := by
  rw [gaussianReal_of_var_ne_zero _ (one_ne_zero : (1 : NNReal) ≠ 0)] at hf
  have := (integrable_withDensity_iff_integrable_smul'
    (measurable_gaussianPDF 0 1) (ae_of_all _ fun _ => gaussianPDF_lt_top)).mp hf
  simpa only [toReal_gaussianPDF, smul_eq_mul] using this

/-- Gaussian integration by parts, under explicit absolute integrability assumptions.
No unproved boundary-decay hypothesis is used. -/
lemma gaussian_integration_by_parts {f f' : ℝ → ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf : Integrable f (gaussianReal 0 1))
    (hf' : Integrable f' (gaussianReal 0 1))
    (hxf : Integrable (fun x => x * f x) (gaussianReal 0 1)) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  have hi1 : Integrable (fun x => f x * (-x * gaussianPDFReal 0 1 x)) := by
    convert (gaussian_weight_integrable hxf).neg using 1
    ext x
    simp only [Pi.neg_apply]
    ring
  have hi2 : Integrable (fun x => f' x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using gaussian_weight_integrable hf'
  have hi0 : Integrable (fun x => f x * gaussianPDFReal 0 1 x) := by
    simpa only [mul_comm] using gaussian_weight_integrable hf
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun x _ => hderiv x) (fun x _ => gaussianPDF_hasDerivAt x) hi1 hi2 hi0
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0),
    integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : NNReal) ≠ 0)]
  simp only [smul_eq_mul]
  have h1 : (∫ x : ℝ, f x * (-x * gaussianPDFReal 0 1 x)) =
      -(∫ x : ℝ, gaussianPDFReal 0 1 x * (x * f x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [h1] at h
  have h2 : (∫ x : ℝ, f' x * gaussianPDFReal 0 1 x) =
      ∫ x : ℝ, gaussianPDFReal 0 1 x * f' x := by
    simp only [mul_comm]
  rw [h2] at h
  linarith

/-- A bounded differentiable function with bounded derivative satisfies Stein's identity. -/
lemma gaussian_integration_by_parts_bounded {f f' : ℝ → ℝ} {C D : ℝ}
    (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hf' : AEStronglyMeasurable f' (gaussianReal 0 1))
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hf'_bound : ∀ x, ‖f' x‖ ≤ D) :
    (∫ x, f' x ∂gaussianReal 0 1) =
      ∫ x, x * f x ∂gaussianReal 0 1 := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun x => (hderiv x).continuousAt
  have hi : Integrable f (gaussianReal 0 1) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hf.aestronglyMeasurable
      (ae_of_all _ hf_bound)
  have hi' : Integrable f' (gaussianReal 0 1) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hf'
      (ae_of_all _ hf'_bound)
  exact gaussian_integration_by_parts hderiv hi hi'
    (IsGaussian.integrable_id.mul_bdd hf.aestronglyMeasurable (ae_of_all _ hf_bound))

end SlepianProof
end

-- Inlined module: SlepianProductIBP
section

open MeasureTheory ProbabilityTheory Filter

namespace SlepianProof

/-- Coordinatewise Gaussian integration by parts in a finite product. -/
lemma gaussian_pi_integration_by_parts {n : ℕ} (i : Fin (n + 1))
    {f df : (Fin (n + 1) → ℝ) → ℝ}
    (hderiv : ∀ (x : Fin (n + 1) → ℝ) (t : ℝ),
      HasDerivAt (fun y => f (Function.update x i y)) (df (Function.update x i t)) t)
    (hf : Integrable f (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hdf : Integrable df (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)))
    (hxf : Integrable (fun x => x i * f x)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))) :
    (∫ x, df x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∫ x, x i * f x ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hp : MeasurePreserving e
      ((gaussianReal 0 1).prod (Measure.pi (fun _ : Fin n => gaussianReal 0 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i).symm
  have hfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hdfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hdf
  have hxfi := (hp.integrable_comp_emb e.measurableEmbedding).mpr hxf
  rw [← hp.integral_comp' df, ← hp.integral_comp' (fun x => x i * f x)]
  simp only [Function.comp_def] at hfi hdfi hxfi
  rw [integral_prod_symm _ hdfi, integral_prod_symm _ hxfi]
  apply integral_congr_ae
  filter_upwards [hfi.prod_left_ae, hdfi.prod_left_ae, hxfi.prod_left_ae]
    with y hy hyd hyx
  have he (t : ℝ) : e (t, y) = i.insertNth t y := rfl
  simp only [Function.comp_def, he, Fin.insertNth_apply_same] at hy hyd hyx ⊢
  apply gaussian_integration_by_parts (f := fun t => f (i.insertNth t y))
    (f' := fun t => df (i.insertNth t y)) _ hy hyd hyx
  intro t
  have h := hderiv (i.insertNth 0 y) t
  simpa only [Fin.update_insertNth] using h

end SlepianProof
end

-- Inlined module: SlepianLinearIBP
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Stein's identity for a smooth bounded function of an arbitrary linear Gaussian image. -/
lemma gaussian_linear_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : (Fin (n + 1) → ℝ) →L[ℝ] E) (i : Fin (n + 1))
    (f : E → ℝ) (hf : ContDiff ℝ 1 f) {C D : ℝ}
    (hf_bound : ∀ x, ‖f x‖ ≤ C) (hdf_bound : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    (∫ x, fderiv ℝ f (L x) (L (Pi.single i 1))
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
    ∫ x, x i * f (L x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  have hfcont : Continuous fun x => f (L x) := hf.continuous.comp L.continuous
  have hdfcont : Continuous fun x => fderiv ℝ f (L x) (L (Pi.single i 1)) :=
    ((hf.continuous_fderiv one_ne_zero).comp L.continuous).clm_apply continuous_const
  have hb : ∀ x : Fin (n + 1) → ℝ,
      ‖fderiv ℝ f (L x) (L (Pi.single i 1))‖ ≤ D * ‖L (Pi.single i 1)‖ := by
    intro x
    exact le_trans ((fderiv ℝ f (L x)).le_opNorm _) <|
      mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _)
  have hfi : Integrable (fun x => f (L x))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hfcont.aestronglyMeasurable
      (ae_of_all _ fun x => hf_bound (L x))
  have hdfi : Integrable (fun x => fderiv ℝ f (L x) (L (Pi.single i 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul hdfcont.aestronglyMeasurable
      (ae_of_all _ hb)
  have hxfi : Integrable (fun x => x i * f (L x))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (integrable_eval (μ := fun _ : Fin (n + 1) => gaussianReal 0 1)
      IsGaussian.integrable_id).mul_bdd hfcont.aestronglyMeasurable
        (ae_of_all _ fun x => hf_bound (L x))
  apply gaussian_pi_integration_by_parts i _ hfi hdfi hxfi
  intro x t
  exact ((hf.differentiable_one (L (Function.update x i t))).hasFDerivAt).comp_hasDerivAt t
    ((L.hasFDerivAt).comp_hasDerivAt t (hasDerivAt_update x i t))

end SlepianProof
end

-- Inlined module: SlepianSecondOrderIBP
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Gaussian integration by parts for the directional derivative of a smooth function.
Both linear images may be singular and may be correlated. -/
lemma gaussian_directional_integration_by_parts {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {D H : ℝ}
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) :
    (∫ x, fderiv ℝ f (L x) (M x)
      ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) =
      ∑ i : Fin (n + 1), ∫ x,
        (fderiv ℝ (fderiv ℝ f) (L x) (L (Pi.single i 1))) (M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgi (i : Fin (n + 1)) : ContDiff ℝ 1
      (fun y => fderiv ℝ f y (M (Pi.single i 1))) :=
    hf1.clm_apply contDiff_const
  have hgderiv (i : Fin (n + 1)) (y : E) : HasFDerivAt
      (fun z => fderiv ℝ f z (M (Pi.single i 1)))
      ((fderiv ℝ (fderiv ℝ f) y).flip (M (Pi.single i 1))) y := by
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using
      (hf1.differentiable_one y).hasFDerivAt.clm_apply
        (hasFDerivAt_const (M (Pi.single i 1)) y)
  have hgb (i : Fin (n + 1)) (y : E) :
      ‖fderiv ℝ f y (M (Pi.single i 1))‖ ≤ D * ‖M (Pi.single i 1)‖ :=
    ((fderiv ℝ f y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hdf_bound _) (norm_nonneg _))
  have hgdb (i : Fin (n + 1)) (y : E) :
      ‖fderiv ℝ (fun z => fderiv ℝ f z (M (Pi.single i 1))) y‖ ≤
        H * ‖M (Pi.single i 1)‖ := by
    rw [(hgderiv i y).fderiv]
    apply le_trans ((fderiv ℝ (fderiv ℝ f) y).flip.le_opNorm _)
    rw [ContinuousLinearMap.opNorm_flip]
    exact mul_le_mul_of_nonneg_right (hddf_bound _) (norm_nonneg _)
  have hid : Integrable (fun x : Fin (n + 1) → ℝ => x)
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    Integrable.of_eval fun i => integrable_eval IsGaussian.integrable_id
  have hi (i : Fin (n + 1)) : Integrable
      (fun x => x i * fderiv ℝ f (L x) (M (Pi.single i 1)))
      (Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) :=
    (hid.eval i).mul_bdd
      (((hf1.continuous.comp L.continuous).clm_apply continuous_const).aestronglyMeasurable)
      (ae_of_all _ fun x => hgb i (L x))
  have hsum (x : Fin (n + 1) → ℝ) :
      fderiv ℝ f (L x) (M x) =
        ∑ i : Fin (n + 1), x i * fderiv ℝ f (L x) (M (Pi.single i 1)) := by
    conv_lhs => arg 2; rw [pi_eq_sum_univ' x]
    simp only [map_sum, map_smul, smul_eq_mul]
  simp_rw [hsum]
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i _
  have h := gaussian_linear_integration_by_parts L i
    (fun y => fderiv ℝ f y (M (Pi.single i 1))) (hgi i) (hgb i) (hgdb i)
  simp_rw [(hgderiv i _).fderiv] at h
  simpa only [ContinuousLinearMap.flip_apply] using h.symm

end SlepianProof
end

-- Inlined module: SlepianInterpolation
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Gaussian interpolation in a basis-independent Hessian form. -/
lemma gaussian_rotation_interpolation {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] E)
    (f : E → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (θ : ℝ) :
    HasDerivAt
      (fun u => ∫ x, f (Real.cos u • L x + Real.sin u • M x)
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1))
      (∑ i : Fin (n + 1), ∫ x,
        (fderiv ℝ (fderiv ℝ f) (Real.cos θ • L x + Real.sin θ • M x)
          (Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)))
          (-Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1))
        ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) θ := by
  have hd := gaussian_rotation_hasDerivAt L M f (hf.of_le (by norm_num))
    hf_bound hdf_bound θ
  let Z : (Fin (n + 1) → ℝ) →L[ℝ] E := Real.cos θ • L + Real.sin θ • M
  let V : (Fin (n + 1) → ℝ) →L[ℝ] E := -Real.sin θ • L + Real.cos θ • M
  have h := gaussian_directional_integration_by_parts Z V f hf hdf_bound hddf_bound
  simp only [Z, V, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at h
  rw [h] at hd
  exact hd

end SlepianProof
end

-- Inlined module: SlepianBilinear
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma bilinear_pi_expansion {m : ℕ}
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) (x : Fin m → ℝ) :
    B x x = ∑ i : Fin m, ∑ j : Fin m,
      (x i * x j) * B (Pi.single i 1) (Pi.single j 1) := by
  classical
  have he (A : (Fin m → ℝ) →L[ℝ] ℝ) :
      A x = ∑ j : Fin m, x j * A (Pi.single j 1) := by
    simpa only [map_sum, map_smul, smul_eq_mul] using congrArg A (pi_eq_sum_univ' x)
  have h1 : B x x = ∑ i : Fin m, x i * B (Pi.single i 1) x := by
    simpa only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] using
        congrArg (fun z => B z x) (pi_eq_sum_univ' x)
  rw [h1]
  simp_rw [he]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Sum of Hessian quadratic forms of the columns is a contraction with the Gram matrix. -/
lemma sum_bilinear_image_eq_gram {m n : ℕ}
    (L : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ) :
    (∑ k : Fin n, B (L (Pi.single k 1)) (L (Pi.single k 1))) =
      ∑ i : Fin m, ∑ j : Fin m,
        (∑ k : Fin n, L (Pi.single k 1) i * L (Pi.single k 1) j) *
          B (Pi.single i 1) (Pi.single j 1) := by
  classical
  simp_rw [bilinear_pi_expansion]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- Equal diagonals and ordered off-diagonal Gram entries order the Hessian contraction. -/
lemma bilinear_gram_comparison {m n : ℕ}
    (L M : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ))
    (B : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) →L[ℝ] ℝ)
    (hdiag : ∀ i : Fin m, (∑ k : Fin n, (L (Pi.single k 1) i) ^ 2) =
      ∑ k : Fin n, (M (Pi.single k 1) i) ^ 2)
    (hcov : ∀ i j : Fin m, (∑ k : Fin n, M (Pi.single k 1) i * M (Pi.single k 1) j) ≤
      ∑ k : Fin n, L (Pi.single k 1) i * L (Pi.single k 1) j)
    (hB : ∀ i j : Fin m, i ≠ j → 0 ≤ B (Pi.single i 1) (Pi.single j 1)) :
    (∑ k : Fin n, B (M (Pi.single k 1)) (M (Pi.single k 1))) ≤
      ∑ k : Fin n, B (L (Pi.single k 1)) (L (Pi.single k 1)) := by
  rw [sum_bilinear_image_eq_gram, sum_bilinear_image_eq_gram]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  by_cases hij : i = j
  · subst j
    have h := hdiag i
    simp only [pow_two] at h
    rw [h]
  · exact mul_le_mul_of_nonneg_right (hcov i j) (hB i j hij)

/-- The cross terms vanish when the two linear images use disjoint Gaussian coordinates. -/
lemma bilinear_disjoint_rotation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] ℝ) (a b : E) (c s : ℝ) (hab : a = 0 ∨ b = 0) :
    B (c • a + s • b) (-s • a + c • b) =
      (c * s) * (B b b - B a a) := by
  rcases hab with rfl | rfl <;>
    simp only [smul_zero, zero_add, add_zero, map_zero, zero_apply,
      map_smul, smul_apply, smul_eq_mul] <;> ring

end SlepianProof
end

-- Inlined module: SlepianFunctional
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- Functional Slepian comparison for independent linear Gaussian images.
The disjoint-column hypothesis expresses the independent-copy construction. -/
lemma slepian_functional_linear {m n : ℕ}
    (L M : (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ))
    (hindep : ∀ k : Fin (n + 1), L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0)
    (hdiag : ∀ i : Fin m, (∑ k : Fin (n + 1), (L (Pi.single k 1) i) ^ 2) =
      ∑ k : Fin (n + 1), (M (Pi.single k 1) i) ^ 2)
    (hcov : ∀ i j : Fin m,
      (∑ k : Fin (n + 1), M (Pi.single k 1) i * M (Pi.single k 1) j) ≤
        ∑ k : Fin (n + 1), L (Pi.single k 1) i * L (Pi.single k 1) j)
    (f : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin m), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    (∫ x, f (M x) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) ≤
      ∫ x, f (L x) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1) := by
  classical
  let μ := Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)
  let Z (θ : ℝ) (x : Fin (n + 1) → ℝ) := Real.cos θ • L x + Real.sin θ • M x
  let U (θ : ℝ) (i : Fin (n + 1)) :=
    Real.cos θ • L (Pi.single i 1) + Real.sin θ • M (Pi.single i 1)
  let V (θ : ℝ) (i : Fin (n + 1)) :=
    -Real.sin θ • L (Pi.single i 1) + Real.cos θ • M (Pi.single i 1)
  let B (y : Fin m → ℝ) := fderiv ℝ (fderiv ℝ f) y
  let g (θ : ℝ) := ∫ x, f (Z θ x) ∂μ
  let Q (θ : ℝ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℝ) := B (Z θ x) (U θ i) (V θ i)
  have hz (θ : ℝ) : Continuous (Z θ) := by
    dsimp [Z]
    fun_prop
  have hb : Continuous B := (hf.fderiv_right (by norm_num) :
    ContDiff ℝ 1 (fderiv ℝ f)).continuous_fderiv one_ne_zero
  have hqi (θ : ℝ) (i : Fin (n + 1)) : Integrable (Q θ i) μ := by
    have hc : Continuous (Q θ i) :=
      (((hb.comp (hz θ)).clm_apply continuous_const).clm_apply continuous_const)
    have he (x : Fin (n + 1) → ℝ) :
        ‖Q θ i x‖ ≤ H * ‖U θ i‖ * ‖V θ i‖ := by
      apply le_trans ((B (Z θ x)).le_opNorm₂ (U θ i) (V θ i))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hddf_bound _) (norm_nonneg _)) (norm_nonneg _)
    simpa using (integrable_const (1 : ℝ)).bdd_mul hc.aestronglyMeasurable (ae_of_all _ he)
  have hd (θ : ℝ) : HasDerivAt g (∑ i : Fin (n + 1), ∫ x, Q θ i x ∂μ) θ :=
    gaussian_rotation_interpolation L M f hf hf_bound hdf_bound hddf_bound θ
  have hnonpos (θ : ℝ) (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) :
      (∑ i : Fin (n + 1), ∫ x, Q θ i x ∂μ) ≤ 0 := by
    rw [← integral_finsetSum Finset.univ (fun i _ => hqi θ i)]
    apply integral_nonpos
    intro x
    have hcs : 0 ≤ Real.cos θ * Real.sin θ := mul_nonneg
      (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
      (Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [hθ.2, Real.pi_pos]⟩)
    have he (i : Fin (n + 1)) : Q θ i x = (Real.cos θ * Real.sin θ) *
        (B (Z θ x) (M (Pi.single i 1)) (M (Pi.single i 1)) -
          B (Z θ x) (L (Pi.single i 1)) (L (Pi.single i 1))) :=
      bilinear_disjoint_rotation (B (Z θ x)) _ _ _ _ (hindep i)
    simp_rw [he]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    apply mul_nonpos_of_nonneg_of_nonpos hcs
    exact sub_nonpos.mpr (bilinear_gram_comparison L M (B (Z θ x)) hdiag hcov
      (hpositive (Z θ x)))
  have hdiff : Differentiable ℝ g := fun θ => (hd θ).differentiableAt
  have hanti := antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) (Real.pi / 2))
    hdiff.continuous.continuousOn hdiff.differentiableOn
    (fun θ hθ => by rw [(hd θ).deriv]; exact hnonpos θ (Set.mem_of_mem_of_subset hθ interior_subset))
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have h := hanti ⟨le_rfl, hpi⟩ ⟨hpi, le_rfl⟩ hpi
  simpa [g, Z] using h

end SlepianProof
end

-- Inlined module: SlepianFunctionalIndex
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma slepian_functional_linear_index {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] {m : ℕ}
    (L M : (κ → ℝ) →L[ℝ] (Fin m → ℝ))
    (hindep : ∀ k : κ, L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0)
    (hdiag : ∀ i : Fin m, (∑ k : κ, (L (Pi.single k 1) i) ^ 2) =
      ∑ k : κ, (M (Pi.single k 1) i) ^ 2)
    (hcov : ∀ i j : Fin m,
      (∑ k : κ, M (Pi.single k 1) i * M (Pi.single k 1) j) ≤
        ∑ k : κ, L (Pi.single k 1) i * L (Pi.single k 1) j)
    (f : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin m), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    (∫ x, f (M x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤
      ∫ x, f (L x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let n := Fintype.card κ - 1
  have hc : n + 1 = Fintype.card κ := by
    have := Fintype.card_pos (α := κ)
    dsimp [n]
    omega
  let e : Fin (n + 1) ≃ κ := (finCongr hc).trans (Fintype.equivFin κ).symm
  let A : (Fin (n + 1) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x k := x (e.symm k)
      map_add' x y := rfl
      map_smul' c x := rfl }
  have ha (k : Fin (n + 1)) : A (Pi.single k 1) = Pi.single (e k) 1 := by
    ext j
    simp [A, Pi.single_apply, e.symm_apply_eq]
  have hd (i : Fin m) : (∑ k : Fin (n + 1), ((L.comp A) (Pi.single k 1) i) ^ 2) =
      ∑ k : Fin (n + 1), ((M.comp A) (Pi.single k 1) i) ^ 2 := by
    simp only [ContinuousLinearMap.comp_apply, ha]
    rw [e.sum_comp (fun k => (L (Pi.single k 1) i) ^ 2),
      e.sum_comp (fun k => (M (Pi.single k 1) i) ^ 2)]
    exact hdiag i
  have hv (i j : Fin m) :
      (∑ k : Fin (n + 1), (M.comp A) (Pi.single k 1) i * (M.comp A) (Pi.single k 1) j) ≤
        ∑ k : Fin (n + 1), (L.comp A) (Pi.single k 1) i * (L.comp A) (Pi.single k 1) j := by
    simp only [ContinuousLinearMap.comp_apply, ha]
    rw [e.sum_comp (fun k => M (Pi.single k 1) i * M (Pi.single k 1) j),
      e.sum_comp (fun k => L (Pi.single k 1) i * L (Pi.single k 1) j)]
    exact hcov i j
  have h := slepian_functional_linear (L.comp A) (M.comp A)
    (fun k => by simpa only [ContinuousLinearMap.comp_apply, ha] using hindep (e k))
    hd hv f hf hf_bound hdf_bound hddf_bound hpositive
  have hp := measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e
  have heA : (⇑(MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e)) = ⇑A := by
    ext x k
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply, A]
  have hM := hp.integral_comp' (fun x => f (M x))
  have hL := hp.integral_comp' (fun x => f (L x))
  rw [heA] at hM hL
  change (∫ x, f (M (A x)) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) = _ at hM
  change (∫ x, f (L (A x)) ∂Measure.pi (fun _ : Fin (n + 1) => gaussianReal 0 1)) = _ at hL
  simpa only [ContinuousLinearMap.comp_apply, hM, hL] using h

end SlepianProof
end

-- Inlined module: SlepianIndependentCopies
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma slepian_functional_independent_copies {κ : Type*} [Fintype κ] [Nonempty κ]
    [DecidableEq κ] {m : ℕ}
    (A B : (κ → ℝ) →L[ℝ] (Fin m → ℝ))
    (hdiag : ∀ i : Fin m, (∑ k : κ, (A (Pi.single k 1) i) ^ 2) =
      ∑ k : κ, (B (Pi.single k 1) i) ^ 2)
    (hcov : ∀ i j : Fin m,
      (∑ k : κ, B (Pi.single k 1) i * B (Pi.single k 1) j) ≤
        ∑ k : κ, A (Pi.single k 1) i * A (Pi.single k 1) j)
    (f : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin m), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    (∫ x, f (B x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) ≤
      ∫ x, f (A x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1) := by
  let p : ((κ ⊕ κ) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x i := x (Sum.inl i)
      map_add' x y := rfl
      map_smul' c x := rfl }
  let q : ((κ ⊕ κ) → ℝ) →L[ℝ] (κ → ℝ) :=
    { toFun x i := x (Sum.inr i)
      map_add' x y := rfl
      map_smul' c x := rfl }
  let L := A.comp p
  let M := B.comp q
  have hpl (k : κ) : p (Pi.single (Sum.inl k) 1) = Pi.single k 1 := by
    ext i
    simp [p, Pi.single_apply]
  have hpr (k : κ) : p (Pi.single (Sum.inr k) 1) = 0 := by
    ext i
    simp [p, Pi.single_apply]
  have hql (k : κ) : q (Pi.single (Sum.inl k) 1) = 0 := by
    ext i
    simp [q, Pi.single_apply]
  have hqr (k : κ) : q (Pi.single (Sum.inr k) 1) = Pi.single k 1 := by
    ext i
    simp [q, Pi.single_apply]
  have hindep (k : κ ⊕ κ) : L (Pi.single k 1) = 0 ∨ M (Pi.single k 1) = 0 := by
    cases k with
    | inl k => right; simp [M, hql]
    | inr k => left; simp [L, hpr]
  have hd (i : Fin m) : (∑ k : κ ⊕ κ, (L (Pi.single k 1) i) ^ 2) =
      ∑ k : κ ⊕ κ, (M (Pi.single k 1) i) ^ 2 := by
    simpa [L, M, Fintype.sum_sum_type, hpl, hpr, hql, hqr] using hdiag i
  have hv (i j : Fin m) :
      (∑ k : κ ⊕ κ, M (Pi.single k 1) i * M (Pi.single k 1) j) ≤
        ∑ k : κ ⊕ κ, L (Pi.single k 1) i * L (Pi.single k 1) j := by
    simpa [L, M, Fintype.sum_sum_type, hpl, hpr, hql, hqr] using hcov i j
  have h := slepian_functional_linear_index L M hindep hd hv f hf
    hf_bound hdf_bound hddf_bound hpositive
  let e := (MeasurableEquiv.sumPiEquivProdPi (fun _ : κ ⊕ κ => ℝ)).symm
  have hp := measurePreserving_sumPiEquivProdPi_symm (fun _ : κ ⊕ κ => gaussianReal 0 1)
  have hi (T : ((κ ⊕ κ) → ℝ) →L[ℝ] (Fin m → ℝ)) :
      Integrable (fun x => f (T x)) (Measure.pi (fun _ : κ ⊕ κ => gaussianReal 0 1)) := by
    simpa using (integrable_const (1 : ℝ)).bdd_mul
      (hf.continuous.comp T.continuous).aestronglyMeasurable
      (ae_of_all _ (fun x => hf_bound (T x)))
  have heL (x : (κ → ℝ) × (κ → ℝ)) : L (e x) = A x.1 := rfl
  have heM (x : (κ → ℝ) × (κ → ℝ)) : M (e x) = B x.2 := rfl
  have hL := hp.integral_comp' (fun x => f (L x))
  have hM := hp.integral_comp' (fun x => f (M x))
  have hiL := (hp.integrable_comp_emb e.measurableEmbedding).mpr (hi L)
  have hiM := (hp.integrable_comp_emb e.measurableEmbedding).mpr (hi M)
  simp only [Function.comp_def] at hiL hiM
  change (∫ x, f (L (e x)) ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : κ => gaussianReal 0 1))) = _ at hL
  change (∫ x, f (M (e x)) ∂(Measure.pi (fun _ : κ => gaussianReal 0 1)).prod
    (Measure.pi (fun _ : κ => gaussianReal 0 1))) = _ at hM
  rw [integral_prod _ hiL] at hL
  rw [integral_prod _ hiM] at hM
  change (∫ x, ∫ _y, f (A x) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
    ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hL
  change (∫ _x, ∫ y, f (B y) ∂Measure.pi (fun _ : κ => gaussianReal 0 1)
    ∂Measure.pi (fun _ : κ => gaussianReal 0 1)) = _ at hM
  simp only [integral_const, probReal_univ, one_smul] at hL hM
  rw [← hM, ← hL] at h
  exact h

end SlepianProof
end

-- Inlined module: SlepianFunctionalGaussian
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma slepian_functional_gaussian {m : ℕ} [Nonempty (Fin m)]
    (μ ν : Measure (Fin m → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (hmμ : (∫ x, x ∂μ) = 0) (hmν : (∫ x, x ∂ν) = 0)
    (hdiag : ∀ i : Fin m,
      cov[fun x => x i, fun x => x i; μ] = cov[fun x => x i, fun x => x i; ν])
    (hcov : ∀ i j : Fin m,
      cov[fun x => x i, fun x => x j; ν] ≤ cov[fun x => x i, fun x => x j; μ])
    (f : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin m), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    (∫ x, f x ∂ν) ≤ ∫ x, f x ∂μ := by
  obtain ⟨A, hA⟩ := centered_gaussian_eq_map_pi μ hmμ
  obtain ⟨B, hB⟩ := centered_gaussian_eq_map_pi ν hmν
  have hc (T : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ)) (i j : Fin m) :
      cov[fun x => x i, fun x => x j;
        (Measure.pi (fun _ : Fin m => gaussianReal 0 1)).map T] =
      ∑ k : Fin m, T (Pi.single k 1) i * T (Pi.single k 1) j := by
    rw [covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable T.continuous.measurable.aemeasurable]
    exact gaussian_pi_covariance_linear T i j
  have hd (i : Fin m) : (∑ k : Fin m, (A (Pi.single k 1) i) ^ 2) =
      ∑ k : Fin m, (B (Pi.single k 1) i) ^ 2 := by
    have h := hdiag i
    rw [hA, hB, hc, hc] at h
    simpa only [pow_two] using h
  have hv (i j : Fin m) :
      (∑ k : Fin m, B (Pi.single k 1) i * B (Pi.single k 1) j) ≤
        ∑ k : Fin m, A (Pi.single k 1) i * A (Pi.single k 1) j := by
    have h := hcov i j
    rwa [hA, hB, hc, hc] at h
  have h := slepian_functional_independent_copies A B hd hv f hf
    hf_bound hdf_bound hddf_bound hpositive
  rw [hA, hB, integral_map (by fun_prop) hf.continuous.aestronglyMeasurable,
    integral_map (by fun_prop) hf.continuous.aestronglyMeasurable]
  exact h

end SlepianProof
end

-- Inlined module: SlepianCovariance
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

/-- The moment assumptions in Slepian's inequality order the covariance matrices. -/
lemma covariance_comparison {Ω T : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : T → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) :
    (∀ i, cov[X i, X i; P] = cov[Y i, Y i; P]) ∧
      ∀ i j, cov[Y i, Y j; P] ≤ cov[X i, X j; P] := by
  have hvX (i : T) : Var[X i; P] = ∫ ω, (X i ω) ^ 2 ∂P := by
    simp only [variance_eq_integral (hXG.aemeasurable i), hXmean, sub_zero]
  have hvY (i : T) : Var[Y i; P] = ∫ ω, (Y i ω) ^ 2 ∂P := by
    simp only [variance_eq_integral (hYG.aemeasurable i), hYmean, sub_zero]
  have hv (i : T) : Var[X i; P] = Var[Y i; P] := by rw [hvX, hvY, hvar]
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · rw [covariance_self (hXG.aemeasurable i), covariance_self (hYG.aemeasurable i), hv]
  · have hmX : (∫ ω, X i ω - X j ω ∂P) = 0 := by
      rw [integral_sub (hXG.hasGaussianLaw_eval i).integrable
        (hXG.hasGaussianLaw_eval j).integrable, hXmean, hXmean, sub_self]
    have hmY : (∫ ω, Y i ω - Y j ω ∂P) = 0 := by
      rw [integral_sub (hYG.hasGaussianLaw_eval i).integrable
        (hYG.hasGaussianLaw_eval j).integrable, hYmean, hYmean, sub_self]
    have hx := variance_fun_sub (hXG.hasGaussianLaw_eval i).memLp_two
      (hXG.hasGaussianLaw_eval j).memLp_two
    have hy := variance_fun_sub (hYG.hasGaussianLaw_eval i).memLp_two
      (hYG.hasGaussianLaw_eval j).memLp_two
    rw [variance_eq_integral (X := fun ω => X i ω - X j ω) ((hXG.aemeasurable i).sub (hXG.aemeasurable j)), hmX] at hx
    rw [variance_eq_integral (X := fun ω => Y i ω - Y j ω) ((hYG.aemeasurable i).sub (hYG.aemeasurable j)), hmY] at hy
    simp only [sub_zero] at hx hy
    rw [hv i, hv j] at hx
    have hi := hinc i j
    linarith

end SlepianProof
end

-- Inlined module: SlepianFunctionalProcess
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma hasGaussianLaw_finite {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (X : ι → Ω → ℝ) (hXG : IsGaussianProcess X P) :
    HasGaussianLaw (fun ω i => X i ω) P := by
  let L : (↥(Finset.univ : Finset ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    { toFun x i := x ⟨i, Finset.mem_univ i⟩
      map_add' x y := rfl
      map_smul' c x := rfl }
  exact (hXG.hasGaussianLaw Finset.univ).map L

lemma slepian_functional_process {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    [Nonempty (Fin m)] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin m → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P)
    (f : (Fin m → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) {C D H : ℝ}
    (hf_bound : ∀ y, ‖f y‖ ≤ C)
    (hdf_bound : ∀ y, ‖fderiv ℝ f y‖ ≤ D)
    (hddf_bound : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hpositive : ∀ y (i j : Fin m), i ≠ j →
      0 ≤ (fderiv ℝ (fderiv ℝ f) y (Pi.single i 1)) (Pi.single j 1)) :
    (∫ ω, f (fun i => Y i ω) ∂P) ≤ ∫ ω, f (fun i => X i ω) ∂P := by
  let x : Ω → (Fin m → ℝ) := fun ω i => X i ω
  let y : Ω → (Fin m → ℝ) := fun ω i => Y i ω
  have hx := hasGaussianLaw_finite P X hXG
  have hy := hasGaussianLaw_finite P Y hYG
  let μ := P.map x
  let ν := P.map y
  haveI : IsGaussian μ := hx.isGaussian_map
  haveI : IsGaussian ν := hy.isGaussian_map
  have hmμ : (∫ z, z ∂μ) = 0 := by
    change (∫ z, id z ∂P.map x) = 0
    rw [integral_map hx.aemeasurable aestronglyMeasurable_id]
    ext i
    change (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) (∫ ω, x ω ∂P) = 0
    rw [← ContinuousLinearMap.integral_comp_comm _ hx.integrable]
    exact hXmean i
  have hmν : (∫ z, z ∂ν) = 0 := by
    change (∫ z, id z ∂P.map y) = 0
    rw [integral_map hy.aemeasurable aestronglyMeasurable_id]
    ext i
    change (ContinuousLinearMap.proj i : (Fin m → ℝ) →L[ℝ] ℝ) (∫ ω, y ω ∂P) = 0
    rw [← ContinuousLinearMap.integral_comp_comm _ hy.integrable]
    exact hYmean i
  have hcX (i j : Fin m) : cov[fun z => z i, fun z => z j; μ] = cov[X i, X j; P] := by
    exact covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable hx.aemeasurable
  have hcY (i j : Fin m) : cov[fun z => z i, fun z => z j; ν] = cov[Y i, Y j; P] := by
    exact covariance_map_fun (measurable_pi_apply i).aestronglyMeasurable
      (measurable_pi_apply j).aestronglyMeasurable hy.aemeasurable
  have hc := covariance_comparison P X Y hXG hYG hXmean hYmean hvar hinc
  have h := slepian_functional_gaussian μ ν hmμ hmν
    (fun i => by rw [hcX, hcY]; exact hc.1 i)
    (fun i j => by rw [hcX, hcY]; exact hc.2 i j)
    f hf hf_bound hdf_bound hddf_bound hpositive
  rw [integral_map hy.aemeasurable hf.continuous.aestronglyMeasurable,
    integral_map hx.aemeasurable hf.continuous.aestronglyMeasurable] at h
  exact h

end SlepianProof
end

-- Inlined module: SlepianTailMean
section

open MeasureTheory ProbabilityTheory Set

namespace SlepianProof

lemma integral_nonneg_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hYnonneg : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ t, 0 < t → P.real {ω | t ≤ X ω} ≤ P.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all P hXnonneg) hX.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all P hYnonneg) hY.aestronglyMeasurable]
  apply ENNReal.toReal_mono hY.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_le P (ae_of_all P hXnonneg) hX.aemeasurable,
    lintegral_eq_lintegral_meas_le P (ae_of_all P hYnonneg) hY.aemeasurable]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
    (htail t ht)

lemma integral_nonneg_le_of_strict_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (hXnonneg : ∀ ω, 0 ≤ X ω) (hYnonneg : ∀ ω, 0 ≤ Y ω)
    (htail : ∀ t, 0 < t → P.real {ω | t < X ω} ≤ P.real {ω | t < Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all P hXnonneg) hX.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all P hYnonneg) hY.aestronglyMeasurable]
  apply ENNReal.toReal_mono hY.lintegral_lt_top.ne
  rw [lintegral_eq_lintegral_meas_lt P (ae_of_all P hXnonneg) hX.aemeasurable,
    lintegral_eq_lintegral_meas_lt P (ae_of_all P hYnonneg) hY.aemeasurable]
  apply setLIntegral_mono' measurableSet_Ioi
  intro t ht
  exact (ENNReal.toReal_le_toReal (measure_ne_top P _) (measure_ne_top P _)).mp
    (htail t ht)

lemma integral_le_of_tail_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P)
    (htail : ∀ t : ℝ, P.real {ω | t ≤ X ω} ≤ P.real {ω | t ≤ Y ω}) :
    (∫ ω, X ω ∂P) ≤ ∫ ω, Y ω ∂P := by
  have hXp : Integrable (fun ω => max (X ω) 0) P := hX.sup (integrable_const 0)
  have hYp : Integrable (fun ω => max (Y ω) 0) P := hY.sup (integrable_const 0)
  have hXn : Integrable (fun ω => max (-X ω) 0) P := hX.neg.sup (integrable_const 0)
  have hYn : Integrable (fun ω => max (-Y ω) 0) P := hY.neg.sup (integrable_const 0)
  have hpos : (∫ ω, max (X ω) 0 ∂P) ≤ ∫ ω, max (Y ω) 0 ∂P := by
    apply integral_nonneg_le_of_tail_le P _ _ hXp hYp
      (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)
    intro t ht
    simpa only [le_max_iff, not_le.mpr ht, or_false] using htail t
  have hneg : (∫ ω, max (-Y ω) 0 ∂P) ≤ ∫ ω, max (-X ω) 0 ∂P := by
    apply integral_nonneg_le_of_strict_tail_le P _ _ hYn hXn
      (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)
    intro t ht
    have hx : P.real {ω | X ω < -t} = 1 - P.real {ω | -t ≤ X ω} := by
      convert probReal_compl_eq_one_sub₀
        (nullMeasurableSet_le aemeasurable_const hX.aemeasurable) using 1
      congr 1
      ext ω
      simp
    have hy : P.real {ω | Y ω < -t} = 1 - P.real {ω | -t ≤ Y ω} := by
      convert probReal_compl_eq_one_sub₀
        (nullMeasurableSet_le aemeasurable_const hY.aemeasurable) using 1
      congr 1
      ext ω
      simp
    have hsets (Z : Ω → ℝ) : {ω | t < max (-Z ω) 0} = {ω | Z ω < -t} := by
      ext ω
      simp only [mem_setOf_eq, lt_max_iff, not_lt.mpr ht.le, or_false]
      constructor <;> intro h <;> linarith
    rw [hsets Y, hsets X, hx, hy]
    linarith [htail (-t)]
  have hx : (∫ ω, X ω ∂P) = (∫ ω, max (X ω) 0 ∂P) - ∫ ω, max (-X ω) 0 ∂P := by
    rw [← integral_sub hXp hXn]
    congr 1
    funext ω
    exact (max_zero_sub_eq_self (X ω)).symm
  have hy : (∫ ω, Y ω ∂P) = (∫ ω, max (Y ω) 0 ∂P) - ∫ ω, max (-Y ω) 0 ∂P := by
    rw [← integral_sub hYp hYn]
    congr 1
    funext ω
    exact (max_zero_sub_eq_self (Y ω)).symm
  rw [hx, hy]
  linarith

end SlepianProof
end

-- Inlined module: SlepianFiniteTail
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma integrable_finset_sup' {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (s : Finset ι) (hs : s.Nonempty) (X : ι → Ω → ℝ)
    (hX : ∀ i ∈ s, Integrable (X i) P) :
    Integrable (fun ω => s.sup' hs (fun i => X i ω)) P := by
  have hi : Integrable (s.sup' hs X) P :=
    Finset.sup'_induction hs X (p := fun Z : Ω → ℝ => Integrable Z P)
      (fun _ hf _ hg => hf.sup hg) hX
  convert hi using 1
  funext ω
  exact (Finset.sup'_apply hs X ω).symm

lemma finite_gaussian_mean_comparison_of_tail_comparison {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ι → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (htail : ∀ t : ℝ,
      P.real {ω | t ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)} ≤
        P.real {ω | t ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω)}) :
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P) ≤
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by
  apply integral_le_of_tail_le P _ _
    (integrable_finset_sup' P Finset.univ Finset.univ_nonempty X
      (fun i _ => (hXG.hasGaussianLaw_eval i).integrable))
    (integrable_finset_sup' P Finset.univ Finset.univ_nonempty Y
      (fun i _ => (hYG.hasGaussianLaw_eval i).integrable)) htail

end SlepianProof
end

-- Inlined module: SlepianFinite
section

open MeasureTheory ProbabilityTheory

namespace SlepianProof

lemma slepian_finite_tail_fin {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    [Nonempty (Fin m)] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Fin m → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) (τ : ℝ) :
    P.real {ω | ∃ i, τ ≤ X i ω} ≤ P.real {ω | ∃ i, τ ≤ Y i ω} := by
  apply tail_comparison_of_cutoff_comparison P (fun ω i => X i ω) (fun ω i => Y i ω)
    (hasGaussianLaw_finite P X hXG).aemeasurable
    (hasGaussianLaw_finite P Y hYG).aemeasurable τ
  intro N
  obtain ⟨D, H, hd, hdd, hp⟩ := cutoffProd_admissible (ι := Fin m) τ N
  apply slepian_functional_process P X Y hXG hYG hXmean hYmean hvar hinc
    (cutoffProd τ N) (cutoffProd_contDiff τ N) (C := 1) (D := D) (H := H) _ hd hdd hp
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (cutoffProd_nonneg τ N x)]
  exact cutoffProd_le_one τ N x

lemma slepian_finite_tail {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : ι → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) (τ : ℝ) :
    P.real {ω | τ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω)} ≤
      P.real {ω | τ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω)} := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  letI : Nonempty (Fin (Fintype.card ι)) := ⟨e.symm (Classical.ofNonempty)⟩
  have h := slepian_finite_tail_fin P (fun i => X (e i)) (fun i => Y (e i))
    (hXG.comp_right e) (hYG.comp_right e)
    (fun i => hXmean (e i)) (fun i => hYmean (e i))
    (fun i => hvar (e i)) (fun i j => hinc (e i) (e j)) τ
  have he (Z : ι → Ω → ℝ) : {ω | ∃ i, τ ≤ Z (e i) ω} =
      {ω | τ ≤ Finset.univ.sup' Finset.univ_nonempty (fun i => Z i ω)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e i, hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa using hi⟩
  rw [he X, he Y] at h
  exact h

theorem slepian_finite_all_thresholds {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ι → Ω → ℝ)
    (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
    (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
    (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤
      ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P) (τ : ℝ) :
    (P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ≥ τ} ≤
      P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ≥ τ}) ∧
    (∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P) ≤
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by
  have ht := slepian_finite_tail P X Y hXG hYG hXmean hYmean hvar hinc
  exact ⟨ht τ, finite_gaussian_mean_comparison_of_tail_comparison P X Y hXG hYG ht⟩

end SlepianProof
end

open MeasureTheory ProbabilityTheory

theorem solution :
∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {ι : Type} [Fintype ι] [Nonempty ι] (X Y : ι → Ω → ℝ)
      (hXG : IsGaussianProcess X P) (hYG : IsGaussianProcess Y P)
      (hXmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hYmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
      (hvar : ∀ i, ∫ ω, (X i ω) ^ 2 ∂P = ∫ ω, (Y i ω) ^ 2 ∂P)
      (hinc : ∀ i j, ∫ ω, (X i ω - X j ω) ^ 2 ∂P ≤ ∫ ω, (Y i ω - Y j ω) ^ 2 ∂P)
      (τ : ℝ),
      (P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ≥ τ} ≤
        P.real {ω | Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ≥ τ}) ∧
      ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => X i ω) ∂P ≤
        ∫ ω, Finset.univ.sup' Finset.univ_nonempty (fun i => Y i ω) ∂P := by
  intro Ω _ P _ ι _ _ X Y hXG hYG hXmean hYmean hvar hinc τ
  exact SlepianProof.slepian_finite_all_thresholds P X Y hXG hYG hXmean hYmean hvar hinc τ
