-- Prove2me | solution 1 for JHolomorphic.exists_similarity_of_norm_dbar_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T11:47:55.862452+00:00
-- url     : https://prove2.me/submissions/36068c61-55c7-4d13-8e97-4b327e6ad39b

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_JHolomorphic_exists_memLp_sum_mul_apply_eq
import Theorems.Thm_JHolomorphic_memLp_clm_apply_of_continuousOn
import Theorems.Thm_JHolomorphic_memLp_of_continuousOn_compact
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_finset_sum
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_clm_apply
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Theorems.Thm_JHolomorphic_exists_local_weak_solution
import Theorems.Thm_JHolomorphic_differentiableOn_of_hasWeakPartialsOn



namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

/-- `v ↦ (r ↦ ∑ vᵢ rᵢ)`. -/
noncomputable def jhfBil {n : ℕ} (v : EuclideanSpace ℂ (Fin n)) :
    EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ :=
  ∑ i, v i • (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ)

theorem jhfBil_apply {n : ℕ} (v r : EuclideanSpace ℂ (Fin n)) :
    jhfBil v r = ∑ i, v i * r i := by
  simp [jhfBil]

/-- `v ↦ (r ↦ (∑ vᵢ rᵢ) eₖ)` as a real bilinear operator. -/
noncomputable def jhfT {n : ℕ} (k : Fin n) : EuclideanSpace ℂ (Fin n) →L[ℝ]
    (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ((jhfBil v).smulRight (EuclideanSpace.single k (1 : ℂ))).restrictScalars ℝ
      map_add' := by
        intro v w; ext r : 1
        simp [jhfBil_apply, add_mul, Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro c v; ext r : 1
        simp [jhfBil_apply, Finset.mul_sum, mul_assoc, smul_smul]
        rw [← Finset.mul_sum, ← smul_smul, Complex.coe_smul] }

theorem jhfT_apply {n : ℕ} (k : Fin n) (v r : EuclideanSpace ℂ (Fin n)) :
    jhfT k v r = (∑ i, v i * r i) • EuclideanSpace.single k (1 : ℂ) := by
  simp [jhfT, jhfBil_apply]

/-- Similarity principle on `ℂⁿ` under a differential inequality. -/
theorem exists_similarity_aux (n : ℕ) (ρ M : ℝ) (hρ : 0 < ρ) (g : ℂ → EuclideanSpace ℂ (Fin n))
    (hg : ContDiffOn ℝ 1 g (ball 0 ρ))
    (hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, g z = Φ z (f z) := by
  set w : ℂ → EuclideanSpace ℂ (Fin n) := fun z =>
    fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I with hw_def
  have hgc : ContinuousOn g (ball 0 ρ) := hg.continuousOn
  have hDc : ContinuousOn (fderiv ℝ g) (ball 0 ρ) :=
    hg.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hwc : ContinuousOn w (ball 0 ρ) :=
    (hDc.clm_apply continuousOn_const).add ((hDc.clm_apply continuousOn_const).const_smul Complex.I)
  obtain ⟨A, hAm, hAid⟩ := exists_memLp_sum_mul_apply_eq n ρ M hρ g w hgc hwc hM (ENNReal.ofReal 3)
  have hev : ∀ k : Fin n, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ u : ℂ → EuclideanSpace ℂ (Fin n),
      ContinuousOn u (ball 0 ε) ∧ u 0 = EuclideanSpace.single k (1 : ℂ) ∧
      ∃ us ut : ℂ → EuclideanSpace ℂ (Fin n), HasWeakPartialsOn (ball 0 ε) u us ut ∧
        MemLp u (ENNReal.ofReal 3) (volume.restrict (ball 0 ε)) ∧
        MemLp us (ENNReal.ofReal 3) (volume.restrict (ball 0 ε)) ∧
        MemLp ut (ENNReal.ofReal 3) (volume.restrict (ball 0 ε)) ∧
        ∀ᵐ z ∂(volume.restrict (ball 0 ε)), us z + Complex.I • ut z + A z (u z) = 0 :=
    fun k => exists_local_weak_solution n 3 (by norm_num) A hAm _
  have hρ2 : (0 : ℝ) < ρ / 2 := by linarith
  obtain ⟨ε₁, hall, hε₁⟩ :=
    ((Filter.eventually_all.2 hev).and (Ioo_mem_nhdsGT hρ2)).exists
  choose r hrc hr0 rs rt hW hr hrs hrt heq using hall
  have hε₁0 : 0 < ε₁ := hε₁.1
  have hε₁ρ : ball (0 : ℂ) ε₁ ⊆ ball 0 ρ := ball_subset_ball (by linarith [hε₁.2])
  -- the matrix of rows
  let Λ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) := fun z =>
    ∑ k, ∑ i, r k z i • (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).smulRight
      (EuclideanSpace.single k (1 : ℂ))
  have hΛ : ∀ z v, Λ z v = ∑ k, (∑ i, r k z i * v i) • EuclideanSpace.single k (1 : ℂ) := by
    intro z v; simp [Λ, Finset.sum_smul, smul_smul]
  have hΛc : ContinuousOn Λ (ball 0 ε₁) := by
    refine continuousOn_finset_sum _ fun k _ => continuousOn_finset_sum _ fun i _ => ?_
    exact (((EuclideanSpace.proj i : EuclideanSpace ℂ (Fin n) →L[ℂ] ℂ).continuous.comp_continuousOn
      (hrc k))).smul continuousOn_const
  have hΛ0 : Λ 0 = 1 := by
    ext v j
    simp [hΛ, hr0, EuclideanSpace.single_apply, Pi.single_apply, WithLp.ofLp_sum]
  -- invertibility near `0`
  have hU : IsOpen {T : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) | IsUnit T} :=
    Units.isOpen
  have hnhds : Λ ⁻¹' {T | IsUnit T} ∩ ball 0 ε₁ ∈ 𝓝 (0 : ℂ) := by
    refine inter_mem ?_ (ball_mem_nhds _ hε₁0)
    have hc0 : ContinuousAt Λ 0 := hΛc.continuousAt (ball_mem_nhds _ hε₁0)
    exact hc0.preimage_mem_nhds (hU.mem_nhds (by rw [hΛ0]; exact isUnit_one))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.1 hnhds
  set ε := δ / 2 with hε_def
  have hε : 0 < ε := by positivity
  have hεδ : closedBall (0 : ℂ) ε ⊆ ball 0 δ := closedBall_subset_ball (by linarith)
  have hunit : ∀ z ∈ closedBall (0 : ℂ) ε, IsUnit (Λ z) := fun z hz => (hδsub (hεδ hz)).1
  have hsub1 : closedBall (0 : ℂ) ε ⊆ ball 0 ε₁ := fun z hz => (hδsub (hεδ hz)).2
  have hsubε : ball (0 : ℂ) ε ⊆ ball 0 ε₁ := ball_subset_closedBall.trans hsub1
  let f : ℂ → EuclideanSpace ℂ (Fin n) := fun z => ∑ k, jhfT k (g z) (r k z)
  have hfΛ : ∀ z, f z = Λ z (g z) := by
    intro z
    simp only [f, jhfT_apply, hΛ]
    exact Finset.sum_congr rfl fun k _ => by rw [Finset.sum_congr rfl fun i _ => mul_comm _ _]
  refine ⟨ε, hε, fun z => Ring.inverse (Λ z), f, ?_, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨u, hu⟩ := hunit z hz
    have h1 := NormedRing.inverse_continuousAt u
    rw [hu] at h1
    exact h1.comp_continuousWithinAt ((hΛc z (hsub1 hz)).mono hsub1)
  · intro z hz
    obtain ⟨u, hu⟩ := (hunit z hz).ringInverse
    change Function.Bijective (DFunLike.coe (Ring.inverse (Λ z)))
    rw [← hu]
    refine Function.bijective_iff_has_inverse.2 ⟨⇑(↑u⁻¹ : EuclideanSpace ℂ (Fin n) →L[ℂ]
      EuclideanSpace ℂ (Fin n)), fun x => ?_, fun x => ?_⟩
    · change ((↑u⁻¹ * ↑u : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) x) = x
      rw [Units.inv_mul]; rfl
    · change ((↑u * ↑u⁻¹ : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) x) = x
      rw [Units.mul_inv]; rfl
  · have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3 := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
    have hMK : ∀ h : ℂ → EuclideanSpace ℂ (Fin n),
        MemLp h (ENNReal.ofReal 3) (volume.restrict (ball 0 ε₁)) → ∀ K ⊆ ball (0 : ℂ) ε,
          MemLp h (ENNReal.ofReal 3) (volume.restrict K) :=
      fun h hh K hK => hh.mono_measure (Measure.restrict_mono (hK.trans hsubε) le_rfl)
    let B : Fin n → ℂ → (EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n)) :=
      fun k z => jhfT k (g z)
    have hBd : ∀ k, ContDiffOn ℝ 1 (B k) (ball 0 ε) := fun k =>
      (jhfT k).contDiff.comp_contDiffOn (hg.mono (hsubε.trans hε₁ρ))
    have hBc : ∀ k, ContinuousOn (B k) (ball 0 ε) := fun k => (hBd k).continuousOn
    have hBDc : ∀ k, ContinuousOn (fderiv ℝ (B k)) (ball 0 ε) := fun k =>
      (hBd k).continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
    have hrcε : ∀ k, ContinuousOn (r k) (ball 0 ε) := fun k => (hrc k).mono hsubε
    have hWk : ∀ k, HasWeakPartialsOn (ball 0 ε) (r k) (rs k) (rt k) :=
      fun k φ h1 h2 h3 => hW k φ h1 h2 (h3.trans hsubε)
    have hfin : ∀ K : Set ℂ, IsCompact K → IsFiniteMeasure (volume.restrict K) :=
      fun K hK => isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    have hintk : ∀ k, ∀ K ⊆ ball (0 : ℂ) ε, IsCompact K →
        IntegrableOn (r k) K ∧ IntegrableOn (rs k) K ∧ IntegrableOn (rt k) K := by
      intro k K hK hKc
      haveI := hfin K hKc
      exact ⟨(memLp_of_continuousOn_compact hKc ((hrcε k).mono hK)).integrable hp1,
        ((hMK _ (hrs k) K hK).mono_exponent hp1).integrable le_rfl,
        ((hMK _ (hrt k) K hK).mono_exponent hp1).integrable le_rfl⟩
    have hterm := fun k => HasWeakPartialsOn.clm_apply isOpen_ball (hBd k) (hWk k) (hintk k)
    have hmem : ∀ k, ∀ K ⊆ ball (0 : ℂ) ε, IsCompact K →
        MemLp (fun z => B k z (r k z)) (ENNReal.ofReal 3) (volume.restrict K) ∧
        MemLp (fun z => fderiv ℝ (B k) z 1 (r k z) + B k z (rs k z))
          (ENNReal.ofReal 3) (volume.restrict K) ∧
        MemLp (fun z => fderiv ℝ (B k) z Complex.I (r k z) + B k z (rt k z))
          (ENNReal.ofReal 3) (volume.restrict K) := by
      intro k K hK hKc
      have hrK := memLp_of_continuousOn_compact (p := ENNReal.ofReal 3) hKc ((hrcε k).mono hK)
      refine ⟨memLp_of_continuousOn_compact hKc (((hBc k).clm_apply (hrcε k)).mono hK), ?_, ?_⟩
      · exact (memLp_clm_apply_of_continuousOn hKc
          (((hBDc k).clm_apply continuousOn_const).mono hK) hrK).add
          (memLp_clm_apply_of_continuousOn hKc ((hBc k).mono hK) (hMK _ (hrs k) K hK))
      · exact (memLp_clm_apply_of_continuousOn hKc
          (((hBDc k).clm_apply continuousOn_const).mono hK) hrK).add
          (memLp_clm_apply_of_continuousOn hKc ((hBc k).mono hK) (hMK _ (hrt k) K hK))
    have hsum := HasWeakPartialsOn.finset_sum Finset.univ (fun k _ => hterm k)
      (fun k _ K hK hKc => by
        haveI := hfin K hKc
        obtain ⟨h1, h2, h3⟩ := hmem k K hK hKc
        exact ⟨h1.integrable hp1, h2.integrable hp1, h3.integrable hp1⟩)
    have hfc : ContinuousOn f (ball 0 ε) :=
      continuousOn_finset_sum _ fun k _ => (hBc k).clm_apply (hrcε k)
    refine differentiableOn_of_hasWeakPartialsOn n 3 (by norm_num) isOpen_ball f _ _ hfc hsum
      (fun K hK hKc => ⟨memLp_of_continuousOn_compact hKc (hfc.mono hK),
        memLp_finsetSum _ fun k _ => (hmem k K hK hKc).2.1,
        memLp_finsetSum _ fun k _ => (hmem k K hK hKc).2.2⟩) ?_
    have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) ε)),
        ∀ k, rs k z + Complex.I • rt k z + A z (r k z) = 0 := by
      rw [ae_all_iff]; intro k
      exact ae_restrict_of_ae_restrict_of_subset hsubε (heq k)
    filter_upwards [hae, ae_restrict_mem measurableSet_ball] with z hz hzb
    have hzρ : z ∈ ball (0 : ℂ) ρ := hε₁ρ (hsubε hzb)
    have hzS : z ∈ closedBall (0 : ℂ) (ρ / 2) := by
      have := hsubε hzb
      rw [mem_ball] at this; rw [mem_closedBall]; linarith [hε₁.2]
    have hgd : DifferentiableAt ℝ g z :=
      (hg.differentiableOn one_ne_zero z hzρ).differentiableAt (isOpen_ball.mem_nhds hzρ)
    have hBder : ∀ k, fderiv ℝ (B k) z = (jhfT k).comp (fderiv ℝ g z) := fun k =>
      ((jhfT k).hasFDerivAt.comp z hgd.hasFDerivAt).fderiv
    simp only [hBder, ContinuousLinearMap.comp_apply, B]
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    have key : ∀ i, rs k z i + Complex.I * rt k z i = -(A z (r k z) i) := by
      intro i
      have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v i) (hz k)
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, PiLp.zero_apply] at this
      exact eq_neg_of_add_eq_zero_left this
    have hwi : ∀ i, w z i = fderiv ℝ g z 1 i + Complex.I * fderiv ℝ g z Complex.I i := by
      intro i; simp [w]
    have hid := hAid z hzS (r k z)
    simp only [jhfT_apply]
    rw [← add_smul, ← add_smul, smul_smul, ← add_smul]
    have hS : (∑ i, fderiv ℝ g z 1 i * r k z i) + (∑ i, g z i * rs k z i) +
        Complex.I * ((∑ i, fderiv ℝ g z Complex.I i * r k z i) + ∑ i, g z i * rt k z i) =
        (∑ i, w z i * r k z i) + ∑ i, g z i * (rs k z i + Complex.I * rt k z i) := by
      simp only [hwi, Finset.mul_sum, add_mul, mul_add, Finset.sum_add_distrib]
      ring
    rw [hS]
    simp only [key, mul_neg, Finset.sum_neg_distrib, hid, add_neg_cancel, zero_smul]
  · intro z hz
    rw [hfΛ]
    change g z = (Ring.inverse (Λ z) * Λ z) (g z)
    rw [Ring.inverse_mul_cancel _ (hunit z (ball_subset_closedBall hz))]
    rfl

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal

theorem solution (n : ℕ) (ρ M : ℝ) (hρ : 0 < ρ) (g : ℂ → EuclideanSpace ℂ (Fin n))
    (hg : ContDiffOn ℝ 1 g (ball 0 ρ))
    (hM : ∀ z ∈ ball (0 : ℂ) ρ,
      ‖fderiv ℝ g z 1 + Complex.I • fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖) :
    ∃ ε > (0 : ℝ), ∃ Φ : ℂ → EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n),
      ∃ f : ℂ → EuclideanSpace ℂ (Fin n), ContinuousOn Φ (closedBall 0 ε) ∧
        (∀ z ∈ closedBall (0 : ℂ) ε, Function.Bijective (Φ z)) ∧
        DifferentiableOn ℂ f (ball 0 ε) ∧ ∀ z ∈ ball (0 : ℂ) ε, g z = Φ z (f z) :=
  exists_similarity_aux n ρ M hρ g hg hM
