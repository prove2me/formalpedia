-- Prove2me | solution 1 for LogLogJam.history_reference_density
-- status  : ACCEPTED   (prove)
-- author  : @Senrui Chen
-- created : 2026-11-26T09:37:15.458124+00:00
-- url     : https://prove2.me/submissions/83c27705-c8cd-4945-bf7c-baf80e125c84

import Theorems.Thm_LogLogJam_gaussian_seed_mass_one
import Theorems.Thm_LogLogJam_history_reference_path_law
import Theorems.Thm_LogLogJam_physical_history_likelihood

open LogLogJam Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal

private theorem sigmaPositive {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (u : X → ℝ) (hp : ∀ x, 0 < u x) (hm : Measurable u)
    (hn : ∫⁻ x, ENNReal.ofReal (u x) ∂μ = 1) : SigmaFinite μ := by
  let r (n : ℕ) := ENNReal.ofReal (1 / (n + 1 : ℝ))
  have hr n : r n ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  refine ⟨⟨⟨(fun n => {x | r n ≤ ENNReal.ofReal (u x)}), fun _ => Set.mem_univ _, ?_, ?_⟩⟩⟩
  · intro n
    have h := meas_ge_le_lintegral_div (μ := μ) hm.ennreal_ofReal.aemeasurable (hr n) ENNReal.ofReal_ne_top
    rw [hn] at h
    exact h.trans_lt (ENNReal.div_lt_top (by simp) (hr n))
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hp x)
    exact Set.mem_iUnion.mpr ⟨n, ENNReal.ofReal_le_ofReal hn.le⟩

private theorem sigma_meas_slice {ι : Type*} {B : ι → Type*} [∀ i, MeasurableSpace (B i)]
    {Y : Type*} [MeasurableSpace Y] (f : (Σ i, B i) → Y)
    (h : ∀ i, Measurable (fun x : B i => f ⟨i,x⟩)) : Measurable f := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun i => h i hs)

private theorem meas_density_pair (k : ℕ) (V : Matrix (Q k) (Q k) ℝ) :
    Measurable fun p : (Q k → Q k → ℝ) × (Q k → ℝ) =>
      outDens k (V + Matrix.of p.1) p.2 := by
  let D (p : (Q k → Q k → ℝ) × (Q k → ℝ)) : Matrix (Q k) (Q k) ℝ := V + Matrix.of p.1
  have hD : Continuous D := continuous_const.add continuous_fst
  have hi (i j : Q k) : Measurable (fun p => (D p)⁻¹ i j) := by
    simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
    exact hD.matrix_det.measurable.inv.mul
      ((continuous_apply j).comp ((continuous_apply i).comp hD.matrix_adjugate)).measurable
  change Measurable (fun p => Real.exp (-(p.2 ⬝ᵥ ((D p)⁻¹ *ᵥ p.2))) /
    (Real.pi ^ k * Real.sqrt (D p).det))
  simp only [dotProduct, Matrix.mulVec]
  have hy (i : Q k) : Measurable (fun p : (Q k → Q k → ℝ) × (Q k → ℝ) => p.2 i) :=
    (measurable_pi_apply i).comp measurable_snd
  apply Measurable.div
  · apply Real.continuous_exp.measurable.comp
    apply Measurable.neg
    exact Finset.measurable_fun_sum _ fun i _ => (hy i).mul (Finset.measurable_fun_sum _ fun j _ =>
      (hi i j).mul (hy j))
  · exact measurable_const.mul (Real.continuous_sqrt.measurable.comp hD.matrix_det.measurable)

private noncomputable def stepInt {t : ℕ} {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ)
    (F : Hist (t+1) → ℝ≥0∞) (H : Hist t) : ℝ≥0∞ :=
  ∫⁻ s, ∫⁻ y, ENNReal.ofReal (outDens s.1 (VsqK lam θ s.1 + Matrix.of s.2) y) *
       F (Fin.snoc H ⟨s.1,(s.2,y)⟩) ∂volume ∂(P.seed t H)

private theorem hist_const {T : ℕ} (P : GaussProtocol T) (lam θ : ℝ) (hlam : 1 < lam) (t : ℕ) (c : ℝ≥0∞) (hc : c ≠ ⊤) :
      histInt lam θ P t (fun _ => c) = c := by
    induction t with
    | zero => rfl
    | succ t ih =>
      change histInt lam θ P t (stepInt P lam θ (fun _ => c)) = c
      apply Eq.trans _ ih
      apply congrArg (histInt lam θ P t)
      funext H
      have := P.isMarkov t
      unfold stepInt
      simp only [lintegral_mul_const' c _ hc]
      have hm : (fun s : Seed => (∫⁻ y, ENNReal.ofReal
          (outDens s.1 (VsqK lam θ s.1 + Matrix.of s.2) y))) =ᵐ[P.seed t H] fun _ => 1 := by
        filter_upwards [P.seed_cov t H] with s hs
        exact gaussian_seed_mass_one lam θ hlam s.1 s.2 hs
      rw [lintegral_congr_ae hm]
      simp

private theorem meas_hist (t : ℕ) (lam θ : ℝ) :
    Measurable (fun H : Hist t => histDens lam θ H) := by
  have ho : Measurable (obsDens lam θ) :=
    sigma_meas_slice _ (fun k => meas_density_pair k (VsqK lam θ k))
  exact Finset.measurable_fun_prod _ (fun i _ => ho.comp (measurable_pi_apply i))

theorem solution {T : ℕ} (P : GaussProtocol T) (t : ℕ) (ht : t ≤ T) :
    let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
    ∃ μ : Measure G, SigmaFinite μ ∧ ∀ l : ℝ, 1 < l →
      (∀ (s : ℝ) (H : G), 0 < histDens l s H.1) ∧
      (∀ (s : ℝ) (H : G), histDens l (s+Real.pi) H.1 = histDens l s H.1) ∧
      (∀ H : G, ContDiff ℝ 1 (fun s => histDens l s H.1)) ∧
      (∀ s : ℝ, Measurable (fun H : G => histDens l s H.1)) ∧
      (∀ s : ℝ, ∫⁻ H : G, ENNReal.ofReal (histDens l s H.1) ∂μ = 1) ∧
      (∀ (s : ℝ) (Φ : Hist t → ℝ≥0∞), Measurable (fun H : G => Φ H.1) →
        histInt l s P t Φ = ∫⁻ H : G, ENNReal.ofReal (histDens l s H.1) * Φ H.1 ∂μ) := by
  let G := {H : Hist t // ∀ i, IsCov (H i).1 (Matrix.of (H i).2.1)}
  obtain ⟨μ, hre⟩ := history_reference_path_law P t ht
  have hnorm (l s : ℝ) (hl : 1 < l) :
      ∫⁻ H : G, ENNReal.ofReal (histDens l s H.1) ∂μ = 1 := by
    have h := hre l hl s (fun _ => 1) measurable_const
    simpa only [mul_one,hist_const P l s hl t 1 (by simp)] using h.symm
  have hm (l s : ℝ) : Measurable (fun H : G => histDens l s H.1) :=
    (meas_hist t l s).comp measurable_subtype_coe
  have hsf := sigmaPositive μ (fun H : G => histDens 2 0 H.1)
    (fun H => (physical_history_likelihood 2 (by norm_num) H.1 H.2).1 0)
    (hm 2 0) (hnorm 2 0 (by norm_num))
  refine ⟨μ,hsf,fun l hl => ?_⟩
  have hr (H : G) := physical_history_likelihood l hl H.1 H.2
  exact ⟨fun s H => (hr H).1 s,fun s H => (hr H).2.1 s,fun H => (hr H).2.2,
    hm l,fun s => hnorm l s hl,hre l hl⟩
