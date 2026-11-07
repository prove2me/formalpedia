-- Prove2me | solution 1 for ManyServerQED.Scheduling.proposition_4_i
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:06:48.266113+00:00
-- url     : https://prove2.me/submissions/1c4035b1-3a7b-46b6-89b5-faca35a018fe

import Mathlib
import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

namespace Prop4iAux

lemma l1norm_nonneg {k : ℕ} (x : Fin k → ℝ) : 0 ≤ l1norm x :=
  Finset.sum_nonneg (fun i _ => abs_nonneg _)

lemma l1norm_add_le {k : ℕ} (x y : Fin k → ℝ) : l1norm (x + y) ≤ l1norm x + l1norm y := by
  unfold l1norm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun i _ => abs_add_le _ _)

lemma l1norm_continuous {k : ℕ} : Continuous (fun x : Fin k → ℝ => l1norm x) := by
  unfold l1norm
  exact continuous_finset_sum _ (fun i _ => (continuous_apply i).abs)

lemma comp_ii {k : ℕ} {g : ℝ → Fin k → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
    (i : Fin k) : IntervalIntegrable (fun s => g s i) volume a b :=
  ⟨(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).integrable_comp hg.1,
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).integrable_comp hg.2⟩

lemma l1_ii {k : ℕ} {g : ℝ → Fin k → ℝ} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun s => l1norm (g s)) volume a b := by
  unfold l1norm
  have : (fun s => ∑ i, |g s i|) = ∑ i, (fun s => |g s i|) := by funext s; simp
  rw [this]
  exact IntervalIntegrable.sum _ (fun i _ => (comp_ii hg i).abs)

lemma l1_integral_le {k : ℕ} (g : ℝ → Fin k → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hg : IntervalIntegrable g volume 0 t) :
    l1norm (∫ s in (0 : ℝ)..t, g s) ≤ ∫ s in (0 : ℝ)..t, l1norm (g s) := by
  have hcomp : ∀ i, (∫ s in (0 : ℝ)..t, g s) i = ∫ s in (0 : ℝ)..t, g s i := by
    intro i
    exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i).intervalIntegral_comp_comm
      hg).symm
  unfold l1norm
  rw [intervalIntegral.integral_finsetSum (fun i _ => (comp_ii hg i).abs)]
  apply Finset.sum_le_sum
  intro i _
  rw [hcomp i]
  exact intervalIntegral.abs_integral_le_integral_abs ht

lemma drift_lip {k : ℕ} (D : DiffusionData k) (y z u : Fin k → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin k)) :
    l1norm (drift D y u - drift D z u) ≤
      (∑ i, (|D.mu i - D.theta i| + D.mu i)) * l1norm (y - z) := by
  set Lyz := l1norm (y - z)
  have hcoord : ∀ i, |(y - z) i| ≤ Lyz := fun i =>
    Finset.single_le_sum (f := fun j => |(y - z) j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hmax : |max (∑ j, y j) 0 - max (∑ j, z j) 0| ≤ Lyz := by
    refine (abs_max_sub_max_le_abs _ _ _).trans ?_
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    rfl
  unfold l1norm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hui0 : 0 ≤ u i := hu.1 i
  have hui1 : u i ≤ 1 := by
    have := Finset.single_le_sum (f := u) (fun j _ => hu.1 j) (Finset.mem_univ i)
    rw [hu.2] at this; exact this
  have e : (drift D y u - drift D z u) i =
      (D.mu i - D.theta i) * (max (∑ j, y j) 0 - max (∑ j, z j) 0) * u i - D.mu i * (y - z) i := by
    simp only [Pi.sub_apply, drift]; ring
  rw [e]
  have hmu := D.mu_pos i
  calc |(D.mu i - D.theta i) * (max (∑ j, y j) 0 - max (∑ j, z j) 0) * u i - D.mu i * (y - z) i|
      ≤ |(D.mu i - D.theta i) * (max (∑ j, y j) 0 - max (∑ j, z j) 0) * u i| +
          |D.mu i * (y - z) i| := abs_sub _ _
    _ = |D.mu i - D.theta i| * |max (∑ j, y j) 0 - max (∑ j, z j) 0| * u i +
          D.mu i * |(y - z) i| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hui0, abs_of_pos hmu]
    _ ≤ |D.mu i - D.theta i| * Lyz * 1 + D.mu i * Lyz := by
        have hL0 : 0 ≤ Lyz := l1norm_nonneg _
        have a1 : |D.mu i - D.theta i| * |max (∑ j, y j) 0 - max (∑ j, z j) 0| * u i ≤
            |D.mu i - D.theta i| * Lyz * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hmax (abs_nonneg _)) hui1 hui0
            (mul_nonneg (abs_nonneg _) hL0)
        have a2 := mul_le_mul_of_nonneg_left (hcoord i) hmu.le
        linarith
    _ = (|D.mu i - D.theta i| + D.mu i) * Lyz := by ring

end Prop4iAux

open Prop4iAux

theorem solution {k : ℕ} [NeZero k] (D : DiffusionData k) :
    ∃ c : ℝ, ∀ (π : AdmissibleSystem k) (x xbar : Fin k → ℝ) (X Xbar : ℝ≥0 → π.Ω → Fin k → ℝ),
      IsControlledProcess D π x X → IsControlledProcess D π xbar Xbar →
        ∀ᵐ ω ∂π.P, ∀ t : ℝ≥0,
          l1norm (X t ω - Xbar t ω) ≤ l1norm (x - xbar) * (1 + Real.exp (c * t)) := by
  set c : ℝ := ∑ i, (|D.mu i - D.theta i| + D.mu i) with hc
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun i _ => by have := D.mu_pos i; positivity)
  refine ⟨c, ?_⟩
  intro π x xbar X Xbar hX hXb
  filter_upwards [hX.eq27, hXb.eq27, hX.integrable, hXb.integrable] with ω h1 h2 h3 h4
  intro t
  set gA : ℝ → Fin k → ℝ := fun s => drift D (X s.toNNReal ω) (π.u s.toNNReal ω) with hgA
  set gB : ℝ → Fin k → ℝ := fun s => drift D (Xbar s.toNNReal ω) (π.u s.toNNReal ω) with hgB
  set φ : ℝ → ℝ := fun s => l1norm (X s.toNNReal ω - Xbar s.toNNReal ω) with hφ
  set δ : ℝ := l1norm (x - xbar)
  have hδ : 0 ≤ δ := l1norm_nonneg _
  have hφc : Continuous φ := l1norm_continuous.comp
    (((hX.cont ω).comp continuous_real_toNNReal).sub ((hXb.cont ω).comp continuous_real_toNNReal))
  have hφ0 : ∀ s, 0 ≤ φ s := fun s => l1norm_nonneg _
  have hiiA : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable gA volume 0 T := fun T hT =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ((h3 T hT).mono_set Set.Ioc_subset_Icc_self)
  have hiiB : ∀ T : ℝ, 0 ≤ T → IntervalIntegrable gB volume 0 T := fun T hT =>
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 ((h4 T hT).mono_set Set.Ioc_subset_Icc_self)
  set ψ : ℝ → ℝ := fun T => δ + ∫ s in (0 : ℝ)..T, c * φ s with hψ
  have hcφc : Continuous (fun s => c * φ s) := continuous_const.mul hφc
  have hψd : ∀ T, HasDerivAt ψ (c * φ T) T := fun T =>
    ((hcφc.integral_hasStrictDerivAt 0 T).hasDerivAt).const_add δ
  have hψc : Continuous ψ := continuous_iff_continuousAt.2 (fun T => (hψd T).continuousAt)
  -- φ ≤ ψ on [0, ∞)
  have hle : ∀ T : ℝ, 0 ≤ T → φ T ≤ ψ T := by
    intro T hT
    have e1 := h1 T.toNNReal
    have e2 := h2 T.toNNReal
    rw [Real.coe_toNNReal T hT] at e1 e2
    have hdiff : X T.toNNReal ω - Xbar T.toNNReal ω =
        (x - xbar) + ∫ s in (0 : ℝ)..T, (gA s - gB s) := by
      rw [intervalIntegral.integral_sub (hiiA T hT) (hiiB T hT), e1, e2]
      abel
    have hint : IntervalIntegrable (fun s => l1norm (gA s - gB s)) volume 0 T :=
      l1_ii ((hiiA T hT).sub (hiiB T hT))
    show l1norm (X T.toNNReal ω - Xbar T.toNNReal ω) ≤ δ + ∫ s in (0 : ℝ)..T, c * φ s
    rw [hdiff]
    refine (l1norm_add_le _ _).trans (add_le_add_right ?_ _)
    refine (l1_integral_le _ T hT ((hiiA T hT).sub (hiiB T hT))).trans ?_
    apply intervalIntegral.integral_mono_on hT hint (hcφc.intervalIntegrable 0 T)
    intro s _
    exact drift_lip D _ _ _ (π.u_mem _ ω)
  -- Gronwall
  have hG := norm_le_gronwallBound_of_norm_deriv_right_le (f := ψ) (f' := fun s => c * φ s)
    (δ := δ) (K := c) (ε := 0) (a := 0) (b := (t : ℝ)) hψc.continuousOn
    (fun s _ => (hψd s).hasDerivWithinAt)
    (by simp [hψ, Real.norm_eq_abs, abs_of_nonneg hδ])
    (by
      intro s hs
      have h0 : 0 ≤ s := hs.1
      have hψs : 0 ≤ ψ s := (hφ0 s).trans (hle s h0)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0 (hφ0 s)),
        abs_of_nonneg hψs, add_zero]
      exact mul_le_mul_of_nonneg_left (hle s h0) hc0) (t : ℝ) ⟨t.2, le_refl _⟩
  rw [gronwallBound_ε0, sub_zero] at hG
  have hφt : φ t = l1norm (X t ω - Xbar t ω) := by simp [hφ]
  rw [← hφt]
  calc φ t ≤ ψ t := hle t t.2
    _ ≤ ‖ψ t‖ := Real.le_norm_self _
    _ ≤ δ * Real.exp (c * t) := hG
    _ ≤ δ * (1 + Real.exp (c * t)) := by
        apply mul_le_mul_of_nonneg_left _ hδ; linarith
