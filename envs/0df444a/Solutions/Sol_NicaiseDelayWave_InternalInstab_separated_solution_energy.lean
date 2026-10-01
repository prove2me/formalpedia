-- Prove2me | solution 1 for NicaiseDelayWave.InternalInstab.separated_solution_energy
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:21:22.43004+00:00
-- url     : https://prove2.me/submissions/75149227-1fef-472b-9902-2cd30c8624bb

import Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Complex.Trigonometric

open Filter Set
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1000000

namespace CNicaise

lemma closure_uniqueDiff {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) :
    UniqueDiffOn ℝ (closure D.Ω) := by
  intro x hx
  by_cases hxin : x ∈ D.Ω
  · exact (D.isOpen_Ω.uniqueDiffWithinAt hxin).mono subset_closure
  have hfront : x ∈ frontier D.Ω := by
    rw [frontier, Set.mem_diff, D.isOpen_Ω.interior_eq]
    exact ⟨hx,hxin⟩
  have hψ : D.ψ x = 0 := by simpa [D.frontier_eq] using hfront
  have hg : gradient D.ψ x ≠ 0 := D.gradient_ne_zero x hfront
  have hd := (D.contDiff_ψ.differentiable (by norm_num) x).hasFDerivAt
  let T := tangentConeAt ℝ (closure D.Ω) x
  let U := {v : EuclideanSpace ℝ (Fin n) | fderiv ℝ D.ψ x v < 0}
  have hU : IsOpen U := isOpen_lt (fderiv ℝ D.ψ x).continuous continuous_const
  have hUn : U.Nonempty := by
    refine ⟨-gradient D.ψ x,?_⟩
    change fderiv ℝ D.ψ x (-gradient D.ψ x) < 0
    rw [← inner_gradient_left]
    simpa [real_inner_self_eq_norm_sq] using neg_neg_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hg))
  have hUT : U ⊆ T := by
    intro v hv
    have hdline : HasDerivAt (fun t : ℝ => D.ψ (x+t • v)) (fderiv ℝ D.ψ x v) 0 := by
      have hline : HasDerivAt (fun t : ℝ => x+t • v) v 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
      have hd0 : HasFDerivAt D.ψ (fderiv ℝ D.ψ x) (x+(0 : ℝ) • v) := by simpa using hd
      exact hd0.comp_hasDerivAt 0 hline
    have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope (fun t : ℝ => D.ψ (x+t • v)) 0 t < 0 :=
      (hdline.tendsto_slope.mono_left (nhdsGT_le_nhdsNE 0)).eventually
        (isOpen_Iio.mem_nhds hv)
    apply mem_tangentConeAt_of_add_smul_mem (tendsto_id'.mpr (nhdsGT_le_nhdsNE 0))
    filter_upwards [hslope, self_mem_nhdsWithin] with t ht htpos
    have ht0 : 0 < t := htpos
    have hh : D.ψ (x+t • v) < 0 := by
      simp only [slope_def_field, zero_smul, add_zero, hψ, sub_zero] at ht
      simpa using (div_lt_iff₀ ht0).mp ht
    apply subset_closure
    rwa [D.Ω_eq]
  have hspan : Submodule.span ℝ T = ⊤ := by
    apply (Submodule.span ℝ T).eq_top_of_nonempty_interior'
    obtain ⟨v,hv⟩ := hUn
    exact ⟨v,interior_mono (hUT.trans Submodule.subset_span) (hU.interior_eq.symm ▸ hv)⟩
  dsimp only [T] at hspan
  rw [uniqueDiffWithinAt_iff, hspan]
  simpa using hx


lemma exp_time_deriv (lam z : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (lam*s)*z)
      (Complex.exp (lam*t)*(lam*z)) t := by
  simpa only [id_eq, mul_one, mul_assoc, mul_left_comm, mul_comm] using
    ((((hasDerivAt_id (t : ℂ)).const_mul lam).cexp).mul_const z).comp_ofReal

lemma exp_ut {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ) (lam : ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    NicaiseDelayWave.InternalInstab.ut (fun x t => Complex.exp (lam*t)*φ x) x t =
      Complex.exp (lam*t)*(lam*φ x) := (exp_time_deriv lam (φ x) t).deriv

lemma exp_utt {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ) (lam : ℂ)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    NicaiseDelayWave.InternalInstab.utt (fun x t => Complex.exp (lam*t)*φ x) x t =
      Complex.exp (lam*t)*(lam^2*φ x) := by
  unfold NicaiseDelayWave.InternalInstab.utt
  simp_rw [exp_ut]
  convert (exp_time_deriv lam (lam*φ x) t).deriv using 1 <;> ring

lemma exp_contDiffOn {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ) (lam : ℂ)
    (S : Set (EuclideanSpace ℝ (Fin n))) (m : WithTop ℕ∞)
    (hφ : ContDiffOn ℝ m φ S) :
    ContDiffOn ℝ m (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Complex.exp (lam*p.2)*φ p.1)
      (S ×ˢ Set.univ) := by
  have ht : ContDiff ℝ m (fun p : EuclideanSpace ℝ (Fin n) × ℝ => (p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact ((contDiff_const.mul ht).cexp.contDiffOn).mul
    (hφ.comp contDiffOn_fst (fun _ h => h.1))

lemma laplacian_const_mul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ : ContDiffOn ℝ 2 φ D.Ω)
    (c : ℂ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D.Ω) :
    NicaiseDelayWave.InternalInstab.laplacian (fun y => c*φ y) x =
      c * NicaiseDelayWave.InternalInstab.laplacian φ x := by
  unfold NicaiseDelayWave.InternalInstab.laplacian
  have hi : iteratedFDeriv ℝ 2 (fun y => c*φ y) x = c • iteratedFDeriv ℝ 2 φ x :=
    iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := c) (f := φ) (i := 2) (hφ.contDiffAt (D.isOpen_Ω.mem_nhds hx))
  rw [hi, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

lemma normal_const_mul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ : ContDiffOn ℝ 1 φ (closure D.Ω))
    (c : ℂ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ closure D.Ω) :
    NicaiseDelayWave.InternalInstab.normalDeriv D (fun y => c*φ y) x =
      c * NicaiseDelayWave.InternalInstab.normalDeriv D φ x := by
  unfold NicaiseDelayWave.InternalInstab.normalDeriv
  rw [fderivWithin_const_mul (closure_uniqueDiff D x hx)
    (hφ.differentiableOn (by norm_num) x hx)]
  rfl

end CNicaise


open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
open NicaiseDelayWave.InternalInstab

namespace CNicaise

noncomputable def baseEnergy {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ) (lam : ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖lam*φ x‖^2 + ∑ i : Fin n, ‖fderiv ℝ φ x (EuclideanSpace.single i 1)‖^2

lemma energy_formula {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (lam : ℂ) (t : ℝ) :
    stdEnergy D (fun x t => Complex.exp (lam*t)*φ x) t =
      (1/2)*Real.exp (2*lam.re*t)*(∫ x in D.Ω, baseEnergy φ lam x) := by
  have hnorm : ‖Complex.exp (lam*t)‖^2 = Real.exp (2*lam.re*t) := by
    rw [Complex.norm_exp,pow_two,← Real.exp_add]
    congr 1
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    ring
  have hder : ∀ x, fderiv ℝ (fun y => Complex.exp (lam*t)*φ y) x =
      Complex.exp (lam*t) • fderiv ℝ φ x := by
    intro x
    exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := φ) (Complex.exp (lam*t))) x
  have he : ∀ x, ‖ut (fun x t => Complex.exp (lam*t)*φ x) x t‖^2 +
      ∑ i : Fin n, ‖fderiv ℝ (fun y => Complex.exp (lam*t)*φ y) x (EuclideanSpace.single i 1)‖^2 =
      Real.exp (2*lam.re*t)*baseEnergy φ lam x := by
    intro x
    rw [exp_ut,hder]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,norm_mul,mul_pow,hnorm]
    rw [← Finset.mul_sum]
    dsimp only [baseEnergy]
    simp only [norm_mul,mul_pow]
    ring
  unfold stdEnergy
  simp_rw [he]
  rw [integral_const_mul]
  ring

lemma baseEnergy_integrable {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ : ContDiffOn ℝ 1 φ (closure D.Ω)) (lam : ℂ) :
    IntegrableOn (baseEnergy φ lam) D.Ω := by
  have hfd := hφ.continuousOn_fderivWithin (closure_uniqueDiff D) (by norm_num)
  have hc : ContinuousOn (fun x => ‖lam*φ x‖^2 +
      ∑ i : Fin n, ‖fderivWithin ℝ φ (closure D.Ω) x (EuclideanSpace.single i 1)‖^2)
      (closure D.Ω) := by
    apply ContinuousOn.add ((continuousOn_const.mul hφ.continuousOn).norm.pow 2)
    apply continuousOn_finset_sum
    intro i _
    exact (hfd.clm_apply continuousOn_const).norm.pow 2
  have hi := (hc.integrableOn_compact (μ := volume) D.isBounded_Ω.isCompact_closure).mono_set subset_closure
  apply hi.congr
  filter_upwards [ae_restrict_mem D.isOpen_Ω.measurableSet] with x hx
  dsimp only [baseEnergy]
  rw [fderivWithin_eq_fderiv (closure_uniqueDiff D x (subset_closure hx))
    ((hφ.contDiffAt (mem_of_superset (D.isOpen_Ω.mem_nhds hx) subset_closure)).differentiableAt
      (by norm_num))]

lemma baseEnergy_integral_pos {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ : ContDiffOn ℝ 1 φ (closure D.Ω))
    (hφne : ∃ x ∈ D.Ω, φ x ≠ 0) (lam : ℂ) (hlam : lam ≠ 0) :
    0 < ∫ x in D.Ω, baseEnergy φ lam x := by
  have hnonneg : ∀ x, 0 ≤ baseEnergy φ lam x := by
    intro x
    exact add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply (setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hnonneg)
    (baseEnergy_integrable D φ hφ lam)).mpr
  obtain ⟨x,hx,hφx⟩ := hφne
  have hc : ContinuousAt φ x := hφ.continuousOn.continuousAt
    (mem_of_superset (D.isOpen_Ω.mem_nhds hx) subset_closure)
  have hne : ∀ᶠ y in 𝓝 x, φ y ≠ 0 := hc.eventually (isOpen_compl_singleton.mem_nhds hφx)
  apply Measure.measure_pos_of_mem_nhds
  filter_upwards [D.isOpen_Ω.mem_nhds hx,hne] with y hy hφy
  refine ⟨?_,hy⟩
  change baseEnergy φ lam y ≠ 0
  have hp : 0 < ‖lam*φ y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hlam hφy))
  have hs : 0 ≤ ∑ i : Fin n, ‖fderiv ℝ φ y (EuclideanSpace.single i 1)‖^2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  unfold baseEnergy
  linarith

end CNicaise

theorem solution {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ) (hφ₁ : ContDiffOn ℝ 1 φ (closure D.Ω))
    (hφ_ne : ∃ x ∈ D.Ω, φ x ≠ 0) (lam : ℂ) (hlam : lam ≠ 0) :
    0 < stdEnergy D (fun x t => Complex.exp (lam*t)*φ x) 0 ∧
      ∀ t : ℝ, stdEnergy D (fun x t => Complex.exp (lam*t)*φ x) t =
        Real.exp (2*lam.re*t)*stdEnergy D (fun x t => Complex.exp (lam*t)*φ x) 0 := by
  have hpos := CNicaise.baseEnergy_integral_pos D φ hφ₁ hφ_ne lam hlam
  constructor
  · rw [CNicaise.energy_formula]
    simp only [mul_zero,Real.exp_zero,mul_one]
    positivity
  · intro t
    rw [CNicaise.energy_formula,CNicaise.energy_formula]
    simp only [mul_zero,Real.exp_zero,mul_one]
    ring
