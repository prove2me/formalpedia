-- Prove2me | solution 1 for NicaiseDelayWave.BoundaryInstab.case_b_minimizer_solves_5_7
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:31:19.546087+00:00
-- url     : https://prove2.me/submissions/faecd5c8-4d35-4aa6-a318-031d84c8e6db

import Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow

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
open NicaiseDelayWave.BoundaryInstab

namespace CBoundary

lemma scalar_root_ineq (s q r b : ℝ) (hs : 0 ≤ s) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hb : 0 ≤ b) (h : 2*b ≤ s*q+Real.sqrt (s^2*q^2+4*r)) :
    b^2 ≤ b*s*q+r := by
  have hr0 : 0 ≤ s^2*q^2+4*r := by positivity
  have hsq := Real.sq_sqrt hr0
  have hroot := Real.sqrt_nonneg (s^2*q^2+4*r)
  by_cases hsmall : b ≤ s*q
  · nlinarith [mul_nonneg hb (sub_nonneg.mpr hsmall)]
  · have htwo : 0 ≤ 2*b-s*q := by nlinarith
    have hh : (2*b-s*q)^2 ≤ (Real.sqrt (s^2*q^2+4*r))^2 := by gcongr; linarith
    nlinarith

lemma admissible_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (c : ℝ) :
    (fun x => c*u x) ∈ admissible D := by
  refine ⟨contDiffOn_const.mul hu.1,contDiffOn_const.mul hu.2.1,?_⟩
  intro x hx
  simp [hu.2.2 x hx]

lemma admissible_add_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D) (t : ℝ) :
    (fun x => u x+t*v x) ∈ admissible D := by
  have ht := admissible_smul D v hv t
  refine ⟨hu.1.add ht.1,hu.2.1.add ht.2.1,?_⟩
  intro x hx
  simp [hu.2.2 x hx,hv.2.2 x hx]

lemma gradient_smul {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gradient (fun y => c*u y) x = c • gradient u x := by
  unfold gradient
  have he := congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := u) c) x
  change fderiv ℝ (fun y => c*u y) x = c • fderiv ℝ u x at he
  rw [he]
  simp

lemma gradient_add_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D)
    (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D.Ω) :
    gradient (fun y => u y+t*v y) x = gradient u x+t • gradient v x := by
  have hud := (hu.1.contDiffAt (D.isOpen_Ω.mem_nhds hx)).differentiableAt (by norm_num)
  have hvd := (hv.1.contDiffAt (D.isOpen_Ω.mem_nhds hx)).differentiableAt (by norm_num)
  unfold gradient
  rw [fderiv_fun_add hud (hvd.const_mul t),fderiv_const_mul hvd t]
  simp

lemma q0_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ) :
    q0 D (fun x => c*u x) = c^2*q0 D u := by
  unfold q0
  simp_rw [mul_pow]
  rw [integral_const_mul]

lemma q1_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (c : ℝ) :
    q1 D (fun x => c*u x) = c^2*q1 D u := by
  unfold q1
  simp_rw [gradient_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [integral_const_mul]

lemma val_product_integrable {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ closure D.Ω) :
    IntegrableOn (fun x => u x*v x) S μ :=
  ((hu.2.1.continuousOn.mul hv.2.1.continuousOn).integrableOn_compact
    D.isBounded_Ω.isCompact_closure).mono_set hS

noncomputable def closedGradient {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderivWithin ℝ u (closure D.Ω) x)

lemma closedGradient_continuous {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) :
    ContinuousOn (closedGradient D u) (closure D.Ω) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp_continuousOn
    (hu.2.1.continuousOn_fderivWithin (CNicaise.closure_uniqueDiff D) (by norm_num))

lemma closedGradient_eq {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ D.Ω) :
    closedGradient D u x = gradient u x := by
  unfold closedGradient gradient
  rw [fderivWithin_eq_fderiv (CNicaise.closure_uniqueDiff D x (subset_closure hx))
    ((hu.1.contDiffAt (D.isOpen_Ω.mem_nhds hx)).differentiableAt (by norm_num))]

lemma grad_product_integrable {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D) :
    IntegrableOn (fun x => ⟪gradient u x,gradient v x⟫) D.Ω := by
  have hc : ContinuousOn (fun x => ⟪closedGradient D u x,closedGradient D v x⟫) (closure D.Ω) :=
    (closedGradient_continuous D u hu).inner (closedGradient_continuous D v hv)
  have hi := (hc.integrableOn_compact (μ := volume) D.isBounded_Ω.isCompact_closure).mono_set subset_closure
  apply hi.congr
  filter_upwards [ae_restrict_mem D.isOpen_Ω.measurableSet] with x hx
  rw [closedGradient_eq D u hu x hx,closedGradient_eq D v hv x hx]


lemma square_integral_add_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasureOnCompacts μ]
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S ⊆ closure D.Ω) (t : ℝ) :
    (∫ x in S, (u x+t*v x)^2 ∂μ) = (∫ x in S, u x^2 ∂μ) +
      2*t*(∫ x in S, u x*v x ∂μ) + t^2*(∫ x in S, v x^2 ∂μ) := by
  have huu : IntegrableOn (fun x => u x^2) S μ := by
    simpa only [pow_two] using val_product_integrable D u u hu hu μ S hS
  have hvv : IntegrableOn (fun x => v x^2) S μ := by
    simpa only [pow_two] using val_product_integrable D v v hv hv μ S hS
  have huv := val_product_integrable D u v hu hv μ S hS
  have he : (fun x => (u x+t*v x)^2) = fun x => u x^2+(2*t)*(u x*v x)+t^2*v x^2 := by
    funext x
    ring
  erw [he,integral_add (huu.add (huv.const_mul (2*t))) (hvv.const_mul (t^2)),
    integral_add huu (huv.const_mul (2*t)),integral_const_mul,integral_const_mul]

lemma q0_add_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D) (t : ℝ) :
    q0 D (fun x => u x+t*v x) = q0 D u+
      2*t*(∫ x in D.ΓN, u x*v x ∂D.σ)+t^2*q0 D v := by
  letI := D.isFiniteMeasure_σ
  exact square_integral_add_smul D u v hu hv D.σ D.ΓN
    (fun x hx => frontier_subset_closure (D.union_eq ▸ Or.inr hx)) t

lemma q1_add_smul {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n)
    (u v : EuclideanSpace ℝ (Fin n) → ℝ) (hu : u ∈ admissible D) (hv : v ∈ admissible D) (t : ℝ) :
    q1 D (fun x => u x+t*v x) = q1 D u+
      2*t*(∫ x in D.Ω, ⟪gradient u x,gradient v x⟫)+t^2*q1 D v := by
  have huu : IntegrableOn (fun x => ‖gradient u x‖^2) D.Ω := by
    simpa only [real_inner_self_eq_norm_sq] using grad_product_integrable D u u hu hu
  have hvv : IntegrableOn (fun x => ‖gradient v x‖^2) D.Ω := by
    simpa only [real_inner_self_eq_norm_sq] using grad_product_integrable D v v hv hv
  have huv := grad_product_integrable D u v hu hv
  unfold q1
  have he : (fun x => ‖gradient (fun y => u y+t*v y) x‖^2) =ᵐ[volume.restrict D.Ω]
      (fun x => ‖gradient u x‖^2+(2*t)*⟪gradient u x,gradient v x⟫+t^2*‖gradient v x‖^2) := by
    filter_upwards [ae_restrict_mem D.isOpen_Ω.measurableSet] with x hx
    rw [gradient_add_smul D u v hu hv t x hx,norm_add_sq_real,real_inner_smul_right,
      norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  erw [integral_congr_ae he,integral_add (huu.add (huv.const_mul (2*t))) (hvv.const_mul (t^2)),
    integral_add huu (huv.const_mul (2*t)),integral_const_mul,integral_const_mul]

end CBoundary



open MeasureTheory Filter Set
open scoped Topology RealInnerProductSpace
open NicaiseDelayWave.BoundaryInstab

namespace CBoundary

lemma minimizer_equation {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (s : ℝ) (hs : 0 ≤ s)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : φ ∈ admissible D)
    (hnorm : ∫ x in D.Ω, φ x^2 = 1)
    (hmin : ∀ w ∈ admissible D, (∫ x in D.Ω, w x^2) = 1 → functionalB D s φ ≤ functionalB D s w)
    (v : EuclideanSpace ℝ (Fin n) → ℝ) (hv : v ∈ admissible D) :
    (∫ x in D.Ω, ⟪gradient φ x,gradient v x⟫) - (functionalB D s φ/2)^2*(∫ x in D.Ω, φ x*v x) +
      (functionalB D s φ/2)*s*(∫ x in D.ΓN, φ x*v x ∂D.σ) = 0 := by
  let b := functionalB D s φ/2
  have hq0 : ∀ w, 0 ≤ q0 D w := fun w => integral_nonneg fun x => sq_nonneg (w x)
  have hq1 : ∀ w, 0 ≤ q1 D w := fun w => integral_nonneg fun x => sq_nonneg ‖gradient w x‖
  have hb : 0 ≤ b := by
    dsimp only [b,functionalB]
    exact div_nonneg (add_nonneg (mul_nonneg hs (hq0 φ)) (Real.sqrt_nonneg _)) (by norm_num)
  have hbrel : b^2 = b*s*q0 D φ+q1 D φ := by
    have hqφ := hq1 φ
    have hsq := Real.sq_sqrt (show 0 ≤ s^2*(q0 D φ)^2+4*q1 D φ by positivity)
    dsimp only [b,functionalB]
    nlinarith
  have hQ : ∀ w ∈ admissible D, 0 < (∫ x in D.Ω, w x^2) →
      b^2*(∫ x in D.Ω, w x^2) ≤ b*s*q0 D w+q1 D w := by
    intro w hw hN
    let c := 1/Real.sqrt (∫ x in D.Ω, w x^2)
    have hc2 : c^2 = 1/(∫ x in D.Ω, w x^2) := by
      dsimp only [c]
      rw [div_pow,one_pow,Real.sq_sqrt hN.le]
    have hnormalized : (∫ x in D.Ω, (c*w x)^2) = 1 := by
      simp_rw [mul_pow]
      rw [integral_const_mul,hc2]
      exact one_div_mul_cancel (ne_of_gt hN)
    have hminimal := hmin (fun x => c*w x) (admissible_smul D w hw c) hnormalized
    have hh := scalar_root_ineq s (q0 D (fun x => c*w x)) (q1 D (fun x => c*w x)) b
      hs (hq0 _) (hq1 _) hb (by
        dsimp only [b,functionalB] at hminimal ⊢
        linarith)
    rw [q0_smul,q1_smul,hc2] at hh
    apply (le_div_iff₀ hN).mp
    convert! hh using 1 <;> ring
  let w : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun t x => φ x+t*v x
  let N : ℝ → ℝ := fun t => ∫ x in D.Ω, (w t x)^2
  let Q : ℝ → ℝ := fun t => q1 D (w t)+b*s*q0 D (w t)-b^2*N t
  have hNpoly : N = fun t => 1+2*t*(∫ x in D.Ω, φ x*v x)+t^2*(∫ x in D.Ω, v x^2) := by
    funext t
    dsimp only [N,w]
    rw [square_integral_add_smul D φ v hφ hv volume D.Ω subset_closure,hnorm]
  have hNcont : Continuous N := by rw [hNpoly]; fun_prop
  have hN0 : N 0 = 1 := by rw [hNpoly]; simp
  have hNpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < N t :=
    hNcont.continuousAt.eventually (isOpen_Ioi.mem_nhds (by rw [hN0]; norm_num))
  have hQpoly : Q = fun t => (q1 D φ+b*s*q0 D φ-b^2) +
      t*(2*(∫ x in D.Ω, ⟪gradient φ x,gradient v x⟫)+2*b*s*(∫ x in D.ΓN, φ x*v x ∂D.σ)-
        2*b^2*(∫ x in D.Ω, φ x*v x)) +
      t^2*(q1 D v+b*s*q0 D v-b^2*(∫ x in D.Ω, v x^2)) := by
    funext t
    dsimp only [Q]
    rw [hNpoly]
    dsimp only [w]
    rw [q1_add_smul D φ v hφ hv,q0_add_smul D φ v hφ hv]
    ring
  have hQ0 : Q 0 = 0 := by rw [hQpoly]; simp; linarith
  have hlocal : IsLocalMin Q 0 := by
    change ∀ᶠ t in 𝓝 (0 : ℝ), Q 0 ≤ Q t
    rw [hQ0]
    filter_upwards [hNpos] with t ht
    have hh := hQ (w t) (admissible_add_smul D φ v hφ hv t) ht
    dsimp only [Q]
    linarith
  have hder : HasDerivAt Q
      (2*(∫ x in D.Ω, ⟪gradient φ x,gradient v x⟫)+2*b*s*(∫ x in D.ΓN, φ x*v x ∂D.σ)-
        2*b^2*(∫ x in D.Ω, φ x*v x)) 0 := by
    rw [hQpoly]
    convert! (((hasDerivAt_const (0 : ℝ) (q1 D φ+b*s*q0 D φ-b^2)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (2*(∫ x in D.Ω, ⟪gradient φ x,gradient v x⟫)+2*b*s*(∫ x in D.ΓN, φ x*v x ∂D.σ)-
          2*b^2*(∫ x in D.Ω, φ x*v x)))).add
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const
        (q1 D v+b*s*q0 D v-b^2*(∫ x in D.Ω, v x^2)))) using 1 <;> norm_num
  have hz := hlocal.hasDerivAt_eq_zero hder
  change (∫ x in D.Ω, ⟪gradient φ x,gradient v x⟫)-b^2*(∫ x in D.Ω, φ x*v x)+
    b*s*(∫ x in D.ΓN, φ x*v x ∂D.σ) = 0
  linarith

end CBoundary

theorem solution {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ1 μ2 : ℝ)
    (hμ1 : 0 < μ1) (hμ12 : μ1 < μ2)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ) (hφ : φ ∈ admissible D)
    (hnorm : ∫ x in D.Ω, φ x^2 = 1)
    (hmin : ∀ w ∈ admissible D, (∫ x in D.Ω, w x^2) = 1 →
      functionalB D (Real.sqrt (μ2^2-μ1^2)) φ ≤ functionalB D (Real.sqrt (μ2^2-μ1^2)) w) :
    ∀ v ∈ admissible D,
      (∫ x in D.Ω, inner ℝ (gradient φ x) (gradient v x)) -
        (functionalB D (Real.sqrt (μ2^2-μ1^2)) φ/2)^2*(∫ x in D.Ω, φ x*v x) +
        (functionalB D (Real.sqrt (μ2^2-μ1^2)) φ/2)*Real.sqrt (μ2^2-μ1^2)*
          (∫ x in D.ΓN, φ x*v x ∂D.σ) = 0 := by
  intro v hv
  exact CBoundary.minimizer_equation D _ (Real.sqrt_nonneg _) φ hφ hnorm hmin v hv
