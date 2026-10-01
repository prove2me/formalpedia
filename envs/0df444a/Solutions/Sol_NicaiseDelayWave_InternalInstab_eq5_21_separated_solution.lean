-- Prove2me | solution 1 for NicaiseDelayWave.InternalInstab.eq5_21_separated_solution
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:16:40.800254+00:00
-- url     : https://prove2.me/submissions/38c140e0-c130-4a1a-9f3f-2b6329e46a29

import Definitions.Def_NicaiseDelayWave_InternalInstab_DelayProblem
import Definitions.Def_NicaiseDelayWave_BoundaryInstab_DelayProblem
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic

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

open NicaiseDelayWave.InternalInstab

theorem solution {n : ℕ} (D : NicaiseDelayWave.Shared.MixedDomain n) (μ₁ μ₂ τ Λ : ℝ)
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ₂ : ContDiffOn ℝ 2 φ D.Ω) (hφ₁ : ContDiffOn ℝ 1 φ (closure D.Ω))
    (hΔ : ∀ x ∈ D.Ω, laplacian φ x = -((Λ : ℂ)^2)*φ x)
    (hD : ∀ x ∈ D.ΓD, φ x = 0)
    (hN : ∀ x ∈ D.ΓN, normalDeriv D φ x = 0)
    (lam : ℂ)
    (hlam : lam^2 + ((μ₁ : ℂ)+(μ₂ : ℂ)*Complex.exp (-lam*τ))*lam = -((Λ : ℂ)^2)) :
    IsClassicalSolution D μ₁ μ₂ τ (fun x t => Complex.exp (lam*t)*φ x) := by
  refine ⟨CNicaise.exp_contDiffOn φ lam D.Ω 2 hφ₂,
    CNicaise.exp_contDiffOn φ lam (closure D.Ω) 1 hφ₁,?_,?_,?_⟩
  · intro x hx t ht
    have he : Complex.exp (lam * ((t-τ : ℝ) : ℂ)) =
        Complex.exp (lam*t)*Complex.exp (-lam*τ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [CNicaise.exp_utt, laplacianX, CNicaise.laplacian_const_mul D φ hφ₂ _ x hx,
      hΔ x hx, CNicaise.exp_ut, CNicaise.exp_ut, he]
    linear_combination Complex.exp (lam*t)*φ x*hlam
  · intro x hx t ht
    simp only [hD x hx,mul_zero]
  · intro x hx t ht
    have hxc : x ∈ closure D.Ω := frontier_subset_closure (D.union_eq ▸ Or.inr hx)
    rw [CNicaise.normal_const_mul D φ hφ₁ _ x hxc,hN x hx,mul_zero]
