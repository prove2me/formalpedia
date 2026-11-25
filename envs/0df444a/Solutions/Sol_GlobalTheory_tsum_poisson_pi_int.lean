-- Prove2me | solution 1 for GlobalTheory.tsum_poisson_pi_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:55:09.519814+00:00
-- url     : https://prove2.me/submissions/c8559f8e-698b-4227-96f5-4b98f8abdd5b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Theorems.Thm_GlobalTheory_tsum_poisson_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix MeasureTheory
open scoped Real
noncomputable section
open GlobalTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution {f F : (ι → ℝ) → ℂ} (hc : Continuous f)
    (hdom : ∀ R : ℝ, ∃ g : (ι → ℤ) → ℝ, Summable g ∧ ∀ (n : ι → ℤ) (u : ι → ℝ), ‖u‖ ≤ R →
      ‖f ((fun i => (n i : ℝ)) + u)‖ ≤ g n)
    (hF : ∀ y : ι → ℝ, ∫ x : ι → ℝ,
      cexp (-(2 * π * I) * ((fun i => (x i : ℂ)) ⬝ᵥ fun i => (y i : ℂ))) * f x = F y)
    (hs : Summable fun n : ι → ℤ => ‖F fun i => (n i : ℝ)‖) (u : ι → ℝ) :
    ∑' n : ι → ℤ, f ((fun i => (n i : ℝ)) + u) =
      ∑' n : ι → ℤ, cexp (2 * π * I * ((fun i => (n i : ℂ)) ⬝ᵥ fun i => (u i : ℂ))) *
        F fun i => (n i : ℝ) := by
  set L : Submodule ℤ (EuclideanSpace ℝ ι) :=
    Submodule.span ℤ (Set.range (EuclideanSpace.basisFun ι ℝ).toBasis) with hL
  have hmem (x : EuclideanSpace ℝ ι) : x ∈ L ↔ ∀ k, ∃ m : ℤ, (m : ℝ) = x k := by
    rw [hL, Module.Basis.mem_span_iff_repr_mem]
    simp
  have hmem' (y : EuclideanSpace ℝ ι) : y ∈ dualLattice L ↔ ∀ k, ∃ m : ℤ, (m : ℝ) = y k := by
    rw [mem_dualLattice]
    refine ⟨fun h k => ?_, fun h x hx => ?_⟩
    · simpa [EuclideanSpace.inner_single_left] using h _ (Submodule.subset_span ⟨k, rfl⟩)
    · choose a ha using (hmem x).1 hx
      choose b hb using h
      exact ⟨∑ k, b k * a k, by simp [PiLp.inner_apply, ha, hb]⟩
  have hequiv (M : Submodule ℤ (EuclideanSpace ℝ ι))
      (hM : ∀ x, x ∈ M ↔ ∀ k, ∃ m : ℤ, (m : ℝ) = x k) :
      ∃ e : (ι → ℤ) ≃ M, ∀ n, (e n : EuclideanSpace ℝ ι) = WithLp.toLp 2 fun i => (n i : ℝ) := by
    refine ⟨Equiv.ofBijective (fun n => ⟨WithLp.toLp 2 fun i => (n i : ℝ),
      (hM _).2 fun k => ⟨n k, rfl⟩⟩) ⟨fun n m h => funext fun i => ?_, fun x => ?_⟩, fun _ => rfl⟩
    · simpa using congrArg (fun x : M => (x : EuclideanSpace ℝ ι) i) h
    · choose a ha using (hM x).1 x.2
      exact ⟨a, Subtype.ext (by ext i; exact ha i)⟩
  obtain ⟨e, he⟩ := hequiv L hmem
  obtain ⟨e', he'⟩ := hequiv _ hmem'
  have hF' (y : ι → ℝ) : FourierTransform.fourier (fun x : EuclideanSpace ℝ ι => f x.ofLp)
      (WithLp.toLp 2 y) = F y := by
    rw [Real.fourier_eq', ← hF, ← (PiLp.volume_preserving_toLp ι).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
    congr 1 with x
    rw [smul_eq_mul]
    congr 2
    simp only [PiLp.inner_apply, dotProduct, RCLike.inner_apply, conj_trivial, mul_comm (y _)]
    push_cast
    ring
  have key := tsum_poisson_lattice L (f := fun x : EuclideanSpace ℝ ι => f x.ofLp) (by fun_prop)
    (fun R => by
      obtain ⟨g, hg, h⟩ := hdom R
      refine ⟨g ∘ e.symm, e.symm.summable_iff.2 hg, fun x v hv => ?_⟩
      obtain ⟨n, rfl⟩ := e.surjective x
      rw [he, Function.comp_apply, e.symm_apply_apply]
      refine h n v.ofLp ((pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans hv)).2 fun i => ?_)
      exact (PiLp.norm_apply_le v i).trans hv)
    (by
      rw [← e'.summable_iff]
      simpa only [Function.comp_def, he', hF'] using hs) (WithLp.toLp 2 u)
  rw [← e.tsum_eq, ← e'.tsum_eq, covolume_span_basis (EuclideanSpace.basisFun ι ℝ),
    Module.Basis.det_self] at key
  simp only [he, he', hF', abs_one, inv_one, one_smul, smul_eq_mul] at key
  refine key.trans (tsum_congr fun n => ?_)
  congr 3
  simp [PiLp.inner_apply, dotProduct, mul_comm]
end GlobalTheory
