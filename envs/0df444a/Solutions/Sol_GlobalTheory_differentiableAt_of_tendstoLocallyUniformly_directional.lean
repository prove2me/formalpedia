-- Prove2me | solution 1 for GlobalTheory.differentiableAt_of_tendstoLocallyUniformly_directional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:43:18.027367+00:00
-- url     : https://prove2.me/submissions/a266ac1f-18cb-4153-893c-3387807c800b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_DifferentiableAtLimitOfDirectionalDerivsConverge
import Theorems.Thm_GlobalTheory_tendstoLocallyUniformly_sum_smul_const

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff Topology
open GlobalTheory
open Filter
namespace GlobalTheory
theorem _root_.solution :
    ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {A : Type} [Fintype A] (v : A → E) (c : A → E →L[ℝ] ℝ), (∀ x, ∑ a, c a x • v a = x) → ∀ (φ : E → ℂ) (g : ℕ → E → ℂ) (ψ : A → E → ℂ), (∀ j, Differentiable ℝ (g j)) → TendstoLocallyUniformly g φ Filter.atTop → (∀ a, TendstoLocallyUniformly (fun j y => fderiv ℝ (g j) y (v a)) (ψ a) Filter.atTop) → ∀ y, DifferentiableAt ℝ φ y ∧ ∀ a, fderiv ℝ φ y (v a) = ψ a y := by
  intro E _ _ A _ v c hvc φ g ψ hg hφ hψ y
  classical
  have hdecomp : (fun j z => fderiv ℝ (g j) z) =
      fun j z => ∑ a, fderiv ℝ (g j) z (v a) • (c a).smulRight (1 : ℂ) := by
    funext j z
    refine ContinuousLinearMap.ext fun x => ?_
    conv_lhs => rw [← hvc x]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Complex.real_smul, mul_comm]
  have hconv : TendstoLocallyUniformly (fun j z => fderiv ℝ (g j) z)
      (fun z => ∑ a, ψ a z • (c a).smulRight (1 : ℂ)) Filter.atTop := by
    rw [hdecomp]
    exact tendstoLocallyUniformly_sum_smul_const Finset.univ (fun a => (c a).smulRight (1 : ℂ))
      (fun a j z => fderiv ℝ (g j) z (v a)) ψ hψ
  have hfd : HasFDerivAt φ (∑ a, ψ a y • (c a).smulRight (1 : ℂ)) y :=
    hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ
      (hconv.tendstoLocallyUniformlyOn (s := Set.univ))
      (fun n z _ => (hg n z).hasFDerivAt)
      (fun z _ => (hφ.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ z))
      (Set.mem_univ y)
  refine ⟨hfd.differentiableAt, fun a => ?_⟩
  rw [hfd.fderiv]
  have h1 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop
      (𝓝 ((∑ b, ψ b y • (c b).smulRight (1 : ℂ)) (v a))) :=
    ((ContinuousLinearMap.apply ℝ ℂ (v a)).continuous.tendsto _).comp
      ((hconv.tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y))
  have h2 : Filter.Tendsto (fun j => fderiv ℝ (g j) y (v a)) Filter.atTop (𝓝 (ψ a y)) :=
    ((hψ a).tendstoLocallyUniformlyOn (s := Set.univ)).tendsto_at (Set.mem_univ y)
  exact tendsto_nhds_unique h1 h2
end GlobalTheory
