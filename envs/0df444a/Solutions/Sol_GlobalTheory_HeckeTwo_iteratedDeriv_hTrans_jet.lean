-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.iteratedDeriv_hTrans_jet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:58:36.48095+00:00
-- url     : https://prove2.me/submissions/7b7924fb-628b-46a6-b5bd-c950f89ea12d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiTransformHasDerivAtHolo
import Theorems.Thm_GlobalTheory_HeckeTwo_iteratedDeriv_hTrans_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open GlobalTheory GlobalTheory.HeckeTwo
namespace GlobalTheory.HeckeTwo
theorem _root_.solution :
    (∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y) → (∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane) →
  (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) := by
  intro h1 h2 n k y hy
  obtain ⟨ι, _, c, ab, hc, hab, h⟩ := iteratedDeriv_hTrans_eq_sum h1 n k
  refine ⟨fun σ hσ => ?_, ?_⟩
  · have hev : iteratedDeriv k (hTrans σ n) =ᶠ[nhds y]
        fun y' => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y' := by
      filter_upwards [isOpen_ne.mem_nhds hy] with y' hy' using h σ hσ y' hy'
    have hd := (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (h1 (ab i).1 (ab i).2 σ n y (hab i) hσ hy).const_mul (c i σ))).congr_of_eventuallyEq hev
    rw [iteratedDeriv_succ]
    exact hd.differentiableAt.hasDerivAt
  · refine DifferentiableOn.congr
      (f := fun σ => ∑ i, c i σ * hTransAB (ab i).1 (ab i).2 σ n y) ?_ (fun σ hσ => h σ hσ y hy)
    exact DifferentiableOn.fun_sum fun i _ =>
      (hc i).differentiableOn.mul (h2 _ _ n y (hab i) hy)
end GlobalTheory.HeckeTwo
