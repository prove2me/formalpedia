-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.TermHol.wirtWord_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:26:08.564805+00:00
-- url     : https://prove2.me/submissions/6dbf5f2a-57a6-48c6-9813-76bd1b8feacf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HTransABTwoZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothHolomorphicInSigmaFamilyAdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABHasDerivAtYStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeHankelTransformABDifferentiableOnSigmaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IteratedDerivHeckePhiTransformHasDerivAtHoloStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeFourierTermWirtingerWordDifferentiableOn
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_upperHalf_isOpen
import Theorems.Thm_GlobalTheory_HeckeTwo_GoodAdd_wirt_congr
import Theorems.Thm_GlobalTheory_HeckeTwo_termQ_zero
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_cons
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_OmegaFactorization_wirtWord_nil
import Theorems.Thm_GlobalTheory_T_heckeYDerivativeTerm_hasFDeriv_upperHalfPlane


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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.TermHol
open Classical
namespace GlobalTheory.HeckeTwo.TermHol
theorem _root_.solution (F : Type) [Field F] [NumberField F] (b ν : F) (hb : b ≠ 0) (hJ : (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane))
    (w : List (Emb F × Bool)) :
    ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (qf : ι → Emb F → ℕ), ∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F,
      wirtWord w (fun z : Emb F → ℂ => fTerm σ z b ν) z = ∑ i, c i * termQ σ b ν (qf i) z := by
  have hU := GlobalTheory.HeckeTwo.GoodAdd.upperHalf_isOpen F
  induction w with
  | nil =>
    refine ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun σ _ z _ => ?_⟩
    simp [wirtWord_nil, termQ_zero]
  | cons x ws ih =>
    obtain ⟨ι, _, c, qf, h⟩ := ih
    obtain ⟨τ₀, bar⟩ := x
    refine ⟨ι ⊕ ι, inferInstance,
      Sum.elim (fun i => c i * (2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ)) / 2)
        (fun i => (if bar then I else -I) * c i * ((τ₀ b : ℝ) : ℂ) / 2),
      Sum.elim qf (fun i => qf i + Pi.single τ₀ 1), fun σ hσ z hz => ?_⟩
    rw [wirtWord_cons]
    rw [GlobalTheory.HeckeTwo.GoodAdd.wirt_congr hU (g := fun z => ∑ i, c i * termQ σ b ν (qf i) z)
      (fun z hz => h σ hσ z hz) _ _ hz]
    have hd := fun i => GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane F b ν hb hJ σ hσ (qf i) z hz τ₀
    have hF : HasFDerivAt (fun z => ∑ i, c i * termQ σ b ν (qf i) z)
        (∑ i, c i • fderiv ℝ (termQ σ b ν (qf i)) z) z :=
      HasFDerivAt.fun_sum fun i _ => ((hd i).1.hasFDerivAt.const_mul (c i))
    simp only [wirt, hF.fderiv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, (hd _).2.1, (hd _).2.2, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
end GlobalTheory.HeckeTwo.TermHol
