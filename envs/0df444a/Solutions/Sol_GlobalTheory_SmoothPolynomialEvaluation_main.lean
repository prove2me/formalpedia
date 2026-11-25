-- Prove2me | solution 1 for GlobalTheory.SmoothPolynomialEvaluation.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:19.010442+00:00
-- url     : https://prove2.me/submissions/910a69f5-7df1-48e6-9a65-feae8f0d34e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ContDiffEvalFun
import Theorems.Thm_GlobalTheory_SmoothPolynomialEvaluation_contDiff_evalFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.SmoothPolynomialEvaluation
namespace GlobalTheory.SmoothPolynomialEvaluation
theorem _root_.solution : ∀ {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ) (a : ℂ),
    Polynomial.eval a (Polynomial.map (MvPolynomial.eval x₀) p) = (0 : ℂ) →
    Polynomial.eval a ((Polynomial.derivative : Polynomial ℂ → Polynomial ℂ)
      (Polynomial.map (MvPolynomial.eval x₀) p)) ≠ (0 : ℂ) →
    ∃ (y : (Fin d → ℂ) → ℂ), y x₀ = a ∧ (∃ s ∈ nhds x₀, ContinuousOn y s) ∧
      ∀ᶠ (x : Fin d → ℂ) in nhds x₀,
        Polynomial.eval (y x) (Polynomial.map (MvPolynomial.eval x) p) = (0 : ℂ) := by
  intro d p x₀ a h0 h1
  set q := Polynomial.map (MvPolynomial.eval x₀) p with hq
  have hFs : HasStrictFDerivAt (evalFun p) (fderiv ℂ (evalFun p) (x₀, a)) (x₀, a) :=
    (contDiff_evalFun p).contDiffAt.hasStrictFDerivAt one_ne_zero
  have hder : fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ
      = (1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q)) := by
    have h1' : HasFDerivAt (fun z => evalFun p (x₀, z))
        (fderiv ℂ (evalFun p) (x₀, a) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a :=
      hFs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)
    have h2' : HasFDerivAt (fun z => evalFun p (x₀, z))
        ((1 : ℂ →L[ℂ] ℂ).smulRight (Polynomial.eval a (Polynomial.derivative q))) a :=
      (Polynomial.hasDerivAt q a).hasFDerivAt
    exact h1'.unique h2'
  have hinv : (fderiv ℂ (evalFun p) (x₀, a) ∘L
      ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hder]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ h1), ?_⟩
    ext; simp
  let φ := hFs.implicitFunctionDataOfProdDomain hinv
  refine ⟨fun x => (φ.toOpenPartialHomeomorph.symm (evalFun p (x₀, a), x)).2, ?_, ?_, ?_⟩
  · have := (hFs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds
    exact this.mp rfl
  · refine ⟨{x | (evalFun p (x₀, a), x) ∈ φ.toOpenPartialHomeomorph.target}, ?_, ?_⟩
    · apply IsOpen.mem_nhds
      · exact φ.toOpenPartialHomeomorph.open_target.preimage (by fun_prop)
      · exact φ.map_pt_mem_toOpenPartialHomeomorph_target
    · exact continuous_snd.comp_continuousOn
        (φ.toOpenPartialHomeomorph.continuousOn_symm.comp (by fun_prop) (fun x hx => hx))
  · have := hFs.eventually_apply_implicitFunctionOfProdDomain hinv
    filter_upwards [this] with x hx
    exact hx.trans h0
end GlobalTheory.SmoothPolynomialEvaluation
