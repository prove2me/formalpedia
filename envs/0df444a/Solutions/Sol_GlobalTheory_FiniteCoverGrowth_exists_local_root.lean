-- Prove2me | solution 1 for GlobalTheory.FiniteCoverGrowth.exists_local_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:28:21.445677+00:00
-- url     : https://prove2.me/submissions/6fd38a9e-16a4-472c-abef-7aab8eeeb1e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IntegralAndRationalOfPolynomialGrowth
import Theorems.Thm_GlobalTheory_FiniteCoverGrowth_contDiff_eval_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.FiniteCoverGrowth
namespace GlobalTheory.FiniteCoverGrowth
theorem _root_.solution {d : ℕ} (p : Polynomial (MvPolynomial (Fin d) ℂ)) (x₀ : Fin d → ℂ)
    (a : ℂ) (ha : (p.map (MvPolynomial.eval x₀)).eval a = 0)
    (ha' : (p.map (MvPolynomial.eval x₀)).derivative.eval a ≠ 0) :
    ∃ y : (Fin d → ℂ) → ℂ, y x₀ = a ∧ DifferentiableAt ℂ y x₀ ∧
      ∀ᶠ x in 𝓝 x₀, (p.map (MvPolynomial.eval x)).eval (y x) = 0 := by
  have hs := (contDiff_eval_map p).contDiffAt.hasStrictFDerivAt (x := (x₀, a)) one_ne_zero
  set L := fderiv ℂ (fun z : (Fin d → ℂ) × ℂ => (p.map (MvPolynomial.eval z.1)).eval z.2) (x₀, a)
  have h1 : HasFDerivAt (fun y : ℂ => (p.map (MvPolynomial.eval x₀)).eval y)
      (L ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) a :=
    hs.hasFDerivAt.comp a (hasFDerivAt_prodMk_right x₀ a)
  have h2 := ((p.map (MvPolynomial.eval x₀)).hasDerivAt a).hasFDerivAt
  have h3 := h1.unique h2
  have hinv : (L ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [h3]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ ha'), ?_⟩
    ext; simp
  refine ⟨hs.implicitFunctionOfProdDomain hinv, ?_, ?_, ?_⟩
  · exact (hs.eventually_apply_eq_iff_implicitFunctionOfProdDomain hinv).self_of_nhds.mp rfl
  · exact (hs.hasStrictFDerivAt_implicitFunctionOfProdDomain hinv).hasFDerivAt.differentiableAt
  · have := hs.eventually_apply_implicitFunctionOfProdDomain hinv
    simpa [ha] using this
end GlobalTheory.FiniteCoverGrowth
