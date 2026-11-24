-- Prove2me | solution 1 for GlobalTheory.MajorantContinuity.maj_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:29:11.184943+00:00
-- url     : https://prove2.me/submissions/0158864e-4f9a-43f9-a855-9dcd32ffde63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_EventuallyComparable
import Theorems.Thm_GlobalTheory_MajorantContinuity_hermC_smul_l
import Theorems.Thm_GlobalTheory_MajorantContinuity_hermC_smul_r
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
namespace GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
private lemma scale_lemma {n : ℕ} (s : ℝ) (A B : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a, ∑ b, (s : ℂ) * A a * M a b * ((s : ℂ) * B b) = ((s ^ 2 : ℝ) : ℂ) * ∑ a, ∑ b, A a * M a b * B b := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring
end GlobalTheory.MajorantContinuity
end

set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix ComplexConjugate ComplexOrder
open GlobalTheory GlobalTheory.MajorantContinuity
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.MajorantContinuity
theorem _root_.solution {r : ℕ} (X : Data E r) (x : Frame X.Ψ r) (τ : X.Ψ) (t : ℝ) (v : Fin r → ℂ) :
    X.maj x τ ((t : ℂ) • v) = t ^ 2 * X.maj x τ v := by
  have hc : conj (t : ℂ) = t := Complex.conj_ofReal t
  have e2 : hermC τ.1 X.Gm ((t : ℂ) • v) ((t : ℂ) • v) = ((t ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hermC_smul_l, hermC_smul_r, hc]; push_cast; ring
  unfold Data.maj Data.posPart
  rw [e2]
  simp_rw [hermC_smul_l (a := (t : ℂ)) (u := v), map_mul, hc]
  rw [scale_lemma, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  ring
end GlobalTheory.MajorantContinuity
