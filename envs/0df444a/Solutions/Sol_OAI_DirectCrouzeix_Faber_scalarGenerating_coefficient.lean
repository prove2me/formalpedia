-- Prove2me | solution 1 for OAI.DirectCrouzeix.Faber.scalarGenerating_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:16:39.814155+00:00
-- url     : https://prove2.me/submissions/96a50671-c834-4632-bb27-09368759016d

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/FaberPolynomials.lean:L99-L143
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.Faber.scalarGenerating_coefficient. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Theorems.Thm_OAI_DirectCrouzeix_Faber_taylorCoeff_pow_mul

-- ---- from OAI.Analysis.DirectCrouzeix.TaylorFourier ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u_94 u_95 u_96 u_97 u_98 u_99 u_100 u_101 u_102 u_103 u_104 u_105

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem taylorCoeff_congr {E : Type u_96} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : ℂ → E} (h : f =ᶠ[𝓝 0] g) (k : ℕ) : taylorCoeff f k = taylorCoeff g k := by
  rw [taylorCoeff,taylorCoeff,h.iteratedDeriv_eq k]

theorem taylorCoeff_add {E : Type u_97} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f g : ℂ → E} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (k : ℕ) :
    taylorCoeff (fun z => f z+g z) k = taylorCoeff f k+taylorCoeff g k := by
  simp only [taylorCoeff,iteratedDeriv_fun_add (n := k) hf.contDiffAt hg.contDiffAt,smul_add]

theorem taylorCoeff_sum {E : Type u_98} {ι : Type u_99} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (I : Finset ι) {f : ι → ℂ → E} (hf : ∀ i ∈ I, AnalyticAt ℂ (f i) 0) (k : ℕ) :
    taylorCoeff (fun z => ∑ i ∈ I, f i z) k = ∑ i ∈ I, taylorCoeff (f i) k := by
  simp only [taylorCoeff, iteratedDeriv_fun_sum (fun i hi => (hf i hi).contDiffAt),Finset.smul_sum]

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- from OAI.Analysis.DirectCrouzeix.FaberPolynomials ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe u_106 u_107

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

noncomputable section

open MeasureTheory Set Filter Metric

open scoped Topology Interval ENNReal NNReal ComplexConjugate

namespace DirectCrouzeix.Faber

theorem analyticAt_localL {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localL c g) 0 := by
  apply (analyticAt_const.add (analyticAt_id.mul hg)).inv
  simpa using hc

theorem analyticAt_localW {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localW c g) 0 := analyticAt_id.mul (analyticAt_localL hc hg)

theorem analyticAt_localN {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    AnalyticAt ℂ (localN c g) 0 :=
  (analyticAt_const.sub ((analyticAt_id.pow 2).mul hg.deriv)).mul (analyticAt_localL hc hg)

theorem faberBasis_eval (c : ℂ) (g : ℂ → ℂ) (k : ℕ) (z : ℂ) :
    (faberBasis c g k).eval z = ∑ j ∈ Finset.range (k+1),
      taylorCoeff (fun u => localN c g u * localW c g u^j) k * z^j := by
  simp [faberBasis,Polynomial.eval_finsetSum,Polynomial.eval_monomial]

theorem scalarGenerating_eq_local {c : ℂ} {g : ℂ → ℂ} {z u : ℂ}
    (hu : c+u*g u ≠ 0) : scalarGenerating c g z u = localN c g u/(1-z*localW c g u) := by
  simp only [scalarGenerating,localN,localW,localL]
  field_simp
  congr 1 ; ring

theorem scalarGenerating_coefficient {c : ℂ} (hc : c ≠ 0) {g : ℂ → ℂ}
    (hg : AnalyticAt ℂ g 0) (z : ℂ) (k : ℕ) :
    taylorCoeff (scalarGenerating c g z) k = (faberBasis c g k).eval z := by
  let N := localN c g
  let L := localL c g
  let W := localW c g
  have hN : AnalyticAt ℂ N 0 := analyticAt_localN hc hg
  have hL : AnalyticAt ℂ L 0 := analyticAt_localL hc hg
  have hW : AnalyticAt ℂ W 0 := analyticAt_localW hc hg
  let tail := fun u => N u*z^(k+1)*L u^(k+1)/(1-z*W u)
  have ht : AnalyticAt ℂ tail 0 := by
    apply ((hN.mul analyticAt_const).mul (hL.pow (k+1))).div
      (analyticAt_const.sub (analyticAt_const.mul hW))
    simp [W]
  have hsmall : ∀ᶠ u in 𝓝 (0:ℂ), c+u*g u ≠ 0 ∧ 1-z*W u ≠ 0 := by
    apply Filter.Eventually.and
    · exact (analyticAt_const.add (analyticAt_id.mul hg)).continuousAt.eventually_ne (by simpa using hc)
    · exact (analyticAt_const.sub (analyticAt_const.mul hW)).continuousAt.eventually_ne (by simp [W])
  have he : scalarGenerating c g z =ᶠ[𝓝 0]
      (fun u => (∑ j ∈ Finset.range (k+1), (N u*W u^j)*z^j) + u^(k+1)*tail u) := by
    filter_upwards [hsmall] with u hu
    rw [scalarGenerating_eq_local hu.1]
    have hsum := geom_sum_mul_neg (z*W u) (k+1)
    have hre : ∑ j ∈ Finset.range (k+1), N u * W u^j*z^j =
        N u * ∑ j ∈ Finset.range (k+1), (z*W u)^j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j hj; rw [mul_pow]; ring
    rw [hre]
    change N u / (1-z*W u) = _
    simp only [tail]
    field_simp [hu.2]
    have hw : W u = u*L u := rfl
    rw [hw] at hsum ⊢
    linear_combination -N u*hsum
  have hs : AnalyticAt ℂ (fun u => ∑ j ∈ Finset.range (k+1), N u*W u^j*z^j) 0 :=
    Finset.analyticAt_fun_sum _ (fun j hj => (hN.mul (hW.pow j)).mul analyticAt_const)
  have htail : AnalyticAt ℂ (fun u => u^(k+1)*tail u) 0 := (analyticAt_id.pow (k+1)).mul ht
  rw [taylorCoeff_congr he k,taylorCoeff_add hs htail,taylorCoeff_pow_mul ht,
    ite_eq_right (by omega : ¬k+1 ≤ k),add_zero,taylorCoeff_sum]
  · rw [faberBasis_eval]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [taylorCoeff,iteratedDeriv_mul_const_field,smul_eq_mul]
    ring
  · intro j hj
    exact (hN.mul (hW.pow j)).mul analyticAt_const

end DirectCrouzeix.Faber

end

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.Faber.scalarGenerating_coefficient := @_root_.OAI.DirectCrouzeix.Faber.scalarGenerating_coefficient
