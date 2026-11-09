-- Prove2me | solution 1 for OAI.SharpPlanar.fullMoment_direct_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:42:50.8607+00:00
-- url     : https://prove2.me/submissions/cb9a81f7-4aea-4b58-826c-5e4c9a88615d

import Mathlib
import Definitions.Def_OAIQ098G1642
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Theorems.Thm_OAI_SharpPlanar_directDensity_series_g
import Theorems.Thm_OAI_SharpPlanar_tableData_density_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FullMomentBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma normalized_direct (m t : ℝ) (ell : ℕ) :
    complexDirectFactor m 1 ell t = directKernel ell m t / (ell.factorial:ℂ) := by
  simp only [complexDirectFactor,Complex.ofReal_one,mul_one,directKernel]
  ring
lemma fullMoment_direct_g_oai (a : Bool) (m : ℝ) (ell : ℕ) :
    fullMoment a false m ell=cardinalSeries (tableData a) ell m/(ell.factorial:ℝ) := by
  have hi : fullMomentIntegral a false m ell =
      (∑ j ∈ Finset.range 6,∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        density (tableData a) j t*directKernel ell m t)/(ell.factorial:ℂ) := by
    unfold fullMomentIntegral
    rw [← Finset.sum_range (fun j => pieceIntegral (fun t => tableDensity a j t*fullFactor false m ell t) j),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pieceIntegral,fullFactor,Bool.false_eq_true,ite_false, if_false,normalized_direct,← tableData_density_g,← mul_div_assoc]
    rw [intervalIntegral.integral_div]
  have ha : fullMomentAtom a false m ell =
      ((tableConstant a:ℝ):ℂ)*(Pcoeff 0*(0:ℂ)^ell+
        ∑ j ∈ Finset.Icc 1 6,2*Pcoeff j*(Complex.I*Real.pi*((j:ℝ)/6))^ell*
          Complex.exp (Complex.I*Real.pi*((j:ℝ)/6)*m))/(ell.factorial:ℂ) := by
    unfold fullMomentAtom
    simp only [fullFactor,Bool.false_eq_true,ite_false, if_false,← Complex.ofReal_ofNat 6,← Complex.ofReal_div,normalized_direct,← mul_div_assoc]
    rw [← Finset.sum_div,← mul_div_assoc]
    congr 2
    norm_num [Fin.sum_univ_succ,Finset.sum_Icc_succ_top,directKernel]
    ring
  unfold fullMoment
  rw [hi,ha,← add_div]
  change (_/((ell.factorial:ℝ):ℂ)).re=_
  rw [Complex.div_ofReal_re,Complex.add_re,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  rw [directDensity_series_g]
  congr 1
  unfold cardinalSeries Pmoment
  change _ = (tableConstant a:ℝ)*_+_+_+_
  simp only [Complex.ofReal_div,Complex.ofReal_ofNat]
  ring
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.fullMoment_direct_g_oai := @OAI.SharpPlanar.fullMoment_direct_g_oai
