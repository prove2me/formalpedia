-- Prove2me | solution 1 for OAI.SharpPlanar.tableMomentK_eq_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T08:48:48.144745+00:00
-- url     : https://prove2.me/submissions/04cf94ef-e893-4378-9641-837d199b5082

import Mathlib
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1691
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_tableData_density_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableKBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Quadrature bounds for finite cardinal kernels

Certified quadrature and the finite coefficient densities control the cardinal kernel integrals.
-/

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma normalized_kernel (m t : ℝ) (ell : ℕ) :
    complexTransformedFactor m 1 ell t = kernelMoment ell m t / (ell.factorial:ℂ) := by
  simp only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,
    Complex.ofReal_one,mul_one,kernelMoment]
  ring
lemma tableMomentK_eq_g_oai (a : Bool) (m : ℝ) (ell : ℕ) :
    tableMomentK a m ell=K (tableData a) ell m/(ell.factorial:ℝ) := by
  have hi : tableMomentIntegral a m ell =
      (∑ j ∈ Finset.range 6,∫ t in (j:ℝ)/6..((j:ℝ)+1)/6,
        density (tableData a) j t*kernelMoment ell m t)/(ell.factorial:ℂ) := by
    unfold tableMomentIntegral
    rw [← Finset.sum_range (fun j => pieceIntegral (fun t => tableDensity a j t*complexTransformedFactor m 1 ell t) j),Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [pieceIntegral,normalized_kernel,← tableData_density_g,← mul_div_assoc]
    rw [intervalIntegral.integral_div]
  have ha : tableMomentAtom a m ell =
      ((tableConstant a:ℝ):ℂ)*(Pcoeff 0*kernelMoment ell m 0+
        ∑ j ∈ Finset.Icc 1 6,2*Pcoeff j*kernelMoment ell m ((j:ℝ)/6))/(ell.factorial:ℂ) := by
    unfold tableMomentAtom
    simp only [← Complex.ofReal_ofNat 6,← Complex.ofReal_div,normalized_kernel,← mul_div_assoc]
    rw [← Finset.sum_div,← mul_div_assoc]
    congr 2
    norm_num [Fin.sum_univ_succ,Finset.sum_Icc_succ_top]
    ring
  unfold tableMomentK K
  rw [hi,ha,← add_div]
  change (_/(ell.factorial:ℂ)).re=_
  change (_/((ell.factorial:ℝ):ℂ)).re=_
  rw [Complex.div_ofReal_re]
  rfl
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableMomentK_eq_g_oai := @OAI.SharpPlanar.tableMomentK_eq_g_oai
