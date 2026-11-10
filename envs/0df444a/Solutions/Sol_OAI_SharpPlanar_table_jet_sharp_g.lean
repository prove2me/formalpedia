-- Prove2me | solution 1 for OAI.SharpPlanar.table_jet_sharp_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T22:35:19.671974+00:00
-- url     : https://prove2.me/submissions/e1281c31-f114-4e1e-8976-e07abb035664

import Mathlib
import Definitions.Def_OAIQ098G1675
import Definitions.Def_OAIQ098G1690
import Definitions.Def_OAIQ098G1695
import Definitions.Def_OAIQ098G1698
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_atomicEnvelope_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_densityCap_nonneg_g
import Theorems.Thm_OAI_SharpPlanar_directEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_direct_spectral_bound_g
import Theorems.Thm_OAI_SharpPlanar_pi_fine_g
import Theorems.Thm_OAI_SharpPlanar_sharp_moment_bound_g
import Theorems.Thm_OAI_SharpPlanar_table_coeff_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_le_rat_g
import Theorems.Thm_OAI_SharpPlanar_transformEnvelope_nonneg_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Envelopes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Spectral derivative bounds

Monotone spectral envelopes bound the cardinal functions and their Fourier kernels.
The estimates follow *A sharp Fourier certificate for planar circle packing*
(OpenAI, 2026).
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma directEnvelope_nonneg (ell : ℕ) : 0 ≤ directEnvelope ell := by
  apply Finset.sum_nonneg; intro j _
  exact mul_nonneg (div_nonneg (densityCap_nonneg_g j) (by norm_num)) (by positivity)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_RationalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Rational Fourier envelopes

Explicit rational majorants control the direct and transformed spectral envelopes
at integral and half-integral radii.
-/

namespace SharpPlanar
open IntegerBasis
open scoped BigOperators
lemma pi_le_upper : Real.pi ≤ piUpper := pi_fine_g.2.le
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableNorms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Norm bounds for the rational coefficient family

Finite rational sums give bounds for the mass of the cardinal coefficients.
-/

namespace SharpPlanar
open Numerical
open scoped BigOperators
lemma table_constant_bound (a : Bool) : |(tableData a).C| ≤ (17:ℝ)/1000 := by
  cases a <;> norm_num [tableData,tableConstant]
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_CoarseTaylor
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open IntegerIntervals IntegerBasis
lemma table_jet_sharp_g_oai (a : Bool) (ell n : ℕ) : |tableHJet a ell n| ≤ sharpTaylor ell n := by
  have hd:=direct_spectral_bound_g (tableData a) ell (n:ℝ)
  have hk:=sharp_moment_bound_g (tableData (!a)) ell (Nat.cast_nonneg n)
  have hc:=table_constant_bound a
  have hm:=table_coeff_mass_g a
  have hcm:=table_constant_bound (!a)
  have hmm:=table_coeff_mass_g (!a)
  have hp:=pow_le_pow_left₀ Real.pi_pos.le pi_le_upper ell
  have hdn:=directEnvelope_nonneg ell
  have htn:=transformEnvelope_nonneg_g ell (Nat.cast_nonneg n)
  have han:=atomicEnvelope_nonneg_g ell (n:ℝ)
  have hd1:=mul_le_mul hc (show 25*Real.pi^ell ≤ 25*piUpper^ell by nlinarith) (by positivity : 0≤25*Real.pi^ell) (by norm_num : (0:ℝ)≤17/1000)
  have hd2:=mul_le_mul (show |(tableData a).c₀|+|(tableData a).d₀|+‖(tableData a).x‖ ≤ (23:ℝ)/10 by linarith)
    (directEnvelope_le_rat_g ell) hdn (by norm_num : (0:ℝ)≤23/10)
  have hk1:=mul_le_mul (show |(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖ ≤ (23:ℝ)/10 by linarith)
    (transformEnvelope_le_rat_g ell n) htn (by norm_num : (0:ℝ)≤23/10)
  have hk2:=mul_le_mul hcm (atomicEnvelope_le_rat_g ell n) han (by norm_num : (0:ℝ)≤17/1000)
  have ha:=abs_add_le (cardinalSeries (tableData a) ell n) (K (tableData (!a)) ell n)
  change |K (tableData (!a)) ell n| ≤ (|(tableData (!a)).c₀|+|(tableData (!a)).d₀|+‖(tableData (!a)).x‖)*transformEnvelope ell n+|(tableData (!a)).C| * atomicEnvelope ell n at hk
  change |cardinalSeries (tableData a) ell n+K (tableData (!a)) ell n| ≤ _
  unfold sharpTaylor
  nlinarith
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.table_jet_sharp_g_oai := @OAI.SharpPlanar.table_jet_sharp_g_oai
