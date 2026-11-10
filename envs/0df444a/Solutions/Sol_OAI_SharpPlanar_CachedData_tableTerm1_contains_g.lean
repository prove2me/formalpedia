-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.tableTerm1_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T19:01:10.889381+00:00
-- url     : https://prove2.me/submissions/87f2967a-c2de-40af-925b-ff210b3257c7

import Mathlib
import Definitions.Def_OAIQ098G055
import Definitions.Def_OAIQ098G397
import Theorems.Thm_OAI_SharpPlanar_CachedData_amp1_1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column1_0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_column1_1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_power1_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisAlpha_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisBeta_mod_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_basisFunction_wave_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_scaled_table_basis_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma waveAmplitude_mod (d : Bool) (n j : ℕ) (t : ℝ) :
    waveAmplitude d (n%12) j t = waveAmplitude d n j t := by
  simp only [waveAmplitude,basisAlpha_mod_g,basisBeta_mod_g]

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_Columns10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid IntegerAlpha IntegerCompact
lemma column1_1_contains (j : Fin 6) (i k : Fin 16) :
    (column1_1 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*basisFunction true 1 j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← column1_1_eq_g,basisFunction_wave_g,← mul_assoc]
  unfold column1_1Expr
  apply CBox.contains_mul_g
  · rw [← waveAmplitude_mod true 1 j.val (quadraturePoint j.val (16*i.val+k.val))]
    exact amp1_1_contains_g j i k
  · exact power1_contains_g j i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensityExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite interval certificates for the planar Fourier construction

These rational enclosures certify the numerical bounds in the sharp planar
Fourier construction of OpenAI. All interval endpoints are exact integers.
-/

namespace SharpPlanar.CachedData
open IntegerIntervals IntegerBasis IntegerGrid
lemma tableTerm1_contains_g_oai (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 1 j i k).Contains (((if d then (tableD a 1:ℝ) else (tableC a 1:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 1 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases d
  · exact scaled_table_basis_g (column1_0_contains_g j i k) a
  · exact scaled_table_basis_g (column1_1_contains j i k) a
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.tableTerm1_contains_g_oai := @OAI.SharpPlanar.CachedData.tableTerm1_contains_g_oai
