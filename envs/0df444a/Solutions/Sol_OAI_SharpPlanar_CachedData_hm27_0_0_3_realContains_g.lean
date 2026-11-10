-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.hm27_0_0_3.realContains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T01:13:54.730675+00:00
-- url     : https://prove2.me/submissions/ac7de7e4-ca07-4e1a-8a8b-1c76c9221855

import Mathlib
import Definitions.Def_OAIQ098G079
import Definitions.Def_OAIQ098G083
import Definitions.Def_OAIQ098G1071
import Definitions.Def_OAIQ098G1077
import Definitions.Def_OAIQ098G1682
import Definitions.Def_OAIQ098G1693
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_ha27_0_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hk27_0_3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm27_0_0_3_s0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm27_0_0_3_s1_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm27_0_0_3_s2_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm27_0_0_3_s3_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm27_0_0_3_s4_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_hm27_0_0_3_s5_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_coefficientBox_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_Numerical_inflate_contains_g
import Theorems.Thm_OAI_SharpPlanar_cached_density_rule_contains_g
import Theorems.Thm_OAI_SharpPlanar_directMoment_rule_error_g
import Theorems.Thm_OAI_SharpPlanar_table_range_mass_g
import Theorems.Thm_OAI_SharpPlanar_transformedMoment_rule_error_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerIntervals

lemma zeroBox_contains : zeroBox.Contains 0 := by simp [zeroBox,CBox.Contains,RBox.Contains]
end SharpPlanar.IntegerIntervals

namespace SharpPlanar.IntegerIntervals

lemma finSum_contains {N : ℕ} {f : Fin N → CBox} {g : Fin N → ℂ}
    (h : ∀ i, (f i).Contains (g i)) : (finSum f).Contains (∑ i, g i) := by
  induction N with
  | zero => simpa [finSum] using zeroBox_contains
  | succ N ih =>
    rw [Fin.sum_univ_succ]
    exact CBox.contains_add_g (h 0) (ih (fun i => h i.succ))

end SharpPlanar.IntegerIntervals

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighMomentsBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Interval enclosures for direct and transformed moments of arbitrary order -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid Numerical
lemma fullMoment_error (a tr : Bool) {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 100) (ell : ℕ) :
    ‖fullMomentIntegral a tr m ell-fullMomentRule a tr m ell‖ < 1/10^22 := by
  cases tr
  · exact directMoment_rule_error_g _ _ (table_range_mass_g a) hm0 hm1 (by norm_num) ell
  · exact transformedMoment_rule_error_g _ _ (table_range_mass_g a) hm0 hm1 (by norm_num) ell
lemma fullAtomBox_contains (a tr : Bool) {kernel : Fin 7 → CBox} {m : ℝ} {ell : ℕ}
    (hk : ∀ j, (kernel j).Contains (fullFactor tr m ell ((j.val:ℝ)/6))) :
    (tableAtomBox a kernel).Contains (fullMomentAtom a tr m ell) := by
  have hh := finSum_contains (fun j : Fin 7 => CBox.contains_mul_g
    (CBox.contains_scale_g (coefficientBox_contains_g j.val) (if j.val=0 then 1 else 2) 1 (by norm_num)) (hk j))
  have hs := CBox.contains_scale_g hh (if a then 17 else -13) 1000 (by norm_num)
  change (tableAtomBox a kernel).Contains _ at hs
  convert hs using 1
  all_goals try with_reducible_and_instances rfl
  cases a <;> simp [fullMomentAtom,tableConstant]
lemma fullMoment_contains {a tr : Bool} {m : ℝ} {ell : ℕ} {ab rb : CBox}
    (ha : ab.Contains (fullMomentAtom a tr m ell))
    (hr : rb.Contains (fullMomentRule a tr m ell)) (hm0 : 0 ≤ m) (hm1 : m ≤ 100) :
    (inflate (ab.add rb).re).Contains (fullMoment a tr m ell) := by
  apply inflate_contains_g (CBox.contains_add_g ha hr).1
  unfold fullMoment
  have he := (Complex.abs_re_le_norm (fullMomentIntegral a tr m ell-fullMomentRule a tr m ell)).trans_lt
    (fullMoment_error a tr hm0 hm1 ell)
  simpa only [Complex.add_re,Complex.sub_re,add_sub_add_left_eq_sub] using he
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_LowBlock27_0
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
open IntegerIntervals IntegerBasis IntegerGrid Numerical
namespace hm27_0_0_3
lemma sums_eq (j : Fin 6) (i : Fin 16) : chunk j i = sums j i := by
  fin_cases j
  · exact s0_eq_g i
  · exact s1_eq_g i
  · exact s2_eq_g i
  · exact s3_eq_g i
  · exact s4_eq_g i
  · exact s5_eq_g i
lemma checked : cachedMomentRuleBox density0 hk27_0_3 = ans := by
  change (finSum (fun j => (finSum (fun i => chunk j i)).scale 1 6)) = ans
  simp_rw [sums_eq]
  decide +kernel
lemma contains : ans.Contains (fullMomentRule false false 27 3) := by
  rw [← checked]
  exact @cached_density_rule_contains_g density0 hk27_0_3 (tableDensity false) (fullFactor false 27 3) density0_contains_g hk27_0_3_contains_g
lemma atomChecked : tableAtomBox false ha27_0_3 = atomAnswer := by decide +kernel
lemma atomContains : atomAnswer.Contains (fullMomentAtom false false 27 3) := by
  rw [← atomChecked]
  exact @fullAtomBox_contains false false ha27_0_3 27 3 ha27_0_3_contains_g
lemma realChecked : inflate (atomAnswer.add ans).re = realAnswer := by decide +kernel
lemma realContains_g_oai : realAnswer.Contains (fullMoment false false 27 3) := by
  rw [← realChecked]
  exact fullMoment_contains atomContains contains (by norm_num) (by norm_num)
end hm27_0_0_3
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.hm27_0_0_3.realContains_g_oai := @OAI.SharpPlanar.CachedData.hm27_0_0_3.realContains_g_oai
