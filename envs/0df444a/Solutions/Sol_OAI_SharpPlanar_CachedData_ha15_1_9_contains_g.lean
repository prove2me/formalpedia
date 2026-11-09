-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.ha15_1_9_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T22:00:52.586581+00:00
-- url     : https://prove2.me/submissions/6a5263f6-f706-47d7-b090-ad86f6a7ce78

import Mathlib
import Definitions.Def_OAIQ098G091
import Definitions.Def_OAIQ098G383
import Definitions.Def_OAIQ098G388
import Definitions.Def_OAIQ098G411
import Definitions.Def_OAIQ098G1680
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint2_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint5_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_atomPoint6_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointLambda_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerBasis_pointZ_eq_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_mul_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_powFast_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_scale_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_piI_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_rcast_contains_g
import Theorems.Thm_OAI_SharpPlanar_complexLambda_ofReal_g
import Theorems.Thm_OAI_SharpPlanar_complexZ_ofReal_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_BasisIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar.IntegerBasis
open IntegerIntervals

lemma kernel0Box_contains {p : PointBox} {t : ℝ} (hp : p.Contains t) {m : ℕ}
    (hm : m < 128) : (kernel0Box p m).Contains
      (lambda t*Complex.exp (Complex.I*Real.pi*z t*m)) := by
  have he := CBox.contains_powFast_g hp.2.2.2.2 9 (4*m) (by omega)
  rw [← Complex.exp_nat_mul] at he
  have hz := CBox.contains_mul_g hp.2.1 he
  unfold kernel0Box
  convert hz using 1
  all_goals try with_reducible_and_instances rfl
  rw [pointLambda_eq_g,pointZ_eq_g]
  congr 2
  push_cast
  ring

end SharpPlanar.IntegerBasis

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MomentRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recurrences for the direct and transformed Gaussian moments -/

namespace SharpPlanar
open ComplexConjugate
open IntegerIntervals IntegerBasis
lemma direct_factor_step (m : ℝ) (ell : ℕ) (t : ℂ) :
    complexDirectFactor m 1 (ell+1) t = complexDirectFactor m 1 ell t *
      (Complex.I*Real.pi*t) / ((ell+1:ℕ):ℂ) := by
  unfold complexDirectFactor
  simp only [Complex.ofReal_one,mul_one,pow_succ,Nat.factorial_succ,Nat.cast_mul]
  ring
lemma transformed_factor_step (m : ℝ) (ell : ℕ) (t : ℂ) :
    complexTransformedFactor m 1 (ell+1) t = complexTransformedFactor m 1 ell t *
      (Complex.I*Real.pi*complexZ t) / ((ell+1:ℕ):ℂ) := by
  unfold complexTransformedFactor
  simp only [Complex.ofReal_one,mul_one,pow_succ,Nat.factorial_succ,Nat.cast_mul]
  ring

lemma transformed_factor_zero_contains {a : CBox} {t : ℝ} {m : ℕ}
    (ha : a.Contains (lambda t*Complex.exp (Complex.I*Real.pi*z t*m))) :
    a.Contains (complexTransformedFactor m 1 0 t) := by
  simpa only [complexTransformedFactor,complexZ_ofReal_g,complexLambda_ofReal_g,pow_zero,
    Nat.factorial_zero,Nat.cast_one,div_one,mul_one,Complex.ofReal_natCast] using ha
lemma factor_step_contains {a b : CBox} {w z : ℂ} (ha : a.Contains w)
    (hb : b.Contains z) (ell : ℕ) :
    ((a.mul b).scale 1 (ell+1)).Contains (w*z/((ell+1:ℕ):ℂ)) := by
  have hh := CBox.contains_scale_g (CBox.contains_mul_g ha hb) 1 (ell+1) (by omega)
  convert hh using 1 <;> first | (with_reducible_and_instances rfl) | (push_cast <;> ring)
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_AtomKernels
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
lemma atomPoints_contains (j : Fin 7) : (atomPoints j).Contains ((j.val:ℝ)/6) := by
  fin_cases j
  · simpa [atomPoints] using atomPoint0_contains_g
  · simpa [atomPoints] using atomPoint1_contains_g
  · simpa [atomPoints] using atomPoint2_contains_g
  · simpa [atomPoints] using atomPoint3_contains_g
  · simpa [atomPoints] using atomPoint4_contains_g
  · simpa [atomPoints] using atomPoint5_contains_g
  · simpa [atomPoints] using atomPoint6_contains_g
lemma atomKernel15_0_eq (j : Fin 7) : atomKernel15_0 j = kernel0Box (atomPoints j) 15 := by
  fin_cases j <;> decide +kernel
lemma atomKernel15_0_contains (j : Fin 7) : (atomKernel15_0 j).Contains
    (complexTransformedFactor 15 1 0 ((j.val:ℝ)/6)) := by
  rw [atomKernel15_0_eq]
  have hh := kernel0Box_contains (atomPoints_contains j) (m:=15) (by decide)
  have h0 := transformed_factor_zero_contains hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one] using h0
end SharpPlanar.CachedData

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
lemma fullFactor_step_contains {a b : CBox} {tr : Bool} {m : ℝ} {ell : ℕ} {t : ℝ}
    (ha : a.Contains (fullFactor tr m ell t))
    (hb : b.Contains (Complex.I*Real.pi*(if tr then z t else (t:ℂ)))) :
    ((a.mul b).scale 1 (ell+1)).Contains (fullFactor tr m (ell+1) t) := by
  cases tr
  · change a.Contains (complexDirectFactor m 1 ell t) at ha
    change b.Contains (Complex.I*Real.pi*t) at hb
    change ((a.mul b).scale 1 (ell+1)).Contains (complexDirectFactor m 1 (ell+1) t)
    rw [direct_factor_step]
    exact factor_step_contains ha hb ell
  · change a.Contains (complexTransformedFactor m 1 ell t) at ha
    change b.Contains (Complex.I*Real.pi*z t) at hb
    change ((a.mul b).scale 1 (ell+1)).Contains (complexTransformedFactor m 1 (ell+1) t)
    rw [transformed_factor_step,complexZ_ofReal_g]
    exact factor_step_contains ha hb ell
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_HighRuleBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gaussian moment bounds at the quadrature nodes and atoms -/

namespace SharpPlanar
open IntegerIntervals IntegerBasis Numerical
lemma fullFactor_step_atom_contains {a : CBox} {tr : Bool} {m : ℝ} {ell : ℕ}
    (j : Fin 7) (ha : a.Contains (fullFactor tr m ell ((j.val:ℝ)/6))) :
    ((a.mul (if tr then piI.mul (CachedData.atomPoints j).z else
      piI.mul (rcast (CachedData.atomPoints j).t))).scale 1 (ell+1)).Contains
      (fullFactor tr m (ell+1) ((j.val:ℝ)/6)) := by
  have hap : a.Contains (fullFactor tr m ell (((j.val:ℝ)/6:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using ha
  have hb : (if tr then piI.mul (CachedData.atomPoints j).z else
      piI.mul (rcast (CachedData.atomPoints j).t)).Contains
      (Complex.I*Real.pi*(if tr then z ((j.val:ℝ)/6) else (((j.val:ℝ)/6:ℝ):ℂ))) := by
    cases tr
    · simpa only [Bool.false_eq_true,ite_false, if_false] using
        CBox.contains_mul_g piI_contains_g (rcast_contains_g (CachedData.atomPoints_contains j).1)
    · have hh := (CachedData.atomPoints_contains j).2.2.1
      rw [pointZ_eq_g] at hh
      simpa only [ite_true, if_true] using CBox.contains_mul_g piI_contains_g hh
  simpa only [Complex.ofReal_div,Complex.ofReal_natCast,Complex.ofReal_ofNat] using
    fullFactor_step_contains hap hb
end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_HighHeaders15
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
lemma ha15_1_0_eq (j : Fin 7) : ha15_1_0 j = atomKernel15_0 j := by fin_cases j <;> decide +kernel
lemma ha15_1_0_contains (j : Fin 7) : (ha15_1_0 j).Contains (fullFactor true 15 0 ((j.val:ℝ)/6)) := by
  rw [ha15_1_0_eq]
  simpa only [fullFactor,ite_true, if_true] using atomKernel15_0_contains j
lemma ha15_1_1_eq (j : Fin 7) : ha15_1_1 j = ((ha15_1_0 j).mul (piI.mul (atomPoints j).z)).scale 1 1 := by fin_cases j <;> decide +kernel
lemma ha15_1_1_contains (j : Fin 7) : (ha15_1_1 j).Contains (fullFactor true 15 1 ((j.val:ℝ)/6)) := by
  rw [ha15_1_1_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_0 j) true 15 0 j (ha15_1_0_contains j)
lemma ha15_1_2_eq (j : Fin 7) : ha15_1_2 j = ((ha15_1_1 j).mul (piI.mul (atomPoints j).z)).scale 1 2 := by fin_cases j <;> decide +kernel
lemma ha15_1_2_contains (j : Fin 7) : (ha15_1_2 j).Contains (fullFactor true 15 2 ((j.val:ℝ)/6)) := by
  rw [ha15_1_2_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_1 j) true 15 1 j (ha15_1_1_contains j)
lemma ha15_1_3_eq (j : Fin 7) : ha15_1_3 j = ((ha15_1_2 j).mul (piI.mul (atomPoints j).z)).scale 1 3 := by fin_cases j <;> decide +kernel
lemma ha15_1_3_contains (j : Fin 7) : (ha15_1_3 j).Contains (fullFactor true 15 3 ((j.val:ℝ)/6)) := by
  rw [ha15_1_3_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_2 j) true 15 2 j (ha15_1_2_contains j)
lemma ha15_1_4_eq (j : Fin 7) : ha15_1_4 j = ((ha15_1_3 j).mul (piI.mul (atomPoints j).z)).scale 1 4 := by fin_cases j <;> decide +kernel
lemma ha15_1_4_contains (j : Fin 7) : (ha15_1_4 j).Contains (fullFactor true 15 4 ((j.val:ℝ)/6)) := by
  rw [ha15_1_4_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_3 j) true 15 3 j (ha15_1_3_contains j)
lemma ha15_1_5_eq (j : Fin 7) : ha15_1_5 j = ((ha15_1_4 j).mul (piI.mul (atomPoints j).z)).scale 1 5 := by fin_cases j <;> decide +kernel
lemma ha15_1_5_contains (j : Fin 7) : (ha15_1_5 j).Contains (fullFactor true 15 5 ((j.val:ℝ)/6)) := by
  rw [ha15_1_5_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_4 j) true 15 4 j (ha15_1_4_contains j)
lemma ha15_1_6_eq (j : Fin 7) : ha15_1_6 j = ((ha15_1_5 j).mul (piI.mul (atomPoints j).z)).scale 1 6 := by fin_cases j <;> decide +kernel
lemma ha15_1_6_contains (j : Fin 7) : (ha15_1_6 j).Contains (fullFactor true 15 6 ((j.val:ℝ)/6)) := by
  rw [ha15_1_6_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_5 j) true 15 5 j (ha15_1_5_contains j)
lemma ha15_1_7_eq (j : Fin 7) : ha15_1_7 j = ((ha15_1_6 j).mul (piI.mul (atomPoints j).z)).scale 1 7 := by fin_cases j <;> decide +kernel
lemma ha15_1_7_contains (j : Fin 7) : (ha15_1_7 j).Contains (fullFactor true 15 7 ((j.val:ℝ)/6)) := by
  rw [ha15_1_7_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_6 j) true 15 6 j (ha15_1_6_contains j)
lemma ha15_1_8_eq (j : Fin 7) : ha15_1_8 j = ((ha15_1_7 j).mul (piI.mul (atomPoints j).z)).scale 1 8 := by fin_cases j <;> decide +kernel
lemma ha15_1_8_contains (j : Fin 7) : (ha15_1_8 j).Contains (fullFactor true 15 8 ((j.val:ℝ)/6)) := by
  rw [ha15_1_8_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_7 j) true 15 7 j (ha15_1_7_contains j)
lemma ha15_1_9_eq (j : Fin 7) : ha15_1_9 j = ((ha15_1_8 j).mul (piI.mul (atomPoints j).z)).scale 1 9 := by fin_cases j <;> decide +kernel
lemma ha15_1_9_contains_g_oai (j : Fin 7) : (ha15_1_9 j).Contains (fullFactor true 15 9 ((j.val:ℝ)/6)) := by
  rw [ha15_1_9_eq]
  simpa only [Bool.false_eq_true,ite_false, if_false,ite_true, if_true,Nat.cast_ofNat,Nat.cast_zero,Nat.cast_one,Int.reduceAdd,Nat.reduceAdd] using @fullFactor_step_atom_contains (ha15_1_8 j) true 15 8 j (ha15_1_8_contains j)
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.ha15_1_9_contains_g_oai := @OAI.SharpPlanar.CachedData.ha15_1_9_contains_g_oai
