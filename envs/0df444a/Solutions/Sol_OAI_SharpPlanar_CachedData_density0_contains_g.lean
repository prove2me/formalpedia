-- Prove2me | solution 1 for OAI.SharpPlanar.CachedData.density0_contains_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T21:25:20.051706+00:00
-- url     : https://prove2.me/submissions/0cd276af-f2c2-4a1d-8682-2ce0ee262fa3

import Mathlib
import Definitions.Def_OAIQ098G395
import Definitions.Def_OAIQ098G397
import Definitions.Def_OAIQ098G1681
import Theorems.Thm_OAI_SharpPlanar_CachedData_density0_eq_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm0_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm100_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm12_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm13_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm15_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm16_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm19_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm1_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm21_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm24_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm25_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm27_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm28_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm31_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm33_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm36_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm37_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm39_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm3_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm40_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm43_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm45_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm48_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm49_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm4_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm51_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm52_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm55_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm57_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm60_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm61_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm63_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm64_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm67_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm69_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm72_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm73_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm75_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm76_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm79_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm7_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm81_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm84_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm85_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm87_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm88_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm91_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm93_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm96_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm97_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm99_contains_g
import Theorems.Thm_OAI_SharpPlanar_CachedData_tableTerm9_contains_g
import Theorems.Thm_OAI_SharpPlanar_IntegerIntervals_CBox_contains_add_g

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

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerAlpha IntegerCompact

lemma complexU_ofReal (n j : ℕ) (t : ℝ) : complexU n j t = u n j t := rfl
lemma complexV_ofReal (n j : ℕ) (t : ℝ) : complexV n j t = v n j t := rfl


end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite cardinal densities

Finite rational coefficient families determine the densities used in the quadrature estimates.
-/

namespace SharpPlanar
open IntegerIntervals IntegerBasis IntegerGrid
open scoped BigOperators

lemma tableDensity_weighted (i : Bool) (j : ℕ) (w t : ℝ) :
    (w:ℂ)*tableDensity i j t =
      ∑ n : Fin 101, (((tableC i n:ℝ):ℂ)*((w:ℂ)*basisFunction false n j t) +
        ((tableD i n:ℝ):ℂ)*((w:ℂ)*basisFunction true n j t)) := by
  rw [tableDensity,finiteDensity,Finset.mul_sum,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [basisFunction,Bool.false_eq_true,ite_false, if_false,ite_true, if_true,complexU_ofReal,complexV_ofReal]
  ring

end SharpPlanar

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
lemma tableTerm2_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 2 j i k).Contains (((if d then (tableD a 2:ℝ) else (tableC a 2:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 2 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm5_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 5 j i k).Contains (((if d then (tableD a 5:ℝ) else (tableC a 5:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 5 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm6_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 6 j i k).Contains (((if d then (tableD a 6:ℝ) else (tableC a 6:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 6 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm8_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 8 j i k).Contains (((if d then (tableD a 8:ℝ) else (tableC a 8:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 8 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm10_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 10 j i k).Contains (((if d then (tableD a 10:ℝ) else (tableC a 10:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 10 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm11_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 11 j i k).Contains (((if d then (tableD a 11:ℝ) else (tableC a 11:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 11 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm14_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 14 j i k).Contains (((if d then (tableD a 14:ℝ) else (tableC a 14:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 14 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm17_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 17 j i k).Contains (((if d then (tableD a 17:ℝ) else (tableC a 17:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 17 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm18_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 18 j i k).Contains (((if d then (tableD a 18:ℝ) else (tableC a 18:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 18 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm20_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 20 j i k).Contains (((if d then (tableD a 20:ℝ) else (tableC a 20:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 20 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm22_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 22 j i k).Contains (((if d then (tableD a 22:ℝ) else (tableC a 22:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 22 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm23_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 23 j i k).Contains (((if d then (tableD a 23:ℝ) else (tableC a 23:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 23 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm26_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 26 j i k).Contains (((if d then (tableD a 26:ℝ) else (tableC a 26:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 26 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm29_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 29 j i k).Contains (((if d then (tableD a 29:ℝ) else (tableC a 29:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 29 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm30_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 30 j i k).Contains (((if d then (tableD a 30:ℝ) else (tableC a 30:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 30 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm32_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 32 j i k).Contains (((if d then (tableD a 32:ℝ) else (tableC a 32:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 32 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm34_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 34 j i k).Contains (((if d then (tableD a 34:ℝ) else (tableC a 34:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 34 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm35_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 35 j i k).Contains (((if d then (tableD a 35:ℝ) else (tableC a 35:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 35 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm38_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 38 j i k).Contains (((if d then (tableD a 38:ℝ) else (tableC a 38:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 38 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm41_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 41 j i k).Contains (((if d then (tableD a 41:ℝ) else (tableC a 41:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 41 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm42_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 42 j i k).Contains (((if d then (tableD a 42:ℝ) else (tableC a 42:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 42 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm44_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 44 j i k).Contains (((if d then (tableD a 44:ℝ) else (tableC a 44:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 44 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm46_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 46 j i k).Contains (((if d then (tableD a 46:ℝ) else (tableC a 46:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 46 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm47_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 47 j i k).Contains (((if d then (tableD a 47:ℝ) else (tableC a 47:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 47 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm50_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 50 j i k).Contains (((if d then (tableD a 50:ℝ) else (tableC a 50:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 50 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm53_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 53 j i k).Contains (((if d then (tableD a 53:ℝ) else (tableC a 53:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 53 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm54_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 54 j i k).Contains (((if d then (tableD a 54:ℝ) else (tableC a 54:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 54 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm56_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 56 j i k).Contains (((if d then (tableD a 56:ℝ) else (tableC a 56:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 56 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm58_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 58 j i k).Contains (((if d then (tableD a 58:ℝ) else (tableC a 58:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 58 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm59_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 59 j i k).Contains (((if d then (tableD a 59:ℝ) else (tableC a 59:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 59 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm62_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 62 j i k).Contains (((if d then (tableD a 62:ℝ) else (tableC a 62:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 62 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm65_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 65 j i k).Contains (((if d then (tableD a 65:ℝ) else (tableC a 65:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 65 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm66_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 66 j i k).Contains (((if d then (tableD a 66:ℝ) else (tableC a 66:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 66 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm68_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 68 j i k).Contains (((if d then (tableD a 68:ℝ) else (tableC a 68:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 68 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm70_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 70 j i k).Contains (((if d then (tableD a 70:ℝ) else (tableC a 70:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 70 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm71_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 71 j i k).Contains (((if d then (tableD a 71:ℝ) else (tableC a 71:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 71 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm74_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 74 j i k).Contains (((if d then (tableD a 74:ℝ) else (tableC a 74:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 74 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm77_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 77 j i k).Contains (((if d then (tableD a 77:ℝ) else (tableC a 77:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 77 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm78_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 78 j i k).Contains (((if d then (tableD a 78:ℝ) else (tableC a 78:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 78 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm80_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 80 j i k).Contains (((if d then (tableD a 80:ℝ) else (tableC a 80:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 80 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm82_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 82 j i k).Contains (((if d then (tableD a 82:ℝ) else (tableC a 82:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 82 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm83_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 83 j i k).Contains (((if d then (tableD a 83:ℝ) else (tableC a 83:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 83 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm86_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 86 j i k).Contains (((if d then (tableD a 86:ℝ) else (tableC a 86:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 86 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm89_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 89 j i k).Contains (((if d then (tableD a 89:ℝ) else (tableC a 89:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 89 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm90_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 90 j i k).Contains (((if d then (tableD a 90:ℝ) else (tableC a 90:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 90 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm92_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 92 j i k).Contains (((if d then (tableD a 92:ℝ) else (tableC a 92:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 92 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm94_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 94 j i k).Contains (((if d then (tableD a 94:ℝ) else (tableC a 94:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 94 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm95_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 95 j i k).Contains (((if d then (tableD a 95:ℝ) else (tableC a 95:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 95 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm98_contains (a d : Bool) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d 98 j i k).Contains (((if d then (tableD a 98:ℝ) else (tableC a 98:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d 98 j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  cases a <;> cases d <;> norm_num [tableTerm,allColumns,tableNum,tableD,tableC,tableRaw,CBox.scale,CBox.rat,RBox.rat,RBox.scale,CBox.Contains,RBox.Contains,precision]
lemma tableTerm_contains (a d : Bool) (n : Fin 101) (j : Fin 6) (i k : Fin 16) :
    (tableTerm a d n j i k).Contains (((if d then (tableD a n:ℝ) else (tableC a n:ℝ)):ℂ)*((fejerWeight (16*i.val+k.val):ℂ)*basisFunction d n j.val (quadraturePoint j.val (16*i.val+k.val)))) := by
  fin_cases n
  · exact tableTerm0_contains_g a d j i k
  · exact tableTerm1_contains_g a d j i k
  · exact tableTerm2_contains a d j i k
  · exact tableTerm3_contains_g a d j i k
  · exact tableTerm4_contains_g a d j i k
  · exact tableTerm5_contains a d j i k
  · exact tableTerm6_contains a d j i k
  · exact tableTerm7_contains_g a d j i k
  · exact tableTerm8_contains a d j i k
  · exact tableTerm9_contains_g a d j i k
  · exact tableTerm10_contains a d j i k
  · exact tableTerm11_contains a d j i k
  · exact tableTerm12_contains_g a d j i k
  · exact tableTerm13_contains_g a d j i k
  · exact tableTerm14_contains a d j i k
  · exact tableTerm15_contains_g a d j i k
  · exact tableTerm16_contains_g a d j i k
  · exact tableTerm17_contains a d j i k
  · exact tableTerm18_contains a d j i k
  · exact tableTerm19_contains_g a d j i k
  · exact tableTerm20_contains a d j i k
  · exact tableTerm21_contains_g a d j i k
  · exact tableTerm22_contains a d j i k
  · exact tableTerm23_contains a d j i k
  · exact tableTerm24_contains_g a d j i k
  · exact tableTerm25_contains_g a d j i k
  · exact tableTerm26_contains a d j i k
  · exact tableTerm27_contains_g a d j i k
  · exact tableTerm28_contains_g a d j i k
  · exact tableTerm29_contains a d j i k
  · exact tableTerm30_contains a d j i k
  · exact tableTerm31_contains_g a d j i k
  · exact tableTerm32_contains a d j i k
  · exact tableTerm33_contains_g a d j i k
  · exact tableTerm34_contains a d j i k
  · exact tableTerm35_contains a d j i k
  · exact tableTerm36_contains_g a d j i k
  · exact tableTerm37_contains_g a d j i k
  · exact tableTerm38_contains a d j i k
  · exact tableTerm39_contains_g a d j i k
  · exact tableTerm40_contains_g a d j i k
  · exact tableTerm41_contains a d j i k
  · exact tableTerm42_contains a d j i k
  · exact tableTerm43_contains_g a d j i k
  · exact tableTerm44_contains a d j i k
  · exact tableTerm45_contains_g a d j i k
  · exact tableTerm46_contains a d j i k
  · exact tableTerm47_contains a d j i k
  · exact tableTerm48_contains_g a d j i k
  · exact tableTerm49_contains_g a d j i k
  · exact tableTerm50_contains a d j i k
  · exact tableTerm51_contains_g a d j i k
  · exact tableTerm52_contains_g a d j i k
  · exact tableTerm53_contains a d j i k
  · exact tableTerm54_contains a d j i k
  · exact tableTerm55_contains_g a d j i k
  · exact tableTerm56_contains a d j i k
  · exact tableTerm57_contains_g a d j i k
  · exact tableTerm58_contains a d j i k
  · exact tableTerm59_contains a d j i k
  · exact tableTerm60_contains_g a d j i k
  · exact tableTerm61_contains_g a d j i k
  · exact tableTerm62_contains a d j i k
  · exact tableTerm63_contains_g a d j i k
  · exact tableTerm64_contains_g a d j i k
  · exact tableTerm65_contains a d j i k
  · exact tableTerm66_contains a d j i k
  · exact tableTerm67_contains_g a d j i k
  · exact tableTerm68_contains a d j i k
  · exact tableTerm69_contains_g a d j i k
  · exact tableTerm70_contains a d j i k
  · exact tableTerm71_contains a d j i k
  · exact tableTerm72_contains_g a d j i k
  · exact tableTerm73_contains_g a d j i k
  · exact tableTerm74_contains a d j i k
  · exact tableTerm75_contains_g a d j i k
  · exact tableTerm76_contains_g a d j i k
  · exact tableTerm77_contains a d j i k
  · exact tableTerm78_contains a d j i k
  · exact tableTerm79_contains_g a d j i k
  · exact tableTerm80_contains a d j i k
  · exact tableTerm81_contains_g a d j i k
  · exact tableTerm82_contains a d j i k
  · exact tableTerm83_contains a d j i k
  · exact tableTerm84_contains_g a d j i k
  · exact tableTerm85_contains_g a d j i k
  · exact tableTerm86_contains a d j i k
  · exact tableTerm87_contains_g a d j i k
  · exact tableTerm88_contains_g a d j i k
  · exact tableTerm89_contains a d j i k
  · exact tableTerm90_contains a d j i k
  · exact tableTerm91_contains_g a d j i k
  · exact tableTerm92_contains a d j i k
  · exact tableTerm93_contains_g a d j i k
  · exact tableTerm94_contains a d j i k
  · exact tableTerm95_contains a d j i k
  · exact tableTerm96_contains_g a d j i k
  · exact tableTerm97_contains_g a d j i k
  · exact tableTerm98_contains a d j i k
  · exact tableTerm99_contains_g a d j i k
  · exact tableTerm100_contains_g a d j i k
end SharpPlanar.CachedData

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Certificate_TableDensityValues
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
lemma density0_contains_g_oai (j : Fin 6) (i k : Fin 16) :
    (density0 j i k).Contains ((fejerWeight (16*i.val+k.val):ℂ)*tableDensity false j.val (quadraturePoint j.val (16*i.val+k.val))) := by
  rw [← density0_eq_g,tableDensity_weighted]
  exact finSum_contains (fun n => CBox.contains_add_g (tableTerm_contains false false n j i k) (tableTerm_contains false true n j i k))
end SharpPlanar.CachedData

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.CachedData.density0_contains_g_oai := @OAI.SharpPlanar.CachedData.density0_contains_g_oai
