-- Prove2me | solution 1 for OAI.AtomicTriangular.Construction.global_signs_tg
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:35:04.689688+00:00
-- url     : https://prove2.me/submissions/a3734bba-cfcd-464d-ba74-542367a28965

import Mathlib
import Definitions.Def_TriangularGaussian
import Definitions.Def_OAIQ262T163
import Definitions.Def_OAIQ262T166
import Definitions.Def_OAIQ262T259
import Definitions.Def_OAIQ262T260
import Theorems.Thm_OAI_AtomicTriangular_Construction_exceptional_rational_comparison_tg
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_negative_polynomial_tg
import Theorems.Thm_OAI_AtomicTriangular_Construction_near_positive_polynomial_tg

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData5_00_mem (j : Fin 31) : (remainderData5_00 j).Mem (remainderWave 0 0 (nearNode 5) (nearRadius 5) (frequency j)) := by
  rw [← remainderData5_00_calc]
  exact remainderBox_mem 0 0 5 j (taylorNormTable_mem 0 0 j) (remainderData5_00_pre j).1 (remainderData5_00_pre j).2
lemma remainderData5_01_mem (j : Fin 31) : (remainderData5_01 j).Mem (remainderWave 0 1 (nearNode 5) (nearRadius 5) (frequency j)) := by
  rw [← remainderData5_01_calc]
  exact remainderBox_mem 0 1 5 j (taylorNormTable_mem 0 1 j) (remainderData5_01_pre j).1 (remainderData5_01_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderConst5_0_bound : rawRemainderConstant 0 5 < (2754364/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData5_00_mem j) (fourierNorm_mem j))
  rw [remainderConst5_0_calc] at hh
  have hb := ri_mem_lt hh 2754364 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst5_1_bound : rawRemainderConstant 1 5 < (146533704/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData5_01_mem j) (fourierNorm_mem j))
  rw [remainderConst5_1_calc] at hh
  have hb := ri_mem_lt hh 146533704 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable5 (c d : Fin 22) : 3*(rawRemainderColumn 0 5 c+rawRemainderColumn 1 5 d)+(6/1000)*(rawRemainderConstant 0 5+rawRemainderConstant 1 5) < (75/10000000:ℝ) := by
  have h0 := remainderColumns5_0_bound c
  have h1 := remainderColumns5_1_bound d
  have h2 := remainderConst5_0_bound
  have h3 := remainderConst5_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderData6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderData6_00_mem (j : Fin 31) : (remainderData6_00 j).Mem (remainderWave 0 0 (nearNode 6) (nearRadius 6) (frequency j)) := by
  rw [← remainderData6_00_calc]
  exact remainderBox_mem 0 0 6 j (taylorNormTable_mem 0 0 j) (remainderData6_00_pre j).1 (remainderData6_00_pre j).2
lemma remainderData6_01_mem (j : Fin 31) : (remainderData6_01 j).Mem (remainderWave 0 1 (nearNode 6) (nearRadius 6) (frequency j)) := by
  rw [← remainderData6_01_calc]
  exact remainderBox_mem 0 1 6 j (taylorNormTable_mem 0 1 j) (remainderData6_01_pre j).1 (remainderData6_01_pre j).2
lemma remainderData6_10_mem (j : Fin 31) : (remainderData6_10 j).Mem (remainderWave 1 0 (nearNode 6) (nearRadius 6) (frequency j)) := by
  rw [← remainderData6_10_calc]
  exact remainderBox_mem 1 0 6 j (taylorNormTable_mem 1 0 j) (remainderData6_10_pre j).1 (remainderData6_10_pre j).2
lemma remainderData6_11_mem (j : Fin 31) : (remainderData6_11 j).Mem (remainderWave 1 1 (nearNode 6) (nearRadius 6) (frequency j)) := by
  rw [← remainderData6_11_calc]
  exact remainderBox_mem 1 1 6 j (taylorNormTable_mem 1 1 j) (remainderData6_11_pre j).1 (remainderData6_11_pre j).2
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderSums6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainderColumns6_0_bound (c : Fin 22) : rawRemainderColumn 0 6 c < (202/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData6_10_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns6_0_calc] at hh
  have hb := ri_mem_lt hh 202 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderColumns6_1_bound (c : Fin 22) : rawRemainderColumn 1 6 c < (162/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData6_11_mem j) (columnNormTable_mem ⟨c.val,by omega⟩ j))
  rw [remainderColumns6_1_calc] at hh
  have hb := ri_mem_lt hh 162 1000000000000000 (by norm_num) (by clear hh; revert c; decide +kernel)
  simpa only [rawRemainderColumn,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst6_0_bound : rawRemainderConstant 0 6 < (2754364/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData6_00_mem j) (fourierNorm_mem j))
  rw [remainderConst6_0_calc] at hh
  have hb := ri_mem_lt hh 2754364 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderConst6_1_bound : rawRemainderConstant 1 6 < (67290392/1000000000000000:ℝ) := by
  have hh := RI.mem_sum (fun j : Fin 31 => RI.mem_mul (remainderData6_01_mem j) (fourierNorm_mem j))
  rw [remainderConst6_1_calc] at hh
  have hb := ri_mem_lt hh 67290392 1000000000000000 (by norm_num) (by decide +kernel)
  simpa only [rawRemainderConstant,Nat.cast_ofNat,Nat.cast_one,Int.cast_ofNat,Int.cast_one] using hb
lemma remainderTable6 (c d : Fin 22) : 3*(rawRemainderColumn 0 6 c+rawRemainderColumn 1 6 d)+(6/1000)*(rawRemainderConstant 0 6+rawRemainderConstant 1 6) < (75/10000000:ℝ) := by
  have h0 := remainderColumns6_0_bound c
  have h1 := remainderColumns6_1_bound d
  have h2 := remainderConst6_0_bound
  have h3 := remainderConst6_1_bound
  linarith
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_RemainderPre
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace AtomicTriangular.FiniteCertificate
open Construction AtomicTriangular.Interval Complex
lemma remainder_table (n : Fin 7) (c d : Fin 22) :
    3*(rawRemainderColumn 0 n c+rawRemainderColumn 1 n d)+(6/1000)*(rawRemainderConstant 0 n+rawRemainderConstant 1 n) <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  fin_cases n
  · exact remainderTable0 c d
  · exact remainderTable1 c d
  · exact remainderTable2 c d
  · exact remainderTable3 c d
  · exact remainderTable4 c d
  · exact remainderTable5 c d
  · exact remainderTable6 c d
end AtomicTriangular.FiniteCertificate
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Taylor_FiniteTaylorError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma finiteJ_remainder (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {v : ℝ}
    (hv : |v|≤nearRadius n) :
    ‖complexError (fun k s => finiteJJet side (actualParameter z) k s) (nearNode n) v‖ <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  obtain ⟨c,_,hc⟩ := Finset.exists_max_image Finset.univ (rawRemainderColumn 0 n) Finset.univ_nonempty
  obtain ⟨d,_,hd⟩ := Finset.exists_max_image Finset.univ (rawRemainderColumn 1 n) Finset.univ_nonempty
  have h0 := finite_input_error ((gamma side *ᵥ actualParameter z) 2) (finiteApprox side (actualParameter z)) 0 n hv (fun i => hc i (Finset.mem_univ i))
  have h1 := finite_input_error ((gamma (otherSide side) *ᵥ actualParameter z) 2) (finiteApprox (otherSide side) (actualParameter z)) 1 n hv (fun i => hd i (Finset.mem_univ i))
  have hg (side : Fin 2) : |(gamma side *ᵥ actualParameter z) 2|=6/1000 := by
    rw [gamma_actual]
    change |(if side.val=0 then -(3/500:ℝ) else 3/500)|=6/1000
    fin_cases side <;> (first | (simp; all_goals first | (norm_num; done) | rfl | decide) | (norm_num; done) | norm_num)
  rw [hg] at h0 h1
  have ha := mul_le_mul_of_nonneg_right (finiteApprox_norm side (actualParameter z) (actualParameter_mem hz hzB)).le (rawRemainderColumn_nonneg 0 n c)
  have hb := mul_le_mul_of_nonneg_right (finiteApprox_norm (otherSide side) (actualParameter z) (actualParameter_mem hz hzB)).le (rawRemainderColumn_nonneg 1 n d)
  simp only [finiteJJet_pair,pairJJet]
  rw [complexError_add]
  have hh := norm_add_le
    (complexError (fun k s => inputJJet (coefficientInput ((gamma side *ᵥ actualParameter z) 2) (finiteApprox side (actualParameter z)) 0) 0 k s) (nearNode n) v)
    (complexError (fun k s => inputJJet (coefficientInput ((gamma (otherSide side) *ᵥ actualParameter z) 2) (finiteApprox (otherSide side) (actualParameter z)) 0) 1 k s) (nearNode n) v)
  have htab := remainder_table n c d
  linarith
lemma finiteTaylor_error (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z≤Z) (n : Fin 7) {y τ : ℝ}
    (hv : |y*τ|≤nearRadius n) :
    |deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+y*τ)-finiteTaylor side (nearNode n) y (actualParameter z) τ| <
      (if n.val=0 then (161/100000:ℝ) else 75/10000000) := by
  rw [←complexDeleted_finiteJ,←complexTaylor_finiteJ,←Complex.sub_re]
  exact (Complex.abs_re_le_norm _).trans_lt (finiteJ_remainder side hz hzB n hv)
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_DeletedAccuracy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators lp
open Complex Matrix Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deleted_accuracy (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    |deletedSecond (actualJ side z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ)-
      finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ|<nearError n y := by
  let corr := pairJ (coefficientInput 0 (extendFiniteError (actualFiniteError side z hz hzB)) (actualTail side z hz hzB))
      (coefficientInput 0 (extendFiniteError (actualFiniteError (otherSide side) z hz hzB)) (actualTail (otherSide side) z hz hzB))
  let K : ℝ := (1/100000)*finiteCurvatureEnvelope (nearBase n y)+(3/1000000000)*tailCurvatureEnvelope (nearBase n y)
  have hb : |deletedSecond corr (nearNode n) (nearNode n+nearDisplacement n y*τ)| ≤ K := by
    have hh := deletedSecond_bound (f:=corr) ((pairJ_contDiff _ _).of_le (by norm_num))
      (m:=(nearNode n:ℝ)) (s:=(nearNode n:ℝ)+nearDisplacement n y*τ) (C:=2*K) ?_
    · linarith
    · intro t ht
      have htB : curvaturePoint (nearBase n y) ≤ t := (le_min (nearBase_le_node n y) (nearBase_le_cell n y hτ)).trans ht.1
      have ha (side : Fin 2) : ‖extendFiniteError (actualFiniteError side z hz hzB)‖ ≤ (1/100000:ℝ) := by
        rw [extendFiniteError_norm]
        simpa only [show (10:ℝ)^5=100000 by norm_num] using (actualFiniteError_norm side hz hzB).le
      have hh := pairJ_curvature _ _ _ _ (nearBase n y) htB (ha side) (ha (otherSide side))
        (actualTail_norm side hz hzB).le (actualTail_norm (otherSide side) hz hzB).le
      norm_num at hh
      change |iteratedDeriv 2 corr t|/2 ≤ K at hh
      linarith
  rw [actualJ_split,deletedSecond_add ((finiteJ_contDiff _ _).of_le (by norm_num)) ((pairJ_contDiff _ _).of_le (by norm_num))]
  have he := finiteTaylor_error side hz hzB n (nearDisplacement_mul_radius n y hτ)
  have hh := abs_add_le (deletedSecond (finiteJ side (actualParameter z)) (nearNode n) (nearNode n+nearDisplacement n y*τ)-finiteTaylor side (nearNode n) (nearDisplacement n y) (actualParameter z) τ)
    (deletedSecond corr (nearNode n) (nearNode n+nearDisplacement n y*τ))
  have htab := near_error_arithmetic n y
  dsimp only [K] at hb
  convert lt_of_le_of_lt hh (by linarith) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_OrdinaryComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_positive_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    0 ≤ deletedSecond (actualJ 1 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_positive_polynomial_tg (actualParameter z) (actualParameter_mem hz hzB) n y hτ
  have he := (abs_lt.mp (deleted_accuracy 1 hz hzB n y hτ)).1
  linarith
lemma near_ordinary_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) (hne : ¬(n=0 ∧ y=1)) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  have hh := near_negative_polynomial_tg (actualParameter z) (actualParameter_mem hz hzB) n y hne hτ
  have he := (abs_lt.mp (deleted_accuracy 0 hz hzB n y hτ)).2
  have hg := gaussian_ordinary_lower hz hzB n y hne hτ
  linarith
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_NearSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma near_exceptional_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) 1 (1+τ) ≤ deletedSecond (gaussianG z) 1 (1+τ) := by
  have he := (abs_lt.mp (deleted_accuracy 0 hz hzB 0 1 hτ)).2
  have hg := gaussian_deleted_right (m:=1) hz hτ.1
  have ht := exceptional_rational_comparison_tg (actualParameter z) (actualParameter_mem hz hzB) hτ hz hzB
  change finiteTaylor 0 1 1 (actualParameter z) τ+3/1000 ≤ _ at ht
  norm_num [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum,nearError] at he
  norm_num at hg
  change _ ≤ Q 1*((3*z+τ)/(6*z^2+4*z*τ+τ^2)) at ht
  linarith
lemma near_deleted {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    deletedSecond (actualJ 0 z hz hzB) (nearNode n) (nearNode n+nearDisplacement n y*τ) ≤
      deletedSecond (gaussianG z) (nearNode n) (nearNode n+nearDisplacement n y*τ) := by
  by_cases he : n=0 ∧ y=1
  · rcases he with ⟨rfl,rfl⟩
    simpa [nearNode,finiteNode,residue,nearDisplacement,nearDisplacementNum] using near_exceptional_deleted hz hzB hτ
  · exact near_ordinary_deleted hz hzB n y he hτ
lemma nearCell_signs {z : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Fin 7) (y : Fin 2) {τ : ℝ} (hτ : τ∈Icc 0 1) :
    actualJ 0 z hz hzB (nearNode n+nearDisplacement n y*τ) ≤ gaussianG z (nearNode n+nearDisplacement n y*τ) ∧
      0 ≤ actualJ 1 z hz hzB (nearNode n+nearDisplacement n y*τ) := by
  have hn : 0<nearNode n ∧ nearNode n%36∈residues := finiteNode_node ⟨n.val,by omega⟩
  have hj := actual_interpolation hz hzB ⟨nearNode n,hn⟩
  exact ⟨real_function_le_of_deleted hj.1 hj.2.1 (near_deleted hz hzB n y hτ),
    real_function_nonneg_of_deleted hj.2.2.1 hj.2.2.2 (near_positive_deleted hz hzB n y hτ)⟩
lemma near_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc 0 (29/2)) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,y,τ,hτ,rfl⟩ := near_cell_cover hs
  exact nearCell_signs hz hzB n y hτ
end AtomicTriangular.Construction
end

end OAI
end

section
-- module Solutions.OAIQ262_TG.Triangular_Signs_FarSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma far_signs_of_barrier {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ))
    (hb : farK i*(s-n.val)^2 ≤ (3/500)*realP s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  have hj := actual_interpolation hz hzB n
  have hj0 := actualJ0_jets 0 hz hzB n
  have hj1 := actualJ0_jets 1 hz hzB n
  have h0 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted 0 hz hzB n i hs hm hs14 hm14)).2 (sq_nonneg (s-n.val))
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted 1 hz hzB n i hs hm hs14 hm14)).1 (sq_nonneg (s-n.val))
  have hg := mul_nonneg (sq_nonneg (s-n.val)) (gaussian_deleted_nonneg hz n.val (s-n.val))
  simp only [add_sub_cancel] at hg
  have he0 := deletedSecond_identity (actualJ0 0 z hz hzB) n.val s
  rw [hj0.1,hj0.2,hj.1,hj.2.1] at he0
  have he1 := deletedSecond_identity (actualJ0 1 z hz hzB) n.val s
  rw [hj1.1,hj1.2,hj.2.2.1,hj.2.2.2] at he1
  have heG := deletedSecond_identity (gaussianG z) n.val s
  have hd0 := congrFun (actualJ_decompose 0 hz hzB) s
  have hd1 := congrFun (actualJ_decompose 1 hz hzB) s
  norm_num [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sideConstant] at hd0 hd1
  constructor <;> nlinarith
lemma middle_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc (29/2) 23) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨m,hm,hP⟩ := realP_middle_lower hs
  have hn : 0 < m ∧ m%36∈residues := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num [residues]
  have hm14 : 29/2 ≤ (m:ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num
  apply far_signs_of_barrier hz hzB ⟨m,hn⟩ 3 hs.1 hm14 hs.1 hm14
  have hK : farK 3=(140109/10000000:ℝ) := by
    change (301/100:ℝ)*(465/100000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  change farK 3*(s-m)^2 ≤ (3/500)*realP s
  rw [hK]
  nlinarith [sq_nonneg (s-m)]
lemma later_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 23 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,hn,hP⟩ := realP_far_lower hs
  have hm : (23:ℝ) ≤ n.val := by exact_mod_cast (show (23:ℤ) ≤ n.val by omega)
  apply far_signs_of_barrier hz hzB n 4 hs hm (by linarith) (by linarith)
  have hK : farK 4=(8363/100000000:ℝ) := by
    change (301/100:ℝ)*(23/1000000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  rw [hK]
  nlinarith [sq_nonneg (s-n.val)]
theorem global_signs_tg_oai {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 0 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  by_cases h14 : s ≤ 29/2
  · exact near_signs hz hzB ⟨hs,h14⟩
  by_cases h23 : s ≤ 23
  · exact middle_signs hz hzB ⟨by linarith,h23⟩
  exact later_signs hz hzB (by linarith)
end AtomicTriangular.Construction
end

end OAI
end

theorem solution : type_of% @OAI.AtomicTriangular.Construction.global_signs_tg_oai := @OAI.AtomicTriangular.Construction.global_signs_tg_oai
