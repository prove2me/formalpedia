-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2AX_roots_exhausted
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:53:28.808537+00:00
-- url     : https://prove2.me/submissions/0cde2353-93b8-490b-8fb9-4239301c7688

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Forall2
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Multiset.Filter
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_OAICatalanIrrationality
import Definitions.Def_OAICatalanBarrierPolynomials
import Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_eq_explicit
import Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_interval0_roots_card_le
import Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_interval1_roots_card_le

section
-- module Solutions.OAICatalan.Catalan.FirstBarrier.BarrierCaseOneRootExistence
namespace OAI

noncomputable section

namespace InternalCatalan

open Polynomial

theorem rationalPolynomial_root_mem_Ioo_of_eval_mul_neg (p : ℚ[X])
    {a b : ℚ} (hab : a < b) (hs : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, x ∈ Set.Ioo (a : ℝ) (b : ℝ) ∧
      (p.map (Rat.castHom ℝ)).eval x = 0 := by
  have heval (q : ℚ) :
      (p.map (Rat.castHom ℝ)).eval (q : ℝ) = ((p.eval q : ℚ) : ℝ) := by
    change (p.map (Rat.castHom ℝ)).eval ((Rat.castHom ℝ) q) =
      (Rat.castHom ℝ) (p.eval q)
    exact Polynomial.eval_map_apply (Rat.castHom ℝ) q
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hs' : (p.map (Rat.castHom ℝ)).eval (a : ℝ) *
      (p.map (Rat.castHom ℝ)).eval (b : ℝ) < 0 := by
    simp only [heval]
    exact_mod_cast hs
  have hc : ContinuousOn (fun x : ℝ => (p.map (Rat.castHom ℝ)).eval x)
      (Set.Icc (a : ℝ) (b : ℝ)) := (p.map (Rat.castHom ℝ)).continuousOn
  rcases mul_neg_iff.mp hs' with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ)) := ⟨hb, ha⟩
    rcases (intermediate_value_Ioo' hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩
  · have hz : (0 : ℝ) ∈ Set.Ioo
        ((p.map (Rat.castHom ℝ)).eval (a : ℝ))
        ((p.map (Rat.castHom ℝ)).eval (b : ℝ)) := ⟨ha, hb⟩
    rcases (intermediate_value_Ioo hab'.le hc) hz with ⟨x, hx, hroot⟩
    exact ⟨x, hx, hroot⟩

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXExplicitGroup7
namespace OAI

noncomputable section

namespace InternalCatalan











open Polynomial

























open Polynomial













































def barrierCase2AXCoefficient (k : ℕ) : ℚ :=
  ([30307837230416268959058568549773/390625000000000000000000000000000000, -388916241323180816905894669551174674670591/1220703125000000000000000000000000000000000000, -4006784573305776602421578075882271527736951993/1220703125000000000000000000000000000000000000000, 1096183954671168725038063556149715387207630523987/61035156250000000000000000000000000000000000000000, -7952498478159654485025286927264757800766806449689461/91552734375000000000000000000000000000000000000000000, -173251421552630457395123417783409511688090895941195417/4577636718750000000000000000000000000000000000000000000, 1222120559292925857030215856817101460328272419116765158471/228881835937500000000000000000000000000000000000000000000, -9002153638868141433199303807358329862172831171827356580769/762939453125000000000000000000000000000000000000000000000, -20430716055979141452221343027896515893162803128568450962685989/286102294921875000000000000000000000000000000000000000000000, 1551532006333267422675951782124692841597537382079615796002800463/7152557373046875000000000000000000000000000000000000000000000, 3430606054133072949419772876756861170914507767290711053103959413/11920928955078125000000000000000000000000000000000000000000000, -505916145739811163969788025388361352785579438858951141108745471259/357627868652343750000000000000000000000000000000000000000000000, 170660418192088844983109244182859397071662139279111654553014694589/357627868652343750000000000000000000000000000000000000000000000, 111802796781702066809285191673959138398105580484717994246462464509/37252902984619140625000000000000000000000000000000000000000000, -45027051395514975383376671261049412207657650433594188527438870439467/8940696716308593750000000000000000000000000000000000000000000000, 16509003686870615770955343186283294035863361608791696629553878592691/4470348358154296875000000000000000000000000000000000000000000000, 39466767544097375649642054097024548875637201165892323429352340271739/8940696716308593750000000000000000000000000000000000000000000000, -26755287098024999828824584679516056137747845043276649132658782483257/1490116119384765625000000000000000000000000000000000000000000000, 168070108726307711595570993536980340222190659762943286668833668339249/8940696716308593750000000000000000000000000000000000000000000000, -832051437619875563928237488265539747452368600303675116627132838151/596046447753906250000000000000000000000000000000000000000000000, -1606955218748669940170405173174994300085549469536010604897519048427/74505805969238281250000000000000000000000000000000000000000000, 2433137840814792444702356102800877012295375212980653188941121382049/59604644775390625000000000000000000000000000000000000000000000, -51739167878202129506248629638529892446087925833524235401379411247437/1490116119384765625000000000000000000000000000000000000000000000, -1082632152122822888597045006113490327710626764705887378288008787721/1490116119384765625000000000000000000000000000000000000000000000, 4986802693523860777269281537299839923932961413477019773621637642489/149011611938476562500000000000000000000000000000000000000000000, -4416319363306657399702427900939605066393368736600070485184725132417/93132257461547851562500000000000000000000000000000000000000000, 430725170281186155782445052791711482276044238852484890595621567703/11641532182693481445312500000000000000000000000000000000000000, -5858283778532255307754122045950281887663478271777393285415699291/1164153218269348144531250000000000000000000000000000000000000, -9526115897201306594135430784633925777531015543666247018754883/465661287307739257812500000000000000000000000000000000000, 627455201464947631518402076531001458986822444066613529731827/23283064365386962890625000000000000000000000000000000000, -1505504840851826080906317395924633616756101528774509886831583/72759576141834259033203125000000000000000000000000000000, 6417086791213399557054520364584799762086047849866994798447/909494701772928237915039062500000000000000000000000000, 463404787046380243295539802625032027305554181181839276149/145519152283668518066406250000000000000000000000000000, -79635932674577498395062383173973277954089807724779169/14551915228366851806640625000000000000000000000000, 306952565700894986183323747480996064114191827407661/72759576141834259033203125000000000000000000000, -29493660039437141081639612350479227384504308233/14551915228366851806640625000000000000000000, 60188546402546646873910140358666064623915029/145519152283668518066406250000000000000000] : List ℚ).getD k 0










theorem barrierCase2AXExplicit_coeff_35 :
    barrierCase2AXExplicit.coeff 35 = barrierCase2AXCoefficient 35 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_36 :
    barrierCase2AXExplicit.coeff 36 = barrierCase2AXCoefficient 36 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXExplicit
namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AXExplicit_coeff_0 :
    barrierCase2AXExplicit.coeff 0 = barrierCase2AXCoefficient 0 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero]

theorem barrierCase2AXExplicit_coeff_1 :
    barrierCase2AXExplicit.coeff 1 = barrierCase2AXCoefficient 1 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_2 :
    barrierCase2AXExplicit.coeff 2 = barrierCase2AXCoefficient 2 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_3 :
    barrierCase2AXExplicit.coeff 3 = barrierCase2AXCoefficient 3 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_4 :
    barrierCase2AXExplicit.coeff 4 = barrierCase2AXCoefficient 4 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_5 :
    barrierCase2AXExplicit.coeff 5 = barrierCase2AXCoefficient 5 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_6 :
    barrierCase2AXExplicit.coeff 6 = barrierCase2AXCoefficient 6 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_7 :
    barrierCase2AXExplicit.coeff 7 = barrierCase2AXCoefficient 7 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_8 :
    barrierCase2AXExplicit.coeff 8 = barrierCase2AXCoefficient 8 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_9 :
    barrierCase2AXExplicit.coeff 9 = barrierCase2AXCoefficient 9 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_10 :
    barrierCase2AXExplicit.coeff 10 = barrierCase2AXCoefficient 10 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_11 :
    barrierCase2AXExplicit.coeff 11 = barrierCase2AXCoefficient 11 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_12 :
    barrierCase2AXExplicit.coeff 12 = barrierCase2AXCoefficient 12 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_13 :
    barrierCase2AXExplicit.coeff 13 = barrierCase2AXCoefficient 13 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_14 :
    barrierCase2AXExplicit.coeff 14 = barrierCase2AXCoefficient 14 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_15 :
    barrierCase2AXExplicit.coeff 15 = barrierCase2AXCoefficient 15 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_16 :
    barrierCase2AXExplicit.coeff 16 = barrierCase2AXCoefficient 16 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_17 :
    barrierCase2AXExplicit.coeff 17 = barrierCase2AXCoefficient 17 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_18 :
    barrierCase2AXExplicit.coeff 18 = barrierCase2AXCoefficient 18 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_19 :
    barrierCase2AXExplicit.coeff 19 = barrierCase2AXCoefficient 19 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_20 :
    barrierCase2AXExplicit.coeff 20 = barrierCase2AXCoefficient 20 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_21 :
    barrierCase2AXExplicit.coeff 21 = barrierCase2AXCoefficient 21 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_22 :
    barrierCase2AXExplicit.coeff 22 = barrierCase2AXCoefficient 22 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_23 :
    barrierCase2AXExplicit.coeff 23 = barrierCase2AXCoefficient 23 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_24 :
    barrierCase2AXExplicit.coeff 24 = barrierCase2AXCoefficient 24 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_25 :
    barrierCase2AXExplicit.coeff 25 = barrierCase2AXCoefficient 25 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_26 :
    barrierCase2AXExplicit.coeff 26 = barrierCase2AXCoefficient 26 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_27 :
    barrierCase2AXExplicit.coeff 27 = barrierCase2AXCoefficient 27 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_28 :
    barrierCase2AXExplicit.coeff 28 = barrierCase2AXCoefficient 28 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_29 :
    barrierCase2AXExplicit.coeff 29 = barrierCase2AXCoefficient 29 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_30 :
    barrierCase2AXExplicit.coeff 30 = barrierCase2AXCoefficient 30 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_31 :
    barrierCase2AXExplicit.coeff 31 = barrierCase2AXCoefficient 31 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_32 :
    barrierCase2AXExplicit.coeff 32 = barrierCase2AXCoefficient 32 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_33 :
    barrierCase2AXExplicit.coeff 33 = barrierCase2AXCoefficient 33 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_coeff_34 :
    barrierCase2AXExplicit.coeff 34 = barrierCase2AXCoefficient 34 := by
  simp only [barrierCase2AXExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2AXExplicit_natDegree : barrierCase2AXExplicit.natDegree = 36 := by
  unfold barrierCase2AXExplicit
  compute_degree!

theorem barrierCase2AXExplicit_coeff (k : ℕ) :
    barrierCase2AXExplicit.coeff k = barrierCase2AXCoefficient k := by
  by_cases hk : k < 37
  · interval_cases k
    · exact barrierCase2AXExplicit_coeff_0
    · exact barrierCase2AXExplicit_coeff_1
    · exact barrierCase2AXExplicit_coeff_2
    · exact barrierCase2AXExplicit_coeff_3
    · exact barrierCase2AXExplicit_coeff_4
    · exact barrierCase2AXExplicit_coeff_5
    · exact barrierCase2AXExplicit_coeff_6
    · exact barrierCase2AXExplicit_coeff_7
    · exact barrierCase2AXExplicit_coeff_8
    · exact barrierCase2AXExplicit_coeff_9
    · exact barrierCase2AXExplicit_coeff_10
    · exact barrierCase2AXExplicit_coeff_11
    · exact barrierCase2AXExplicit_coeff_12
    · exact barrierCase2AXExplicit_coeff_13
    · exact barrierCase2AXExplicit_coeff_14
    · exact barrierCase2AXExplicit_coeff_15
    · exact barrierCase2AXExplicit_coeff_16
    · exact barrierCase2AXExplicit_coeff_17
    · exact barrierCase2AXExplicit_coeff_18
    · exact barrierCase2AXExplicit_coeff_19
    · exact barrierCase2AXExplicit_coeff_20
    · exact barrierCase2AXExplicit_coeff_21
    · exact barrierCase2AXExplicit_coeff_22
    · exact barrierCase2AXExplicit_coeff_23
    · exact barrierCase2AXExplicit_coeff_24
    · exact barrierCase2AXExplicit_coeff_25
    · exact barrierCase2AXExplicit_coeff_26
    · exact barrierCase2AXExplicit_coeff_27
    · exact barrierCase2AXExplicit_coeff_28
    · exact barrierCase2AXExplicit_coeff_29
    · exact barrierCase2AXExplicit_coeff_30
    · exact barrierCase2AXExplicit_coeff_31
    · exact barrierCase2AXExplicit_coeff_32
    · exact barrierCase2AXExplicit_coeff_33
    · exact barrierCase2AXExplicit_coeff_34
    · exact barrierCase2AXExplicit_coeff_35
    · exact barrierCase2AXExplicit_coeff_36
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [barrierCase2AXExplicit_natDegree]; omega)]
    unfold barrierCase2AXCoefficient
    symm
    apply List.getD_eq_default
    simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0
namespace OAI

namespace InternalCatalan

section




open Polynomial




theorem barrierCase2AX_natDegree : barrierCase2AX.natDegree = 36 := by
  rw [barrierCase2AX_eq_explicit]
  exact barrierCase2AXExplicit_natDegree

end
section

theorem barrierCase2AX_coeff_small (k : ℕ) (_hk : k < 37) :
    barrierCase2AX.coeff k = barrierCase2AXCoefficient k := by
  rw [barrierCase2AX_eq_explicit]
  exact barrierCase2AXExplicit_coeff k

end

noncomputable section

open Polynomial
open scoped BigOperators

def barrierCase2AXFiniteEval (x : ℚ) : ℚ :=
  ∑ k ∈ Finset.range 37, barrierCase2AXCoefficient k * x ^ k


theorem barrierCase2AX_eval_finite (x : ℚ) :
    barrierCase2AX.eval x = barrierCase2AXFiniteEval x := by
  have hd : barrierCase2AX.natDegree < 37 := by
    rw [barrierCase2AX_natDegree]
    decide
  calc
    barrierCase2AX.eval x =
        ∑ k ∈ Finset.range 37, barrierCase2AX.coeff k * x ^ k :=
      Polynomial.eval_eq_sum_range' hd x
    _ = barrierCase2AXFiniteEval x := by
      unfold barrierCase2AXFiniteEval
      apply Finset.sum_congr rfl
      intro k hk
      rw [barrierCase2AX_coeff_small k (Finset.mem_range.mp hk)]


end

section
open Polynomial







end

private theorem barrierCase2AX_bracket_finite_sign_00 :
    barrierCase2AXFiniteEval (barrierBracketLeft (-9601109148)) *
      barrierCase2AXFiniteEval (barrierBracketRight (-9601109148)) < 0 := by
  decide +kernel

theorem barrierCase2AX_bracket_sign_00 :
    barrierCase2AX.eval (barrierBracketLeft (-9601109148)) *
      barrierCase2AX.eval (barrierBracketRight (-9601109148)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-9601109148)),
    barrierCase2AX_eval_finite (barrierBracketRight (-9601109148))]
  exact barrierCase2AX_bracket_finite_sign_00

theorem barrierCase2AX_bracket_sign_01 :
    barrierCase2AX.eval (barrierBracketLeft (-8942317572)) *
      barrierCase2AX.eval (barrierBracketRight (-8942317572)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-8942317572)),
    barrierCase2AX_eval_finite (barrierBracketRight (-8942317572))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_02 :
    barrierCase2AX.eval (barrierBracketLeft (-7608305633)) *
      barrierCase2AX.eval (barrierBracketRight (-7608305633)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-7608305633)),
    barrierCase2AX_eval_finite (barrierBracketRight (-7608305633))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_03 :
    barrierCase2AX.eval (barrierBracketLeft (-6503394794)) *
      barrierCase2AX.eval (barrierBracketRight (-6503394794)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-6503394794)),
    barrierCase2AX_eval_finite (barrierBracketRight (-6503394794))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_04 :
    barrierCase2AX.eval (barrierBracketLeft (-5185864065)) *
      barrierCase2AX.eval (barrierBracketRight (-5185864065)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-5185864065)),
    barrierCase2AX_eval_finite (barrierBracketRight (-5185864065))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_05 :
    barrierCase2AX.eval (barrierBracketLeft (-4015634158)) *
      barrierCase2AX.eval (barrierBracketRight (-4015634158)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-4015634158)),
    barrierCase2AX_eval_finite (barrierBracketRight (-4015634158))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_06 :
    barrierCase2AX.eval (barrierBracketLeft (-3108806646)) *
      barrierCase2AX.eval (barrierBracketRight (-3108806646)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-3108806646)),
    barrierCase2AX_eval_finite (barrierBracketRight (-3108806646))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_07 :
    barrierCase2AX.eval (barrierBracketLeft (-2067921826)) *
      barrierCase2AX.eval (barrierBracketRight (-2067921826)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-2067921826)),
    barrierCase2AX_eval_finite (barrierBracketRight (-2067921826))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_08 :
    barrierCase2AX.eval (barrierBracketLeft (-1589849496)) *
      barrierCase2AX.eval (barrierBracketRight (-1589849496)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (-1589849496)),
    barrierCase2AX_eval_finite (barrierBracketRight (-1589849496))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_09 :
    barrierCase2AX.eval (barrierBracketLeft (1531948062)) *
      barrierCase2AX.eval (barrierBracketRight (1531948062)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (1531948062)),
    barrierCase2AX_eval_finite (barrierBracketRight (1531948062))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_10 :
    barrierCase2AX.eval (barrierBracketLeft (2072448179)) *
      barrierCase2AX.eval (barrierBracketRight (2072448179)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (2072448179)),
    barrierCase2AX_eval_finite (barrierBracketRight (2072448179))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_11 :
    barrierCase2AX.eval (barrierBracketLeft (3208186484)) *
      barrierCase2AX.eval (barrierBracketRight (3208186484)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (3208186484)),
    barrierCase2AX_eval_finite (barrierBracketRight (3208186484))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_12 :
    barrierCase2AX.eval (barrierBracketLeft (4381119427)) *
      barrierCase2AX.eval (barrierBracketRight (4381119427)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (4381119427)),
    barrierCase2AX_eval_finite (barrierBracketRight (4381119427))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_13 :
    barrierCase2AX.eval (barrierBracketLeft (5851354199)) *
      barrierCase2AX.eval (barrierBracketRight (5851354199)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (5851354199)),
    barrierCase2AX_eval_finite (barrierBracketRight (5851354199))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_14 :
    barrierCase2AX.eval (barrierBracketLeft (7269030693)) *
      barrierCase2AX.eval (barrierBracketRight (7269030693)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (7269030693)),
    barrierCase2AX_eval_finite (barrierBracketRight (7269030693))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_15 :
    barrierCase2AX.eval (barrierBracketLeft (8390277402)) *
      barrierCase2AX.eval (barrierBracketRight (8390277402)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (8390277402)),
    barrierCase2AX_eval_finite (barrierBracketRight (8390277402))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_16 :
    barrierCase2AX.eval (barrierBracketLeft (9332614564)) *
      barrierCase2AX.eval (barrierBracketRight (9332614564)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (9332614564)),
    barrierCase2AX_eval_finite (barrierBracketRight (9332614564))]
  decide +kernel

theorem barrierCase2AX_bracket_sign_17 :
    barrierCase2AX.eval (barrierBracketLeft (9709786219)) *
      barrierCase2AX.eval (barrierBracketRight (9709786219)) < 0 := by
  rw [barrierCase2AX_eval_finite (barrierBracketLeft (9709786219)),
    barrierCase2AX_eval_finite (barrierBracketRight (9709786219))]
  decide +kernel




end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoYRootSimplicity
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
















end

section













open Polynomial


theorem barrierCase2AX_bracket_signs (m : ℤ) (hm : m ∈ barrierCase2XBrackets) :
    barrierCase2AX.eval (barrierBracketLeft m) *
      barrierCase2AX.eval (barrierBracketRight m) < 0 := by
  simp only [barrierCase2XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact barrierCase2AX_bracket_sign_00
  · exact barrierCase2AX_bracket_sign_01
  · exact barrierCase2AX_bracket_sign_02
  · exact barrierCase2AX_bracket_sign_03
  · exact barrierCase2AX_bracket_sign_04
  · exact barrierCase2AX_bracket_sign_05
  · exact barrierCase2AX_bracket_sign_06
  · exact barrierCase2AX_bracket_sign_07
  · exact barrierCase2AX_bracket_sign_08
  · exact barrierCase2AX_bracket_sign_09
  · exact barrierCase2AX_bracket_sign_10
  · exact barrierCase2AX_bracket_sign_11
  · exact barrierCase2AX_bracket_sign_12
  · exact barrierCase2AX_bracket_sign_13
  · exact barrierCase2AX_bracket_sign_14
  · exact barrierCase2AX_bracket_sign_15
  · exact barrierCase2AX_bracket_sign_16
  · exact barrierCase2AX_bracket_sign_17

theorem barrierCase2X_bracket_domain (m : ℤ) (hm : m ∈ barrierCase2XBrackets) :
    -1 < barrierBracketLeft m ∧
      barrierBracketLeft m < barrierBracketRight m ∧
      barrierBracketRight m < 1 ∧
      (barrierBracketRight m < 0 ∨ 0 < barrierBracketLeft m) := by
  simp only [barrierCase2XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  <;> norm_num [barrierBracketLeft, barrierBracketRight]




end

theorem barrierCase2AX_bracket_root (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  exact rationalPolynomial_root_mem_Ioo_of_eval_mul_neg barrierCase2AX
    (barrierCase2X_bracket_domain m hm).2.1 (barrierCase2AX_bracket_signs m hm)


open Polynomial





















open Polynomial














end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXRootSimplicity
namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial





















































theorem barrierCase2AX_domain_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 18 := by
  classical
  let s0 := s.filter (fun x => x ∈ Set.Ioo (-1 : ℝ) 0)
  let s1 := s.filter (fun x => x ∈ Set.Ioo (0 : ℝ) 1)
  have h0 : s0.card ≤ 9 := by
    apply barrierCase2AX_interval0_roots_card_le
    intro x hx
    have hh := Finset.mem_filter.mp hx
    exact ⟨hh.2, (hs x hh.1).2⟩
  have h1 : s1.card ≤ 9 := by
    apply barrierCase2AX_interval1_roots_card_le
    intro x hx
    have hh := Finset.mem_filter.mp hx
    exact ⟨hh.2, (hs x hh.1).2⟩
  have hcover : s ⊆ s0 ∪ s1 := by
    intro x hx
    rcases (hs x hx).1 with hn | hp
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hx, hn⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hx, hp⟩))
  calc
    s.card ≤ (s0 ∪ s1).card := Finset.card_le_card hcover
    _ ≤ s0.card + s1.card := Finset.card_union_le _ _
    _ ≤ 9 + 9 := Nat.add_le_add h0 h1
    _ = 18 := rfl

private theorem barrierCase2X_bracket_subset_domain {m : ℤ}
    (hm : m ∈ barrierCase2XBrackets) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 := by
  obtain ⟨ha, _, hb, hzero⟩ := barrierCase2X_bracket_domain m hm
  have ha' : (-1 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast ha
  have hb' : (barrierBracketRight m : ℝ) < (1 : ℝ) := by exact_mod_cast hb
  rcases hzero with hn | hp
  · have hn' : (barrierBracketRight m : ℝ) < (0 : ℝ) := by exact_mod_cast hn
    exact Or.inl ⟨ha'.trans hx.1, hx.2.trans hn'⟩
  · have hp' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hp
    exact Or.inr ⟨hp'.trans hx.1, hx.2.trans hb'⟩

private theorem barrierCase2X_brackets_disjoint {m n : ℤ}
    (hm : m ∈ barrierCase2XBrackets) (hn : n ∈ barrierCase2XBrackets)
    (hmn : m ≠ n) {x : ℝ}
    (hx : x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hy : x ∈ Set.Ioo (barrierBracketLeft n : ℝ) (barrierBracketRight n : ℝ)) :
    False := by
  have : Std.Symm (fun a b : ℤ => a + 2 ≤ b ∨ b + 2 ≤ a) :=
    ⟨fun _ _ h => h.symm⟩
  have hp : barrierCase2XBrackets.Pairwise
      (fun a b : ℤ => a + 2 ≤ b ∨ b + 2 ≤ a) := by decide
  rcases hp.forall hm hn hmn with hmn' | hnm'
  · have hq : barrierBracketRight m ≤ barrierBracketLeft n := by
      unfold barrierBracketRight barrierBracketLeft
      exact div_le_div_of_nonneg_right (by exact_mod_cast hmn') (by norm_num)
    have hr : (barrierBracketRight m : ℝ) ≤ (barrierBracketLeft n : ℝ) := by
      exact_mod_cast hq
    exact (not_lt_of_ge hr) (hy.1.trans hx.2)
  · have hq : barrierBracketRight n ≤ barrierBracketLeft m := by
      unfold barrierBracketRight barrierBracketLeft
      exact div_le_div_of_nonneg_right (by exact_mod_cast hnm') (by norm_num)
    have hr : (barrierBracketRight n : ℝ) ≤ (barrierBracketLeft m : ℝ) := by
      exact_mod_cast hq
    exact (not_lt_of_ge hr) (hx.1.trans hy.2)

private def barrierCase2XChosenRoot (m : ℤ) : ℝ :=
  if hm : m ∈ barrierCase2XBrackets then
    Classical.choose (barrierCase2AX_bracket_root m hm)
  else 0

private theorem barrierCase2XChosenRoot_spec (m : ℤ)
    (hm : m ∈ barrierCase2XBrackets) :
    barrierCase2XChosenRoot m ∈
        Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval (barrierCase2XChosenRoot m) = 0 := by
  simpa only [barrierCase2XChosenRoot, dif_pos hm] using
    Classical.choose_spec (barrierCase2AX_bracket_root m hm)

private def barrierCase2XChosenRoots : Finset ℝ := by
  classical
  exact barrierCase2XBrackets.toFinset.image barrierCase2XChosenRoot

private theorem barrierCase2XChosenRoots_card : barrierCase2XChosenRoots.card = 18 := by
  classical
  have hinj : Set.InjOn barrierCase2XChosenRoot
      (↑barrierCase2XBrackets.toFinset : Set ℤ) := by
    intro m hm n hn heq
    have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
    have hn' : n ∈ barrierCase2XBrackets := List.mem_toFinset.mp hn
    by_contra hmn
    exact barrierCase2X_brackets_disjoint hm' hn' hmn
      (barrierCase2XChosenRoot_spec m hm').1
      (by simpa only [heq] using (barrierCase2XChosenRoot_spec n hn').1)
  unfold barrierCase2XChosenRoots
  rw [Finset.card_image_of_injOn hinj]
  norm_num [barrierCase2XBrackets]

private theorem barrierCase2XChosenRoots_spec {x : ℝ}
    (hx : x ∈ barrierCase2XChosenRoots) :
    x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  classical
  change x ∈ barrierCase2XBrackets.toFinset.image barrierCase2XChosenRoot at hx
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
  have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
  have hr := barrierCase2XChosenRoot_spec m hm'
  exact ⟨barrierCase2X_bracket_subset_domain hm' hr.1, hr.2⟩

private theorem barrierCase2AX_root_mem_chosen {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    x ∈ barrierCase2XChosenRoots := by
  classical
  by_contra hnot
  have hb : (insert x barrierCase2XChosenRoots).card ≤ 18 := by
    apply barrierCase2AX_domain_roots_card_le
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hx, hr⟩
    · exact barrierCase2XChosenRoots_spec hy
  rw [Finset.card_insert_of_notMem hnot, barrierCase2XChosenRoots_card] at hb
  norm_num at hb

theorem barrierCase2AX_roots_exhausted {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase2XBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  classical
  have hmem := barrierCase2AX_root_mem_chosen hx hr
  change x ∈ barrierCase2XBrackets.toFinset.image barrierCase2XChosenRoot at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hmem
  have hm' : m ∈ barrierCase2XBrackets := List.mem_toFinset.mp hm
  exact ⟨m, hm', (barrierCase2XChosenRoot_spec m hm').1⟩



















end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Polynomial

theorem solution {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 0 ∪ Set.Ioo (0 : ℝ) 1)
    (hr : (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) :
    ∃ m ∈ barrierCase2XBrackets,
      x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) := by
  first
  | exact @OAI.InternalCatalan.barrierCase2AX_roots_exhausted
  | (apply OAI.InternalCatalan.barrierCase2AX_roots_exhausted <;> assumption)

end
