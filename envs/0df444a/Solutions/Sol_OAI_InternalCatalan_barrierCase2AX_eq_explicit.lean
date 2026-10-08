-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2AX_eq_explicit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:47:59.196551+00:00
-- url     : https://prove2.me/submissions/76576b4f-e1e2-4695-829a-0bab6fbf47ba

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

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierCoefficientConvolution
namespace OAI

namespace InternalCatalan

open Polynomial
open scoped BigOperators

def barrierCoeffConv (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, a ij.1 * b ij.2

theorem barrier_coeff_mul_eq_conv (p q : ℚ[X]) (a b : ℕ → ℚ)
    (hp : ∀ k, p.coeff k = a k) (hq : ∀ k, q.coeff k = b k) (n : ℕ) :
    (p * q).coeff n = barrierCoeffConv a b n := by
  rw [Polynomial.coeff_mul]
  unfold barrierCoeffConv
  apply Finset.sum_congr rfl
  intro ij hij
  rw [hp, hq]

end InternalCatalan

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

def barrierCase2PTailNumeratorExplicit : ℚ[X] :=
  C (-334625418567286147906955121183793659/4882812500000000000000000000000000000000) +
  C (20127644970984429229663641286102109817/12207031250000000000000000000000000000000) * X ^ 1 +
  C (-2852876572408096311386663148074363127/610351562500000000000000000000000000000) * X ^ 2 +
  C (219782662978769686811412440485306881/3051757812500000000000000000000000000) * X ^ 3 +
  C (-4894248692719660966896600643752953/19073486328125000000000000000000000) * X ^ 4 +
  C (45491985122617474473894836809089153/15258789062500000000000000000000000) * X ^ 5 +
  C (-568781315379457100097709309340883/30517578125000000000000000000000) * X ^ 6 +
  C (803074381853681639161748844303/7629394531250000000000000000) * X ^ 7 +
  C (-5453962494228714418500320647/30517578125000000000000000) * X ^ 8 +
  C (680879861223820138383153/7629394531250000000000) * X ^ 9

def barrierCase2PTailProductExplicit : ℚ[X] :=
  C (4785447983749937204061879244701/24414062500000000000000000000000000) +
  C (-474962018866734369442083826221/1220703125000000000000000000000000) * X ^ 1 +
  C (7705227818365150047259368501/2441406250000000000000000000000) * X ^ 2 +
  C (-3589839094005450574517959947/610351562500000000000000000000) * X ^ 3 +
  C (84481480701896139333127067089/152587890625000000000000000000) * X ^ 4 +
  C (-8340696096348800303572388719/7629394531250000000000000000) * X ^ 5 +
  C (2527238180877059028537517647/76293945312500000000000000) * X ^ 6 +
  C (-1973789704813765919735753/30517578125000000000000) * X ^ 7 +
  C (37686962338137420137757/152587890625000000000) * X ^ 8 +
  C (-13017638552052412621/30517578125000000) * X ^ 9 +
  C (32299425202362199/152587890625000) * X ^ 10

theorem barrierCase2PTailNumerator_eq_explicit :
    barrierFractionNumerator (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) = barrierCase2PTailNumeratorExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2PTailNumeratorExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

theorem barrierCase2PTailProduct_eq_explicit :
    barrierFractionProduct (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) = barrierCase2PTailProductExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2PTailProductExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring






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
-- module Solutions.OAICatalan.Catalan.Energy.BarrierFractionAlgebra
namespace OAI

namespace InternalCatalan

open Polynomial

theorem barrierFractionProduct_append_exact (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (fs ++ gs) =
      barrierFractionProduct fs * barrierFractionProduct gs := by
  simp only [barrierFractionProduct, List.map_append, List.prod_append]

theorem barrierFractionNumerator_append_exact (fs gs : List (ℚ[X] × ℚ[X])) :
    barrierFractionNumerator (fs ++ gs) =
      barrierFractionNumerator fs * barrierFractionProduct gs +
        barrierFractionProduct fs * barrierFractionNumerator gs := by
  induction fs with
  | nil =>
      simp only [List.nil_append, barrierFractionNumerator, barrierFractionProduct,
        List.map_nil, List.prod_nil, zero_mul, one_mul, zero_add]
  | cons aq fs ih =>
      change aq.1 * barrierFractionProduct (fs ++ gs) +
          aq.2 * barrierFractionNumerator (fs ++ gs) =
        (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs) *
            barrierFractionProduct gs +
          (aq.2 * barrierFractionProduct fs) * barrierFractionNumerator gs
      rw [barrierFractionProduct_append_exact, ih]
      ring

theorem barrierFractionProduct_scale_exact (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionProduct (barrierScaleFractions c fs) = barrierFractionProduct fs := by
  simp only [barrierFractionProduct, barrierScaleFractions, List.map_map,
    Function.comp_def]

theorem barrierFractionNumerator_scale_exact (c : ℚ) (fs : List (ℚ[X] × ℚ[X])) :
    barrierFractionNumerator (barrierScaleFractions c fs) =
      C c * barrierFractionNumerator fs := by
  induction fs with
  | nil =>
      simp only [barrierScaleFractions, List.map_nil, barrierFractionNumerator, mul_zero]
  | cons aq fs ih =>
      change (C c * aq.1) * barrierFractionProduct (barrierScaleFractions c fs) +
          aq.2 * barrierFractionNumerator (barrierScaleFractions c fs) =
        C c * (aq.1 * barrierFractionProduct fs + aq.2 * barrierFractionNumerator fs)
      rw [barrierFractionProduct_scale_exact, ih]
      ring

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXBaseProductCoefficientsData
namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial

def barrierCase2VTailNumeratorExplicit : ℚ[X] :=
  C (-37299120109/50000000000) +
  C (57077222972893/50000000000000) * X ^ 1 +
  C (-3015697796249587/2500000000000000) * X ^ 2 +
  C (1903374555313940637/1250000000000000000) * X ^ 3 +
  C (6401582921755134889/62500000000000000000) * X ^ 4 +
  C (-2107925339418386175807/3125000000000000000000) * X ^ 5 +
  C (26392524978815695479879/31250000000000000000000) * X ^ 6 +
  C (-5289414969008072326466637/3906250000000000000000000) * X ^ 7 +
  C (25472189400411520051226379/97656250000000000000000000) * X ^ 8 +
  C (-31165297145766469289445579/244140625000000000000000000) * X ^ 9 +
  C (11777948990802686139931413/305175781250000000000000000) * X ^ 10 +
  C (20103852089848325076621603/122070312500000000000000000) * X ^ 11 +
  C (21124036836699354417939651/381469726562500000000000000) * X ^ 12

def barrierCase2VTailProductExplicit : ℚ[X] :=
  C (1) +
  C (-527/500) * X ^ 1 +
  C (1750761/1000000) * X ^ 2 +
  C (-909979287/500000000) * X ^ 3 +
  C (-6075541559/12500000000) * X ^ 4 +
  C (71558150879/125000000000) * X ^ 5 +
  C (-67966663885113/31250000000000) * X ^ 6 +
  C (7242405375152601/3125000000000000) * X ^ 7 +
  C (-47227503939133689/78125000000000000) * X ^ 8 +
  C (1167344873752127031/1953125000000000000) * X ^ 9 +
  C (5704562351214682263/9765625000000000000) * X ^ 10 +
  C (-3201700060905414417/4882812500000000000) * X ^ 11 +
  C (7665395189269475619/30517578125000000000) * X ^ 12 +
  C (-5244014001398472729/19073486328125000000) * X ^ 13

theorem barrierCase2VTailNumerator_eq_explicit :
    barrierFractionNumerator (barrierLinearFractions barrierV2RealRows barrierV2PairRows) = barrierCase2VTailNumeratorExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2VTailNumeratorExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

theorem barrierCase2VTailProduct_eq_explicit :
    barrierFractionProduct (barrierLinearFractions barrierV2RealRows barrierV2PairRows) = barrierCase2VTailProductExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2VTailProductExplicit, barrierFractionNumerator, barrierFractionProduct,
    barrierLinearFractions, barrierQuadraticFractions,
    barrierRealLinearQ, barrierRealQuadraticQ,
    barrierPairLinearA, barrierPairLinearQ, barrierPairQuadraticA, barrierPairQuadraticQ,
    barrierP2RealRows, barrierP2PairRows, barrierV2RealRows, barrierV2PairRows,
    eval_list_prod]
  ring

def barrierCase2VTailNumeratorCoefficient (k : ℕ) : ℚ :=
  ([-37299120109/50000000000,
    57077222972893/50000000000000,
    -3015697796249587/2500000000000000,
    1903374555313940637/1250000000000000000,
    6401582921755134889/62500000000000000000,
    -2107925339418386175807/3125000000000000000000,
    26392524978815695479879/31250000000000000000000,
    -5289414969008072326466637/3906250000000000000000000,
    25472189400411520051226379/97656250000000000000000000,
    -31165297145766469289445579/244140625000000000000000000,
    11777948990802686139931413/305175781250000000000000000,
    20103852089848325076621603/122070312500000000000000000,
    21124036836699354417939651/381469726562500000000000000] : List ℚ).getD k 0

private theorem barrierCase2VTailNumeratorExplicit_coeff_00 :
    barrierCase2VTailNumeratorExplicit.coeff 0 = barrierCase2VTailNumeratorCoefficient 0 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero]

private theorem barrierCase2VTailNumeratorExplicit_coeff_01 :
    barrierCase2VTailNumeratorExplicit.coeff 1 = barrierCase2VTailNumeratorCoefficient 1 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_02 :
    barrierCase2VTailNumeratorExplicit.coeff 2 = barrierCase2VTailNumeratorCoefficient 2 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_03 :
    barrierCase2VTailNumeratorExplicit.coeff 3 = barrierCase2VTailNumeratorCoefficient 3 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_04 :
    barrierCase2VTailNumeratorExplicit.coeff 4 = barrierCase2VTailNumeratorCoefficient 4 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_05 :
    barrierCase2VTailNumeratorExplicit.coeff 5 = barrierCase2VTailNumeratorCoefficient 5 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_06 :
    barrierCase2VTailNumeratorExplicit.coeff 6 = barrierCase2VTailNumeratorCoefficient 6 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_07 :
    barrierCase2VTailNumeratorExplicit.coeff 7 = barrierCase2VTailNumeratorCoefficient 7 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_08 :
    barrierCase2VTailNumeratorExplicit.coeff 8 = barrierCase2VTailNumeratorCoefficient 8 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_09 :
    barrierCase2VTailNumeratorExplicit.coeff 9 = barrierCase2VTailNumeratorCoefficient 9 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_10 :
    barrierCase2VTailNumeratorExplicit.coeff 10 = barrierCase2VTailNumeratorCoefficient 10 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_11 :
    barrierCase2VTailNumeratorExplicit.coeff 11 = barrierCase2VTailNumeratorCoefficient 11 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailNumeratorExplicit_coeff_12 :
    barrierCase2VTailNumeratorExplicit.coeff 12 = barrierCase2VTailNumeratorCoefficient 12 := by
  simp only [barrierCase2VTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2VTailNumeratorExplicit_natDegree :
    barrierCase2VTailNumeratorExplicit.natDegree = 12 := by
  unfold barrierCase2VTailNumeratorExplicit
  compute_degree!

theorem barrierCase2VTailNumeratorExplicit_coeff (k : ℕ) :
    barrierCase2VTailNumeratorExplicit.coeff k = barrierCase2VTailNumeratorCoefficient k := by
  by_cases hk : k < 13
  · interval_cases k
    · exact barrierCase2VTailNumeratorExplicit_coeff_00
    · exact barrierCase2VTailNumeratorExplicit_coeff_01
    · exact barrierCase2VTailNumeratorExplicit_coeff_02
    · exact barrierCase2VTailNumeratorExplicit_coeff_03
    · exact barrierCase2VTailNumeratorExplicit_coeff_04
    · exact barrierCase2VTailNumeratorExplicit_coeff_05
    · exact barrierCase2VTailNumeratorExplicit_coeff_06
    · exact barrierCase2VTailNumeratorExplicit_coeff_07
    · exact barrierCase2VTailNumeratorExplicit_coeff_08
    · exact barrierCase2VTailNumeratorExplicit_coeff_09
    · exact barrierCase2VTailNumeratorExplicit_coeff_10
    · exact barrierCase2VTailNumeratorExplicit_coeff_11
    · exact barrierCase2VTailNumeratorExplicit_coeff_12
  · have hlen : 13 ≤ k := Nat.le_of_not_gt hk
    have hlookup : barrierCase2VTailNumeratorCoefficient k = 0 := by
      unfold barrierCase2VTailNumeratorCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using hlen
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2VTailNumeratorExplicit_natDegree]
    exact lt_of_lt_of_le (by decide : 12 < 13) hlen

def barrierCase2VTailProductCoefficient (k : ℕ) : ℚ :=
  ([1,
    -527/500,
    1750761/1000000,
    -909979287/500000000,
    -6075541559/12500000000,
    71558150879/125000000000,
    -67966663885113/31250000000000,
    7242405375152601/3125000000000000,
    -47227503939133689/78125000000000000,
    1167344873752127031/1953125000000000000,
    5704562351214682263/9765625000000000000,
    -3201700060905414417/4882812500000000000,
    7665395189269475619/30517578125000000000,
    -5244014001398472729/19073486328125000000] : List ℚ).getD k 0

private theorem barrierCase2VTailProductExplicit_coeff_00 :
    barrierCase2VTailProductExplicit.coeff 0 = barrierCase2VTailProductCoefficient 0 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero]

private theorem barrierCase2VTailProductExplicit_coeff_01 :
    barrierCase2VTailProductExplicit.coeff 1 = barrierCase2VTailProductCoefficient 1 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_02 :
    barrierCase2VTailProductExplicit.coeff 2 = barrierCase2VTailProductCoefficient 2 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_03 :
    barrierCase2VTailProductExplicit.coeff 3 = barrierCase2VTailProductCoefficient 3 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_04 :
    barrierCase2VTailProductExplicit.coeff 4 = barrierCase2VTailProductCoefficient 4 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_05 :
    barrierCase2VTailProductExplicit.coeff 5 = barrierCase2VTailProductCoefficient 5 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_06 :
    barrierCase2VTailProductExplicit.coeff 6 = barrierCase2VTailProductCoefficient 6 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_07 :
    barrierCase2VTailProductExplicit.coeff 7 = barrierCase2VTailProductCoefficient 7 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_08 :
    barrierCase2VTailProductExplicit.coeff 8 = barrierCase2VTailProductCoefficient 8 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_09 :
    barrierCase2VTailProductExplicit.coeff 9 = barrierCase2VTailProductCoefficient 9 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_10 :
    barrierCase2VTailProductExplicit.coeff 10 = barrierCase2VTailProductCoefficient 10 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_11 :
    barrierCase2VTailProductExplicit.coeff 11 = barrierCase2VTailProductCoefficient 11 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_12 :
    barrierCase2VTailProductExplicit.coeff 12 = barrierCase2VTailProductCoefficient 12 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2VTailProductExplicit_coeff_13 :
    barrierCase2VTailProductExplicit.coeff 13 = barrierCase2VTailProductCoefficient 13 := by
  simp only [barrierCase2VTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2VTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2VTailProductExplicit_natDegree :
    barrierCase2VTailProductExplicit.natDegree = 13 := by
  unfold barrierCase2VTailProductExplicit
  compute_degree!

theorem barrierCase2VTailProductExplicit_coeff (k : ℕ) :
    barrierCase2VTailProductExplicit.coeff k = barrierCase2VTailProductCoefficient k := by
  by_cases hk : k < 14
  · interval_cases k
    · exact barrierCase2VTailProductExplicit_coeff_00
    · exact barrierCase2VTailProductExplicit_coeff_01
    · exact barrierCase2VTailProductExplicit_coeff_02
    · exact barrierCase2VTailProductExplicit_coeff_03
    · exact barrierCase2VTailProductExplicit_coeff_04
    · exact barrierCase2VTailProductExplicit_coeff_05
    · exact barrierCase2VTailProductExplicit_coeff_06
    · exact barrierCase2VTailProductExplicit_coeff_07
    · exact barrierCase2VTailProductExplicit_coeff_08
    · exact barrierCase2VTailProductExplicit_coeff_09
    · exact barrierCase2VTailProductExplicit_coeff_10
    · exact barrierCase2VTailProductExplicit_coeff_11
    · exact barrierCase2VTailProductExplicit_coeff_12
    · exact barrierCase2VTailProductExplicit_coeff_13
  · have hlen : 14 ≤ k := Nat.le_of_not_gt hk
    have hlookup : barrierCase2VTailProductCoefficient k = 0 := by
      unfold barrierCase2VTailProductCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using hlen
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2VTailProductExplicit_natDegree]
    exact lt_of_lt_of_le (by decide : 13 < 14) hlen

def barrierCase2XBaseFractions : List (ℚ[X] × ℚ[X]) :=
  [(C (19 / 48), X), (-C (1 / 12), 1 - X), (-C (65 / 24) * X, 1 + X ^ 2),
   (-(C 4 * barrierFiniteUDerivative barrierP2Finite +
       barrierFinitePowerDerivative barrierV2Finite), 1)]

def barrierCase2XBaseNumeratorExplicit : ℚ[X] :=
  C (19/48) +
  C (-385043839/150000000) * X ^ 1 +
  C (372377653/50000000) * X ^ 2 +
  C (-189294451/75000000) * X ^ 3 +
  C (-1151057621/100000000) * X ^ 4 +
  C (108894531/50000000) * X ^ 5 +
  C (300309089/20000000) * X ^ 6 +
  C (-129850079/20000000) * X ^ 7 +
  C (4681561/2500000) * X ^ 8 +
  C (264361599/100000000) * X ^ 9 +
  C (-510055997/25000000) * X ^ 10 +
  C (6872329/1000000) * X ^ 11 +
  C (175140243/12500000) * X ^ 12 +
  C (-355349099/50000000) * X ^ 13

def barrierCase2XBaseProductExplicit : ℚ[X] :=
  C (0) +
  C (1) * X ^ 1 +
  C (-1) * X ^ 2 +
  C (1) * X ^ 3 +
  C (-1) * X ^ 4

private theorem barrier_case2_U_3 :
    Chebyshev.U ℚ 3 = 2 * X * Chebyshev.U ℚ 2 - Chebyshev.U ℚ 1 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 1

private theorem barrier_case2_U_4 :
    Chebyshev.U ℚ 4 = 2 * X * Chebyshev.U ℚ 3 - Chebyshev.U ℚ 2 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 2

private theorem barrier_case2_U_5 :
    Chebyshev.U ℚ 5 = 2 * X * Chebyshev.U ℚ 4 - Chebyshev.U ℚ 3 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 3

private theorem barrier_case2_U_6 :
    Chebyshev.U ℚ 6 = 2 * X * Chebyshev.U ℚ 5 - Chebyshev.U ℚ 4 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 4

private theorem barrier_case2_U_7 :
    Chebyshev.U ℚ 7 = 2 * X * Chebyshev.U ℚ 6 - Chebyshev.U ℚ 5 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 5

private theorem barrier_case2_U_8 :
    Chebyshev.U ℚ 8 = 2 * X * Chebyshev.U ℚ 7 - Chebyshev.U ℚ 6 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 6

private theorem barrier_case2_U_9 :
    Chebyshev.U ℚ 9 = 2 * X * Chebyshev.U ℚ 8 - Chebyshev.U ℚ 7 := by
  simpa only [Int.reduceAdd] using Chebyshev.U_add_two ℚ 7

theorem barrierCase2XBaseNumerator_eq_explicit :
    barrierFractionNumerator barrierCase2XBaseFractions =
      barrierCase2XBaseNumeratorExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2XBaseFractions, barrierCase2XBaseNumeratorExplicit,
    barrierFractionNumerator, barrierFractionProduct, barrierFiniteUDerivative,
    barrierFinitePowerDerivative, barrierP2Finite, barrierV2Finite,
    Finset.sum_range_succ, eval_finsetSum, eval_list_prod,
    Chebyshev.U_two, barrier_case2_U_3, barrier_case2_U_4,
    barrier_case2_U_5, barrier_case2_U_6, barrier_case2_U_7,
    barrier_case2_U_8, barrier_case2_U_9]
  ring

theorem barrierCase2XBaseProduct_eq_explicit :
    barrierFractionProduct barrierCase2XBaseFractions =
      barrierCase2XBaseProductExplicit := by
  apply Polynomial.funext
  intro x
  norm_num [barrierCase2XBaseFractions, barrierCase2XBaseProductExplicit,
    barrierFractionProduct, eval_list_prod]
  ring

theorem barrierCase2AX_eq_factored :
    barrierCase2AX =
      barrierCase2XBaseNumeratorExplicit * barrierCase2PTailProductExplicit *
          barrierCase2VTailProductExplicit -
        C 4 * barrierCase2XBaseProductExplicit * barrierCase2PTailNumeratorExplicit *
          barrierCase2VTailProductExplicit -
        barrierCase2XBaseProductExplicit * barrierCase2PTailProductExplicit *
          barrierCase2VTailNumeratorExplicit := by
  unfold barrierCase2AX
  change barrierFractionNumerator
    (barrierCase2XBaseFractions ++
      barrierScaleFractions (-4)
        (barrierQuadraticFractions barrierP2RealRows barrierP2PairRows) ++
      barrierScaleFractions (-1)
        (barrierLinearFractions barrierV2RealRows barrierV2PairRows)) = _
  simp only [barrierFractionNumerator_append_exact, barrierFractionProduct_append_exact,
    barrierFractionNumerator_scale_exact, barrierFractionProduct_scale_exact,
    barrierCase2XBaseNumerator_eq_explicit, barrierCase2XBaseProduct_eq_explicit,
    barrierCase2PTailNumerator_eq_explicit, barrierCase2PTailProduct_eq_explicit,
    barrierCase2VTailNumerator_eq_explicit, barrierCase2VTailProduct_eq_explicit,
    map_neg, map_ofNat, map_one]
  ring

def barrierCase2XBaseNumeratorCoefficient (k : ℕ) : ℚ :=
  ([19/48, -385043839/150000000, 372377653/50000000, -189294451/75000000, -1151057621/100000000, 108894531/50000000, 300309089/20000000, -129850079/20000000, 4681561/2500000, 264361599/100000000, -510055997/25000000, 6872329/1000000, 175140243/12500000, -355349099/50000000] : List ℚ).getD k 0

def barrierCase2XBaseProductCoefficient (k : ℕ) : ℚ :=
  ([0, 1, -1, 1, -1] : List ℚ).getD k 0

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
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXTailCoefficientsP
namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial

def barrierCase2PTailNumeratorCoefficient (k : ℕ) : ℚ :=
  ([-334625418567286147906955121183793659/4882812500000000000000000000000000000000,
    20127644970984429229663641286102109817/12207031250000000000000000000000000000000,
    -2852876572408096311386663148074363127/610351562500000000000000000000000000000,
    219782662978769686811412440485306881/3051757812500000000000000000000000000,
    -4894248692719660966896600643752953/19073486328125000000000000000000000,
    45491985122617474473894836809089153/15258789062500000000000000000000000,
    -568781315379457100097709309340883/30517578125000000000000000000000,
    803074381853681639161748844303/7629394531250000000000000000,
    -5453962494228714418500320647/30517578125000000000000000,
    680879861223820138383153/7629394531250000000000] : List ℚ).getD k 0

private theorem barrierCase2PTailNumeratorExplicit_coeff_0 :
    barrierCase2PTailNumeratorExplicit.coeff 0 = barrierCase2PTailNumeratorCoefficient 0 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero]

private theorem barrierCase2PTailNumeratorExplicit_coeff_1 :
    barrierCase2PTailNumeratorExplicit.coeff 1 = barrierCase2PTailNumeratorCoefficient 1 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_2 :
    barrierCase2PTailNumeratorExplicit.coeff 2 = barrierCase2PTailNumeratorCoefficient 2 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_3 :
    barrierCase2PTailNumeratorExplicit.coeff 3 = barrierCase2PTailNumeratorCoefficient 3 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_4 :
    barrierCase2PTailNumeratorExplicit.coeff 4 = barrierCase2PTailNumeratorCoefficient 4 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_5 :
    barrierCase2PTailNumeratorExplicit.coeff 5 = barrierCase2PTailNumeratorCoefficient 5 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_6 :
    barrierCase2PTailNumeratorExplicit.coeff 6 = barrierCase2PTailNumeratorCoefficient 6 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_7 :
    barrierCase2PTailNumeratorExplicit.coeff 7 = barrierCase2PTailNumeratorCoefficient 7 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_8 :
    barrierCase2PTailNumeratorExplicit.coeff 8 = barrierCase2PTailNumeratorCoefficient 8 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailNumeratorExplicit_coeff_9 :
    barrierCase2PTailNumeratorExplicit.coeff 9 = barrierCase2PTailNumeratorCoefficient 9 := by
  simp only [barrierCase2PTailNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2PTailNumeratorExplicit_natDegree :
    barrierCase2PTailNumeratorExplicit.natDegree = 9 := by
  unfold barrierCase2PTailNumeratorExplicit
  compute_degree!

theorem barrierCase2PTailNumeratorExplicit_coeff (k : ℕ) :
    barrierCase2PTailNumeratorExplicit.coeff k = barrierCase2PTailNumeratorCoefficient k := by
  by_cases hk : k < 10
  · interval_cases k
    · exact barrierCase2PTailNumeratorExplicit_coeff_0
    · exact barrierCase2PTailNumeratorExplicit_coeff_1
    · exact barrierCase2PTailNumeratorExplicit_coeff_2
    · exact barrierCase2PTailNumeratorExplicit_coeff_3
    · exact barrierCase2PTailNumeratorExplicit_coeff_4
    · exact barrierCase2PTailNumeratorExplicit_coeff_5
    · exact barrierCase2PTailNumeratorExplicit_coeff_6
    · exact barrierCase2PTailNumeratorExplicit_coeff_7
    · exact barrierCase2PTailNumeratorExplicit_coeff_8
    · exact barrierCase2PTailNumeratorExplicit_coeff_9
  · have hlookup : barrierCase2PTailNumeratorCoefficient k = 0 := by
      unfold barrierCase2PTailNumeratorCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2PTailNumeratorExplicit_natDegree]
    omega

def barrierCase2PTailProductCoefficient (k : ℕ) : ℚ :=
  ([4785447983749937204061879244701/24414062500000000000000000000000000,
    -474962018866734369442083826221/1220703125000000000000000000000000,
    7705227818365150047259368501/2441406250000000000000000000000,
    -3589839094005450574517959947/610351562500000000000000000000,
    84481480701896139333127067089/152587890625000000000000000000,
    -8340696096348800303572388719/7629394531250000000000000000,
    2527238180877059028537517647/76293945312500000000000000,
    -1973789704813765919735753/30517578125000000000000,
    37686962338137420137757/152587890625000000000,
    -13017638552052412621/30517578125000000,
    32299425202362199/152587890625000] : List ℚ).getD k 0

private theorem barrierCase2PTailProductExplicit_coeff_0 :
    barrierCase2PTailProductExplicit.coeff 0 = barrierCase2PTailProductCoefficient 0 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero]

private theorem barrierCase2PTailProductExplicit_coeff_1 :
    barrierCase2PTailProductExplicit.coeff 1 = barrierCase2PTailProductCoefficient 1 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_2 :
    barrierCase2PTailProductExplicit.coeff 2 = barrierCase2PTailProductCoefficient 2 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_3 :
    barrierCase2PTailProductExplicit.coeff 3 = barrierCase2PTailProductCoefficient 3 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_4 :
    barrierCase2PTailProductExplicit.coeff 4 = barrierCase2PTailProductCoefficient 4 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_5 :
    barrierCase2PTailProductExplicit.coeff 5 = barrierCase2PTailProductCoefficient 5 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_6 :
    barrierCase2PTailProductExplicit.coeff 6 = barrierCase2PTailProductCoefficient 6 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_7 :
    barrierCase2PTailProductExplicit.coeff 7 = barrierCase2PTailProductCoefficient 7 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_8 :
    barrierCase2PTailProductExplicit.coeff 8 = barrierCase2PTailProductCoefficient 8 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_9 :
    barrierCase2PTailProductExplicit.coeff 9 = barrierCase2PTailProductCoefficient 9 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

private theorem barrierCase2PTailProductExplicit_coeff_10 :
    barrierCase2PTailProductExplicit.coeff 10 = barrierCase2PTailProductCoefficient 10 := by
  simp only [barrierCase2PTailProductExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2PTailProductCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2PTailProductExplicit_natDegree :
    barrierCase2PTailProductExplicit.natDegree = 10 := by
  unfold barrierCase2PTailProductExplicit
  compute_degree!

theorem barrierCase2PTailProductExplicit_coeff (k : ℕ) :
    barrierCase2PTailProductExplicit.coeff k = barrierCase2PTailProductCoefficient k := by
  by_cases hk : k < 11
  · interval_cases k
    · exact barrierCase2PTailProductExplicit_coeff_0
    · exact barrierCase2PTailProductExplicit_coeff_1
    · exact barrierCase2PTailProductExplicit_coeff_2
    · exact barrierCase2PTailProductExplicit_coeff_3
    · exact barrierCase2PTailProductExplicit_coeff_4
    · exact barrierCase2PTailProductExplicit_coeff_5
    · exact barrierCase2PTailProductExplicit_coeff_6
    · exact barrierCase2PTailProductExplicit_coeff_7
    · exact barrierCase2PTailProductExplicit_coeff_8
    · exact barrierCase2PTailProductExplicit_coeff_9
    · exact barrierCase2PTailProductExplicit_coeff_10
  · have hlookup : barrierCase2PTailProductCoefficient k = 0 := by
      unfold barrierCase2PTailProductCoefficient
      apply List.getD_eq_default
      simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)
    rw [hlookup]
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2PTailProductExplicit_natDegree]
    omega

end InternalCatalan

end

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXConvolutionGroup6
namespace OAI

namespace InternalCatalan

section
open Polynomial

theorem barrierCase2XBaseNumeratorExplicit_coeff_0 :
    barrierCase2XBaseNumeratorExplicit.coeff 0 = barrierCase2XBaseNumeratorCoefficient 0 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero]

theorem barrierCase2XBaseNumeratorExplicit_coeff_1 :
    barrierCase2XBaseNumeratorExplicit.coeff 1 = barrierCase2XBaseNumeratorCoefficient 1 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_2 :
    barrierCase2XBaseNumeratorExplicit.coeff 2 = barrierCase2XBaseNumeratorCoefficient 2 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_3 :
    barrierCase2XBaseNumeratorExplicit.coeff 3 = barrierCase2XBaseNumeratorCoefficient 3 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_4 :
    barrierCase2XBaseNumeratorExplicit.coeff 4 = barrierCase2XBaseNumeratorCoefficient 4 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_5 :
    barrierCase2XBaseNumeratorExplicit.coeff 5 = barrierCase2XBaseNumeratorCoefficient 5 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_6 :
    barrierCase2XBaseNumeratorExplicit.coeff 6 = barrierCase2XBaseNumeratorCoefficient 6 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_7 :
    barrierCase2XBaseNumeratorExplicit.coeff 7 = barrierCase2XBaseNumeratorCoefficient 7 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_8 :
    barrierCase2XBaseNumeratorExplicit.coeff 8 = barrierCase2XBaseNumeratorCoefficient 8 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_9 :
    barrierCase2XBaseNumeratorExplicit.coeff 9 = barrierCase2XBaseNumeratorCoefficient 9 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_10 :
    barrierCase2XBaseNumeratorExplicit.coeff 10 = barrierCase2XBaseNumeratorCoefficient 10 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_11 :
    barrierCase2XBaseNumeratorExplicit.coeff 11 = barrierCase2XBaseNumeratorCoefficient 11 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_12 :
    barrierCase2XBaseNumeratorExplicit.coeff 12 = barrierCase2XBaseNumeratorCoefficient 12 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseNumeratorExplicit_coeff_13 :
    barrierCase2XBaseNumeratorExplicit.coeff 13 = barrierCase2XBaseNumeratorCoefficient 13 := by
  simp only [barrierCase2XBaseNumeratorExplicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2XBaseNumeratorCoefficient, List.getD_cons_zero, List.getD_cons_succ]

theorem barrierCase2XBaseProductExplicit_coeff_0 :
    barrierCase2XBaseProductExplicit.coeff 0 = barrierCase2XBaseProductCoefficient 0 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_1 :
    barrierCase2XBaseProductExplicit.coeff 1 = barrierCase2XBaseProductCoefficient 1 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_2 :
    barrierCase2XBaseProductExplicit.coeff 2 = barrierCase2XBaseProductCoefficient 2 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_3 :
    barrierCase2XBaseProductExplicit.coeff 3 = barrierCase2XBaseProductCoefficient 3 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseProductExplicit_coeff_4 :
    barrierCase2XBaseProductExplicit.coeff 4 = barrierCase2XBaseProductCoefficient 4 := by
  norm_num [barrierCase2XBaseProductExplicit, barrierCase2XBaseProductCoefficient, coeff_C_mul, coeff_X_pow, coeff_X]

theorem barrierCase2XBaseNumeratorExplicit_natDegree : barrierCase2XBaseNumeratorExplicit.natDegree = 13 := by
  unfold barrierCase2XBaseNumeratorExplicit
  compute_degree!

theorem barrierCase2XBaseNumeratorExplicit_coeff (k : ℕ) :
    barrierCase2XBaseNumeratorExplicit.coeff k = barrierCase2XBaseNumeratorCoefficient k := by
  by_cases hk : k < 14
  · interval_cases k
    · exact barrierCase2XBaseNumeratorExplicit_coeff_0
    · exact barrierCase2XBaseNumeratorExplicit_coeff_1
    · exact barrierCase2XBaseNumeratorExplicit_coeff_2
    · exact barrierCase2XBaseNumeratorExplicit_coeff_3
    · exact barrierCase2XBaseNumeratorExplicit_coeff_4
    · exact barrierCase2XBaseNumeratorExplicit_coeff_5
    · exact barrierCase2XBaseNumeratorExplicit_coeff_6
    · exact barrierCase2XBaseNumeratorExplicit_coeff_7
    · exact barrierCase2XBaseNumeratorExplicit_coeff_8
    · exact barrierCase2XBaseNumeratorExplicit_coeff_9
    · exact barrierCase2XBaseNumeratorExplicit_coeff_10
    · exact barrierCase2XBaseNumeratorExplicit_coeff_11
    · exact barrierCase2XBaseNumeratorExplicit_coeff_12
    · exact barrierCase2XBaseNumeratorExplicit_coeff_13
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [barrierCase2XBaseNumeratorExplicit_natDegree]; omega)]
    unfold barrierCase2XBaseNumeratorCoefficient
    symm
    apply List.getD_eq_default
    simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)

theorem barrierCase2XBaseProductExplicit_natDegree : barrierCase2XBaseProductExplicit.natDegree = 4 := by
  unfold barrierCase2XBaseProductExplicit
  compute_degree!

theorem barrierCase2XBaseProductExplicit_coeff (k : ℕ) :
    barrierCase2XBaseProductExplicit.coeff k = barrierCase2XBaseProductCoefficient k := by
  by_cases hk : k < 5
  · interval_cases k
    · exact barrierCase2XBaseProductExplicit_coeff_0
    · exact barrierCase2XBaseProductExplicit_coeff_1
    · exact barrierCase2XBaseProductExplicit_coeff_2
    · exact barrierCase2XBaseProductExplicit_coeff_3
    · exact barrierCase2XBaseProductExplicit_coeff_4
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [barrierCase2XBaseProductExplicit_natDegree]; omega)]
    unfold barrierCase2XBaseProductCoefficient
    symm
    apply List.getD_eq_default
    simpa only [List.length_cons, List.length_nil] using (Nat.le_of_not_gt hk)

end

noncomputable section
open Polynomial

def barrierCase2AXComputedCoefficient (k : ℕ) : ℚ :=
  barrierCoeffConv
      (barrierCoeffConv barrierCase2XBaseNumeratorCoefficient
        barrierCase2PTailProductCoefficient) barrierCase2VTailProductCoefficient k -
    barrierCoeffConv
      (barrierCoeffConv (fun i => 4 * barrierCase2XBaseProductCoefficient i)
        barrierCase2PTailNumeratorCoefficient) barrierCase2VTailProductCoefficient k -
    barrierCoeffConv
      (barrierCoeffConv barrierCase2XBaseProductCoefficient
        barrierCase2PTailProductCoefficient) barrierCase2VTailNumeratorCoefficient k

end

theorem barrierCase2AX_computed_coeff_0 :
    barrierCase2AXComputedCoefficient 0 = barrierCase2AXCoefficient 0 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_1 :
    barrierCase2AXComputedCoefficient 1 = barrierCase2AXCoefficient 1 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_2 :
    barrierCase2AXComputedCoefficient 2 = barrierCase2AXCoefficient 2 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_3 :
    barrierCase2AXComputedCoefficient 3 = barrierCase2AXCoefficient 3 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_4 :
    barrierCase2AXComputedCoefficient 4 = barrierCase2AXCoefficient 4 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_5 :
    barrierCase2AXComputedCoefficient 5 = barrierCase2AXCoefficient 5 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_6 :
    barrierCase2AXComputedCoefficient 6 = barrierCase2AXCoefficient 6 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_7 :
    barrierCase2AXComputedCoefficient 7 = barrierCase2AXCoefficient 7 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_8 :
    barrierCase2AXComputedCoefficient 8 = barrierCase2AXCoefficient 8 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_9 :
    barrierCase2AXComputedCoefficient 9 = barrierCase2AXCoefficient 9 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_10 :
    barrierCase2AXComputedCoefficient 10 = barrierCase2AXCoefficient 10 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_11 :
    barrierCase2AXComputedCoefficient 11 = barrierCase2AXCoefficient 11 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_12 :
    barrierCase2AXComputedCoefficient 12 = barrierCase2AXCoefficient 12 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_13 :
    barrierCase2AXComputedCoefficient 13 = barrierCase2AXCoefficient 13 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_14 :
    barrierCase2AXComputedCoefficient 14 = barrierCase2AXCoefficient 14 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_15 :
    barrierCase2AXComputedCoefficient 15 = barrierCase2AXCoefficient 15 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_16 :
    barrierCase2AXComputedCoefficient 16 = barrierCase2AXCoefficient 16 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_17 :
    barrierCase2AXComputedCoefficient 17 = barrierCase2AXCoefficient 17 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_18 :
    barrierCase2AXComputedCoefficient 18 = barrierCase2AXCoefficient 18 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_19 :
    barrierCase2AXComputedCoefficient 19 = barrierCase2AXCoefficient 19 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_20 :
    barrierCase2AXComputedCoefficient 20 = barrierCase2AXCoefficient 20 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_21 :
    barrierCase2AXComputedCoefficient 21 = barrierCase2AXCoefficient 21 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_22 :
    barrierCase2AXComputedCoefficient 22 = barrierCase2AXCoefficient 22 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_23 :
    barrierCase2AXComputedCoefficient 23 = barrierCase2AXCoefficient 23 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_24 :
    barrierCase2AXComputedCoefficient 24 = barrierCase2AXCoefficient 24 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_25 :
    barrierCase2AXComputedCoefficient 25 = barrierCase2AXCoefficient 25 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_26 :
    barrierCase2AXComputedCoefficient 26 = barrierCase2AXCoefficient 26 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_27 :
    barrierCase2AXComputedCoefficient 27 = barrierCase2AXCoefficient 27 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_28 :
    barrierCase2AXComputedCoefficient 28 = barrierCase2AXCoefficient 28 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_29 :
    barrierCase2AXComputedCoefficient 29 = barrierCase2AXCoefficient 29 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_30 :
    barrierCase2AXComputedCoefficient 30 = barrierCase2AXCoefficient 30 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_31 :
    barrierCase2AXComputedCoefficient 31 = barrierCase2AXCoefficient 31 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_32 :
    barrierCase2AXComputedCoefficient 32 = barrierCase2AXCoefficient 32 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_33 :
    barrierCase2AXComputedCoefficient 33 = barrierCase2AXCoefficient 33 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_34 :
    barrierCase2AXComputedCoefficient 34 = barrierCase2AXCoefficient 34 := by
  decide +kernel

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoBracketYGroup0
namespace OAI

namespace InternalCatalan

section

theorem barrierCase2AX_computed_coeff_35 :
    barrierCase2AXComputedCoefficient 35 = barrierCase2AXCoefficient 35 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_36 :
    barrierCase2AXComputedCoefficient 36 = barrierCase2AXCoefficient 36 := by
  decide +kernel

theorem barrierCase2AX_computed_coeff_small (k : ℕ) (hk : k < 37) :
    barrierCase2AXComputedCoefficient k = barrierCase2AXCoefficient k := by
  interval_cases k
  · exact barrierCase2AX_computed_coeff_0
  · exact barrierCase2AX_computed_coeff_1
  · exact barrierCase2AX_computed_coeff_2
  · exact barrierCase2AX_computed_coeff_3
  · exact barrierCase2AX_computed_coeff_4
  · exact barrierCase2AX_computed_coeff_5
  · exact barrierCase2AX_computed_coeff_6
  · exact barrierCase2AX_computed_coeff_7
  · exact barrierCase2AX_computed_coeff_8
  · exact barrierCase2AX_computed_coeff_9
  · exact barrierCase2AX_computed_coeff_10
  · exact barrierCase2AX_computed_coeff_11
  · exact barrierCase2AX_computed_coeff_12
  · exact barrierCase2AX_computed_coeff_13
  · exact barrierCase2AX_computed_coeff_14
  · exact barrierCase2AX_computed_coeff_15
  · exact barrierCase2AX_computed_coeff_16
  · exact barrierCase2AX_computed_coeff_17
  · exact barrierCase2AX_computed_coeff_18
  · exact barrierCase2AX_computed_coeff_19
  · exact barrierCase2AX_computed_coeff_20
  · exact barrierCase2AX_computed_coeff_21
  · exact barrierCase2AX_computed_coeff_22
  · exact barrierCase2AX_computed_coeff_23
  · exact barrierCase2AX_computed_coeff_24
  · exact barrierCase2AX_computed_coeff_25
  · exact barrierCase2AX_computed_coeff_26
  · exact barrierCase2AX_computed_coeff_27
  · exact barrierCase2AX_computed_coeff_28
  · exact barrierCase2AX_computed_coeff_29
  · exact barrierCase2AX_computed_coeff_30
  · exact barrierCase2AX_computed_coeff_31
  · exact barrierCase2AX_computed_coeff_32
  · exact barrierCase2AX_computed_coeff_33
  · exact barrierCase2AX_computed_coeff_34
  · exact barrierCase2AX_computed_coeff_35
  · exact barrierCase2AX_computed_coeff_36

open Polynomial

private theorem barrierCase2AX_coeff_computed (k : ℕ) :
    barrierCase2AX.coeff k = barrierCase2AXComputedCoefficient k := by
  have hs : ∀ j : ℕ,
      (C (4 : ℚ) * barrierCase2XBaseProductExplicit).coeff j =
        4 * barrierCase2XBaseProductCoefficient j := by
    intro j
    rw [coeff_C_mul, barrierCase2XBaseProductExplicit_coeff]
  have h1 := barrier_coeff_mul_eq_conv
    (barrierCase2XBaseNumeratorExplicit * barrierCase2PTailProductExplicit)
    barrierCase2VTailProductExplicit _ _
    (fun j => barrier_coeff_mul_eq_conv _ _ _ _
      barrierCase2XBaseNumeratorExplicit_coeff barrierCase2PTailProductExplicit_coeff j)
    barrierCase2VTailProductExplicit_coeff k
  have h2 := barrier_coeff_mul_eq_conv
    (C (4 : ℚ) * barrierCase2XBaseProductExplicit * barrierCase2PTailNumeratorExplicit)
    barrierCase2VTailProductExplicit _ _
    (fun j => barrier_coeff_mul_eq_conv _ _ _ _ hs
      barrierCase2PTailNumeratorExplicit_coeff j)
    barrierCase2VTailProductExplicit_coeff k
  have h3 := barrier_coeff_mul_eq_conv
    (barrierCase2XBaseProductExplicit * barrierCase2PTailProductExplicit)
    barrierCase2VTailNumeratorExplicit _ _
    (fun j => barrier_coeff_mul_eq_conv _ _ _ _
      barrierCase2XBaseProductExplicit_coeff barrierCase2PTailProductExplicit_coeff j)
    barrierCase2VTailNumeratorExplicit_coeff k
  rw [barrierCase2AX_eq_factored, coeff_sub, coeff_sub, h1, h2, h3]
  rfl

private theorem barrierCase2AX_natDegree_le : barrierCase2AX.natDegree ≤ 36 := by
  have hn : barrierCase2XBaseNumeratorExplicit.natDegree ≤ 13 :=
    le_of_eq barrierCase2XBaseNumeratorExplicit_natDegree
  have hq : barrierCase2XBaseProductExplicit.natDegree ≤ 4 :=
    le_of_eq barrierCase2XBaseProductExplicit_natDegree
  have hpn : barrierCase2PTailNumeratorExplicit.natDegree ≤ 9 :=
    le_of_eq barrierCase2PTailNumeratorExplicit_natDegree
  have hpq : barrierCase2PTailProductExplicit.natDegree ≤ 10 :=
    le_of_eq barrierCase2PTailProductExplicit_natDegree
  have hvn : barrierCase2VTailNumeratorExplicit.natDegree ≤ 12 :=
    le_of_eq barrierCase2VTailNumeratorExplicit_natDegree
  have hvq : barrierCase2VTailProductExplicit.natDegree ≤ 13 :=
    le_of_eq barrierCase2VTailProductExplicit_natDegree
  have hc : (C (4 : ℚ)).natDegree ≤ 0 := by simp
  have h1 : (barrierCase2XBaseNumeratorExplicit * barrierCase2PTailProductExplicit *
      barrierCase2VTailProductExplicit).natDegree ≤ 36 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le hn hpq) hvq
  have h2 : (C (4 : ℚ) * barrierCase2XBaseProductExplicit *
      barrierCase2PTailNumeratorExplicit * barrierCase2VTailProductExplicit).natDegree ≤ 26 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_mul_le_of_le hc hq) hpn) hvq
  have h3 : (barrierCase2XBaseProductExplicit * barrierCase2PTailProductExplicit *
      barrierCase2VTailNumeratorExplicit).natDegree ≤ 26 :=
    natDegree_mul_le_of_le (natDegree_mul_le_of_le hq hpq) hvn
  rw [barrierCase2AX_eq_factored]
  refine (natDegree_sub_le _ _).trans (max_le ?_ (h3.trans (by omega)))
  exact (natDegree_sub_le _ _).trans (max_le h1 (h2.trans (by omega)))

theorem barrierCase2AX_eq_explicit : barrierCase2AX = barrierCase2AXExplicit := by
  apply Polynomial.ext
  intro k
  by_cases hk : k < 37
  · rw [barrierCase2AX_coeff_computed, barrierCase2AX_computed_coeff_small k hk,
      barrierCase2AXExplicit_coeff]
  · have hl : barrierCase2AX.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by
        have h := barrierCase2AX_natDegree_le
        omega)
    have hr : barrierCase2AXExplicit.coeff k = 0 :=
      coeff_eq_zero_of_natDegree_lt (by rw [barrierCase2AXExplicit_natDegree]; omega)
    exact hl.trans hr.symm


end
section


end

noncomputable section

open Polynomial
open scoped BigOperators





end

section
open Polynomial







end























end InternalCatalan

end OAI

end

section
open OAI.InternalCatalan
open Polynomial

theorem solution : barrierCase2AX = barrierCase2AXExplicit := by
  first
  | exact @OAI.InternalCatalan.barrierCase2AX_eq_explicit
  | (apply OAI.InternalCatalan.barrierCase2AX_eq_explicit <;> assumption)

end
