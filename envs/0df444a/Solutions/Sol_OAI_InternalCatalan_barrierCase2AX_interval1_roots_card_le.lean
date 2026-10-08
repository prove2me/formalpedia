-- Prove2me | solution 1 for OAI.InternalCatalan.barrierCase2AX_interval1_roots_card_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T20:52:56.366983+00:00
-- url     : https://prove2.me/submissions/214bfc16-d08a-42b2-ac3d-b7ec6db8d18c

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

section
-- module Solutions.OAICatalan.Catalan.Energy.BarrierDescartesCoefficientDegree
namespace OAI

noncomputable section

namespace InternalCatalan

section

open Polynomial
open scoped BigOperators

def barrierDescartesTransform {R : Type*} [CommRing R] (p : R[X])
    (d : ℕ) (a b : R) : R[X] :=
  ∑ k ∈ Finset.range (d + 1),
    C (p.coeff k) * (C a + C b * X) ^ k * (1 + X) ^ (d - k)

theorem barrierDescartesTransform_eval {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t =
      (1 + t) ^ d * p.eval ((a + b * t) / (1 + t)) := by
  unfold barrierDescartesTransform
  rw [eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkd : k ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : (1 + t) ^ (d - k) = (1 + t) ^ d / (1 + t) ^ k := by
    apply (eq_div_iff (pow_ne_zero k ht)).2
    rw [← pow_add, Nat.sub_add_cancel hkd]
  simp only [eval_mul, eval_C, eval_pow, eval_add, eval_X, eval_one]
  rw [hp, div_pow]
  ring

theorem barrierDescartesTransform_eval_eq_zero_iff {R : Type*} [Field R] (p : R[X])
    (d : ℕ) (a b t : R) (hd : p.natDegree ≤ d) (ht : 1 + t ≠ 0) :
    (barrierDescartesTransform p d a b).eval t = 0 ↔
      p.eval ((a + b * t) / (1 + t)) = 0 := by
  rw [barrierDescartesTransform_eval p d a b t hd ht]
  simp [pow_ne_zero d ht]

theorem barrierMobius_inverse {a b x : ℝ} (hx : x ∈ Set.Ioo a b) :
    0 < (x - a) / (b - x) ∧
      (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) = x := by
  have hp : 0 < (x - a) / (b - x) :=
    div_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)
  have hb : b - x ≠ 0 := ne_of_gt (sub_pos.mpr hx.2)
  have h1 : 1 + (x - a) / (b - x) ≠ 0 := ne_of_gt (by linarith)
  refine ⟨hp, ?_⟩
  apply (div_eq_iff h1).2
  field_simp [hb]
  ring

theorem barrierDescartesTransform_root_of_interval (p : ℝ[X]) (d : ℕ)
    {a b x : ℝ} (hd : p.natDegree ≤ d) (hx : x ∈ Set.Ioo a b)
    (hp : p.eval x = 0) :
    0 < (x - a) / (b - x) ∧
      (barrierDescartesTransform p d a b).eval ((x - a) / (b - x)) = 0 := by
  obtain ⟨ht, heq⟩ := barrierMobius_inverse hx
  refine ⟨ht, ?_⟩
  apply (barrierDescartesTransform_eval_eq_zero_iff p d a b _ hd
    (ne_of_gt (by linarith))).2
  rw [heq]
  exact hp

theorem barrier_coeff_affine_pow {R : Type*} [CommRing R]
    (a b : R) (j k : ℕ) :
    ((C a + C b * X) ^ j).coeff k =
      (j.choose k : R) * a ^ (j - k) * b ^ k := by
  calc
    ((C a + C b * X) ^ j).coeff k =
        (((X + C a) ^ j).comp (C b * X)).coeff k := by
      rw [pow_comp, add_comp, X_comp, C_comp,
        add_comm (C b * X) (C a)]
    _ = ((X + C a) ^ j).coeff k * b ^ k := comp_C_mul_X_coeff
    _ = _ := by
      rw [coeff_X_add_C_pow]
      ac_rfl

theorem barrierDescartesTransform_coeff {R : Type*} [CommRing R]
    (p : R[X]) (d : ℕ) (a b : R) (h : ℕ) :
    (barrierDescartesTransform p d a b).coeff h =
      ∑ j ∈ Finset.range (d + 1), p.coeff j *
        ∑ k ∈ Finset.range (h + 1),
          (j.choose k : R) * a ^ (j - k) * b ^ k *
            ((d - j).choose (h - k) : R) := by
  unfold barrierDescartesTransform
  rw [finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc, coeff_C_mul, coeff_mul]
  have hanti :
      (∑ x ∈ Finset.HasAntidiagonal.antidiagonal h,
        Polynomial.coeff ((C a + C b * X : R[X]) ^ j) x.1 *
          Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) x.2) =
      ∑ k ∈ Finset.range (h + 1),
        Polynomial.coeff ((C a + C b * X : R[X]) ^ j) k *
          Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) (h - k) :=
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun (k l : ℕ) => Polynomial.coeff ((C a + C b * X : R[X]) ^ j) k *
        Polynomial.coeff ((1 + X : R[X]) ^ (d - j)) l) h
  rw [hanti]
  simp only [barrier_coeff_affine_pow, coeff_one_add_X_pow]

def barrierDescartesCoeffRat (c : ℕ → ℚ) (d : ℕ) (a b : ℚ) (h : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (d + 1), c j *
    ∑ k ∈ Finset.range (h + 1),
      (j.choose k : ℚ) * a ^ (j - k) * b ^ k *
        ((d - j).choose (h - k) : ℚ)

theorem barrierDescartesTransform_coeff_rat (p : ℚ[X]) (c : ℕ → ℚ)
    (d : ℕ) (a b : ℚ) (h : ℕ)
    (hc : ∀ j, j < d + 1 → p.coeff j = c j) :
    (barrierDescartesTransform (p.map (Rat.castHom ℝ)) d (a : ℝ) (b : ℝ)).coeff h =
      (barrierDescartesCoeffRat c d a b h : ℝ) := by
  change (barrierDescartesTransform (p.map (Rat.castHom ℝ)) d
      ((Rat.castHom ℝ) a) ((Rat.castHom ℝ) b)).coeff h =
    (Rat.castHom ℝ) (barrierDescartesCoeffRat c d a b h)
  rw [barrierDescartesTransform_coeff]
  simp only [barrierDescartesCoeffRat, map_sum, map_mul, map_pow, map_natCast]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Polynomial.coeff_map, hc j (Finset.mem_range.mp hj)]

end

section

open Polynomial

theorem barrierDescartes_interval_roots_card_le (p : ℝ[X]) (d : ℕ) (a b : ℝ)
    (hd : p.natDegree ≤ d)
    (hne : barrierDescartesTransform p d a b ≠ 0)
    (s : Finset ℝ) (hs : ∀ x ∈ s, x ∈ Set.Ioo a b ∧ p.eval x = 0) :
    s.card ≤ (barrierDescartesTransform p d a b).signVariations := by
  classical
  let Q := barrierDescartesTransform p d a b
  let t := (Q.roots.filter (fun x => 0 < x)).toFinset
  have hcard : s.card ≤ t.card := by
    apply Finset.card_le_card_of_injOn (fun x : ℝ => (x - a) / (b - x))
    · intro x hx
      obtain ⟨hpos, hroot⟩ := barrierDescartesTransform_root_of_interval p d hd
        (hs x hx).1 (hs x hx).2
      apply Multiset.mem_toFinset.mpr
      exact Multiset.mem_filter.mpr
        ⟨(Polynomial.mem_roots hne).mpr hroot, hpos⟩
    · intro x hx y hy hxy
      change (x - a) / (b - x) = (y - a) / (b - y) at hxy
      have hix := (barrierMobius_inverse (hs x hx).1).2
      have hiy := (barrierMobius_inverse (hs y hy).1).2
      calc
        x = (a + b * ((x - a) / (b - x))) / (1 + (x - a) / (b - x)) := hix.symm
        _ = (a + b * ((y - a) / (b - y))) / (1 + (y - a) / (b - y)) := by rw [hxy]
        _ = y := hiy
  have htcard : t.card ≤ Q.roots.countP (fun x => 0 < x) := by
    simpa only [t, Multiset.countP_eq_card_filter] using
      Multiset.toFinset_card_le (Q.roots.filter (fun x => 0 < x))
  exact hcard.trans (htcard.trans (Polynomial.roots_countP_pos_le_signVariations Q))

end

section

open Filter Polynomial
open scoped Topology





end

open Polynomial
open scoped BigOperators

theorem barrierDescartesTransform_coeff_zero_above {R : Type*} [CommRing R]
    (p : R[X]) (d : ℕ) (a b : R) {h : ℕ} (hh : d < h) :
    (barrierDescartesTransform p d a b).coeff h = 0 := by
  rw [barrierDescartesTransform_coeff]
  apply Finset.sum_eq_zero
  intro j hj
  have hjd : j ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  suffices hsum :
      (∑ k ∈ Finset.range (h + 1),
        (j.choose k : R) * a ^ (j - k) * b ^ k *
          ((d - j).choose (h - k) : R)) = 0 by
    rw [hsum, mul_zero]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hkj : k ≤ j
  · have hchoose : d - j < h - k := by omega
    rw [Nat.choose_eq_zero_of_lt hchoose, Nat.cast_zero, mul_zero]
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hkj), Nat.cast_zero]
    simp only [zero_mul]

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





end

section
open Polynomial


noncomputable def barrierCase2AXTransform0Explicit : ℝ[X] :=
  C (-209727640868826299424336416762338709942801370466452116724113605281/372529029846191406250000000000000000000000000000000000000000000) +
  C (29990430724927816666033136640856349643849968721081048973244265950299/2235174179077148437500000000000000000000000000000000000000000000) * X ^ 1 +
  C (3357906261848697996591467826930270130313885311709171832650442860053/93132257461547851562500000000000000000000000000000000000000000) * X ^ 2 +
  C (-24590963384023039515420590414698371686095080041627657037105194103701/35762786865234375000000000000000000000000000000000000000000000) * X ^ 3 +
  C (-2306508751839564351435452412461153607804094025499082722799405470081919/894069671630859375000000000000000000000000000000000000000000000) * X ^ 4 +
  C (2924891549108577321044827309468575806585032990929219309633704833688387/2235174179077148437500000000000000000000000000000000000000000000) * X ^ 5 +
  C (14411598956122795329331864199854562313336400006244324780890158315048687/596046447753906250000000000000000000000000000000000000000000000) * X ^ 6 +
  C (240381398647980647101856218614047605091315685169542870941982922816337303/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 7 +
  C (39885989596923405446549835155953122182561380492645118009331989674413097/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 8 +
  C (-978586830578078170972451228097853787832396273357426564012917061368949953/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 9 +
  C (-158440174472980594608917492739210300359811388834719174968003522587204237/558793544769287109375000000000000000000000000000000000000000000) * X ^ 10 +
  C (-703864023670599536558628469873347789123416175681271510789359021360201331/2235174179077148437500000000000000000000000000000000000000000000) * X ^ 11 +
  C (-160113213351764291861201186805751996162101959738250470821832147628867419/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 12 +
  C (309812611750322580212480507691216004229022262566970055494116583705025949/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 13 +
  C (581529776775973204693503668958886132450237152695753169260358818525251939/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 14 +
  C (494093676341358291590064846714583417862419544295803931885275921281589091/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 15 +
  C (599505146329554516733832728172374151553193026940910075102845517630111953/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 16 +
  C (-47900878605033432752942164445733137747690750437419411279247639948763059/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 17 +
  C (-6167112187755891892734519611873802395964033588596732737108869210264191/69849193096160888671875000000000000000000000000000000000000000) * X ^ 18 +
  C (-73014091895547631416669441607350888345745513959153443980583318627415841/1117587089538574218750000000000000000000000000000000000000000000) * X ^ 19 +
  C (-718643360856260597932302951573856619855700467753323571167250432340481/27939677238464355468750000000000000000000000000000000000000000) * X ^ 20 +
  C (-962710094481727644002692983230956011591671992529789541063829819320489/372529029846191406250000000000000000000000000000000000000000000) * X ^ 21 +
  C (10475172842855275063025914179797938359414706205970415525576210815121651/2980232238769531250000000000000000000000000000000000000000000000) * X ^ 22 +
  C (189012225093546594887349294510415129844013362596133511317289078629177/74505805969238281250000000000000000000000000000000000000000000) * X ^ 23 +
  C (6685437708480859631346371400150028934041144961591212738489176237793/7450580596923828125000000000000000000000000000000000000000000) * X ^ 24 +
  C (56883849508272084742909282830181562202875366477095133499216766513999/357627868652343750000000000000000000000000000000000000000000000) * X ^ 25 +
  C (-14162788042848861308695537254795963896812943228709998738880103209/1490116119384765625000000000000000000000000000000000000000000) * X ^ 26 +
  C (-105824054567037626735172832742563012016584123203582782754721299013/7152557373046875000000000000000000000000000000000000000000000) * X ^ 27 +
  C (-108401669132996375979111866927555492310924000243379808178314947/23841857910156250000000000000000000000000000000000000000000) * X ^ 28 +
  C (-1658680191867456800674700159253893771282068235395595112263893/2288818359375000000000000000000000000000000000000000000000) * X ^ 29 +
  C (-7376747513873566993466802463786371979148944982194833585179/228881835937500000000000000000000000000000000000000000000) * X ^ 30 +
  C (64388063814669102438480427386034434361192371953632857817/4577636718750000000000000000000000000000000000000000000) * X ^ 31 +
  C (378535933566809808538323945203474350603724584632479039/91552734375000000000000000000000000000000000000000000) * X ^ 32 +
  C (37474721360256790411245335672338372712089633337913/61035156250000000000000000000000000000000000000000) * X ^ 33 +
  C (69273838420387581502431292190774435835733733007/1220703125000000000000000000000000000000000000000) * X ^ 34 +
  C (3798547929745011074799983631400637174670591/1220703125000000000000000000000000000000000000) * X ^ 35 +
  C (30307837230416268959058568549773/390625000000000000000000000000000000) * X ^ 36


def barrierCase2AXTransform1Coefficient (k : ℕ) : ℚ :=
  ([30307837230416268959058568549773/390625000000000000000000000000000000, 3020715447098649440988194292298287825329409/1220703125000000000000000000000000000000000000, 42049701527764924319018665322192208608792363007/1220703125000000000000000000000000000000000000000, 16526572910869869255420729946342910343604729885887/61035156250000000000000000000000000000000000000000, 105239625160222745319730145430430437079427292257192039/91552734375000000000000000000000000000000000000000000, -622692595364234084080007511740406912826852679493044339/1525878906250000000000000000000000000000000000000000000, -10403475965502560290507023728419939191219522285064499377879/228881835937500000000000000000000000000000000000000000000, -796341291334825150204456286901420218568536239273112120653507/2288818359375000000000000000000000000000000000000000000000, -190417993219164348175941220351527049372877505555918601849190057/143051147460937500000000000000000000000000000000000000000000, -10998230901604155772014886097508950316611506164716154996022835587/7152557373046875000000000000000000000000000000000000000000000, 69012298141575578427543995084228995116521595452411291451411451749/5960464477539062500000000000000000000000000000000000000000000, 26472627895496058373003337267539682980479610599668646934315679010281/357627868652343750000000000000000000000000000000000000000000000, 38180434059164806195032940364096257703997173159049508794781897358057/178813934326171875000000000000000000000000000000000000000000000, 21911864516068933481751846495705045770326803445561148622764671676713/74505805969238281250000000000000000000000000000000000000000000, -1588858933820436772647604483137891453570816484976347478422017696265687/8940696716308593750000000000000000000000000000000000000000000000, -4039042052146899346912568262956863049215147660882490857399077644694503/2235174179077148437500000000000000000000000000000000000000000000, -9441976227791514236176683788037718246329833002604146108805551092650789/2235174179077148437500000000000000000000000000000000000000000000, -5715106567517964277929475523886351309772855950196359586348628861808659/1117587089538574218750000000000000000000000000000000000000000000, -441905876152895468480205247986763468005866444890784398153999721991617/279396772384643554687500000000000000000000000000000000000000000, 8972146537617572116496022164441273469563738295972157508555990311549347/1490116119384765625000000000000000000000000000000000000000000000, 55237601974390179407308360690623695054057098357780420490863110590526563/4470348358154296875000000000000000000000000000000000000000000000, 52017130120220076393499270758253682468134505064533870946548098514617879/4470348358154296875000000000000000000000000000000000000000000000, 6465348060898014135278701555426785839113632019353528087169835342328617/1490116119384765625000000000000000000000000000000000000000000000, -13038904013535082935357326722895363312283408857352000450818649401093983/4470348358154296875000000000000000000000000000000000000000000000, -21857174100232297715359777686090725468351831899688782951167595341612371/4470348358154296875000000000000000000000000000000000000000000000, -5923061423107121018038988853092831502667515677942828271004300497070357/2235174179077148437500000000000000000000000000000000000000000000, -313121369493492007175972146705443151292167839540887217982577851263427/1117587089538574218750000000000000000000000000000000000000000000, 695429197629917346237482846088245723343544654340124994481784762257021/1788139343261718750000000000000000000000000000000000000000000000, 12751929960502662877986233727003216874003813129985261266517566129183/74505805969238281250000000000000000000000000000000000000000000, 21306080097912416985791981075803357240168820595544028536565763228961/4470348358154296875000000000000000000000000000000000000000000000, -67866030654188050248849133766479558220872634260228298832620249056067/8940696716308593750000000000000000000000000000000000000000000000, -115736781820307005143841220465526915569688003345514072881529166347/223517417907714843750000000000000000000000000000000000000000000, 230017984253306181278277431120594418732678114969982719989701584703/4470348358154296875000000000000000000000000000000000000000000000, 3063812846755407988776804010415196437715658015588410972497995987/1490116119384765625000000000000000000000000000000000000000000000, -27950441608976463524030794323746905995423195320004998148701391/745058059692382812500000000000000000000000000000000000000000000, -1023909159565987428772051848621582094363911264149216672704023/745058059692382812500000000000000000000000000000000000000000000, -57062552915849414305718329706307989546263442479977/14901161193847656250000000000000000000000000000000000000] : List ℚ).getD k 0

noncomputable def barrierCase2AXTransform1Explicit : ℝ[X] :=
  C (30307837230416268959058568549773/390625000000000000000000000000000000) +
  C (3020715447098649440988194292298287825329409/1220703125000000000000000000000000000000000000) * X ^ 1 +
  C (42049701527764924319018665322192208608792363007/1220703125000000000000000000000000000000000000000) * X ^ 2 +
  C (16526572910869869255420729946342910343604729885887/61035156250000000000000000000000000000000000000000) * X ^ 3 +
  C (105239625160222745319730145430430437079427292257192039/91552734375000000000000000000000000000000000000000000) * X ^ 4 +
  C (-622692595364234084080007511740406912826852679493044339/1525878906250000000000000000000000000000000000000000000) * X ^ 5 +
  C (-10403475965502560290507023728419939191219522285064499377879/228881835937500000000000000000000000000000000000000000000) * X ^ 6 +
  C (-796341291334825150204456286901420218568536239273112120653507/2288818359375000000000000000000000000000000000000000000000) * X ^ 7 +
  C (-190417993219164348175941220351527049372877505555918601849190057/143051147460937500000000000000000000000000000000000000000000) * X ^ 8 +
  C (-10998230901604155772014886097508950316611506164716154996022835587/7152557373046875000000000000000000000000000000000000000000000) * X ^ 9 +
  C (69012298141575578427543995084228995116521595452411291451411451749/5960464477539062500000000000000000000000000000000000000000000) * X ^ 10 +
  C (26472627895496058373003337267539682980479610599668646934315679010281/357627868652343750000000000000000000000000000000000000000000000) * X ^ 11 +
  C (38180434059164806195032940364096257703997173159049508794781897358057/178813934326171875000000000000000000000000000000000000000000000) * X ^ 12 +
  C (21911864516068933481751846495705045770326803445561148622764671676713/74505805969238281250000000000000000000000000000000000000000000) * X ^ 13 +
  C (-1588858933820436772647604483137891453570816484976347478422017696265687/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 14 +
  C (-4039042052146899346912568262956863049215147660882490857399077644694503/2235174179077148437500000000000000000000000000000000000000000000) * X ^ 15 +
  C (-9441976227791514236176683788037718246329833002604146108805551092650789/2235174179077148437500000000000000000000000000000000000000000000) * X ^ 16 +
  C (-5715106567517964277929475523886351309772855950196359586348628861808659/1117587089538574218750000000000000000000000000000000000000000000) * X ^ 17 +
  C (-441905876152895468480205247986763468005866444890784398153999721991617/279396772384643554687500000000000000000000000000000000000000000) * X ^ 18 +
  C (8972146537617572116496022164441273469563738295972157508555990311549347/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 19 +
  C (55237601974390179407308360690623695054057098357780420490863110590526563/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 20 +
  C (52017130120220076393499270758253682468134505064533870946548098514617879/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 21 +
  C (6465348060898014135278701555426785839113632019353528087169835342328617/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 22 +
  C (-13038904013535082935357326722895363312283408857352000450818649401093983/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 23 +
  C (-21857174100232297715359777686090725468351831899688782951167595341612371/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 24 +
  C (-5923061423107121018038988853092831502667515677942828271004300497070357/2235174179077148437500000000000000000000000000000000000000000000) * X ^ 25 +
  C (-313121369493492007175972146705443151292167839540887217982577851263427/1117587089538574218750000000000000000000000000000000000000000000) * X ^ 26 +
  C (695429197629917346237482846088245723343544654340124994481784762257021/1788139343261718750000000000000000000000000000000000000000000000) * X ^ 27 +
  C (12751929960502662877986233727003216874003813129985261266517566129183/74505805969238281250000000000000000000000000000000000000000000) * X ^ 28 +
  C (21306080097912416985791981075803357240168820595544028536565763228961/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 29 +
  C (-67866030654188050248849133766479558220872634260228298832620249056067/8940696716308593750000000000000000000000000000000000000000000000) * X ^ 30 +
  C (-115736781820307005143841220465526915569688003345514072881529166347/223517417907714843750000000000000000000000000000000000000000000) * X ^ 31 +
  C (230017984253306181278277431120594418732678114969982719989701584703/4470348358154296875000000000000000000000000000000000000000000000) * X ^ 32 +
  C (3063812846755407988776804010415196437715658015588410972497995987/1490116119384765625000000000000000000000000000000000000000000000) * X ^ 33 +
  C (-27950441608976463524030794323746905995423195320004998148701391/745058059692382812500000000000000000000000000000000000000000000) * X ^ 34 +
  C (-1023909159565987428772051848621582094363911264149216672704023/745058059692382812500000000000000000000000000000000000000000000) * X ^ 35 +
  C (-57062552915849414305718329706307989546263442479977/14901161193847656250000000000000000000000000000000000000) * X ^ 36

theorem barrierCase2AXTransform1Explicit_natDegree : barrierCase2AXTransform1Explicit.natDegree = 36 := by
  unfold barrierCase2AXTransform1Explicit
  compute_degree!

end























end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesX1Group0
namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform1_ratCoeff_0 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 0 =
      barrierCase2AXTransform1Coefficient 0 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_0 :
    barrierCase2AXTransform1Explicit.coeff 0 = (barrierCase2AXTransform1Coefficient 0 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_1 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 1 =
      barrierCase2AXTransform1Coefficient 1 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_1 :
    barrierCase2AXTransform1Explicit.coeff 1 = (barrierCase2AXTransform1Coefficient 1 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_2 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 2 =
      barrierCase2AXTransform1Coefficient 2 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_2 :
    barrierCase2AXTransform1Explicit.coeff 2 = (barrierCase2AXTransform1Coefficient 2 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_3 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 3 =
      barrierCase2AXTransform1Coefficient 3 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_3 :
    barrierCase2AXTransform1Explicit.coeff 3 = (barrierCase2AXTransform1Coefficient 3 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_4 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 4 =
      barrierCase2AXTransform1Coefficient 4 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_4 :
    barrierCase2AXTransform1Explicit.coeff 4 = (barrierCase2AXTransform1Coefficient 4 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesX1Group1
namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform1_ratCoeff_5 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 5 =
      barrierCase2AXTransform1Coefficient 5 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_5 :
    barrierCase2AXTransform1Explicit.coeff 5 = (barrierCase2AXTransform1Coefficient 5 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_6 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 6 =
      barrierCase2AXTransform1Coefficient 6 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_6 :
    barrierCase2AXTransform1Explicit.coeff 6 = (barrierCase2AXTransform1Coefficient 6 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_7 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 7 =
      barrierCase2AXTransform1Coefficient 7 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_7 :
    barrierCase2AXTransform1Explicit.coeff 7 = (barrierCase2AXTransform1Coefficient 7 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_8 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 8 =
      barrierCase2AXTransform1Coefficient 8 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_8 :
    barrierCase2AXTransform1Explicit.coeff 8 = (barrierCase2AXTransform1Coefficient 8 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_9 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 9 =
      barrierCase2AXTransform1Coefficient 9 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_9 :
    barrierCase2AXTransform1Explicit.coeff 9 = (barrierCase2AXTransform1Coefficient 9 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoDescartesX1Group2
namespace OAI

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform1_ratCoeff_10 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 10 =
      barrierCase2AXTransform1Coefficient 10 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_10 :
    barrierCase2AXTransform1Explicit.coeff 10 = (barrierCase2AXTransform1Coefficient 10 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_11 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 11 =
      barrierCase2AXTransform1Coefficient 11 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_11 :
    barrierCase2AXTransform1Explicit.coeff 11 = (barrierCase2AXTransform1Coefficient 11 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_12 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 12 =
      barrierCase2AXTransform1Coefficient 12 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_12 :
    barrierCase2AXTransform1Explicit.coeff 12 = (barrierCase2AXTransform1Coefficient 12 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_13 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 13 =
      barrierCase2AXTransform1Coefficient 13 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_13 :
    barrierCase2AXTransform1Explicit.coeff 13 = (barrierCase2AXTransform1Coefficient 13 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_14 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 14 =
      barrierCase2AXTransform1Coefficient 14 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_14 :
    barrierCase2AXTransform1Explicit.coeff 14 = (barrierCase2AXTransform1Coefficient 14 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

end InternalCatalan

end OAI

end

section
-- module Solutions.OAICatalan.Catalan.SecondBarrier.BarrierCaseTwoXRootSimplicity
namespace OAI

noncomputable section

namespace InternalCatalan
open Polynomial

theorem barrierCase2AX_transform1_ratCoeff_15 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 15 =
      barrierCase2AXTransform1Coefficient 15 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_15 :
    barrierCase2AXTransform1Explicit.coeff 15 = (barrierCase2AXTransform1Coefficient 15 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_16 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 16 =
      barrierCase2AXTransform1Coefficient 16 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_16 :
    barrierCase2AXTransform1Explicit.coeff 16 = (barrierCase2AXTransform1Coefficient 16 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_17 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 17 =
      barrierCase2AXTransform1Coefficient 17 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_17 :
    barrierCase2AXTransform1Explicit.coeff 17 = (barrierCase2AXTransform1Coefficient 17 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_18 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 18 =
      barrierCase2AXTransform1Coefficient 18 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_18 :
    barrierCase2AXTransform1Explicit.coeff 18 = (barrierCase2AXTransform1Coefficient 18 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_19 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 19 =
      barrierCase2AXTransform1Coefficient 19 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_19 :
    barrierCase2AXTransform1Explicit.coeff 19 = (barrierCase2AXTransform1Coefficient 19 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_20 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 20 =
      barrierCase2AXTransform1Coefficient 20 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_20 :
    barrierCase2AXTransform1Explicit.coeff 20 = (barrierCase2AXTransform1Coefficient 20 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_21 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 21 =
      barrierCase2AXTransform1Coefficient 21 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_21 :
    barrierCase2AXTransform1Explicit.coeff 21 = (barrierCase2AXTransform1Coefficient 21 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_22 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 22 =
      barrierCase2AXTransform1Coefficient 22 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_22 :
    barrierCase2AXTransform1Explicit.coeff 22 = (barrierCase2AXTransform1Coefficient 22 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_23 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 23 =
      barrierCase2AXTransform1Coefficient 23 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_23 :
    barrierCase2AXTransform1Explicit.coeff 23 = (barrierCase2AXTransform1Coefficient 23 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_24 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 24 =
      barrierCase2AXTransform1Coefficient 24 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_24 :
    barrierCase2AXTransform1Explicit.coeff 24 = (barrierCase2AXTransform1Coefficient 24 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_25 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 25 =
      barrierCase2AXTransform1Coefficient 25 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_25 :
    barrierCase2AXTransform1Explicit.coeff 25 = (barrierCase2AXTransform1Coefficient 25 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_26 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 26 =
      barrierCase2AXTransform1Coefficient 26 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_26 :
    barrierCase2AXTransform1Explicit.coeff 26 = (barrierCase2AXTransform1Coefficient 26 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_27 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 27 =
      barrierCase2AXTransform1Coefficient 27 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_27 :
    barrierCase2AXTransform1Explicit.coeff 27 = (barrierCase2AXTransform1Coefficient 27 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_28 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 28 =
      barrierCase2AXTransform1Coefficient 28 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_28 :
    barrierCase2AXTransform1Explicit.coeff 28 = (barrierCase2AXTransform1Coefficient 28 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_29 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 29 =
      barrierCase2AXTransform1Coefficient 29 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_29 :
    barrierCase2AXTransform1Explicit.coeff 29 = (barrierCase2AXTransform1Coefficient 29 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_30 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 30 =
      barrierCase2AXTransform1Coefficient 30 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_30 :
    barrierCase2AXTransform1Explicit.coeff 30 = (barrierCase2AXTransform1Coefficient 30 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_31 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 31 =
      barrierCase2AXTransform1Coefficient 31 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_31 :
    barrierCase2AXTransform1Explicit.coeff 31 = (barrierCase2AXTransform1Coefficient 31 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_32 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 32 =
      barrierCase2AXTransform1Coefficient 32 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_32 :
    barrierCase2AXTransform1Explicit.coeff 32 = (barrierCase2AXTransform1Coefficient 32 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_33 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 33 =
      barrierCase2AXTransform1Coefficient 33 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_33 :
    barrierCase2AXTransform1Explicit.coeff 33 = (barrierCase2AXTransform1Coefficient 33 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_34 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 34 =
      barrierCase2AXTransform1Coefficient 34 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_34 :
    barrierCase2AXTransform1Explicit.coeff 34 = (barrierCase2AXTransform1Coefficient 34 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_35 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 35 =
      barrierCase2AXTransform1Coefficient 35 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_35 :
    barrierCase2AXTransform1Explicit.coeff 35 = (barrierCase2AXTransform1Coefficient 35 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_ratCoeff_36 :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) 36 =
      barrierCase2AXTransform1Coefficient 36 := by decide +kernel

theorem barrierCase2AXTransform1Explicit_coeff_36 :
    barrierCase2AXTransform1Explicit.coeff 36 = (barrierCase2AXTransform1Coefficient 36 : ℝ) := by
  simp only [barrierCase2AXTransform1Explicit, coeff_add, coeff_C_mul_X_pow,
    coeff_C, Nat.reduceEqDiff, ite_true, ite_false, add_zero, zero_add]
  simp only [barrierCase2AXTransform1Coefficient, List.getD_cons_zero, List.getD_cons_succ]
  norm_num

theorem barrierCase2AX_transform1_all_coeff_rat (h : Fin 37) :
    barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) h.val =
      barrierCase2AXTransform1Coefficient h.val := by
  rcases h with ⟨h, hh⟩
  change barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) h =
    barrierCase2AXTransform1Coefficient h
  interval_cases h
  · exact barrierCase2AX_transform1_ratCoeff_0
  · exact barrierCase2AX_transform1_ratCoeff_1
  · exact barrierCase2AX_transform1_ratCoeff_2
  · exact barrierCase2AX_transform1_ratCoeff_3
  · exact barrierCase2AX_transform1_ratCoeff_4
  · exact barrierCase2AX_transform1_ratCoeff_5
  · exact barrierCase2AX_transform1_ratCoeff_6
  · exact barrierCase2AX_transform1_ratCoeff_7
  · exact barrierCase2AX_transform1_ratCoeff_8
  · exact barrierCase2AX_transform1_ratCoeff_9
  · exact barrierCase2AX_transform1_ratCoeff_10
  · exact barrierCase2AX_transform1_ratCoeff_11
  · exact barrierCase2AX_transform1_ratCoeff_12
  · exact barrierCase2AX_transform1_ratCoeff_13
  · exact barrierCase2AX_transform1_ratCoeff_14
  · exact barrierCase2AX_transform1_ratCoeff_15
  · exact barrierCase2AX_transform1_ratCoeff_16
  · exact barrierCase2AX_transform1_ratCoeff_17
  · exact barrierCase2AX_transform1_ratCoeff_18
  · exact barrierCase2AX_transform1_ratCoeff_19
  · exact barrierCase2AX_transform1_ratCoeff_20
  · exact barrierCase2AX_transform1_ratCoeff_21
  · exact barrierCase2AX_transform1_ratCoeff_22
  · exact barrierCase2AX_transform1_ratCoeff_23
  · exact barrierCase2AX_transform1_ratCoeff_24
  · exact barrierCase2AX_transform1_ratCoeff_25
  · exact barrierCase2AX_transform1_ratCoeff_26
  · exact barrierCase2AX_transform1_ratCoeff_27
  · exact barrierCase2AX_transform1_ratCoeff_28
  · exact barrierCase2AX_transform1_ratCoeff_29
  · exact barrierCase2AX_transform1_ratCoeff_30
  · exact barrierCase2AX_transform1_ratCoeff_31
  · exact barrierCase2AX_transform1_ratCoeff_32
  · exact barrierCase2AX_transform1_ratCoeff_33
  · exact barrierCase2AX_transform1_ratCoeff_34
  · exact barrierCase2AX_transform1_ratCoeff_35
  · exact barrierCase2AX_transform1_ratCoeff_36

theorem barrierCase2AXTransform1Explicit_coeff (h : ℕ) (hh : h < 37) :
    barrierCase2AXTransform1Explicit.coeff h = (barrierCase2AXTransform1Coefficient h : ℝ) := by
  interval_cases h
  · exact barrierCase2AXTransform1Explicit_coeff_0
  · exact barrierCase2AXTransform1Explicit_coeff_1
  · exact barrierCase2AXTransform1Explicit_coeff_2
  · exact barrierCase2AXTransform1Explicit_coeff_3
  · exact barrierCase2AXTransform1Explicit_coeff_4
  · exact barrierCase2AXTransform1Explicit_coeff_5
  · exact barrierCase2AXTransform1Explicit_coeff_6
  · exact barrierCase2AXTransform1Explicit_coeff_7
  · exact barrierCase2AXTransform1Explicit_coeff_8
  · exact barrierCase2AXTransform1Explicit_coeff_9
  · exact barrierCase2AXTransform1Explicit_coeff_10
  · exact barrierCase2AXTransform1Explicit_coeff_11
  · exact barrierCase2AXTransform1Explicit_coeff_12
  · exact barrierCase2AXTransform1Explicit_coeff_13
  · exact barrierCase2AXTransform1Explicit_coeff_14
  · exact barrierCase2AXTransform1Explicit_coeff_15
  · exact barrierCase2AXTransform1Explicit_coeff_16
  · exact barrierCase2AXTransform1Explicit_coeff_17
  · exact barrierCase2AXTransform1Explicit_coeff_18
  · exact barrierCase2AXTransform1Explicit_coeff_19
  · exact barrierCase2AXTransform1Explicit_coeff_20
  · exact barrierCase2AXTransform1Explicit_coeff_21
  · exact barrierCase2AXTransform1Explicit_coeff_22
  · exact barrierCase2AXTransform1Explicit_coeff_23
  · exact barrierCase2AXTransform1Explicit_coeff_24
  · exact barrierCase2AXTransform1Explicit_coeff_25
  · exact barrierCase2AXTransform1Explicit_coeff_26
  · exact barrierCase2AXTransform1Explicit_coeff_27
  · exact barrierCase2AXTransform1Explicit_coeff_28
  · exact barrierCase2AXTransform1Explicit_coeff_29
  · exact barrierCase2AXTransform1Explicit_coeff_30
  · exact barrierCase2AXTransform1Explicit_coeff_31
  · exact barrierCase2AXTransform1Explicit_coeff_32
  · exact barrierCase2AXTransform1Explicit_coeff_33
  · exact barrierCase2AXTransform1Explicit_coeff_34
  · exact barrierCase2AXTransform1Explicit_coeff_35
  · exact barrierCase2AXTransform1Explicit_coeff_36

theorem barrierCase2AX_transform1_eq_explicit :
    barrierDescartesTransform (barrierCase2AX.map (Rat.castHom ℝ)) 36 (0) (1) =
      barrierCase2AXTransform1Explicit := by
  apply Polynomial.ext
  intro h
  by_cases hh : h < 37
  · have hc := barrierDescartesTransform_coeff_rat barrierCase2AX
      barrierCase2AXCoefficient 36 (0) (1) h barrierCase2AX_coeff_small
    have hr := barrierCase2AX_transform1_all_coeff_rat ⟨h, hh⟩
    change barrierDescartesCoeffRat barrierCase2AXCoefficient 36 (0) (1) h =
      barrierCase2AXTransform1Coefficient h at hr
    rw [hr] at hc
    have ha : ((0 : ℚ) : ℝ) = (0 : ℝ) := by norm_num
    have hb : ((1 : ℚ) : ℝ) = (1 : ℝ) := by norm_num
    rw [ha, hb] at hc
    exact hc.trans (barrierCase2AXTransform1Explicit_coeff h hh).symm
  · rw [barrierDescartesTransform_coeff_zero_above _ _ _ _ (by omega)]
    symm
    apply coeff_eq_zero_of_natDegree_lt
    rw [barrierCase2AXTransform1Explicit_natDegree]
    omega

theorem barrierCase2AX_transform1_signVariations :
    (barrierDescartesTransform (barrierCase2AX.map (Rat.castHom ℝ))
      36 (0) (1)).signVariations = 9 := by
  rw [barrierCase2AX_transform1_eq_explicit]
  have hd : barrierCase2AXTransform1Explicit.degree = 36 :=
    (degree_eq_iff_natDegree_eq_of_pos (show 0 < (36 : ℕ) by decide)).mpr
      barrierCase2AXTransform1Explicit_natDegree
  rw [signVariations, coeffList, hd]
  norm_num [barrierCase2AXTransform1Explicit_coeff, barrierCase2AXTransform1Coefficient,
    List.range_succ, List.destutter, List.destutter', sign_apply,
    coeff_C_mul, coeff_X_pow, coeff_X]


private theorem barrierCase2AX_mapped_natDegree_le :
    (barrierCase2AX.map (Rat.castHom ℝ)).natDegree ≤ 36 := by
  calc
    _ ≤ barrierCase2AX.natDegree := Polynomial.natDegree_map_le
    _ = 36 := barrierCase2AX_natDegree


theorem barrierCase2AX_interval1_roots_card_le (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 9 := by
  have hne : barrierDescartesTransform
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1 ≠ 0 := by
    intro hz
    have h := barrierCase2AX_transform1_signVariations
    rw [hz, Polynomial.signVariations_zero] at h
    norm_num at h
  simpa only [barrierCase2AX_transform1_signVariations] using
    barrierDescartes_interval_roots_card_le
      (barrierCase2AX.map (Rat.castHom ℝ)) 36 0 1
      barrierCase2AX_mapped_natDegree_le hne s hs





























end InternalCatalan

end

end OAI

end

section
open OAI.InternalCatalan
open Polynomial

theorem solution (s : Finset ℝ)
    (hs : ∀ x ∈ s, x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0) : s.card ≤ 9 := by
  first
  | exact @OAI.InternalCatalan.barrierCase2AX_interval1_roots_card_le
  | (apply OAI.InternalCatalan.barrierCase2AX_interval1_roots_card_le <;> assumption)

end
