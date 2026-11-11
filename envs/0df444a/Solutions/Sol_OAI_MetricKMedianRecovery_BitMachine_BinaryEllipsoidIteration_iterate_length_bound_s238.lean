-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:27:51.293827+00:00
-- url     : https://prove2.me/submissions/20261a65-404b-4372-8ead-930ade476d87

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_Ellipsoid_iterate_shape_entry_bound_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace Signed
lemma encode_length (z : ℤ) : (encode z).length=z.natAbs.size+1 := by
  simp only [encode,List.length_cons,Nat.size_eq_bits_len]
end Signed
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Op
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic
namespace WordList
lemma encode_le_bound (ws : List (List Bool)) (B : ℕ) (hB : ∀ w∈ws,w.length ≤ B) :
    (encode ws).length ≤ ws.length*(2*B+2) := by
  induction ws with
  | nil => simp only [encode,List.length_nil,Nat.zero_mul,Nat.le_refl]
  | cons w ws ih =>
    have hw := hB w (List.mem_cons_self ..)
    have ht := ih (fun x hx=>hB x (List.mem_cons_of_mem _ hx))
    simp only [encode,length_cons,List.length_cons]
    nlinarith
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
attribute [local irreducible] WordList.mapWith WordList.Indices.run WordList.Lookup.run
  WordList.Fold.run IntegerArray.sumWords 
open WordOperations BinaryArithmetic
namespace WordList
lemma length_member_le_encode {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) :
    w.length≤(encode ws).length := by
  induction ws with
  | nil => simp only [List.not_mem_nil] at hw
  | cons v vs ih =>
    simp only [List.mem_cons] at hw
    rw [encode,length_cons]
    rcases hw with rfl|hv
    · omega
    · have hh := ih hv
      omega
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Height
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
open scoped BigOperators

lemma Height.mono {q : ℚ} {b c : ℕ} (h : Height q b) (hc : b ≤ c) : Height q c :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by norm_num) hc),h.2.trans (Nat.pow_le_pow_right (by norm_num) hc)⟩

lemma zero (b : ℕ) : Height 0 b := by
  constructor
  · simp
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma of_fraction (p : ℤ) (d b : ℕ) (hd : 0<d) (hp : p.natAbs≤2^b) (hdb : d≤2^b) :
    Height ((p:ℚ)/(d:ℚ)) b := by
  constructor
  · by_cases hz : p=0
    · simp [hz]
    · have hh := Rat.num_dvd p (by exact_mod_cast hd.ne' : (d:ℤ)≠0)
      rw [←Rat.intCast_div_eq_divInt] at hh
      simp only [Int.cast_natCast] at hh
      exact (Nat.le_of_dvd (by omega : 0<p.natAbs) (Int.natAbs_dvd_natAbs.mpr hh)).trans hp
  · have hh := Rat.den_dvd p (d:ℤ)
    rw [←Rat.intCast_div_eq_divInt] at hh
    simp only [Int.cast_natCast] at hh
    exact (Nat.le_of_dvd hd (Int.natCast_dvd_natCast.mp hh)).trans hdb

lemma natCast (n b : ℕ) (hn : n≤2^b) : Height (n:ℚ) b := by
  constructor
  · simpa using hn
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^b)

lemma Height.neg {q : ℚ} {b : ℕ} (hq : Height q b) : Height (-q) b := by
  simpa only [Height,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den] using hq

lemma Height.add {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q+r) (b+c+1) := by
  have hn : (q.num*(r.den:ℤ)+r.num*(q.den:ℤ)).natAbs≤2^(b+c+1) := by
    calc
      _ ≤ q.num.natAbs*r.den+r.num.natAbs*q.den := by
        simpa only [Int.natAbs_mul,Int.natAbs_natCast] using
          Int.natAbs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      _ ≤ 2^b*2^c+2^c*2^b := Nat.add_le_add (Nat.mul_le_mul hq.1 hr.2) (Nat.mul_le_mul hr.1 hq.2)
      _ = _ := by rw [pow_succ,pow_add]; ring
  have hd : q.den*r.den≤2^(b+c+1) := by
    have hh := Nat.mul_le_mul hq.2 hr.2
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have he : q+r=((q.num*(r.den:ℤ)+r.num*(q.den:ℤ):ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    convert div_add_div (q.num:ℚ) (r.num:ℚ) (by exact_mod_cast q.den_nz : (q.den:ℚ)≠0) (by exact_mod_cast r.den_nz : (r.den:ℚ)≠0) using 1
    all_goals try with_reducible_and_instances rfl
    ring
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.sub {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q-r) (b+c+1) := by
  rw [sub_eq_add_neg]
  exact hq.add hr.neg

lemma Height.mul {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q*r) (b+c) := by
  have hn : (q.num*r.num).natAbs≤2^(b+c) := by
    rw [Int.natAbs_mul,pow_add]
    exact Nat.mul_le_mul hq.1 hr.1
  have hd : q.den*r.den≤2^(b+c) := by rw [pow_add]; exact Nat.mul_le_mul hq.2 hr.2
  have he : q*r=((q.num*r.num:ℤ):ℚ)/(q.den*r.den:ℕ) := by
    nth_rw 1 [←Rat.num_div_den q]
    nth_rw 1 [←Rat.num_div_den r]
    push_cast
    exact div_mul_div_comm _ _ _ _
  rw [he]
  exact of_fraction _ _ _ (Nat.mul_pos q.den_pos r.den_pos) hn hd

lemma Height.inv {q : ℚ} {b : ℕ} (hq : Height q b) : Height q⁻¹ b := by
  by_cases hz : q=0
  · subst q
    simpa only [inv_zero] using zero b
  · have hn : q.num≠0 := Rat.num_ne_zero.mpr hz
    constructor
    · simpa only [Rat.num_inv,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero hn,
        Int.natAbs_natCast,one_mul] using hq.2
    · simpa only [Rat.den_inv_of_ne_zero hz] using hq.1

lemma sum {V : Type*} [Fintype V] (f : V → ℚ) (b : ℕ) (hf : ∀ i,Height (f i) b) :
    Height (∑ i,f i) (Fintype.card V*(b+1)) := by
  have haux (s : Finset V) : Height (∑ i∈s,f i) (s.card*(b+1)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using zero 0
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]
      convert (hf a).add ih using 1
      all_goals try with_reducible_and_instances rfl
      ring
  simpa using haux Finset.univ

lemma sqrtFraction (p d D b e : ℕ) (hp : p≤2^b) (hd : d≤2^b) (hD : D≤2^e)
    (hd0 : 0<d) (hD0 : 0<D) :
    Height (((Nat.sqrt (p*d*D^2)+1:ℕ):ℚ)/(d*D:ℕ)) (2*b+2*e+1) := by
  have harg : p*d*D^2≤2^(2*b+2*e) := by
    calc
      _ ≤ 2^b*2^b*(2^e)^2 := Nat.mul_le_mul (Nat.mul_le_mul hp hd) (Nat.pow_le_pow_left hD 2)
      _ = _ := by rw [←pow_add,←pow_mul,←pow_add]; congr 1; omega
  have hs : Nat.sqrt (p*d*D^2)+1≤2^(2*b+2*e+1) := by
    have hh := (Nat.sqrt_le_self (p*d*D^2)).trans harg
    have ho : 1≤2^(2*b+2*e) := one_le_pow₀ (by norm_num)
    calc
      _ ≤ 2^(2*b+2*e)+1 := Nat.add_le_add_right hh 1
      _ ≤ 2^(2*b+2*e)*2 := by omega
      _ = _ := (Nat.pow_succ 2 (2*b+2*e)).symm
  have hden : d*D≤2^(2*b+2*e+1) := by
    have hh := Nat.mul_le_mul hd hD
    rw [←pow_add] at hh
    exact hh.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  simpa only [Int.cast_natCast] using of_fraction ((Nat.sqrt (p*d*D^2)+1:ℕ):ℤ) (d*D) _
    (Nat.mul_pos hd0 hD0) (by simpa only [Int.natAbs_natCast] using hs) hden

end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_Encode2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace BinaryRational
lemma encode_length (q : ℚ) : (encode q).length=2*(q.num.natAbs.size+1)+1+q.den.size := by
  simp only [encode,pairBits_length,Signed.encode_length,←Nat.size_eq_bits_len]
lemma encode_height {q : ℚ} {b : ℕ} (hq : RationalHeight.Height q b) :
    (encode q).length≤3*b+6 := by
  have hn := Nat.size_le_size hq.1
  have hd := Nat.size_le_size hq.2
  rw [Nat.size_pow] at hn hd
  rw [encode_length]
  omega
lemma input_height (q : ℚ) : RationalHeight.Height q (encode q).length := by
  rw [encode_length]
  constructor
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
  · apply Nat.le_of_lt
    apply Nat.size_le.mp
    omega
end BinaryRational
namespace RationalMatrix
open WordList

lemma rowEncode_eq {n : ℕ} (v : Fin n → ℚ) :
    rowEncode v=WordList.encode (List.ofFn (fun i=>BinaryRational.encode (v i))) := by
  simp only [rowEncode,RationalArray.encode,List.map_ofFn,Function.comp_def]

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Machines_LoopInput2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList
lemma dimension_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : n≤(encode A).length := by
  rw [encode]
  simpa only [List.length_ofFn] using length_le_encode (List.ofFn (fun i=>rowEncode (A i)))
lemma encode_height {n b : ℕ} (F : Matrix (Fin n) (Fin n) ℚ)
    (hF : ∀ i j,RationalHeight.Height (F i j) b) :
    (encode F).length≤n*(2*(n*(6*b+14))+2) := by
  have hr (i : Fin n) : (rowEncode (F i)).length≤n*(6*b+14) := by
    rw [rowEncode_eq]
    have hh := encode_le_bound (List.ofFn (fun j=>BinaryRational.encode (F i j))) (3*b+6) (by
      intro w hw
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
      exact BinaryRational.encode_height (hF i j))
    simp only [List.length_ofFn] at hh
    convert hh using 1 <;> first | rfl | ring
  have hh := encode_le_bound (List.ofFn (fun i=>rowEncode (F i))) (n*(6*b+14)) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact hr i)
  rw [encode]
  simpa only [List.length_ofFn] using hh

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_FormTrans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid

open Matrix
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma gridDenominator_pos (n T : ℕ) (hn : 0<n) : 0<gridDenominator n T := by
  unfold gridDenominator
  positivity

lemma gridDenominator_size (n T : ℕ) : gridDenominator n T≤2^(4+3*n+2*(T+1)) := by
  have hn : n≤2^n := (Nat.lt_two_pow_self).le
  have ht : 3^(T+1)≤(2^2)^(T+1) := Nat.pow_le_pow_left (by norm_num) _
  have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hn 3)) ht
  have he : 16*(2^n)^3*(2^2)^(T+1)=2^(4+3*n+2*(T+1)) := by
    calc
      _ = 2^4*(2^n)^3*(2^2)^(T+1) := rfl
      _ = _ := by rw [←pow_mul,←pow_mul,←pow_add,←pow_add]; congr 1; ring
  exact hh.trans_eq he

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma badRow_some {n : ℕ} (rows : List (Row n)) (c : Fin n → ℚ) (r : Row n)
    (hr : badRow rows c=some r) : r∈rows ∧ r.bound < r.value c := by
  have hb := List.find?_some (p:=fun q : Row n => decide (q.bound<q.value c)) hr
  exact ⟨List.mem_of_find?_eq_some hr,of_decide_eq_true hb⟩

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Grid
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility
open scoped Matrix

lemma onGrid_den (D : ℕ) (hD : 0<D) (q : ℚ) (h : OnGrid D q) : q.den≤D := by
  obtain ⟨z,rfl⟩ := h
  have hh := Rat.den_dvd z (D:ℤ)
  rw [←Rat.intCast_div_eq_divInt] at hh
  simp only [Int.cast_natCast] at hh
  exact Nat.le_of_dvd hD (Int.natCast_dvd_natCast.mp hh)

lemma gridShape_onGrid {n : ℕ} (D : ℕ) (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    OnGrid D (gridShape D A i j) := by
  by_cases hij : i=j
  · subst j
    refine ⟨⌊(D:ℚ)*A i i⌋+(n:ℤ),?_⟩
    simp only [gridShape,Matrix.add_apply,gridMatrix,gridFloor,Matrix.smul_apply,
      Matrix.one_apply_eq,smul_eq_mul,mul_one,Fintype.card_fin,Int.cast_add,Int.cast_natCast]
    exact (add_div _ _ _).symm
  · refine ⟨⌊(D:ℚ)*A i j⌋,?_⟩
    simp [gridShape,gridMatrix,gridFloor,hij]

lemma initial_onGrid (n D R : ℕ) (hD : 0<D) (i j : Fin n) :
    OnGrid D ((Ellipsoid.initialState n (R:ℚ)).shape i j) := by
  have hDq : (D:ℚ)≠0 := by exact_mod_cast hD.ne'
  by_cases hij : i=j
  · subst j
    refine ⟨(D:ℤ)*(R:ℤ)^2,?_⟩
    simp only [initialState,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,
      Int.cast_mul,Int.cast_pow,Int.cast_natCast]
    field_simp
  · refine ⟨0,?_⟩
    simp [initialState,hij]

lemma iterate_onGrid {n : ℕ} (D : ℕ) (rows : List (Row n)) (S : State n)
    (hS : ∀ i j,OnGrid D (S.shape i j)) (t : ℕ) :
    ∀ i j,OnGrid D ((iterate D rows S t).shape i j) := by
  induction t with
  | zero => exact hS
  | succ t ih =>
    intro i j
    simp only [iterate,advance]
    split
    · exact ih i j
    · split_ifs
      · exact ih i j
      · exact gridShape_onGrid D _ i j

lemma numerator_bound (q : ℚ) (D K : ℕ) (hd : q.den≤D) (hq : |q|≤(K:ℚ)) :
    q.num.natAbs≤K*D := by
  have he : (q.num.natAbs:ℚ)=|q| *(q.den:ℚ) := by
    have hm : (q.num:ℚ)=q*(q.den:ℚ) :=
      (div_eq_iff (by exact_mod_cast q.den_nz)).mp (Rat.num_div_den q)
    rw [Nat.cast_natAbs,Int.cast_abs,hm,abs_mul,abs_of_nonneg (by positivity : (0:ℚ)≤q.den)]
  have hh : (q.num.natAbs:ℚ)≤(K:ℚ)*(D:ℚ) := by
    rw [he]
    exact mul_le_mul hq (by exact_mod_cast hd) (by positivity) (by positivity)
  exact_mod_cast hh

theorem iterate_shape_height (n T R r : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (hRr : R≤2^r) (t : ℕ) (ht : t≤T) (i j : Fin n) :
    let q := (iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j
    q.den≤2^(4+3*n+2*(T+1)) ∧
    q.num.natAbs≤2^(T+2*r+(4+3*n+2*(T+1))) := by
  dsimp only
  have hD := gridDenominator_pos n T (by omega)
  have hg := iterate_onGrid (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ))
    (initial_onGrid n _ R hD) t i j
  have hd := onGrid_den _ hD _ hg
  refine ⟨hd.trans (gridDenominator_size n T),?_⟩
  have hv := iterate_shape_entry_bound_s238 n T R rows hn hR t ht i j
  have hv' : |(iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j|
      ≤((2^t*R^2:ℕ):ℚ) := by exact_mod_cast hv
  have hnum := numerator_bound _ _ _ hd hv'
  have hpow : 2^t*R^2≤2^(T+2*r) := by
    calc
      _ ≤2^T*(2^r)^2 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) ht)
        (Nat.pow_le_pow_left hRr 2)
      _ = _ := by rw [←pow_mul,←pow_add]; congr 1; omega
  exact hnum.trans ((Nat.mul_le_mul hpow (gridDenominator_size n T)).trans_eq (pow_add _ _ _).symm)

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_VectorHeight
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.boundedRationalDecide_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.finalFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.iterate_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.selectFace_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.state_eq _root_.OAI.MetricKMedianRecovery.Ellipsoid.Stored.weakSolve_eq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Ellipsoid
open Matrix RationalLinearFeasibility RationalHeight
open scoped Matrix BigOperators

lemma mulVec_height {n h a : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (hH : ∀ i j,Height (H i j) h) (hv : ∀ i,Height (v i) a) (i : Fin n) :
    Height ((H *ᵥ v) i) (vectorHeight n h a) := by
  simpa only [Matrix.mulVec,dotProduct,Fintype.card_fin,vectorHeight] using
    RationalHeight.sum (fun j => H i j*v j) (h+a) (fun j => (hH i j).mul (hv j))

lemma rationalQuad_height {n h a : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (hH : ∀ i j,Height (H i j) h) (hv : ∀ i,Height (v i) a) :
    Height (rationalQuad H v) (quadHeight n h a) := by
  simpa only [rationalQuad,dotProduct,Fintype.card_fin,quadHeight] using
    RationalHeight.sum (fun i => v i*(H *ᵥ v) i) (a+vectorHeight n h a)
      (fun i => (hv i).mul (mulVec_height H v hH hv i))

lemma rationalRootUpper_height {q : ℚ} {b n : ℕ} (hq : Height q b) (hn : 0<n) :
    Height (rationalRootUpper (32*n) q) (2*b+2*(5+n)+1) := by
  have hD : 32*n≤2^(5+n) := by
    rw [pow_add]
    exact Nat.mul_le_mul_left 32 (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  exact RationalHeight.sqrtFraction q.num.natAbs q.den (32*n) b (5+n)
    hq.1 hq.2 hD q.den_pos (by omega)

lemma center_increment_height {n h a : ℕ} (H : Matrix (Fin n) (Fin n) ℚ) (v : Fin n → ℚ)
    (hH : ∀ i j,Height (H i j) h) (hv : ∀ i,Height (v i) a) (hn : 0<n) (i : Fin n) :
    Height ((1/(((n:ℚ)+1)*rationalRootUpper (32*n) (rationalQuad H v)))*(H *ᵥ v) i)
      (incrementHeight n h a) := by
  have hroot := rationalRootUpper_height (rationalQuad_height H v hH hv) hn
  have hd : Height ((n:ℚ)+1) (n+1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using RationalHeight.natCast (n+1) (n+1)
      (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n+1)))
  simpa only [one_div,rootHeight,incrementHeight] using
    (hd.mul hroot).inv.mul (mulVec_height H v hH hv i)

lemma iterate_shape_Height (n T R r : ℕ) (rows : List (Row n)) (hn : 2≤n) (hR : 1≤R)
    (hRr : R≤2^r) (t : ℕ) (ht : t≤T) (i j : Fin n) :
    Height ((iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).shape i j)
      (storedShapeHeight n T r) := by
  have hh := iterate_shape_height n T R r rows hn hR hRr t ht i j
  exact ⟨hh.2,hh.1.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [storedShapeHeight]; omega))⟩

theorem iterate_center_height (n T R r a : ℕ) (rows : List (Row n))
    (hn : 2≤n) (hR : 1≤R) (hRr : R≤2^r)
    (hrows : ∀ v∈rows, ∀ i,Height (v.coeff i) a) (t : ℕ) (ht : t≤T) (i : Fin n) :
    Height ((iterate (gridDenominator n T) rows (Ellipsoid.initialState n (R:ℚ)) t).center i)
      (t*(incrementHeight n (storedShapeHeight n T r) a+1)) := by
  induction t with
  | zero => exact RationalHeight.zero _
  | succ t ih =>
    have hc := ih (by omega)
    have hs := iterate_shape_Height n T R r rows hn hR hRr t (by omega)
    simp only [iterate,advance]
    split
    · exact hc.mono (Nat.mul_le_mul_right _ (by omega))
    · rename_i v hv
      split_ifs
      · exact hc.mono (Nat.mul_le_mul_right _ (by omega))
      · have hi := center_increment_height _ v.coeff hs
          (hrows v ((badRow_some _ _ _ hv).1)) (by omega) i
        have hh := hc.sub hi
        simp only [rationalStepCenter,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,Fintype.card_fin]
        convert hh using 1
        all_goals try with_reducible_and_instances rfl
        ring

end MetricKMedianRecovery.Ellipsoid

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Pack7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid RationalHeight
namespace BinaryEllipsoidIteration
open RationalMatrix BinaryEllipsoidAdvance

lemma pack_length (n T R : ℕ) (rs : List (Row n)) :
    (pack n T R rs).length=2*T+2*R.bits.length+
      (BinaryEllipsoidAdvance.pack (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ))).length+2 := by
  simp only [pack,pairBits_length,List.length_replicate]; omega
lemma advance_pack_length {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    (BinaryEllipsoidAdvance.pack D rs S).length=
      2*n.bits.length+2*D.bits.length+2*(BinaryRow.rowsEncode rs).length+
        2*(RationalMatrix.encode S.shape).length+(rowEncode S.center).length+4 := by
  simp only [BinaryEllipsoidAdvance.pack,stateEncode,pairBits_length]; omega
lemma coeff_length {n : ℕ} {rs : List (Row n)} {r : Row n} (hr : r∈rs) (i : Fin n) :
    (BinaryRational.encode (r.coeff i)).length≤(BinaryRow.rowsEncode rs).length := by
  have h₁ := WordList.length_member_le_encode (List.mem_ofFn.mpr ⟨i,rfl⟩ :
    BinaryRational.encode (r.coeff i)∈List.ofFn (fun j=>BinaryRational.encode (r.coeff j)))
  rw [←rowEncode_eq] at h₁
  have h₂ := WordList.length_member_le_encode (List.mem_map.mpr ⟨r,hr,rfl⟩ :
    BinaryRow.encode r∈rs.map BinaryRow.encode)
  change (BinaryRow.encode r).length≤(BinaryRow.rowsEncode rs).length at h₂
  simp only [BinaryRow.encode,pairBits_length] at h₂
  omega

lemma input_bounds (n T R : ℕ) (rs : List (Row n)) :
    let L := (pack n T R rs).length
    n≤ L ∧ T≤ L ∧ R≤2^L ∧
    (∀ r∈rs,∀ i,Height (r.coeff i) L) ∧
    2*n.bits.length+2*(gridDenominator n T).bits.length+2*(BinaryRow.rowsEncode rs).length+4≤ L := by
  dsimp only
  have hl := pack_length n T R rs
  have hp := advance_pack_length (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ))
  have hn := RationalMatrix.dimension_bound (Ellipsoid.initialState n (R:ℚ)).shape
  have hR : R≤2^(pack n T R rs).length := by
    apply Nat.le_of_lt
    apply Nat.size_le.mp
    rw [←Nat.size_eq_bits_len]
    omega
  refine ⟨by omega,by omega,hR,?_,by omega⟩
  intro r hr i
  exact (BinaryRational.input_height (r.coeff i)).mono ((coeff_length hr i).trans (by omega))

lemma shapePoly_eval (L : ℕ) : shapePoly.eval L=storedShapeHeight L L L := by
  simp only [shapePoly,storedShapeHeight,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
lemma incrementPoly_eval (L : ℕ) : incrementPoly.eval L=incrementHeight L (storedShapeHeight L L L) L := by
  simp only [incrementPoly,quadPoly,vectorPoly,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,shapePoly_eval,
    incrementHeight,rootHeight,quadHeight,vectorHeight]
lemma centerPoly_eval (L : ℕ) : centerPoly.eval L=L*(incrementHeight L (storedShapeHeight L L L) L+1) := by
  simp only [centerPoly,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,
    Polynomial.eval_one,incrementPoly_eval]
lemma storagePoly_eval (L : ℕ) : storagePoly.eval L=
    10*(L+1)+2*L*(2*(L*(6*shapePoly.eval L+14))+2)+L*(6*centerPoly.eval L+14) := by
  simp only [storagePoly,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X,Polynomial.eval_one]
lemma shape_mono {n T r L : ℕ} (hn : n≤ L) (hT : T≤ L) (hr : r≤ L) :
    storedShapeHeight n T r≤ storedShapeHeight L L L := by
  unfold storedShapeHeight
  omega
lemma increment_mono {n h a N H A : ℕ} (hn : n≤ N) (hh : h≤ H) (ha : a≤ A) :
    incrementHeight n h a≤ incrementHeight N H A := by
  unfold incrementHeight rootHeight quadHeight vectorHeight
  gcongr
lemma vector_encode_height {n b : ℕ} (v : Fin n → ℚ) (hv : ∀ i,Height (v i) b) :
    (rowEncode v).length≤ n*(6*b+14) := by
  rw [rowEncode_eq]
  have hh := WordList.encode_le_bound (List.ofFn (fun i=>BinaryRational.encode (v i))) (3*b+6) (by
    intro w hw
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
    exact BinaryRational.encode_height (hv i))
  simp only [List.length_ofFn] at hh
  convert hh using 1 <;> first | rfl | ring

lemma iterate_length_bound_s238_oai (n T R : ℕ) (rs : List (Row n)) (hn : 2≤ n) (hR : 1≤ R)
    (t : ℕ) (ht : t≤ T) :
    (BinaryEllipsoidAdvance.pack (gridDenominator n T) rs
      (Ellipsoid.iterate (gridDenominator n T) rs (Ellipsoid.initialState n (R:ℚ)) t)).length≤
        storagePoly.eval (pack n T R rs).length := by
  let L := (pack n T R rs).length
  obtain ⟨hnL,hTL,hRL,hrows,hstatic⟩ := input_bounds n T R rs
  change n≤ L at hnL
  change T≤ L at hTL
  change R≤2^L at hRL
  change ∀ r∈rs,∀ i,Height (r.coeff i) L at hrows
  change _≤ L at hstatic
  have hs := iterate_shape_Height n T R L rs hn hR hRL t ht
  have hc := iterate_center_height n T R L L rs hn hR hRL hrows t ht
  have hm : storedShapeHeight n T L≤ shapePoly.eval L := by
    rw [shapePoly_eval]
    exact shape_mono hnL hTL le_rfl
  have hcm : t*(incrementHeight n (storedShapeHeight n T L) L+1)≤ centerPoly.eval L := by
    rw [centerPoly_eval]
    exact Nat.mul_le_mul (ht.trans hTL) (Nat.add_le_add_right
      (increment_mono hnL (shape_mono hnL hTL le_rfl) le_rfl) 1)
  have hshape := RationalMatrix.encode_height (Ellipsoid.iterate (gridDenominator n T) rs
      (Ellipsoid.initialState n (R:ℚ)) t).shape (fun i j=>(hs i j).mono hm)
  have hcenc := vector_encode_height (Ellipsoid.iterate (gridDenominator n T) rs
      (Ellipsoid.initialState n (R:ℚ)) t).center (fun i=>(hc i).mono hcm)
  have hm' : n*(2*(n*(6*shapePoly.eval L+14))+2)≤ L*(2*(L*(6*shapePoly.eval L+14))+2) := by gcongr
  have hc' : n*(6*centerPoly.eval L+14)≤ L*(6*centerPoly.eval L+14) := Nat.mul_le_mul_right _ hnL
  rw [advance_pack_length,storagePoly_eval]
  change _≤10*(L+1)+2*L*(2*(L*(6*shapePoly.eval L+14))+2)+L*(6*centerPoly.eval L+14)
  have ha := hshape.trans hm'
  have hb := hcenc.trans hc'
  simp only [Nat.mul_assoc]
  omega

end BinaryEllipsoidIteration
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.iterate_length_bound_s238_oai
