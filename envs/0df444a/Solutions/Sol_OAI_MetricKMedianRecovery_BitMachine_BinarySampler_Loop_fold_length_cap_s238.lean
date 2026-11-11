-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:32.955249+00:00
-- url     : https://prove2.me/submissions/5b6f6462-ec3e-4f14-9c05-c0143ce483b5

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K021
import Definitions.Def_Q238K022

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

lemma Height.div {q r : ℚ} {b c : ℕ} (hq : Height q b) (hr : Height r c) :
    Height (q/r) (b+c) := by
  rw [div_eq_mul_inv]
  exact hq.mul hr.inv

lemma Height.pow {q : ℚ} {b : ℕ} (hq : Height q b) (k : ℕ) : Height (q^k) (k*b) := by
  induction k with
  | zero => simpa using natCast 1 0 (by norm_num)
  | succ k ih =>
    rw [pow_succ,Nat.succ_mul]
    exact ih.mul hq

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
lemma entry_length_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    (BinaryRational.encode (A i j)).length≤(encode A).length := by
  have hr := length_member_le_encode (List.mem_ofFn.mpr ⟨i,rfl⟩ : rowEncode (A i)∈List.ofFn (fun i=>rowEncode (A i)))
  have he := length_member_le_encode (List.mem_ofFn.mpr ⟨j,rfl⟩ : BinaryRational.encode (A i j)∈List.ofFn (fun j=>BinaryRational.encode (A i j)))
  rw [←rowEncode_eq] at he
  exact he.trans hr
lemma input_height {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    RationalHeight.Height (A i j) (encode A).length :=
  (BinaryRational.input_height (A i j)).mono (entry_length_bound A i j)
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Fuel
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalHeight
lemma Height.min {q r : ℚ} {a : ℕ} (hq : Height q a) (hr : Height r a) :
    Height (min q r) a := by
  rcases le_total q r with h|h
  · simpa only [min_eq_left h] using hq
  · simpa only [min_eq_right h] using hr
end MetricKMedianRecovery.RationalHeight

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_FinSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFinSet
open WordOperations WordList
variable {n : ℕ}
lemma values_sort (S : Finset (Fin n)) : (values S).sort (·≤·)=(S.sort (·≤·)).map Fin.val := by
  let f : Fin n ↪ ℕ := ⟨Fin.val,Fin.val_injective⟩
  have hh := Finset.map_sort f S (·≤·) (·≤·) (fun a _ b _=>show a≤b↔a.val≤b.val from Iff.rfl)
  simpa only [f,Finset.map_eq_image,values,Function.Embedding.coeFn_mk] using hh.symm
lemma encode_eq (S : Finset (Fin n)) : encode S=WordList.encode ((S.sort (·≤·)).map (fun i=>i.val.bits)) := by
  rw [encode,BinaryNatSet.encode,BinaryNatSet.pack,values_sort,List.map_map]
  rfl
end MetricKMedianRecovery.BitMachine.BinaryFinSet

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_LabelSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.WordList
lemma member_length {ws : List (List Bool)} {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>exact False.elim (List.not_mem_nil hw)
  | cons v vs ih=>
    rw [encode,length_cons]
    rcases List.mem_cons.mp hw with rfl|hw
    · omega
    · have h:=ih hw
      omega
end MetricKMedianRecovery.BitMachine.WordList

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerDraw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
lemma height_max {q r : ℚ} {H : ℕ} (hq : Height q H) (hr : Height r H) : Height (max q r) H := by
  rcases le_total q r with h|h
  · simpa only [max_eq_right h] using hr
  · simpa only [max_eq_left h] using hq
lemma height_minimum (qs : List ℚ) (H : ℕ) (hh : ∀ q∈qs,Height q H) : Height (RationalMin.minimum qs) H := by
  have hf (xs : List ℚ) (a : ℚ) (ha : Height a H) (hx : ∀ q∈xs,Height q H) : Height (xs.foldl min a) H := by
    induction xs generalizing a with
    | nil=>exact ha
    | cons q xs ih=>
      exact ih _ (ha.min (hx q (by simp))) (fun r hr=>hx r (by simp only [List.mem_cons];exact Or.inr hr))
  apply hf _ _ _ hh
  cases qs with
  | nil=>exact RationalHeight.zero H
  | cons q qs=>exact hh q (by simp)
lemma height_nat (x H : ℕ) (hx : x≤H) : Height (x:ℚ) H :=
  RationalHeight.natCast x H (hx.trans (Nat.le_of_lt (Nat.lt_two_pow_self (n:=H))))
lemma population_height (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) (P : ℚ) (m H : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hn : n≤H) (hm : m≤H) (w : Fin n) :
    Height (BinaryPopulation.radiusQ P m (BinaryPopulation.distanceList δ D w)) (3*H) := by
  apply height_minimum
  intro q hq
  obtain ⟨d,hdmem,rfl⟩:=List.mem_map.mp hq
  apply height_max
  · obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hdmem
    exact (hd w z).mono (by omega)
  · apply (hP.div ((height_nat m H hm).mul (height_nat _ H ?_))).mono (by omega)
    have hl : (BinaryPopulation.distanceList δ D w).length=D.card := by
      simp only [BinaryPopulation.distanceList,List.length_map,Finset.length_sort]
    exact (List.length_filter_le _ _).trans (hl.le.trans ((Finset.card_le_univ D).trans (by simpa using hn)))
lemma nearest_height (δ : Fin n→Fin n→ℚ) (s : State n) (w : Fin n) (H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hs : s.Height K) (r : ℚ) (hr : nearestLeaf δ s w=some r) :
    Height r (H+K+1) := by
  unfold nearestLeaf at hr
  split_ifs at hr with he
  cases Option.some.inj hr
  apply height_minimum
  intro q hq
  obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hq
  exact (hd w z.1).add (hs z hz)
lemma menu_height (δ : Fin n→Fin n→ℚ) (D : Finset (Fin n)) (P κ : ℚ) (m M E J H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hκ : Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (s : State n) (hs : s.Height K) (w : Fin n) (e : Sampling.Entry M E J) (R : ℚ)
    (hr : menuRadius δ D P κ m M E J s w e=some R) : Height R (K+heightIncrement H) := by
  rcases e with j | (e | j)
  · cases Option.some.inj hr
    rw [←Nat.cast_succ]
    apply (((height_nat (j.val+1) H (by omega)).mul hκ).mul (population_height δ D P m H hd hP hn hm w)).mono
    dsimp [heightIncrement] <;> nlinarith
  · simp only [menuRadius] at hr
    obtain ⟨r,hr0,he⟩:=Option.map_eq_some_iff.mp hr
    rw [←he]
    have h1 : Height (1:ℚ) 1 := by norm_num [RationalHeight.Height]
    have hh := (nearest_height δ s w H K hd hs r hr0).div ((h1.add hκ).pow e.val)
    apply hh.mono
    have he : e.val≤H := le_trans (Nat.le_of_lt_succ e.isLt) hE
    have hp := Nat.mul_le_mul_right (1+H+1) he
    dsimp [heightIncrement] <;> nlinarith
  · cases Option.some.inj hr
    rw [←Nat.cast_succ]
    apply (((height_nat (j.val+1) H (by omega)).mul hκ).mul (population_height δ D P m H hd hP hn hm w)).mono
    dsimp [heightIncrement] <;> nlinarith
lemma retain_height (m : ℕ) (s t : State n) (K : ℕ) (hs : s.Height K) (ht : retain m s=some t) : t.Height K := by
  unfold retain at ht
  split_ifs at ht
  cases Option.some.inj ht
  exact hs
lemma update_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J H K : ℕ)
    (hd : ∀ i j,Height (δ i j) H) (hP : Height P H) (hκ : Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (s t : State n) (hs : s.Height K) (a : Sampling.Action D M E J)
    (ht : update δ D F S Δ P κ m M E J (some s) a=some t) : t.Height (K+heightIncrement H) := by
  simp only [update] at ht
  split_ifs at ht
  rcases a with u | (w | ⟨w,e⟩)
  · contradiction
  · dsimp only at ht
    split_ifs at ht
    apply retain_height m _ t _ _ ht
    exact fun z hz=>(hs z hz).mono (by omega)
  · dsimp only at ht
    cases he : menuRadius δ D P κ m M E J s w e with
    | none=>simp only [he] at ht;contradiction
    | some R=>
      simp only [he] at ht
      split_ifs at ht
      apply retain_height m _ t _ _ ht
      intro z hz
      simp only [State.add,List.mem_append,List.mem_singleton] at hz
      rcases hz with hz|rfl
      · exact (hs z hz).mono (by omega)
      · exact menu_height δ D P κ m M E J H K hd hP hκ hn hm hM hE hJ s hs w e R he
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplingPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open BitMachine RationalHeight
variable {n : ℕ}
lemma initial_height (K : ℕ) : (State.initial (n:=n)).Height K := by simp [State.initial,State.Height]
lemma initial_bounded (m : ℕ) : (State.initial (n:=n)).Bounded m := by simp [State.initial,State.Bounded]
lemma retain_bounded (m : ℕ) (s t : State n) (ht : retain m s=some t) : t.Bounded m := by
  unfold retain at ht
  split_ifs at ht with h
  cases Option.some.inj ht
  exact h
lemma update_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ)
    (s : Option (State n)) (a : Sampling.Action D M E J) (t : State n)
    (ht : update δ D F S Δ P κ m M E J s a=some t) : t.Bounded m := by
  cases s with
  | none=>simp only [update] at ht;contradiction
  | some s=>
    simp only [update] at ht
    split_ifs at ht
    rcases a with u | (w | ⟨w,e⟩)
    · contradiction
    · dsimp only at ht
      split_ifs at ht
      exact retain_bounded m _ t ht
    · dsimp only at ht
      cases he : menuRadius δ D P κ m M E J s w e with
      | none=>simp only [he] at ht;contradiction
      | some R=>
        simp only [he] at ht
        split_ifs at ht
        exact retain_bounded m _ t ht
end MetricKMedianRecovery.RationalSampling
namespace MetricKMedianRecovery.BitMachine.BinarySamplingState
open WordOperations WordList RationalHeight
variable {n : ℕ}
lemma finset_length (D : Finset (Fin n)) : (BinaryFinSet.encode D).length ≤ n*(2*n+2) := by
  rw [BinaryFinSet.encode_eq]
  apply (encode_le_bound _ n ?_).trans
  · simp only [List.length_map,Finset.length_sort]
    exact Nat.mul_le_mul_right _ ((Finset.card_le_univ D).trans_eq (Fintype.card_fin n))
  · intro w hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact (Indices.bits_length_le i.val).trans (Nat.le_of_lt i.isLt)
lemma leaf_length (z : Fin n×ℚ) (K : ℕ) (hz : Height z.2 K) : (BinarySamplingReference.leafBits z.1 z.2).length ≤ 2*n+3*K+7 := by
  have hn:=(Indices.bits_length_le z.1.val).trans (Nat.le_of_lt z.1.isLt)
  have hq:=BinaryRational.encode_height hz
  simp only [BinarySamplingReference.leafBits,pairBits_length]
  omega
lemma leaves_length (s : RationalSampling.State n) (m K : ℕ) (hs : s.Height K) (hm : s.leaves.length ≤ m) :
    (BinaryNearestLeaf.leavesBits s.leaves).length ≤ m*(4*n+6*K+16) := by
  unfold BinaryNearestLeaf.leavesBits
  apply (encode_le_bound _ (2*n+3*K+7) ?_).trans
  · simp only [List.length_map]
    rw [show 2*(2*n+3*K+7)+2=4*n+6*K+16 by ring]
    exact Nat.mul_le_mul_right _ hm
  · intro w hw
    obtain ⟨z,hz,rfl⟩:=List.mem_map.mp hw
    exact leaf_length z K (hs z hz)
lemma encode_length (s : RationalSampling.State n) (m K : ℕ) (hs : s.Height K) (hm : s.leaves.length ≤ m) :
    (encode s).length ≤ 2*n*(2*n+2)+m*(4*n+6*K+16)+1 := by
  have ht:=finset_length s.deleted
  have hl:=leaves_length s m K hs hm
  simp only [encode,pairBits_length]
  nlinarith
lemma option_length (s : Option (RationalSampling.State n)) (m K : ℕ)
    (hs : ∀ z,s=some z→z.Height K) (hm : ∀ z,s=some z→z.leaves.length ≤ m) :
    (optionBits s).length ≤ 4*n*(2*n+2)+2*m*(4*n+6*K+16)+4 := by
  cases s with
  | none=>simp [optionBits,WordList.encode]
  | some s=>
    have hh:=encode_length s m K (hs s rfl) (hm s rfl)
    simp only [optionBits,Option.toList_some,List.map_cons,List.map_nil,WordList.encode,length_cons,List.length_nil]
    nlinarith
end MetricKMedianRecovery.BitMachine.BinarySamplingState

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
lemma next_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b H K : ℕ)
    (hd : ∀ i j,RationalHeight.Height (δ i j) H) (hP : RationalHeight.Height P H) (hκ : RationalHeight.Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (s : Option (State n)) (hs : ∀ z,s=some z→z.Height K) (seed : Fin b→Bool) (t : State n)
    (ht : next δ D F S Δ P κ m M E J b s seed=some t) : t.Height (K+heightIncrement H) := by
  unfold next at ht
  cases s with
  | none=>simp [update] at ht
  | some s=>exact update_height δ D F S Δ P κ m M E J H K hd hP hκ hn hm hM hE hJ s t (hs s rfl) _ ht
lemma fold_next_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b H K : ℕ)
    (hd : ∀ i j,RationalHeight.Height (δ i j) H) (hP : RationalHeight.Height P H) (hκ : RationalHeight.Height κ H)
    (hn : n≤H) (hm : m≤H) (hM : M≤H) (hE : E≤H) (hJ : J≤H)
    (seeds : List (Fin b→Bool)) (s : Option (State n)) (hs : ∀ z,s=some z→z.Height K) (t : State n)
    (ht : seeds.foldl (next δ D F S Δ P κ m M E J b) s=some t) : t.Height (K+seeds.length*heightIncrement H) := by
  induction seeds generalizing K s with
  | nil=>simpa only [List.length_nil,Nat.zero_mul,Nat.add_zero] using hs t ht
  | cons seed seeds ih=>
    rw [List.foldl_cons] at ht
    have hh := ih (K+heightIncrement H) _ (fun z hz=>next_height δ D F S Δ P κ m M E J b H K hd hP hκ hn hm hM hE hJ s hs seed z hz) ht
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    simp only [List.length_cons] <;> ring
lemma fold_next_bounded (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ)
    (seeds : List (Fin b→Bool)) (s : Option (State n)) (hs : ∀ z,s=some z→z.Bounded m) (t : State n)
    (ht : seeds.foldl (next δ D F S Δ P κ m M E J b) s=some t) : t.Bounded m := by
  induction seeds generalizing s with
  | nil=>exact hs t ht
  | cons seed seeds ih=>exact ih _ (fun z hz=>update_bounded δ D F S Δ P κ m M E J s _ z hz) ht
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_SamplerResources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySampler.Loop
open WordOperations WordList BinaryArithmetic RationalHeight
open BinaryOpeningPayment (field field_encode)
variable {n : ℕ}
lemma config_height (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J : ℕ) :
    let N:=(config δ D F S Δ P κ m M E J).length
    (∀ i j,Height (δ i j) N) ∧ Height P N ∧ Height κ N ∧ n≤N ∧ M≤N ∧ E≤N ∧ J≤N := by
  dsimp only
  have hd : (RationalMatrix.encode δ).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hp : (BinaryRational.encode P).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hk : (BinaryRational.encode κ).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hw : (BinaryMenu.weights M E J).length≤(config δ D F S Δ P κ m M E J).length := member_length (by simp)
  have hM : M≤(BinaryMenu.weights M E J).length := by
    simpa only [BinaryMenu.weights,List.length_replicate] using (member_length (show List.replicate M true∈[List.replicate M true,List.replicate E true,List.replicate J true] by simp))
  have hE : E≤(BinaryMenu.weights M E J).length := by
    simpa only [BinaryMenu.weights,List.length_replicate] using (member_length (show List.replicate E true∈[List.replicate M true,List.replicate E true,List.replicate J true] by simp))
  have hJ : J≤(BinaryMenu.weights M E J).length := by
    simpa only [BinaryMenu.weights,List.length_replicate] using (member_length (show List.replicate J true∈[List.replicate M true,List.replicate E true,List.replicate J true] by simp))
  exact ⟨fun i j=>(RationalMatrix.input_height δ i j).mono hd,(BinaryRational.input_height P).mono hp,
    (BinaryRational.input_height κ).mono hk,(RationalMatrix.dimension_bound δ).trans hd,hM.trans hw,hE.trans hw,hJ.trans hw⟩
lemma runPack_bounds (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) :
    let N:=(runPack (config δ D F S Δ P κ m M E J) m b seeds).length
    (∀ i j,Height (δ i j) N) ∧ Height P N ∧ Height κ N ∧ n≤N ∧ m≤N ∧ M≤N ∧ E≤N ∧ J≤N ∧ seeds.length≤N := by
  dsimp only
  have hc : (config δ D F S Δ P κ m M E J).length≤(runPack (config δ D F S Δ P κ m M E J) m b seeds).length := member_length (by simp)
  have hm : m≤(runPack (config δ D F S Δ P κ m M E J) m b seeds).length := by
    simpa only [runPack,List.length_replicate] using (member_length (show List.replicate m true∈[config δ D F S Δ P κ m M E J,List.replicate m true,List.replicate b true,encode (seeds.map List.ofFn)] by simp))
  have ht : seeds.length≤(encode (seeds.map List.ofFn)).length := by simpa only [List.length_map] using length_le_encode (seeds.map List.ofFn)
  have ht2 : (encode (seeds.map List.ofFn)).length≤(runPack (config δ D F S Δ P κ m M E J) m b seeds).length := member_length (by simp)
  obtain ⟨hd,hp,hk,hn,hM,hE,hJ⟩:=config_height δ D F S Δ P κ m M E J
  exact ⟨fun i j=>(hd i j).mono hc,hp.mono hc,hk.mono hc,hn.trans hc,hm,hM.trans hc,hE.trans hc,hJ.trans hc,ht.trans ht2⟩
lemma length_cap (s : Option (RationalSampling.State n)) (m H t : ℕ) (hn : n≤H) (hm : m≤H) (ht : t≤H)
    (hs : ∀ z,s=some z→z.Height (t*RationalSampling.heightIncrement H)) (hb : ∀ z,s=some z→z.Bounded m) :
    (BinarySamplingState.optionBits s).length ≤ capPoly.eval H := by
  have hh:=BinarySamplingState.option_length s m (t*RationalSampling.heightIncrement H) hs (fun z hz=>(hb z hz).1)
  have hK : t*RationalSampling.heightIncrement H≤H*(10*(H+1)^2) := Nat.mul_le_mul_right _ ht
  have hl : 4*n*(2*n+2)+2*m*(4*n+6*(t*RationalSampling.heightIncrement H)+16)+4≤
      4*H*(2*H+2)+2*H*(4*H+6*(H*(10*(H+1)^2))+16)+4 := by gcongr
  apply hh.trans (hl.trans ?_)
  simp only [capPoly,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  nlinarith [sq_nonneg (H:ℤ)]
lemma fold_length_cap_s238_oai (δ : Fin n→Fin n→ℚ) (D F S : Finset (Fin n)) (Δ P κ : ℚ) (m M E J b : ℕ) (seeds : List (Fin b→Bool)) (j : ℕ) :
    (BinarySamplingState.optionBits ((seeds.take j).foldl (RationalSampling.next δ D F S Δ P κ m M E J b) (some RationalSampling.State.initial))).length≤
      capPoly.eval (runPack (config δ D F S Δ P κ m M E J) m b seeds).length := by
  obtain ⟨hd,hp,hk,hn,hm,hM,hE,hJ,ht⟩:=runPack_bounds δ D F S Δ P κ m M E J b seeds
  apply length_cap _ m _ (seeds.take j).length hn hm ((by simp only [List.length_take];exact Nat.min_le_right _ _ : (seeds.take j).length ≤ seeds.length).trans ht)
  · intro z hz
    have hh:=RationalSampling.fold_next_height δ D F S Δ P κ m M E J b _ 0 hd hp hk hn hm hM hE hJ (seeds.take j)
      (some RationalSampling.State.initial) (fun t ht=>by cases Option.some.inj ht;exact RationalSampling.initial_height 0) z hz
    simpa only [Nat.zero_add] using hh
  · intro z hz
    exact RationalSampling.fold_next_bounded δ D F S Δ P κ m M E J b (seeds.take j) (some RationalSampling.State.initial)
      (fun t ht=>by cases Option.some.inj ht;exact RationalSampling.initial_bounded m) z hz
end MetricKMedianRecovery.BitMachine.BinarySampler.Loop

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Loop.fold_length_cap_s238_oai
