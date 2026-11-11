-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T00:15:56.028135+00:00
-- url     : https://prove2.me/submissions/4f03f17d-c37a-4240-9f98-c2f37705fd76

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K050
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseRun_finish_bound_s238

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
-- module Solutions.Q238_KM.KMedianRecovery_Geometry_NearestHeight
attribute [-instance] _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.EffectiveOpenability
open RationalHeight RationalOpenability
lemma nearest_height {m d a : ℕ} (distance : Fin m → Fin d → ℚ)
    (hd : ∀ f j,Height (distance f j) a) (W : Finset (Fin m)) (j : Fin d) :
    Height (nearest distance W j) a := by
  unfold nearest
  split_ifs with hW
  · obtain ⟨f,hf,he⟩ := Finset.exists_mem_eq_inf' hW (fun f => distance f j)
    rw [he]
    exact hd f j
  · exact RationalHeight.zero _
end MetricKMedianRecovery.EffectiveOpenability

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_Clipped
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalPhase
open EffectiveOpenability OrdinaryProducer

lemma advance_get {m d : ℕ} (distance : Fin m → Fin d → ℚ) (v : ℚ)
    (s : State m d) (j : Fin d) :
    (advance distance v s).budget[j] = if active distance v s.phase s.opened j then
      clipped distance v ((1+v^2)*s.phase) s.opened j else s.budget[j] := by
  simp only [advance,Fin.getElem_fin,Vector.getElem_ofFn]

end MetricKMedianRecovery.RationalPhase

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Answer
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate

lemma member_length_le (ws : List (List Bool)) {w : List Bool} (hw : w∈ws) : w.length≤(encode ws).length := by
  induction ws with
  | nil=>simp only [List.not_mem_nil] at hw
  | cons a ws ih=>
    simp only [encode,length_cons]
    rcases List.mem_cons.mp hw with h|h
    · subst w; omega
    · have hh:=ih h; omega
lemma indices_length {m : ℕ} (fs : List (Fin m)) (hl : fs.length ≤ m) :
    (BinaryOpeningActivity.indices fs).length ≤ m*(2*m+2) := by
  apply (encode_le_bound (fs.map (fun i=>i.val.bits)) m (by
    intro w hw
    obtain ⟨i,_,rfl⟩:=List.mem_map.mp hw
    exact (Indices.bits_length_le i.val).trans (Nat.le_of_lt i.isLt))).trans
  simpa only [List.length_map] using Nat.mul_le_mul_right (2*m+2) hl
lemma finset_indices_length {m : ℕ} (W : Finset (Fin m)) :
    (BinaryOpeningActivity.indices ((subtypeList W).map Subtype.val)).length ≤ m*(2*m+2) := by
  apply indices_length
  simp only [List.length_map,subtypeList,List.length_ofFn]
  exact (Finset.card_le_univ W).trans_eq (Fintype.card_fin m)
lemma context_length_change {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W W' : Finset (Fin m))
    (v z lam : ℚ) :
    (BinaryPhaseFirst.context distance F W' v z lam).length≤
      (BinaryPhaseFirst.context distance F W v z lam).length+2*m*(2*m+2) := by
  have hh:=finset_indices_length W'
  simp only [BinaryPhaseFirst.context,length_encode,List.map_cons,List.sum_cons,List.length_cons,
    List.map_nil,List.sum_nil,List.length_nil]
  nlinarith
lemma dimensions {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : m≤(stateBits distance F v lam s).length ∧ d≤(stateBits distance F v lam s).length := by
  have hm := length_le_encode (List.ofFn (fun i : Fin m=>RationalMatrix.rowEncode (distance i)))
  have h0 := member_length_le [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode s.phase,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
      (w:=Rectangular.encode distance) (by simp only [List.mem_cons, true_or])
  have hd := length_le_encode (List.ofFn (fun j : Fin d=>BinaryRational.encode s.budget[j]))
  simp only [List.length_ofFn] at hm hd
  change _≤(BinaryPhaseFirst.context distance F s.opened v s.phase lam).length at h0
  change m≤(Rectangular.encode distance).length at hm
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  constructor <;> omega
lemma initial_budget_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (j : Fin d) :
    (BinaryRational.encode s.budget[j]).length≤(stateBits distance F v lam s).length := by
  have hh:=member_length_le (List.ofFn (fun j : Fin d=>BinaryRational.encode s.budget[j]))
    (w:=BinaryRational.encode s.budget[j]) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  omega
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFinish
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
lemma ctx_bound {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤
      (stateBits distance F v lam s).length+2*(stateBits distance F v lam s).length*(2*(stateBits distance F v lam s).length+2) := by
  let L := (stateBits distance F v lam s).length
  have hm := (dimensions distance F v lam s).1
  have hc := context_length_change distance F s.opened W v s.phase lam
  have ho : (BinaryPhaseFirst.context distance F s.opened v s.phase lam).length ≤ L := by
    simp only [L,stateBits,pairBits_length]; omega
  have hmul := Nat.mul_le_mul hm (show 2*m+2 ≤ 2*L+2 by omega)
  change (BinaryPhaseFirst.context distance F W v s.phase lam).length ≤ L+2*L*(2*L+2)
  nlinarith
end MetricKMedianRecovery.BitMachine.BinaryPhaseFinish

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
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_BidBound
attribute [-simp] _root_.OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.heightWords_encode
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate RationalHeight
open BinaryPhaseFinish
lemma context_height {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) :
    Height v (stateBits distance F v lam s).length ∧
    Height s.phase (stateBits distance F v lam s).length ∧
    ∀ f j, Height (distance f j) (stateBits distance F v lam s).length := by
  let ws := [Rectangular.encode distance,
      BinaryOpeningActivity.indices ((subtypeList s.opened).map Subtype.val),BinaryRational.encode v,
      BinaryRational.encode s.phase,BinaryRational.encode lam,BinaryRational.encode 0,[],
      List.replicate d true,BinaryOpeningActivity.indices ((subtypeList F).map Subtype.val)]
  have hc : (encode ws).length ≤ (stateBits distance F v lam s).length := by
    change (BinaryPhaseFirst.context distance F s.opened v s.phase lam).length ≤ _
    simp only [stateBits,pairBits_length]; omega
  have hv := member_length_le ws (w:=BinaryRational.encode v) (by simp only [ws,List.mem_cons,true_or,or_true])
  have hz := member_length_le ws (w:=BinaryRational.encode s.phase) (by simp only [ws,List.mem_cons,true_or,or_true])
  have hd := member_length_le ws (w:=Rectangular.encode distance) (by simp only [ws,List.mem_cons,true_or])
  refine ⟨(BinaryRational.input_height v).mono (hv.trans hc),
    (BinaryRational.input_height s.phase).mono (hz.trans hc),?_⟩
  intro f j
  have hr := member_length_le (List.ofFn (fun f : Fin m=>RationalMatrix.rowEncode (distance f)))
    (w:=RationalMatrix.rowEncode (distance f)) (List.mem_ofFn.mpr ⟨f,rfl⟩)
  have he := member_length_le (List.ofFn (fun j : Fin d=>BinaryRational.encode (distance f j)))
    (w:=BinaryRational.encode (distance f j)) (List.mem_ofFn.mpr ⟨j,rfl⟩)
  rw [RationalMatrix.rowEncode_eq] at hr
  exact (BinaryRational.input_height (distance f j)).mono (he.trans (hr.trans (hd.trans hc)))
lemma change_phase_length {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (z : ℚ) :
    (stateBits distance F v lam {s with phase:=z}).length ≤
      (stateBits distance F v lam s).length+4*(BinaryRational.encode z).length := by
  simp only [stateBits,pairBits_length,BinaryPhaseFirst.context,length_encode,List.map_cons,List.sum_cons,
    List.length_cons,List.map_nil,List.sum_nil,List.length_nil]
  omega
lemma reference_length {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) :
    (stateBits distance F v lam {s with phase:=z}).length ≤ 100*(N+1)^2 := by
  have h := change_phase_length distance F v lam s z
  have hh := BinaryRational.encode_height hz
  nlinarith
lemma clipped_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (z : ℚ) (hz : Height z (3*(N+1)^2)) (W : Finset (Fin m)) (j : Fin d) :
    (BinaryRational.encode (clipped distance v z W j)).length ≤ budgetBound.eval N := by
  let A := 3*(N+1)^2
  have hNA : N ≤ A := by dsimp only [A] <;> nlinarith
  obtain ⟨hv,_,hd⟩ := context_height distance F v lam s
  have hv' := hv.mono (hL.trans hNA)
  have h1 : Height (1:ℚ) 0 := natCast 1 0 (by norm_num)
  have h3 : Height (3:ℚ) 2 := natCast 3 2 (by norm_num)
  have ht : Height (1-3*v) (A+3) := by convert h1.sub (h3.mul hv') using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  have hn := nearest_height distance (fun f j=>(hd f j).mono (hL.trans hNA)) W j
  have hh : Height (clipped distance v z W j) (2*A+3) := by
    unfold clipped
    split_ifs
    · exact (hz.mono (by dsimp only [A]; omega)).min ((ht.mul hn).mono (by omega))
    · exact hz.mono (by dsimp only [A]; omega)
  have he := BinaryRational.encode_height hh
  simp only [budgetBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
  dsimp only [A] at he
  nlinarith
lemma run_bound_invariant {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (q : ℕ) (t : State m d)
    (hz : ∀ j ≤ q,Height ((1+v^2)^j*t.phase) (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (RationalPhase.run distance F v lam q t).1.phase=(1+v^2)^q*t.phase ∧
    ∀ j : Fin d,(BinaryRational.encode (RationalPhase.run distance F v lam q t).1.budget[j]).length ≤ budgetBound.eval N := by
  induction q generalizing t with
  | zero=>simpa only [RationalPhase.run,pow_zero,one_mul] using And.intro (rfl : t.phase=t.phase) hb
  | succ q ih=>
    let r := finish distance F v lam F.card t
    obtain ⟨hp,hbudget⟩ := finish_bound_s238 distance F v lam s hL F.card t
      (by simpa only [pow_zero,one_mul] using hz 0 (Nat.zero_le _)) hb
    change r.1.phase=t.phase at hp
    change (∀ j : Fin d,(BinaryRational.encode r.1.budget[j]).length ≤ budgetBound.eval N) at hbudget
    have hphase (j : ℕ) (hj : j ≤ q) : Height ((1+v^2)^j*(advance distance v r.1).phase) (3*(N+1)^2) := by
      change Height ((1+v^2)^j*((1+v^2)*r.1.phase)) _
      rw [hp,←mul_assoc,←pow_succ]
      exact hz (j+1) (by omega)
    have hb' (j : Fin d) : (BinaryRational.encode (advance distance v r.1).budget[j]).length ≤ budgetBound.eval N := by
      rw [advance_get]
      split_ifs
      · apply clipped_bound distance F v lam s hL
        rw [hp]
        simpa only [pow_one] using hz 1 (by omega)
      · exact hbudget j
    obtain ⟨hpres,hbres⟩ := ih (advance distance v r.1) hphase hb'
    simp only [RationalPhase.run]
    refine ⟨?_,hbres⟩
    rw [hpres]
    change (1+v^2)^q*((1+v^2)*r.1.phase)=_
    rw [hp,pow_succ]
    ring
lemma state_length_bound {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s t : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (hz : Height t.phase (3*(N+1)^2))
    (hb : ∀ j : Fin d,(BinaryRational.encode t.budget[j]).length ≤ budgetBound.eval N) :
    (stateBits distance F v lam t).length ≤ sizeBound.eval N := by
  have hdim := dimensions distance F v lam s
  have hctx := ctx_bound distance F t.opened v lam {s with phase:=t.phase}
  have href := reference_length distance F v lam s hL t.phase hz
  have hchg := context_length_change distance F s.opened t.opened v t.phase lam
  have hctx0 : (BinaryPhaseFirst.context distance F s.opened v t.phase lam).length ≤
      (stateBits distance F v lam {s with phase:=t.phase}).length := by
    simp only [stateBits,pairBits_length]; omega
  have hbudget := encode_le_bound (List.ofFn (fun j : Fin d=>BinaryRational.encode t.budget[j])) (budgetBound.eval N) (by
    intro w hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    exact hb j)
  simp only [List.length_ofFn] at hbudget
  have hmul := Nat.mul_le_mul_right (2*budgetBound.eval N+2) (hdim.2.trans hL)
  have hmask := Nat.mul_le_mul (hdim.1.trans hL) (show 2*m+2 ≤ 2*N+2 by omega)
  simp only [stateBits,pairBits_length,RationalMatrix.rowEncode_eq]
  simp only [sizeBound,budgetBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] at hbudget hmul ⊢
  nlinarith
lemma run_length_bound_s238_oai {m d N : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) (hL : (stateBits distance F v lam s).length ≤ N)
    (q : ℕ) (hq : q ≤ N) :
    (stateBits distance F v lam (RationalPhase.run distance F v lam q s).1).length ≤ sizeBound.eval N := by
  obtain ⟨hv,hz,_⟩ := context_height distance F v lam s
  have hv' := hv.mono hL
  have hz' := hz.mono hL
  have h1 : Height (1:ℚ) 0 := natCast 1 0 (by norm_num)
  have hK : Height (1+v^2) (2*N+1) := by convert h1.add (hv'.pow 2) using 1 <;> first | (with_reducible_and_instances rfl) | (omega)
  have hphases (j : ℕ) (hj : j ≤ q) : Height ((1+v^2)^j*s.phase) (3*(N+1)^2) := by
    apply ((hK.pow j).mul hz').mono
    have hjN : j ≤ N := hj.trans hq
    nlinarith
  have hb (j : Fin d) : (BinaryRational.encode s.budget[j]).length ≤ budgetBound.eval N := by
    have hh := (initial_budget_length distance F v lam s j).trans hL
    simp only [budgetBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_one]
    omega
  obtain ⟨hp,hbudget⟩ := run_bound_invariant distance F v lam s hL q s hphases hb
  apply state_length_bound distance F v lam s _ hL _ hbudget
  rw [hp]
  exact hphases q le_rfl
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.run_length_bound_s238_oai
