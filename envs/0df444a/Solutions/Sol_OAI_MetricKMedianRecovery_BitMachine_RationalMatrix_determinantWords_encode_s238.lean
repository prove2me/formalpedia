-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:28:56.740202+00:00
-- url     : https://prove2.me/submissions/f55138b9-9ca9-4a76-ba65-a72d8ebf5ad9

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K009
import Definitions.Def_Q238K018
import Definitions.Def_Q238K022
import Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_RationalMatrix_fold_steps_s238

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_LengthPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations UnaryTake

namespace WordList

lemma cons_ne_nil (w ws : List Bool) : cons w ws≠[] := List.cons_ne_nil _ _

end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Step2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations
namespace WordList
lemma length_encode_append (xs ys : List (List Bool)) :
    (encode (xs++ys)).length=(encode xs).length+(encode ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,encode,List.length_nil,Nat.zero_add]
  | cons x xs ih => simp only [List.cons_append,encode,length_cons,ih]; omega
lemma length_encode_drop (xs : List (List Bool)) (n : ℕ) :
    (encode (xs.drop n)).length ≤ (encode xs).length := by
  have h := length_encode_append (xs.take n) (xs.drop n)
  rw [List.take_append_drop] at h
  omega
namespace Fold

lemma length_pack (ws ctx a : List Bool) : (pack ws ctx a).length=2*ws.length+2*ctx.length+a.length+2 := by
  simp only [pack,pairBits_length]; omega
lemma step_nil (f : List Bool → List Bool) (ctx a : List Bool) :
    step f (pack (encode []) ctx a)=pack (encode []) ctx a := by
  simp only [step,items_pack,encode,ite_true, if_true]
lemma step_cons (f : List Bool → List Bool) (ctx a w : List Bool) (ws : List (List Bool)) :
    step f (pack (encode (w::ws)) ctx a)=pack (encode ws) ctx (operation f ctx a w) := by
  simp only [step,items_pack,encode,cons_ne_nil,ite_false, if_false,context_pack,head_cons,tail_cons,accum_pack,operation]
lemma iterate_pack (f : List Bool → List Bool) (ctx a : List Bool) (ws : List (List Bool)) (n : ℕ) :
    (step f)^[n] (pack (encode ws) ctx a)=
      pack (encode (ws.drop n)) ctx ((ws.take n).foldl (operation f ctx) a) := by
  induction n generalizing ws a with
  | zero => simp only [Function.iterate_zero_apply,List.drop_zero,List.take_zero,List.foldl_nil]
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases ws with
    | nil =>
      rw [step_nil,Function.iterate_fixed (step_nil f ctx a)]
      rfl
    | cons w ws =>
      rw [step_cons,ih]
      simp only [List.drop_succ_cons,List.take_succ_cons,List.foldl_cons]

lemma run_encode (f : List Bool → List Bool) (R : Polynomial ℕ) (ctx a : List Bool)
    (ws : List (List Bool)) (B : ℕ)
    (hB : ∀ n,((ws.take n).foldl (operation f ctx) a).length ≤ B)
    (hR : 2*(encode ws).length+2*ctx.length+B+2 ≤ R.eval (pack (encode ws) ctx a).length) :
    run f R (pack (encode ws) ctx a)=ws.foldl (operation f ctx) a := by
  have he := BoundedIteration.polynomialRun_eq (step f) Polynomial.X R (pack (encode ws) ctx a) (by
    intro j _
    rw [iterate_pack,length_pack]
    have hd := length_encode_drop ws j
    have hb := hB j
    omega)
  simp only [run,Function.comp_apply,he,Polynomial.eval_X,iterate_pack,accum_pack]
  rw [List.take_of_length_le]
  have hw := length_le_encode ws
  rw [length_pack]
  omega
end Fold
end WordList
end MetricKMedianRecovery.BitMachine

end OAI
end

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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Freeze
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdInteger
open Matrix Function
open scoped BigOperators

section Bridge
variable {R : Type*} [CommRing R] {n : ℕ}
lemma sumFrom_eq_sum_Ico {lo : ℕ} (f : ℕ → R) :
    BirdDet.sumFrom n lo f = ∑ k ∈ Finset.Ico lo n, f k := by
  induction lo using BirdDet.sumFrom_induct n with
  | step lo hlo ih => rw [BirdDet.sumFrom_step n lo f hlo, ih, ← Finset.sum_eq_sum_Ico_succ_bot hlo f]
  | stop lo hlo => rw [BirdDet.sumFrom_stop n lo f hlo, Finset.Ico_eq_empty hlo, Finset.sum_empty]

lemma sumFrom_fin_tail (i : Fin n) (f : ℕ → R) :
    BirdDet.sumFrom n (i.val + 1) f = ∑ k ∈ Finset.Ioi i, f k.val := calc
  _ = ∑ k ∈ Finset.Ico (i.val + 1) n, f k := by rw [sumFrom_eq_sum_Ico]
  _ = ∑ k ∈ (Finset.range n).filter (i.val < ·), f k := by congr; ext; aesop
  _ = ∑ k ∈ Finset.range n, if i.val < k then f k else 0 := by rw [Finset.sum_filter]
  _ = ∑ k : Fin n, if i.val < k.val then f k else 0 := by rw [← Fin.sum_univ_eq_sum_range]
  _ = ∑ k ∈ Finset.Ioi i, f k.val := by simp [← Finset.sum_filter, Finset.filter_lt_eq_Ioi]

lemma iterate_get_eq_spec (A : Array R) (hA : A.size = n*n) (t : ℕ) (i j : Fin n) :
    ((BirdDet.stepEntry n A)^[t] (BirdDet.get n A)) i.val j.val =
      (BirdDet.Spec.stepEntry (.ofArray A hA))^[t] (.ofArray A hA) i j := by
  rw [Matrix.ofArray_eq_of_getD]
  induction t generalizing i j with
  | zero => simp [BirdDet.get_eq]
  | succ t ih =>
    simp_rw [iterate_succ_apply',BirdDet.stepEntry_eq,BirdDet.Spec.stepEntry_eq,
      sumFrom_fin_tail,ih,Matrix.of_apply,BirdDet.get_eq]

lemma bird_eq_spec (A : Array R) (hA : A.size=n*n) :
    BirdDet.birdDet n A=BirdDet.Spec.birdDet (.ofArray A hA) := by
  cases n with
  | zero => rw [BirdDet.birdDet_zero,BirdDet.Spec.birdDetSpec_zero]
  | succ k => simp [BirdDet.birdDet_succ,BirdDet.Spec.birdDetSpec_succ,←iterate_get_eq_spec A hA k]

lemma spec_eq_det (A : Matrix (Fin n) (Fin n) R) : BirdDet.Spec.birdDet A=A.det := by
  let ar := Array.ofFn (fun k : Fin (n*n) => A k.divNat k.modNat)
  have har : ar.size=n*n := Array.size_ofFn
  have he : Matrix.ofArray ar har=A := Matrix.ofArray_ofFn A
  rw [←he,←bird_eq_spec ar har,←BirdDet.det_eq_birdDet ar har]
end Bridge

lemma sum_natAbs_bound {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℤ) (B : ℕ)
    (hf : ∀ i∈s,(f i).natAbs≤B) : (∑ i∈s,f i).natAbs≤n*B := by
  calc
    _ ≤ ∑ i∈s,(f i).natAbs := Int.natAbs_sum_le _ _
    _ ≤ ∑ _i∈s,B := Finset.sum_le_sum hf
    _ = s.card*B := by simp
    _ ≤ n*B := Nat.mul_le_mul_right B (by simpa using s.card_le_univ)

lemma step_height {n a b : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j,(A i j).natAbs≤2^a) (hF : ∀ i j,(F i j).natAbs≤2^b) (i j : Fin n) :
    (BirdDet.Spec.stepEntry A F i j).natAbs≤2^(a+b+n+1) := by
  have hd := sum_natAbs_bound (Finset.Ioi i) (fun k => F k k) (2^b) (fun k _ => hF k k)
  have hs := sum_natAbs_bound (Finset.Ioi i) (fun k => F i k*A k j) (2^b*2^a)
    (fun k _ => by rw [Int.natAbs_mul]; exact Nat.mul_le_mul (hF i k) (hA k j))
  calc
    _ ≤ (∑ k∈Finset.Ioi i,F k k).natAbs*(A i j).natAbs+
        (∑ k∈Finset.Ioi i,F i k*A k j).natAbs := by
      simpa only [BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Int.natAbs_mul,Int.natAbs_neg] using
        Int.natAbs_add_le (-(∑ k∈Finset.Ioi i,F k k)*A i j) (∑ k∈Finset.Ioi i,F i k*A k j)
    _ ≤ (n*2^b)*2^a+n*(2^b*2^a) := Nat.add_le_add (Nat.mul_le_mul hd (hA i j)) hs
    _ ≤ (2^n*2^b)*2^a+2^n*(2^b*2^a) := by
      gcongr <;> exact Nat.le_of_lt Nat.lt_two_pow_self
    _ = _ := by simp only [pow_add,pow_one] <;> ring

theorem iterate_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (hA : ∀ i j,(A i j).natAbs≤2^a) (t : ℕ) (i j : Fin n) :
    (iterate A t i j).natAbs≤2^((t+1)*a+t*(n+1)) := by
  induction t generalizing i j with
  | zero => simpa [iterate] using hA i j
  | succ t ih =>
    simp only [iterate,freeze_eq]
    convert step_height A (iterate A t) hA (fun i j => ih i j) i j using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring

end MetricKMedianRecovery.BirdInteger

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
lemma tail_encode (ws : List (List Bool)) : tail (encode ws)=encode ws.tail := by
  cases ws with
  | nil => rfl
  | cons w ws => simp only [encode,tail_cons,List.tail_cons]
lemma head_ofFn {n : ℕ} (f : Fin (n+1) → List Bool) : head (encode (List.ofFn f))=f 0 := by
  rw [List.ofFn_succ]
  exact head_cons ..
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
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CommonDen
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRational
open Matrix RationalHeight
open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]

omit [DecidableEq J] in
lemma commonDen_pos (q : J → ℚ) : 0 < commonDen q := by
  exact Finset.prod_pos (fun i _ => by exact_mod_cast (q i).den_pos)

lemma scaled_cast (q : J → ℚ) (i : J) :
    (scaled q i:ℚ)=(commonDen q:ℚ)*q i := by
  have hh : commonDen q = (q i).den * ∏ j ∈ Finset.univ.erase i, ((q j).den:ℤ) :=
    (Finset.mul_prod_erase Finset.univ (fun j => ((q j).den:ℤ)) (Finset.mem_univ i)).symm
  have hn : ((q i).den:ℚ)≠0 := by exact_mod_cast (q i).den_nz
  calc
    _ = (commonDen q:ℚ)*((q i).num/(q i).den) := by
      rw [hh]
      unfold scaled
      push_cast
      field_simp
    _ = _ := by rw [Rat.num_div_den]

lemma scaled_height (q : J → ℚ) (a : ℕ) (hq : ∀ i,Height (q i) a) (i : J) :
    (scaled q i).natAbs≤2^((Fintype.card J+1)*a) := by
  have hp : (∏ j∈Finset.univ.erase i,((q j).den:ℤ)).natAbs≤2^(Fintype.card J*a) := by
    rw [show (∏ j∈Finset.univ.erase i,((q j).den:ℤ)).natAbs =
      ∏ j∈Finset.univ.erase i,((q j).den:ℤ).natAbs from map_prod Int.natAbsHom _ _]
    calc
      _ ≤ ∏ _j∈Finset.univ.erase i,2^a := by
        apply Finset.prod_le_prod'
        intro j _
        simpa only [Int.natAbs_natCast] using (hq j).2
      _ = 2^((Finset.univ.erase i).card*a) := by rw [Finset.prod_const,←pow_mul]; congr 1; ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right a (Finset.card_le_univ _))
  rw [scaled,Int.natAbs_mul]
  calc
    _ ≤ 2^a*2^(Fintype.card J*a) := Nat.mul_le_mul (hq i).1 hp
    _ = _ := by rw [←pow_add]; congr 1; ring

lemma intCast_height (z : ℤ) (a : ℕ) (hz : z.natAbs≤2^a) : Height (z:ℚ) a := by
  constructor
  · simpa using hz
  · simpa using (one_le_pow₀ (by norm_num : (1:ℕ)≤2) : 1≤2^a)

end MetricKMedianRecovery.BirdRational

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Iterate
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BirdRationalIteration
open Matrix RationalHeight
open scoped BigOperators

lemma iterate_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : iterate A 0=A := rfl
lemma iterate_succ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (t : ℕ) :
    iterate A (t+1)=BirdDet.Spec.stepEntry A (iterate A t) := by
  exact Function.iterate_succ_apply' ..
lemma step_smul {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℚ) (c d : ℚ) :
    BirdDet.Spec.stepEntry (c • A) (d • F)=(c*d) • BirdDet.Spec.stepEntry A F := by
  ext i j
  have hs : (∑ k∈Finset.Ioi i,(d*F i k)*(c*A k j))=
      (c*d)*∑ k∈Finset.Ioi i,F i k*A k j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Matrix.smul_apply,smul_eq_mul,
    ←Finset.mul_sum,hs]
  ring
lemma iterate_smul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (c : ℚ) (t : ℕ) :
    iterate (c • A) t=c^(t+1) • iterate A t := by
  induction t with
  | zero => simp only [iterate_zero,Nat.zero_add,pow_one]
  | succ t ih =>
    rw [iterate_succ,ih,step_smul,iterate_succ]
    congr 1
    simp only [pow_succ]
    ring
lemma step_cast {n : ℕ} (A F : Matrix (Fin n) (Fin n) ℤ) :
    (BirdDet.Spec.stepEntry A F).map (Int.cast : ℤ→ℚ)=
      BirdDet.Spec.stepEntry (A.map (Int.cast : ℤ→ℚ)) (F.map (Int.cast : ℤ→ℚ)) := by
  ext i j
  simp only [Matrix.map_apply,BirdDet.Spec.stepEntry_eq,Matrix.of_apply,Int.cast_add,
    Int.cast_mul,Int.cast_neg,Int.cast_sum]
lemma iterate_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (t : ℕ) :
    (BirdInteger.iterate A t).map (Int.cast : ℤ→ℚ)=iterate (A.map (Int.cast : ℤ→ℚ)) t := by
  induction t with
  | zero => simp only [BirdInteger.iterate,BirdInteger.freeze_eq,iterate_zero]
  | succ t ih =>
    simp only [BirdInteger.iterate,BirdInteger.freeze_eq,step_cast,ih,iterate_succ]

lemma integral_cast {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    (integral A).map (Int.cast : ℤ→ℚ)=(BirdRational.commonDen (flat A):ℚ) • A := by
  ext i j
  exact BirdRational.scaled_cast (flat A) (i,j)
lemma commonDen_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j,Height (A i j) a) :
    (BirdRational.commonDen (flat A)).natAbs≤2^((n*n)*a) := by
  unfold BirdRational.commonDen
  rw [show (∏ i,((flat A i).den:ℤ)).natAbs=∏ i,((flat A i).den:ℤ).natAbs from map_prod Int.natAbsHom _ _]
  calc
    _ ≤ ∏ _p : Fin n×Fin n,2^a := Finset.prod_le_prod' (fun p _=>by
      simpa only [Int.natAbs_natCast,flat] using (hA p.1 p.2).2)
    _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,←pow_mul]; congr 1; ring

lemma iterate_height {n a : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : ∀ i j,Height (A i j) a) (t : ℕ) (i j : Fin n) :
    Height (iterate A t i j) ((t+1)*((2*n*n+1)*a)+t*(n+1)) := by
  let Z := integral A
  let D := BirdRational.commonDen (flat A)
  have hD : (D:ℚ)≠0 := by exact_mod_cast (BirdRational.commonDen_pos (flat A)).ne'
  have hZ : ∀ i j,(Z i j).natAbs≤2^((n*n+1)*a) := by
    intro i j
    simpa only [Fintype.card_prod,Fintype.card_fin,Z,integral] using
      BirdRational.scaled_height (flat A) a (fun p=>hA p.1 p.2) (i,j)
  have hi := BirdInteger.iterate_height Z hZ t i j
  have he : ((BirdInteger.iterate Z t i j:ℤ):ℚ)=(D:ℚ)^(t+1)*iterate A t i j := by
    have hh := congrFun (congrFun (iterate_cast Z t) i) j
    rw [show Z.map (Int.cast : ℤ→ℚ)=(D:ℚ) • A from integral_cast A,iterate_smul] at hh
    exact hh
  have hf : iterate A t i j=((BirdInteger.iterate Z t i j:ℤ):ℚ)/(D:ℚ)^(t+1) := by
    rw [he,mul_div_cancel_left₀ _ (pow_ne_zero _ hD)]
  rw [hf]
  have hnum := BirdRational.intCast_height (BirdInteger.iterate Z t i j) _ hi
  have hden := (BirdRational.intCast_height D _ (commonDen_height A hA)).pow (t+1)
  convert hnum.div hden using 1 <;> first | rfl | ring
lemma determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : determinant A=A.det := by
  rw [←BirdInteger.spec_eq_det]
  cases n with
  | zero => rfl
  | succ k => simp only [determinant,BirdDet.Spec.birdDetSpec_succ,iterate]
end MetricKMedianRecovery.BirdRationalIteration

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
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
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

lemma iterate_length_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) {t : ℕ} (ht : t≤n) :
    (encode (MetricKMedianRecovery.BirdRationalIteration.iterate A t)).length≤80*((encode A).length+1)^6 := by
  let L := (encode A).length
  let P := L+1
  have hn : n≤L := dimension_bound A
  have hp : 1≤P := by omega
  have hp₂ : 1≤P^2 := one_le_pow₀ hp
  have hp₂₄ : P^2≤P^4 := Nat.pow_le_pow_right hp (by omega)
  have hn₂ : 2*n*n+1≤3*P^2 := by dsimp [P] <;> nlinarith
  have hb : (t+1)*((2*n*n+1)*L)+t*(n+1)≤4*P^4 := by
    have h₁ : (t+1)*((2*n*n+1)*L)≤P*((3*P^2)*P) := by
      gcongr <;> omega
    have h₂ : t*(n+1)≤P*P := by gcongr <;> omega
    nlinarith
  have hh := encode_height (MetricKMedianRecovery.BirdRationalIteration.iterate A t)
    (MetricKMedianRecovery.BirdRationalIteration.iterate_height A (input_height A) t)
  have hp₁₆ : P≤P^6 := by simpa using Nat.pow_le_pow_right hp (show 1≤6 by omega)
  have hp₂₆ : P^2≤P^6 := Nat.pow_le_pow_right hp (by omega)
  calc
    _ ≤ n*(2*(n*(6*((t+1)*((2*n*n+1)*L)+t*(n+1))+14))+2) := hh
    _ ≤ P*(2*(P*(6*(4*P^4)+14))+2) := by gcongr <;> omega
    _ ≤ 80*(L+1)^6 := by change _≤80*P^6; nlinarith

lemma iterateWords_encode {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    iterateWords (encode A)=encode (MetricKMedianRecovery.BirdRationalIteration.iterate A (n-1)) := by
  let ws := List.ofFn (fun i=>rowEncode (A i))
  have hws : WordList.encode ws=encode A := rfl
  have hlen : ws.length=n := List.length_ofFn
  simp only [iterateWords,Function.comp_apply,iterationInput,←hws,tail_encode]
  rw [Fold.run_encode loopOp (200*(Polynomial.X+1)^6) (WordList.encode ws)
    (WordList.encode ws) ws.tail (80*((encode A).length+1)^6)]
  · rw [hws,fold_steps_s238,←MetricKMedianRecovery.BirdRationalIteration.iterate,List.length_tail,hlen]
  · intro j
    rw [hws,fold_steps_s238,←MetricKMedianRecovery.BirdRationalIteration.iterate]
    apply iterate_length_bound
    simp only [List.length_take,List.length_tail,hlen]
    omega
  · have ht := length_encode_drop ws 1
    rw [List.drop_one] at ht
    let L := (encode A).length
    have hS : L≤(Fold.pack (WordList.encode ws.tail) (WordList.encode ws) (WordList.encode ws)).length := by
      rw [Fold.length_pack,hws]
      omega
    have hq : 1≤L+1 := by omega
    have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hS 1) 6
    have hlin : L+1≤(L+1)^6 := by simpa using Nat.pow_le_pow_right hq (show 1≤6 by omega)
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change 2*(WordList.encode ws.tail).length+2*(WordList.encode ws).length+80*(L+1)^6+2≤_
    change (WordList.encode ws.tail).length≤L at ht
    rw [hws] at hp
    rw [hws]
    change 2*(WordList.encode ws.tail).length+2*L+80*(L+1)^6+2≤_
    nlinarith

lemma rawDet_encode {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) :
    rawDet (encode A)=BinaryRational.encode (MetricKMedianRecovery.BirdRationalIteration.iterate A n 0 0) := by
  simp only [rawDet,Function.comp_apply]
  rw [iterateWords_encode,Nat.add_sub_cancel,encode,head_ofFn,rowEncode_eq,head_ofFn]

lemma sign_fold (ws : List (List Bool)) (z : ℚ) :
    ws.foldl (Fold.operation signOp []) (BinaryRational.encode z)=BinaryRational.encode ((-1)^ws.length*z) := by
  induction ws generalizing z with
  | nil => simp only [List.foldl_nil,List.length_nil,pow_zero,one_mul]
  | cons w ws ih =>
    have hs : Fold.operation signOp [] (BinaryRational.encode z) w=BinaryRational.encode (-z) := by
      simp only [Fold.operation,signOp,Function.comp_apply,discardPrefix_pairBits,BinaryRational.negWords_encode]
    rw [List.foldl_cons,hs,ih,List.length_cons,pow_succ]
    congr 1
    ring

lemma signRun_encode (ws : List (List Bool)) (z : ℚ) :
    signRun (Fold.pack (WordList.encode ws) [] (BinaryRational.encode z))=BinaryRational.encode ((-1)^ws.length*z) := by
  unfold signRun
  rw [Fold.run_encode signOp (4*Polynomial.X+4) [] (BinaryRational.encode z) ws (BinaryRational.encode z).length]
  · exact sign_fold ws z
  · intro n
    rw [sign_fold]
    have he : ((-1:ℚ)^((ws.take n).length)*z).num.natAbs=z.num.natAbs ∧
        ((-1:ℚ)^((ws.take n).length)*z).den=z.den := by
      rcases neg_one_pow_eq_or ℚ ((ws.take n).length) with h|h
      · simp only [h,one_mul,and_self]
      · simp only [h,neg_one_mul,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den,and_self]
    simp only [BinaryRational.encode_length,he.1,he.2,Nat.le_refl]
  · simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
      Fold.length_pack,List.length_nil,Nat.mul_zero,Nat.add_zero]
    omega
lemma determinantWords_encode_s238_oai {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    determinantWords (encode A)=BinaryRational.encode A.det := by
  rw [←MetricKMedianRecovery.BirdRationalIteration.determinant_eq]
  cases n with
  | zero => rfl
  | succ n =>
    have hne : encode A≠[] := by
      have hh := dimension_bound A
      intro he
      rw [he,List.length_nil] at hh
      omega
    rw [determinantWords,ite_eq_right hne]
    simp only [signedDet,Function.comp_apply,determinantInput,rawDet_encode]
    rw [encode,tail_encode,signRun_encode,List.length_tail,List.length_ofFn,Nat.add_sub_cancel]
    rfl
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238_oai := @OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238_oai
