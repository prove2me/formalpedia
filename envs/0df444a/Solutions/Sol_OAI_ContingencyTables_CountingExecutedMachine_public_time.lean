-- Prove2me | solution 1 for OAI.ContingencyTables.CountingExecutedMachine.public_time
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:26:58.480331+00:00
-- url     : https://prove2.me/submissions/ecf4bde0-8244-4e8f-90a9-7d2330da3e3c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A009
import Definitions.Def_OAIQ089A010
import Theorems.Thm_OAI_ContingencyTables_CountingBranchProgram_polynomial_publicBudget
import Theorems.Thm_OAI_ContingencyTables_CountingBranchProgram_polynomial_publicOutput
import Theorems.Thm_OAI_ContingencyTables_CountingExecutedMachine_polynomial_positive

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_TreeBits
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeData

lemma bits_length (A : List Bool) : (encode (bits A)).length≤4*A.length+1 := by
  induction A with
  | nil => simp [encode]
  | cons b A ih => cases b <;> simp only [bits_cons,encode,bit,Bool.false_eq_true,↓reduceIte,
      List.length_cons,List.length_append,List.length_nil] <;> omega
end MatchingFPRAS.TreeData

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeList
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma size_encode_list (as : List A) :
    TreeFunction.size (encode as) = 1+as.length+(as.map (fun a=>TreeFunction.size (encode a))).sum := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [encode_list_cons,size_cons,ih,List.length_cons,List.map_cons,List.sum_cons]; omega

lemma size_encode_mem {as : List A} {a : A} (ha : a ∈ as) :
    TreeFunction.size (encode a) ≤ TreeFunction.size (encode as) := by
  induction as with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    simp only [encode_list_cons,size_cons]
    rcases ha with rfl|ha
    · omega
    · have := ih ha; omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeRepeat
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeMachine RegisterProc TreeFunction

variable {B : Type} [Codec B]

omit [Codec B] in
lemma Repeat.cost_bound {f : ℕ×B → B} (t : ℕ×B → ℕ) (I : ℕ → B → Prop) (N : ℕ) (b : B)
    (T S : ℕ) (hb : I N b)
    (hstep : ∀ n<N,∀ z,I (n+1) z → I n (f (n+1,z)) ∧ t (n+1,z) ≤ T)
    (hsize : ∀ n<N,TreeFunction.size (nat (n+1)) ≤ S) :
    Repeat.cost f t N b ≤ N*(T+4*S+12)+10 := by
  induction N generalizing b with
  | zero => simp [cost]
  | succ n ih =>
    have hs:=hstep n (by omega) b hb
    have ht:=ih (f (n+1,b)) hs.1 (fun k hk z hz=>hstep k (by omega) z hz) (fun k hk=>hsize k (by omega))
    have hz:=hsize n (by omega)
    simp only [cost]
    nlinarith
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma normalize_repr (x : Fraction) : normalize x=repr (val x) := by
  by_cases hd : x.2=0
  · simp [normalize,repr,val,hd]
  · have he : val x=mkRat (x.1:Int) x.2 := by simp [val,Rat.mkRat_eq_div]
    simp only [normalize,hd,↓reduceIte,he,repr,Rat.num_mkRat,Rat.den_mkRat]
    simp [Nat.gcd_comm,←Int.natCast_ediv]

lemma val_nonneg (x : Fraction) : 0≤val x := by unfold val; positivity
lemma val_repr {q : ℚ} (h : 0≤q) : val (repr q)=q := by
  have hn : 0≤q.num := by exact Rat.num_nonneg.mpr h
  have he : (q.num.natAbs : ℤ)=q.num := Int.natAbs_of_nonneg hn
  change (q.num.natAbs:ℚ)/(q.den:ℚ)=q
  rw [←Int.cast_natCast q.num.natAbs,he]
  exact Rat.num_div_den q

lemma normalize_val (x : Fraction) : val (normalize x)=val x := by
  rw [normalize_repr]
  exact val_repr (val_nonneg x)

lemma normalize_den_pos (x : Fraction) : 0<(normalize x).2 := by
  rw [normalize_repr]; exact (val x).pos

lemma mul_val (x y : Fraction) : val (mul (x,y))=val x*val y := by
  rw [mul,normalize_val]
  simp only [val,Nat.cast_mul]
  exact (div_mul_div_comm _ _ _ _).symm

lemma add_val (x y : Fraction) (hx : x.2≠0) (hy : y.2≠0) :
    val (add (x,y))=val x+val y := by
  rw [add,normalize_val]
  simp only [val,Nat.cast_add,Nat.cast_mul]
  rw [div_add_div (x.1:ℚ) (y.1:ℚ) (b:=(x.2:ℚ)) (d:=(y.2:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast hy)]
  ring

lemma div_val (x y : Fraction) : val (div (x,y))=val x/val y := by
  rw [div,normalize_val]
  simp only [val,Nat.cast_mul]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma weight_pos (a : A) : 0<weight a := by
  change 0<TreeFunction.size (encode a)
  cases encode a <;> simp only [size_nil,size_cons] <;> omega
lemma list_length_le_weight (as : List A) : as.length≤weight as := by
  rw [weight,size_encode_list]; omega
lemma weight_mem {as : List A} {a : A} (ha : a∈as) : weight a≤weight as := size_encode_mem ha

lemma polynomial_eval_monotone (p : Polynomial ℕ) : Monotone (fun n=>p.eval n) := by
  intro a b hab
  simp only [Polynomial.eval_eq_sum,Polynomial.sum_def]
  exact Finset.sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

lemma polynomial_identity : PolynomialTime (identity (A:=A)) := by
  refine ⟨X+1,?_⟩
  intro a
  simp [identity,weight,Polynomial.eval_add,Polynomial.eval_X, Nat.add_comm]
lemma polynomial_first : PolynomialTime (first (A:=A) (B:=B)) := by
  refine ⟨7*X+11,?_⟩
  intro ⟨a,b⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change 6*weight a+weight b+11+weight a≤7*(1+weight a+weight b)+11
  omega
lemma polynomial_second : PolynomialTime (second (A:=A) (B:=B)) := by
  refine ⟨4*X+7,?_⟩
  intro ⟨a,b⟩
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change 3*weight a+7+weight b≤4*(1+weight a+weight b)+7
  omega

lemma polynomial_composition {f : A → B} {g : B → C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (composition F G) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  refine ⟨p+q.comp p,fun a=>?_⟩
  have h1 := hp a
  have h2 := hq (f a)
  have h3 := polynomial_eval_monotone q (show weight (f a)≤p.eval (weight a) by omega)
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  change F.cost a+G.cost (f a)+weight (g (f a))≤_
  dsimp only at h3
  omega
lemma polynomial_pair {f : A → B} {g : A → C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (pair F G) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  refine ⟨7*p+q+11*X+32,fun a=>?_⟩
  have h1 := hp a
  have h2 := hq a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  rw [weight_prod]
  change F.cost a+G.cost a+11*weight a+6*weight (f a)+31+(1+weight (f a)+weight (g a))≤_
  omega
lemma polynomial_congr {f g : A → B} {F : Realizer f} (h : ∀ a,f a=g a)
    (hF : PolynomialTime F) : PolynomialTime (F.congr h) := by
  obtain ⟨p,hp⟩ := hF
  exact ⟨p,fun a=>by simpa only [Realizer.congr,←h a] using hp a⟩
lemma polynomial_choose {f : A → Bool} {g h : A → B} {F : Realizer f} {G : Realizer g} {H : Realizer h}
    (hF : PolynomialTime F) (hG : PolynomialTime G) (hH : PolynomialTime H) :
    PolynomialTime (choose F G H) := by
  obtain ⟨p,hp⟩ := hF
  obtain ⟨q,hq⟩ := hG
  obtain ⟨r,hr⟩ := hH
  refine ⟨p+q+r+7*X+18,fun a=>?_⟩
  have h1 := hp a
  have h2 := hq a
  have h3 := hr a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change F.cost a+(if f a then G.cost a else H.cost a)+7*weight a+18+
    weight (if f a then g a else h a)≤_
  cases f a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega
lemma polynomial_constantData (b : Data) : PolynomialTime (constantData (A:=A) b) := by
  induction b with
  | nil => refine ⟨X+3,fun a=>?_⟩; simp [constantData,weight,Codec.encode,size_nil]
  | cons b c hb hc =>
    obtain ⟨p,hp⟩ := polynomial_pair hb hc
    exact ⟨p,hp⟩
lemma polynomial_constant (b : B) : PolynomialTime (constant (A:=A) b) :=
  polynomial_constantData (encode b)

omit [Codec B] in
lemma Fold.cost_prefix_bound {f : A×B → B} (t : A×B → ℕ) (as : List A) (b : B) (T S : ℕ)
    (hs : weight as≤S)
    (hstep : ∀ pre a post,as=pre++a::post → t (a,pre.foldl (fun z c=>f (c,z)) b)≤T) :
    Fold.cost f t as b≤as.length*(T+14*S+34)+10 := by
  induction as generalizing b with
  | nil => simp [Fold.cost]
  | cons a as ih =>
    have ht := hstep [] a as rfl
    simp only [List.foldl_nil] at ht
    have hs' : weight as≤S := by rw [weight_cons] at hs; omega
    have hi := ih (f (a,b)) hs' (by
      intro pre c post he
      have hh := hstep (a::pre) c post (by simp only [List.cons_append,he])
      exact hh)
    simp only [Fold.cost,List.length_cons]
    change t (a,b)+6*weight a+8*weight as+34+Fold.cost f t as (f (a,b))≤_
    have ha : weight a≤S := by rw [weight_cons] at hs; omega
    nlinarith

lemma polynomial_fold {f : A×B → B} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ)
    (hsize : ∀ (as : List A) (b : B) pre post,as=pre++post →
      weight (pre.foldl (fun z a=>f (a,z)) b)≤p.eval (weight (as,b))) :
    PolynomialTime (fold F) := by
  obtain ⟨q,hq⟩ := hF
  refine ⟨X*(q.comp (1+X+p)+14*X+34)+10+p,fun ⟨as,b⟩=>?_⟩
  let S:=weight (as,b)
  let T:=q.eval (1+S+p.eval S)
  have hs : weight as≤S := by dsimp [S]; rw [weight_prod]; omega
  have hc := Fold.cost_prefix_bound (f:=f) F.cost as b T S hs (by
    intro pre a post he
    have hz := hsize as b pre (a::post) he
    change _≤p.eval S at hz
    have ha : weight a≤S := (weight_mem (by simp [he])).trans hs
    have hq' := hq (a,pre.foldl (fun z c=>f (c,z)) b)
    have hm := polynomial_eval_monotone q (show weight (a,pre.foldl (fun z c=>f (c,z)) b)≤1+S+p.eval S by rw [weight_prod]; omega)
    dsimp only at hm
    dsimp only [T]
    omega)
  have hout := hsize as b as [] (by simp)
  change _≤p.eval S at hout
  have hlen : as.length≤S := (list_length_le_weight as).trans hs
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change Fold.cost f F.cost as b+weight (as.foldl (fun z a=>f (a,z)) b)≤_
  change _≤S*(T+14*S+34)+10+p.eval S
  nlinarith
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialArithmetic
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open TreeData TreeFunction Polynomial

lemma weight_bool (b : Bool) : weight b≤3 := by cases b <;> decide
lemma weight_bits (bs : List Bool) : weight bs≤4*bs.length+1 := TreeData.bits_length bs
lemma weight_nat (n : ℕ) : weight n=weight n.bits := rfl
lemma weight_nat_le (n : ℕ) : weight n≤4*n.size+1 := by
  rw [weight_nat,←Nat.size_eq_bits_len]; exact weight_bits _
lemma size_le_weight (n : ℕ) : n.size≤weight n := by
  rw [weight_nat,←Nat.size_eq_bits_len]; exact list_length_le_weight _
lemma weight_nat_small {a b : ℕ} (h : a≤b) : weight a≤4*weight b+1 := by
  have h1:=Nat.size_le_size h
  have h2:=weight_nat_le a
  have h3:=size_le_weight b
  omega
lemma nat_size_add (a b : ℕ) : (a+b).size≤ max a.size b.size+1 := by
  apply Nat.size_le.mpr
  have ha : a<2^(max a.size b.size) := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hb : b<2^(max a.size b.size) := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  rw [pow_succ]; omega
lemma nat_size_mul (a b : ℕ) : (a*b).size≤a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.le_of_lt (Nat.lt_size_self b))).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))
lemma weight_add (a b : ℕ) : weight (a+b)≤4*(weight a+weight b+1)+1 := by
  have h:=weight_nat_le (a+b)
  have h1:=nat_size_add a b
  have h2:=size_le_weight a
  have h3:=size_le_weight b
  have hm : max a.size b.size≤weight a+weight b := max_le (by omega) (by omega)
  omega
lemma polynomial_add : PolynomialTime add := by
  refine ⟨20*X+30,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have ho:=weight_add a b
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change (2*weight a+5+9*(a.bits.length+b.bits.length)+20)+weight (a+b)≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega
lemma polynomial_less : PolynomialTime less := by
  refine ⟨8*X+40,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have ho:=weight_bool (decide (a<b))
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change (2*weight a+3*(a.bits.length+b.bits.length)+31)+weight (decide (a<b))≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega
lemma polynomial_subtract : PolynomialTime subtract := by
  refine ⟨50*X+100,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have hc:=weight_nat_small (Nat.sub_le a b)
  have ho:=weight_bool (decide (a<b))
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  change (2*weight a+3*(a.bits.length+b.bits.length)+31)+
    (if decide (a<b) then weight (a,b)+2 else
      2*weight a+9*(a.bits.length+b.bits.length)+4*weight (a-b)+32)+
      7*weight (a,b)+18+weight (a-b)≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len,weight_prod]
  split <;> omega
lemma polynomial_toBits : PolynomialTime toBits := by
  refine ⟨X+1,fun _=>?_⟩
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change 1+weight _ ≤ weight _+1
  rw [weight_nat]; omega
lemma polynomial_listCons {A : Type} [Codec A] : PolynomialTime (listCons (A:=A)) := by
  refine ⟨X+1,fun ⟨a,as⟩=>?_⟩
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,weight_prod,weight_cons]
  change 1+(1+weight a+weight as)≤(1+weight a+weight as)+1
  omega
lemma polynomial_double : PolynomialTime double :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity) polynomial_add)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialLists
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]
lemma polynomial_fst {f : A → B×C} {F : Realizer f} (h : PolynomialTime F) :
    PolynomialTime (composition F first) := polynomial_composition h polynomial_first
lemma polynomial_snd {f : A → B×C} {F : Realizer f} (h : PolynomialTime F) :
    PolynomialTime (composition F second) := polynomial_composition h polynomial_second
lemma weight_append (as bs : List A) : weight (as++bs)+1=weight as+weight bs := by
  induction as with
  | nil => simp only [List.nil_append,weight_nil]; omega
  | cons a as ih => simp only [List.cons_append,weight_cons]; omega
lemma weight_reverse (as : List A) : weight as.reverse=weight as := by
  simp only [weight,size_encode_list,List.length_reverse,List.map_reverse,List.sum_reverse]
lemma weight_prefix {as pre post : List A} (h : as=pre++post) : weight pre≤weight as := by
  have := weight_append pre post
  have := weight_pos post
  rw [h]; omega
omit [Codec A] in
lemma weight_map_bound {f : A → B} {as : List A} {N : ℕ}
    (h : ∀ a∈as,weight (f a)≤N) : weight (as.map f)≤as.length*(N+1)+1 := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ht:=ih (fun b hb=>h b (by simp [hb]))
    have ha:=h a (by simp)
    simp only [List.map_cons,weight_cons,List.length_cons]
    nlinarith
lemma polynomial_reverse : PolynomialTime (reverse (A:=A)) := by
  unfold reverse
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
  apply polynomial_fold polynomial_listCons (2*X+1)
  intro as bs pre post he
  have hp := weight_prefix he
  have h:=weight_append pre.reverse bs
  rw [weight_reverse] at h
  simp only [List.foldl_flip_cons_eq_append']
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
lemma polynomial_mulStep : PolynomialTime mulStepRealizer := by
  unfold mulStepRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_composition polynomial_second polynomial_first)
  apply polynomial_composition _ polynomial_add
  apply polynomial_pair
  · exact polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_double
  · exact polynomial_choose polynomial_first
      (polynomial_composition polynomial_second polynomial_first) (polynomial_constant 0)
lemma mulStep_size (b : Bool) (n c : ℕ) : (mulStep (b,(n,c))).2.size ≤ c.size+n.size+3 := by
  have hh:=nat_size_mul 2 c
  have ha:=nat_size_add (2*c) (if b then n else 0)
  have hb : (if b then n else 0).size≤n.size := by cases b <;> simp
  have h2 : Nat.size 2=2 := by decide
  have hm : max (2*c).size (if b then n else 0).size ≤ c.size+n.size+2 := max_le (by omega) (by omega)
  change (2*c+(if b then n else 0)).size≤_
  omega
lemma mulStep_fold_first (bs : List Bool) (n c : ℕ) :
    (bs.foldl (fun z b=>mulStep (b,z)) (n,c)).1=n := by
  induction bs generalizing c with
  | nil => rfl
  | cons b bs ih => exact ih _
lemma mulStep_fold_size (bs : List Bool) (n c : ℕ) :
    (bs.foldl (fun z b=>mulStep (b,z)) (n,c)).2.size ≤ c.size+bs.length*(n.size+3) := by
  induction bs generalizing c with
  | nil => simp
  | cons b bs ih =>
    have hs:=mulStep_size b n c
    have ht:=ih (2*c+(if b then n else 0))
    change (bs.foldl _ (mulStep (b,(n,c)))).2.size≤_
    simp only [mulStep] at hs
    simp only [List.length_cons]
    change (bs.foldl _ (n,2*c+(if b then n else 0))).2.size≤_
    nlinarith
lemma polynomial_mulFold : PolynomialTime (fold mulStepRealizer) := by
  apply polynomial_fold polynomial_mulStep (10*(X+1)^2)
  rintro bs ⟨n,c⟩ pre post he
  let S:=weight (bs,(n,c))
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have hn : n.size≤S := by have h:=size_le_weight n; dsimp [S]; simp only [weight_prod]; omega
  have hc : c.size≤S := by have h:=size_le_weight c; dsimp [S]; simp only [weight_prod]; omega
  have hn' : weight n≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hs:=mulStep_fold_size pre n c
  have ho:=weight_nat_le (pre.foldl (fun z b=>mulStep (b,z)) (n,c)).2
  have hr:=mulStep_fold_first pre n c
  rw [←Prod.eta (pre.foldl (fun z b=>mulStep (b,z)) (n,c)),weight_prod,hr]
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤10*(S+1)^2
  have hmul : pre.length*(n.size+3)≤S*(S+3) := Nat.mul_le_mul hpre (by omega)
  nlinarith
lemma polynomial_multiply : PolynomialTime multiply := by
  unfold multiply
  apply polynomial_congr
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_mulFold
  apply polynomial_pair
  · exact polynomial_composition (polynomial_composition polynomial_first polynomial_toBits) polynomial_reverse
  · exact polynomial_pair polynomial_second (polynomial_constant 0)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialDivision
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

lemma polynomial_digitValue : PolynomialTime digitValue := by
  unfold digitValue
  exact polynomial_congr _ (polynomial_choose polynomial_identity (polynomial_constant 1) (polynomial_constant 0))
lemma polynomial_divStep : PolynomialTime divStepRealizer := by
  unfold divStepRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_fst polynomial_second)
  apply polynomial_choose
  · apply polynomial_composition _ polynomial_less
    apply polynomial_pair
    · apply polynomial_composition _ polynomial_add
      exact polynomial_pair (polynomial_composition (polynomial_snd (polynomial_snd polynomial_second)) polynomial_double)
        (polynomial_composition polynomial_first polynomial_digitValue)
    · exact polynomial_fst polynomial_second
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_fst (polynomial_snd polynomial_second)) polynomial_double
    · apply polynomial_composition _ polynomial_add
      exact polynomial_pair (polynomial_composition (polynomial_snd (polynomial_snd polynomial_second)) polynomial_double)
        (polynomial_composition polynomial_first polynomial_digitValue)
  · apply polynomial_pair
    · apply polynomial_composition _ polynomial_add
      exact polynomial_pair
        (polynomial_composition (polynomial_fst (polynomial_snd polynomial_second)) polynomial_double) (polynomial_constant 1)
    · apply polynomial_composition _ polynomial_subtract
      apply polynomial_pair
      · apply polynomial_composition _ polynomial_add
        exact polynomial_pair (polynomial_composition (polynomial_snd (polynomial_snd polynomial_second)) polynomial_double)
          (polynomial_composition polynomial_first polynomial_digitValue)
      · exact polynomial_fst polynomial_second
lemma nat_size_double_digit (r : ℕ) (b : Bool) : (2*r+b.toNat).size ≤ r.size+3 := by
  have h1:=nat_size_mul 2 r
  have h2:=nat_size_add (2*r) b.toNat
  have h3 : b.toNat.size≤1 := Nat.size_le_size (Bool.toNat_le b)
  have h4 : Nat.size 2=2 := by decide
  have hm : max (2*r).size b.toNat.size ≤ r.size+2 := max_le (by omega) (by omega)
  omega
lemma divStep_sizes (b : Bool) (n q r : ℕ) :
    (divStep (b,(n,q,r))).2.1.size≤q.size+3 ∧ (divStep (b,(n,q,r))).2.2.size ≤ r.size+3 := by
  have hq:=nat_size_double_digit q true
  have hq0:=nat_size_double_digit q false
  have hr:=nat_size_double_digit r b
  have hsub:=Nat.size_le_size (Nat.sub_le (2*r+b.toNat) n)
  simp only [Bool.toNat_true] at hq
  simp only [Bool.toNat_false,Nat.add_zero] at hq0
  dsimp only [divStep]
  split_ifs <;> simp only <;> constructor <;> omega
lemma divFold_sizes (bs : List Bool) (n q r : ℕ) :
    (bs.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.1.size≤q.size+3*bs.length ∧
    (bs.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2.size ≤ r.size+3*bs.length := by
  induction bs generalizing q r with
  | nil => simp
  | cons b bs ih =>
    have hs:=divStep_sizes b n q r
    have ht:=ih (divStep (b,(n,q,r))).2.1 (divStep (b,(n,q,r))).2.2
    have he : divStep (b,(n,q,r))=(n,(divStep (b,(n,q,r))).2.1,(divStep (b,(n,q,r))).2.2) := by
      exact Prod.ext rfl (Prod.eta _).symm
    change (bs.foldl _ (divStep (b,(n,q,r)))).2.1.size≤_ ∧ (bs.foldl _ (divStep (b,(n,q,r)))).2.2.size≤_
    rw [he]
    simp only [List.length_cons]
    constructor <;> omega
lemma polynomial_divFold : PolynomialTime (fold divStepRealizer) := by
  apply polynomial_fold polynomial_divStep (40*X+10)
  rintro bs ⟨n,q,r⟩ pre post he
  let S:=weight (bs,(n,q,r))
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have hq : q.size≤S := by have h:=size_le_weight q; dsimp [S]; simp only [weight_prod]; omega
  have hr : r.size≤S := by have h:=size_le_weight r; dsimp [S]; simp only [weight_prod]; omega
  have hn : weight n≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hs:=divFold_sizes pre n q r
  have hqo:=weight_nat_le (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.1
  have hro:=weight_nat_le (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2
  have hf:=divFold_first pre n q r
  rw [←Prod.eta (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)),weight_prod,hf,
    ←Prod.eta (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)).2,weight_prod]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤40*S+10
  omega
lemma polynomial_divCore : PolynomialTime divCore := by
  unfold divCore
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_divFold
  exact polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_toBits) polynomial_reverse)
    (polynomial_pair polynomial_second (polynomial_pair (polynomial_constant 0) (polynomial_constant 0)))
lemma polynomial_division : PolynomialTime division := by
  unfold division
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_second) polynomial_less)
    polynomial_divCore (polynomial_pair (polynomial_constant 0) polynomial_first)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialLoop
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma polynomial_predecessor : PolynomialTime predecessor :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1)) polynomial_subtract
lemma polynomial_repeatNext {f : ℕ×B → B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (Repeat.nextRealizer F) :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_predecessor) hF

omit [Codec A] [Codec B] in
lemma countDown_invariant {f : ℕ×B → B} (I : ℕ → B → Prop) {n : ℕ} {b : B}
    (hi : I n b) (hs : ∀ k<n,∀ z,I (k+1) z → I k (f (k+1,z))) : I 0 (countDown f n b) := by
  induction n generalizing b with
  | zero => exact hi
  | succ n ih => exact ih (hs n (by omega) b hi) (fun k hk z hz=>hs k (by omega) z hz)

lemma polynomial_boundedRepeat {init : A → ℕ×B} {f : ℕ×B → B}
    {Init : Realizer init} {F : Realizer f} (hInit : PolynomialTime Init) (hF : PolynomialTime F)
    (p q : Polynomial ℕ) (I : A → ℕ → B → Prop)
    (hn : ∀ a,(init a).1≤p.eval (weight a))
    (hi : ∀ a,I a (init a).1 (init a).2)
    (hs : ∀ a k,(k<(init a).1) → ∀ z,I a (k+1) z → I a k (f (k+1,z)))
    (hw : ∀ a k z,I a k z → weight z≤q.eval (weight a)) :
    PolynomialTime (composition Init (iterateDown F)) := by
  obtain ⟨r,hr⟩ := hInit
  obtain ⟨t,ht⟩ := polynomial_repeatNext hF
  refine ⟨r+p*(t.comp (2+4*p+q)+4*(4*p+1)+12)+10+q,fun a=>?_⟩
  let S:=weight a
  let N:=(init a).1
  let T:=t.eval (2+4*p.eval S+q.eval S)
  have hN : N≤p.eval S := hn a
  have hsz : ∀ k<N,weight (k+1)≤4*p.eval S+1 := by
    intro k hk
    have hh:=weight_nat_le (k+1)
    have hbit : (k+1).size≤k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hc:=Repeat.cost_bound (f:=f) (Repeat.nextRealizer F).cost (I a) N (init a).2
    T (4*p.eval S+1) (hi a) (by
      intro k hk z hz
      refine ⟨hs a k hk z hz,?_⟩
      have h1:=ht (k+1,z)
      have h2:=hsz k hk
      have h3:=hw a (k+1) z hz
      have h4:=polynomial_eval_monotone t (show weight (k+1,z)≤2+4*p.eval S+q.eval S by
        rw [weight_prod]; change weight z≤q.eval S at h3; omega)
      dsimp only at h4
      dsimp only [T]
      omega) hsz
  have hout:=hw a 0 (countDown f N (init a).2)
    (countDown_invariant (I a) (hi a) (hs a))
  have hinit:=hr a
  change _ ≤ r.eval S at hinit
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,
    Polynomial.eval_comp]
  change Init.cost a+Repeat.cost f (Repeat.nextRealizer F).cost N (init a).2+
    weight (countDown f N (init a).2) ≤ r.eval S+p.eval S*(T+4*(4*p.eval S+1)+12)+10+q.eval S
  change _≤q.eval S at hout
  have hm:=Nat.mul_le_mul_right (T+4*(4*p.eval S+1)+12) hN
  omega

lemma polynomial_listLength : PolynomialTime (listLength (A:=A)) := by
  unfold listLength
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
  apply polynomial_fold (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 1)) polynomial_add)
    (4*X+5)
  intro as n pre post he
  have hf : pre.foldl (fun z (_ : A)=>z+1) n=n+pre.length := by
    clear he
    induction pre generalizing n with
    | nil => simp
    | cons a pre ih => simp only [List.foldl_cons,ih,List.length_cons]; omega
  change weight (pre.foldl (fun z (_ : A)=>z+1) n)≤_
  rw [hf]
  have h:=weight_nat_le (n+pre.length)
  have hs:=nat_size_add n pre.length
  have hl : pre.length.size≤pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have hn:=size_le_weight n
  have hp:pre.length≤weight as := (list_length_le_weight pre).trans (weight_prefix he)
  have hm : max n.size pre.length.size≤weight as+weight n := max_le (by omega) (by omega)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialGCD
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

lemma polynomial_boolNot : PolynomialTime boolNot := by
  unfold boolNot
  exact polynomial_congr _ (polynomial_choose polynomial_identity (polynomial_constant false) (polynomial_constant true))
lemma polynomial_boolAnd : PolynomialTime boolAnd := by
  unfold boolAnd
  exact polynomial_congr _ (polynomial_choose polynomial_first polynomial_second (polynomial_constant false))
lemma polynomial_natEqual : PolynomialTime natEqual := by
  unfold natEqual
  apply polynomial_congr
  apply polynomial_choose polynomial_less (polynomial_constant false)
  exact polynomial_choose (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less)
    (polynomial_constant false) (polynomial_constant true)
lemma polynomial_quotient : PolynomialTime quotient := polynomial_composition polynomial_division polynomial_first
lemma polynomial_remainder : PolynomialTime remainder := polynomial_composition polynomial_division polynomial_second
lemma polynomial_digits : PolynomialTime digits := by
  refine ⟨X+1,?_⟩
  intro a
  change 1+weight a≤_
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  omega
lemma polynomial_bitSize : PolynomialTime bitSize := by
  unfold bitSize
  exact polynomial_congr _ (polynomial_composition polynomial_digits polynomial_listLength)
lemma polynomial_sortedPair : PolynomialTime sortedPairRealizer := by
  unfold sortedPairRealizer
  exact polynomial_congr _ (polynomial_choose polynomial_less (polynomial_pair polynomial_second polynomial_first) polynomial_identity)
lemma polynomial_gcdStep : PolynomialTime gcdStepRealizer := by
  unfold gcdStepRealizer
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0)) polynomial_natEqual)
    polynomial_identity (polynomial_pair polynomial_second polynomial_remainder))
lemma gcdStep_size_le (x : ℕ×ℕ) : (gcdStep x).1.size+(gcdStep x).2.size≤x.1.size+x.2.size := by
  dsimp only [gcdStep]
  split_ifs with h
  · exact le_rfl
  · simp only
    have hm:=Nat.size_le_size (Nat.mod_le x.1 x.2)
    omega
lemma polynomial_gcd : PolynomialTime gcd := by
  unfold gcd
  apply polynomial_congr
  apply polynomial_composition _ polynomial_first
  apply polynomial_boundedRepeat
    (polynomial_pair (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_bitSize)
      (polynomial_composition polynomial_second polynomial_bitSize)) polynomial_add) polynomial_sortedPair)
    (polynomial_composition polynomial_second polynomial_gcdStep) X (4*X+3)
    (fun x _ z=>z.1.size+z.2.size≤x.1.size+x.2.size)
  · intro x
    simp only [Polynomial.eval_X,Function.comp_apply]
    have h1:=size_le_weight x.1
    have h2:=size_le_weight x.2
    rw [←Prod.eta x,weight_prod]
    try dsimp only
    omega
  · intro x
    exact (sortedPair_size x).le
  · intro x _iteration _bounded z hz
    exact (gcdStep_size_le z).trans hz
  · intro x _iteration z hz
    have ha:=weight_nat_le z.1
    have hb:=weight_nat_le z.2
    have hx:=size_le_weight x.1
    have hy:=size_le_weight x.2
    rw [←Prod.eta z,weight_prod]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    rw [←Prod.eta x,weight_prod]
    try dsimp only
    omega
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma polynomial_normalize : PolynomialTime normalizeRealizer := by
  unfold normalizeRealizer
  apply polynomial_congr
  apply polynomial_choose
  · exact polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0)) polynomial_natEqual
  · exact polynomial_constant (0,1)
  · exact polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first polynomial_gcd) polynomial_quotient)
      (polynomial_composition (polynomial_pair polynomial_second polynomial_gcd) polynomial_quotient)
lemma polynomial_mul : PolynomialTime mulRealizer := by
  unfold mulRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)) polynomial_normalize
lemma polynomial_div : PolynomialTime divRealizer := by
  unfold divRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_fst polynomial_second)) polynomial_multiply)) polynomial_normalize
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialCollections
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma polynomial_listCase (b : B) {g : A×List A → B} {G : Realizer g}
    (hG : PolynomialTime G) : PolynomialTime (listCase b G) := by
  obtain ⟨p,hp⟩:=hG
  obtain ⟨q,hq⟩:=polynomial_constant (A:=List A) b
  refine ⟨p+q+3,fun as=>?_⟩
  simp only [Polynomial.eval_add,Polynomial.eval_ofNat]
  cases as with
  | nil =>
    have hh:=hq []
    change (constant b (A:=List A)).cost []+weight b≤_ at hh
    change 3+(constant b (A:=List A)).cost []+weight b≤_
    omega
  | cons a as =>
    have hh:=hp (a,as)
    have he : weight (a,as)=weight (a::as) := rfl
    rw [he] at hh
    change 3+G.cost (a,as)+weight (g (a,as))≤_
    omega
lemma polynomial_head (d : A) : PolynomialTime (head d) := by
  unfold head
  exact polynomial_congr _ (polynomial_listCase d polynomial_first)
lemma polynomial_tail : PolynomialTime (tail (A:=A)) := polynomial_listCase [] polynomial_second
lemma weight_sublist {as bs : List A} (h : as.Sublist bs) : weight as≤weight bs := by
  induction h with
  | slnil => exact le_rfl
  | cons a h ih => rw [weight_cons]; omega
  | cons_cons a h ih => simp only [weight_cons]; omega
lemma polynomial_append : PolynomialTime (append (A:=A)) := by
  unfold append
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_reverse) polynomial_second)
  apply polynomial_fold polynomial_listCons (2*X+1)
  intro as bs pre post he
  simp only [List.foldl_flip_cons_eq_append']
  have hh:=weight_append pre.reverse bs
  rw [weight_reverse] at hh
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
lemma polynomial_mapStep {f : A×B → C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapStepRealizer F) := by
  unfold mapStepRealizer
  exact polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_first) hF)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_listCons)
lemma polynomial_mapWith {f : A×B → C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapWith F) := by
  unfold mapWith
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_composition polynomial_second polynomial_reverse)
  apply polynomial_composition (polynomial_pair polynomial_second (polynomial_pair polynomial_first (polynomial_constant [])))
  obtain ⟨p,hp⟩:=hF
  apply polynomial_fold (polynomial_mapStep ⟨p,hp⟩) (2*X+X*(p.comp (1+2*X)+1)+2)
  rintro bs ⟨a,cs⟩ pre post he
  let S:=weight (bs,(a,cs))
  have hb : weight bs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have ha : weight a≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hc : weight cs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hl : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans hb)
  have hm:=weight_map_bound (f:=fun b=>f (a,b)) (as:=pre) (N:=p.eval (1+2*S)) (by
    intro b hmem
    have hbs:=weight_mem hmem
    have hpre:=weight_prefix he
    have hh:=hp (a,b)
    have ht:=polynomial_eval_monotone p (show weight (a,b)≤1+2*S by rw [weight_prod]; omega)
    dsimp only at ht
    omega)
  rw [mapStep_fold,weight_prod]
  have happ:=weight_append (pre.map fun b=>f (a,b)).reverse cs
  rw [weight_reverse] at happ
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change _≤2*S+S*(p.eval (1+2*S)+1)+2
  nlinarith [Nat.mul_le_mul_right (p.eval (1+2*S)+1) hl]
lemma polynomial_map {f : A → B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (map F) := by
  unfold map
  apply polynomial_congr
  apply polynomial_composition _ polynomial_reverse
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
  obtain ⟨p,hp⟩:=hF
  apply polynomial_fold (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first ⟨p,hp⟩) polynomial_second) polynomial_listCons)
    (X+X*(p+1)+1)
  intro as bs pre post he
  let S:=weight (as,bs)
  have ha : weight as≤S := by dsimp [S]; rw [weight_prod]; omega
  have hb : weight bs≤S := by dsimp [S]; rw [weight_prod]; omega
  have hl : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans ha)
  have hm:=weight_map_bound (f:=f) (as:=pre) (N:=p.eval S) (by
    intro a hmem
    have hh:=hp a
    have ht:=polynomial_eval_monotone p ((weight_mem hmem).trans ((weight_prefix he).trans ha))
    dsimp only at ht
    omega)
  have hfold : pre.foldl (fun bs a=>f a::bs) bs=(pre.map f).reverse++bs := by
    simp [List.foldl_flip_cons_eq_append]
  change weight (pre.foldl (fun bs a=>f a::bs) bs)≤_
  rw [hfold]
  have happ:=weight_append (pre.map f).reverse bs
  rw [weight_reverse] at happ
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  change _≤S+S*(p.eval S+1)+1
  nlinarith [Nat.mul_le_mul_right (p.eval S+1) hl]
omit [Codec A] in
lemma filter_fold (f : A → Bool) (as bs : List A) :
    as.foldl (fun bs a=>if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => cases hf:f a <;> simp [List.foldl_cons,hf,ih,List.append_assoc]
lemma polynomial_filter {f : A → Bool} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (filter F) := by
  unfold filter
  apply polynomial_congr
  apply polynomial_composition _ polynomial_reverse
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
  apply polynomial_fold (polynomial_choose (polynomial_composition polynomial_first hF) polynomial_listCons polynomial_second) (2*X+1)
  intro as bs pre post he
  change weight (pre.foldl (fun bs a=>if f a then a::bs else bs) bs)≤_
  rw [filter_fold]
  have happ:=weight_append (pre.filter f).reverse bs
  rw [weight_reverse] at happ
  have hf:=weight_sublist (List.filter_sublist (p:=f) (l:=pre))
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega
lemma weight_bool_le (b : Bool) : weight b≤3 := by cases b <;> decide
lemma polynomial_any : PolynomialTime any := by
  unfold any
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
  apply polynomial_fold (polynomial_choose polynomial_first (polynomial_constant true) polynomial_second) 3
  intro as b pre post he
  simpa using weight_bool_le (pre.foldl (fun z b=>if b then true else z) b)
lemma polynomial_membership : PolynomialTime membership := by
  unfold membership
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_mapWith polynomial_natEqual)) polynomial_any)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeCanonical
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

lemma polynomial_contains [DecidableEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (contains E) := by
  unfold contains
  exact polynomial_congr _ (polynomial_composition (polynomial_mapWith hE) polynomial_any)

lemma weight_dedupFold [DecidableEq A] (as bs : List A) :
    weight (as.foldl (fun bs a=>dedupStep (a,bs)) bs)≤weight as+weight bs := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons]
    have hh:=ih (dedupStep (a,bs))
    simp only [weight_cons]
    have hs : weight (dedupStep (a,bs))≤1+weight a+weight bs := by
      change weight (if a∈bs then bs else a::bs)≤_
      split_ifs
      · omega
      · rw [weight_cons]
    omega
lemma polynomial_dedup [DecidableEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (dedup E) := by
  unfold dedup
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold (polynomial_congr _ (polynomial_choose (polynomial_contains hE) polynomial_second polynomial_listCons)) (2*X+1)
  intro as bs pre post he
  have hh:=weight_dedupFold pre bs
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

variable (r : A → A → Prop) [DecidableRel r]
lemma weight_perm {as bs : List A} (h : as.Perm bs) : weight as=weight bs := by
  simp only [weight,size_encode_list,h.length_eq,(h.map (fun a=>TreeFunction.size (encode a))).sum_eq]
lemma weight_orderedInsert (a : A) (as : List A) :
    weight (List.orderedInsert r a as)=1+weight a+weight as := by
  rw [weight_perm (List.perm_orderedInsert r a as),weight_cons]
lemma polynomial_insertStep {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (insertStepRealizer r R) := by
  unfold insertStepRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_fst polynomial_second)
  apply polynomial_pair (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst (polynomial_snd polynomial_second))) polynomial_listCons)
  exact polynomial_choose (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hR)
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst (polynomial_snd polynomial_second))) polynomial_listCons)) polynomial_listCons)
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_snd (polynomial_snd polynomial_second))) polynomial_listCons)
lemma insert_fold_bound (as bs cs : List A) (a : A) :
    weight ((as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).2.1)≤weight as+weight bs ∧
    weight ((as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).2.2)≤2*weight as+weight bs+weight cs+weight a+1 ∧
    (as.foldl (fun z b=>insertStep r (b,z)) (a,(bs,cs))).1=a := by
  induction as generalizing bs cs with
  | nil =>
    change weight bs≤1+weight bs ∧ weight cs≤2+weight bs+weight cs+weight a+1 ∧ a=a
    exact ⟨by omega,by omega,rfl⟩
  | cons b as ih =>
    rw [List.foldl_cons]
    by_cases h : r a b
    · have hs : insertStep r (b,(a,(bs,cs)))=(a,(b::bs,a::b::bs)) := by simp [insertStep,h]
      rw [hs]
      have he:=insert_fold r as.reverse (b::bs) a
      simp only [List.reverse_reverse] at he
      have ho : List.orderedInsert r a (b::bs)=a::b::bs := by simp [h]
      rw [ho] at he
      rw [he]
      have hw:=weight_append as.reverse (b::bs)
      rw [weight_reverse,weight_cons] at hw
      simp only [weight_orderedInsert,weight_cons]
      exact ⟨by omega,by omega,trivial⟩
    · have hs : insertStep r (b,(a,(bs,cs)))=(a,(b::bs,b::cs)) := by simp [insertStep,h]
      rw [hs]
      have hh:=ih (b::bs) (b::cs)
      simp only [weight_cons] at hh ⊢
      exact ⟨by omega,by omega,hh.2.2⟩
lemma polynomial_orderedInsert {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (orderedInsert r R) := by
  unfold orderedInsert
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_snd polynomial_second)
  apply polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
    (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant [])
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_listCons))))
  apply polynomial_fold (polynomial_insertStep r hR) (5*X+10)
  rintro as ⟨a,bs,cs⟩ pre post he
  have hh:=insert_fold_bound r pre bs cs a
  have hp:=weight_prefix he
  rw [weight_prod,hh.2.2,weight_prod]
  calc
    _ ≤ 1+weight a+(1+(weight pre+weight bs)+(2*weight pre+weight bs+weight cs+weight a+1)) := by
      gcongr
      · exact hh.1
      · exact hh.2.1
    _ ≤ _ := by
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
      omega

lemma weight_insertFold (as bs : List A) :
    weight (as.foldl (fun bs a=>List.orderedInsert r a bs) bs)+1=weight as+weight bs := by
  induction as generalizing bs with
  | nil => simp only [List.foldl_nil,weight_nil]; omega
  | cons a as ih =>
    rw [List.foldl_cons]
    have hh:=ih (List.orderedInsert r a bs)
    rw [weight_orderedInsert] at hh
    rw [weight_cons]
    omega
lemma polynomial_insertionSort {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hR : PolynomialTime R) : PolynomialTime (insertionSort r R) := by
  unfold insertionSort
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold (polynomial_orderedInsert r hR) (2*X+1)
  intro as bs pre post he
  have hh:=weight_insertFold r pre bs
  have hp:=weight_prefix he
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

variable [DecidableEq A]
lemma polynomial_canonical {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (r x.1 x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (canonical r E R) :=
  polynomial_composition (polynomial_dedup hE) (polynomial_insertionSort r hR)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFinite
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

lemma polynomial_recode {f : C → D} {F : Realizer f} (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a))
    (hF : PolynomialTime F) : PolynomialTime (F.recode i g hi ho) := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  have h:=hp (i a)
  change F.cost (i a)+weight (g a)≤_
  simpa only [weight,hi,ho] using h

variable [LinearOrder A]

lemma polynomial_finsetList : PolynomialTime (finsetList (A:=A)) := by
  unfold finsetList
  exact polynomial_recode _ _ _ _ polynomial_identity

lemma polynomial_listFinset {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (listFinset E R) := by
  unfold listFinset
  exact polynomial_recode _ _ _ _ (polynomial_canonical _ hE hR)

lemma polynomial_finsetMember {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetMember E) := by
  unfold finsetMember
  exact polynomial_recode _ _ _ _ (polynomial_contains hE)

lemma polynomial_finsetCard : PolynomialTime (finsetCard (A:=A)) := by
  unfold finsetCard
  exact polynomial_congr _ (polynomial_composition polynomial_finsetList polynomial_listLength)

lemma polynomial_finsetUnion {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetUnion E R) := by
  unfold finsetUnion
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_finsetList)
      (polynomial_composition polynomial_second polynomial_finsetList)) polynomial_append)
    (polynomial_listFinset hE hR))

lemma polynomial_finsetImage [LinearOrder B] {f : A → B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetImage F E R) := by
  unfold finsetImage
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_finsetList (polynomial_map hF)) (polynomial_listFinset hE hR))

lemma polynomial_finsetFilter {p : A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetFilter P) := by
  unfold finsetFilter
  exact polynomial_recode _ _ _ _ (polynomial_filter hP)

omit [LinearOrder A] in
lemma polynomial_filterWith {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (filterWith P) := by
  unfold filterWith
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_mapWith (polynomial_pair polynomial_second hP))
      (polynomial_filter polynomial_second)) (polynomial_map polynomial_first))
lemma polynomial_finsetFilterWith {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetFilterWith P) := by
  unfold finsetFilterWith
  exact polynomial_recode _ _ _ _ (polynomial_filterWith hP)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeCostMeasure
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma work_of_polynomial {f : A → B} {F : Realizer f} (hF : PolynomialTime F)
    {measure : A → ℕ} (p : Polynomial ℕ) (hp : ∀ a,weight a≤p.eval (measure a)) : WorkBound F measure := by
  obtain ⟨q,hq⟩:=hF
  exact ⟨q.comp p,fun a=>(hq a).trans (by simpa using polynomial_eval_monotone q (hp a))⟩
lemma work_congr {f g : A → B} {F : Realizer f} {measure : A → ℕ}
    (h : ∀ a,f a=g a) (hF : WorkBound F measure) : WorkBound (F.congr h) measure := by
  obtain ⟨p,hp⟩:=hF
  exact ⟨p,fun a=>by simpa only [Realizer.congr,←h a] using hp a⟩
lemma work_composition {f : A → B} {g : B → C} {F : Realizer f} {G : Realizer g}
    {measure : A → ℕ} {other : B → ℕ}
    (hF : WorkBound F measure) (hG : WorkBound G other) (p : Polynomial ℕ)
    (hm : ∀ a,other (f a)≤p.eval (measure a)) : WorkBound (composition F G) measure := by
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=hG
  refine ⟨q+r.comp p,fun a=>?_⟩
  have h1:=hq a
  have h2:=hr (f a)
  have h3:=polynomial_eval_monotone r (hm a)
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  change F.cost a+G.cost (f a)+weight (g (f a))≤_
  dsimp only at h3
  omega
lemma work_remeasure {f : A → B} {F : Realizer f} {measure other : A → ℕ}
    (hF : WorkBound F measure) (p : Polynomial ℕ) (hm : ∀ a,measure a≤p.eval (other a)) :
    WorkBound F other := by
  obtain ⟨q,hq⟩:=hF
  exact ⟨q.comp p,fun a=>(hq a).trans (by simpa using polynomial_eval_monotone q (hm a))⟩

lemma work_boundedRepeat {init : A → ℕ×B} {f : ℕ×B → B}
    {Init : Realizer init} {F : Realizer f} {measure : A → ℕ}
    (hInit : WorkBound Init measure) (hF : PolynomialTime F)
    (p q : Polynomial ℕ) (I : A → ℕ → B → Prop)
    (hn : ∀ a,(init a).1≤p.eval (measure a))
    (hi : ∀ a,I a (init a).1 (init a).2)
    (hs : ∀ a k,(k<(init a).1) → ∀ z,I a (k+1) z → I a k (f (k+1,z)))
    (hw : ∀ a k z,I a k z → weight z≤q.eval (measure a)) :
    WorkBound (composition Init (iterateDown F)) measure := by
  obtain ⟨r,hr⟩:=hInit
  obtain ⟨t,ht⟩:=polynomial_repeatNext hF
  refine ⟨r+p*(t.comp (2+4*p+q)+4*(4*p+1)+12)+10+q,fun a=>?_⟩
  let S:=measure a
  let N:=(init a).1
  let T:=t.eval (2+4*p.eval S+q.eval S)
  have hN : N≤p.eval S:=hn a
  have hsz : ∀ k<N,weight (k+1)≤4*p.eval S+1 := by
    intro k hk
    have hh:=weight_nat_le (k+1)
    have hbit : (k+1).size≤k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hc:=Repeat.cost_bound (f:=f) (Repeat.nextRealizer F).cost (I a) N (init a).2
    T (4*p.eval S+1) (hi a) (by
      intro k hk z hz
      refine ⟨hs a k hk z hz,?_⟩
      have h1:=ht (k+1,z)
      have h2:=hsz k hk
      have h3:=hw a (k+1) z hz
      change weight z≤q.eval S at h3
      have h4:=polynomial_eval_monotone t (show weight (k+1,z)≤2+4*p.eval S+q.eval S by rw [weight_prod]; omega)
      dsimp only at h4
      dsimp only [T]
      omega) hsz
  have hout:=hw a 0 (countDown f N (init a).2)
    (countDown_invariant (I a) (hi a) (hs a))
  have hinit:=hr a
  change _ ≤ r.eval S at hinit
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one,
    Polynomial.eval_comp]
  change Init.cost a+Repeat.cost f (Repeat.nextRealizer F).cost N (init a).2+
    weight (countDown f N (init a).2) ≤ r.eval S+p.eval S*(T+4*(4*p.eval S+1)+12)+10+q.eval S
  change _≤q.eval S at hout
  have hm:=Nat.mul_le_mul_right (T+4*(4*p.eval S+1)+12) hN
  omega

lemma weight_nat_numeric (n : ℕ) : weight n≤4*n+1 := by
  have h:=weight_nat_le n
  have hn : n.size≤n := Nat.size_le.mpr Nat.lt_two_pow_self
  omega
lemma polynomial_successor : PolynomialTime successor :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1)) polynomial_add)
lemma polynomial_rangeStep : PolynomialTime rangeStepRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_predecessor) polynomial_second) polynomial_listCons

lemma range_numeric_work : WorkBound range id := by
  unfold range
  apply work_congr
  apply work_boundedRepeat (work_of_polynomial (polynomial_pair polynomial_identity (polynomial_constant []))
    (4*X+1) (fun n=>by simpa using weight_nat_numeric n)) polynomial_rangeStep X (4*X^2+2*X+1)
    (fun n k zs=>zs.length+k=n ∧ ∀ z∈zs,z<n)
  · intro n; simp
  · intro n; simp
  · intro n k hk zs hz
    change k<n at hk
    change ((k+1-1)::zs).length+k=n ∧ ∀ z∈((k+1-1)::zs),z<n
    simp only [Nat.add_sub_cancel,List.length_cons,List.mem_cons]
    constructor
    · omega
    · intro z h
      rcases h with rfl | h
      · exact hk
      · exact hz.2 z h
  · intro n k zs hz
    have hh:=weight_map_bound (as:=zs) (f:=id) (N:=4*n+1) (by
      intro z h
      exact (weight_nat_numeric z).trans (by have :=hz.2 z h; omega))
    simp only [List.map_id] at hh
    have hlen:zs.length≤n:=by omega
    have hm:=Nat.mul_le_mul_right (4*n+2) hlen
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_pow,Polynomial.eval_one,id_eq]
    nlinarith

lemma polynomial_boundedRange {f : A → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,f a≤p.eval (weight a)) : PolynomialTime (composition F range) :=
  work_composition hF range_numeric_work p hn

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteOps
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma polynomial_all : PolynomialTime all := by
  unfold all
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_map polynomial_boolNot) polynomial_any) polynomial_boolNot)

lemma polynomial_pairEqual [DecidableEq A] [DecidableEq B]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {F : Realizer (fun x : B×B=>decide (x.1=x.2))}
    (hE : PolynomialTime E) (hF : PolynomialTime F) : PolynomialTime (pairEqual E F) := by
  unfold pairEqual
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hE)
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) hF)) polynomial_boolAnd)

lemma polynomial_leNat : PolynomialTime leNat := by
  unfold leNat
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less) polynomial_boolNot)

variable [LinearOrder A]
lemma polynomial_finsetAny {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetAny P) := by
  unfold finsetAny
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith hP)) polynomial_any)

lemma polynomial_finsetAll {p : B×A → Bool} {P : Realizer p} (hP : PolynomialTime P) :
    PolynomialTime (finsetAll P) := by
  unfold finsetAll
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith hP)) polynomial_all)

lemma polynomial_finsetSubset {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetSubset E) := by
  unfold finsetSubset
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetAll (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE))))

lemma polynomial_finsetEqual {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetEqual E) := by
  unfold finsetEqual
  exact polynomial_congr _ (polynomial_composition (polynomial_pair (polynomial_finsetSubset hE)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetSubset hE))) polynomial_boolAnd)

lemma polynomial_finsetSDiff {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetSDiff E) := by
  unfold finsetSDiff
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE)) polynomial_boolNot)))

lemma polynomial_finsetInter {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetInter E) := by
  unfold finsetInter
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_finsetFilterWith (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetMember hE))))

lemma polynomial_finsetErase {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (finsetErase E) := by
  unfold finsetErase
  exact polynomial_congr _ (polynomial_finsetFilterWith (polynomial_composition hE polynomial_boolNot))
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFastLookup
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

lemma polynomial_minNat : PolynomialTime minNat :=
  polynomial_congr _ (polynomial_choose polynomial_leNat polynomial_first polynomial_second)

lemma polynomial_dropInit : PolynomialTime (dropInit (A:=A)) := by
  unfold dropInit
  exact polynomial_pair (polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_listLength)) polynomial_minNat) polynomial_first

lemma polynomial_dropFast : PolynomialTime (dropFast (A:=A)) := by
  unfold dropFast
  apply polynomial_congr
  apply polynomial_boundedRepeat polynomial_dropInit
    (polynomial_composition polynomial_second polynomial_tail) X X
    (fun x _ z=>z.Sublist x.1)
  · intro x
    simp only [Polynomial.eval_X]
    exact (min_le_right _ _).trans ((list_length_le_weight x.1).trans (by rw [weight_prod]; omega))
  · intro x; exact List.Sublist.refl _
  · intro x k hk z hz
    exact (List.tail_sublist z).trans hz
  · intro x k z hz
    simp only [Polynomial.eval_X]
    exact (weight_sublist hz).trans (by rw [weight_prod]; omega)

lemma polynomial_getDFast (d : A) : PolynomialTime (getDFast d) :=
  polynomial_congr _ (polynomial_composition polynomial_dropFast (polynomial_head d))

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialSums
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

lemma nat_fold_size_bound (f : ℕ×ℕ → ℕ) (K M : ℕ)
    (hf : ∀ a b,(f (a,b)).size≤a.size+b.size+K) (as : List ℕ) (z : ℕ)
    (ha : ∀ a∈as,a.size≤M) :
    (as.foldl (fun z a=>f (a,z)) z).size≤z.size+as.length*(M+K) := by
  induction as generalizing z with
  | nil => simp
  | cons a as ih =>
    have hh:=hf a z
    have ha':=ha a (by simp)
    have ht:=ih (f (a,z)) (fun a h=>ha a (by simp [h]))
    simp only [List.foldl_cons,List.length_cons]
    nlinarith
lemma polynomial_nat_fold {f : ℕ×ℕ → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (K : ℕ) (hf : ∀ a b,(f (a,b)).size≤a.size+b.size+K) : PolynomialTime (fold F) := by
  apply polynomial_fold hF (4*X+4*X*(X+Polynomial.C K)+1)
  intro as z pre post he
  let S:=weight (as,z)
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; rw [weight_prod]; omega))
  have ha : ∀ a∈pre,a.size≤S := by
    intro a ha
    exact (size_le_weight a).trans ((weight_mem (as := as) (by simp [he,ha])).trans (by dsimp [S]; rw [weight_prod]; omega))
  have hz : z.size≤S := (size_le_weight z).trans (by dsimp [S]; rw [weight_prod]; omega)
  have hb:=nat_fold_size_bound f K S hf pre z ha
  have hw:=weight_nat_le (pre.foldl (fun z a=>f (a,z)) z)
  have hm:=Nat.mul_le_mul_right (S+K) hp
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one]
  change _≤4*S+4*S*(S+K)+1
  nlinarith
lemma polynomial_listSum : PolynomialTime listSum := by
  unfold listSum
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
    (polynomial_nat_fold polynomial_add 1 (fun a b=>(nat_size_add a b).trans (by omega)))
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseIntegerProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list arithmetic for integral dense completion -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

theorem polynomial_matrixEntry : PolynomialTime matrixEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeFiniteCollections
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma weight_flatten (as : List (List A)) : weight as.flatten≤weight as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatten_cons,weight_cons]
    have h:=weight_append a as.flatten
    omega

lemma polynomial_flatten : PolynomialTime (flatten (A:=A)) := by
  unfold flatten
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant []))
  apply polynomial_fold polynomial_append (2*X+1)
  intro as bs pre post he
  rw [fold_prepend]
  have h1:=weight_append pre.reverse.flatten bs
  have h2:=weight_flatten pre.reverse
  rw [weight_reverse] at h2
  have h3:=weight_prefix he
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma polynomial_flatMapPoly {f : A → List B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (flatMapPoly F) :=
  polynomial_congr _ (polynomial_composition (polynomial_map hF) polynomial_flatten)

variable [LinearOrder A]
lemma polynomial_finsetSingleton : PolynomialTime (finsetSingleton (A:=A)) := by
  unfold finsetSingleton
  exact polynomial_recode _ _ _ _ (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_constant [])) polynomial_listCons)

lemma polynomial_finsetInsert {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (finsetInsert E R) :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_finsetSingleton) polynomial_second)
    (polynomial_finsetUnion hE hR))

variable [LinearOrder B]
lemma polynomial_finsetBiUnion {f : C×A → Finset B} {F : Realizer f}
    {E : Realizer (fun x : B×B=>decide (x.1=x.2))}
    {R : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hF : PolynomialTime F) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (finsetBiUnion F E R) := by
  unfold finsetBiUnion
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith (polynomial_composition hF polynomial_finsetList))) polynomial_flatten)
    (polynomial_listFinset hE hR)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeColex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B] [LinearOrder A] [LinearOrder B]

lemma polynomial_boolOr : PolynomialTime boolOr := by
  unfold boolOr
  exact polynomial_congr _ (polynomial_choose polynomial_first (polynomial_constant true) polynomial_second)

lemma polynomial_colexLe {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) : PolynomialTime (colexLe E R) := by
  unfold colexLe
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_finsetSDiff hE))
    (polynomial_finsetSDiff hE))
    (polynomial_finsetAll (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_finsetAny hR)))

lemma polynomial_lexLe {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    {S : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hE : PolynomialTime E) (hR : PolynomialTime R) (hS : PolynomialTime S) :
    PolynomialTime (lexLe E R S) := by
  unfold lexLe
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hR)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_first) (polynomial_fst polynomial_second)) hE) polynomial_boolNot)
      (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) hS)) polynomial_boolOr))
    polynomial_boolAnd)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeSum
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

omit [Codec B] [Codec C] [Codec D] in
lemma polynomial_some [Inhabited A] : PolynomialTime (some (A:=A)) := by
  unfold some
  apply polynomial_recode
  ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe | apply polynomial_congr)))

omit [Codec B] in
lemma polynomial_optionCases [Inhabited A] {f : C→D} {g : C×A→D}
    {F : Realizer f} {G : Realizer g} (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (optionCases F G) := by
  unfold optionCases
  apply polynomial_recode
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe | apply polynomial_congr)))
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating the actual small cells from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_pairAt : PolynomialTime pairAtRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_pair polynomial_quotient polynomial_remainder)

lemma polynomial_cellPairCodes : PolynomialTime cellPairCodes := by
  apply polynomial_boundedRange (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_multiply) (X^2)
  intro z
  have hr : z.1.length≤weight z :=
    (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  have hc : z.2.length≤weight z :=
    (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  simpa only [Function.comp_apply,eval_pow,eval_mul,eval_X,pow_two] using Nat.mul_le_mul hr hc

theorem polynomial_cellPairs : PolynomialTime cellPairsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_listLength) polynomial_cellPairCodes)
    (polynomial_mapWith polynomial_pairAt)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the companion's retained small-cell capacities

The program scans the rectangular cell list determined by the two
margin-list lengths, then tests the binary cell bound against W. It
does not enumerate up to the numeric value of a capacity.
-/

namespace ContingencyTables.CompanionCellCatalog

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_second) polynomial_matrixEntry

lemma polynomial_retainedTest : PolynomialTime retainedTestRealizer :=
  polynomial_composition (polynomial_pair polynomial_entry
    (polynomial_composition polynomial_first polynomial_second)) polynomial_less

theorem polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_retainedTest)

theorem polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_catalog)
    (polynomial_mapWith polynomial_entry)

noncomputable section
open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma capacities_eq (A : Instance (Fin m) (Fin n)) :
    capacities (input A)=List.ofFn (fun i => A.b ((cellEquiv A) i).val.1 ((cellEquiv A) i).val.2) := by
  apply List.ext_getElem
  · simp only [capacities,List.length_map,List.length_ofFn]
  · intro i hi hj
    have hi' : i<(catalog (input A)).length := by simpa only [List.length_ofFn] using hj
    simp only [capacities,List.getElem_map,List.getElem_ofFn]
    have he := catalogCell_coordinates A ⟨i,hi'⟩
    change entry (input A,(catalog (input A))[i]'hi')=
      A.b (catalogCell A ⟨i,hi'⟩).val.1 (catalogCell A ⟨i,hi'⟩).val.2
    rw [←he]
    exact entry_input A _ _

end
end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreePolynomialGrid
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma weight_fst (a : A×B) : weight a.1≤weight a := by rcases a with ⟨a,b⟩; simp only [weight_prod]; omega
lemma weight_snd (a : A×B) : weight a.2≤weight a := by rcases a with ⟨a,b⟩; simp only [weight_prod]; omega

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeChoiceCosts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A]

lemma polynomial_takeFast : PolynomialTime (takeFast (A:=A)) := by
  unfold takeFast
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_reverse)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_listLength)
      polynomial_second) polynomial_subtract)) polynomial_dropFast) polynomial_reverse
omit [Codec A] in
lemma polynomial_minimum : PolynomialTime minimum := by
  unfold minimum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit scalar schedules for the adaptive counting phases

Every precision and sample length below is a rational or natural arithmetic
expression. In particular the dyadic exponents use a polynomial reciprocal
allowance, so no real logarithm is evaluated by the algorithm.
-/

namespace ContingencyTables.CountingPhaseSchedule

open scoped BigOperators

lemma tolerance_pos (H : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    0 < tolerance H epsilon := by
  unfold tolerance
  positivity

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalSchedule
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the terminal coefficient without real logarithms

The source's ceiling of log₂(1/epsilon) is exactly the natural ceiling
logarithm of ceil(1/epsilon). All terminal metadata can therefore be
computed with natural and rational arithmetic.
-/

namespace ContingencyTables.CountingTerminalSchedule

open CompanionFactorialApplication CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type} [Fintype I] [Fintype J]

lemma finalPhase_eq (A : Instance I J) (L : ℕ) (epsilon : ℚ) (he : 0 < epsilon) :
    CompanionTerminalApplication.finalPhase A L (epsilon:ℝ)=
      rationalHeight A (coefficient L A.d epsilon) := by
  rw [CompanionTerminalApplication.finalPhase,←coefficient_eq L A.d A.hd epsilon he]
  rfl

end
end ContingencyTables.CountingTerminalSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_OffsetCountProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary tabulation of the bounded offset law -/

namespace ContingencyTables.OffsetCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_ceilQuotient : PolynomialTime ceilQuotientRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first polynomial_second) polynomial_add)
      (polynomial_constant 1)) polynomial_subtract)
    polynomial_second) polynomial_quotient

end ContingencyTables.OffsetCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleScheduleProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the counting oracle sample schedule -/

namespace ContingencyTables.CountingOracleScheduleProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_ceiling : PolynomialTime ceilingRealizer := OffsetCountPrograms.polynomial_ceilQuotient

lemma ceiling_val (e : Fraction) : ceiling e=⌈TreeFraction.val e⌉₊ := by
  by_cases h : e.2=0
  · simp only [ceiling,OffsetCountPrograms.ceilQuotient,TreeFraction.val,h,Nat.div_zero,
      Nat.cast_zero,div_zero,Nat.ceil_zero]
  · exact OffsetCountPrograms.ceilQuotient_eq e.1 e.2 (Nat.pos_of_ne_zero h)

lemma polynomial_natural : PolynomialTime naturalRealizer :=
  polynomial_pair polynomial_identity (polynomial_constant 1)
lemma natural_val (n : ℕ) : TreeFraction.val (natural n)=(n:ℚ) := by
  simp only [natural,TreeFraction.val,Nat.cast_one,div_one]

lemma sampleCount_val (j : ℕ) (delta failure : Fraction) :
    sampleCount (j,(delta,failure))=
      CompanionOracleDensity.sampleCount j (TreeFraction.val delta) (TreeFraction.val failure) := by
  rw [sampleCount,ceiling_val,sampleRatio,TreeFraction.div_val,sampleBase,natural_val,
    sampleDenominator,TreeFraction.mul_val,TreeFraction.mul_val]
  unfold CompanionOracleDensity.sampleCount
  congr 1
  push_cast
  ring

lemma offsetAccuracy_val (d : ℕ) (delta : Fraction) :
    offsetAccuracy (d,delta)=⌈4096*(d:ℚ)/TreeFraction.val delta⌉₊ := by
  rw [offsetAccuracy,ceiling_val,offsetRatio,TreeFraction.div_val,offsetBase,natural_val]
  simp only [Nat.cast_mul,Nat.cast_ofNat]


lemma oracleTime_val (M B : ℕ) (theta : Fraction) :
    oracleTime ((M,B),theta)=⌈(M:ℚ)*((B:ℚ)+16/TreeFraction.val theta)⌉₊ := by
  have he : (timeExtra ((M,B),theta)).2 ≠ 0 := by
    exact (TreeFraction.normalize_den_pos _).ne'
  rw [oracleTime,ceiling_val,timeTotal,TreeFraction.add_val _ _ (by change (1:ℕ) ≠ 0; decide) he,
    timeBase,natural_val,timeExtra,TreeFraction.div_val,timeNumerator,natural_val]
  congr 1
  push_cast
  ring

lemma oracleTime_instance {I J : Type} [Fintype I] [Fintype J]
    (A : CompanionFactorialApplication.Instance I J) (C K : ℕ) (theta : Fraction) :
    oracleTime ((2*(10000*A.d^2*K)^2,
      CompanionOracleDensity.rationalHeight A C+A.d*K+2),theta)=
      CompanionOracleDensity.oracleTime A C K 1 (TreeFraction.val theta) := by
  rw [oracleTime_val,CompanionOracleDensity.oracleTime]
  rw [←CountingTerminalSchedule.natCeil_ratCast]
  congr 1
  simp only [CompanionOracleDensity.mixingConstant,CompanionOracleDensity.rationalHeight,
    CompanionOracleDensity.height,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,
    Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_pow]
  ring

end ContingencyTables.CountingOracleScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the scalar counting schedules

These circuits only read a fixed finite list and perform binary addition
and multiplication. Their syntax describes the fixed program, not a
numeric loop selected by the input.
-/

namespace ContingencyTables.ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma Expr.polynomial (e : Expr) : PolynomialTime e.realizer := by
  induction e with
  | input i => exact polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_constant i)) (polynomial_getDFast 0)
  | number n => exact polynomial_constant n
  | plus a b ha hb => exact polynomial_composition (polynomial_pair ha hb) polynomial_add
  | times a b ha hb => exact polynomial_composition (polynomial_pair ha hb) polynomial_multiply

lemma Expr.eval_pow (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a.pow n).eval xs=(a.eval xs)^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Expr.pow,Expr.eval,ih,pow_succ]


@[simp] lemma Expr.eval_power (a : Expr) (n : ℕ) (xs : List ℕ) :
    (a^n).eval xs=(a.eval xs)^n := Expr.eval_pow a n xs

lemma polynomial_vector (es : List Expr) : PolynomialTime (vectorRealizer es) := by
  induction es with
  | nil => exact polynomial_constant []
  | cons e es ih => exact polynomial_composition (polynomial_pair e.polynomial ih) polynomial_listCons


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseScalarProgram
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fixed arithmetic circuits for the phase scalar controls -/

namespace ContingencyTables.CountingPhaseScalarProgram
open ScalarScheduleProgram
open MatchingFPRAS.TreeTyped

lemma observationNumerator_value (P W H T N R L : ℕ) :
    observationNumerator.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.observationCoefficient P W := by
  simp [observationNumerator,observable,p,w,h,Expr.eval,
    CountingPhaseSchedule.observationCoefficient,CountingPhaseSchedule.observable]

lemma returnCap_value (P W H T N R L : ℕ) :
    returnCap.eval [P,W,H,T,N,R,L]=CountingPhaseSchedule.returnCap P H T := by
  simp [returnCap,p,h,tau,Expr.eval,CountingPhaseSchedule.returnCap]

lemma precisionBase_value (P W H T N R L : ℕ) :
    precisionBase.eval [P,W,H,T,N,R,L]=
      1024*(H+1)*CountingPhaseSchedule.noiseCoefficient H T N R+1 := by
  simp [precisionBase,h,tau,observations,returns,Expr.eval,CountingPhaseSchedule.noiseCoefficient]

lemma initialPrecision_value (P W H T N R L : ℕ) :
    initialPrecision.eval [P,W,H,T,N,R,L]=CountingPhaseSchedule.initialPrecision H := by
  simp [initialPrecision,h,Expr.eval,CountingPhaseSchedule.initialPrecision]

lemma restartTime_instance {I J : Type} [Fintype I] [Fintype J]
    (A : CompanionFactorialApplication.Instance I J) (H L T N R : ℕ) :
    restartTime.eval [Fintype.card (CompanionFactorialApplication.Labels A),A.W,H,T,N,R,L]=
      CompanionTargetMixing.restartTime A H L := by
  simp [restartTime,observable,p,w,h,capacityBits,Expr.eval,
    CompanionTargetMixing.restartTime,CompanionTrace.time,CompanionTrace.integerConstant]
  ring

end ContingencyTables.CountingPhaseScalarProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPhaseParametersProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable rational controls for the adaptive counting phases -/

namespace ContingencyTables.CountingPhaseParametersProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open CountingOracleScheduleProgram ScalarScheduleProgram

lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition polynomial_first e.polynomial

lemma polynomial_scalarFraction (e : Expr) : PolynomialTime (scalarFractionRealizer e) :=
  polynomial_composition (polynomial_scalar e) polynomial_natural

lemma polynomial_tolerance : PolynomialTime toleranceRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_scalarFraction toleranceDenominator)) TreeFraction.polynomial_div

lemma tolerance_val (P W H T N R L : ℕ) (e : Fraction) :
    TreeFraction.val (tolerance ([P,W,H,T,N,R,L],e))=
      CountingPhaseSchedule.tolerance H (TreeFraction.val e) := by
  rw [tolerance,TreeFraction.div_val,scalarFraction,natural_val]
  simp [scalar,toleranceDenominator,CountingPhaseScalarProgram.h,Expr.eval,
    CountingPhaseSchedule.tolerance]

lemma polynomial_toleranceSquare : PolynomialTime toleranceSquareRealizer :=
  polynomial_composition (polynomial_pair polynomial_tolerance polynomial_tolerance)
    TreeFraction.polynomial_mul

lemma polynomial_observationRatio : PolynomialTime observationRatioRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_scalarFraction CountingPhaseScalarProgram.observationNumerator)
    polynomial_toleranceSquare) TreeFraction.polynomial_div

lemma polynomial_observations : PolynomialTime observationsRealizer :=
  polynomial_composition (polynomial_composition polynomial_observationRatio polynomial_ceiling)
    polynomial_successor

lemma observations_val (P W H T N R L : ℕ) (e : Fraction) :
    observations ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [observations,ceiling_val,observationRatio,TreeFraction.div_val,
    scalarFraction,natural_val,toleranceSquare,TreeFraction.mul_val,tolerance_val]
  change ⌈((CountingPhaseScalarProgram.observationNumerator.eval [P,W,H,T,N,R,L]:ℕ):ℚ)/
    (CountingPhaseSchedule.tolerance H (TreeFraction.val e)*
      CountingPhaseSchedule.tolerance H (TreeFraction.val e))⌉₊+1= _
  rw [CountingPhaseScalarProgram.observationNumerator_value]
  simp only [CountingPhaseSchedule.observations,Nat.cast_mul,Nat.cast_ofNat,
    Nat.cast_add,Nat.cast_one,pow_two]

lemma polynomial_reciprocalTolerance : PolynomialTime reciprocalToleranceRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant (1,1)) polynomial_tolerance)
    TreeFraction.polynomial_div

lemma polynomial_reciprocalCeiling : PolynomialTime reciprocalCeilingRealizer :=
  polynomial_composition polynomial_reciprocalTolerance polynomial_ceiling

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_scalar CountingPhaseScalarProgram.precisionBase)
    polynomial_reciprocalCeiling) polynomial_add

lemma precision_val (P W H T N R L : ℕ) (e : Fraction) :
    precision ([P,W,H,T,N,R,L],e)=
      CountingPhaseSchedule.precision H T N R
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)) := by
  rw [precision,reciprocalCeiling,ceiling_val,reciprocalTolerance,TreeFraction.div_val,tolerance_val]
  simp only [TreeFraction.val,Nat.cast_one,div_one]
  change CountingPhaseScalarProgram.precisionBase.eval [P,W,H,T,N,R,L]+
    ⌈1/CountingPhaseSchedule.tolerance H (TreeFraction.val e)⌉₊= _
  rw [CountingPhaseScalarProgram.precisionBase_value]
  simp only [CountingPhaseSchedule.precision,TreeFraction.val]
  omega

lemma polynomial_noise : PolynomialTime noiseRealizer :=
  polynomial_pair (polynomial_constant 1) polynomial_precision

end ContingencyTables.CountingPhaseParametersProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixLayoutProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma flatten_matrixCode {m n : ℕ} (f : Fin (m*n) → ℕ) :
    (matrixCode (fun i j => f (finProdFinEquiv (i,j)))).flatten=List.ofFn f := by
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  apply congrArg f
  apply Fin.ext
  change j.val+n*i.val=i.val*n+j.val
  ac_rfl

lemma sliceRow_ofFn {m n : ℕ} (f : Fin (m*n) → ℕ) (i : Fin m) :
    sliceRow ((n,List.ofFn f),i.val)=
      List.ofFn (fun j : Fin n => f (finProdFinEquiv (i,j))) := by
  have hbound : n ≤ m*n-i.val*n := by
    have h := Nat.mul_le_mul_right n (Nat.succ_le_of_lt i.isLt)
    apply Nat.le_sub_of_add_le
    simpa only [Nat.succ_mul, Nat.add_comm] using h
  apply List.ext_getElem
  · simp only [sliceRow,List.length_take,List.length_drop,List.length_ofFn,min_eq_left hbound]
  · intro j _ _
    simp only [sliceRow,List.getElem_take,List.getElem_drop,List.getElem_ofFn]
    apply congrArg f
    apply Fin.ext
    change i.val*n+j=j+n*i.val
    ac_rfl

theorem unflattenGrid_code {m n : ℕ} (R : Option (Fin m) → ℕ)
    (P : Option (Fin n) → ℕ) (f : Fin (m*n) → ℕ) :
    unflattenGrid ((marginCode R,marginCode P),List.ofFn f)=
      matrixCode (fun i j => f (finProdFinEquiv (i,j))) := by
  have hrows : layoutRows ((marginCode R,marginCode P),List.ofFn f)=List.range m := by
    simp only [layoutRows,marginCode,List.tail_cons,List.length_ofFn]
  have hcols : (marginCode P).tail.length=n := by
    simp only [marginCode,List.tail_cons,List.length_ofFn]
  unfold unflattenGrid matrixCode
  rw [hrows]
  apply List.ext_getElem
  · simp only [List.length_map,List.length_range,List.length_ofFn]
  · intro i hi _
    have him : i < m := by simpa only [List.length_map,List.length_range] using hi
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn,layoutRow,hcols]
    exact sliceRow_ofFn f ⟨i,him⟩

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting the actual dense transition word in polynomial time -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_ceilLogTwo : PolynomialTime ceilLogTwoRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_predecessor polynomial_bitSize)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphRootProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program computing a component root

The graph is supplied by adjacency lists. The program makes one growth
round per stored vertex, then minimizes the reached indices. No loop
depends on the numeric size of an index or of an edge capacity.
-/

namespace ContingencyTables.FiniteGraphRootProgram

open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength X
  intro rows
  simpa only [Function.comp_apply,eval_X] using list_length_le_weight rows

lemma polynomial_neighborHit : PolynomialTime neighborHitRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_mapWith polynomial_membership) polynomial_any)

lemma polynomial_growTest : PolynomialTime growTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_membership)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_getDFast []))) polynomial_neighborHit)) polynomial_boolOr

lemma polynomial_grow : PolynomialTime growRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_filterWith polynomial_growTest)

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_grow)

lemma fold_first (steps : List (List ℕ)) (s : SearchState) :
    (steps.foldl (fun s row => advance (row,s)) s).1=s.1 := by
  induction steps generalizing s with
  | nil => rfl
  | cons row steps ih => exact ih (advance (row,s))

lemma grow_weight (s : SearchState) : weight (grow s)≤weight (indices s.1) :=
  weight_sublist (List.filter_sublist (p := fun a => growTest (s,a)) (l := indices s.1))

lemma fold_weight (steps : List (List ℕ)) (s : SearchState) :
    weight (steps.foldl (fun s row => advance (row,s)) s).2≤
      max (weight s.2) (weight (indices s.1)) := by
  induction steps generalizing s with
  | nil => exact le_max_left _ _
  | cons row steps ih =>
    have ht := ih (advance (row,s))
    have hs := grow_weight s
    exact ht.trans (max_le (hs.trans (le_max_right _ _)) (le_max_right _ _))

lemma indices_weight (rows : GraphCode) :
    weight (indices rows) ≤ rows.length*(4*rows.length+2)+1 := by
  have h := weight_map_bound (as := List.range rows.length) (f := id)
    (N := 4*rows.length+1) (by
      intro a ha
      exact (weight_nat_numeric a).trans (by
        have := List.mem_range.mp ha
        omega))
  simpa only [List.map_id,List.length_range,indices] using h

lemma polynomial_searchFold : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance (10*(X+1)^2)
  intro steps s pre _post _he
  let S := weight (steps,s)
  let out := pre.foldl (fun s row => advance (row,s)) s
  have hs : weight s≤S := weight_snd (steps,s)
  have hr : weight s.1≤S := (weight_fst s).trans hs
  have hv : weight s.2≤S := (weight_snd s).trans hs
  have hn : s.1.length≤S := (list_length_le_weight s.1).trans hr
  have hi := indices_weight s.1
  have hib : weight (indices s.1)≤4*S^2+2*S+1 := by
    have hm := Nat.mul_le_mul hn (show 4*s.1.length+2≤4*S+2 by omega)
    nlinarith
  have ho : weight out.2 ≤ max (weight s.2) (weight (indices s.1)) := fold_weight pre s
  have hot : weight out.2≤4*S^2+3*S+1 := ho.trans (max_le (by omega) (by omega))
  have hf : out.1=s.1 := fold_first pre s
  have hw : weight out=weight out.1+weight out.2+1 := by
    change weight (out.1,out.2)=_
    rw [weight_prod]
    omega
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤10*(S+1)^2
  rw [hw,hf]
  nlinarith

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair polynomial_first (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant []))
      polynomial_listCons))

lemma polynomial_run : PolynomialTime runRealizer :=
  polynomial_composition polynomial_prepare polynomial_searchFold

theorem polynomial_reached : PolynomialTime reachedRealizer :=
  polynomial_composition polynomial_run polynomial_second

lemma minimum_fold_le (xs : List ℕ) (b : ℕ) :
    xs.foldl (fun b a => min a b) b≤b := by
  induction xs generalizing b with
  | nil => exact le_rfl
  | cons a xs ih => exact (ih (min a b)).trans (min_le_right _ _)

lemma polynomial_minimumFold : PolynomialTime (fold minimum) := by
  apply polynomial_fold polynomial_minimum (4*X+1)
  intro xs b pre _post _he
  have hb : b.size≤weight (xs,b) := (size_le_weight b).trans (weight_snd (xs,b))
  have hs := Nat.size_le_size (minimum_fold_le pre b)
  have hw := weight_nat_le (pre.foldl (fun b a => min a b) b)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  omega

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedPairProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed arithmetic used to prepare the forest evaluator

A pair stores a difference of naturals. Arithmetic never iterates through
the represented integer value, and normalization returns the exact
positive/negative parts expected by the affine penalty program.
-/

namespace ContingencyTables.SignedPairProgram

open MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma polynomial_plus : PolynomialTime plusRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)

lemma polynomial_normalize : PolynomialTime normalizeRealizer :=
  polynomial_pair polynomial_subtract
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_subtract)

lemma polynomial_sum : PolynomialTime sumRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_map polynomial_first) polynomial_listSum)
    (polynomial_composition (polynomial_map polynomial_second) polynomial_listSum)

end ContingencyTables.SignedPairProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteGraphCutProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the selected root-away cut

Deletion filters the stored adjacency rows. The endpoint and cut side
are then computed by the bounded reachability program.
-/

namespace ContingencyTables.FiniteGraphCutProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram

lemma polynomial_reachableCode : PolynomialTime reachableCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_reached) polynomial_second)
    polynomial_membership

end ContingencyTables.FiniteGraphCutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCoefficientProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing signed affine coefficients from the actual forest graph

The tree and cell endpoints are ordinary vertex indices. The program
computes the canonical cut flags, tests the capacity threshold and tree
adjacency, and returns the normalized signed coefficient.
-/

namespace ContingencyTables.RootedCoefficientProgram

open MatchingFPRAS.TreeTyped
open SignedPairProgram FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

lemma polynomial_adjacent : PolynomialTime adjacentRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) polynomial_membership

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

end ContingencyTables.RootedCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestCatalog
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the tree and free-cell catalogs

Both catalogs scan the rectangular cell array. A free cell is selected
by its binary capacity and absence from the supplied forest graph; a
tree cell is selected by graph adjacency. Empty forests need no chosen
edge and are handled by the same program.
-/

namespace ContingencyTables.RootedForestCatalog

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open RootedCoefficientProgram FiniteGraphRootProgram
open scoped Classical

lemma polynomial_edge : PolynomialTime edgeRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
          polynomial_listLength)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_add))

lemma polynomial_treeTest : PolynomialTime treeTestRealizer :=
  polynomial_composition polynomial_edge polynomial_adjacent

lemma polynomial_largeTest : PolynomialTime largeTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_matrixEntry)) polynomial_leNat

lemma polynomial_freeTest : PolynomialTime freeTestRealizer :=
  polynomial_composition (polynomial_pair polynomial_largeTest
    (polynomial_composition polynomial_treeTest polynomial_boolNot)) polynomial_boolAnd

lemma polynomial_selectedTest : PolynomialTime selectedTestRealizer :=
  polynomial_choose (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_treeTest)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_freeTest)

theorem polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first
      polynomial_first) polynomial_second) polynomial_cellPairs))
    (polynomial_filterWith polynomial_selectedTest)

open CompanionFactorialApplication ForestAssignmentSplit GraphCompletionCounts

end ContingencyTables.RootedForestCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPenaltyEvaluateProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the actual forest exponent

The bin width and height are computed from the dimension allowance,
capacity scale and phase coefficient. All forest metadata is generated
from the cell arrays by `RootedForestPrepareProgram`.
-/

namespace ContingencyTables.RootedPenaltyEvaluateProgram

open MatchingFPRAS.TreeTyped
open scoped Classical

lemma polynomial_squareDimension : PolynomialTime squareDimensionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply

lemma polynomial_scaledSquare : PolynomialTime scaledSquareRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first) polynomial_squareDimension)
    polynomial_multiply

lemma polynomial_baseHeight : PolynomialTime baseHeightRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 10) polynomial_scaledSquare)
    polynomial_multiply

lemma polynomial_height : PolynomialTime heightRealizer :=
  polynomial_composition (polynomial_pair polynomial_baseHeight
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_successor)) polynomial_multiply

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinDrawLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed bin program has the analysed independent law

The execution order is the computed free-cell catalog.  The mathematical
law uses another enumeration.  Dependent word equivalences identify their
independent Boolean inputs, while preserving each physical cell's draw.
-/

namespace ContingencyTables.RootedBinDrawLaw

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

attribute [local instance] OAI.ContingencyTables.RootedBinDrawLaw.freeCellDecidableEq
lemma wordBits_eq (A : Instance (Fin m) (Fin n)) (h : ℕ) :
    wordBits A h=binWordBits A h := by
  unfold wordBits binWordBits
  apply Fintype.sum_equiv (RootedCatalogGrid.coordinateEquiv A)
  intro i
  simp only [RootedCatalogGrid.coordinateEquiv,Equiv.trans_apply,
    Equiv.apply_symm_apply]

end
end ContingencyTables.RootedBinDrawLaw

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordLaw
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact finite-word law of the executed selected-root weight oracle -/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma scheduledWordWidth (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (delta failure : ℚ)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) :
    wordWidth (scheduledContext A C K j delta failure z v)=
      estimatorWordBits A C K j delta failure := by
  change j*(sampleCount j delta failure*ratioWidth
    (scheduledContext A C K j delta failure z v))+
    sampleCount j delta failure*(correctionWalkWidth
      (scheduledContext A C K j delta failure z v)+
        RootedEstimatorLayoutProgram.binWidth (scheduledContext A C K j delta failure z v))=_
  simp only [scheduledContext,ratioWidth_data,correctionWalkWidth_data,binWidth_data,
    RootedBinDrawLaw.wordBits_eq,estimatorWordBits,oracleIntegerBits]

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase's physical oracle configuration

Numeric schedules use binary arithmetic. The supplied reserve bounds
the two materialized precision markers; no binary natural controls an
unbounded list allocation.
-/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingOracleScheduleProgram DensePrograms

private lemma polynomial_consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (consR F G) := polynomial_composition (polynomial_pair hF hG) polynomial_listCons

lemma polynomial_fields : PolynomialTime fieldsRealizer := by
  unfold fieldsRealizer
  apply polynomial_consR
  · ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
  apply polynomial_consR
  · ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
  apply polynomial_consR
  · exact polynomial_composition (by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))) RootedPenaltyEvaluateProgram.polynomial_height
  exact polynomial_consR _ _ (polynomial_composition polynomial_first polynomial_second)
    (polynomial_constant [])

attribute [local irreducible] output

attribute [local irreducible] context

attribute [local irreducible] contextWidth

noncomputable section
open CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
variable {m n : ℕ}

lemma fields_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    fields (data A C K j xi z v reserve)=[A.d,K,rationalHeight A C,j] := by
  have hh : 10*(C*(A.d*A.d))*(A.W+1)=10*C*A.d^2*(A.W+1) := by ring
  exact congrArg (fun h => [A.d,K,h,j]) hh

lemma inner_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (inner (data A C K j xi z v reserve))=
      innerTolerance (TreeFraction.val xi/2) j := by
  rw [inner,TreeFraction.div_val,natural_val,scalar,fields_data]
  simp only [relativeDenominator,phase,Expr.eval,List.getD_cons_zero,List.getD_cons_succ,
    Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  unfold innerTolerance
  dsimp only [data]
  field_simp
  ring

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact schedules in the computed weight-oracle configuration -/

namespace ContingencyTables.RootedOracleConfigProgram

open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma scalar_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K)
    (reserve : List Bool) (e : ScalarScheduleProgram.Expr) :
    scalar e (data A C K j xi z v reserve)=e.eval [A.d,K,rationalHeight A C,j] := by
  rw [scalar,fields_data]

lemma timeInput_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    timeInput (data A C K j xi z v reserve)=
      (2*(10000*A.d^2*K)^2,rationalHeight A C+A.d*K+2) := by
  simp only [timeInput,scalar_data,mixing,allowance,dim,grid,height,
    ScalarScheduleProgram.Expr.eval_power,ScalarScheduleProgram.Expr.eval,List.getD_cons_zero,List.getD_cons_succ]

lemma correction_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    TreeFraction.val (correction (data A C K j xi z v reserve))=
      correctionTheta (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [correction,TreeFraction.div_val,inner_data]
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,correctionTheta,Rat.cast_div,Rat.cast_ofNat]

lemma samples_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    samples (data A C K j xi z v reserve)=sampleCount j (innerTolerance (TreeFraction.val xi/2) j) 1 := by
  unfold samples
  rw [CountingOracleScheduleProgram.sampleCount_val,inner_data]
  simp only [data,TreeFraction.val,Nat.cast_one,div_one]

lemma ratioTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    ratioTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [ratioTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,inner_data]

lemma correctionTime_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    correctionTime (data A C K j xi z v reserve)=
      oracleTime A C K 1 (correctionTheta (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [correctionTime,timeInput_data,CountingOracleScheduleProgram.oracleTime_instance,correction_data]

lemma offsetAccuracy_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    offsetAccuracy (data A C K j xi z v reserve)=
      CompanionOracleDensity.offsetAccuracy A (innerTolerance (TreeFraction.val xi/2) j) := by
  rw [offsetAccuracy,CountingOracleScheduleProgram.offsetAccuracy_val,inner_data,scalar_data]
  rfl

lemma context_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    context (data A C K j xi z v reserve)=
      RootedEstimatorMedianProgram.context A C K j (TreeFraction.val xi) z v := by
  unfold context output schedule
  rw [samples_data,ratioTime_data,correctionTime_data,offsetAccuracy_data]
  rfl

lemma rootDegree_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    rootDegree (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [rootDegree,CountingOracleScheduleProgram.ceiling_val,TreeFraction.div_val,inner_data]
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  congr 1
  simp only [TreeFraction.val,Nat.cast_ofNat,Nat.cast_one,div_one,div_div_eq_mul_div]
  ring

lemma depth_data (A : Instance (Fin m) (Fin n)) (C K j : ℕ) (xi : TreeFraction.Fraction)
    (z : View A → ℕ) (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (reserve : List Bool) :
    depth (data A C K j xi z v reserve)=
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (TreeFraction.val xi/2) j)) := by
  rw [depth,rootDegree_data]
  rfl

end
end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingOracleWordBounds
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial word sizes for the executed density oracle -/

namespace ContingencyTables.CountingOracleWordBounds
open CompanionFactorialApplication CompanionOracleDensity GridBoundary
open Polynomial
open scoped BigOperators Classical
noncomputable section
variable {I J : Type} [Fintype I] [Fintype J]

lemma binWordBits_bound (A : Instance I J) (h : ℕ) :
    binWordBits A h ≤ A.d*(CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by
  have hb (i : Fin (dimension A)) :
      Nat.clog 2 (freeRange A (index A i)+1) ≤ CountingTerminalSchedule.capacityBits A+1 := by
    let t := index A i
    have hs : (A.b t.val.1 t.val.2+1).size ≤ CountingTerminalSchedule.capacityBits A := by
      change (A.b t.val.1 t.val.2+1).size ≤ ∑ a : I×J,(A.b a.1 a.2+1).size
      exact Finset.single_le_sum (f := fun a : I×J => (A.b a.1 a.2+1).size)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ (t.val.1,t.val.2))
    have hp := Nat.lt_size_self (A.b t.val.1 t.val.2+1)
    apply Nat.clog_le_of_le_pow
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hs
    change A.b t.val.1 t.val.2+1+1 ≤ 2^(CountingTerminalSchedule.capacityBits A+1)
    rw [pow_succ]
    omega
  unfold binWordBits
  calc
    _ ≤ ∑ _i : Fin (dimension A),
        (CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add_right (hb i) _
    _ = dimension A*(CountingTerminalSchedule.capacityBits A+1+4*(h+A.d)) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (ForestScaledPenalty.free_card_le A)

lemma oracle_time_bound (A : Instance I J) (C K E : ℕ) (theta : ℚ)
    (hE : 1/theta ≤ (E:ℚ)) :
    oracleTime A C K 1 theta ≤
      2*(10000*A.d^2*K)^2*(rationalHeight A C+A.d*K+2+16*E) := by
  unfold oracleTime
  apply Nat.ceil_le.mpr
  have ht : (1:ℝ)/(theta:ℝ) ≤ (E:ℝ) := by exact_mod_cast hE
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add_left (mul_le_mul_of_nonneg_left ht (show (0:ℝ) ≤ 16 by norm_num))
      (height A C+(A.d:ℝ)*K+2))
    (show 0 ≤ mixingConstant A K by unfold mixingConstant; positivity)
  convert hh using 1 <;>
    simp only [mixingConstant,←rationalHeight_cast A C,Nat.cast_mul,Nat.cast_add,
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] <;> ring

lemma samples_bound (j E : ℕ) (delta : ℚ) (hd : 0 < delta)
    (hE : 1/delta ≤ (E:ℚ)) : sampleCount j delta 1 ≤ 65536*(j+1)*E^2 := by
  unfold sampleCount
  apply Nat.ceil_le.mpr
  have he0 : 0 ≤ 1/delta := (one_div_pos.mpr hd).le
  have hs : (1/delta)^2 ≤ (E:ℚ)^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hs (show (0:ℚ) ≤ 65536*(j+1) by positivity)
  convert hh using 1 <;> first | rfl | (push_cast; ring)

lemma offset_bound (A : Instance I J) (E : ℕ) (delta : ℚ)
    (hE : 1/delta ≤ (E:ℚ)) : offsetAccuracy A delta ≤ 4096*A.d*E := by
  unfold offsetAccuracy
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 4096*A.d by positivity)
  convert hh using 1 <;> first | rfl | (push_cast; ring)

lemma oracle_time_uniform (A : Instance I J) (C K M E : ℕ) (theta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hE : 1/theta ≤ ((256*E:ℕ):ℚ)) :
    oracleTime A C K 1 theta ≤ timeBound M E := by
  apply (oracle_time_bound A C K (256*E) theta hE).trans
  unfold timeBound
  apply Nat.mul_le_mul
  · exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left
      (Nat.mul_le_mul (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left hd 2)) hK) 2)
  · have hk := Nat.mul_le_mul hd hK
    omega

lemma estimator_bound (A : Instance I J) (C K j M E : ℕ) (delta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hdelta : 0 < delta) (hE : 1/delta ≤ (E:ℚ)) :
    estimatorWordBits A C K j delta 1 ≤ estimatorBound M E := by
  have hE' : 1/delta ≤ ((256*E:ℕ):ℚ) := hE.trans (by exact_mod_cast (show E ≤ 256*E by omega))
  have ht := oracle_time_uniform A C K M E delta hd hK hH hE'
  have hcorr : 1/(delta/256) ≤ ((256*E:ℕ):ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 256 by norm_num)
    convert hh using 1 <;> first | rfl | (push_cast; field_simp)
  have htc : oracleTime A C K 1 (correctionTheta delta) ≤ timeBound M E := by
    simpa only [correctionTheta,Rat.cast_div,Rat.cast_ofNat] using
      oracle_time_uniform A C K M E (delta/256) hd hK hH hcorr
  have hs : sampleCount j delta 1 ≤ sampleBound M E :=
    (samples_bound j E delta hdelta hE).trans (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_left 65536 (Nat.add_le_add_right hj 1)))
  have ha : offsetAccuracy A delta ≤ 4096*M*E :=
    (offset_bound A E delta hE).trans (Nat.mul_le_mul_right E (Nat.mul_le_mul_left 4096 hd))
  have hb : binWordBits A (offsetAccuracy A delta) ≤ binBound M E := by
    apply (binWordBits_bound A _).trans
    unfold binBound
    exact Nat.mul_le_mul hd (Nat.add_le_add (Nat.add_le_add_right hL 1)
      (Nat.mul_le_mul_left 4 (Nat.add_le_add ha hd)))
  have hw : oracleStepBits A C ≤ 9*M := by
    have hl : Nat.clog 2 (8*A.d) ≤ 8*A.d :=
      Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    unfold oracleStepBits
    omega
  unfold estimatorWordBits estimatorBound oracleIntegerBits
  exact Nat.add_le_add (Nat.mul_le_mul hj (Nat.mul_le_mul hs (Nat.mul_le_mul ht hw)))
    (Nat.mul_le_mul hs (Nat.add_le_add (Nat.mul_le_mul htc hw) hb))

lemma estimatorPolynomial_eval (M : ℕ) :
    estimatorPolynomial.eval M=estimatorBound M (400*(M+1)*M) := by
  simp only [estimatorPolynomial,samplePolynomial,timePolynomial,innerPolynomial,binPolynomial,
    estimatorBound,sampleBound,timeBound,binBound,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]

lemma median_bound_separate (A : Instance I J) (C K j M : ℕ) (xi delta : ℚ)
    (hd : A.d ≤ M) (hK : K ≤ M) (hH : rationalHeight A C ≤ M)
    (hj : j ≤ M) (hL : CountingTerminalSchedule.capacityBits A ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ))
    (hr : CommonBasesFPRAS.repetitionCount delta ≤ 64*(M+1)) :
    medianEstimatorBits A C K j xi delta ≤ medianPolynomial.eval M := by
  have hdelta : 0 < innerTolerance (xi/2) j := by unfold innerTolerance; positivity
  have heq : 1/innerTolerance (xi/2) j=(400:ℚ)*(j+1)*(1/xi) := by
    unfold innerTolerance
    field_simp
    ring
  have he : 1/innerTolerance (xi/2) j ≤ ((400*(M+1)*M:ℕ):ℚ) := by
    rw [heq]
    have hh := mul_le_mul
      (show (400:ℚ)*(j+1) ≤ 400*(M+1) by exact_mod_cast Nat.mul_le_mul_left 400 (Nat.add_le_add_right hj 1))
      hi (one_div_pos.mpr hxi).le (by positivity)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh
  have hb := estimator_bound A C K j M (400*(M+1)*M) (innerTolerance (xi/2) j)
    hd hK hH hj hL hdelta he
  unfold medianEstimatorBits
  rw [medianPolynomial,Polynomial.eval_mul,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,estimatorPolynomial_eval]
  exact Nat.mul_le_mul hr hb

end
end ContingencyTables.CountingOracleWordBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMarkerBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial space for the executed power-approximation markers -/
namespace ContingencyTables.CountingMarkerBounds
open CompanionOracleDensity Polynomial
noncomputable section

lemma inner_inverse_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    1/innerTolerance (xi/2) j ≤ ((400*(M+1)*M:ℕ):ℚ) := by
  have heq : 1/innerTolerance (xi/2) j=(400:ℚ)*(j+1)*(1/xi) := by
    unfold innerTolerance
    field_simp
    ring
  rw [heq]
  have hh := mul_le_mul
    (show (400:ℚ)*(j+1) ≤ 400*(M+1) by exact_mod_cast Nat.mul_le_mul_left 400 (Nat.add_le_add_right hj 1))
    hi (one_div_pos.mpr hxi).le (by positivity)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh

lemma degree_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)) ≤
      512*(400*(M+1)*M) := by
  unfold PowerOfTwoApproximation.rootDegree roundingTolerance
  apply Nat.ceil_le.mpr
  have hh := mul_le_mul_of_nonneg_left (inner_inverse_bound j M xi hj hxi hi)
    (show (0:ℚ) ≤ 512 by norm_num)
  convert hh using 1
  · field_simp
    ring
  · push_cast
    rfl

lemma padding_bound (j M : ℕ) (xi : ℚ) (hj : j ≤ M)
    (hxi : 0 < xi) (hi : 1/xi ≤ (M:ℚ)) :
    PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j))+
      PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)) ≤
        paddingPolynomial.eval M := by
  have hd := degree_bound j M xi hj hxi hi
  have hdepth : PowerOfTwoApproximation.depth (roundingTolerance (innerTolerance (xi/2) j)) ≤
      PowerOfTwoApproximation.rootDegree (roundingTolerance (innerTolerance (xi/2) j)) :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
  simp only [paddingPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  have heq : 409600*(M+1)*M=2*(512*(400*(M+1)*M)) := by ring
  rw [heq]
  omega

end
end ContingencyTables.CountingMarkerBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseWidth
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed common padded width for every adaptive phase

All bounds are fixed arithmetic circuits. No numeric phase count controls
an unbounded preprocessing loop.
-/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram

lemma polynomial_oracleInput : PolynomialTime oracleInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second CountingPhaseParametersProgram.polynomial_noise))
    (polynomial_constant 0)) (polynomial_constant [])

lemma polynomial_rawFields : PolynomialTime rawFieldsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_oracleInput RootedOracleConfigProgram.polynomial_fields)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_append

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition polynomial_second CountingPhaseParametersProgram.polynomial_precision

lemma polynomial_initialPrecision : PolynomialTime initialPrecisionRealizer :=
  polynomial_composition polynomial_second
    (CountingPhaseParametersProgram.polynomial_scalar CountingPhaseScalarProgram.initialPrecision)

lemma polynomial_fields : PolynomialTime fieldsRealizer :=
  polynomial_composition (polynomial_pair polynomial_rawFields
    (polynomial_composition (polynomial_pair polynomial_precision
      (polynomial_composition (polynomial_pair polynomial_initialPrecision (polynomial_constant []))
        polynomial_listCons)) polynomial_listCons)) polynomial_append

lemma polynomial_measure : PolynomialTime measureRealizer :=
  polynomial_composition (polynomial_composition polynomial_fields polynomial_listSum) polynomial_successor

theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_measure (polynomial_constant [])) polynomial_listCons)
    widthExpression.polynomial

theorem width_value (z : Input) :
    width z=CountingWordsBound.wordPolynomial.eval (measure z)+
      CountingMarkerBounds.paddingPolynomial.eval (measure z)+2*measure z+1 := by
  simp only [width,widthExpression,phaseExpression,initialExpression,stageExpression,stepExpression,
    medianExpression,estimatorExpression,sampleExpression,timeExpression,binExpression,innerExpression,x,
    Expr.eval_power,Expr.eval,CountingWordsBound.wordPolynomial,CountingWordsBound.phasePolynomial,
    CountingWordsBound.initialPolynomial,CountingWordsBound.stagePolynomial,CountingWordsBound.stepPolynomial,
    CountingOracleWordBounds.medianPolynomial,CountingOracleWordBounds.estimatorPolynomial,
    CountingOracleWordBounds.samplePolynomial,CountingOracleWordBounds.timePolynomial,
    CountingOracleWordBounds.binPolynomial,CountingOracleWordBounds.innerPolynomial,
    CountingMarkerBounds.paddingPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one,List.getD_cons_zero]

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingScheduleSizes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial numeric bounds for the explicit counting schedules -/

namespace ContingencyTables.CountingPhaseSchedule

/-- A natural reciprocal-accuracy allowance bounds the rational inverse
tolerance; no logarithmic operation is used. -/
lemma inverse_tolerance_le (H E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    1/tolerance H epsilon ≤ (800*(H+1)*E:ℕ) := by
  have heq : 1/tolerance H epsilon=(800:ℚ)*(H+1)*(1/epsilon) := by
    unfold tolerance
    field_simp
  rw [heq]
  have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 800*(H+1) by positivity)
  simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hh

lemma observations_le (p W H E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    observations p W H (tolerance H epsilon) ≤ observationBound p W H E := by
  have heta := tolerance_pos H epsilon he
  have hinv := inverse_tolerance_le H E epsilon he hE
  have hinv0 : (0:ℚ) ≤ 1/tolerance H epsilon := (one_div_pos.mpr heta).le
  have hs : (1/tolerance H epsilon)^2 ≤ ((800*(H+1)*E:ℕ):ℚ)^2 := by
    nlinarith
  have hb : (1024:ℚ)*(H+1)*observationCoefficient p W/(tolerance H epsilon)^2 ≤
      (1024*(H+1)*observationCoefficient p W*(800*(H+1)*E)^2:ℕ) := by
    calc
      _ = ((1024:ℚ)*(H+1)*observationCoefficient p W)*(1/tolerance H epsilon)^2 := by ring
      _ ≤ ((1024:ℚ)*(H+1)*observationCoefficient p W)*((800*(H+1)*E:ℕ):ℚ)^2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by push_cast; ring
  have hc := Nat.ceil_le.mpr hb
  unfold observations observationBound
  omega

end ContingencyTables.CountingPhaseSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScalarScheduleBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numeric bounds for the fixed arithmetic circuits -/

namespace ContingencyTables.ScalarScheduleProgram
open Polynomial
noncomputable section

lemma Expr.eval_le (e : Expr) (xs : List ℕ) (M : ℕ)
    (h : ∀ i,xs.getD i 0 ≤ M) : e.eval xs ≤ e.bound.eval M := by
  induction e with
  | input i => simpa only [Expr.eval,Expr.bound,Polynomial.eval_X] using h i
  | number n => simp only [Expr.eval,Expr.bound,eval_C,le_refl]
  | plus a b ha hb =>
    simp only [Expr.eval,Expr.bound,Polynomial.eval_add]
    exact Nat.add_le_add ha hb
  | times a b ha hb =>
    simp only [Expr.eval,Expr.bound,Polynomial.eval_mul]
    exact Nat.mul_le_mul ha hb

lemma getD_le_of_mem (xs : List ℕ) (M : ℕ) (h : ∀ x∈xs,x ≤ M) :
    ∀ i,xs.getD i 0 ≤ M := by
  induction xs with
  | nil => intro i; simp
  | cons x xs ih =>
    intro i
    cases i with
    | zero => simpa using h x (by simp)
    | succ i =>
      simpa using ih (fun y hy => h y (by simp only [List.mem_cons]; exact Or.inr hy)) i

lemma Expr.eval_le_of_mem (e : Expr) (xs : List ℕ) (M : ℕ) (h : ∀ x∈xs,x ≤ M) :
    e.eval xs ≤ e.bound.eval M := e.eval_le xs M (getD_le_of_mem xs M h)

end
end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingControlBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial bounds for the observation and precision controls -/

namespace ContingencyTables.CountingControlBounds
open ScalarScheduleProgram CountingPhaseSchedule Polynomial
noncomputable section

lemma half_inverse_le (epsilon : ℚ) (M : ℕ) (h : 1/epsilon ≤ (M:ℚ)) :
    1/(epsilon/2) ≤ ((2*M:ℕ):ℚ) := by
  have hh := mul_le_mul_of_nonneg_left h (show (0:ℚ) ≤ 2 by norm_num)
  convert hh using 1 <;> first | rfl | (push_cast; ring)

lemma observations_bound (p W H M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hp : p ≤ M) (hW : W ≤ M) (hH : H ≤ M) (hi : 1/epsilon ≤ (M:ℚ)) :
    observations p W H (tolerance H (epsilon/2)) ≤ observationPolynomial.eval M := by
  have hn := observations_le p W H (2*M) (epsilon/2) (by positivity)
    (half_inverse_le epsilon M hi)
  have hnumer := CountingPhaseScalarProgram.observationNumerator.eval_le_of_mem
    [p,W,H,0,0,0,0] M (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  rw [CountingPhaseScalarProgram.observationNumerator_value] at hnumer
  have ht : 800*(H+1)*(2*M) ≤ 1600*(M+1)*M := by
    calc
      _ = 1600*(H+1)*M := by ring
      _ ≤ _ := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 1600 (Nat.add_le_add_right hH 1))
  refine hn.trans ?_
  simp only [observationBound,observationPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_pow,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  exact Nat.add_le_add_right (Nat.mul_le_mul hnumer (Nat.pow_le_pow_left ht 2)) 2

lemma return_bound (p H T M : ℕ) (hp : p ≤ M) (hH : H ≤ M) (hT : T ≤ M) :
    returnCap p H T ≤ returnPolynomial.eval M := by
  have hb := CountingPhaseScalarProgram.returnCap.eval_le_of_mem [p,0,H,T,0,0,0] M (by
    intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  rwa [CountingPhaseScalarProgram.returnCap_value] at hb

lemma precision_bound (p W H T M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hp : p ≤ M) (hW : W ≤ M) (hH : H ≤ M) (hT : T ≤ M)
    (hi : 1/epsilon ≤ (M:ℚ)) :
    precision H T (observations p W H (tolerance H (epsilon/2))) (returnCap p H T)
      (tolerance H (epsilon/2)) ≤ precisionPolynomial.eval M := by
  let N := observations p W H (tolerance H (epsilon/2))
  let R := returnCap p H T
  have hN : N ≤ observationPolynomial.eval M := observations_bound p W H M epsilon he hp hW hH hi
  have hR : R ≤ returnPolynomial.eval M := return_bound p H T M hp hH hT
  have hB : M ≤ largePolynomial.eval M := by
    simp only [largePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hb := CountingPhaseScalarProgram.precisionBase.eval_le_of_mem [p,W,H,T,N,R,0]
    (largePolynomial.eval M) (by
      intro x hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      have hN' : N ≤ largePolynomial.eval M := by
        simp only [largePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        omega
      have hR' : R ≤ largePolynomial.eval M := by
        simp only [largePolynomial,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
        omega
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  rw [CountingPhaseScalarProgram.precisionBase_value] at hb
  have hc : ⌈1/tolerance H (epsilon/2)⌉₊ ≤ 1600*(M+1)*M := by
    apply (Nat.ceil_le.mpr (inverse_tolerance_le H (2*M) (epsilon/2) (by positivity)
      (half_inverse_le epsilon M hi))).trans
    calc
      800*(H+1)*(2*M)=1600*(H+1)*M := by ring
      _ ≤ _ := Nat.mul_le_mul_right M (Nat.mul_le_mul_left 1600 (Nat.add_le_add_right hH 1))
  simp only [precisionPolynomial,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change 1024*(H+1)*noiseCoefficient H T N R+⌈1/tolerance H (epsilon/2)⌉₊+1 ≤ _
  omega

end
end ContingencyTables.CountingControlBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the actual number of factorial labels

Only retained capacities are summed; the program does not expand any
capacity into a list of labels to obtain the phase controls.
-/

namespace ContingencyTables.CountingLabelCountProgram
open MatchingFPRAS.TreeTyped

lemma polynomial_catalogInput : PolynomialTime catalogInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)

lemma polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition polynomial_catalogInput CompanionCellCatalog.polynomial_capacities

lemma polynomial_count : PolynomialTime countRealizer :=
  polynomial_composition polynomial_capacities polynomial_listSum

open CompanionFactorialApplication
open scoped BigOperators Classical
variable {m n : ℕ}

lemma catalogInput_data (A : Instance (Fin m) (Fin n)) :
    catalogInput (RootedForestCatalog.data A)=CompanionCellCatalog.input A := rfl

lemma count_data (A : Instance (Fin m) (Fin n)) :
    count (RootedForestCatalog.data A)=Fintype.card (Labels A) := by
  rw [count,capacities,catalogInput_data,CompanionCellCatalog.capacities_eq,List.sum_ofFn]
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact Fintype.sum_equiv (CompanionCellCatalog.cellEquiv A) _ _ (fun _ => rfl)

lemma count_bound (A : Instance (Fin m) (Fin n)) :
    Fintype.card (Labels A) ≤ A.d*A.W := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ s : SmallCell A,A.b s.val.1 s.val.2) ≤ ∑ _s : SmallCell A,A.W :=
      Finset.sum_le_sum (fun s _ => (A.hsmall _ _ s.property).le)
    _ = Fintype.card (SmallCell A)*A.W := by simp
    _ ≤ A.d*A.W := Nat.mul_le_mul_right A.W
      ((Fintype.card_subtype_le (fun a : Fin m×Fin n => A.small a.1 a.2=true)).trans
        (by simpa only [Fintype.card_prod] using A.hcard))

end ContingencyTables.CountingLabelCountProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DirectedBFSProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary programs for one stored BFS round -/

namespace ContingencyTables.DirectedBFSProgram

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength X
  intro g
  simpa only [Function.comp_apply,eval_X] using list_length_le_weight g

lemma polynomial_pathSome : PolynomialTime pathSomeRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_constant false) polynomial_identity)
    (polynomial_optionCases (polynomial_constant false) (polynomial_constant true)))

lemma polynomial_lookup : PolynomialTime lookupRealizer := polynomial_getDFast none

lemma polynomial_readEdge : PolynomialTime readEdgeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_getDFast [])) polynomial_second)
    (polynomial_getDFast false)

lemma polynomial_candidate : PolynomialTime candidateRealizer := by
  unfold candidateRealizer
  apply polynomial_composition
  · apply polynomial_pair
    · exact polynomial_composition
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_second) polynomial_second) polynomial_lookup) polynomial_pathSome
    · exact polynomial_composition (polynomial_pair
        (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_first) polynomial_second)
        (polynomial_composition polynomial_first polynomial_second)) polynomial_readEdge
  · exact polynomial_boolAnd

lemma polynomial_headOption : PolynomialTime headOptionRealizer :=
  polynomial_congr _ (polynomial_listCase none
    (polynomial_composition polynomial_first polynomial_some))

lemma polynomial_predecessor : PolynomialTime predecessorRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_indices)) (polynomial_filterWith polynomial_candidate)) polynomial_headOption)

lemma polynomial_appendPath : PolynomialTime appendPathRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_constant [])) polynomial_listCons)) polynomial_append) polynomial_some

lemma polynomial_fromPredecessor : PolynomialTime fromPredecessorRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) polynomial_lookup))
    (polynomial_optionCases (polynomial_constant none) polynomial_appendPath))

lemma polynomial_missing : PolynomialTime missingRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_predecessor)
    (polynomial_optionCases (polynomial_constant none) polynomial_fromPredecessor))

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second) polynomial_lookup))
    (polynomial_optionCases polynomial_missing
      (polynomial_composition polynomial_second polynomial_some)))

theorem polynomial_round : PolynomialTime roundRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_row)

end ContingencyTables.DirectedBFSProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_DirectedBFSBounds
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial size of the materialized BFS path store -/

namespace ContingencyTables.DirectedBFSBounds

open MatchingFPRAS.TreeTyped DirectedBFSCode

lemma none_weight : weight (none : Option (List ℕ))≤5 := by decide

lemma lookup_weight (P : Store) (B : ℕ) (hB : 5≤B) (hP : Bounded P B) (v : ℕ) :
    weight (lookup P v)≤B := by
  by_cases hv : v<P.length
  · have he : lookup P v=P[v] := by simp [lookup,List.getD_eq_getElem?_getD,hv]
    rw [he]
    exact hP _ (List.getElem_mem hv)
  · have he : lookup P v=none := by simp [lookup,List.getD_eq_getElem?_getD,hv]
    rw [he]
    exact none_weight.trans hB

lemma append_weight (xs : List ℕ) (v : ℕ) :
    weight (Option.some (xs++[v]))=weight (Option.some xs)+weight v+1 := by
  change weight (true,xs++[v])=weight (true,xs)+weight v+1
  have h := weight_append xs [v]
  simp only [weight_cons,weight_nil] at h
  simp only [weight_prod]
  omega

lemma row_weight (g : Graph) (P : Store) (B : ℕ) (hB : 5≤B)
    (hP : Bounded P B) (v : ℕ) (hv : v<g.length) :
    weight (roundRow g P v)≤B+4*g.length+2 := by
  have hwv : weight v≤4*g.length+1 := (weight_nat_numeric v).trans (by omega)
  cases hc : lookup P v with
  | some xs =>
    have h := lookup_weight P B hB hP v
    simp only [hc] at h
    simpa only [roundRow,hc] using h.trans (by omega)
  | none =>
    cases hp : predecessor g P v with
    | none =>
      simpa only [roundRow,hc,hp,Option.bind_none] using none_weight.trans (by omega)
    | some u =>
      cases hu : lookup P u with
      | none =>
        simpa only [roundRow,hc,hp,Option.bind_some,hu,Option.map_none] using
          none_weight.trans (by omega)
      | some xs =>
        have h := lookup_weight P B hB hP u
        simp only [hu] at h
        simp only [roundRow,hc,hp,Option.bind_some,hu,Option.map_some,append_weight]
        omega

lemma round_bounded (g : Graph) (P : Store) (B : ℕ) (hB : 5≤B)
    (hP : Bounded P B) : Bounded (round g P) (B+4*g.length+2) := by
  intro o ho
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp ho
  exact row_weight g P B hB hP v (List.mem_range.mp hv)

lemma round_length (g : Graph) (P : Store) : (round g P).length=g.length := by
  simp [DirectedBFSCode.round]

lemma fold_bounded (g : Graph) (P : Store) (B : ℕ) (hB : 5≤B)
    (hP : Bounded P B) (steps : List ℕ) :
    Bounded (steps.foldl (fun P _=>round g P) P) (B+steps.length*(4*g.length+2)) := by
  induction steps generalizing P B with
  | nil => simpa using hP
  | cons a steps ih =>
    have h := ih (round g P) (B+4*g.length+2) (by omega) (round_bounded g P B hB hP)
    have he : B+(a::steps).length*(4*g.length+2)=
        B+4*g.length+2+steps.length*(4*g.length+2) := by
      simp only [List.length_cons]
      ring
    rw [List.foldl_cons,he]
    exact h

lemma fold_length_le (g : Graph) (P : Store) (steps : List ℕ) :
    (steps.foldl (fun P _=>round g P) P).length≤ max P.length g.length := by
  induction steps generalizing P with
  | nil => exact le_max_left _ _
  | cons a steps ih =>
    have h := ih (round g P)
    simp only [List.foldl_cons]
    exact h.trans (by rw [round_length,max_self]; exact le_max_right _ _)

lemma store_weight (P : Store) (B : ℕ) (hP : Bounded P B) :
    weight P≤P.length*(B+1)+1 := by
  have h := weight_map_bound (as:=P) (f:=id) (N:=B) hP
  simpa only [List.map_id] using h

end ContingencyTables.DirectedBFSBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DirectedBFSRuntime
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the entire materialized BFS -/

namespace ContingencyTables.DirectedBFSRuntime

open MatchingFPRAS.TreeTyped Polynomial DirectedBFSCode DirectedBFSBounds DirectedBFSProgram

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_round)

theorem polynomial_fold : PolynomialTime (MatchingFPRAS.TreeTyped.fold advanceRealizer) := by
  apply MatchingFPRAS.TreeTyped.polynomial_fold polynomial_advance (20*(X+1)^3)
  intro steps s pre post he
  let S := weight (steps,s)
  have hsw : weight s≤ S := weight_snd (steps,s)
  have hgw : weight s.1≤ S := (weight_fst s).trans hsw
  have hpw : weight s.2≤ S := (weight_snd s).trans hsw
  have hn : s.1.length≤ S := (list_length_le_weight s.1).trans hgw
  have hpn : s.2.length≤ S := (list_length_le_weight s.2).trans hpw
  have hpre : pre.length≤ S := by
    have hl : pre.length≤ steps.length := by rw [he,List.length_append]; omega
    exact hl.trans ((list_length_le_weight steps).trans (weight_fst (steps,s)))
  have hb : Bounded s.2 (S+5) := by
    intro o ho
    exact (weight_mem ho).trans (hpw.trans (by omega))
  let out := pre.foldl (fun P _=>round s.1 P) s.2
  have ho : Bounded out (S+5+pre.length*(4*s.1.length+2)) :=
    fold_bounded s.1 s.2 (S+5) (by omega) hb pre
  have hol : out.length≤ S := (fold_length_le s.1 s.2 pre).trans
    (max_le hpn hn)
  have hob : S+5+pre.length*(4*s.1.length+2)≤4*S^2+3*S+5 := by
    have hm := Nat.mul_le_mul hpre (show 4*s.1.length+2≤4*S+2 by omega)
    nlinarith
  have hwo := store_weight out _ ho
  have hwm := Nat.mul_le_mul hol (Nat.add_le_add_right hob 1)
  have hwout : weight out≤4*S^3+3*S^2+6*S+1 := by nlinarith
  change weight (pre.foldl (fun s i=>advance (i,s)) s)≤_
  have hf := fold_eq pre s.1 s.2
  rw [Prod.eta] at hf
  rw [hf,weight_prod]
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change 1+weight s.1+weight out≤20*(S+1)^3
  nlinarith

lemma polynomial_initialRow : PolynomialTime initialRowRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_natEqual)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_listCons) polynomial_some)
    (polynomial_constant none))

lemma polynomial_initial : PolynomialTime initialRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_initialRow)

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_indices)
    (polynomial_pair polynomial_first polynomial_initial)

theorem polynomial_run : PolynomialTime runRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_prepare polynomial_fold) polynomial_second)

theorem polynomial_search : PolynomialTime searchRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_run) polynomial_second) polynomial_lookup

end ContingencyTables.DirectedBFSRuntime

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualGraphProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction and search of the actual residual graph -/

namespace ContingencyTables.ResidualGraphProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram SignedPairProgram

lemma polynomial_matrixIndices : PolynomialTime matrixIndicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength Polynomial.X
  intro C
  simpa only [Function.comp_apply,Polynomial.eval_X] using list_length_le_weight C

lemma polynomial_capacityEntry : PolynomialTime capacityEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_first))
    (polynomial_getDFast [])) (polynomial_composition polynomial_second polynomial_second))
    (polynomial_getDFast 0)

lemma polynomial_flowEntry : PolynomialTime flowEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_first))
    (polynomial_getDFast [])) (polynomial_composition polynomial_second polynomial_second))
    (polynomial_getDFast (0,0))

lemma polynomial_arcData : PolynomialTime arcDataRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_capacityEntry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_flowEntry)

lemma polynomial_residualValue : PolynomialTime residualValueRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_second))
    polynomial_add) (polynomial_composition polynomial_second polynomial_first)) polynomial_subtract

lemma polynomial_positive : PolynomialTime positiveRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)) polynomial_less

lemma polynomial_arc : PolynomialTime arcRealizer :=
  polynomial_composition polynomial_arcData polynomial_positive

lemma polynomial_arcRow : PolynomialTime arcRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_matrixIndices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_arc))

lemma polynomial_graph : PolynomialTime graphRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_matrixIndices))
    (polynomial_mapWith polynomial_arcRow)

lemma polynomial_search : PolynomialTime searchRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_graph)
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second))
    DirectedBFSRuntime.polynomial_search

end ContingencyTables.ResidualGraphProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FlowClamp
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary flow magnitudes and a harmless total-domain clamp

Skew symmetry bounds a feasible entry between its two directed
capacities. The executed list program clamps normalized entries to this
interval. This is the identity on every valid flow and bounds every
stored value even on unrelated raw program inputs.
-/

namespace ContingencyTables.FlowClamp

open MatchingFPRAS.TreeTyped SignedPairProgram PublishedEdmondsKarp

theorem polynomial_clamp : PolynomialTime clampRealizer := by
  unfold clampRealizer
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition
        (polynomial_composition polynomial_second polynomial_normalize) polynomial_first))
      polynomial_minimum
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition
        (polynomial_composition polynomial_second polynomial_normalize) polynomial_second))
      polynomial_minimum

theorem clamp_bounds (limits : ℕ×ℕ) (z : Signed) :
    (clamp (limits,z)).1≤limits.1 ∧ (clamp (limits,z)).2≤limits.2 :=
  ⟨min_le_left _ _,min_le_left _ _⟩

end ContingencyTables.FlowClamp

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowPathProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary path bottlenecks and one integral flow-entry update -/

namespace ContingencyTables.FlowPathProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram SignedPairProgram

lemma polynomial_pairAt : PolynomialTime pairAtRealizer :=
  polynomial_pair (polynomial_getDFast 0) (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second
      polynomial_successor)) (polynomial_getDFast 0))

lemma polynomial_arcIndices : PolynomialTime arcIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition polynomial_listLength polynomial_predecessor) Polynomial.X
  intro xs
  have h := list_length_le_weight xs
  simpa only [Function.comp_apply,Polynomial.eval_X] using (Nat.sub_le xs.length 1).trans h

lemma polynomial_arcPairs : PolynomialTime arcPairsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_arcIndices)
    (polynomial_mapWith polynomial_pairAt)

lemma polynomial_minimumScan : PolynomialTime minimumScanRealizer :=
  polynomial_congr _ (polynomial_listCase 0 (polynomial_composition
    (polynomial_pair polynomial_second polynomial_first)
    FiniteGraphRootProgram.polynomial_minimumFold))

lemma polynomial_residuals : PolynomialTime residualsRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_arcPairs))
    (polynomial_mapWith (polynomial_composition polynomial_arcData polynomial_residualValue))

lemma polynomial_bottleneck : PolynomialTime bottleneckRealizer :=
  polynomial_composition polynomial_residuals polynomial_minimumScan

lemma polynomial_pairEqual : PolynomialTime pairEqualRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_natEqual))
    polynomial_boolAnd

lemma polynomial_arcCount : PolynomialTime arcCountRealizer :=
  polynomial_composition (polynomial_filterWith polynomial_pairEqual) polynomial_listLength

end ContingencyTables.FlowPathProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowEntryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary signed augmentation of one matrix entry -/

namespace ContingencyTables.FlowEntryProgram

open MatchingFPRAS.TreeTyped ResidualGraphProgram SignedPairProgram FlowPathProgram

lemma polynomial_rawUpdate : PolynomialTime rawUpdateRealizer := by
  unfold rawUpdateRealizer
  apply polynomial_composition
  · apply polynomial_pair polynomial_first
    apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_first)) polynomial_multiply
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_second)) polynomial_multiply
  · exact polynomial_plus

lemma polynomial_limits : PolynomialTime limitsRealizer := by
  unfold limitsRealizer
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_second) polynomial_capacityEntry
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
        (polynomial_composition polynomial_second polynomial_first))) polynomial_capacityEntry

lemma polynomial_rawInput : PolynomialTime rawInputRealizer := by
  unfold rawInputRealizer
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) polynomial_flowEntry
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_second
    · apply polynomial_pair
      · exact polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
            polynomial_first)) polynomial_arcCount
      · exact polynomial_composition (polynomial_pair
          (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
            (polynomial_composition polynomial_second polynomial_first))
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
            polynomial_first)) polynomial_arcCount

lemma polynomial_updateCell : PolynomialTime updateCellRealizer :=
  polynomial_composition (polynomial_pair polynomial_limits
    (polynomial_composition polynomial_rawInput polynomial_rawUpdate)) FlowClamp.polynomial_clamp

lemma updateCell_bounds (z : EntryInput) :
    (updateCell z).1≤(limits z).1 ∧ (updateCell z).2≤(limits z).2 :=
  FlowClamp.clamp_bounds _ _

end ContingencyTables.FlowEntryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materialized binary residual augmentation

The path and bottleneck are computed once, then every matrix entry is
updated from the preceding matrix. Missing paths leave that matrix
unchanged.
-/

namespace ContingencyTables.FlowMatrixProgram

open MatchingFPRAS.TreeTyped DirectedBFSProgram ResidualGraphProgram FlowPathProgram
  FlowEntryProgram

lemma polynomial_updateRow : PolynomialTime updateRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_matrixIndices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_updateCell))

lemma polynomial_updateMatrix : PolynomialTime updateMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_matrixIndices)) (polynomial_mapWith polynomial_updateRow)

lemma polynomial_prepareAugment : PolynomialTime prepareAugmentRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_arcPairs) polynomial_bottleneck)

lemma polynomial_augment : PolynomialTime augmentRealizer :=
  polynomial_composition polynomial_prepareAugment polynomial_updateMatrix

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_identity ResidualGraphProgram.polynomial_search)
    (polynomial_optionCases (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_augment)))

end ContingencyTables.FlowMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FlowMatrixBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-size bounds for materialized flow updates -/

namespace ContingencyTables.FlowMatrixBounds

open MatchingFPRAS.TreeTyped ResidualGraphProgram FlowEntryProgram FlowMatrixProgram

lemma getD_weight {α : Type} [Codec α] (xs : List α) (d : α)
    (hd : weight d≤ weight xs) (i : ℕ) : weight (xs.getD i d)≤ weight xs := by
  by_cases hi : i< xs.length
  · have he : xs.getD i d=xs[i] := by simp [List.getD_eq_getElem?_getD,hi]
    rw [he]
    exact weight_mem (List.getElem_mem hi)
  · simpa [List.getD_eq_getElem?_getD,hi] using hd

lemma capacityEntry_weight (C : NatMatrix) (u v : ℕ) :
    weight (capacityEntry (C,(u,v)))≤ weight C := by
  have hr : weight (C.getD u [])≤ weight C :=
    getD_weight C [] (by
      rw [weight_nil]
      have hp := weight_pos C
      omega) u
  have he : weight ((C.getD u []).getD v 0)≤ weight (C.getD u []) :=
    getD_weight (C.getD u []) 0 (by
      change 1≤ weight (C.getD u [])
      exact weight_pos _) v
  exact he.trans hr

lemma updateCell_weight (z : EntryInput) :
    weight (updateCell z)≤8*weight z.1.1.1+3 := by
  have hb := updateCell_bounds z
  have h1 := weight_nat_small hb.1
  have h2 := weight_nat_small hb.2
  have hc1 := capacityEntry_weight z.1.1.1 z.2.1 z.2.2
  have hc2 := capacityEntry_weight z.1.1.1 z.2.2 z.2.1
  change weight ((updateCell z).1,(updateCell z).2)≤_
  rw [weight_prod]
  change weight (updateCell z).1≤4*weight (capacityEntry (z.1.1.1,(z.2.1,z.2.2)))+1 at h1
  change weight (updateCell z).2≤
    4*weight (capacityEntry (z.1.1.1,(z.2.2,z.2.1)))+1 at h2
  omega

lemma updateRow_weight (z : FlowEntryProgram.UpdateData×ℕ) :
    weight (updateRow z)≤ z.1.1.1.length*(8*weight z.1.1.1+4)+1 := by
  have h := weight_map_bound (as:=List.range z.1.1.1.length)
    (f:=fun v=>updateCell (z.1,(z.2,v))) (N:=8*weight z.1.1.1+3)
    (fun v _=>updateCell_weight (z.1,(z.2,v)))
  simpa only [updateRow,List.length_range] using h

lemma updateMatrix_weight (z : FlowEntryProgram.UpdateData) :
    weight (updateMatrix z)≤ z.1.1.length*(z.1.1.length*(8*weight z.1.1+4)+2)+1 := by
  have h := weight_map_bound (as:=List.range z.1.1.length)
    (f:=fun u=>updateRow (z,u)) (N:=z.1.1.length*(8*weight z.1.1+4)+1)
    (fun u _=>updateRow_weight (z,u))
  simpa only [updateMatrix,List.length_range] using h

lemma augment_weight (z : Data×List ℕ) : weight (augment z)≤ matrixBound z.1.1 := by
  exact updateMatrix_weight (prepareAugment z)

lemma advance_weight (z : Data×(ℕ×ℕ)) :
    weight (advance z)≤ max (weight z.1.2) (matrixBound z.1.1) := by
  cases hs : ResidualGraphProgram.search z with
  | none => simpa only [advance,hs] using le_max_left (weight z.1.2) (matrixBound z.1.1)
  | some xs =>
    simpa only [advance,hs] using (augment_weight (z.1,xs)).trans
      (le_max_right (weight z.1.2) (matrixBound z.1.1))

lemma matrixBound_le {S : ℕ} (C : NatMatrix) (h : weight C≤ S) :
    matrixBound C≤8*S^3+4*S^2+2*S+1 := by
  have hn : C.length≤ S := (list_length_le_weight C).trans h
  have h1 := Nat.mul_le_mul hn (show 8*weight C+4≤8*S+4 by omega)
  have h2 := Nat.mul_le_mul hn (show C.length*(8*weight C+4)+2≤ S*(8*S+4)+2 by omega)
  unfold matrixBound
  nlinarith

end ContingencyTables.FlowMatrixBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FlowLoopProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded residual-flow loop -/

namespace ContingencyTables.FlowLoopProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram FlowMatrixBounds

lemma polynomial_step : PolynomialTime stepRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_first) (polynomial_composition polynomial_second polynomial_second))
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_second)) FlowMatrixProgram.polynomial_advance)

lemma fold_context (steps : List ℕ) (s : State) :
    (steps.foldl (fun s i=>step (i,s)) s).1=s.1 := by
  induction steps generalizing s with
  | nil => rfl
  | cons i steps ih => exact ih (step (i,s))

lemma fold_weight (steps : List ℕ) (s : State) :
    weight (steps.foldl (fun s i=>step (i,s)) s).2≤
      max (weight s.2) (matrixBound s.1.1) := by
  induction steps generalizing s with
  | nil => exact le_max_left _ _
  | cons i steps ih =>
    have ht := ih (step (i,s))
    have hs := advance_weight ((s.1.1,s.2),s.1.2)
    exact ht.trans (max_le hs (le_max_right _ _))

theorem polynomial_loop : PolynomialTime (MatchingFPRAS.TreeTyped.fold stepRealizer) := by
  apply polynomial_fold polynomial_step (20*(X+1)^3)
  intro steps s pre _post _he
  let S := weight (steps,s)
  let out := pre.foldl (fun s i=>step (i,s)) s
  have hs : weight s≤ S := weight_snd (steps,s)
  have hc : weight s.1≤ S := (weight_fst s).trans hs
  have hC : weight s.1.1≤ S := (weight_fst s.1).trans hc
  have hF : weight s.2≤ S := (weight_snd s).trans hs
  have hb := matrixBound_le s.1.1 hC
  have hfo := fold_weight pre s
  have hout : weight out.2≤8*S^3+4*S^2+3*S+1 :=
    hfo.trans (max_le (by omega) (by omega))
  have hctx : out.1=s.1 := fold_context pre s
  have he : weight out=1+weight out.1+weight out.2 := by
    change weight (out.1,out.2)=_
    exact weight_prod _ _
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)^3
  rw [he,hctx]
  nlinarith

lemma polynomial_zeroMatrix : PolynomialTime zeroMatrixRealizer :=
  polynomial_map (polynomial_map (polynomial_constant (0,0)))

lemma polynomial_cube : PolynomialTime cubeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
      polynomial_multiply) polynomial_identity) polynomial_multiply

lemma polynomial_iterationCount : PolynomialTime iterationCountRealizer :=
  polynomial_composition (polynomial_composition polynomial_listLength polynomial_cube)
    polynomial_successor

lemma polynomial_steps : PolynomialTime stepsRealizer := by
  apply polynomial_boundedRange polynomial_iterationCount (X^3+1)
  intro C
  have h := Nat.pow_le_pow_left (list_length_le_weight C) 3
  simpa only [Function.comp_apply,iterationCount,cube,pow_succ,pow_zero,one_mul,
    eval_add,eval_pow,eval_mul,eval_X,eval_one] using Nat.add_le_add_right h 1

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair
    (polynomial_composition (f := fun z : Context=>z.1) (g := steps)
      polynomial_first polynomial_steps)
    (polynomial_pair polynomial_identity
      (polynomial_composition (f := fun z : Context=>z.1) (g := zeroMatrix)
        polynomial_first polynomial_zeroMatrix))

theorem polynomial_run : PolynomialTime runRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepare polynomial_loop)
    polynomial_second

end ContingencyTables.FlowLoopProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkCapacityProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded-table capacity network in binary -/

namespace ContingencyTables.NetworkCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram

lemma polynomial_kind : PolynomialTime kindRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0))
      polynomial_natEqual) (polynomial_constant 0)
    (polynomial_choose
      (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 1))
        polynomial_natEqual) (polynomial_constant 1)
      (polynomial_choose
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_first)
            polynomial_add)) polynomial_less)
        (polynomial_constant 2) (polynomial_constant 3))))

lemma polynomial_rowCount : PolynomialTime rowCountRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_listLength

lemma polynomial_columnBase : PolynomialTime columnBaseRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_rowCount)
    polynomial_add

lemma polynomial_kinds : PolynomialTime kindsRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_rowCount
    (polynomial_composition polynomial_second polynomial_first)) polynomial_kind)
    (polynomial_composition (polynomial_pair polynomial_rowCount
      (polynomial_composition polynomial_second polynomial_second)) polynomial_kind)

lemma polynomial_pattern (a b : ℕ) : PolynomialTime (patternRealizer a b) :=
  polynomial_composition polynomial_kinds (polynomial_composition
    (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant a))
        polynomial_natEqual)
      (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant b))
        polynomial_natEqual)) polynomial_boolAnd)

lemma polynomial_rowRead : PolynomialTime rowReadRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_second) (polynomial_constant 2))
      polynomial_subtract)) (polynomial_getDFast 0)

lemma polynomial_columnRead : PolynomialTime columnReadRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_first) polynomial_columnBase)
      polynomial_subtract)) (polynomial_getDFast 0)

lemma polynomial_boundRead : PolynomialTime boundReadRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first) (polynomial_constant 2))
        polynomial_subtract)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_second) polynomial_columnBase)
        polynomial_subtract))) polynomial_capacityEntry

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_congr _ (polynomial_choose (polynomial_pattern 0 2) polynomial_rowRead
    (polynomial_choose (polynomial_pattern 2 3) polynomial_boundRead
      (polynomial_choose (polynomial_pattern 3 1) polynomial_columnRead (polynomial_constant 0))))

lemma polynomial_vertexCount : PolynomialTime vertexCountRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_listLength)) polynomial_add)) polynomial_add

lemma polynomial_vertices : PolynomialTime verticesRealizer := by
  apply polynomial_boundedRange polynomial_vertexCount (2+2*X)
  intro z
  have hr := (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))
  have hc := (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))
  simp only [vertexCount,eval_add,eval_ofNat,eval_mul,eval_X]
  omega

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_vertices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_entry))

lemma polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_vertices)
    (polynomial_mapWith polynomial_row)

lemma polynomial_solve : PolynomialTime solveRealizer :=
  polynomial_composition (polynomial_pair polynomial_matrix (polynomial_constant (0,1)))
    FlowLoopProgram.polynomial_run

end ContingencyTables.NetworkCapacityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkFeasibilityProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual polynomial binary bounded-table feasibility test -/

namespace ContingencyTables.NetworkFeasibilityProgram

open MatchingFPRAS.TreeTyped NetworkVertexCode NetworkCapacityProgram ResidualGraphProgram
open scoped BigOperators

lemma polynomial_sourcePair : PolynomialTime sourcePairRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_solve (polynomial_constant 0)) (polynomial_getDFast []))
    SignedPairProgram.polynomial_sum

lemma polynomial_inputValues : PolynomialTime inputValuesRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listSum)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listSum)) polynomial_sourcePair

lemma polynomial_testValues : PolynomialTime testValuesRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_natEqual)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_add))
      polynomial_natEqual)) polynomial_boolAnd

lemma polynomial_test : PolynomialTime testRealizer :=
  polynomial_composition polynomial_inputValues polynomial_testValues

end ContingencyTables.NetworkFeasibilityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BoundedComplementProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing complementary bounded-table margins in binary -/

namespace ContingencyTables.BoundedComplementProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode

lemma polynomial_rowValue : PolynomialTime rowValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast [])) polynomial_listSum)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_second) (polynomial_getDFast 0))) polynomial_subtract

lemma polynomial_columnValues : PolynomialTime columnValuesRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_mapWith (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_getDFast 0)))

lemma polynomial_columnValue : PolynomialTime columnValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_columnValues polynomial_listSum)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) (polynomial_getDFast 0))) polynomial_subtract

lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_columnIndices : PolynomialTime columnIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma polynomial_complement : PolynomialTime complementRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
      (polynomial_mapWith polynomial_rowValue))
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_columnIndices)
      (polynomial_mapWith polynomial_columnValue))) polynomial_second

end ContingencyTables.BoundedComplementProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinarySearchProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for monotone endpoint search

The supplied test is a realized binary predicate. The loop
performs one midpoint test per bit of the upper bound and keeps the
unchanged test data throughout.
-/

namespace ContingencyTables.BinarySearchProgram

open MatchingFPRAS.TreeTyped Polynomial BoundedBinarySearch

lemma polynomial_midpoint : PolynomialTime midpointRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition
        (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
          polynomial_subtract) polynomial_successor) (polynomial_constant 2))
      polynomial_quotient)) polynomial_add

variable {A : Type} [Codec A]
variable (test : A×ℕ→Bool) (T : Realizer test)

lemma polynomial_advance (hT : PolynomialTime T) : PolynomialTime (advanceRealizer test T) := by
  unfold advanceRealizer
  apply polynomial_pair
  · exact polynomial_composition polynomial_second polynomial_first
  · apply polynomial_choose
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_midpoint)) hT
    · exact polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_midpoint)
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_second)
    · exact polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_first)
        (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
            polynomial_midpoint) polynomial_predecessor)

lemma midpoint_le_max (p : Window) : midpoint p≤ max p.1 p.2 := by
  rcases p with ⟨lo,hi⟩
  unfold BoundedBinarySearch.midpoint
  omega

lemma step_le_max (f : ℕ→Bool) (p : Window) :
    (step f p).1≤ max p.1 p.2 ∧ (step f p).2≤ max p.1 p.2 := by
  have h := midpoint_le_max p
  unfold step
  split_ifs <;> dsimp only <;> constructor <;> omega

omit [Codec A] in
lemma fold_context (xs : List ℕ) (s : State A) :
    (xs.foldl (fun s i=>advance test (i,s)) s).1=s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih => exact ih (advance test (i,s))

omit [Codec A] in
lemma fold_bounds (xs : List ℕ) (s : State A) (M : ℕ)
    (h1 : s.2.1≤M) (h2 : s.2.2≤M) :
    (xs.foldl (fun s i=>advance test (i,s)) s).2.1≤M ∧
      (xs.foldl (fun s i=>advance test (i,s)) s).2.2≤M := by
  induction xs generalizing s with
  | nil => exact ⟨h1,h2⟩
  | cons i xs ih =>
    have h := step_le_max (fun t=>test (s.1,t)) s.2
    have hm : max s.2.1 s.2.2≤M := max_le h1 h2
    exact ih (advance test (i,s)) (h.1.trans hm) (h.2.trans hm)

lemma polynomial_loop (hT : PolynomialTime T) :
    PolynomialTime (fold (advanceRealizer test T)) := by
  apply polynomial_fold (polynomial_advance test T hT) (20*(X+1))
  intro xs s pre _post _he
  let S := weight (xs,s)
  let out := pre.foldl (fun s i=>advance test (i,s)) s
  have hs : weight s≤S := weight_snd (xs,s)
  have ha : weight s.1≤S := (weight_fst s).trans hs
  have hp : weight s.2≤S := (weight_snd s).trans hs
  have hM : weight (max s.2.1 s.2.2)≤S := by
    rcases le_total s.2.1 s.2.2 with h | h
    · rw [max_eq_right h]
      exact (weight_snd s.2).trans hp
    · rw [max_eq_left h]
      exact (weight_fst s.2).trans hp
  have hb := fold_bounds test pre s (max s.2.1 s.2.2) (le_max_left _ _) (le_max_right _ _)
  have h1 := weight_nat_small hb.1
  have h2 := weight_nat_small hb.2
  change weight out.2.1≤4*weight (max s.2.1 s.2.2)+1 at h1
  change weight out.2.2≤4*weight (max s.2.1 s.2.2)+1 at h2
  have hc : out.1=s.1 := fold_context test pre s
  have ho : weight out=weight out.1+weight out.2.1+weight out.2.2+2 := by
    change weight (out.1,(out.2.1,out.2.2))=_
    simp only [weight_prod]
    omega
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)
  rw [ho,hc]
  omega

lemma polynomial_steps : PolynomialTime (stepsRealizer (A := A)) := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_bitSize) X
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (size_le_weight z.2).trans (weight_snd z)

lemma polynomial_prepare : PolynomialTime (prepareRealizer (A := A)) :=
  polynomial_pair polynomial_steps
    (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant 0) polynomial_second))

lemma polynomial_execute (hT : PolynomialTime T) : PolynomialTime (executeRealizer test T) :=
  polynomial_composition polynomial_prepare (polynomial_loop test T hT)

lemma polynomial_search (hT : PolynomialTime T) : PolynomialTime (searchRealizer test T) :=
  polynomial_composition (polynomial_execute test T hT)
    (polynomial_composition polynomial_second polynomial_first)

end ContingencyTables.BinarySearchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListSubtractProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary subtraction at one list coordinate

The scan depends on the stored list length. The subtracted amount remains
binary throughout and never controls a loop.
-/

namespace ContingencyTables.ListSubtractProgram

open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_entry : PolynomialTime entryRealizer := by
  unfold entryRealizer
  apply polynomial_composition
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_second) (polynomial_getDFast 0)
    · exact polynomial_congr _ (polynomial_choose
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_second)) polynomial_natEqual)
        (polynomial_composition polynomial_first polynomial_second) (polynomial_constant 0))
  · exact polynomial_subtract

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_subtractAt : PolynomialTime subtractAtRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_entry)

end ContingencyTables.ListSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LowerCapacityProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable subtraction of a lower bound from a capacity matrix -/

namespace ContingencyTables.LowerCapacityProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

lemma polynomial_readRow : PolynomialTime readRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_second) (polynomial_getDFast [])

lemma polynomial_selected : PolynomialTime selectedRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_first)) polynomial_natEqual

lemma polynomial_shiftedInput : PolynomialTime shiftedInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_readRow
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_congr _ (polynomial_choose polynomial_selected
    (polynomial_composition polynomial_shiftedInput ListSubtractProgram.polynomial_subtractAt)
    polynomial_readRow)

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_row)

end ContingencyTables.LowerCapacityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellLowerTestProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed feasibility test with one extra lower cell bound -/

namespace ContingencyTables.CellLowerTestProgram

open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_rowInput : PolynomialTime rowInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
    polynomial_second

lemma polynomial_columnInput : PolynomialTime columnInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_second

lemma polynomial_capacityInput : PolynomialTime capacityInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second

lemma polynomial_shifted : PolynomialTime shiftedRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_rowInput ListSubtractProgram.polynomial_subtractAt)
    (polynomial_composition polynomial_columnInput ListSubtractProgram.polynomial_subtractAt))
    (polynomial_composition polynomial_capacityInput LowerCapacityProgram.polynomial_matrix)

lemma polynomial_guards : PolynomialTime guardsRealizer := by
  unfold guardsRealizer
  apply polynomial_composition
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_rowInput polynomial_first)
          (polynomial_getDFast 0))) polynomial_leNat
    · apply polynomial_composition
      · apply polynomial_pair
        · exact polynomial_composition (polynomial_pair polynomial_second
            (polynomial_composition (polynomial_composition polynomial_columnInput polynomial_first)
              (polynomial_getDFast 0))) polynomial_leNat
        · exact polynomial_composition (polynomial_pair polynomial_second
            (polynomial_composition (polynomial_composition polynomial_capacityInput polynomial_first)
              ResidualGraphProgram.polynomial_capacityEntry)) polynomial_leNat
      · exact polynomial_boolAnd
  · exact polynomial_boolAnd

lemma polynomial_test : PolynomialTime testRealizer :=
  polynomial_composition (polynomial_pair polynomial_guards
    (polynomial_composition polynomial_shifted NetworkFeasibilityProgram.polynomial_test))
    polynomial_boolAnd

end ContingencyTables.CellLowerTestProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellMaximumProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing an attained cell maximum by binary feasibility search

A finite maximum is used only to prove the result of the executed binary
search. The program never enumerates feasible tables.
-/

namespace ContingencyTables.CellMaximumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram
open scoped Classical

lemma polynomial_bound : PolynomialTime boundRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    ResidualGraphProgram.polynomial_capacityEntry

lemma polynomial_maximum : PolynomialTime maximumRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_bound)
    (BinarySearchProgram.polynomial_search test testRealizer polynomial_test)

end ContingencyTables.CellMaximumProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CellMinimumProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing an attained minimum through the complementary table

Complementation changes the lower endpoint query to the
upper endpoint query and preserves every cell capacity.
-/

namespace ContingencyTables.CellMinimumProgram

open MatchingFPRAS.TreeTyped CellLowerTestProgram

lemma polynomial_complemented : PolynomialTime complementedRealizer :=
  polynomial_pair (polynomial_composition polynomial_first
    BoundedComplementProgram.polynomial_complement) polynomial_second

lemma polynomial_minimum : PolynomialTime minimumRealizer :=
  polynomial_composition (polynomial_pair CellMaximumProgram.polynomial_bound
    (polynomial_composition polynomial_complemented CellMaximumProgram.polynomial_maximum))
    polynomial_subtract

end ContingencyTables.CellMinimumProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_EndpointMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every attained cell endpoint

Both scans use the dimensions of the stored margin lists. Each entry is
computed by the binary feasibility search; neither scan enumerates tables.
-/

namespace ContingencyTables.EndpointMatrixProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram

lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_second)

lemma polynomial_lowerEntry : PolynomialTime lowerEntryRealizer :=
  polynomial_composition polynomial_context CellMinimumProgram.polynomial_minimum

lemma polynomial_upperEntry : PolynomialTime upperEntryRealizer :=
  polynomial_composition polynomial_context CellMaximumProgram.polynomial_maximum

lemma polynomial_columns : PolynomialTime columnsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1.2).trans
      ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))

lemma polynomial_lowerRow : PolynomialTime lowerRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_lowerEntry)

lemma polynomial_upperRow : PolynomialTime upperRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_upperEntry)

lemma polynomial_rows : PolynomialTime rowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_lowerMatrix : PolynomialTime lowerMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rows)
    (polynomial_mapWith polynomial_lowerRow)

lemma polynomial_upperMatrix : PolynomialTime upperMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rows)
    (polynomial_mapWith polynomial_upperRow)

end ContingencyTables.EndpointMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NetworkTableProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Extracting the bounded table from the executed flow

The output reads the row-to-column arcs of the computed flow. Both the
matrix dimensions and the encoded entries are obtained from the input;
there is no choice of a mathematical witness in the program.
-/

namespace ContingencyTables.NetworkTableProgram

open MatchingFPRAS.TreeTyped Polynomial NetworkVertexCode ResidualGraphProgram
open scoped BigOperators

lemma polynomial_cell : PolynomialTime cellRealizer := by
  unfold cellRealizer
  apply polynomial_composition
  · apply polynomial_composition
    · exact polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_pair
          (polynomial_composition (polynomial_pair (polynomial_constant 2)
            (polynomial_composition polynomial_second polynomial_first)) polynomial_add)
          (polynomial_composition (polynomial_pair
            (polynomial_composition (polynomial_pair (polynomial_constant 2)
              (polynomial_composition
                (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
                  polynomial_first) polynomial_listLength)) polynomial_add)
            (polynomial_composition polynomial_second polynomial_second)) polynomial_add))
    · exact polynomial_flowEntry
  · exact polynomial_subtract

lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_columnIndices : PolynomialTime columnIndicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_columnIndices))
    (polynomial_mapWith (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_cell))

lemma polynomial_table : PolynomialTime tableRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
    (polynomial_mapWith polynomial_row)

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair polynomial_first NetworkCapacityProgram.polynomial_solve

lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare polynomial_table

end ContingencyTables.NetworkTableProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TightenedInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed endpoint translation and a feasible tightened baseline

The lower and upper matrices are computed by the endpoint scans. Binary
subtraction updates the capacities and both margins, then the same proved
flow program produces a baseline table in the translated instance.
-/

namespace ContingencyTables.TightenedInputProgram

open MatchingFPRAS.TreeTyped Polynomial ResidualGraphProgram NetworkVertexCode
open scoped BigOperators Classical

lemma polynomial_rowValue : PolynomialTime rowValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_first)
      polynomial_second) (polynomial_getDFast 0))
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_second) (polynomial_getDFast [])) polynomial_listSum))
    polynomial_subtract

lemma polynomial_columnValue : PolynomialTime columnValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_second) (polynomial_getDFast 0))
    (polynomial_composition (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      BoundedComplementProgram.polynomial_columnValues) polynomial_listSum)) polynomial_subtract

lemma polynomial_position : PolynomialTime positionRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second

lemma polynomial_cellValue : PolynomialTime cellValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_position) polynomial_capacityEntry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_position) polynomial_capacityEntry)) polynomial_subtract

lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer :=
  polynomial_composition polynomial_first BoundedComplementProgram.polynomial_rowIndices

lemma polynomial_columnIndices : PolynomialTime columnIndicesRealizer :=
  polynomial_composition polynomial_first BoundedComplementProgram.polynomial_columnIndices

lemma polynomial_capacityRow : PolynomialTime capacityRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_columnIndices))
    (polynomial_mapWith polynomial_cellValue)

lemma polynomial_translate : PolynomialTime translateRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
      (polynomial_mapWith polynomial_rowValue))
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_columnIndices)
      (polynomial_mapWith polynomial_columnValue)))
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
      (polynomial_mapWith polynomial_capacityRow))

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_first EndpointMatrixProgram.polynomial_lowerMatrix)
    EndpointMatrixProgram.polynomial_upperMatrix

lemma polynomial_compute : PolynomialTime computeRealizer :=
  polynomial_composition polynomial_prepare polynomial_translate

lemma polynomial_baseline : PolynomialTime baselineRealizer :=
  polynomial_composition polynomial_compute NetworkTableProgram.polynomial_output

end ContingencyTables.TightenedInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_WeightedArgmaxProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary scan selecting a greatest weighted edge

The accumulator is either empty or one stored edge. Its binary size is
bounded by the input list size even when capacities are numerically large.
-/

namespace ContingencyTables.WeightedArgmaxProgram

open MatchingFPRAS.TreeTyped Polynomial

private lemma polynomial_compare : PolynomialTime compareRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)

private lemma polynomial_choose : PolynomialTime chooseRealizer :=
  polynomial_congr _ (MatchingFPRAS.TreeTyped.polynomial_choose
    (polynomial_composition polynomial_compare polynomial_less)
    (polynomial_composition polynomial_first polynomial_some)
    (polynomial_composition polynomial_second polynomial_some))

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_congr _ (polynomial_optionCases polynomial_some polynomial_choose)

private lemma some_weight (e : Edge) :
    weight (Option.some e)=1+weight true+weight e := by
  change weight (true,e)=_
  exact weight_prod _ _

private lemma none_large : 1+weight true≤weight (none : Option Edge) := by decide

lemma advance_weight (e : Edge) (o : Option Edge) :
    weight (advance (e,o))≤weight o+weight e+1 := by
  cases o with
  | none=>
    simp only [advance,some_weight]
    have h := none_large
    omega
  | some a=>
    simp only [advance]
    split <;> simp only [some_weight] <;> omega

lemma fold_weight (xs : List Edge) (o : Option Edge) :
    weight (xs.foldl (fun o e=>advance (e,o)) o)≤weight o+weight xs := by
  induction xs generalizing o with
  | nil=>simp only [List.foldl_nil,weight_nil]; omega
  | cons e xs ih=>
    have h := ih (advance (e,o))
    have hs := advance_weight e o
    simp only [List.foldl_cons,weight_cons]
    omega

lemma polynomial_scan : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance X
  intro xs o pre post he
  have hp := weight_prefix he
  have hf := fold_weight pre o
  simp only [eval_X,weight_prod]
  omega

lemma polynomial_best : PolynomialTime bestRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant none))
    polynomial_scan

end ContingencyTables.WeightedArgmaxProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestEdgeChoiceProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Choosing the heaviest edge between distinct forest components

The filter runs the actual finite component-search program. The maximum
scan receives only eligible stored edges and retains their binary weights.
-/

namespace ContingencyTables.ForestEdgeChoiceProgram

open MatchingFPRAS.TreeTyped WeightedArgmaxProgram FiniteGraphRootProgram
open FiniteGraphCutProgram
open scoped Classical

lemma polynomial_query : PolynomialTime queryRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_first))
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_second)

lemma polynomial_eligible : PolynomialTime eligibleRealizer :=
  polynomial_composition (polynomial_composition polynomial_query polynomial_reachableCode)
    polynomial_boolNot

lemma polynomial_filtered : PolynomialTime filteredRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_filterWith polynomial_eligible)

lemma polynomial_choice : PolynomialTime choiceRealizer :=
  polynomial_composition polynomial_filtered WeightedArgmaxProgram.polynomial_best

end ContingencyTables.ForestEdgeChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestJoinProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical adjacency-list insertion of a forest edge

Every row is rebuilt from the stored vertex range. This keeps the graph
encoding canonical and bounds all intermediate lists by the vertex count.
-/

namespace ContingencyTables.ForestJoinProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram SimpleGraph

lemma polynomial_keep : PolynomialTime keepRealizer := by
  unfold keepRealizer
  have hr : PolynomialTime (composition (first (A:=RowInput) (B:=ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hu : PolynomialTime (composition (composition
      (composition (first (A:=RowInput) (B:=ℕ)) first) second) first) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first
  have hv : PolynomialTime (composition (composition
      (composition (first (A:=RowInput) (B:=ℕ)) first) second) second) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second
  apply polynomial_composition _ polynomial_boolOr
  apply polynomial_pair
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) hr) (polynomial_getDFast [])) polynomial_second) polynomial_membership
  · apply polynomial_composition _ polynomial_boolOr
    apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair hr hu) polynomial_natEqual)
        (polynomial_composition (polynomial_pair polynomial_second hv) polynomial_natEqual))
        polynomial_boolAnd
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair hr hv) polynomial_natEqual)
        (polynomial_composition (polynomial_pair polynomial_second hu) polynomial_natEqual))
        polynomial_boolAnd

lemma polynomial_vertices : PolynomialTime verticesRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_indices

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_vertices)
    (polynomial_filterWith polynomial_keep)

lemma polynomial_join : PolynomialTime joinRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_row)

lemma join_length (z : Input) : (join z).length=z.1.length := by
  simp only [join,List.length_map,indices,List.length_range]

lemma row_weight (z : RowInput) : weight (row z)≤weight (indices z.1.1) :=
  weight_sublist (List.filter_sublist (p:=fun a=>keep (z,a)) (l:=vertices z))

lemma join_weight (z : Input) :
    weight (join z)≤z.1.length*(4*z.1.length^2+2*z.1.length+2)+1 := by
  have hi := indices_weight z.1
  have hs : ∀ i∈indices z.1,weight (row (z,i))≤4*z.1.length^2+2*z.1.length+1 := by
    intro i _
    exact (row_weight (z,i)).trans (by nlinarith [hi])
  have h := weight_map_bound (as:=indices z.1) (f:=fun i=>row (z,i))
    (N:=4*z.1.length^2+2*z.1.length+1) hs
  simpa only [join,indices,List.length_range,Nat.add_assoc] using h

end ContingencyTables.ForestJoinProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeEdgeCatalogProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weighted catalog of large cells

Rows and columns are indexed by their stored margin-list lengths. The
catalog contains each retained large cell once, with its actual binary
capacity and its row/column graph endpoints.
-/

namespace ContingencyTables.LargeEdgeCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms WeightedArgmaxProgram

lemma polynomial_vertexCount : PolynomialTime vertexCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_listLength)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_listLength)) polynomial_add

lemma polynomial_endpoints : PolynomialTime endpointsRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_first) polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_pair polynomial_endpoints CompanionCellCatalog.polynomial_entry

lemma polynomial_large : PolynomialTime largeRealizer :=
  polynomial_composition CompanionCellCatalog.polynomial_retainedTest polynomial_boolNot

lemma polynomial_cells : PolynomialTime cellsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_large)

lemma polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_cells)
    (polynomial_mapWith polynomial_entry)

end ContingencyTables.LargeEdgeCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestGreedyProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the component-greedy forest loop

The immutable weighted edge catalog is scanned after every insertion.
There are at most the square of the stored vertex count many iterations;
all adjacency rows stay inside that fixed vertex range.
-/

namespace ContingencyTables.ForestGreedyProgram

open MatchingFPRAS.TreeTyped Polynomial FiniteGraphRootProgram WeightedArgmaxProgram

private lemma polynomial_insert : PolynomialTime insertRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)) ForestJoinProgram.polynomial_join

lemma polynomial_update : PolynomialTime updateRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity ForestEdgeChoiceProgram.polynomial_choice)
    (polynomial_optionCases polynomial_first polynomial_insert)

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_update)
    (polynomial_composition polynomial_second polynomial_second)

lemma update_length (s : State) : (update s).length=s.1.length := by
  unfold update
  cases h : ForestEdgeChoiceProgram.choice s with
  | none=>rfl
  | some e=>exact ForestJoinProgram.join_length _

lemma update_weight (s : State) :
    weight (update s)≤ max (weight s.1)
      (s.1.length*(4*s.1.length^2+2*s.1.length+2)+1) := by
  unfold update
  cases h : ForestEdgeChoiceProgram.choice s with
  | none=>exact le_max_left _ _
  | some e=>exact (ForestJoinProgram.join_weight _).trans (le_max_right _ _)

lemma fold_edges (xs : List ℕ) (s : State) :
    (xs.foldl (fun s a=>advance (a,s)) s).2=s.2 := by
  induction xs generalizing s with
  | nil=>rfl
  | cons a xs ih=>exact ih (advance (a,s))

lemma fold_weight (xs : List ℕ) (s : State) :
    weight (xs.foldl (fun s a=>advance (a,s)) s).1≤ max (weight s.1)
      (s.1.length*(4*s.1.length^2+2*s.1.length+2)+1) := by
  induction xs generalizing s with
  | nil=>exact le_max_left _ _
  | cons a xs ih=>
    have h := ih (advance (a,s))
    simp only [advance,update_length] at h
    exact h.trans (max_le (update_weight s) (le_max_right _ _))

lemma polynomial_loop : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance (30*(X+1)^3)
  intro xs s pre post he
  let S := weight (xs,s)
  let out := pre.foldl (fun s a=>advance (a,s)) s
  have hs : weight s≤S := weight_snd (xs,s)
  have hg : weight s.1≤S := (weight_fst s).trans hs
  have hec : weight s.2≤S := (weight_snd s).trans hs
  have hn : s.1.length≤S := (list_length_le_weight s.1).trans hg
  have hb : s.1.length*(4*s.1.length^2+2*s.1.length+2)+1≤4*S^3+2*S^2+2*S+1 := by
    have hpow := Nat.pow_le_pow_left hn 2
    have hmul := Nat.mul_le_mul hn (show 4*s.1.length^2+2*s.1.length+2≤4*S^2+2*S+2 by omega)
    nlinarith
  have ho : weight out.1≤4*S^3+2*S^2+3*S+1 :=
    (fold_weight pre s).trans (max_le (by omega) (by omega))
  have heq : out.2=s.2 := fold_edges pre s
  have hw : weight out=1+weight out.1+weight out.2 := by
    change weight (out.1,out.2)=_
    exact weight_prod _ _
  simp only [eval_mul,eval_ofNat,eval_add,eval_pow,eval_X,eval_one]
  change weight out≤30*(S+1)^3
  rw [hw,heq]
  nlinarith

lemma polynomial_slots : PolynomialTime slotsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_first polynomial_listLength)) polynomial_multiply) (X^2)
  intro s
  have h : s.1.length≤weight s := (list_length_le_weight s.1).trans (weight_fst s)
  simpa only [Function.comp_apply,eval_pow,eval_mul,eval_X,pow_two] using Nat.mul_self_le_mul_self h

lemma polynomial_execute : PolynomialTime executeRealizer :=
  polynomial_composition (polynomial_pair polynomial_slots polynomial_identity) polynomial_loop

lemma polynomial_emptyGraph : PolynomialTime emptyGraphRealizer := by
  apply polynomial_composition
  · apply polynomial_boundedRange LargeEdgeCatalogProgram.polynomial_vertexCount (2*X)
    intro z
    have hr : z.1.1.1.length≤weight z := (list_length_le_weight z.1.1.1).trans
      ((weight_fst z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    have hc : z.1.1.2.length≤weight z := (list_length_le_weight z.1.1.2).trans
      ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    simp only [LargeEdgeCatalogProgram.vertexCount,eval_mul,eval_ofNat,eval_X]
    omega
  · exact polynomial_map (polynomial_constant [])

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair polynomial_emptyGraph LargeEdgeCatalogProgram.polynomial_catalog

lemma polynomial_forest : PolynomialTime forestRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepare polynomial_execute) polynomial_first

end ContingencyTables.ForestGreedyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_ComputedCountingParameters
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting schedules computed from the original bounded margins

The capacity-bit sum is formed after the executed endpoint translation.
All remaining dimensions, precisions, cutoffs and phase counts use the
proved rational/natural formulas. No numeric schedule hypothesis is
left to an external caller.
-/

namespace ContingencyTables.ComputedCountingParameters

open CompanionFactorialApplication CompanionOracleDensity RootedPhaseHistory GridBoundary
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma phases_final (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0<epsilon) :
    phases r c b epsilon=CompanionTerminalApplication.finalPhase
      (data hEK r c b hne epsilon he) (capacityBits r c b) ((epsilon/2:ℚ):ℝ) := by
  rw [CountingTerminalSchedule.finalPhase_eq _ _ (epsilon/2) (by positivity)]
  rfl

end
end ContingencyTables.ComputedCountingParameters

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numeric polynomial bounds for the computed terminal coefficient -/

namespace ContingencyTables.CountingCoefficientBounds
open CountingTerminalSchedule
noncomputable section

lemma precision_le (epsilon : ℚ) (E : ℕ) (hE : 1/epsilon ≤ (E:ℚ)) :
    precision epsilon ≤ E := by
  unfold precision
  have hc : ⌈1/epsilon⌉₊ ≤ E := Nat.ceil_le.mpr hE
  exact Nat.clog_le_of_le_pow (hc.trans (Nat.lt_two_pow_self.le))

lemma allowance_le (L d E : ℕ) (epsilon : ℚ) (hE : 1/epsilon ≤ (E:ℚ)) :
    allowance L d epsilon ≤ 20*(L+d+E+1) := by
  have hp := precision_le epsilon E hE
  unfold allowance
  omega

lemma coefficient_le (L d E : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) :
    coefficient L d epsilon ≤ 2048*d*(20*(L+d+E+1))^2*E := by
  apply Nat.ceil_le.mpr
  have ha := allowance_le L d E epsilon hE
  have haQ : (allowance L d epsilon:ℚ) ≤ (20*(L+d+E+1):ℕ) := by exact_mod_cast ha
  have hs : (allowance L d epsilon:ℚ)^2 ≤ ((20*(L+d+E+1):ℕ):ℚ)^2 := by
    have ha0 : (0:ℚ) ≤ allowance L d epsilon := Nat.cast_nonneg _
    nlinarith
  have hm := mul_le_mul hs hE (one_div_pos.mpr he).le (sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_left hm (show (0:ℚ) ≤ 2048*d by positivity)
  convert hmul using 1 <;> first | rfl | (push_cast; ring)

open Polynomial

lemma coefficient_polynomial (L d E M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) (hL : L ≤ M) (hd : d ≤ M) (hEM : E ≤ M) :
    coefficient L d epsilon ≤ coefficientPolynomial.eval M := by
  have hb := coefficient_le L d E epsilon he hE
  have ha : 20*(L+d+E+1) ≤ 20*(3*M+1) := by omega
  have ht : 2048*d*(20*(L+d+E+1))^2*E ≤ 2048*M*(20*(3*M+1))^2*M :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2048 hd)
      (Nat.pow_le_pow_left ha 2)) hEM
  exact hb.trans (by simpa only [coefficientPolynomial,eval_mul,eval_ofNat,eval_X,
    eval_pow,eval_add,eval_one] using ht)

end
end ContingencyTables.CountingCoefficientBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial numeric bounds for the three terminal controls -/

namespace ContingencyTables.CountingTerminalBounds
open Polynomial CountingCoefficientBounds
noncomputable section

lemma coefficient_bound (L d E M : ℕ) (epsilon : ℚ) (he : 0 < epsilon)
    (hE : 1/epsilon ≤ (E:ℚ)) (hL : L ≤ M) (hd : d ≤ M) (hEM : E ≤ M) :
    CountingTerminalSchedule.coefficient L d (epsilon/2) ≤ coefficientPolynomial.eval M := by
  have hhalf : 1/(epsilon/2) ≤ ((2*E:ℕ):ℚ) := by
    have hh := mul_le_mul_of_nonneg_left hE (show (0:ℚ) ≤ 2 by norm_num)
    convert hh using 1 <;> first | rfl | (push_cast; ring)
  have hb := CountingCoefficientBounds.coefficient_polynomial L d (2*E) (2*M)
    (epsilon/2) (by positivity) hhalf (by omega) (by omega) (by omega)
  simpa only [coefficientPolynomial,eval_comp,eval_mul,eval_ofNat,eval_X] using hb

lemma terminal_bounds (C d W H M : ℕ)
    (hC : C ≤ coefficientPolynomial.eval M) (hd : d ≤ M)
    (hW : W=100*d*(16*C*d^2)) (hH : H=10*C*d^2*(W+1)) :
    16*C*d^2 ≤ gridPolynomial.eval M ∧
    W ≤ cutoffPolynomial.eval M ∧ H ≤ phasePolynomial.eval M := by
  have hgrid : 16*C*d^2 ≤ gridPolynomial.eval M := by
    simp only [gridPolynomial,eval_mul,eval_ofNat,eval_pow,eval_X]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 16 hC) (Nat.pow_le_pow_left hd 2)
  have hw : W ≤ cutoffPolynomial.eval M := by
    rw [hW]
    simp only [cutoffPolynomial,eval_mul,eval_ofNat,eval_X]
    exact Nat.mul_le_mul (Nat.mul_le_mul_left 100 hd) hgrid
  refine ⟨hgrid,hw,?_⟩
  rw [hH]
  simp only [phasePolynomial,eval_mul,eval_ofNat,eval_pow,eval_X,eval_add,eval_one]
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left 10 hC) (Nat.pow_le_pow_left hd 2))
    (Nat.add_le_add_right hw 1)

end
end ContingencyTables.CountingTerminalBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicInputBounds
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding counting parameters by the public binary input -/

namespace ContingencyTables.CountingPublicInputBounds
open MatchingFPRAS Algorithms
open scoped BigOperators
noncomputable section

lemma nat_length (x : ℕ) : (encodeNat x).length=x.size+1 := by
  simp only [encodeNat,List.length_append,List.length_map,List.length_singleton,Nat.size_eq_bits_len]

lemma successor_size (x : ℕ) : (x+1).size ≤ x.size+1 := by
  apply Nat.size_le.mpr
  have h := Nat.lt_size_self x
  have hp : 0 < 2^x.size := by positivity
  rw [pow_succ]
  omega

lemma matrix_length {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    (encodeMatrix b).length=∑ a : Fin m×Fin n,((b a.1 a.2).size+1) := by
  simp [encodeMatrix,List.length_flatten,List.map_ofFn,List.sum_ofFn,nat_length,
    Fintype.sum_prod_type,Function.comp_def]

lemma cells_le_matrix_length {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    m*n ≤ (encodeMatrix b).length := by
  rw [matrix_length]
  calc
    m*n = ∑ _a : Fin m×Fin n,1 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun _ _ => by omega)

lemma matrix_le_input {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    (encodeMatrix b).length ≤ (encodeCountingInput r c b epsilon delta).length := by
  simp only [encodeCountingInput,List.length_append]
  omega

lemma dimension_le {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) ≤ size r c b epsilon delta := by
  have hc := (cells_le_matrix_length b).trans (matrix_le_input r c b epsilon delta)
  unfold ComputedCountingParameters.dimensionAllowance size
  omega

lemma capacityBits_le {m n : ℕ} (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) :
    ComputedCountingParameters.capacityBits r c b ≤ size r c b epsilon delta := by
  have hb : ComputedCountingParameters.capacityBits r c b ≤ (encodeMatrix b).length := by
    rw [ComputedCountingParameters.capacityBits,matrix_length]
    apply Finset.sum_le_sum
    intro a _
    have hu := ComputedTableTightening.upper_le_bound hEK r c b hne a.1 a.2
    have hn : ComputedTableTightening.newBounds r c b a.1 a.2 ≤ b a.1 a.2 := by
      exact (Nat.sub_le _ _).trans hu
    exact (Nat.size_le_size (Nat.add_le_add_right hn 1)).trans (successor_size _)
  have hi := hb.trans (matrix_le_input r c b epsilon delta)
  unfold size
  omega

lemma inverse_le {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    1/epsilon ≤ (size r c b epsilon delta:ℚ) := by
  have hc := Nat.le_ceil (epsilon⁻¹)
  have hn : ⌈epsilon⁻¹⌉₊ ≤ size r c b epsilon delta := by unfold size; omega
  have hc' : 1/epsilon ≤ (⌈epsilon⁻¹⌉₊:ℚ) := by simpa only [one_div] using hc
  exact hc'.trans (by exact_mod_cast hn)

lemma repeats_le {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    64*(delta.den.bits.length+1) ≤ 64*size r c b epsilon delta := by
  have hd : delta.den.bits.length+1 ≤ (encodeCountingInput r c b epsilon delta).length := by
    simp only [encodeCountingInput,encodeRat,List.length_append,nat_length,Nat.size_eq_bits_len]
    omega
  exact Nat.mul_le_mul_left 64 (hd.trans (by unfold size; omega))

end
end ContingencyTables.CountingPublicInputBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicTerminalBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public polynomial bounds for the terminal grid and phase controls -/

namespace ContingencyTables.CountingPublicTerminalBounds
open CountingTerminalBounds CountingPublicInputBounds CompanionFactorialApplication
open ScalarScheduleProgram Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma coefficient_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    ComputedCountingParameters.coefficient r c b epsilon ≤
      coefficientPolynomial.eval (size r c b epsilon delta) :=
  coefficient_bound _ _ (size r c b epsilon delta) _ epsilon he (inverse_le r c b epsilon delta)
    (capacityBits_le hEK r c b hne epsilon delta) (dimension_le r c b epsilon delta) (le_refl _)

lemma terminal_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    ComputedCountingParameters.binCount r c b epsilon ≤ gridPolynomial.eval (size r c b epsilon delta) ∧
    ComputedCountingParameters.cutoff r c b epsilon ≤ cutoffPolynomial.eval (size r c b epsilon delta) ∧
    ComputedCountingParameters.phases r c b epsilon ≤ phasePolynomial.eval (size r c b epsilon delta) :=
  terminal_bounds _ _ _ _ _ (coefficient_public hEK r c b hne epsilon delta he)
    (dimension_le r c b epsilon delta) rfl rfl

lemma label_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ≤
      (size r c b epsilon delta)*cutoffPolynomial.eval (size r c b epsilon delta) := by
  have hl := CountingLabelCountProgram.count_bound (ComputedCountingParameters.data hEK r c b hne epsilon he)
  exact hl.trans (Nat.mul_le_mul (dimension_le r c b epsilon delta)
    (terminal_public hEK r c b hne epsilon delta he).2.1)

lemma scalar_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let H := ComputedCountingParameters.phases r c b epsilon
    let L := ComputedCountingParameters.capacityBits r c b
    ∀ x∈[Fintype.card (Labels A),A.W,H,0,0,0,L],
      x ≤ basicPolynomial.eval (size r c b epsilon delta) := by
  dsimp only
  have hp := label_public hEK r c b hne epsilon delta he
  have hw := (terminal_public hEK r c b hne epsilon delta he).2.1
  have hh := (terminal_public hEK r c b hne epsilon delta he).2.2
  have hl := capacityBits_le hEK r c b hne epsilon delta
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [basicPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
  change x=Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) ∨
    x=ComputedCountingParameters.cutoff r c b epsilon ∨
    x=ComputedCountingParameters.phases r c b epsilon ∨ x=0 ∨ x=0 ∨ x=0 ∨
    x=ComputedCountingParameters.capacityBits r c b at hx
  omega

lemma restart_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    CompanionTargetMixing.restartTime A (ComputedCountingParameters.phases r c b epsilon)
      (ComputedCountingParameters.capacityBits r c b) ≤ restartPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hb := CountingPhaseScalarProgram.restartTime.eval_le_of_mem
    [Fintype.card (Labels A),A.W,H,0,0,0,L]
    (basicPolynomial.eval (size r c b epsilon delta))
    (scalar_public hEK r c b hne epsilon delta he)
  rw [CountingPhaseScalarProgram.restartTime_instance A H L 0 0 0] at hb
  simpa only [restartPolynomial,Polynomial.eval_comp] using hb

end
end ContingencyTables.CountingPublicTerminalBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPublicControls
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All dynamic scalar controls are polynomial in the public input -/

namespace ContingencyTables.CountingPublicControls
open CountingPublicInputBounds CountingPublicTerminalBounds CountingControlBounds
open CompanionFactorialApplication Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma scalar_bound (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let H := ComputedCountingParameters.phases r c b epsilon
    let L := ComputedCountingParameters.capacityBits r c b
    ∀ x∈[Fintype.card (Labels A),A.W,H,CompanionTargetMixing.restartTime A H L,L],
      x ≤ inputPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hs : ∀ x∈[Fintype.card (Labels A),A.W,H,0,0,0,L],
      x ≤ basicPolynomial.eval (size r c b epsilon delta) :=
    scalar_public hEK r c b hne epsilon delta he
  have ht := restart_public hEK r c b hne epsilon delta he
  have hp := hs (Fintype.card (Labels A)) (by simp only [List.mem_cons, eq_self, true_or])
  have hw := hs A.W (by simp only [List.mem_cons, eq_self, true_or, or_true])
  have hh := hs H (by simp only [List.mem_cons, eq_self, true_or, or_true])
  have hl := hs L (by simp only [List.mem_cons, eq_self, true_or, or_true])
  change ∀ x∈[Fintype.card (Labels A),A.W,H,CompanionTargetMixing.restartTime A H L,L],
    x ≤ inputPolynomial.eval (size r c b epsilon delta)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  simp only [inputPolynomial,Polynomial.eval_add,Polynomial.eval_X]
  change CompanionTargetMixing.restartTime A H L ≤ _ at ht
  omega

lemma settings_bounds (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    s.N ≤ observationPolynomial.eval (size r c b epsilon delta) ∧
    s.n ≤ returnPolynomial.eval (size r c b epsilon delta) ∧
    s.k ≤ precisionPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  let T := CompanionTargetMixing.restartTime A H L
  let M := inputPolynomial.eval (size r c b epsilon delta)
  have hs : ∀ x∈[Fintype.card (Labels A),A.W,H,T,L],x ≤ M :=
    scalar_bound hEK r c b hne epsilon delta he
  have hp : Fintype.card (Labels A) ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or])
  have hw : A.W ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])
  have hh : H ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])
  have ht : T ≤ M := hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])
  have hSM : size r c b epsilon delta ≤ M := by
    dsimp only [M]
    simp only [inputPolynomial,Polynomial.eval_add,Polynomial.eval_X]
    omega
  have hi : 1/epsilon ≤ (M:ℚ) := (inverse_le r c b epsilon delta).trans (by exact_mod_cast hSM)
  refine ⟨?_,?_,?_⟩
  · change CountingPhaseSchedule.observations (Fintype.card (Labels A)) A.W H
        (CountingPhaseSchedule.tolerance H (epsilon/2)) ≤ _
    simpa only [observationPolynomial,Polynomial.eval_comp,M] using
      observations_bound _ _ _ M epsilon he hp hw hh hi
  · change CountingPhaseSchedule.returnCap (Fintype.card (Labels A)) H T ≤ _
    simpa only [returnPolynomial,Polynomial.eval_comp,M] using return_bound _ _ _ M hp hh ht
  · change CountingPhaseSchedule.precision H T
        (CountingPhaseSchedule.observations (Fintype.card (Labels A)) A.W H
          (CountingPhaseSchedule.tolerance H (epsilon/2)))
        (CountingPhaseSchedule.returnCap (Fintype.card (Labels A)) H T)
        (CountingPhaseSchedule.tolerance H (epsilon/2)) ≤ _
    simpa only [precisionPolynomial,Polynomial.eval_comp,M] using
      precision_bound _ _ _ _ M epsilon he hp hw hh ht hi

end
end ContingencyTables.CountingPublicControls

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionUniformPhaseBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed common width covers every actual phase and marker -/
namespace ContingencyTables.CompanionUniformPhaseWidth
open MatchingFPRAS CompanionFactorialApplication CompanionOracleDensity
open RootedPhaseHistory GridBoundary
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ}

lemma fields_data (A : Instance (Fin m) (Fin n)) (s : Settings A)
    (epsilon : TreeFraction.Fraction) (z : View A→ℕ)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) s.K)
    (hk : CountingPhaseParametersProgram.precision
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon)=s.k)
    (hh : s.h=CountingPhaseSchedule.initialPrecision s.H) :
    fields (data A s epsilon z v)=
      [A.d,s.K,rationalHeight A s.C,0,Fintype.card (Labels A),A.W,s.H,
        CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L,s.k,s.h] := by
  have ho : oracleInput (data A s epsilon z v)=RootedOracleConfigProgram.data A s.C s.K 0
      (CountingPhaseParametersProgram.noise
        ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon))
      z v [] := rfl
  unfold fields rawFields
  rw [ho,RootedOracleConfigProgram.fields_data]
  change [A.d,s.K,rationalHeight A s.C,0]++
    [Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L]++
      [CountingPhaseParametersProgram.precision
        ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L],epsilon),
        CountingPhaseScalarProgram.initialPrecision.eval
          [Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,s.N,s.n,s.L]]=_
  rw [hk,CountingPhaseScalarProgram.initialPrecision_value,←hh]
  rfl

end
end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingCoefficientProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The terminal coefficient computed with binary natural arithmetic -/

namespace ContingencyTables.CountingCoefficientProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial
open OffsetCountPrograms DensePrograms

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      polynomial_ceilQuotient) polynomial_ceilLogTwo

lemma polynomial_allowance : PolynomialTime allowanceRealizer := by
  unfold allowanceRealizer
  exact polynomial_composition (polynomial_pair (polynomial_constant 20)
    (polynomial_composition (polynomial_composition
      (polynomial_pair (polynomial_composition polynomial_first TreeTyped.polynomial_add)
        (polynomial_composition polynomial_second polynomial_precision)) TreeTyped.polynomial_add)
      polynomial_successor)) polynomial_multiply

lemma polynomial_numerator : PolynomialTime numeratorRealizer := by
  unfold numeratorRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2048)
        (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)
      (polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_allowance polynomial_allowance) polynomial_multiply)))
      polynomial_multiply)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply

lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator
    (polynomial_composition polynomial_second polynomial_first)) polynomial_ceilQuotient

lemma precision_val (e : Fraction) (hn : 0 < e.1) :
    precision e=CountingTerminalSchedule.precision (val e) := by
  unfold precision CountingTerminalSchedule.precision
  rw [ceilQuotient_eq e.2 e.1 hn]
  congr 2
  simp only [val,one_div,inv_div]

lemma allowance_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) :
    allowance ((L,d),e)=CountingTerminalSchedule.allowance L d (val e) := by
  simp only [allowance,CountingTerminalSchedule.allowance,precision_val e hn]

lemma coefficient_val (L d : ℕ) (e : Fraction) (hn : 0 < e.1) (hd : 0 < e.2) :
    coefficient ((L,d),e)=CountingTerminalSchedule.coefficient L d (val e) := by
  unfold coefficient
  rw [ceilQuotient_eq _ _ hn]
  unfold CountingTerminalSchedule.coefficient
  rw [←allowance_val L d e hn]
  congr 1
  simp only [numerator,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,val]
  field_simp

end ContingencyTables.CountingCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBaseProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the capacity-bit and dimension inputs to the counting schedule -/

namespace ContingencyTables.CountingBaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
open NetworkVertexCode

lemma polynomial_cellBits : PolynomialTime cellBitsRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_successor polynomial_toBits) polynomial_listLength)

lemma polynomial_capacityBits : PolynomialTime capacityBitsRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition TightenedInputProgram.polynomial_compute polynomial_second)
      polynomial_flatten)
    (polynomial_composition (polynomial_map polynomial_cellBits) polynomial_listSum)

lemma polynomial_dimension : PolynomialTime dimensionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 1)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_listLength))
      polynomial_multiply)) polynomial_add

lemma polynomial_half : PolynomialTime halfRealizer :=
  polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_second) polynomial_multiply)

lemma half_val (e : TreeFraction.Fraction) : TreeFraction.val (half e)=TreeFraction.val e/2 := by
  simp only [half,TreeFraction.val,Nat.cast_mul,Nat.cast_ofNat]
  ring

lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_capacityBits)
    (polynomial_composition polynomial_first polynomial_dimension))
    (polynomial_composition polynomial_second polynomial_half)

lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_composition polynomial_frame CountingCoefficientProgram.polynomial_coefficient

lemma capacityBits_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    capacityBits (data r c b)=ComputedCountingParameters.capacityBits r c b := by
  unfold capacityBits
  rw [TightenedInputProgram.compute_code]
  simp only [data,ResidualGraphProgram.natCode,List.map_flatten,List.map_ofFn,Function.comp_def,
    List.sum_flatten,List.sum_ofFn,cellBits,ComputedCountingParameters.capacityBits,
    Fintype.sum_prod_type]

lemma dimension_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) :
    dimension (data r c b)=ComputedCountingParameters.dimensionAllowance (m:=m) (n:=n) := by
  simp only [dimension,data,List.length_ofFn,ComputedCountingParameters.dimensionAllowance]

lemma coefficient_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    coefficient (data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.coefficient r c b epsilon := by
  unfold coefficient frame
  rw [capacityBits_data,dimension_data]
  have hn : 0 < (half (TreeFraction.repr epsilon)).1 := by
    change 0 < epsilon.num.natAbs
    exact Int.natAbs_pos.mpr (ne_of_gt (Rat.num_pos.mpr he))
  have hd : 0 < (half (TreeFraction.repr epsilon)).2 := by
    change 0 < 2*epsilon.den
    exact Nat.mul_pos (by decide) epsilon.pos
  rw [CountingCoefficientProgram.coefficient_val _ _ _ hn hd,half_val,
    TreeFraction.val_repr he.le]
  rfl

end ContingencyTables.CountingBaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingTerminalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed terminal grid width, cutoff and phase count -/

namespace ContingencyTables.CountingTerminalProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_base : PolynomialTime baseRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair CountingBaseProgram.polynomial_coefficient
      (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)) polynomial_multiply)
    (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)) polynomial_multiply

lemma polynomial_binCount : PolynomialTime binCountRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 16) polynomial_base) polynomial_multiply

lemma polynomial_cutoff : PolynomialTime cutoffRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 100)
      (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)) polynomial_multiply)
    polynomial_binCount) polynomial_multiply

lemma polynomial_phases : PolynomialTime phasesRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 10) polynomial_base) polynomial_multiply)
    (polynomial_composition polynomial_cutoff polynomial_successor)) polynomial_multiply

lemma binCount_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    binCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.binCount r c b epsilon := by
  unfold binCount base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data]
  unfold ComputedCountingParameters.binCount
  ring

lemma cutoff_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    cutoff (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.cutoff r c b epsilon := by
  unfold cutoff
  rw [CountingBaseProgram.dimension_data,binCount_data r c b epsilon he]
  rfl

lemma phases_data {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon : ℚ) (he : 0 < epsilon) :
    phases (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ComputedCountingParameters.phases r c b epsilon := by
  unfold phases base
  rw [CountingBaseProgram.coefficient_data r c b epsilon he,
    CountingBaseProgram.dimension_data,cutoff_data r c b epsilon he]
  unfold ComputedCountingParameters.phases
  ring

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedForestCode
attribute [-instance] _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed forest retains its literal adjacency-list code -/

namespace ContingencyTables.ComputedLargeForest
open SimpleGraph MaximumForest ForestCapacity ForestGreedySemantics
open FiniteGraphRootProgram LargeEdgeCatalogProgram
open scoped Classical

variable {m n : ℕ}

private lemma code_congr {N : ℕ} (G H : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G=H) : graphCode G=graphCode H := by
  subst H
  apply congrArg (@graphCode N G)
  exact Subsingleton.elim _ _

lemma computed_code (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (W : ℕ) (hW : 1 ≤ W) :
    graphCode ((computed r c b W).comap finSumFinEquiv.symm)=
      ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W) := by
  obtain ⟨F,hF,_⟩ := iterate_optimal (graph b W) ⊥ (capacities b)
    (catalog (NetworkVertexCode.data r c b,W)) (catalog_correct r c b W)
    (capacity_positive b W hW) (MaximumForestExchange.bottom_extendible _ _)
    ((m+n)*(m+n)) (by
      have hb := unordered_pair_budget (n:=m+n)
      omega)
  have hzero (d : DecidableRel (⊥ : SimpleGraph (Fin (m+n))).Adj) :
      @graphCode (m+n) ⊥ d=ForestGreedyProgram.emptyGraph (NetworkVertexCode.data r c b,W) := by
    symm
    simp only [ForestGreedyProgram.emptyGraph,vertexCount_code,DirectedBFSCode.range_eq_map,
      ←List.ofFn_eq_map,List.map_ofFn,graphCode]
    apply congrArg List.ofFn
    funext v
    simp [adjacencyRow]
  have hout : ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)=graphCode F := by
    unfold ForestGreedyProgram.forest ForestGreedyProgram.prepare
    rw [←hzero (fun a b => Classical.propDecidable _),execute_iterate,graphCode_length]
    exact congrArg Prod.fst hF
  have hc : (computed r c b W).comap finSumFinEquiv.symm=
      decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W)) := by
    ext u v
    change (decoded (ForestGreedyProgram.forest (NetworkVertexCode.data r c b,W))).Adj
      (vertexEquiv (finSumFinEquiv.symm u)) (vertexEquiv (finSumFinEquiv.symm v)) ↔ _
    simp only [vertexEquiv,Equiv.apply_symm_apply]
  have he : (computed r c b W).comap finSumFinEquiv.symm=F := by
    simpa only [hout,decoded_graphCode] using hc
  exact (code_congr _ _ he).trans hout.symm

end ContingencyTables.ComputedLargeForest

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rooted-oracle metadata from the executed original-input preprocessing -/

namespace ContingencyTables.ComputedRootedInput
open MatchingFPRAS MatchingFPRAS.TreeTyped
open DensePrograms NetworkVertexCode

lemma polynomial_forestFrame : PolynomialTime forestFrameRealizer :=
  polynomial_pair (polynomial_composition polynomial_first TightenedInputProgram.polynomial_compute)
    polynomial_second

lemma polynomial_catalogData : PolynomialTime catalogDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_forestFrame ForestGreedyProgram.polynomial_forest) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first TightenedInputProgram.polynomial_compute)
      polynomial_first))
    (polynomial_composition (polynomial_composition polynomial_first TightenedInputProgram.polynomial_compute)
      polynomial_second)

open scoped Classical
variable {m n : ℕ}

lemma catalogData_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    catalogData (data r c b,W)=RootedForestCatalog.data
      (ComputedCompanionInstance.instanceData hEK r c b hne W hW) := by
  unfold catalogData forestFrame
  rw [TightenedInputProgram.compute_code]
  unfold RootedForestCatalog.data ComputedCompanionInstance.instanceData
  rw [ComputedLargeForest.computed_code _ _ _ W (by omega)]
  simp only [data,Int.toNat_natCast,ResidualGraphProgram.natCode,matrixCode]

lemma baseline_instance (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (W : ℕ) (hW : 2 ≤ W) :
    TightenedInputProgram.baseline (data r c b)=matrixCode
      (fun i j => ((ComputedCompanionInstance.instanceData hEK r c b hne W hW).X i j).toNat) := by
  obtain ⟨Y,hY,_,_⟩ := TightenedInputProgram.baseline_correct hEK r c b hne
  rw [hY]
  unfold matrixCode
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  simp only [ComputedCompanionInstance.instanceData,ComputedCompanionInstance.baseline,
    hY,ResidualGraphProgram.natCode,List.getD_eq_getElem?_getD,List.getElem?_ofFn,
    i.isLt,j.isLt,dite_true,Option.getD_some,Fin.eta,Int.toNat_natCast]

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every scalar control from the original bounded table -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CountingPhaseScalarProgram

lemma polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_first CountingTerminalProgram.polynomial_cutoff)
    ComputedRootedInput.polynomial_catalogData

lemma polynomial_labelCount : PolynomialTime labelCountRealizer :=
  polynomial_composition polynomial_catalog CountingLabelCountProgram.polynomial_count

private lemma poly_consR {f : Input → ℕ} {g : Input → List ℕ}
    (F : Realizer f) (G : Realizer g) (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (consR F G) := polynomial_composition (polynomial_pair hF hG) polynomial_listCons

lemma polynomial_preliminary : PolynomialTime preliminaryRealizer := by
  unfold preliminaryRealizer
  apply poly_consR _ _ polynomial_labelCount
  apply poly_consR _ _ CountingTerminalProgram.polynomial_cutoff
  apply poly_consR _ _ CountingTerminalProgram.polynomial_phases
  apply poly_consR _ _ (polynomial_constant 0)
  apply poly_consR _ _ (polynomial_constant 0)
  apply poly_consR _ _ (polynomial_constant 0)
  exact poly_consR _ _ (polynomial_composition polynomial_first CountingBaseProgram.polynomial_capacityBits)
    (polynomial_constant [])

lemma polynomial_basic : PolynomialTime basicRealizer :=
  polynomial_pair (polynomial_composition polynomial_preliminary (polynomial_vector controlExpressions))
    (polynomial_composition polynomial_second CountingBaseProgram.polynomial_half)

lemma polynomial_fillObservations : PolynomialTime fillObservationsRealizer := by
  unfold fillObservationsRealizer
  exact polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant 4)) polynomial_takeFast)
    (polynomial_composition (polynomial_pair CountingPhaseParametersProgram.polynomial_observations
      (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant 5)) polynomial_dropFast))
        polynomial_listCons)) polynomial_append) polynomial_second

lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_composition polynomial_basic polynomial_fillObservations

open CompanionFactorialApplication
open scoped Classical
variable {m n : ℕ}

lemma catalog_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedForestCatalog.data (ComputedCountingParameters.data hEK r c b hne epsilon he) := by
  unfold catalog
  rw [CountingTerminalProgram.cutoff_data r c b epsilon he]
  exact ComputedRootedInput.catalogData_instance hEK r c b hne _ _

lemma labelCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    labelCount (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      Fintype.card (Labels (ComputedCountingParameters.data hEK r c b hne epsilon he)) := by
  rw [labelCount,catalog_data hEK r c b hne epsilon he,CountingLabelCountProgram.count_data]

lemma basic_values (P W H L : ℕ) :
    vector controlExpressions [P,W,H,0,0,0,L]=
      [P,W,H,4*CountingPhaseSchedule.observable P W*(H+P+L+5),0,
        CountingPhaseSchedule.returnCap P H (4*CountingPhaseSchedule.observable P W*(H+P+L+5)),L] := by
  simp [vector,controlExpressions,CountingPhaseScalarProgram.p,CountingPhaseScalarProgram.w,
    CountingPhaseScalarProgram.h,capacityBits,restartTime,observable,fullReturnCap,Expr.eval,
    CountingPhaseSchedule.observable,CountingPhaseSchedule.returnCap]

lemma fillObservations_values (P W H T N R L : ℕ) (e : CountingOracleScheduleProgram.Fraction) :
    fillObservations ([P,W,H,T,N,R,L],e)=
      ([P,W,H,T,CountingPhaseSchedule.observations P W H
        (CountingPhaseSchedule.tolerance H (TreeFraction.val e)),R,L],e) := by
  simp [fillObservations,CountingPhaseParametersProgram.observations_val]

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingSettingsCorrect
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed controls are the proven counting schedule -/

namespace ContingencyTables.CountingComputedSettings
open MatchingFPRAS CompanionFactorialApplication
open CountingPhaseParametersProgram
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma parameters_values (z : Input) (P W H L : ℕ)
    (hz : preliminary z=[P,W,H,0,0,0,L]) :
    parameters z=
      (let T := 4*CountingPhaseSchedule.observable P W*(H+P+L+5)
       let eta := CountingPhaseSchedule.tolerance H (TreeFraction.val z.2/2)
       ([P,W,H,T,CountingPhaseSchedule.observations P W H eta,
         CountingPhaseSchedule.returnCap P H T,L],CountingBaseProgram.half z.2)) := by
  unfold parameters basic
  rw [hz,basic_values,fillObservations_values,CountingBaseProgram.half_val]

lemma parameters_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ([Fintype.card (Labels A),A.W,s.H,CompanionTargetMixing.restartTime A s.H s.L,
        s.N,s.n,s.L],CountingBaseProgram.half (TreeFraction.repr epsilon)) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let H := ComputedCountingParameters.phases r c b epsilon
  let L := ComputedCountingParameters.capacityBits r c b
  have hp : preliminary (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      [Fintype.card (Labels A),A.W,H,0,0,0,L] := by
    unfold preliminary
    rw [labelCount_data hEK r c b hne epsilon he,
      CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingTerminalProgram.phases_data r c b epsilon he,CountingBaseProgram.capacityBits_data]
    rfl
  rw [parameters_values _ _ _ _ _ hp,TreeFraction.val_repr he.le]
  have ht : 4*CountingPhaseSchedule.observable (Fintype.card (Labels A)) A.W*
      (H+Fintype.card (Labels A)+L+5)=CompanionTargetMixing.restartTime A H L := by
    simp only [CountingPhaseSchedule.observable,CompanionTargetMixing.restartTime,
      CompanionTrace.time,CompanionTrace.integerConstant]
    ring
  dsimp only
  rw [ht]
  rfl

lemma precision_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    precision (parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon))=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).k := by
  rw [parameters_data hEK r c b hne epsilon he,precision_val,
    CountingBaseProgram.half_val,TreeFraction.val_repr he.le]
  rfl

end
end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the immutable rooted state from the public bounded input -/

namespace ContingencyTables.CountingPreparedState
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
lemma polynomial_catalog : PolynomialTime catalogRealizer := CountingComputedSettings.polynomial_catalog

lemma polynomial_baseline : PolynomialTime baselineRealizer :=
  polynomial_composition polynomial_first TightenedInputProgram.polynomial_baseline

lemma polynomial_capacity : PolynomialTime capacityRealizer := polynomial_composition polynomial_catalog polynomial_second

lemma polynomial_zeroMatrix : PolynomialTime zeroMatrixRealizer :=
  polynomial_composition polynomial_capacity (polynomial_map (polynomial_map (polynomial_constant 0)))

lemma polynomial_demand : PolynomialTime demandRealizer :=
  polynomial_pair polynomial_catalog (polynomial_pair polynomial_baseline
    (polynomial_pair polynomial_zeroMatrix polynomial_capacity))

lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first CountingBaseProgram.polynomial_dimension)
    CountingTerminalProgram.polynomial_cutoff) (polynomial_pair CountingBaseProgram.polynomial_coefficient
      (polynomial_constant 0))

lemma polynomial_zeroGrid : PolynomialTime zeroGridRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_catalog (polynomial_constant false))
    RootedForestCatalog.polynomial_catalog) (polynomial_map (polynomial_constant 0))

lemma polynomial_state : PolynomialTime stateRealizer :=
  polynomial_pair (polynomial_pair CountingTerminalProgram.polynomial_binCount
    (polynomial_pair polynomial_parameters polynomial_demand)) polynomial_zeroGrid

lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair polynomial_state CountingComputedSettings.polynomial_parameters

open CompanionFactorialApplication ForestAssignmentSplit
open scoped Classical
variable {m n : ℕ}

lemma demand_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    demand (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedDemandProgram.data (ComputedCountingParameters.data hEK r c b hne epsilon he)
        (fun _ _ => 0) (ComputedCountingParameters.data hEK r c b hne epsilon he).b := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hc : catalog (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=RootedForestCatalog.data A :=
    CountingComputedSettings.catalog_data hEK r c b hne epsilon he
  have hb : baseline (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      matrixCode (fun i j => (A.X i j).toNat) := by
    exact ComputedRootedInput.baseline_instance hEK r c b hne _ (ComputedCountingParameters.cutoff_two r c b epsilon he)
  have hcap : capacity (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode A.b := by
    rw [capacity,hc]
    rfl
  have hz : zeroMatrix (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=matrixCode (fun (_ : Fin m) (_ : Fin n) => 0) := by
    rw [zeroMatrix,hcap]
    simp only [matrixCode,List.map_ofFn,Function.comp_def]
  unfold demand RootedDemandProgram.data
  rw [hc,hb,hz,hcap]

lemma state_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    state (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      RootedOracleWalkProgram.data A C 0 K (fun _ => 0)
        (start A K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  have hp : parameters (NetworkVertexCode.data r c b,TreeFraction.repr epsilon)=
      ((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)) := by
    unfold parameters
    rw [CountingBaseProgram.dimension_data,CountingTerminalProgram.cutoff_data r c b epsilon he,
      CountingBaseProgram.coefficient_data r c b epsilon he]
    rfl
  have hz : ForestCountIdentification.smallX A.small (fun _ => 0)=(fun _ _ => 0) := by
    funext i j
    simp [ForestCountIdentification.smallX]
  have hq : (fun i j => A.b i j-ForestCountIdentification.smallY A.small (fun _ => 0) i j)=A.b := by
    funext i j
    simp [ForestCountIdentification.smallY]
  unfold state RootedOracleWalkProgram.data
  rw [CountingTerminalProgram.binCount_data r c b epsilon he,hp,hz,hq,demand_data hEK r c b hne epsilon he]
  apply congrArg (fun coords => ((ComputedCountingParameters.binCount r c b epsilon,
    (((A.d,A.W),(ComputedCountingParameters.coefficient r c b epsilon,0)),
      RootedDemandProgram.data A (fun _ _ => 0) A.b)),coords))
  unfold zeroGrid catalog
  rw [CountingComputedSettings.catalog_data hEK r c b hne epsilon he]
  simp [DensePrograms.gridNatCode,start,GridBoundary.corner,RootedCatalogGrid.freeCount]

end ContingencyTables.CountingPreparedState

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionRepetitionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the confidence repetition count on a rational input -/
namespace ContingencyTables.FractionRepetitionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_count : PolynomialTime countRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 64)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition TreeFraction.polynomial_normalize polynomial_second) polynomial_toBits)
      polynomial_listLength) polynomial_successor)) polynomial_multiply
lemma count_val (x : TreeFraction.Fraction) : count x=CommonBasesFPRAS.repetitionCount (TreeFraction.val x) := by
  simp only [count,TreeFraction.normalize_repr,TreeFraction.repr,CommonBasesFPRAS.repetitionCount]
end ContingencyTables.FractionRepetitionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed initial record is the literal adaptive counting record -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionMultiplierMatrixProgram TwoLiftStates GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (reserve : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),reserve)=
      CompanionRestartInitializer.data A s.C s.K s.H
        (CompanionTargetMixing.restartTime A s.H s.L) s.N s.n s.L
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  dsimp only
  unfold prepared CountingPreparedState.output
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingComputedSettings.parameters_data hEK r c b hne epsilon he]
  rfl

end
end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Outer confidence repetition of the executed counting program -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped CommonBasesFPRAS GridBoundary

variable (single : Input→TreeFraction.Fraction) (F : Realizer single)
variable (width : Request→ℕ) (N : Realizer width)

lemma polynomial_repeats : PolynomialTime repeatsRealizer :=
  polynomial_composition polynomial_second FractionRepetitionProgram.polynomial_count

attribute [local irreducible] prepared

lemma polynomial_budget (hN : PolynomialTime N) : PolynomialTime (budgetRealizer width N) :=
  polynomial_composition (polynomial_pair polynomial_repeats hN) polynomial_multiply

end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The direct binary evaluator uses the original counting parameters -/
namespace ContingencyTables.CountingDirectProgram
open MatchingFPRAS CompanionFactorialApplication GridBoundary CompanionOracleDensity
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma accuracy_value (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (bits : List Bool) :
    TreeFraction.val (accuracy (request r c b epsilon delta,bits))=(epsilon/2)/2 := by
  change TreeFraction.val (CountingBaseProgram.half (CountingBaseProgram.half (TreeFraction.repr epsilon)))=_
  rw [CountingBaseProgram.half_val,CountingBaseProgram.half_val,TreeFraction.val_repr he.le]

lemma oracleInput_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let C := ComputedCountingParameters.coefficient r c b epsilon
    let K := ComputedCountingParameters.binCount r c b epsilon
    let H := ComputedCountingParameters.phases r c b epsilon
    oracleInput (request r c b epsilon delta,bits)=
      RootedOracleConfigProgram.data A C K H
        (accuracy (request r c b epsilon delta,bits)) (fun _ => 0)
        (CountingPreparedState.start A K (ComputedCountingParameters.binCount_pos r c b epsilon he))
        (bits.map (fun _ => false)) := by
  dsimp only
  unfold oracleInput request
  rw [CountingPreparedState.state_data hEK r c b hne epsilon he,
    CountingTerminalProgram.phases_data r c b epsilon he]
  rfl

lemma wordWidth_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta)
    (bits : List Bool) :
    wordWidth (request r c b epsilon delta,bits)=
      ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta := by
  have hr : repeats (request r c b epsilon delta,bits)=CommonBasesFPRAS.repetitionCount delta := by
    change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
    rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]
  rw [wordWidth,hr,contextWidth]
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.contextWidth,RootedOracleConfigProgram.context_data,
    accuracy_value r c b epsilon delta he bits]
  rw [RootedEstimatorMedianProgram.context,RootedEstimatorWordProgram.scheduledWordWidth]
  unfold ComputedCountingZero.zeroBits medianEstimatorBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]

lemma degree_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    RootedOracleConfigProgram.rootDegree (oracleInput (request r c b epsilon delta,bits))=
      degree r c b epsilon := by
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.rootDegree_data,accuracy_value r c b epsilon delta he bits]
  rfl

lemma depth_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon)
    (bits : List Bool) :
    RootedOracleConfigProgram.depth (oracleInput (request r c b epsilon delta,bits))=
      depth r c b epsilon := by
  rw [oracleInput_data hEK r c b hne epsilon delta he bits,
    RootedOracleConfigProgram.depth_data,accuracy_value r c b epsilon delta he bits]
  rfl

lemma budget_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    budget (request r c b epsilon delta)=
      ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta+degree r c b epsilon+depth r c b epsilon := by
  unfold budget padding empty
  rw [wordWidth_data hEK r c b hne epsilon delta he hd [],
    degree_data hEK r c b hne epsilon delta he [],depth_data hEK r c b hne epsilon delta he []]
  omega

end
end ContingencyTables.CountingDirectProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAmplifiedLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact law and public word budget of outer confidence repetition -/
namespace ContingencyTables.CountingAmplifiedProgram
open MatchingFPRAS GridBoundary CommonBasesFPRAS FiniteObservableTransport Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section

variable (single : Input→TreeFraction.Fraction) (width : Request→ℕ)

variable {m n : ℕ}

lemma repeats_request (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (hd : 0 < delta) :
    repeats (CountingDirectProgram.request r c b epsilon delta)=repetitionCount delta := by
  change FractionRepetitionProgram.count (TreeFraction.repr delta)=_
  rw [FractionRepetitionProgram.count_val,TreeFraction.val_repr hd.le]

lemma budget_bound (p : Polynomial ℕ)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (hd : 0 < delta)
    (hw : width (CountingDirectProgram.request r c b epsilon delta) ≤ p.eval (size r c b epsilon delta)) :
    budget width (CountingDirectProgram.request r c b epsilon delta) ≤
      (budgetPolynomial p).eval (size r c b epsilon delta) := by
  unfold budget
  rw [repeats_request r c b epsilon delta hd]
  simpa only [budgetPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,
    CommonBasesFPRAS.repetitionCount]
    using Nat.mul_le_mul (repeats_le r c b epsilon delta) hw

end
end ContingencyTables.CountingAmplifiedProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma weight_word (as : List Symbol) : weight as=18*as.length+1 := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [weight_cons,weight_symbol,ih,List.length_cons]; omega

end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

lemma bits_fold (n : ℕ) (ns : List ℕ) :
    (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=n::ns := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn,List.map_cons,List.foldr_cons,ih]
    cases b <;> simp [fromBit,numStep,Nat.bit]
lemma encodeNat_fold (n : ℕ) (ns : List ℕ) :
    (encodeNat n).foldr (fun a ns=>numStep (a,ns)) ns=n::ns := by
  change (n.bits.map fromBit++[3]).foldr _ ns=_
  rw [List.foldr_append]
  change (n.bits.map fromBit).foldr (fun a ns=>numStep (a,ns)) (0::ns)=_
  exact bits_fold n ns
lemma encodeInt_fold (z : ℤ) (ns : List ℕ) :
    (encodeInt z).foldr (fun a ns=>numStep (a,ns)) ns=z.natAbs::ns := by
  unfold encodeInt
  rw [List.foldr_append,encodeNat_fold]
  split_ifs <;> simp [numStep]
lemma encodeRat_fold (q : ℚ) (ns : List ℕ) :
    (encodeRat q).foldr (fun a ns=>numStep (a,ns)) ns=q.num.natAbs::q.den::ns := by
  rw [encodeRat,List.foldr_append,encodeNat_fold,encodeInt_fold]
end MatchingFPRAS.LiteralParse

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyPublicProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public margins and printing the greedy matrix

All operations are existing binary list programs. The bounded take and
drop operations also terminate polynomially on malformed headers.
-/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS TreeTyped LiteralCodec LiteralParse
open scoped BigOperators

lemma natWords_fold (ns tail : List ℕ) :
    (ns.flatMap encodeNat).foldr (fun a ns => numStep (a,ns)) tail=ns++tail := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold,List.cons_append]

lemma encodeMargins_natWords {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    Algorithms.encodeMargins r c=
      (m::n::(List.ofFn r++List.ofFn c)).flatMap encodeNat := by
  simp only [Algorithms.encodeMargins,List.flatMap_cons,List.flatMap_append]
  simp only [List.ofFn_comp',List.flatMap_def,List.append_assoc]

lemma marginLists_spec (m n : ℕ) (rs cs tail : List ℕ)
    (hr : rs.length=m) (hc : cs.length=n) :
    marginLists (m::n::(rs++cs++tail))=(rs,cs) := by
  simp only [marginLists,List.headD_cons,List.tail_cons]
  rw [←hr,←hc]
  simp only [List.append_assoc,List.take_left,List.drop_left]

lemma printMatrix_ofFn {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    printMatrix (List.ofFn (fun i => List.ofFn (X i)))=Algorithms.encodeMatrix X := by
  simp only [printMatrix,Algorithms.encodeMatrix,List.flatMap_def,List.ofFn_comp',List.map_map,
    Function.comp_def]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingInputParser
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the public cell-bounded counting input

Dimensions only delimit bounded list slices. The matrix layout uses the
lengths of the parsed margin lists, so malformed headers do not create
unbounded numeric loops. Positive rational parameters use their natural
numerator and denominator, exactly as in the public tape encoding.
-/

namespace ContingencyTables.CountingInputParser
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse
open MatchingFPRAS.TreeFraction DensePrograms

lemma decode_blocks (rs cs flat tail : List ℕ) (hf : flat.length=rs.length*cs.length) :
    decode (rs.length::cs.length::(rs++cs++flat++tail))=
      (( (rs,cs),unflattenGrid ((0::rs,0::cs),flat)),fractionPair tail) := by
  have hm := GreedyFeasibleTable.marginLists_spec rs.length cs.length rs cs (flat++tail) rfl rfl
  have hr : rest (rs.length::cs.length::(rs++cs++flat++tail))=flat++tail := by
    simp only [rest,offset,List.headD_cons,List.tail_cons]
    rw [show 2+rs.length+cs.length=(rs.length+cs.length)+1+1 by omega]
    simp only [List.drop_succ_cons,List.append_assoc]
    rw [←List.drop_drop,List.drop_left,List.drop_left]
  have hc : cells (rs.length::cs.length::(rs++cs++flat++tail))=flat.length := by
    unfold cells
    rw [show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc],hm]
    exact hf.symm
  simp only [decode,capacityFrame,parameters]
  rw [show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc],hm]
  rw [←show rs++cs++flat++tail=rs++cs++(flat++tail) by simp only [List.append_assoc]]
  rw [hr,hc,List.take_left,List.drop_left]

lemma encodeMatrix_words {m n : ℕ} (b : Fin m→Fin n→ℕ) :
    Algorithms.encodeMatrix b=
      (List.ofFn (fun i => List.ofFn (b i))).flatten.flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  unfold GreedyFeasibleTable.printMatrix
  generalize List.ofFn (fun i => List.ofFn (b i))=rows
  induction rows with
  | nil => rfl
  | cons row rows ih => simp only [List.flatMap_cons,List.flatten_cons,List.flatMap_append,ih]

lemma parse_public {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    parse (Algorithms.encodeCountingInput r c b epsilon delta)=
      m::n::(List.ofFn r++List.ofFn c++
        (List.ofFn (fun i => List.ofFn (b i))).flatten++
          [epsilon.num.natAbs,epsilon.den,delta.num.natAbs,delta.den]) := by
  unfold Algorithms.encodeCountingInput parse
  rw [GreedyFeasibleTable.encodeMargins_natWords,encodeMatrix_words]
  simp only [List.foldr_append,encodeRat_fold]
  rw [GreedyFeasibleTable.natWords_fold,GreedyFeasibleTable.natWords_fold]
  simp only [List.cons_append,List.append_assoc]

lemma public_spec {m n : ℕ} (r : Fin m→ℕ) (c : Fin n→ℕ)
    (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    parseInput (Algorithms.encodeCountingInput r c b epsilon delta)=
      (NetworkVertexCode.data r c b,(TreeFraction.repr epsilon,TreeFraction.repr delta)) := by
  unfold parseInput
  rw [parse_public]
  have hf : (List.ofFn (fun i => List.ofFn (b i))).flatten.length=
      (List.ofFn r).length*(List.ofFn c).length := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,List.length_ofFn,
      List.sum_ofFn,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  have hh := decode_blocks (List.ofFn r) (List.ofFn c)
    (List.ofFn (fun i => List.ofFn (b i))).flatten
    [epsilon.num.natAbs,epsilon.den,delta.num.natAbs,delta.den] hf
  simp only [List.length_ofFn] at hh
  rw [hh]
  change (( (List.ofFn r,List.ofFn c),_),_)=( ( (List.ofFn r,List.ofFn c),_),_)
  congr 2
  let f : Fin (m*n)→ℕ := fun k => b (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have he : (List.ofFn (fun i => List.ofFn (b i))).flatten=List.ofFn f := by
    simpa only [f,Equiv.symm_apply_apply,matrixCode] using flatten_matrixCode f
  rw [he]
  simpa only [marginCode,f,Equiv.symm_apply_apply,matrixCode,ResidualGraphProgram.natCode,Option.elim_none,Option.elim_some]
    using unflattenGrid_code (fun i : Option (Fin m) => i.elim 0 r)
      (fun j : Option (Fin n) => j.elim 0 c) f

end ContingencyTables.CountingInputParser

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchSemantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The public counting dispatch preserves the original bounded input -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CompanionFactorialApplication
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma feasible_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ) (epsilon delta : ℚ) :
    feasible (CountingDirectProgram.request r c b epsilon delta)=true ↔
      ∃ X,TableTightening.Feasible r c b X := by
  exact NetworkFeasibilityProgram.test_correct hEK r c b

lemma budget_rejected (positive : Request→ℕ) (req : Request)
    (h : feasible req=false) : budget positive req=0 := by
  simp only [budget,h,Bool.false_eq_true,ite_false]

lemma budget_direct (positive : Request→ℕ) (req : Request)
    (hf : feasible req=true) (hd : direct req=true) :
    budget positive req=CountingDirectProgram.budget req := by
  simp only [budget,feasibleBudget,hf,hd,ite_true, if_true]

lemma budget_positive (positive : Request→ℕ) (req : Request)
    (hf : feasible req=true) (hd : direct req=false) : budget positive req=positive req := by
  simp only [budget,feasibleBudget,hf,hd,ite_true, if_true,Bool.false_eq_true,ite_false]

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectWordBound
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public word budget for the direct zero-label estimator -/
namespace ContingencyTables.CountingDirectWordBound
open CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma zeroBits_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    ComputedCountingZero.zeroBits hEK r c b hne epsilon he delta ≤
      wordPolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let C := ComputedCountingParameters.coefficient r c b epsilon
  let K := ComputedCountingParameters.binCount r c b epsilon
  let H := ComputedCountingParameters.phases r c b epsilon
  let S := size r c b epsilon delta
  let M := controlPolynomial.eval S
  have hSM : S ≤ M := by
    simp only [M,controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hKM : CountingTerminalBounds.gridPolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hHM : CountingTerminalBounds.phasePolynomial.eval S ≤ M := by
    simp only [M,controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have h4SM : 4*S ≤ M := by
    simp only [M,controlPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have ht := CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he
  have hd : A.d ≤ M := (dimension_le r c b epsilon delta).trans hSM
  have hK : K ≤ M := ht.1.trans hKM
  have hH : H ≤ M := ht.2.2.trans hHM
  have hL : CountingTerminalSchedule.capacityBits A ≤ M :=
    (capacityBits_le hEK r c b hne epsilon delta).trans hSM
  have hi : 1/((epsilon/2)/2) ≤ (M:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left (inverse_le r c b epsilon delta)
      (show (0:ℚ) ≤ 4 by norm_num)
    have hh' : 1/((epsilon/2)/2) ≤ ((4*S:ℕ):ℚ) := by
      convert hh using 1 <;> first | rfl | (push_cast; ring)
    exact hh'.trans (by exact_mod_cast h4SM)
  have hr : CommonBasesFPRAS.repetitionCount delta ≤ 64*(M+1) :=
    (repeats_le r c b epsilon delta).trans (Nat.mul_le_mul_left 64 (by omega))
  have hb := CountingOracleWordBounds.median_bound_separate A C K H M ((epsilon/2)/2) delta
    hd hK hH hH hL (by positivity) hi hr
  unfold ComputedCountingZero.zeroBits
  rw [←ComputedCountingParameters.phases_final hEK r c b hne epsilon he]
  simpa only [wordPolynomial,Polynomial.eval_comp] using hb

end
end ContingencyTables.CountingDirectWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingDirectBudgetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public runtime allowance for the direct branch's padded random word -/
namespace ContingencyTables.CountingDirectBudgetBound
open Polynomial CountingPublicInputBounds
open scoped Classical
noncomputable section
variable {m n : ℕ}

lemma budget_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    CountingDirectProgram.budget (CountingDirectProgram.request r c b epsilon delta) ≤
      budgetPolynomial.eval (size r c b epsilon delta) := by
  let S := size r c b epsilon delta
  let M := CountingDirectWordBound.controlPolynomial.eval S
  have hH : ComputedCountingParameters.phases r c b epsilon ≤ M := by
    have hb : CountingTerminalBounds.phasePolynomial.eval S ≤ M := by
      simp only [M,CountingDirectWordBound.controlPolynomial,CountingPublicWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
      omega
    exact (CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he).2.2.trans hb
  have h4S : 4*S ≤ M := by
    simp only [M,CountingDirectWordBound.controlPolynomial,
      Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have hi : 1/((epsilon/2)/2) ≤ (M:ℚ) := by
    have hh := mul_le_mul_of_nonneg_left (inverse_le r c b epsilon delta)
      (show (0:ℚ) ≤ 4 by norm_num)
    have hh' : 1/((epsilon/2)/2) ≤ ((4*S:ℕ):ℚ) := by
      convert hh using 1 <;> first | rfl | (push_cast; ring)
    exact hh'.trans (by exact_mod_cast h4S)
  have hp := CountingMarkerBounds.padding_bound
    (ComputedCountingParameters.phases r c b epsilon) M ((epsilon/2)/2) hH (by positivity) hi
  rw [CountingDirectProgram.budget_data hEK r c b hne epsilon delta he hd]
  have hw := CountingDirectWordBound.zeroBits_public hEK r c b hne epsilon delta he
  rw [Nat.add_assoc]
  simpa only [budgetPolynomial,Polynomial.eval_add,Polynomial.eval_comp,
    CountingDirectProgram.degree,CountingDirectProgram.depth,S,M] using Nat.add_le_add hw hp

end
end ContingencyTables.CountingDirectBudgetBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingBranchBudgetBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Combining the computed counting branches' public word budgets -/
namespace ContingencyTables.CountingBranchProgram
open MatchingFPRAS CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section

lemma publicBudget_bound (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (positive : Request→ℕ) (p : Polynomial ℕ)
    (hp : ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ),
      (∃ X,TableTightening.Feasible r c b X) → ∀ epsilon delta : ℚ,
      0 < epsilon → 0 < delta →
      positive (CountingDirectProgram.request r c b epsilon delta) ≤ p.eval (size r c b epsilon delta))
    (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta) :
    publicBudget positive (Algorithms.encodeCountingInput r c b epsilon delta) ≤
      (budgetPolynomial p).eval (size r c b epsilon delta) := by
  have hrequest : request (CountingInputParser.parseInput
      (Algorithms.encodeCountingInput r c b epsilon delta))=
      CountingDirectProgram.request r c b epsilon delta := by
    rw [CountingInputParser.public_spec]
    rfl
  unfold publicBudget
  rw [hrequest]
  by_cases hf : feasible (CountingDirectProgram.request r c b epsilon delta)=true
  · have hne := (feasible_data hEK r c b epsilon delta).mp hf
    by_cases hz : direct (CountingDirectProgram.request r c b epsilon delta)=true
    · rw [budget_direct positive _ hf hz]
      exact (CountingDirectBudgetBound.budget_public hEK r c b hne epsilon delta he hd).trans
        (by simp only [budgetPolynomial,Polynomial.eval_add]; omega)
    · have hz' : direct (CountingDirectProgram.request r c b epsilon delta)=false :=
        Bool.eq_false_iff.mpr hz
      rw [budget_positive positive _ hf hz']
      exact (hp m n r c b hne epsilon delta he hd).trans
        (by simp only [budgetPolynomial,Polynomial.eval_add]; omega)
  · have hf' : feasible (CountingDirectProgram.request r c b epsilon delta)=false :=
      Bool.eq_false_iff.mpr hf
    rw [budget_rejected positive _ hf']
    exact Nat.zero_le _

end
end ContingencyTables.CountingBranchProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Graphs_ExperimentSupport
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {α β : Type}
lemma all_bind (p : Experiment α) (q : α → Experiment β) (P : β → Prop) :
    All (p.bind q) P ↔ All p (fun a=>All (q a) P) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,All,ih]
  | delay n p ih => exact ih

variable {α : Type}
lemma worst_le (p : Experiment α) (f : α → ℕ) (N : ℕ) (h : All p (fun a=>f a≤N)) : p.worst f≤N := by
  induction p with
  | done a => exact h
  | read p ih => exact max_le (ih false h.1) (ih true h.2)
  | delay n p ih => exact ih h
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Online
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineStack
open Turing MachineCost PhysicalStream

variable {K Λ σ α : Type} {Γ : K → Type} [DecidableEq K]

namespace Executes
variable {M : Λ → TM2.Stmt Γ Λ σ} {coin : CoinTM1.Coins Λ}
  {out : α → TM2.Cfg Γ Λ σ} {c : TM2.Cfg Γ Λ σ} {p : Experiment α}

variable [Fintype K] [∀ k,Fintype (Γ k)] [Inhabited Λ] [Fintype Λ]
  [Inhabited σ] [Fintype σ]

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
lemma factor_mono [Inhabited Λ] [Inhabited σ] [Fintype σ]
    (H H' n n' : ℕ) (hH : H≤H') (hn : n≤n') :
    factor M H n ≤ factor M H' n' := by unfold factor; gcongr
end Executes
end MatchingFPRAS.OnlineStack

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_LiteralProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public binary input and output for typed finite programs

Literal packing is independent of the counting algorithm. Its cost includes every packing, execution, and printing step.
-/

namespace ContingencyTables.LiteralProgram
open MatchingFPRAS Turing PhysicalPost PhysicalStream LiteralPacked TreeTyped Polynomial

lemma packTime_mono {n m : ℕ} (h : n ≤ m) : packTime n ≤ packTime m := by
  unfold packTime LiteralBlockMap.budget
  gcongr

lemma postTime_mono {n m : ℕ} (h : n ≤ m) : postTime n ≤ postTime m := by
  unfold postTime LiteralBlockMap.budget
  gcongr

lemma eval_budgetPolynomial (w H : ℕ) (p q : Polynomial ℕ) (n : ℕ) :
    (budgetPolynomial w H p q).eval n=LiteralBlockMap.budget w H (p.eval n) (q.eval n) := by
  simp only [budgetPolynomial,LiteralBlockMap.budget,eval_mul,eval_add,eval_C,eval_one,eval_ofNat]

end ContingencyTables.LiteralProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_OnlineFoldCost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]

omit [Codec B] in
lemma fold_cost_bound (f : A×B→Experiment B) (t : A×B→ℕ)
    (as : List A) (b : B) (P : ℕ→B→Prop) (C M : ℕ)
    (hb : P as.length b) (hw : weight as≤M)
    (hs : ∀ a∈as,∀ k<as.length,∀ b,P (k+1) b→(f (a,b)).All (P k))
    (hc : ∀ a∈as,∀ k<as.length,∀ b,P (k+1) b→t (a,b)≤C) :
    Fold.cost f t as b≤as.length*(C+14*M+34)+10 ∧ (foldM f as b).All (P 0) := by
  induction as generalizing b with
  | nil => exact ⟨by simp [Fold.cost],hb⟩
  | cons a as ih =>
    have hwa : weight a≤M := by rw [weight_cons] at hw; omega
    have hwt : weight as≤M := by rw [weight_cons] at hw; omega
    have hb' : P (as.length+1) b := hb
    have hstep := hs a (by simp) as.length (by simp) b hb'
    have htime := hc a (by simp) as.length (by simp) b hb'
    have htt : (f (a,b)).All (fun v=>Fold.cost f t as v≤as.length*(C+14*M+34)+10 ∧
        (foldM f as v).All (P 0)) := hstep.mono (fun v hv=>ih v hv hwt
          (fun a ha k hk v hv=>hs a (by simp [ha]) k (by simp only [List.length_cons]; omega) v hv)
          (fun a ha k hk v hv=>hc a (by simp [ha]) k (by simp only [List.length_cons]; omega) v hv))
    constructor
    · have hworst := Experiment.worst_le _ _ _ (htt.mono (fun _ h=>h.1))
      change t (a,b)+6*weight a+8*weight as+34+_≤_
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [foldM,Experiment.all_bind]
      exact htt.mono (fun _ h=>h.2)

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_OnlineCost
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A B : Type}
lemma worst_bind (p : Experiment A) (f : A→Experiment B) (h : B→ℕ) :
    (p.bind f).worst h=p.worst (fun a=>(f a).worst h) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,worst,ih]
  | delay n p ih => exact ih
lemma worst_map (p : Experiment A) (f : A→B) (h : B→ℕ) :
    (p.map f).worst h=p.worst (h ∘ f) := worst_bind _ _ _
lemma worst_eq_of_mean_eq {p q : Experiment A} (h : ∀ f : A→ℚ,p.mean f=q.mean f) (g : A→ℕ) :
    p.worst g=q.worst g := by
  apply Nat.le_antisymm
  · exact worst_le _ _ _ (all_of_mean_eq h _ (all_worst q g))
  · exact worst_le _ _ _ (all_of_mean_eq (fun f=>(h f).symm) _ (all_worst p g))
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma work_deterministic {f : A→B} {F : TreeTyped.Realizer f} {m : A→ℕ}
    (hF : TreeTyped.WorkBound F m) : WorkBound (deterministic F) m := hF
lemma work_congr {f g : A→Experiment B} {F : Realizer f} {m : A→ℕ}
    (h : ∀ a w,(f a).mean w=(g a).mean w) (hF : WorkBound F m) : WorkBound (F.congr h) m := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  change F.cost a+(g a).worst weight≤_
  rw [←Experiment.worst_eq_of_mean_eq (h a)]
  exact hp a
lemma work_remeasure {f : A→Experiment B} {F : Realizer f} {m n : A→ℕ}
    (hF : WorkBound F m) (p : Polynomial ℕ) (hm : ∀ a,m a≤p.eval (n a)) : WorkBound F n := by
  obtain ⟨q,hq⟩:=hF
  exact ⟨q.comp p,fun a=>(hq a).trans (by simpa using polynomial_eval_monotone q (hm a))⟩
lemma work_of_polynomial {f : A→Experiment B} {F : Realizer f} {m : A→ℕ}
    (hF : PolynomialTime F) (p : Polynomial ℕ) (hm : ∀ a,weight a≤p.eval (m a)) : WorkBound F m :=
  work_remeasure hF p hm
lemma work_composition {f : A→Experiment B} {g : B→Experiment C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} {n : B→ℕ} (hF : WorkBound F m) (hG : WorkBound G n)
    (p : Polynomial ℕ) (hm : ∀ a,(f a).All (fun b=>n b≤p.eval (m a))) :
    WorkBound (composition F G) m := by
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=hG
  refine ⟨q+2*(r.comp p),fun a=>?_⟩
  have hb : (f a).All (fun b=>G.cost b+(g b).worst weight ≤ r.eval (p.eval (m a))) :=
    (hm a).mono (fun b hb=>(hr b).trans (polynomial_eval_monotone r hb))
  have h1:=Experiment.worst_le _ _ _ (hb.mono (fun b hb=>Nat.le_trans (Nat.le_add_right _ _) hb))
  have h2:=Experiment.worst_le _ _ _ (hb.mono (fun b hb=>Nat.le_trans (Nat.le_add_left _ _) hb))
  have h3:=hq a
  change F.cost a+(f a).worst G.cost+((f a).bind g).worst weight≤_
  rw [Experiment.worst_bind]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega
lemma work_then_polynomial {f : A→Experiment B} {g : B→Experiment C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} (hF : WorkBound F m) (hG : PolynomialTime G) : WorkBound (composition F G) m := by
  obtain ⟨p,hp⟩:=hF
  apply work_composition ⟨p,hp⟩ hG p
  intro a
  exact (Experiment.all_worst (f a) weight).mono (fun b hb=>hb.trans (Nat.le_trans (Nat.le_add_left _ _) (hp a)))
lemma polynomial_deterministic {f : A→B} {F : TreeTyped.Realizer f} (hF : TreeTyped.PolynomialTime F) :
    PolynomialTime (deterministic F) := hF
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_OnlineFrameCost
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A : Type}
lemma worst_affine (p : Experiment A) (g : A→ℕ) (k c : ℕ) :
    p.worst (fun a=>k*g a+c)=k*p.worst g+c := by
  induction p with
  | done a => rfl
  | read p ih =>
    simp only [worst,ih]
    rcases le_total ((p false).worst g) ((p true).worst g) with h|h
    · rw [max_eq_right h,max_eq_right (Nat.add_le_add_right (Nat.mul_le_mul_left k h) c)]
    · rw [max_eq_left h,max_eq_left (Nat.add_le_add_right (Nat.mul_le_mul_left k h) c)]
  | delay n p ih => exact ih
lemma worst_const_add (p : Experiment A) (c : ℕ) (g : A→ℕ) :
    p.worst (fun a=>c+g a)=c+p.worst g := by
  simpa only [one_mul,Nat.add_comm c] using worst_affine p g 1 c
lemma worst_add_const (p : Experiment A) (g : A→ℕ) (c : ℕ) :
    p.worst (fun a=>g a+c)=p.worst g+c := by
  simpa only [one_mul] using worst_affine p g 1 c
end MatchingFPRAS.PhysicalStream.Experiment

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma pair_cost {f : A→Experiment B} {g : A→Experiment C} (F : Realizer f) (G : Realizer g) (a : A) :
    (pair F G).cost a=F.cost a+G.cost a+45*weight a+26*(f a).worst weight+137 := by
  simp only [pair,Realizer.congr,composition,deterministic,mapSecond,TreeTyped.pair,
    TreeTyped.identity,TreeTyped.first,TreeTyped.second,Experiment.worst_map,
    Experiment.worst,Function.comp_def,id_eq]
  change 1+1+11*weight a+6*weight a+31+
    (F.cost a+8*weight a+22+(f a).worst (fun b=>
      3*weight a+7+(6*weight a+weight b+11)+11*weight (a,b)+6*weight b+31+
        (G.cost a+8*weight b+22)))=_
  simp only [weight_prod]
  have h : (fun b : B=>3*weight a+7+(6*weight a+weight b+11)+11*(1+weight a+weight b)+6*weight b+31+
        (G.cost a+8*weight b+22))=(fun b=>26*weight b+(20*weight a+G.cost a+82)) := by funext b; omega
  rw [h,Experiment.worst_affine]
  omega
omit [Codec A] in
lemma pair_weight [Codec A] {f : A→Experiment B} {g : A→Experiment C} (a : A) :
    ((f a).bind (fun b=>(g a).map (Prod.mk b))).worst weight=
      1+(f a).worst weight+(g a).worst weight := by
  rw [Experiment.worst_bind]
  simp only [Experiment.worst_map,Function.comp_def,weight_prod,
    Experiment.worst_const_add,Experiment.worst_add_const]
lemma work_pair {f : A→Experiment B} {g : A→Experiment C} {F : Realizer f} {G : Realizer g}
    {m : A→ℕ} (hF : WorkBound F m) (hG : WorkBound G m)
    (p : Polynomial ℕ) (hw : ∀ a,weight a≤p.eval (m a)) : WorkBound (pair F G) m := by
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=hG
  refine ⟨27*q+r+45*p+138,fun a=>?_⟩
  change (pair F G).cost a+((f a).bind (fun b=>(g a).map (Prod.mk b))).worst weight≤_
  rw [pair_cost,pair_weight]
  have h1:=hq a
  have h2:=hr a
  have h3:=hw a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  omega
lemma work_choose {f g : A→Experiment B} {F : Realizer f} {G : Realizer g} {m : A→ℕ}
    (hF : WorkBound F m) (hG : WorkBound G m) : WorkBound (choose F G) m := by
  obtain ⟨p,hp⟩:=hF
  obtain ⟨q,hq⟩:=hG
  refine ⟨p+q+1,fun a=>?_⟩
  change 1+max (F.cost a) (G.cost a)+max ((f a).worst weight) ((g a).worst weight)≤_
  have h1:=hp a
  have h2:=hq a
  simp only [Polynomial.eval_add,Polynomial.eval_one]
  omega
lemma polynomial_choose {f g : A→Experiment B} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (choose F G) := work_choose hF hG
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_OnlineWord
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open PhysicalStream TreeData TreeFunction TreeTyped OnlineTree

lemma all_length (n : ℕ) (acc : List Bool) :
    (prepend n acc).All (fun bs=>bs.length=n+acc.length) := by
  induction n generalizing acc with
  | zero => simp only [prepend,Experiment.All,Nat.zero_add]
  | succ n ih =>
    change (prepend n (false::acc)).All _ ∧ (prepend n (true::acc)).All _
    constructor <;> exact (ih _).mono (fun bs h=>by simp only [List.length_cons] at h; omega)
end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_OnlineWordCost
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineWord
open TreeTyped OnlineTree PhysicalStream Polynomial

lemma polynomial_step : OnlineTree.PolynomialTime stepRealizer := by
  unfold stepRealizer
  apply OnlineTree.work_congr
  apply OnlineTree.polynomial_choose <;> apply OnlineTree.polynomial_deterministic <;>
    apply TreeTyped.polynomial_composition <;> first | exact TreeTyped.polynomial_listCons |
      exact TreeTyped.polynomial_pair (TreeTyped.polynomial_constant _) TreeTyped.polynomial_second

lemma weight_bools (bs : List Bool) : weight bs≤4*bs.length+1 := by
  induction bs with
  | nil => simp
  | cons b bs ih => have hb:=TreeTyped.weight_bool b; simp only [weight_cons,List.length_cons];omega
lemma all_weight (n : ℕ) (acc : List Bool) :
    (prepend n acc).All (fun bs=>weight bs≤4*(n+acc.length)+1) :=
  (all_length n acc).mono (fun bs hb=>by rw [←hb]; exact weight_bools bs)

lemma polynomial_list : OnlineTree.PolynomialTime listRealizer := by
  obtain ⟨p,hp⟩:=polynomial_step
  have prep := TreeTyped.polynomial_pair (TreeTyped.polynomial_identity (A:=List ℕ))
    (TreeTyped.polynomial_constant ([] : List Bool))
  obtain ⟨q,hq⟩:=prep
  refine ⟨q+X*((p.comp (5*X+2))+14*X+34)+4*X+11,fun as=>?_⟩
  let S:=weight as
  have hlen : as.length≤S := list_length_le_weight as
  have bound := OnlineTree.fold_cost_bound step stepRealizer.cost as ([] : List Bool)
    (fun k bs=>bs.length+k=as.length) (p.eval (5*S+2)) S (by simp) le_rfl
    (by
      intro a ha k hk bs hb
      simp only [step,Experiment.All,List.length_cons]
      constructor <;> omega)
    (by
      intro a ha k hk bs hb
      have ha' : weight a≤S := weight_mem ha
      have hbs:=weight_bools bs
      have hw : weight (a,bs)≤5*S+2 := by rw [weight_prod];omega
      exact (Nat.le_add_right _ _).trans ((hp (a,bs)).trans (polynomial_eval_monotone p hw)))
  have hlenmul := Nat.mul_le_mul_right (p.eval (5*S+2)+14*S+34) hlen
  have hout := Experiment.worst_le _ _ _ (all_weight as.length [])
  have hpre:=hq as
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List Bool))).cost as+
    OnlineTree.Fold.cost step stepRealizer.cost as []+(prepend as.length []).worst weight≤_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_comp,Polynomial.eval_X,Polynomial.eval_ofNat]
  dsimp [S] at *
  omega

lemma work_natural : OnlineTree.WorkBound naturalRealizer (fun n=>n+weight n) := by
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial _ polynomial_list
  exact OnlineTree.work_deterministic (TreeTyped.work_remeasure TreeTyped.range_numeric_work X (fun n=>by simp))
end MatchingFPRAS.OnlineWord

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordExecution
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing a computed finite Boolean sampler

The program reads a fresh word on the physical online machine, preserves
the input, and runs the deterministic binary sampler on that word.
-/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Polynomial

variable {A B : Type} [TreeTyped.Codec A] [TreeTyped.Codec B]

theorem work_source {n : A → ℕ} {N : TreeTyped.Realizer n}
    (hN : TreeTyped.PolynomialTime N) :
    OnlineTree.WorkBound (sourceRealizer N) (wordMeasure n) := by
  unfold sourceRealizer
  apply OnlineTree.work_congr
  have hN' : OnlineTree.WorkBound (OnlineTree.deterministic N) (wordMeasure n) :=
    OnlineTree.work_of_polynomial (OnlineTree.polynomial_deterministic hN) X (by
      intro a
      simp only [eval_X,wordMeasure]
      omega)
  apply OnlineTree.work_composition hN' OnlineWord.work_natural (5*X+1)
  intro a
  change n a+TreeTyped.weight (n a)≤(5*X+1).eval (wordMeasure n a)
  have hw := TreeTyped.weight_nat_numeric (n a)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one,wordMeasure]
  omega

/-- Runtime is polynomial in the input's encoded size plus the number of
fresh bits. -/
theorem work_realizer {n : A → ℕ} {f : A×List Bool → B}
    {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f}
    (hN : TreeTyped.PolynomialTime N) (hF : TreeTyped.PolynomialTime F) :
    OnlineTree.WorkBound (realizer N F) (wordMeasure n) := by
  unfold realizer
  apply OnlineTree.work_congr
  apply OnlineTree.work_then_polynomial _ (OnlineTree.polynomial_deterministic hF)
  have hid : OnlineTree.WorkBound (OnlineTree.deterministic (TreeTyped.identity (A := A)))
      (wordMeasure n) :=
    OnlineTree.work_of_polynomial (OnlineTree.polynomial_deterministic TreeTyped.polynomial_identity) X (by
      intro a
      simp only [eval_X,wordMeasure]
      omega)
  apply OnlineTree.work_pair hid (work_source hN) X
  intro a
  simp only [eval_X,wordMeasure]
  omega

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FiniteWordMachine
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single physical machine for a computed finite-word algorithm -/

namespace ContingencyTables.FiniteWordExecution
open MatchingFPRAS MatchingFPRAS.PhysicalStream Turing
open TreeTyped Polynomial

variable {n : List Symbol → ℕ} {f : List Symbol×List Bool → List Symbol}

/-- Packing, coin reads, deterministic execution and public output all
have a polynomial bound in encoded input size plus the declared word. -/
theorem machineTime_polynomial {N : TreeTyped.Realizer n} {F : TreeTyped.Realizer f}
    (hN : TreeTyped.PolynomialTime N) (hF : TreeTyped.PolynomialTime F) :
    ∃ q : Polynomial ℕ,∀ as,machineTime N F as≤q.eval (wordMeasure n as) := by
  obtain ⟨p,hp⟩ := work_realizer hN hF
  let G := realizer N F
  let a := OnlineStack.accesses G.program.code
  let o := OnlineStack.overhead G.program.code
  let pk : Polynomial ℕ := (1+LiteralProgram.budgetPolynomial 1 (18*LiteralPacked.width) X 0)*
    C (MachineCost.programCost LiteralPacked.packCode)
  let out : Polynomial ℕ := C (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))+
    (1+LiteralProgram.budgetPolynomial (18*LiteralPacked.width) 1 p 0)*
      C (MachineCost.programCost LiteralPacked.unpackCode)
  let fac : Polynomial ℕ := C o*(1+2*C a*(X+p*C a+1))+1
  refine ⟨pk+p*fac+out,fun as => ?_⟩
  let M := wordMeasure n as
  have hw : weight as≤M := Nat.le_add_right _ _
  have hn : as.length≤M := (list_length_le_weight as).trans hw
  have hc : G.cost as≤p.eval M := (Nat.le_add_right _ _).trans (hp as)
  have hout : (experiment n f as).worst weight≤p.eval M :=
    (Nat.le_add_left _ _).trans (hp as)
  have hl : (experiment n f as).worst List.length≤p.eval M :=
    Experiment.worst_le _ _ _ ((Experiment.all_worst _ weight).mono
      (fun bs hbs => (list_length_le_weight bs).trans (hbs.trans hout)))
  have hf : OnlineStack.Executes.factor G.program.code (weight as) (G.cost as)≤fac.eval M := by
    have he : fac.eval M=OnlineStack.Executes.factor G.program.code M (p.eval M) := by
      simp only [fac,eval_add,eval_mul,eval_C,eval_ofNat,eval_X,eval_one,
        OnlineStack.Executes.factor,a,o]
    rw [he]
    exact OnlineStack.Executes.factor_mono _ _ _ _ hw hc
  have hpk : pk.eval M=LiteralProgram.packTime M := by
    simp only [pk,eval_mul,eval_add,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.packTime]
  have hpout : out.eval M=LiteralProgram.postTime (p.eval M) := by
    simp only [out,eval_add,eval_mul,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_zero,LiteralProgram.postTime]
  change LiteralProgram.wrapTime G as≤(pk+p*fac+out).eval M
  simp only [eval_add,eval_mul,hpk,hpout]
  unfold LiteralProgram.wrapTime OnlineTree.physicalCost
  exact Nat.add_le_add
    (Nat.add_le_add (LiteralProgram.packTime_mono hn) (Nat.mul_le_mul hc hf))
    (LiteralProgram.postTime_mono hl)

end ContingencyTables.FiniteWordExecution

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRuntimeBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A uniform public polynomial bound for the physical sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec Polynomial
open scoped BigOperators

lemma polynomial_scaled_power (p : Polynomial ℕ) (A x b : ℕ) (hx : 1≤x) :
    p.eval (A*x^b)≤p.eval A*x^(b*p.natDegree) := by
  rw [p.eval_eq_sum_range,p.eval_eq_sum_range,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i≤p.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [mul_pow,←pow_mul]
  calc
    p.coeff i*(A^i*x^(b*i))=(p.coeff i*A^i)*x^(b*i) := by ring
    _ ≤ (p.coeff i*A^i)*x^(b*p.natDegree) :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (Nat.mul_le_mul_left b hi'))
    _ = _ := by ring

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingMachineTime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform public time from the counting word budget -/
namespace ContingencyTables.CountingMachineTime
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec
open CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section

variable {wordCount : List Symbol→ℕ} {output : List Symbol×List Bool→List Symbol}

theorem public_bound (N : Realizer wordCount) (F : Realizer output)
    (hN : PolynomialTime N) (hF : PolynomialTime F) (p : Polynomial ℕ)
    (hb : ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (epsilon delta : ℚ), 0 < epsilon → 0 < delta →
      wordCount (Algorithms.encodeCountingInput r c b epsilon delta) ≤
        p.eval (size r c b epsilon delta)) :
    ∃ C d : ℕ, 0 < C ∧
      ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
        (epsilon delta : ℚ), 0 < epsilon → 0 < delta →
        FiniteWordExecution.machineTime N F (Algorithms.encodeCountingInput r c b epsilon delta) ≤
          Algorithms.countingTime C d r c b epsilon delta := by
  obtain ⟨q,hq⟩ := FiniteWordExecution.machineTime_polynomial hN hF
  let P : Polynomial ℕ := q.comp (18*X+1+p)
  refine ⟨P.eval 1+1,P.natDegree,by omega,?_⟩
  intro m n r c b epsilon delta he hd
  let S := size r c b epsilon delta
  have hS : 1 ≤ S := by unfold S size; omega
  have hlen : (Algorithms.encodeCountingInput r c b epsilon delta).length ≤ S := by
    unfold S size
    omega
  have hm : FiniteWordExecution.wordMeasure wordCount
      (Algorithms.encodeCountingInput r c b epsilon delta) ≤ (18*X+1+p).eval S := by
    unfold FiniteWordExecution.wordMeasure
    rw [weight_word]
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    exact Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 18 hlen) 1)
      (hb m n r c b epsilon delta he hd)
  calc
    _ ≤ q.eval (FiniteWordExecution.wordMeasure wordCount
        (Algorithms.encodeCountingInput r c b epsilon delta)) := hq _
    _ ≤ q.eval ((18*X+1+p).eval S) := polynomial_eval_monotone q hm
    _ = P.eval S := by simp only [P,Polynomial.eval_comp]
    _ ≤ P.eval 1*S^P.natDegree := by
      simpa only [one_mul,pow_one] using ProfilePrograms.polynomial_scaled_power P 1 S 1 hS
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.le_succ _)

end
end ContingencyTables.CountingMachineTime

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed positive-label counting run

The supplied word is partitioned into equally padded phase words. The phase
count only truncates a supplied list, so malformed scalar inputs do
not create an unbounded loop.
-/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_prepared : PolynomialTime preparedRealizer :=
  polynomial_composition polynomial_first CountingPreparedState.polynomial_output

lemma polynomial_phaseCount : PolynomialTime phaseCountRealizer :=
  polynomial_composition (polynomial_composition polynomial_prepared polynomial_second)
    (CountingPhaseParametersProgram.polynomial_scalar (.input 2))

lemma polynomial_phaseWidth : PolynomialTime phaseWidthRealizer :=
  polynomial_composition polynomial_prepared CompanionUniformPhaseWidth.polynomial_width

theorem polynomial_bitCount : PolynomialTime bitCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_phaseCount polynomial_phaseWidth) polynomial_multiply

attribute [local irreducible] historyInput

end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input semantics of the positive counting adapter -/
namespace ContingencyTables.CountingPositiveProgram
open MatchingFPRAS CompanionFactorialApplication CompanionComputedProposal GridBoundary
open scoped Classical
noncomputable section
variable {m n : ℕ}

theorem prepared_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    let A := ComputedCountingParameters.data hEK r c b hne epsilon he
    let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
    prepared ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      CompanionUniformPhaseWidth.data A s
        (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
        (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he)) := by
  exact CountingAdaptiveInputProgram.prepared_data hEK r c b hne epsilon he []

theorem phaseCount_data (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon : ℚ) (he : 0 < epsilon)
    (delta : TreeFraction.Fraction) :
    phaseCount ((NetworkVertexCode.data r c b,TreeFraction.repr epsilon),delta)=
      (ComputedCountingParameters.settings hEK r c b hne epsilon he).H := by
  unfold phaseCount
  rw [prepared_data hEK r c b hne epsilon he delta]
  rfl

end
end ContingencyTables.CountingPositiveProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPositiveWordBound
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Public polynomial bounds for the executed positive counting words -/
namespace ContingencyTables.CountingPositiveWordBound
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionFactorialApplication CountingPublicInputBounds Polynomial
open scoped Classical
noncomputable section
variable {m n : ℕ}

private lemma control_parts (S : ℕ) :
    let M := CountingPublicWordBound.controlPolynomial.eval S
    CountingPublicControls.inputPolynomial.eval S ≤ M ∧
    CountingPublicControls.observationPolynomial.eval S ≤ M ∧
    CountingPublicControls.returnPolynomial.eval S ≤ M ∧
    CountingPublicControls.precisionPolynomial.eval S ≤ M ∧
    CountingTerminalBounds.gridPolynomial.eval S ≤ M ∧
    2048*(CountingTerminalBounds.phasePolynomial.eval S+1) ≤ M ∧ S ≤ M := by
  simp only [CountingPublicWordBound.controlPolynomial,eval_add,eval_mul,eval_ofNat,eval_one,eval_X]
  omega

lemma phaseCount_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    CountingPositiveProgram.phaseCount (CountingDirectProgram.request r c b epsilon delta) ≤
      CountingPublicWordBound.controlPolynomial.eval (size r c b epsilon delta) := by
  rw [CountingDirectProgram.request,CountingPositiveProgram.phaseCount_data hEK r c b hne epsilon he]
  change ComputedCountingParameters.phases r c b epsilon ≤ _
  have hs := CountingPublicControls.scalar_bound hEK r c b hne epsilon delta he
  exact (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans
    (control_parts (size r c b epsilon delta)).1

lemma measure_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    CompanionUniformPhaseWidth.measure
      (CountingPositiveProgram.prepared (CountingDirectProgram.request r c b epsilon delta)) ≤
      measurePolynomial.eval (size r c b epsilon delta) := by
  let A := ComputedCountingParameters.data hEK r c b hne epsilon he
  let s := ComputedCountingParameters.settings hEK r c b hne epsilon he
  let S := size r c b epsilon delta
  let M := CountingPublicWordBound.controlPolynomial.eval S
  have hparts := control_parts S
  have hs : ∀ x∈[Fintype.card (Labels A),A.W,s.H,
      CompanionTargetMixing.restartTime A s.H s.L,s.L],
      x ≤ CountingPublicControls.inputPolynomial.eval S :=
    CountingPublicControls.scalar_bound hEK r c b hne epsilon delta he
  have hp : Fintype.card (Labels A) ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or])).trans hparts.1
  have hW : A.W ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hH : s.H ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hT : CompanionTargetMixing.restartTime A s.H s.L ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hL : s.L ≤ M :=
    (hs _ (by simp only [List.mem_cons,eq_self,true_or,or_true])).trans hparts.1
  have hc := CountingPublicControls.settings_bounds hEK r c b hne epsilon delta he
  have hN : s.N ≤ M := hc.1.trans hparts.2.1
  have hn : s.n ≤ M := hc.2.1.trans hparts.2.2.1
  have hk : s.k ≤ M := hc.2.2.trans hparts.2.2.2.1
  have ht := CountingPublicTerminalBounds.terminal_public hEK r c b hne epsilon delta he
  have hK : s.K ≤ M := ht.1.trans hparts.2.2.2.2.1
  have hh : s.h ≤ M :=
    (Nat.mul_le_mul_left 2048 (Nat.add_le_add_right ht.2.2 1)).trans hparts.2.2.2.2.2.1
  have hd : A.d ≤ M := (dimension_le r c b epsilon delta).trans hparts.2.2.2.2.2.2
  have hheight : CompanionOracleDensity.rationalHeight A s.C ≤ M := hH
  have hkdata := CountingComputedSettings.precision_data hEK r c b hne epsilon he
  rw [CountingComputedSettings.parameters_data hEK r c b hne epsilon he] at hkdata
  have hf := CompanionUniformPhaseWidth.fields_data A s
    (CountingBaseProgram.half (TreeFraction.repr epsilon)) (fun _ => 0)
    (CountingPreparedState.start A s.K (ComputedCountingParameters.binCount_pos r c b epsilon he))
    hkdata (show s.h=CountingPhaseSchedule.initialPrecision s.H from rfl)
  rw [CountingDirectProgram.request,CountingPositiveProgram.prepared_data hEK r c b hne epsilon he]
  unfold CompanionUniformPhaseWidth.measure
  rw [hf]
  simp only [List.sum_cons,List.sum_nil,measurePolynomial,eval_add,eval_mul,eval_ofNat,eval_one]
  dsimp only [M,S] at hp hW hH hT hL hN hn hk hK hh hd hheight
  omega

lemma width_value (req : CountingDirectProgram.Request) :
    CountingPositiveProgram.phaseWidth req=widthPolynomial.eval
      (CompanionUniformPhaseWidth.measure (CountingPositiveProgram.prepared req)) := by
  simp only [CountingPositiveProgram.phaseWidth,CompanionUniformPhaseWidth.width_value,
    widthPolynomial,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]

theorem single_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ) (he : 0 < epsilon) :
    CountingPositiveProgram.bitCount (CountingDirectProgram.request r c b epsilon delta) ≤
      singlePolynomial.eval (size r c b epsilon delta) := by
  have hH := phaseCount_public hEK r c b hne epsilon delta he
  have hM := measure_public hEK r c b hne epsilon delta he
  have hW := polynomial_eval_monotone widthPolynomial hM
  dsimp only at hW
  rw [←width_value] at hW
  simpa only [CountingPositiveProgram.bitCount,singlePolynomial,eval_mul,eval_comp] using
    Nat.mul_le_mul hH hW

theorem amplified_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (hne : ∃ X,TableTightening.Feasible r c b X) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount
      (CountingDirectProgram.request r c b epsilon delta) ≤
      amplifiedPolynomial.eval (size r c b epsilon delta) :=
  CountingAmplifiedProgram.budget_bound CountingPositiveProgram.bitCount singlePolynomial
    r c b epsilon delta hd (single_public hEK r c b hne epsilon delta he)

theorem branch_public (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1)
    (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
    (epsilon delta : ℚ) (he : 0 < epsilon) (hd : 0 < delta) :
    CountingBranchProgram.publicBudget
      (CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount)
      (Algorithms.encodeCountingInput r c b epsilon delta) ≤
      (CountingBranchProgram.budgetPolynomial amplifiedPolynomial).eval
        (size r c b epsilon delta) := by
  exact CountingBranchProgram.publicBudget_bound hEK
    (CountingAmplifiedProgram.budget CountingPositiveProgram.bitCount) amplifiedPolynomial
    (fun _ _ r c b hne epsilon delta he hd => amplified_public hEK r c b hne epsilon delta he hd)
    m n r c b epsilon delta he hd

end
end ContingencyTables.CountingPositiveWordBound

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingExecutedMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One fixed counting machine with the computed adaptive program -/
namespace ContingencyTables.CountingExecutedMachine
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open scoped Classical
noncomputable section

lemma polynomial_positiveWidth : PolynomialTime positiveWidthRealizer :=
  CountingAmplifiedProgram.polynomial_budget CountingPositiveProgram.bitCount
    CountingPositiveProgram.bitCountRealizer CountingPositiveProgram.polynomial_bitCount

theorem public_time_oai (hEK : PublishedEdmondsKarp.EdmondsKarp1972Theorem1) :
    ∃ C d : ℕ,0<C ∧ ∀ (m n : ℕ) (r : Fin m→ℕ) (c : Fin n→ℕ) (b : Fin m→Fin n→ℕ)
      (epsilon delta : ℚ),0<epsilon→0<delta→
      machineTime (Algorithms.encodeCountingInput r c b epsilon delta) ≤
        Algorithms.countingTime C d r c b epsilon delta := by
  exact CountingMachineTime.public_bound
    (CountingBranchProgram.publicBudgetRealizer positiveWidth positiveWidthRealizer)
    (CountingBranchProgram.publicOutputRealizer positive positiveRealizer)
    (CountingBranchProgram.polynomial_publicBudget positiveWidth positiveWidthRealizer polynomial_positiveWidth)
    (CountingBranchProgram.polynomial_publicOutput positive positiveRealizer polynomial_positive)
    (CountingBranchProgram.budgetPolynomial CountingPositiveWordBound.amplifiedPolynomial)
    (CountingPositiveWordBound.branch_public hEK)

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.CountingExecutedMachine.public_time_oai := @OAI.ContingencyTables.CountingExecutedMachine.public_time_oai
