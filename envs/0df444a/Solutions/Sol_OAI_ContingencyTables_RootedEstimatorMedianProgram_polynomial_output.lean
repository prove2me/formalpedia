-- Prove2me | solution 1 for OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:14:17.240449+00:00
-- url     : https://prove2.me/submissions/a008a440-3c00-44d7-96ec-c9b7779cfaef

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A006
import Definitions.Def_OAIQ089A010

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

lemma normalize_size_num (x : Fraction) : (normalize x).1.size≤x.1.size := by
  unfold normalize; split_ifs
  · simp
  · exact Nat.size_le_size (Nat.div_le_self _ _)
lemma normalize_size_den (x : Fraction) : (normalize x).2.size≤x.2.size+1 := by
  unfold normalize; split_ifs
  · simp
  · exact (Nat.size_le_size (Nat.div_le_self _ _)).trans (Nat.le_succ _)

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
lemma polynomial_add : PolynomialTime addRealizer := by
  unfold addRealizer
  apply polynomial_composition _ polynomial_normalize
  apply polynomial_pair
  · apply polynomial_composition _ TreeTyped.polynomial_add
    exact polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)
      (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) (polynomial_snd polynomial_first)) polynomial_multiply)
  · exact polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply
lemma polynomial_div : PolynomialTime divRealizer := by
  unfold divRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_fst polynomial_second)) polynomial_multiply)) polynomial_normalize
lemma polynomial_less : PolynomialTime lessRealizer := by
  unfold lessRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) (polynomial_snd polynomial_first)) polynomial_multiply)) TreeTyped.polynomial_less
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
lemma work_then_polynomial {f : A → B} {g : B → C} {F : Realizer f} {G : Realizer g}
    {measure : A → ℕ} (hF : WorkBound F measure) (hG : PolynomialTime G) :
    WorkBound (composition F G) measure := by
  obtain ⟨p,hp⟩:=hF
  exact work_composition ⟨p,hp⟩ hG p (fun a=>Nat.le_trans (Nat.le_add_left _ _) (hp a))

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
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeFractionCosts
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

lemma height_le_weight (x : Fraction) : height x≤weight x := by
  rcases x with ⟨a,b⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  simp only [height,weight_prod]
  exact max_le (by omega) (by omega)
lemma weight_le_height (x : Fraction) : weight x≤8*height x+3 := by
  rcases x with ⟨a,b⟩
  have ha:=weight_nat_le a
  have hb:=weight_nat_le b
  have h1:=le_max_left a.size b.size
  have h2:=le_max_right a.size b.size
  simp only [height,weight_prod]
  omega
lemma height_add (a b : Fraction) : height (add (a,b))≤height a+height b+2 := by
  have hn:=normalize_size_num (a.1*b.2+b.1*a.2,a.2*b.2)
  have hd:=normalize_size_den (a.1*b.2+b.1*a.2,a.2*b.2)
  have hs:=nat_size_add (a.1*b.2) (b.1*a.2)
  have hm:=nat_size_mul a.1 b.2
  have hm':=nat_size_mul b.1 a.2
  have hm'':=nat_size_mul a.2 b.2
  have ha:=le_max_left a.1.size a.2.size
  have ha':=le_max_right a.1.size a.2.size
  have hb:=le_max_left b.1.size b.2.size
  have hb':=le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (add (a,b)).1.size≤_ at hn
  change (add (a,b)).2.size≤_ at hd
  unfold height
  apply max_le <;> omega
lemma fractionFold_height (xs : List Fraction) (a : Fraction) (M : ℕ)
    (hx : ∀ b∈xs,height b≤M) :
    height (xs.foldl (fun a b=>add (b,a)) a)≤height a+xs.length*(M+2) := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hh:=height_add b a
    have hb:=hx b (by simp)
    have ht:=ih (add (b,a)) (fun c h=>hx c (by simp [h]))
    simp only [List.foldl_cons,List.length_cons]
    nlinarith
lemma polynomial_fractionFold : PolynomialTime (fold addRealizer) := by
  apply polynomial_fold polynomial_add (8*X+8*X*(X+2)+3)
  intro xs a pre post he
  let S:=weight (xs,a)
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (xs,a)))
  have hb : ∀ b∈pre,height b≤S := by
    intro b hb
    exact (height_le_weight b).trans ((weight_mem (as:=xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have ha : height a≤S := (height_le_weight a).trans (weight_snd (xs,a))
  have hh:=fractionFold_height pre a S hb
  have hw:=weight_le_height (pre.foldl (fun a b=>add (b,a)) a)
  have hm:=Nat.mul_le_mul_right (S+2) hpre
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤8*S+8*S*(S+2)+3
  nlinarith
lemma polynomial_sum : PolynomialTime sumRealizer := by
  unfold sumRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_fractionFold
end MatchingFPRAS.TreeFraction

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
lemma polynomial_bitValue : PolynomialTime bitValue := by
  unfold bitValue
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_pair polynomial_reverse
    (polynomial_constant (1,0))) polynomial_mulFold) polynomial_second
omit [Codec A] in
lemma polynomial_bitDenominator : PolynomialTime bitDenominatorRealizer := by
  unfold bitDenominatorRealizer
  apply polynomial_congr
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1))
  apply polynomial_fold (polynomial_composition polynomial_second polynomial_double) (4*X+8*X+1)
  intro bs n pre post he
  have hfold : ∀ z,(pre.foldl (fun a (_ : Bool)=>2*a) z).size≤z.size+pre.length*2 := by
    clear he
    induction pre with
    | nil => intro z; simp
    | cons b pre ih =>
      intro z
      have hh:=nat_size_mul 2 z
      have ht:=ih (2*z)
      simp only [List.foldl_cons,List.length_cons]
      have h2 : Nat.size 2=2 := by decide
      omega
  let S:=weight (bs,n)
  have hn : n.size≤S := (size_le_weight n).trans (weight_snd (bs,n))
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (bs,n)))
  have hw:=weight_nat_le (pre.foldl (fun a (_ : Bool)=>2*a) n)
  have hh:=hfold n
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change weight (pre.foldl (fun a (_ : Bool)=>2*a) n)≤4*S+8*S+1
  omega
omit [Codec A] in
lemma polynomial_minimum : PolynomialTime minimum := by
  unfold minimum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileExchangeProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary list program for a small-profile unit exchange -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_exchangeEntry : PolynomialTime exchangeEntryRealizer := by
  have hV : PolynomialTime (composition
      (first (A := ExchangeInput) (B := ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hA : PolynomialTime (second (A := ExchangeInput) (B := ℕ)) := polynomial_second
  have hI : PolynomialTime (composition
      (composition (first (A := ExchangeInput) (B := ℕ)) second) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first
  have hJ : PolynomialTime (composition
      (composition (first (A := ExchangeInput) (B := ℕ)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second
  have hi := polynomial_choose (polynomial_composition (polynomial_pair hA hI) polynomial_natEqual)
    (polynomial_constant 1) (polynomial_constant 0)
  have hj := polynomial_choose (polynomial_composition (polynomial_pair hA hJ) polynomial_natEqual)
    (polynomial_constant 1) (polynomial_constant 0)
  unfold exchangeEntryRealizer
  exact polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair hV hA) (polynomial_getDFast 0)) hi) polynomial_add) hj)
    polynomial_subtract)

/-- Its loop traverses the input profile once, even if the supplied
coordinate indices are much larger than its length. -/
theorem polynomial_listExchange : PolynomialTime listExchangeRealizer := by
  have hr : PolynomialTime (composition
      (composition (first (A := List ℕ) (B := ℕ×ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    intro z
    simp only [Polynomial.eval_X]
    exact (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_mapWith polynomial_exchangeEntry)

lemma listExchange_length (z : ExchangeInput) : (listExchange z).length=z.1.length := by
  simp only [listExchange,List.length_map,List.length_range]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded binary coordinate moves in the dense grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

/-- An invalid or boundary move terminates immediately. Its index is
never used as an iteration count. -/
theorem polynomial_axisListStep : PolynomialTime axisListStepRealizer := by
  have hK : PolynomialTime (composition
      (composition (first (A := (ℕ×List ℕ)×ℕ) (B := Bool)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first
  have hX : PolynomialTime (composition
      (composition (first (A := (ℕ×List ℕ)×ℕ) (B := Bool)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have hI : PolynomialTime (composition
      (first (A := (ℕ×List ℕ)×ℕ) (B := Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hL := polynomial_composition hX polynomial_listLength
  have hV := polynomial_composition (polynomial_pair hX hI) (polynomial_getDFast 0)
  have hup := polynomial_composition (polynomial_composition
    (polynomial_pair hX (polynomial_pair hI hL)) polynomial_listExchange) polynomial_some
  have hdown := polynomial_composition (polynomial_composition
    (polynomial_pair hX (polynomial_pair hL hI)) polynomial_listExchange) polynomial_some
  unfold axisListStepRealizer
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair hI hL) polynomial_less)
    (polynomial_choose polynomial_second
      (polynomial_choose (polynomial_composition (polynomial_pair
        (polynomial_composition hV polynomial_successor) hK) polynomial_less)
        hup (polynomial_constant none))
      (polynomial_choose (polynomial_composition (polynomial_pair (polynomial_constant 0) hV)
        polynomial_less) hdown (polynomial_constant none))) (polynomial_constant none))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseAxisWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary-word decoding for a dense coordinate proposal -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

theorem polynomial_axisWordStep : PolynomialTime axisWordStepRealizer := by
  have hv : PolynomialTime (composition
      (second (A := ℕ×List ℕ) (B := List Bool)) bitValue) :=
    polynomial_composition polynomial_second polynomial_bitValue
  have hi := polynomial_composition (polynomial_pair hv (polynomial_constant 2)) polynomial_quotient
  have hs := polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair hv (polynomial_constant 2)) polynomial_remainder)
    (polynomial_constant 1)) polynomial_natEqual
  unfold axisWordStepRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_first hi) hs)
    polynomial_axisListStep

end ContingencyTables.DensePrograms

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
lemma polynomial_listProd : PolynomialTime listProd := by
  unfold listProd
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1))
    (polynomial_nat_fold polynomial_multiply 0 (fun a b=>by simpa using nat_size_mul a b))

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary evaluation of the finite Metropolis coin -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

theorem polynomial_dyadicWordAccept : PolynomialTime dyadicWordAcceptRealizer := by
  have hn : PolynomialTime (composition
      (pair (composition (first (A := List Bool) (B := ℕ)) listLength) second) subtract) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength) polynomial_second)
      polynomial_subtract
  have hb := polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_first hn) polynomial_takeFast) polynomial_bitDenominator
  unfold dyadicWordAcceptRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_bitValue) hb) polynomial_less)

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseStepGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary size bounds for repeated dense steps on arbitrary input -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

lemma getD_size_bound (xs : List ℕ) (S i : ℕ)
    (h : ∀ a∈xs,a.size≤S) : (xs.getD i 0).size≤S := by
  by_cases hi : i<xs.length
  · rw [List.getD_eq_getElem xs 0 hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default xs 0 (Nat.le_of_not_gt hi)]
    simp

lemma listExchange_size_bound (xs : List ℕ) (i j S : ℕ)
    (h : ∀ a∈xs,a.size≤S) :
    ∀ a∈listExchange (xs,(i,j)),a.size≤S+2 := by
  intro a ha
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
  have hv := getD_size_bound xs S k h
  have ha : (if k=i then 1 else 0).size≤1 := by split_ifs <;> decide
  have hb := nat_size_add (xs.getD k 0) (if k=i then 1 else 0)
  have hs := Nat.size_le_size (Nat.sub_le
    (xs.getD k 0+(if k=i then 1 else 0)) (if k=j then 1 else 0))
  change (xs.getD k 0+(if k=i then 1 else 0)-(if k=j then 1 else 0)).size≤S+2
  omega

lemma axisListStep_growth (z : AxisData) (ys : List ℕ) (S : ℕ)
    (h : axisListStep z=some ys) (hx : ∀ a∈z.1.1.2,a.size≤S) :
    ys.length=z.1.1.2.length ∧ ∀ a∈ys,a.size≤S+2 := by
  rcases z with ⟨⟨⟨K,xs⟩,i⟩,sign⟩
  by_cases hi : i<xs.length
  · cases sign with
    | false =>
      by_cases hp : 0<xs.getD i 0
      · have he : listExchange (xs,(xs.length,i))=ys := by
          simpa only [axisListStep,hi,ite_true, if_true,Bool.false_eq_true,ite_false,hp,
            Option.some.injEq] using h
        rw [←he]
        exact ⟨listExchange_length _,listExchange_size_bound _ _ _ _ hx⟩
      · simp only [axisListStep,hi,ite_true, if_true,Bool.false_eq_true,ite_false,hp,
          reduceCtorEq] at h
    | true =>
      by_cases hp : xs.getD i 0+1<K
      · have he : listExchange (xs,(i,xs.length))=ys := by
          simpa only [axisListStep,hi,ite_true, if_true,hp,Option.some.injEq] using h
        rw [←he]
        exact ⟨listExchange_length _,listExchange_size_bound _ _ _ _ hx⟩
      · simp only [axisListStep,hi,ite_true, if_true,hp,ite_false,reduceCtorEq] at h
  · simp only [axisListStep,hi,ite_false,reduceCtorEq] at h

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScaledWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the bounded quotient draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

theorem polynomial_scaledWord : PolynomialTime scaledWordRealizer := by
  unfold scaledWordRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_bitValue)) polynomial_multiply)
    (polynomial_composition polynomial_second polynomial_bitDenominator)) polynomial_quotient)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RationalIntervalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact binary arithmetic for a forest interval penalty

A signed affine numerator is stored as a difference of two naturals.
Its distance outside the interval [0,1] is a nonnegative fraction with
the same denominator; no signed rational comparison is required.
-/

namespace ContingencyTables.RationalIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_numerator : PolynomialTime numeratorRealizer := by
  unfold numeratorRealizer
  have hp := polynomial_composition
    (polynomial_first (A := ℕ×ℕ) (B := ℕ)) polynomial_first
  have hn := polynomial_composition
    (polynomial_first (A := ℕ×ℕ) (B := ℕ)) polynomial_second
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair hn hp) polynomial_subtract)
    (polynomial_composition (polynomial_pair hp
      (polynomial_composition (polynomial_pair hn polynomial_second) polynomial_add))
      polynomial_subtract)) polynomial_add

theorem polynomial_intervalCode : PolynomialTime intervalCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator polynomial_second)
    TreeFraction.polynomial_normalize

end ContingencyTables.RationalIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestAffineProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary list evaluation of the forest's signed affine numerators

Each coefficient is stored by its nonnegative and nonpositive parts.
The program performs two finite product sums and passes their difference
to the proved interval-cost routine. Large capacities are never iterated.
-/

namespace ContingencyTables.ForestAffineProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma polynomial_positiveTerm : PolynomialTime positiveTermRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_multiply

lemma polynomial_negativeTerm : PolynomialTime negativeTermRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_multiply

lemma polynomial_positiveSum : PolynomialTime positiveSumRealizer :=
  polynomial_composition (polynomial_map polynomial_positiveTerm) polynomial_listSum

lemma polynomial_negativeSum : PolynomialTime negativeSumRealizer :=
  polynomial_composition (polynomial_map polynomial_negativeTerm) polynomial_listSum

lemma polynomial_parts : PolynomialTime partsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_positiveSum)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_negativeSum)) polynomial_add)

theorem polynomial_evaluate : PolynomialTime evaluateRealizer :=
  polynomial_composition (polynomial_pair polynomial_parts polynomial_second)
    RationalIntervalProgram.polynomial_intervalCode

end ContingencyTables.ForestAffineProgram

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

lemma polynomial_neg : PolynomialTime negRealizer :=
  polynomial_pair polynomial_second polynomial_first

lemma polynomial_minus : PolynomialTime minusRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_neg)) polynomial_plus

lemma polynomial_times : PolynomialTime timesRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_second polynomial_first)) polynomial_multiply)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition polynomial_second polynomial_first)) polynomial_multiply)) polynomial_add)

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SignedFloorProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary floor of a signed rational

Two natural quotients and the comparison of their remainders compute
the exact floor. No loop depends on the numeric numerator or denominator.
-/

namespace ContingencyTables.SignedFloorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram

lemma polynomial_numeratorQuotient : PolynomialTime numeratorQuotientRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_quotient

lemma polynomial_negativeQuotient : PolynomialTime negativeQuotientRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    polynomial_quotient

lemma polynomial_carry : PolynomialTime carryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_remainder)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_remainder)) polynomial_less

lemma polynomial_carryValue : PolynomialTime carryValueRealizer :=
  polynomial_choose polynomial_carry (polynomial_constant 1) (polynomial_constant 0)

lemma polynomial_raw : PolynomialTime rawRealizer :=
  polynomial_pair polynomial_numeratorQuotient
    (polynomial_composition (polynomial_pair polynomial_negativeQuotient polynomial_carryValue)
      polynomial_add)

theorem polynomial_floorCode : PolynomialTime floorCodeRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0))
      polynomial_natEqual) (polynomial_constant (0,0)) polynomial_raw)

lemma polynomial_scale : PolynomialTime scaleRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first)) polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_listLength)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second)) polynomial_multiply))
    (polynomial_composition polynomial_first polynomial_second)

theorem polynomial_scaledFloor : PolynomialTime scaledFloorRealizer :=
  polynomial_composition polynomial_scale polynomial_floorCode

end ContingencyTables.SignedFloorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinIntervalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary evaluation of a bin interval and its bounded quotient draw

The lower endpoint is computed as the negative floor of a negative
rational. Thus the executed arithmetic uses natural quotient/remainder,
without enumerating any of the integers in the interval.
-/

namespace ContingencyTables.BinIntervalProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped SignedPairProgram ProfilePrograms

lemma polynomial_negativeInput : PolynomialTime negativeInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_constant 0)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply))
    (polynomial_composition polynomial_first polynomial_first)

theorem polynomial_endpoint : PolynomialTime endpointRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_negativeInput SignedFloorProgram.polynomial_floorCode)
    SignedPairProgram.polynomial_normalize) polynomial_second

lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_successor)

theorem polynomial_intervalSize : PolynomialTime intervalSizeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_next polynomial_endpoint) polynomial_endpoint)
    polynomial_subtract

theorem polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_endpoint)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_intervalSize) polynomial_second)
      polynomial_scaledWord)) polynomial_add

end ContingencyTables.BinIntervalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial signed component sums for the executed root labels -/

namespace ContingencyTables.RootedComponentProgram

open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

lemma polynomial_positiveTerm : PolynomialTime positiveTermRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_first) (polynomial_constant 0))

lemma polynomial_negativeTerm : PolynomialTime negativeTermRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_second) (polynomial_constant 0))

lemma polynomial_parts : PolynomialTime partsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_mapWith polynomial_positiveTerm) polynomial_listSum)
    (polynomial_composition (polynomial_mapWith polynomial_negativeTerm) polynomial_listSum)

lemma polynomial_absoluteDifference : PolynomialTime absoluteDifferenceRealizer :=
  polynomial_composition (polynomial_pair polynomial_subtract
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_subtract))
    polynomial_add

lemma polynomial_component : PolynomialTime componentRealizer :=
  polynomial_composition polynomial_parts polynomial_absoluteDifference

theorem polynomial_total : PolynomialTime totalRealizer := by
  have hr : PolynomialTime (composition (listLength (A := Record)) range) := by
    apply polynomial_boundedRange polynomial_listLength X
    intro rs
    simpa only [Polynomial.eval_X] using list_length_le_weight rs
  exact polynomial_composition
    (polynomial_composition (polynomial_pair polynomial_identity hr)
      (polynomial_mapWith (polynomial_composition
        (polynomial_pair polynomial_second polynomial_first) polynomial_component))) polynomial_listSum

end ContingencyTables.RootedComponentProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ForestPenaltyProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact rational assembly of the companion forest penalty

The natural root discrepancy and the finite list of tree affine forms
are combined by polynomial binary arithmetic to compute rationalD,
including the original maximum-forest cuts.
-/

namespace ContingencyTables.ForestPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionFactorialApplication CompanionOracleDensity ForestAssignmentSplit GraphCompletionCounts
open ForestScaledPenalty
open scoped BigOperators Classical

lemma polynomial_treeSum : PolynomialTime treeSumRealizer :=
  polynomial_composition (polynomial_composition polynomial_second
    (polynomial_map ForestAffineProgram.polynomial_evaluate)) TreeFraction.polynomial_sum

lemma polynomial_rootSum : PolynomialTime rootSumRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_constant 1)) polynomial_treeSum) TreeFraction.polynomial_add

theorem polynomial_penaltyCode : PolynomialTime penaltyCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_first) (polynomial_constant 1))
    polynomial_rootSum) TreeFraction.polynomial_mul

lemma polynomial_weightedPenalty : PolynomialTime weightedPenaltyRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_penaltyCode)) TreeFraction.polynomial_mul

theorem polynomial_exponentCode : PolynomialTime exponentCodeRealizer :=
  polynomial_composition polynomial_weightedPenalty polynomial_quotient

end ContingencyTables.ForestPenaltyProgram

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

theorem polynomial_rootCode : PolynomialTime rootCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_reached
    (polynomial_composition polynomial_first polynomial_listLength)) polynomial_minimumFold

end ContingencyTables.FiniteGraphRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedComponentCode
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing every root label before summing its signed demand

The input contains an adjacency list and one positive/negative demand
pair per vertex. The polynomial program computes the root labels itself.
-/

namespace ContingencyTables.RootedComponentCode

open MatchingFPRAS.TreeTyped Polynomial
open RootedCompletion RootedComponentProgram FiniteGraphRootProgram
open scoped BigOperators Classical

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_rootCode)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast (0,0)))

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.2).trans (weight_snd z)

lemma polynomial_labels : PolynomialTime labelsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_entry)

theorem polynomial_count : PolynomialTime countRealizer :=
  polynomial_composition polynomial_labels polynomial_total

open CompanionFactorialApplication

end ContingencyTables.RootedComponentCode

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BooleanChunkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial partition of a supplied Boolean word into fixed-width rows -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_wordChunk : PolynomialTime wordChunkRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply))
      polynomial_dropFast)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_takeFast

theorem polynomial_completeWordRows : PolynomialTime completeWordRowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_listLength) polynomial_first)
      polynomial_quotient) X
  intro z
  simp only [eval_X,Function.comp_apply]
  exact (Nat.div_le_self _ _).trans ((list_length_le_weight _).trans (weight_snd z))

theorem polynomial_wordChunks : PolynomialTime wordChunksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_completeWordRows)
    (polynomial_mapWith polynomial_wordChunk)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DependentWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Splitting a binary word at input-dependent coordinate widths -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_chunkStart : PolynomialTime chunkStartRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_takeFast) polynomial_listSum

theorem polynomial_dependentChunk : PolynomialTime dependentChunkRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_chunkStart)
      polynomial_dropFast)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))) polynomial_takeFast

open scoped BigOperators

end ContingencyTables.DensePrograms

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

lemma polynomial_keep : PolynomialTime keepRealizer := by
  unfold keepRealizer
  have hi : PolynomialTime (composition (first (A := (ℕ×ℕ)×ℕ) (B := ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hu : PolynomialTime (composition
      (composition (first (A := (ℕ×ℕ)×ℕ) (B := ℕ)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first
  have hv : PolynomialTime (composition
      (composition (first (A := (ℕ×ℕ)×ℕ) (B := ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair hi hu) polynomial_natEqual)
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_second hv)
      polynomial_natEqual) polynomial_boolNot)
    (polynomial_choose (polynomial_composition (polynomial_pair hi hv) polynomial_natEqual)
      (polynomial_composition (polynomial_composition (polynomial_pair polynomial_second hu)
        polynomial_natEqual) polynomial_boolNot) (polynomial_constant true)))

lemma polynomial_deleteRow : PolynomialTime deleteRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast []))) (polynomial_filterWith polynomial_keep)

theorem polynomial_deleteGraph : PolynomialTime deleteGraphRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_indices))
    (polynomial_mapWith polynomial_deleteRow)

lemma polynomial_reachableCode : PolynomialTime reachableCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_reached) polynomial_second)
    polynomial_membership

lemma polynomial_awayTest : PolynomialTime awayTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_deleteGraph)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)) polynomial_second) polynomial_reachableCode

lemma polynomial_awayCode : PolynomialTime awayCodeRealizer :=
  polynomial_choose polynomial_awayTest
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first)

theorem polynomial_cutCode : PolynomialTime cutCodeRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_deleteGraph)
    (polynomial_composition polynomial_first polynomial_awayCode)) polynomial_second)
    polynomial_reachableCode

theorem polynomial_canonicalCutCode : PolynomialTime canonicalCutCodeRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)) polynomial_rootCode)) polynomial_second) polynomial_cutCode

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

lemma polynomial_bit : PolynomialTime bitRealizer :=
  polynomial_choose polynomial_identity (polynomial_constant 1) (polynomial_constant 0)

lemma polynomial_signs : PolynomialTime signsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_canonicalCutCode)
      polynomial_bit)
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_second)) polynomial_canonicalCutCode)
      polynomial_bit)

lemma polynomial_treeSigns : PolynomialTime treeSignsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_second) polynomial_signs

lemma polynomial_adjacent : PolynomialTime adjacentRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) polynomial_membership

lemma polynomial_freeTest : PolynomialTime freeTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_leNat)
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_adjacent)
      polynomial_boolNot)) polynomial_boolAnd

lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_choose polynomial_freeTest
    (polynomial_composition (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_signs)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_treeSigns)) polynomial_times) polynomial_neg) polynomial_normalize)
    (polynomial_constant (0,0))

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

end ContingencyTables.RootedCoefficientProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOffsetProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the forest affine offset from the stored cell values

Every summand uses the executed cut flags and coefficient. The input
contains the baseline and the two stored views, rather than an affine
offset supplied by an oracle.
-/

namespace ContingencyTables.RootedOffsetProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped BigOperators Classical

lemma polynomial_weightedDifference : PolynomialTime weightedDifferenceRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
        (polynomial_constant 0))
      (polynomial_composition polynomial_second polynomial_first)) polynomial_times)
    (polynomial_composition (polynomial_pair
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_constant 0))
      (polynomial_composition polynomial_second polynomial_second)) polynomial_times))
    polynomial_minus

lemma polynomial_cellInput : PolynomialTime cellInputRealizer :=
  polynomial_composition polynomial_first polynomial_first

lemma polynomial_shifted : PolynomialTime shiftedRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first) polynomial_second) polynomial_minus)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_second) polynomial_second) polynomial_minus)

lemma polynomial_cutTerm : PolynomialTime cutTermRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_cellInput polynomial_first)
      RootedCoefficientProgram.polynomial_signs) polynomial_shifted) polynomial_weightedDifference

lemma polynomial_smallTest : PolynomialTime smallTestRealizer :=
  polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_cellInput polynomial_second)
      polynomial_leNat) polynomial_boolNot

lemma polynomial_smallTerm : PolynomialTime smallTermRealizer :=
  polynomial_choose polynomial_smallTest polynomial_cutTerm (polynomial_constant (0,0))

lemma polynomial_summand : PolynomialTime summandRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_smallTerm
      (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_cellInput polynomial_first)
          polynomial_first) RootedCoefficientProgram.polynomial_treeSigns)) polynomial_times)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_cellInput RootedCoefficientProgram.polynomial_coefficient)
      polynomial_second) polynomial_times)) polynomial_plus

theorem polynomial_offset : PolynomialTime offsetRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    polynomial_first
    (polynomial_composition (polynomial_composition polynomial_second
      (polynomial_map polynomial_summand)) polynomial_sum)) polynomial_minus) polynomial_normalize

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation

end ContingencyTables.RootedOffsetProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestDataProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing a tree penalty from executed coefficients and offsets

All signed affine data are computed internally from the graph, capacities,
baseline and two stored views. Only ordinary cell indices and values occur
in the input; no affine coefficient or offset is supplied.
-/

namespace ContingencyTables.RootedForestDataProgram

open MatchingFPRAS.TreeTyped SignedPairProgram
open scoped Classical

lemma polynomial_scale : PolynomialTime scaleRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_pair polynomial_first (polynomial_constant 0)) polynomial_second)
    polynomial_times) polynomial_normalize

lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_second) polynomial_successor)
    (polynomial_composition polynomial_first RootedCoefficientProgram.polynomial_coefficient))
    polynomial_scale) polynomial_second

lemma polynomial_numeratorOffset : PolynomialTime numeratorOffsetRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedOffsetProgram.polynomial_offset)) polynomial_scale

theorem polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_numeratorOffset
    (polynomial_composition polynomial_second (polynomial_map polynomial_term)))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_multiply)

open CompanionFactorialApplication RootedCompletion RootedIntegerEvaluation ForestAssignmentSplit

end ContingencyTables.RootedForestDataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCellDataProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Assembling the affine input from ordinary rectangular cell arrays

The baseline and both stored views are binary natural matrices. The
program reads each cell once, computes its row/column vertex indices,
and constructs the offset evaluator input in row-major order.
-/

namespace ContingencyTables.RootedCellDataProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open FiniteGraphRootProgram FiniteGraphCutProgram
open scoped Classical

lemma polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_second) polynomial_matrixEntry)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_second) polynomial_second) polynomial_matrixEntry))
    (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_first) polynomial_second) polynomial_matrixEntry)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_second) polynomial_second) polynomial_matrixEntry))

lemma polynomial_endpoints : PolynomialTime endpointsRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_first)
        polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)

lemma polynomial_cellValues : PolynomialTime cellValuesRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) polynomial_values

lemma polynomial_coefficientInput : PolynomialTime coefficientInputRealizer :=
  polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_endpoints))
    (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_cellValues polynomial_first)
        polynomial_first))

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_pair (polynomial_pair polynomial_coefficientInput
    (polynomial_pair
      (polynomial_pair (polynomial_composition (polynomial_composition polynomial_cellValues
        polynomial_second) polynomial_first) (polynomial_constant 0))
      (polynomial_pair (polynomial_composition (polynomial_composition polynomial_cellValues
        polynomial_second) polynomial_second) (polynomial_constant 0))))
    (polynomial_pair (polynomial_composition (polynomial_composition polynomial_cellValues
      polynomial_first) polynomial_second) (polynomial_constant 0))

lemma polynomial_baselineCell : PolynomialTime baselineCellRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_listLength)) polynomial_subtract)

theorem polynomial_offsetInput : PolynomialTime offsetInputRealizer :=
  polynomial_pair
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
      (polynomial_composition polynomial_first polynomial_baselineCell)) polynomial_matrixEntry)
      (polynomial_constant 0))
    (polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_cellPairs)) (polynomial_mapWith polynomial_entry))

open CompanionFactorialApplication RootedCompletion

end ContingencyTables.RootedCellDataProgram

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedDemandProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the root-demand input from the actual cell arrays

The two natural entries at a vertex encode its signed small-cell
discrepancy. They are formed by rectangular scans and then passed to the
component/root program.
-/

namespace ContingencyTables.RootedDemandProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms SignedPairProgram
open FiniteGraphRootProgram
open scoped BigOperators Classical

lemma polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair
      (polynomial_pair
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first))
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
    polynomial_second) RootedCellDataProgram.polynomial_values

lemma polynomial_retainedTest : PolynomialTime retainedTestRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) RootedForestCatalog.polynomial_largeTest) polynomial_boolNot

lemma polynomial_rowTest : PolynomialTime rowTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual

lemma polynomial_columnTest : PolynomialTime columnTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first
          polynomial_first) polynomial_first) polynomial_first) polynomial_second) polynomial_first)
        polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_add)) polynomial_natEqual

lemma polynomial_rowPair : PolynomialTime rowPairRealizer :=
  polynomial_pair
    (polynomial_composition polynomial_values (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_values (polynomial_composition polynomial_second polynomial_first))

lemma polynomial_columnPair : PolynomialTime columnPairRealizer :=
  polynomial_pair
    (polynomial_composition polynomial_values (polynomial_composition polynomial_second polynomial_second))
    (polynomial_composition polynomial_values (polynomial_composition polynomial_first polynomial_second))

lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_choose polynomial_retainedTest
    (polynomial_composition (polynomial_pair
      (polynomial_choose polynomial_rowTest polynomial_rowPair (polynomial_constant (0,0)))
      (polynomial_choose polynomial_columnTest polynomial_columnPair (polynomial_constant (0,0))))
      polynomial_plus) (polynomial_constant (0,0))

lemma polynomial_demand : PolynomialTime demandRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_cellPairs)) (polynomial_mapWith polynomial_term)) polynomial_sum

lemma polynomial_vertexCount : PolynomialTime vertexCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
      polynomial_listLength)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
      polynomial_listLength)) polynomial_add

lemma polynomial_vertices : PolynomialTime verticesRealizer := by
  apply polynomial_boundedRange polynomial_vertexCount (2*Polynomial.X)
  intro z
  have h₁ : z.1.1.2.1.length≤weight z := (list_length_le_weight _).trans
    ((weight_fst _).trans ((weight_snd _).trans ((weight_fst _).trans (weight_fst _))))
  have h₂ : z.1.1.2.2.length≤weight z := (list_length_le_weight _).trans
    ((weight_snd _).trans ((weight_snd _).trans ((weight_fst _).trans (weight_fst _))))
  simp only [vertexCount,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

lemma polynomial_demandList : PolynomialTime demandListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_vertices)
    (polynomial_mapWith polynomial_demand)

theorem polynomial_rootCount : PolynomialTime rootCountRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first
      polynomial_first) polynomial_first) polynomial_first) polynomial_demandList)
    RootedComponentCode.polynomial_count

open CompanionFactorialApplication RootedCompletion

end ContingencyTables.RootedDemandProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedTreeInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Building tree-local inputs from the common raw arrays

The graph, capacity array, baseline and stored views are shared across
all tree terms. A term uses only its pair of cell indices; the program
builds its offset frame and reads the free-grid coordinates in catalog
order.
-/

namespace ContingencyTables.RootedTreeInputProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

lemma polynomial_metadata : PolynomialTime metadataRealizer :=
  polynomial_composition polynomial_first polynomial_first

lemma polynomial_edge : PolynomialTime edgeRealizer :=
  polynomial_composition (polynomial_pair polynomial_metadata polynomial_second)
    RootedForestCatalog.polynomial_edge

theorem polynomial_treeInput : PolynomialTime treeInputRealizer :=
  polynomial_pair
    (polynomial_pair (polynomial_pair polynomial_edge
      (polynomial_composition polynomial_metadata (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)))
      (polynomial_composition polynomial_metadata (polynomial_composition polynomial_first polynomial_second)))
    (polynomial_pair (polynomial_pair (polynomial_composition polynomial_metadata polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))

lemma polynomial_termAt : PolynomialTime termAtRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_second) (polynomial_getDFast (0,0))))
      RootedCellDataProgram.polynomial_coefficientInput)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_second) (polynomial_getDFast 0))

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength Polynomial.X
  intro xs
  simpa only [Polynomial.eval_X] using list_length_le_weight xs

theorem polynomial_terms : PolynomialTime termsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_indices)) (polynomial_mapWith polynomial_termAt)

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedTreeInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedForestPrepareProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the whole selected-root forest penalty

The program takes the four cell arrays and the graph. It computes the
root discrepancy, both catalogs, every cut coefficient and every affine
offset before invoking the rational penalty evaluator.
-/

namespace ContingencyTables.RootedForestPrepareProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

lemma polynomial_treeFrame : PolynomialTime treeFrameRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_second) RootedTreeInputProgram.polynomial_treeInput

lemma polynomial_freeCells : PolynomialTime freeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_first) (polynomial_constant false)) RootedForestCatalog.polynomial_catalog

lemma polynomial_widthCapacity : PolynomialTime widthCapacityRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_first) polynomial_second) polynomial_second) polynomial_matrixEntry)

lemma polynomial_forestInput : PolynomialTime forestInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_widthCapacity
    (polynomial_composition polynomial_treeFrame RootedCellDataProgram.polynomial_offsetInput))
    (polynomial_composition (polynomial_pair
      (polynomial_pair polynomial_treeFrame polynomial_freeCells)
      (polynomial_composition polynomial_first polynomial_second))
      RootedTreeInputProgram.polynomial_terms)

lemma polynomial_prepareTree : PolynomialTime prepareTreeRealizer :=
  polynomial_composition polynomial_forestInput RootedForestDataProgram.polynomial_prepare

lemma polynomial_treeBundle : PolynomialTime treeBundleRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)) polynomial_second

lemma polynomial_treeCells : PolynomialTime treeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first) (polynomial_constant true)) RootedForestCatalog.polynomial_catalog

lemma polynomial_prepareTrees : PolynomialTime prepareTreesRealizer :=
  polynomial_composition (polynomial_pair polynomial_treeBundle polynomial_treeCells)
    (polynomial_mapWith polynomial_prepareTree)

theorem polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedDemandProgram.polynomial_rootCount)) polynomial_prepareTrees

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedForestPrepareProgram

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

lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 16) polynomial_scaledSquare)
    polynomial_multiply

lemma polynomial_baseHeight : PolynomialTime baseHeightRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 10) polynomial_scaledSquare)
    polynomial_multiply

lemma polynomial_height : PolynomialTime heightRealizer :=
  polynomial_composition (polynomial_pair polynomial_baseHeight
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_successor)) polynomial_multiply

lemma polynomial_forestInput : PolynomialTime forestInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_first)
    (polynomial_composition polynomial_first polynomial_width))
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

lemma polynomial_exponentInput : PolynomialTime exponentInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_second) (polynomial_composition polynomial_first polynomial_height))
    (polynomial_composition polynomial_forestInput RootedForestPrepareProgram.polynomial_prepare)

theorem polynomial_evaluate : PolynomialTime evaluateRealizer :=
  polynomial_composition polynomial_exponentInput ForestPenaltyProgram.polynomial_exponentCode

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedPenaltyEvaluateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinPopulationProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact population correction in binary

The program multiplies one interval size and one full-range denominator
per free coordinate. It never lists the integer assignments in a bin.
-/

namespace ContingencyTables.BinPopulationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma polynomial_factorNumerator : PolynomialTime factorNumeratorRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    BinIntervalProgram.polynomial_intervalSize) polynomial_multiply

lemma polynomial_numerator : PolynomialTime numeratorRealizer :=
  polynomial_composition (polynomial_map polynomial_factorNumerator) polynomial_listProd

lemma polynomial_denominator : PolynomialTime denominatorRealizer :=
  polynomial_composition (polynomial_map
    (polynomial_composition polynomial_first polynomial_second)) polynomial_listProd

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator polynomial_denominator)
    TreeFraction.polynomial_normalize

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

end ContingencyTables.BinPopulationProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinVectorProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed independent bin-coordinate draws

Each coordinate reserves a width determined by its full range, and
uses only the prefix needed by the selected interval. The implementation
splits one Boolean list and performs binary arithmetic per coordinate.
-/

namespace ContingencyTables.BinVectorProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators

lemma polynomial_reservedWidth : PolynomialTime reservedWidthRealizer := by
  unfold reservedWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_successor) polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 4)
      (polynomial_composition polynomial_second polynomial_add)) polynomial_multiply)) polynomial_add

lemma polynomial_activeWidth : PolynomialTime activeWidthRealizer := by
  unfold activeWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first BinIntervalProgram.polynomial_intervalSize)
      polynomial_successor) polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 4)
      (polynomial_composition polynomial_second polynomial_add)) polynomial_multiply)) polynomial_add

lemma polynomial_coordinate : PolynomialTime coordinateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_activeWidth)) polynomial_takeFast))
    BinIntervalProgram.polynomial_draw

lemma polynomial_widths : PolynomialTime widthsRealizer :=
  polynomial_composition polynomial_first (polynomial_map polynomial_reservedWidth)

lemma polynomial_item : PolynomialTime itemRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) (polynomial_getDFast (((0,0),0),(0,0))))
    (polynomial_composition (polynomial_pair (polynomial_pair
      (polynomial_composition polynomial_first polynomial_widths)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
      polynomial_dependentChunk)) polynomial_coordinate

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
    Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_item)

end ContingencyTables.BinVectorProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_IntegerMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_multiply

lemma polynomial_dot : PolynomialTime dotRealizer := by
  unfold dotRealizer
  apply polynomial_composition
  · apply polynomial_pair polynomial_identity
    exact polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
      Polynomial.X (fun z => by
        simpa using (list_length_le_weight z.1).trans (weight_fst z))
  · exact polynomial_composition (polynomial_mapWith polynomial_entry) polynomial_listSum

lemma polynomial_propagate : PolynomialTime propagateRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_dot)

lemma polynomial_step : PolynomialTime stepRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_propagate)

lemma dot_nil (b : List ℕ) : dot ([],b)=0 := by simp [dot]

lemma dot_cons (a : ℕ) (v b : List ℕ) :
    dot (a::v,b)=a*b.headD 0+dot (v,b.tail) := by
  have hzero : b.getD 0 0=b.headD 0 := by cases b <;> rfl
  simp only [dot,List.length_cons,List.sum_range_succ',List.getD_cons_zero]
  rw [hzero]
  congr 1
  congr 1
  apply List.map_congr_left
  intro i _
  cases b <;> simp

lemma dot_le (v b : List ℕ) : dot (v,b) ≤ v.sum*b.sum := by
  induction v generalizing b with
  | nil => simp [dot_nil]
  | cons a v ih =>
    rw [dot_cons]
    cases b with
    | nil => simpa using ih []
    | cons b bs =>
      have hb:=ih bs
      simp only [List.headD_cons,List.tail_cons,List.sum_cons]
      nlinarith [Nat.zero_le (a*bs.sum),Nat.zero_le (v.sum*b)]

lemma propagate_sum_le (B : List (List ℕ)) (v : List ℕ) :
    (propagate (B,v)).sum ≤ v.sum*matrixTotal B := by
  induction B with
  | nil => simp [propagate,matrixTotal]
  | cons b B ih =>
    have hb:=dot_le v b
    simp only [propagate,List.map_cons,List.sum_cons,matrixTotal] at *
    nlinarith

lemma sum_size_le_weight (v : List ℕ) : v.sum.size ≤ weight v := by
  induction v with
  | nil => simp
  | cons a v ih =>
    have ha:=size_le_weight a
    have hs:=nat_size_add a v.sum
    rw [List.sum_cons,weight_cons]
    have hm : max a.size v.sum.size ≤ weight a+weight v := max_le (by omega) (by omega)
    omega

lemma matrixTotal_size_le_weight (B : List (List ℕ)) : (matrixTotal B).size ≤ weight B := by
  induction B with
  | nil => simp [matrixTotal]
  | cons b B ih =>
    have hb:=sum_size_le_weight b
    have hs:=nat_size_add b.sum (matrixTotal B)
    change (b.sum+matrixTotal B).size ≤ weight (b::B)
    rw [weight_cons]
    have hm : max b.sum.size (matrixTotal B).size ≤ weight b+weight B :=
      max_le (by omega) (by omega)
    omega

lemma pow_size_le (a N : ℕ) : (a^N).size ≤ 1+N*a.size := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hs:=nat_size_mul (a^N) a
    rw [pow_succ]
    nlinarith

lemma weight_of_entry_bound (v : List ℕ) (M : ℕ) (h : ∀ a∈v,a.size ≤ M) :
    weight v ≤ v.length*(4*M+2)+1 := by
  have hw:=weight_map_bound (as := v) (f := id) (N := 4*M+1) (by
    intro a ha
    have hs:=h a ha
    have hw:=weight_nat_le a
    simpa using (show weight a ≤ 4*M+1 by omega))
  simpa using hw

/-- The iteration bound uses the number of steps and the binary input size.
The numerical values of the matrix entries never control a loop. -/
theorem work_iterate : WorkBound iterateRealizer
    (fun z => z.1+weight z.2) := by
  unfold iterateRealizer
  apply work_then_polynomial _ polynomial_second
  apply work_boundedRepeat
    (work_of_polynomial polynomial_identity (5*Polynomial.X+3) (by
      intro z
      have hn:=weight_nat_numeric z.1
      rw [←Prod.eta z,weight_prod]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X]
      omega)) polynomial_step Polynomial.X
    (2+Polynomial.X+Polynomial.X*(4*(Polynomial.X+1+Polynomial.X*(Polynomial.X+2))+2))
    (fun z k state => state.1=z.2.1 ∧ state.2.length ≤ z.1+weight z.2 ∧
      state.2.sum ≤ z.2.2.sum*(matrixTotal z.2.1+1)^(z.1-k))
  · intro z
    simp
  · intro z
    refine ⟨rfl,?_,?_⟩
    · have hv:=weight_snd z.2
      exact (list_length_le_weight z.2.2).trans (by omega)
    · simp
  · intro z k hk state hs
    change k<z.1 at hk
    rcases hs with ⟨hB,hlen,hsum⟩
    change state.1=z.2.1 ∧ (propagate state).length ≤ _ ∧ _
    refine ⟨hB,?_,?_⟩
    · simp only [propagate,List.length_map,hB]
      have hB:=weight_fst z.2
      exact (list_length_le_weight z.2.1).trans (by omega)
    · have hp:=propagate_sum_le state.1 state.2
      have hm : matrixTotal state.1  ≤  matrixTotal z.2.1+1 := by rw [hB]; omega
      have hb:=Nat.mul_le_mul hsum hm
      have he : z.1-k=(z.1-(k+1))+1 := by omega
      calc
        (propagate state).sum ≤ state.2.sum*matrixTotal state.1 := hp
        _ ≤ (z.2.2.sum*(matrixTotal z.2.1+1)^(z.1-(k+1)))*(matrixTotal z.2.1+1) := hb
        _=z.2.2.sum*(matrixTotal z.2.1+1)^(z.1-k) := by rw [he,pow_succ]; ac_rfl
  · intro z k state hs
    rcases hs with ⟨hB,hlen,hsum⟩
    let S:=z.1+weight z.2
    change state.2.length ≤ S at hlen
    have hN : z.1-k ≤ S := by dsimp [S]; omega
    have hBweight : weight z.2.1 ≤ S := (weight_fst z.2).trans (by dsimp [S]; omega)
    have hvweight : weight z.2.2 ≤ S := (weight_snd z.2).trans (by dsimp [S]; omega)
    have hQ : (matrixTotal z.2.1+1).size ≤ S+2 := by
      have hm:=matrixTotal_size_le_weight z.2.1
      have ha:=nat_size_add (matrixTotal z.2.1) 1
      norm_num at ha
      have hh : max (matrixTotal z.2.1).size 1 ≤ S+1 := max_le (by omega) (by omega)
      omega
    have hv : z.2.2.sum.size ≤ S := (sum_size_le_weight z.2.2).trans hvweight
    have hsbit : state.2.sum.size ≤ S+1+S*(S+2) := by
      have hm:=Nat.size_le_size hsum
      have hm':=nat_size_mul z.2.2.sum ((matrixTotal z.2.1+1)^(z.1-k))
      have hp:=pow_size_le (matrixTotal z.2.1+1) (z.1-k)
      have hn:=Nat.mul_le_mul hN hQ
      omega
    have ha : ∀ a∈state.2,a.size ≤ S+1+S*(S+2) := by
      intro a ha
      exact (Nat.size_le_size (List.single_le_sum (fun _ _ => Nat.zero_le _) _ ha)).trans hsbit
    have hw:=weight_of_entry_bound state.2 (S+1+S*(S+2)) ha
    have hm:=Nat.mul_le_mul_right (4*(S+1+S*(S+2))+2) hlen
    change weight state ≤ _
    rw [←Prod.eta state,weight_prod,hB]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    change 1+weight z.2.1+weight state.2 ≤ 2+S+S*(4*(S+1+S*(S+2))+2)
    omega

end ContingencyTables.IntegerMatrixPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryPowerProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary powers with a polynomial bound in the exponent and input bits -/

namespace ContingencyTables.BinaryPowerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma polynomial_singleton {A : Type} [Codec A] : PolynomialTime (singleton (A := A)) :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
    polynomial_listCons

lemma polynomial_setup : PolynomialTime setupRealizer :=
  polynomial_pair polynomial_second (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_singleton)
      polynomial_singleton) (polynomial_constant [1]))

/-- Multiplication uses binary operands; only the exponent controls the
number of iterations. This is sufficient for the dyadic tabulation. -/
theorem work_power : WorkBound powerRealizer (fun z => z.2+weight z.1) := by
  unfold powerRealizer
  apply work_then_polynomial _ (polynomial_head 0)
  apply work_composition
    (work_of_polynomial polynomial_setup (5*Polynomial.X+3) (by
      intro z
      have hn:=weight_nat_numeric z.2
      rw [←Prod.eta z,weight_prod]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X]
      omega)) IntegerMatrixPrograms.work_iterate (Polynomial.X+12)
  intro z
  simp only [setup,weight_prod,weight_cons,weight_nil,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  have hw:=weight_nat_le (1:ℕ)
  norm_num at hw
  omega

end ContingencyTables.BinaryPowerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_DyadicRootProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary execution of the rational correction bisection

The root degree is the length of a supplied allowance list. One fixed
depth list controls the outer loop. Thus both natural-power evaluation
and the bisection loop have polynomial cost in the supplied binary data
and the two explicit allowances.
-/

namespace ContingencyTables.DyadicRootProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_powerInput : PolynomialTime powerInputRealizer := by
  unfold powerInputRealizer
  exact polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_listLength)

lemma polynomial_markedPower : PolynomialTime markedPowerRealizer := by
  apply work_composition polynomial_powerInput BinaryPowerPrograms.work_power X
  intro z
  have hl:=list_length_le_weight z.2
  simp only [powerInput,eval_X]
  rw [←Prod.eta z,weight_prod]
  dsimp only
  omega

lemma markedPower_eq (a : ℕ) (xs : List Bool) : markedPower (a,xs)=a^xs.length :=
  BinaryPowerPrograms.power_eq a xs.length

private lemma polynomial_low : PolynomialTime lowRealizer := by unfold lowRealizer; ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
private lemma polynomial_high : PolynomialTime highRealizer := by unfold highRealizer; ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
private lemma polynomial_denominator : PolynomialTime denominatorRealizer := by
  unfold denominatorRealizer; ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
private lemma polynomial_numerator : PolynomialTime numeratorRealizer := by
  unfold numeratorRealizer; ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
private lemma polynomial_targetDenominator : PolynomialTime targetDenominatorRealizer := by
  unfold targetDenominatorRealizer; ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
private lemma polynomial_allowance : PolynomialTime allowanceRealizer := by
  unfold allowanceRealizer; ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))

lemma polynomial_mid : PolynomialTime midRealizer :=
  polynomial_composition (polynomial_pair polynomial_low polynomial_high) polynomial_add

lemma polynomial_twiceDenominator : PolynomialTime twiceDenominatorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_denominator)
    polynomial_multiply

lemma polynomial_leftProduct : PolynomialTime leftProductRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_mid polynomial_allowance)
      polynomial_markedPower) polynomial_targetDenominator) polynomial_multiply

lemma polynomial_rightProduct : PolynomialTime rightProductRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator
    (polynomial_composition (polynomial_pair polynomial_twiceDenominator polynomial_allowance)
      polynomial_markedPower)) polynomial_multiply

lemma polynomial_test : PolynomialTime testRealizer :=
  polynomial_composition (polynomial_pair polynomial_leftProduct polynomial_rightProduct)
    polynomial_leNat

lemma polynomial_next : PolynomialTime nextRealizer := by
  apply polynomial_pair polynomial_first
  apply polynomial_choose polynomial_test
  · exact polynomial_pair (polynomial_pair polynomial_mid
      (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_high)
        polynomial_multiply)) polynomial_twiceDenominator
  · exact polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_low)
        polynomial_multiply) polynomial_mid) polynomial_twiceDenominator

lemma next_eq (z : State) :
    next z=(z.1,DyadicRootBisection.advance z.1.1 z.1.2.length z.2) := by
  simp only [next,test,leftProduct,rightProduct,markedPower_eq,mid,twiceDenominator,
    DyadicRootBisection.advance,decide_eq_true_eq]

private lemma size_double (a : ℕ) : (2*a).size≤a.size+1 := by
  simpa only [two_mul,max_self] using nat_size_add a a

lemma height_advance (c : TreeFraction.Fraction) (s : ℕ) (z : DyadicRootBisection.State) :
    height (DyadicRootBisection.advance c s z)≤height z+1 := by
  have hm:=nat_size_add z.1.1 z.1.2
  have ha:=size_double z.1.1
  have hb:=size_double z.1.2
  have hd:=size_double z.2
  unfold DyadicRootBisection.advance height
  split_ifs <;> dsimp only <;> omega

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_composition polynomial_second polynomial_next

lemma fold_parameters (xs : List Bool) (z : State) :
    (xs.foldl (fun z a=>advance (a,z)) z).1=z.1 := by
  induction xs generalizing z with
  | nil=>rfl
  | cons a xs ih=>exact ih (next z)

lemma fold_height (xs : List Bool) (z : State) :
    height (xs.foldl (fun z a=>advance (a,z)) z).2≤height z.2+xs.length := by
  induction xs generalizing z with
  | nil=>simp only [List.foldl_nil,List.length_nil,Nat.add_zero,le_refl]
  | cons a xs ih=>
    have hh:=height_advance z.1.1 z.1.2.length z.2
    have ht:=ih (next z)
    have hn: height (next z).2≤height z.2+1 := by
      rw [next_eq]
      exact hh
    change height (xs.foldl (fun z a=>advance (a,z)) (next z)).2≤
      height z.2+(xs.length+1)
    omega

lemma height_le_weight (z : DyadicRootBisection.State) : height z≤weight z := by
  have ha: z.1.1.size≤weight z :=
    (size_le_weight _).trans ((weight_fst z.1).trans (weight_fst z))
  have hb: z.1.2.size≤weight z :=
    (size_le_weight _).trans ((weight_snd z.1).trans (weight_fst z))
  have hd: z.2.size≤weight z := (size_le_weight _).trans (weight_snd z)
  exact max_le (max_le ha hb) hd

lemma polynomial_loop : PolynomialTime (fold advanceRealizer) := by
  apply polynomial_fold polynomial_advance (30*(X+1))
  intro xs z pre post he
  let S:=weight (xs,z)
  let out:=pre.foldl (fun z a=>advance (a,z)) z
  have hz: weight z≤S:=weight_snd (xs,z)
  have hp: weight z.1≤S:=(weight_fst z).trans hz
  have hs: height z.2≤S:=(height_le_weight z.2).trans ((weight_snd z).trans hz)
  have hl: pre.length≤S:=(list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (xs,z)))
  have hh:=fold_height pre z
  change height out.2≤height z.2+pre.length at hh
  have hctx: out.1=z.1:=fold_parameters pre z
  have h1:=weight_nat_le out.2.1.1
  have h2:=weight_nat_le out.2.1.2
  have h3:=weight_nat_le out.2.2
  have hs1: out.2.1.1.size≤height out.2:=
    (le_max_left _ _).trans (le_max_left _ _)
  have hs2: out.2.1.2.size≤height out.2:=
    (le_max_right _ _).trans (le_max_left _ _)
  have hs3: out.2.2.size≤height out.2:=le_max_right _ _
  have hw: weight out=weight out.1+weight out.2.1.1+weight out.2.1.2+weight out.2.2+3 := by
    change weight (out.1,((out.2.1.1,out.2.1.2),out.2.2))=_
    simp only [weight_prod]
    omega
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  change weight out≤30*(S+1)
  rw [hw,hctx]
  omega

lemma polynomial_prepare : PolynomialTime prepareRealizer := by
  unfold prepareRealizer
  exact polynomial_pair polynomial_second
    (polynomial_pair polynomial_first (polynomial_constant ((0,8),1)))

lemma polynomial_execute : PolynomialTime executeRealizer :=
  polynomial_composition polynomial_prepare polynomial_loop

lemma polynomial_finish : PolynomialTime finishRealizer :=
  polynomial_composition (polynomial_pair polynomial_mid polynomial_twiceDenominator)
    TreeFraction.polynomial_normalize

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_execute polynomial_finish

end ContingencyTables.DyadicRootProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RoundedPowerProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the rounded power used by the correction oracle

The exponent lies in [-2,2]. Clipping the computed signed floor
at twice the supplied degree allowance plus one is therefore inactive
on valid inputs, and keeps every binary execution polynomial even on
arbitrary malformed numerator/denominator data.
-/

namespace ContingencyTables.RoundedPowerProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial SignedPairProgram

lemma polynomial_normalized : PolynomialTime normalizedRealizer :=
  polynomial_composition SignedFloorProgram.polynomial_scaledFloor SignedPairProgram.polynomial_normalize

lemma polynomial_cap : PolynomialTime capRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 2)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_multiply)
    polynomial_successor

lemma polynomial_clipped : PolynomialTime clippedRealizer := polynomial_pair
  (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_normalized polynomial_first) polynomial_cap) polynomial_minimum)
  (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_normalized polynomial_second) polynomial_cap) polynomial_minimum)

lemma polynomial_positiveInput : PolynomialTime positiveInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition polynomial_clipped polynomial_first)
lemma polynomial_negativeInput : PolynomialTime negativeInputRealizer :=
  polynomial_pair (polynomial_constant 2) (polynomial_composition polynomial_clipped polynomial_second)

lemma polynomial_positivePower : PolynomialTime positivePowerRealizer := by
  apply work_composition polynomial_positiveInput BinaryPowerPrograms.work_power (2*X+10)
  intro z
  have hl: z.2.length ≤ weight z:=(list_length_le_weight z.2).trans (weight_snd z)
  have hm: (clipped z).1 ≤ cap z:=min_le_right _ _
  have ht: weight (2:ℕ) ≤ 9:=by decide
  simp only [positiveInput,cap,eval_add,eval_mul,eval_ofNat,eval_X] at *
  omega

lemma polynomial_negativePower : PolynomialTime negativePowerRealizer := by
  apply work_composition polynomial_negativeInput BinaryPowerPrograms.work_power (2*X+10)
  intro z
  have hl: z.2.length ≤ weight z:=(list_length_le_weight z.2).trans (weight_snd z)
  have hm: (clipped z).2 ≤ cap z:=min_le_right _ _
  have ht: weight (2:ℕ) ≤ 9:=by decide
  simp only [negativeInput,cap,eval_add,eval_mul,eval_ofNat,eval_X] at *
  omega

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_positivePower polynomial_negativePower)
    TreeFraction.polynomial_normalize

end ContingencyTables.RoundedPowerProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PowerApproximationProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed power-of-two approximation used by the weight oracle

Both stages are concrete binary programs: compute the rounded signed
power, then bisect using natural cross-products and shared denominators.
The two allowance lists determine the precision parameters.
-/

namespace ContingencyTables.PowerApproximationProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first))
      RoundedPowerProgram.polynomial_output)
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare DyadicRootProgram.polynomial_output

end ContingencyTables.PowerApproximationProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CorrectionValueProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary composition of the correction value

The input contains the computed grid exponent, phase ratio, point
penalty, population factor and two precision marker lists. Normalized
fraction multiplication supplies a positive denominator for the signed
exponent passed to the executed power approximation.
-/

namespace ContingencyTables.CorrectionValueProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_weighted : PolynomialTime weightedRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) TreeFraction.polynomial_mul

lemma polynomial_exponentInput : PolynomialTime exponentInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_weighted polynomial_second)) polynomial_multiply)
    (polynomial_composition polynomial_weighted polynomial_first))
    (polynomial_composition polynomial_weighted polynomial_second)

lemma polynomial_powerInput : PolynomialTime powerInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_exponentInput)
    polynomial_second

lemma polynomial_power : PolynomialTime powerRealizer :=
  polynomial_composition polynomial_powerInput PowerApproximationProgram.polynomial_output

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_power) TreeFraction.polynomial_mul

end ContingencyTables.CorrectionValueProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAggregateProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial exact fraction averages and products

These are the arithmetic folds used by the executed weight estimator.
Normalization makes the average valid on every input, including a raw
fraction with denominator zero.
-/

namespace ContingencyTables.FractionAggregateProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

lemma polynomial_average : PolynomialTime averageRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_map TreeFraction.polynomial_normalize)
      TreeFraction.polynomial_sum)
    (polynomial_pair polynomial_listLength (polynomial_constant 1))) TreeFraction.polynomial_div

private lemma height_mul (a b : TreeFraction.Fraction) :
    TreeFraction.height (TreeFraction.mul (a,b)) ≤
      TreeFraction.height a+TreeFraction.height b+1 := by
  have hn := TreeFraction.normalize_size_num (a.1*b.1,a.2*b.2)
  have hd := TreeFraction.normalize_size_den (a.1*b.1,a.2*b.2)
  have hnum := nat_size_mul a.1 b.1
  have hden := nat_size_mul a.2 b.2
  have ha := le_max_left a.1.size a.2.size
  have ha' := le_max_right a.1.size a.2.size
  have hb := le_max_left b.1.size b.2.size
  have hb' := le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (TreeFraction.mul (a,b)).1.size ≤ _ at hn
  change (TreeFraction.mul (a,b)).2.size ≤ _ at hd
  unfold TreeFraction.height
  apply max_le <;> omega

private lemma fold_height (xs : List TreeFraction.Fraction) (a : TreeFraction.Fraction)
    (M : ℕ) (hx : ∀ b∈xs,TreeFraction.height b ≤ M) :
    TreeFraction.height (xs.foldl (fun a b => TreeFraction.mul (b,a)) a) ≤
      TreeFraction.height a+xs.length*(M+1) := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hb := hx b (by simp)
    have ht := ih (TreeFraction.mul (b,a)) (fun c hc => hx c (by simp [hc]))
    have hm := height_mul b a
    simp only [List.foldl_cons,List.length_cons]
    nlinarith

private lemma polynomial_productFold : PolynomialTime (fold TreeFraction.mulRealizer) := by
  apply polynomial_fold TreeFraction.polynomial_mul (8*X+8*X*(X+1)+3)
  intro xs a pre post he
  let S := weight (xs,a)
  have hp : pre.length ≤ S :=
    (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (xs,a)))
  have hb : ∀ b∈pre,TreeFraction.height b ≤ S := by
    intro b hb
    exact (TreeFraction.height_le_weight b).trans
      ((weight_mem (as := xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have ha : TreeFraction.height a ≤ S :=
    (TreeFraction.height_le_weight a).trans (weight_snd (xs,a))
  have hh := fold_height pre a S hb
  have hw := TreeFraction.weight_le_height (pre.foldl (fun a b => TreeFraction.mul (b,a)) a)
  have hm := Nat.mul_le_mul_right (S+1) hp
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  change _ ≤ 8*S+8*S*(S+1)+3
  nlinarith

lemma polynomial_product : PolynomialTime productRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant (1,1)))
    polynomial_productFold

end ContingencyTables.FractionAggregateProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MedianFractionProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary fraction median with polynomial running time -/

namespace ContingencyTables.MedianFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.TreeFraction Polynomial

lemma polynomial_step : PolynomialTime stepRealizer := by
  unfold stepRealizer
  exact polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
          polynomial_first)) polynomial_listCons)
      (polynomial_choose
        (polynomial_composition (polynomial_pair polynomial_first
          (polynomial_composition polynomial_second polynomial_first)) TreeFraction.polynomial_less)
        (polynomial_composition (polynomial_pair polynomial_first
          (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
            polynomial_second)) polynomial_listCons)
        (polynomial_composition (polynomial_pair
          (polynomial_composition polynomial_second polynomial_first)
          (polynomial_composition (polynomial_pair polynomial_first
            (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
              polynomial_first)) polynomial_listCons)) polynomial_listCons)))

lemma insert_fold (q : Fraction) (xs : List Fraction) :
    xs.reverse.foldl (fun s x => step (x,s)) (q,([],[q])) = (q,(xs,insertRaw q xs)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.reverse_cons,List.foldl_append,ih,List.foldl_cons,List.foldl_nil]
    rfl

lemma insert_eq (q : Fraction) (xs : List Fraction) : insert (q,xs)=insertRaw q xs := by
  unfold insert
  rw [insert_fold]

lemma insert_weight (q : Fraction) (xs : List Fraction) :
    weight (insertRaw q xs)=1+weight q+weight xs := by
  induction xs with
  | nil => simp [insertRaw]
  | cons x xs ih =>
    simp only [insertRaw]
    split <;> simp only [weight_cons,ih]
    all_goals omega

lemma fold_weight (xs : List Fraction) (q : Fraction) (zs ys : List Fraction) :
    let t := xs.foldl (fun s x => step (x,s)) (q,(zs,ys))
    t.1=q ∧ weight t.2.1+1=weight zs+weight xs ∧
      weight t.2.2 ≤ max (weight ys) (weight q+weight zs+1)+weight xs := by
  induction xs generalizing zs ys with
  | nil =>
    exact ⟨rfl,by simp only [List.foldl_nil,weight_nil],by
      simpa only [List.foldl_nil,weight_nil] using
        (Nat.le_max_left (weight ys) (weight q+weight zs+1)).trans (Nat.le_succ _)⟩
  | cons x xs ih =>
    rw [List.foldl_cons]
    change (let t := xs.foldl (fun s x => step (x,s)) (q,(x::zs,if TreeFraction.less (x,q) then x::ys else q::x::zs));
      t.1=q ∧ weight t.2.1+1=weight zs+weight (x::xs) ∧
        weight t.2.2 ≤ max (weight ys) (weight q+weight zs+1)+weight (x::xs))
    have hh := ih (x::zs) (if TreeFraction.less (x,q) then x::ys else q::x::zs)
    dsimp only at hh ⊢
    refine ⟨hh.1,?_,?_⟩
    · simp only [weight_cons] at hh ⊢; omega
    · by_cases h : TreeFraction.less (x,q)=true
      · simp only [h,ite_true, if_true,weight_cons] at hh ⊢; omega
      · simp only [h,Bool.false_eq_true,ite_false,weight_cons] at hh ⊢; omega

lemma state_weight (s : State) :
    weight s=1+weight s.1+(1+weight s.2.1+weight s.2.2) := by
  rcases s with ⟨q,xs,ys⟩
  simp only [weight_prod]

lemma polynomial_stepFold : PolynomialTime (fold stepRealizer) := by
  apply polynomial_fold polynomial_step (5*X+5)
  intro xs s pre post he
  rcases s with ⟨q,zs,ys⟩
  have hh := fold_weight pre q zs ys
  have hp := weight_prefix he
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  rw [state_weight,hh.1]
  omega

lemma polynomial_insert : PolynomialTime insertRealizer := by
  unfold insertRealizer
  exact polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
      (polynomial_pair polynomial_first (polynomial_pair (polynomial_constant ([] : List Fraction))
        (polynomial_composition (polynomial_pair polynomial_first (polynomial_constant ([] : List Fraction)))
          polynomial_listCons))))
    (polynomial_composition (polynomial_composition polynomial_stepFold polynomial_second)
      polynomial_second)

lemma sortFold_weight (xs zs : List Fraction) :
    weight (xs.foldl (fun s x => insert (x,s)) zs)+1=weight zs+weight xs := by
  induction xs generalizing zs with
  | nil => simp
  | cons x xs ih =>
    have hh := ih (insert (x,zs))
    simp only [List.foldl_cons,insert_eq,insert_weight,weight_cons] at hh ⊢
    omega

lemma polynomial_insertFold : PolynomialTime (fold insertRealizer) := by
  apply polynomial_fold polynomial_insert (2*X)
  intro xs zs pre post he
  have hh := sortFold_weight pre zs
  have hp := weight_prefix he
  simp only [eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma polynomial_sort : PolynomialTime sortRealizer :=
  polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant ([] : List Fraction)))
    polynomial_insertFold

lemma polynomial_median : PolynomialTime medianRealizer :=
  polynomial_composition
    (polynomial_pair (polynomial_composition (polynomial_map TreeFraction.polynomial_normalize)
      polynomial_sort)
      (polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
        polynomial_quotient)) (polynomial_getDFast (0,1))

end ContingencyTables.MedianFractionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedBinFramesProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the actual bin draws from the computed free-cell catalog

Only the capacity matrix, catalog metadata, grid coordinate list and
numeric sampling parameters are supplied. The program computes each
full range and bin index before invoking the proved vector draw.
-/

namespace ContingencyTables.RootedBinFramesProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

lemma polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_constant false)) RootedForestCatalog.polynomial_catalog

lemma polynomial_cell : PolynomialTime cellRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_catalog)
    polynomial_second) (polynomial_getDFast (0,0))

lemma polynomial_rangeSize : PolynomialTime rangeSizeRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second)
    polynomial_cell) polynomial_matrixEntry) polynomial_successor

lemma polynomial_coordinate : PolynomialTime coordinateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second)
    (polynomial_getDFast 0)

lemma polynomial_item : PolynomialTime itemRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_rangeSize) polynomial_coordinate)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)

lemma polynomial_indices : PolynomialTime indicesRealizer :=
  polynomial_composition polynomial_catalog RootedTreeInputProgram.polynomial_indices

theorem polynomial_frames : PolynomialTime framesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_item)

theorem polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_frames)
    polynomial_second) BinVectorProgram.polynomial_output

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

end ContingencyTables.RootedBinFramesProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleStepProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of the catalog-order oracle step

The program uses the computed forest exponent twice, one arithmetic
axis proposal and one independent bounded dyadic acceptance word.
-/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped Classical

lemma polynomial_replace : PolynomialTime replaceRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second)

lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second))
    (polynomial_composition polynomial_second polynomial_first)) polynomial_axisWordStep

lemma polynomial_currentData : PolynomialTime currentDataRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second

lemma polynomial_candidateData : PolynomialTime candidateDataRealizer :=
  polynomial_composition (polynomial_pair polynomial_currentData polynomial_second) polynomial_replace

lemma polynomial_gap : PolynomialTime gapRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_candidateData RootedPenaltyEvaluateProgram.polynomial_evaluate)
    (polynomial_composition polynomial_currentData RootedPenaltyEvaluateProgram.polynomial_evaluate))
    polynomial_subtract

lemma polynomial_acceptCandidate : PolynomialTime acceptCandidateRealizer :=
  polynomial_choose (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    polynomial_gap) polynomial_dyadicWordAccept) polynomial_second
    (polynomial_composition (polynomial_composition polynomial_currentData polynomial_second)
      polynomial_second)

theorem polynomial_step : PolynomialTime stepRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_candidate)
    (polynomial_optionCases
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_second)
      polynomial_acceptCandidate)

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single fixed word drives an executed oracle transition -/

namespace ContingencyTables.RootedOracleStepProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  have hd : PolynomialTime (composition
      (composition (composition (composition (first (A := Data) (B := List Bool)) second)
        first) first) first) :=
    polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_first) polynomial_first
  unfold proposalWidthRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 8) hd) polynomial_multiply) polynomial_ceilLogTwo

theorem polynomial_wordStep : PolynomialTime wordStepRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth)
      polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth)
      polynomial_dropFast))) polynomial_step

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FairBits

end ContingencyTables.RootedOracleStepProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an oracle walk

The immutable graph and cell arrays are kept separately from the grid
coordinates. A coordinate changes by at most one per transition, which
bounds every accumulator reached by the binary list fold.
-/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial
open scoped Classical

lemma polynomial_toData : PolynomialTime toDataRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_second) polynomial_second))

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_toData) polynomial_first)
      RootedOracleStepProgram.polynomial_wordStep)

lemma step_growth (z : RootedOracleStepProgram.StepInput) (S : ℕ)
    (hx : ∀ a∈z.1.2.2.2,a.size≤S) :
    (RootedOracleStepProgram.step z).length=z.1.2.2.2.length ∧
      ∀ a∈RootedOracleStepProgram.step z,a.size≤S+2 := by
  have hstay : z.1.2.2.2.length=z.1.2.2.2.length ∧
      ∀ a∈z.1.2.2.2,a.size≤S+2 :=
    ⟨rfl,fun a ha => (hx a ha).trans (Nat.le_add_right _ _)⟩
  unfold RootedOracleStepProgram.step
  cases h : RootedOracleStepProgram.candidate z with
  | none => exact hstay
  | some ys =>
    have hy := axisListStep_growth
      (((z.1.1,z.1.2.2.2),MatchingFPRAS.StackAddition.value z.2.1/2),
        decide (MatchingFPRAS.StackAddition.value z.2.1%2=1)) ys S h hx
    simp only [Option.elim_some,RootedOracleStepProgram.acceptCandidate]
    split <;> assumption

lemma advance_growth (state : State) (bits : List Bool) (S : ℕ)
    (hx : ∀ a∈state.2,a.size≤S) :
    (advance (bits,state)).2.length=state.2.length ∧
      ∀ a∈(advance (bits,state)).2,a.size≤S+2 :=
  step_growth _ S hx

lemma fold_frame (bits : List (List Bool)) (state : State) :
    let out := bits.foldl (fun state bits => advance (bits,state)) state
    out.1=state.1 ∧ out.2.length=state.2.length := by
  induction bits generalizing state with
  | nil => exact ⟨rfl,rfl⟩
  | cons b bs ih =>
    have h := ih (advance (b,state))
    have hl : (advance (b,state)).2.length=state.2.length := by
      exact (advance_growth state b (state.2.map Nat.size).sum
        (fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a.size
          (List.mem_map.mpr ⟨a,ha,rfl⟩))).1
    exact ⟨h.1,h.2.trans hl⟩

lemma fold_sizes (bits : List (List Bool)) (state : State) (S : ℕ)
    (hx : ∀ a∈state.2,a.size≤S) :
    ∀ a∈(bits.foldl (fun state bits => advance (bits,state)) state).2,
      a.size≤S+2*bits.length := by
  induction bits generalizing state S with
  | nil => simpa using hx
  | cons b bs ih =>
    have hs := ih (advance (b,state)) (S+2) (advance_growth state b S hx).2
    intro a ha
    exact (hs a ha).trans_eq (by simp only [List.length_cons]; omega)

theorem polynomial_walkWords : PolynomialTime walkWordsRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (20*(X+1)^2)
  intro bits state pre post he
  let S := weight (bits,state)
  let out := pre.foldl (fun state bits => advance (bits,state)) state
  have hd : weight state≤S := weight_snd (bits,state)
  have hp : pre.length≤S := (list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (bits,state)))
  have hxs : weight state.2≤S := (weight_snd state).trans hd
  have hn : state.2.length≤S := (list_length_le_weight _).trans hxs
  have hi : ∀ a∈state.2,a.size≤S := fun a ha =>
    (size_le_weight a).trans ((weight_mem ha).trans hxs)
  have hs := fold_sizes pre state S hi
  have ht := fold_frame pre state
  have hw : weight out.2≤out.2.length*(4*(S+2*pre.length)+2)+1 := by
    have h := weight_map_bound (f := id) (as := out.2) (N := 4*(S+2*pre.length)+1)
      (fun a ha => (weight_nat_le a).trans (by have h := hs a ha; omega))
    simpa only [List.map_id_fun,id_eq,Nat.add_assoc] using h
  have hf : weight out.1≤S := by
    rw [ht.1]
    exact (weight_fst state).trans hd
  have hl : out.2.length≤S := ht.2.trans_le hn
  have hmul : out.2.length*(4*(S+2*pre.length)+2)≤S*(12*S+2) :=
    Nat.mul_le_mul hl (by omega)
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)^2
  have hweight : weight out=1+weight out.1+weight out.2 := by
    change weight (out.1,out.2)=1+weight out.1+weight out.2
    exact weight_prod _ _
  nlinarith

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess

end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedPointPenaltyProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed penalty evaluation at a sampled integer assignment

At an integer point, the coordinate scale in the affine coefficient
cancels its inverse in the coordinate. The program therefore forms the
unscaled signed affine numerator directly from the sampled integers.
-/

namespace ContingencyTables.RootedPointPenaltyProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped RootedForestPrepareProgram
open scoped BigOperators Classical

lemma polynomial_term : PolynomialTime termRealizer :=
  polynomial_pair (polynomial_composition polynomial_first
    RootedCoefficientProgram.polynomial_coefficient) polynomial_second

lemma polynomial_tree : PolynomialTime treeRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedOffsetProgram.polynomial_offset)
    (polynomial_composition polynomial_second (polynomial_map polynomial_term)))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)

lemma polynomial_prepareTree : PolynomialTime prepareTreeRealizer :=
  polynomial_composition polynomial_forestInput polynomial_tree

lemma polynomial_trees : PolynomialTime treesRealizer :=
  polynomial_composition (polynomial_pair polynomial_treeBundle polynomial_treeCells)
    (polynomial_mapWith polynomial_prepareTree)

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      RootedDemandProgram.polynomial_rootCount)) polynomial_trees

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare ForestPenaltyProgram.polynomial_penaltyCode

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit GraphCompletionCounts

end ContingencyTables.RootedPointPenaltyProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed selected-root correction

The stored grid point and sampled integer point share their literal
capacity, forest, baseline and small-view arrays.  The program computes
the grid exponent, point penalty and population factor before the
bounded rational power approximation.
-/

namespace ContingencyTables.RootedCorrectionProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms
open scoped BigOperators Classical

lemma polynomial_exponentInput : PolynomialTime exponentInputRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_second) polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_second) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second))

lemma polynomial_pointInput : PolynomialTime pointInputRealizer := by
  unfold pointInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_exponentInput polynomial_first) polynomial_second)
      polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_exponentInput polynomial_first)
      RootedPenaltyEvaluateProgram.polynomial_width))
    (polynomial_composition (polynomial_composition polynomial_exponentInput polynomial_second)
      polynomial_first)) (polynomial_composition polynomial_first polynomial_second)

lemma polynomial_binInput : PolynomialTime binInputRealizer :=
  polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_first polynomial_first) polynomial_first) polynomial_first)
      (polynomial_pair (polynomial_constant 0)
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition (polynomial_composition (polynomial_composition
            polynomial_first polynomial_first) polynomial_first) polynomial_second)
            polynomial_first) polynomial_first) polynomial_first)))
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        polynomial_exponentInput polynomial_second) polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second))

lemma polynomial_populationInput : PolynomialTime populationInputRealizer :=
  polynomial_composition
    (polynomial_composition polynomial_binInput RootedBinFramesProgram.polynomial_frames)
    (polynomial_map polynomial_first)

lemma polynomial_phase : PolynomialTime phaseRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_exponentInput polynomial_first) polynomial_second)
    polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_exponentInput polynomial_first)
      RootedPenaltyEvaluateProgram.polynomial_height)

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate
  RootedPointPenaltyProgram.output BinPopulationProgram.output

lemma polynomial_exponentValue : PolynomialTime exponentValueRealizer :=
  polynomial_composition polynomial_exponentInput RootedPenaltyEvaluateProgram.polynomial_evaluate

lemma polynomial_pointValue : PolynomialTime pointValueRealizer :=
  polynomial_composition polynomial_pointInput RootedPointPenaltyProgram.polynomial_output

lemma polynomial_populationValue : PolynomialTime populationValueRealizer :=
  polynomial_composition polynomial_populationInput BinPopulationProgram.polynomial_output

attribute [local irreducible] exponentValue pointValue populationValue

lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair polynomial_exponentValue polynomial_phase) polynomial_pointValue

attribute [local irreducible] frame

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_frame polynomial_populationValue) polynomial_second

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CorrectionValueProgram.polynomial_output

end ContingencyTables.RootedCorrectionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleFlatProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial flat-word program for the actual oracle walk -/

namespace ContingencyTables.RootedOracleWalkProgram

open MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  have hd : PolynomialTime (composition
      (composition (composition (second (A := ℕ) (B := RootedPenaltyEvaluateProgram.Parameters×
        RootedDemandProgram.Input)) first) first) first) :=
    polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_first
  unfold proposalWidthRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 8) hd) polynomial_multiply) polynomial_ceilLogTwo

lemma polynomial_stepWidth : PolynomialTime stepWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_proposalWidth
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      RootedPenaltyEvaluateProgram.polynomial_height)) polynomial_add

theorem polynomial_flatWalk : PolynomialTime flatWalkRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_stepWidth) polynomial_second) polynomial_wordChunks)) polynomial_walkWords

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

end ContingencyTables.RootedOracleWalkProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedCorrectionSampleProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing one selected-root correction sample

Separate finite words drive the grid walk and the integer draw. The
computed final bin and sampled integer are then passed to the exact
population and rational-power correction program.
-/

namespace ContingencyTables.RootedCorrectionSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

lemma polynomial_walked : PolynomialTime walkedRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_first)) RootedOracleWalkProgram.polynomial_flatWalk

attribute [local irreducible] walked

lemma polynomial_binFrame : PolynomialTime binFrameRealizer := by
  unfold binFrameRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_walked polynomial_first)
        polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_walked polynomial_first)
            polynomial_second) polynomial_first) polynomial_first) polynomial_first)))
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_walked polynomial_first) polynomial_second)
          polynomial_second) polynomial_first)
      (polynomial_composition polynomial_walked polynomial_second))

attribute [local irreducible] binFrame

lemma polynomial_sampled : PolynomialTime sampledRealizer :=
  polynomial_composition (polynomial_pair polynomial_binFrame
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
      polynomial_second)) RootedBinFramesProgram.polynomial_draw

attribute [local irreducible] sampled

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_walked polynomial_sampled)
    (polynomial_composition polynomial_second polynomial_first)

attribute [local irreducible] prepare

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare RootedCorrectionProgram.polynomial_output

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity FairBits
open scoped BigOperators

end ContingencyTables.RootedCorrectionSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedRatioSampleProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial execution of an adjacent-parameter ratio sample

The exact ratio is either one or one half. The program compares the two
computed integer exponents and never materializes an exponential weight.
-/

namespace ContingencyTables.RootedRatioSampleProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open scoped Classical

lemma polynomial_bump : PolynomialTime bumpRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_first)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_second)
          polynomial_successor))) polynomial_second

attribute [local irreducible] RootedPenaltyEvaluateProgram.evaluate

lemma polynomial_equalExponents : PolynomialTime equalExponentsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_bump RootedPenaltyEvaluateProgram.polynomial_evaluate)
    RootedPenaltyEvaluateProgram.polynomial_evaluate) polynomial_natEqual

lemma polynomial_ratio : PolynomialTime ratioRealizer :=
  polynomial_choose polynomial_equalExponents (polynomial_constant _) (polynomial_constant _)

lemma polynomial_currentInput : PolynomialTime currentInputRealizer :=
  polynomial_composition RootedOracleWalkProgram.polynomial_flatWalk
    (polynomial_composition RootedOracleWalkProgram.polynomial_toData polynomial_second)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_currentInput polynomial_ratio

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedCompletion
open scoped BigOperators

end ContingencyTables.RootedRatioSampleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorBlockProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed sample blocks and the product weight estimator

The lists contain the actual sample inputs and their disjoint finite
words. Each sample is evaluated by the checked binary program before
its average or product is formed.
-/

namespace ContingencyTables.RootedEstimatorBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_ratioAverage : PolynomialTime ratioAverageRealizer :=
  polynomial_composition (polynomial_map RootedRatioSampleProgram.polynomial_output)
    FractionAggregateProgram.polynomial_average

lemma polynomial_correctionAverage : PolynomialTime correctionAverageRealizer :=
  polynomial_composition (polynomial_map RootedCorrectionSampleProgram.polynomial_output)
    FractionAggregateProgram.polynomial_average

attribute [local irreducible] ratioAverage correctionAverage

lemma polynomial_ratioProduct : PolynomialTime ratioProductRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_map polynomial_ratioAverage)) FractionAggregateProgram.polynomial_product

lemma polynomial_factors : PolynomialTime factorsRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratioProduct
    (polynomial_composition polynomial_second polynomial_correctionAverage)) TreeFraction.polynomial_mul

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_first) (polynomial_constant 1))
    polynomial_factors) TreeFraction.polynomial_mul

end ContingencyTables.RootedEstimatorBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorLayoutProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed sizes of the estimator's disjoint word banks

The schedule supplies the phase and sample counts and the two walk times.
The catalog itself supplies both the integer-draw widths and the initial
free-assignment count. No list is allocated from a binary count here.
-/

namespace ContingencyTables.RootedEstimatorLayoutProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_stepWidth : PolynomialTime stepWidthRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    RootedOracleWalkProgram.polynomial_stepWidth

lemma polynomial_ratioWidth : PolynomialTime ratioWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_first) polynomial_first)
    polynomial_stepWidth) polynomial_multiply

lemma polynomial_ratioBlockWidth : PolynomialTime ratioBlockWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
    polynomial_ratioWidth) polynomial_multiply

lemma polynomial_ratioBankWidth : PolynomialTime ratioBankWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first)
    polynomial_ratioBlockWidth) polynomial_multiply

lemma polynomial_binFrame : PolynomialTime binFrameRealizer := by
  unfold binFrameRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second)
        (polynomial_composition (polynomial_composition (polynomial_composition
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_second) polynomial_first) polynomial_first) polynomial_first)))
    (polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
          polynomial_second) polynomial_first)
      (polynomial_composition polynomial_first polynomial_second))

lemma polynomial_frames : PolynomialTime framesRealizer :=
  polynomial_composition polynomial_binFrame RootedBinFramesProgram.polynomial_frames

attribute [local irreducible] frames

lemma polynomial_binWidth : PolynomialTime binWidthRealizer :=
  polynomial_composition polynomial_frames
    (polynomial_composition (polynomial_map BinVectorProgram.polynomial_reservedWidth) polynomial_listSum)

lemma polynomial_rangeValue : PolynomialTime rangeValueRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second

lemma polynomial_rangeValues : PolynomialTime rangeValuesRealizer := polynomial_map polynomial_rangeValue

attribute [local irreducible] rangeValue rangeValues

lemma polynomial_assignmentCount : PolynomialTime assignmentCountRealizer := by
  unfold assignmentCountRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition polynomial_frames polynomial_rangeValues)
    polynomial_listProd

lemma polynomial_correctionWalkWidth : PolynomialTime correctionWalkWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_first) polynomial_second)
    polynomial_stepWidth) polynomial_multiply

lemma polynomial_correctionWidth : PolynomialTime correctionWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_correctionWalkWidth polynomial_binWidth) polynomial_add

lemma polynomial_wordWidth : PolynomialTime wordWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratioBankWidth
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
      polynomial_correctionWidth) polynomial_multiply)) polynomial_add

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped BigOperators Classical

end ContingencyTables.RootedEstimatorLayoutProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One flat word executes the complete weight estimator

The number of generated rows is bounded by the supplied word length.
The binary schedule therefore remains safe even on malformed inputs.
-/

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

lemma polynomial_phase : PolynomialTime phaseRealizer := by
  unfold phaseRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_pair
        (polynomial_pair
          (polynomial_composition (polynomial_composition (polynomial_composition
            (polynomial_composition polynomial_first polynomial_first) polynomial_second)
              polynomial_first) polynomial_first)
          (polynomial_pair
            (polynomial_composition (polynomial_composition (polynomial_composition
              (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
                polynomial_second) polynomial_first) polynomial_second) polynomial_first)
            polynomial_second))
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)))
    (polynomial_composition polynomial_first polynomial_second)

lemma polynomial_ratioPrefix : PolynomialTime ratioPrefixRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_first polynomial_ratioBankWidth)) polynomial_takeFast

lemma polynomial_ratioRows : PolynomialTime ratioRowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_ratioBlockWidth) polynomial_ratioPrefix)
    polynomial_completeWordRows

lemma polynomial_ratioChunk : PolynomialTime ratioChunkRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_ratioBlockWidth)
    (polynomial_composition polynomial_first polynomial_ratioPrefix)) polynomial_second)
    polynomial_wordChunk

lemma polynomial_ratioState : PolynomialTime ratioStateRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) polynomial_phase

lemma polynomial_ratioWords : PolynomialTime ratioWordsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_ratioWidth)
    polynomial_ratioChunk) polynomial_wordChunks

lemma polynomial_ratioBlock : PolynomialTime ratioBlockRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratioState polynomial_ratioWords)
    (polynomial_mapWith polynomial_identity)

lemma polynomial_ratioBlocks : PolynomialTime ratioBlocksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_ratioRows)
    (polynomial_mapWith polynomial_ratioBlock)

lemma polynomial_correctionTail : PolynomialTime correctionTailRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_first polynomial_ratioBankWidth)) polynomial_dropFast

lemma polynomial_correctionWords : PolynomialTime correctionWordsRealizer := by
  unfold correctionWordsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_correctionWidth) polynomial_correctionTail)
      polynomial_wordChunks)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second))
    polynomial_takeFast

lemma polynomial_terminalState : PolynomialTime terminalStateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_first))
    polynomial_phase

lemma polynomial_correctionSample : PolynomialTime correctionSampleRealizer := by
  unfold correctionSampleRealizer
  exact polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_terminalState)
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
          polynomial_second) polynomial_second))
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_correctionWalkWidth)) polynomial_takeFast)
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            polynomial_correctionWalkWidth)) polynomial_dropFast)))

lemma polynomial_correctionBlock : PolynomialTime correctionBlockRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_correctionWords)
    (polynomial_mapWith polynomial_correctionSample)

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_assignmentCount) polynomial_ratioBlocks)
    polynomial_correctionBlock

attribute [local irreducible] prepare

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare RootedEstimatorBlockProgram.polynomial_output

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open scoped Classical
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedEstimatorMedianProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing independent complete estimators and their rational median -/

namespace ContingencyTables.RootedEstimatorMedianProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms
open RootedEstimatorLayoutProgram

lemma polynomial_words : PolynomialTime wordsRealizer := by
  unfold wordsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_wordWidth) (polynomial_composition polynomial_second polynomial_second))
      polynomial_wordChunks)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_takeFast

lemma polynomial_sample : PolynomialTime sampleRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_second)) RootedEstimatorWordProgram.polynomial_output

lemma polynomial_samples : PolynomialTime samplesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_words)
    (polynomial_mapWith polynomial_sample)

attribute [local irreducible] samples

theorem polynomial_output_oai : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_samples MedianFractionProgram.polynomial_median

open GridBoundary CommonBasesFPRAS
open scoped Classical

end ContingencyTables.RootedEstimatorMedianProgram

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output_oai := @OAI.ContingencyTables.RootedEstimatorMedianProgram.polynomial_output_oai
