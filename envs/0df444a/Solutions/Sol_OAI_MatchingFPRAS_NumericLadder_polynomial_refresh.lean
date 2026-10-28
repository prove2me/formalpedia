-- Prove2me | solution 1 for OAI.MatchingFPRAS.NumericLadder.polynomial_refresh
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:27:50.477991+00:00
-- url     : https://prove2.me/submissions/b03070f7-b20e-432b-b71c-769e542c5907

import Mathlib
import Definitions.Def_OAIQ051M004

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_TreeBits
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.instCodecData
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeList
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRepeat
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFraction
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomial
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialArithmetic
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialLists
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialDivision
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialLoop
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialGCD
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
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
lemma polynomial_add : PolynomialTime addRealizer := by
  unfold addRealizer
  apply polynomial_composition _ polynomial_normalize
  apply polynomial_pair
  · apply polynomial_composition _ TreeTyped.polynomial_add
    exact polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)
      (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) (polynomial_snd polynomial_first)) polynomial_multiply)
  · exact polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply
lemma polynomial_less : PolynomialTime lessRealizer := by
  unfold lessRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) (polynomial_snd polynomial_first)) polynomial_multiply)) TreeTyped.polynomial_less
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialCollections
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCanonical
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.finsetCodec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFinite
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeCostMeasure
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFiniteOps
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColex
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFiniteCollections
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialGrid
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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

variable {m n : A → ℕ} {f : A×(ℕ×ℕ) → B}
lemma polynomial_grid {M : Realizer m} {N : Realizer n} {F : Realizer f}
    (hM : PolynomialTime M) (hN : PolynomialTime N) (hF : PolynomialTime F)
    (p q : Polynomial ℕ) (hm : ∀ a,m a≤p.eval (weight a)) (hn : ∀ a,n a≤q.eval (weight a)) :
    PolynomialTime (grid M N F) := by
  have hrows : PolynomialTime (composition (composition (composition (first (A:=A) (B:=ℕ)) N) successor) range) := by
    apply polynomial_boundedRange (polynomial_composition (polynomial_composition polynomial_first hN) polynomial_successor) (q+1)
    intro x
    have hb:=(hn x.1).trans (polynomial_eval_monotone q (weight_fst x))
    simpa only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_one] using Nat.add_le_add_right hb 1
  unfold grid
  dsimp only
  apply polynomial_composition (polynomial_pair polynomial_identity (polynomial_boundedRange hM p hm))
  apply polynomial_mapWith
  apply polynomial_composition (polynomial_pair polynomial_identity hrows)
  apply polynomial_mapWith
  apply polynomial_composition _ hF
  exact polynomial_pair (polynomial_fst polynomial_first)
    (polynomial_pair (polynomial_snd polynomial_first) polynomial_second)

omit [Codec A] [Codec B] in
lemma polynomial_clip : PolynomialTime clipRealizer := by
  unfold clipRealizer
  apply polynomial_congr
  apply polynomial_choose _ polynomial_second (polynomial_constant 0)
  apply polynomial_composition _ polynomial_leNat
  apply polynomial_pair (polynomial_composition polynomial_second polynomial_bitSize) polynomial_first
omit [Codec A] [Codec B] in
lemma clip_size (K n : ℕ) : (clip (K,n)).size≤K := by
  unfold clip
  split_ifs with h
  · exact h
  · simp
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeListMore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B X : Type} [Codec A] [Codec B] [Codec X]

lemma listMin_le_default (as : List ℕ) (d : ℕ) : listMin (as,d)≤d := by
  induction as generalizing d with
  | nil => rfl
  | cons a as ih => exact (ih (min d a)).trans (min_le_left _ _)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeFractionCosts
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFastLookup
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeChoiceCosts
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
omit [Codec A] in
lemma polynomial_listMin : PolynomialTime listMinRealizer := by
  unfold listMinRealizer
  apply polynomial_congr
  apply polynomial_fold polynomial_minimum (4*X+1)
  intro as n pre post he
  have hm : pre.foldl (fun z a=>min a z) n=listMin (pre,n) := by
    unfold listMin
    congr 1
    funext z a
    exact Nat.min_comm _ _
  change weight (pre.foldl (fun z a=>min a z) n)≤_
  rw [hm]
  have hl:=listMin_le_default pre n
  have hs:=(Nat.size_le_size hl).trans (size_le_weight n)
  have hw:=weight_nat_le (listMin (pre,n))
  have hn : weight n≤weight (as,n) := weight_snd (as,n)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma polynomial_cumulativeFast : PolynomialTime cumulativeFast :=
  polynomial_composition polynomial_takeFast polynomial_sum
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableChoice
open TreeTyped TreeFraction Polynomial

lemma polynomial_predicateFast : PolynomialTime predicateFast := by
  unfold predicateFast
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ TreeFraction.polynomial_less
  apply polynomial_pair (polynomial_snd polynomial_first)
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_fst polynomial_first)
      (polynomial_composition polynomial_second polynomial_successor)) polynomial_cumulativeFast

lemma polynomial_chooseFast : PolynomialTime chooseFast := by
  unfold chooseFast
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_listMin
  apply polynomial_pair _ (polynomial_composition polynomial_first polynomial_listLength)
  apply polynomial_composition _ (polynomial_filterWith polynomial_predicateFast)
  apply polynomial_pair polynomial_identity
  exact polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    (fun x=>by simpa using (list_length_le_weight x.1).trans (weight_fst x))

lemma polynomial_chooseBitsFast : PolynomialTime chooseBitsFast :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_bitValue)
    (polynomial_composition polynomial_second polynomial_bitDenominator))) polynomial_chooseFast
end MatchingFPRAS.ExecutableChoice

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreeNumericCosts
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

lemma work_pair {f : A → B} {g : A → C} {F : Realizer f} {G : Realizer g}
    {measure : A → ℕ} (hF : WorkBound F measure) (hG : WorkBound G measure)
    (u : Polynomial ℕ) (hu : ∀ a,weight a≤u.eval (measure a)) : WorkBound (pair F G) measure := by
  obtain ⟨p,hp⟩:=hF
  obtain ⟨q,hq⟩:=hG
  refine ⟨7*p+q+11*u+32,fun a=>?_⟩
  have h1:=hp a
  have h2:=hq a
  have h3:=hu a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  rw [weight_prod]
  change F.cost a+G.cost a+11*weight a+6*weight (f a)+31+(1+weight (f a)+weight (g a))≤_
  omega
omit [Codec C] in
lemma work_choose {f : A → Bool} {g h : A → B} {F : Realizer f} {G : Realizer g} {H : Realizer h}
    {measure : A → ℕ} (hF : WorkBound F measure) (hG : WorkBound G measure) (hH : WorkBound H measure)
    (u : Polynomial ℕ) (hu : ∀ a,weight a≤u.eval (measure a)) : WorkBound (choose F G H) measure := by
  obtain ⟨p,hp⟩:=hF
  obtain ⟨q,hq⟩:=hG
  obtain ⟨r,hr⟩:=hH
  refine ⟨p+q+r+7*u+18,fun a=>?_⟩
  have h1:=hp a
  have h2:=hq a
  have h3:=hr a
  have h4:=hu a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
  change F.cost a+(if f a then G.cost a else H.cost a)+7*weight a+18+
    weight (if f a then g a else h a)≤_
  cases f a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

omit [Codec A] [Codec B] [Codec C] in
lemma factorial_numeric_work : WorkBound factorial id := by
  unfold factorial
  apply work_congr
  apply work_boundedRepeat (work_of_polynomial (polynomial_pair polynomial_identity (polynomial_constant 1))
    (4*X+1) (fun n=>by simpa using weight_nat_numeric n)) polynomial_multiply X (4*X^2+5)
    (fun n k z=>k≤n ∧ z.size≤1+(n-k)*n)
  · intro n; simp
  · intro n; simp
  · intro n k hk z hz
    change k<n at hk
    have he : n-k=(n-(k+1))+1:=by omega
    have hh:=nat_size_mul (k+1) z
    have hb : (k+1).size≤n := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    change k≤n ∧ ((k+1)*z).size≤1+(n-k)*n
    refine ⟨by omega,?_⟩
    have hbound : 1+(n-k)*n=1+(n-(k+1))*n+n := by rw [he]; ring
    rw [hbound]
    omega
  · intro n k z hz
    have hh:=weight_nat_le z
    have hm:=Nat.mul_le_mul_right n (Nat.sub_le n k)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_pow,id_eq]
    nlinarith

omit [Codec A] [Codec B] [Codec C] in
lemma pair_nat_weight_numeric (x : ℕ×ℕ) : weight x≤4*(x.1+x.2)+3 := by
  have h1:=weight_nat_numeric x.1
  have h2:=weight_nat_numeric x.2
  rw [←Prod.eta x,weight_prod]
  omega
omit [Codec A] [Codec B] [Codec C] in
lemma natChoose_numeric_work : WorkBound natChoose (fun x=>x.1+x.2) := by
  have ht : ∀ {f : ℕ×ℕ → ℕ} {F : Realizer f},PolynomialTime F → WorkBound F (fun x=>x.1+x.2) :=
    fun h=>work_of_polynomial h (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)
  have hb : ∀ {f : ℕ×ℕ → Bool} {F : Realizer f},PolynomialTime F → WorkBound F (fun x=>x.1+x.2) :=
    fun h=>work_of_polynomial h (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)
  have hpair : ∀ {f g : ℕ×ℕ → ℕ} {F : Realizer f} {G : Realizer g},
      WorkBound F (fun x=>x.1+x.2) → WorkBound G (fun x=>x.1+x.2) → WorkBound (pair F G) (fun x=>x.1+x.2) :=
    fun h1 h2=>work_pair h1 h2 (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)
  have hf : WorkBound (composition (first (A:=ℕ) (B:=ℕ)) factorial) (fun x=>x.1+x.2) :=
    work_composition (ht polynomial_first) factorial_numeric_work X (fun x=>by simp only [Polynomial.eval_X,id_eq]; omega)
  have hs : WorkBound (composition (second (A:=ℕ) (B:=ℕ)) factorial) (fun x=>x.1+x.2) :=
    work_composition (ht polynomial_second) factorial_numeric_work X (fun x=>by simp only [Polynomial.eval_X,id_eq]; omega)
  have hd : WorkBound (composition subtract factorial) (fun x=>x.1+x.2) :=
    work_composition (ht polynomial_subtract) factorial_numeric_work X (fun x=>by simp only [Polynomial.eval_X,id_eq]; omega)
  unfold natChoose
  apply work_congr
  exact work_choose
    (hb (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less))
    (work_then_polynomial (hpair hf (work_then_polynomial (hpair hs hd) polynomial_multiply)) polynomial_quotient)
    (work_choose (hb (polynomial_composition (polynomial_pair polynomial_first polynomial_second) polynomial_less))
      (ht (polynomial_constant 0)) (ht (polynomial_constant 1)) (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x))
    (4*X+3) (fun x=>by simpa using pair_nat_weight_numeric x)

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_TreePolynomialSums
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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

lemma pairingStep_fold_size (as : List ℕ) (a b M : ℕ) (ha : ∀ i∈as,i.size≤M) :
    max (as.foldl (fun z i=>pairingStep (i,z)) (a,b)).1.size
      (as.foldl (fun z i=>pairingStep (i,z)) (a,b)).2.size ≤
      max a.size b.size+as.length*(M+2) := by
  induction as generalizing a b with
  | nil => simp
  | cons i as ih =>
    have hi:=ha i (by simp)
    have hsmall:=nat_size_add i 1
    have he : Nat.size 1=1:=by decide
    have hm:=nat_size_mul (i+1) a
    have hmax : max i.size 1≤M+1:=max_le (by omega) (by omega)
    have hstep : max b.size ((i+1)*a).size ≤ max a.size b.size+(M+2) := by
      rw [he] at hsmall
      have h1:=le_max_left a.size b.size
      have h2:=le_max_right a.size b.size
      exact max_le (by omega) (by omega)
    have ht:=ih b ((i+1)*a) (fun j h=>ha j (by simp [h]))
    simp only [pairingStep] at ht
    simp only [List.foldl_cons,List.length_cons,pairingStep]
    nlinarith
lemma polynomial_pairingFold : PolynomialTime (fold
    (pair (composition (second (A:=ℕ) (B:=ℕ×ℕ)) second)
      (composition (pair (composition first successor) (composition second first)) multiply))) := by
  apply polynomial_fold (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_successor)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_multiply)) (8*X+8*X*(X+2)+3)
  rintro as ⟨a,b⟩ pre post he
  let S:=weight (as,(a,b))
  have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have ha : ∀ i∈pre,i.size≤S := by
    intro i hi
    exact (size_le_weight i).trans ((weight_mem (as := as) (by simp [he,hi])).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have hab : max a.size b.size≤S := by
    have hh:=size_le_weight a
    have hh':=size_le_weight b
    apply max_le <;> dsimp [S] <;> simp only [weight_prod] <;> omega
  let z:=pre.foldl (fun z i=>pairingStep (i,z)) (a,b)
  have hm:=pairingStep_fold_size pre a b S ha
  have h1:=weight_nat_le z.1
  have h2:=weight_nat_le z.2
  have h3:=le_max_left z.1.size z.2.size
  have h4:=le_max_right z.1.size z.2.size
  change max z.1.size z.2.size≤_ at hm
  have hmul:=Nat.mul_le_mul_right (S+2) hp
  change weight z≤_
  rw [←Prod.eta z,weight_prod]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤8*S+8*S*(S+2)+3
  nlinarith
lemma pairingNumber_numeric_work : WorkBound pairingNumber id := by
  unfold pairingNumber
  apply work_congr
  apply work_then_polynomial _ polynomial_first
  apply work_then_polynomial _ polynomial_pairingFold
  exact work_pair range_numeric_work
    (work_of_polynomial (polynomial_constant (1,0)) (4*X+1) (fun n=>by simpa using weight_nat_numeric n))
    (4*X+1) (fun n=>by simpa using weight_nat_numeric n)
lemma polynomial_boundedPairingNumber {A : Type} [Codec A] {f : A → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,f a≤p.eval (weight a)) : PolynomialTime (composition F pairingNumber) :=
  work_composition hF pairingNumber_numeric_work p hn
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeFastChoose
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

lemma fastChoose_work : WorkBound fastChoose (fun x=>x.1+weight x) := by
  obtain ⟨p,hp⟩:=natChoose_numeric_work
  let F := composition (pair (second (A:=ℕ) (B:=ℕ)) first) leNat
  have hF : PolynomialTime F := polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_leNat
  obtain ⟨q,hq⟩:=hF
  obtain ⟨r,hr⟩:=polynomial_constant (A:=ℕ×ℕ) (0:ℕ)
  refine ⟨p.comp (2*X)+q+r+7*X+18,fun x=>?_⟩
  have hq':=(hq x).trans (polynomial_eval_monotone q (show weight x≤x.1+weight x by omega))
  have hr':=(hr x).trans (polynomial_eval_monotone r (show weight x≤x.1+weight x by omega))
  simp only [Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change F.cost x+(if decide (x.2≤x.1) then natChoose.cost x else (constant (A:=ℕ×ℕ) (0:ℕ)).cost x)+
    7*weight x+18+weight (x.1.choose x.2)≤_
  simp only [decide_eq_true_eq]
  by_cases h : x.2≤x.1
  · rw [ite_eq_left h]
    have hp':=(hp x).trans (polynomial_eval_monotone p (show x.1+x.2≤2*(x.1+weight x) by omega))
    dsimp only at hq' hr' hp'
    omega
  · rw [ite_eq_right h,Nat.choose_eq_zero_of_lt (show x.1<x.2 by omega)]
    dsimp only at hq' hr'
    omega

lemma polynomial_boundedFastChoose {A : Type} [Codec A] {f : A → ℕ×ℕ} {F : Realizer f}
    (hF : PolynomialTime F) (p : Polynomial ℕ)
    (hn : ∀ a,(f a).1≤p.eval (weight a)) : PolynomialTime (composition F fastChoose) := by
  obtain ⟨q,hq⟩:=hF
  apply work_composition ⟨q,hq⟩ fastChoose_work (p+q)
  intro a
  have h1:=hn a
  have h2:=hq a
  simp only [Polynomial.eval_add]
  omega
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastDPEntry
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

lemma polynomial_readFast : PolynomialTime readFast := by
  unfold readFast
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_composition _ (polynomial_getDFast 0)
  apply polynomial_pair _ (polynomial_snd polynomial_second)
  apply polynomial_composition _ (polynomial_getDFast [])
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_totalFlag : PolynomialTime totalFlagRealizer := by
  unfold totalFlagRealizer
  apply polynomial_composition _ polynomial_membership
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma polynomial_countWith {A B : Type} [Codec A] [Codec B] {p : A×B → Bool}
    {P : Realizer p} (hP : PolynomialTime P) : PolynomialTime (countWith P) := by
  unfold countWith countTrue
  exact polynomial_congr _ (polynomial_composition (polynomial_mapWith hP)
    (polynomial_composition (polynomial_filter polynomial_identity) polynomial_listLength))

lemma polynomial_privateFlag : PolynomialTime privateFlagRealizer := by
  unfold privateFlagRealizer
  apply polynomial_composition _ polynomial_boolAnd
  apply polynomial_pair _ polynomial_totalFlag
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma polynomial_sharedFlag : PolynomialTime sharedFlagRealizer := by
  unfold sharedFlagRealizer
  exact polynomial_composition (polynomial_pair polynomial_totalFlag
    (polynomial_composition polynomial_privateFlag polynomial_boolNot)) polynomial_boolAnd
lemma polynomial_privateNumber : PolynomialTime privateNumberRealizer := by
  unfold privateNumberRealizer
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_countWith polynomial_privateFlag)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma polynomial_sharedNumber : PolynomialTime sharedNumberRealizer := by
  unfold sharedNumberRealizer
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_countWith polynomial_sharedFlag)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma polynomial_totalNumber : PolynomialTime totalNumberRealizer := by
  unfold totalNumberRealizer
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_countWith polynomial_totalFlag)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma polynomial_trim : PolynomialTime trimRealizer := by
  unfold trimRealizer
  apply polynomial_composition _ (polynomial_filterWith (polynomial_composition polynomial_totalFlag polynomial_boolNot))
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_contextFast : PolynomialTime contextFast := by
  unfold contextFast
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  apply polynomial_pair
  · apply polynomial_composition _ (polynomial_getDFast (false,0))
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
  · apply polynomial_pair (polynomial_fst polynomial_second)
    apply polynomial_pair (polynomial_snd polynomial_second)
    apply polynomial_pair
    · apply polynomial_composition _ polynomial_privateNumber
      ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
    · apply polynomial_pair
      · apply polynomial_composition _ polynomial_sharedNumber
        ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
      · apply polynomial_composition _ polynomial_totalNumber
        ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma sharedNumber_le (bs : Bags) (l : ℕ) : sharedNumber bs l≤bs.length := List.length_filter_le _ _
lemma polynomial_rawTerm : PolynomialTime rawTermRealizer := by
  unfold rawTermRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  have hc:=polynomial_contextFast
  have hr:=polynomial_readFast
  have hch : PolynomialTime (composition
      (pair (composition first.fst contextFast).snd.snd.snd.snd.fst (second (A:=RawCtx×ℕ) (B:=ℕ))) fastChoose) := by
    apply polynomial_boundedFastChoose (by dsimp only [Realizer.fst, Realizer.snd]; ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))) X
    intro x
    simp only [Polynomial.eval_X]
    change sharedNumber x.1.1.1.1 x.1.1.2.1≤weight x
    exact (sharedNumber_le _ _).trans ((list_length_le_weight _).trans (by
      rcases x with ⟨⟨⟨⟨bs,ps⟩,⟨l,t⟩⟩,r⟩,k⟩
      simp only [weight_prod]; omega))
  dsimp only [Realizer.fst, Realizer.snd] at hch
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_rawEntry : PolynomialTime rawEntryRealizer := by
  unfold rawEntryRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  have hc:=polynomial_contextFast
  have hr:=polynomial_readFast
  have ht:=polynomial_rawTerm
  have hs:=polynomial_listSum
  have hks : PolynomialTime (composition (composition
      (composition (first (A:=RawCtx) (B:=ℕ×ℕ)) contextFast).snd.snd.snd.snd.fst successor) range) := by
    apply polynomial_boundedRange (by
      have := polynomial_successor
      dsimp only [Realizer.fst, Realizer.snd]
      ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))) (X+1)
    intro x
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
    change sharedNumber x.1.1.1 x.1.2.1+1≤weight x+1
    have hh:=sharedNumber_le x.1.1.1 x.1.2.1
    have hw:=list_length_le_weight x.1.1.1
    rcases x with ⟨⟨⟨bs,ps⟩,⟨l,t⟩⟩,ar⟩
    simp only [weight_prod]
    dsimp only at hh hw
    omega
  dsimp only [Realizer.fst, Realizer.snd] at hks
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeClippedDP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

lemma polynomial_nVertices : PolynomialTime nVerticesRealizer := by unfold nVerticesRealizer; exact polynomial_composition (polynomial_fst polynomial_first) polynomial_listLength
lemma polynomial_nLabels : PolynomialTime nLabelsRealizer := by unfold nLabelsRealizer; exact polynomial_composition (polynomial_snd polynomial_first) polynomial_listLength
lemma polynomial_nPlan : PolynomialTime nPlanRealizer := by unfold nPlanRealizer; exact polynomial_composition polynomial_second polynomial_listLength
lemma polynomial_BInitial : PolynomialTime BInitialRealizer :=
  polynomial_composition (polynomial_pair polynomial_nVertices polynomial_nLabels) polynomial_multiply
lemma polynomial_capBits : PolynomialTime capBitsRealizer := by
  unfold capBitsRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_successor
  apply polynomial_composition _ polynomial_add
  have := polynomial_BInitial
  have := polynomial_nVertices
  have := polynomial_nLabels
  have := polynomial_nPlan
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma input_lengths (o : CountInput) : nVertices o≤weight o ∧ nLabels o≤weight o ∧ nPlan o≤weight o := by
  refine ⟨(list_length_le_weight _).trans ((weight_fst o.1).trans (weight_fst o)),
    (list_length_le_weight _).trans ((weight_snd o.1).trans (weight_fst o)),
    (list_length_le_weight _).trans (weight_snd o)⟩
lemma BInitial_bound (o : CountInput) : BInitial o≤(weight o)^2 := by
  obtain ⟨hn,hm,_⟩:=input_lengths o
  exact (Nat.mul_le_mul hn hm).trans_eq (pow_two _).symm
lemma capBits_bound (o : CountInput) : capBits o≤(weight o)^2+(weight o)^5+1 := by
  obtain ⟨hn,hm,hL⟩:=input_lengths o
  have hB:=BInitial_bound o
  have h1:=Nat.mul_le_mul hn hL
  have h2:=Nat.mul_le_mul (Nat.pow_le_pow_left hB 2) hm
  calc
    _ ≤ weight o*weight o+((weight o)^2)^2*weight o+1 := by unfold capBits; omega
    _ = _ := by ring

lemma polynomial_initialEntry : PolynomialTime initialEntryRealizer := by
  unfold initialEntryRealizer
  refine polynomial_boundedPairingNumber ?_ (X^2) ?_
  · apply polynomial_composition _ polynomial_minNat
    apply polynomial_pair (polynomial_snd polynomial_second) (polynomial_composition polynomial_first polynomial_BInitial)
  · intro x
    simp only [Polynomial.eval_pow,Polynomial.eval_X]
    exact (min_le_right _ _).trans ((BInitial_bound x.1).trans (Nat.pow_le_pow_left (weight_fst x) 2))
lemma polynomial_initialFast : PolynomialTime initialFast := by
  unfold initialFast
  apply polynomial_congr
  exact polynomial_grid polynomial_nLabels polynomial_BInitial polynomial_initialEntry X (X^2)
    (fun o=>by simpa using (input_lengths o).2.1) (fun o=>by simpa using BInitial_bound o)

lemma polynomial_updateRows : PolynomialTime updateRowsRealizer :=
  polynomial_composition (polynomial_fst polynomial_first) polynomial_nLabels
lemma polynomial_updateColumns : PolynomialTime updateColumnsRealizer := by
  unfold updateColumnsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_fst polynomial_first) polynomial_nVertices)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition (polynomial_fst polynomial_first) polynomial_nPlan)) polynomial_minNat)) polynomial_multiply
lemma update_dimensions (x : UpdateInput) : updateRows x≤weight x ∧ updateColumns x≤(weight x)^2 := by
  have hwo:weight x.1.1≤weight x := (weight_fst x.1).trans (weight_fst x)
  obtain ⟨hn,hm,hL⟩:=input_lengths x.1.1
  refine ⟨hm.trans hwo,?_⟩
  exact (Nat.mul_le_mul (hn.trans hwo) ((min_le_right _ _).trans (hL.trans hwo))).trans_eq (pow_two _).symm

lemma polynomial_cappedEntry : PolynomialTime cappedEntryRealizer := by
  unfold cappedEntryRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  apply polynomial_composition _ polynomial_clip
  apply polynomial_pair
  · apply polynomial_composition _ polynomial_capBits
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
  · apply polynomial_composition _ polynomial_rawEntry
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_cappedUpdate : PolynomialTime cappedUpdateRealizer :=
  polynomial_grid polynomial_updateRows polynomial_updateColumns polynomial_cappedEntry X (X^2)
    (fun x=>by simpa using (update_dimensions x).1) (fun x=>by simpa using (update_dimensions x).2)

end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeClippedRun
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableDP
open TreeTyped Polynomial

lemma polynomial_cappedStep : PolynomialTime cappedStepRealizer := by
  unfold cappedStepRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_trim
  have := polynomial_cappedUpdate
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma cappedUpdate_weight (x : UpdateInput) : weight (cappedUpdate x)≤tableWeightBound x.1.1 := by
  unfold cappedUpdate tabulate
  have hw:=weight_map_bound (as:=List.range (updateRows x))
    (f:=fun a=>(List.range (updateColumns x+1)).map fun r=>cappedEntry (x,(a,r)))
    (N:=1+(nVertices x.1.1*nPlan x.1.1+1)*(4*capBits x.1.1+2)) (by
      intro a _
      have hh:=weight_map_bound (as:=List.range (updateColumns x+1))
        (f:=fun r=>cappedEntry (x,(a,r))) (N:=4*capBits x.1.1+1) (by
          intro r _
          have hb:=clip_size (capBits x.1.1) (rawEntry (x.1.2,(a,r)))
          have hw:=weight_nat_le (cappedEntry (x,(a,r)))
          change (cappedEntry (x,(a,r))).size ≤ capBits x.1.1 at hb
          omega)
      simp only [List.length_range] at hh
      simp only [Nat.add_assoc, Nat.reduceAdd] at hh
      have hdim : updateColumns x≤nVertices x.1.1*nPlan x.1.1 := Nat.mul_le_mul_left _ (min_le_right _ _)
      have hm:=Nat.mul_le_mul_right (4*capBits x.1.1+2) (Nat.add_le_add_right hdim 1)
      exact hh.trans (by omega))
  simp only [List.length_range,updateRows] at hw
  unfold tableWeightBound
  dsimp only
  exact hw.trans_eq (by ring)
lemma tableWeightBound_polynomial (o : CountInput) :
    tableWeightBound o≤1+weight o*(2+((weight o)^2+1)*(4*((weight o)^2+(weight o)^5+1)+2)) := by
  obtain ⟨hn,hm,hL⟩:=input_lengths o
  have hb:=capBits_bound o
  have hprod : nVertices o*nPlan o≤(weight o)^2 := by simpa only [pow_two] using Nat.mul_le_mul hn hL
  unfold tableWeightBound
  exact Nat.add_le_add_left (Nat.mul_le_mul hm (Nat.add_le_add_left (Nat.mul_le_mul
    (Nat.add_le_add_right hprod 1) (by omega)) 2)) 1

lemma cappedFold_invariant (ls : List ℕ) (z : CappedState) :
    let r:=ls.foldl (fun z l=>cappedStep (l,z)) z
    r.1=z.1 ∧ r.2.1≤z.2.1 ∧ r.2.2.1.Sublist z.2.2.1 ∧
      weight r.2.2.2≤weight z.2.2.2+tableWeightBound z.1 := by
  induction ls generalizing z with
  | nil => exact ⟨rfl,le_rfl,List.Sublist.refl _,Nat.le_add_right _ _⟩
  | cons l ls ih =>
    have h:=ih (cappedStep (l,z))
    dsimp only at h ⊢
    simp only [List.foldl_cons]
    refine ⟨h.1,h.2.1.trans (Nat.sub_le _ _),h.2.2.1.trans (List.filter_sublist (p:=fun b=>!(totalFlag (l,b))) (l:=z.2.2.1)),?_⟩

    cases ls with
    | nil =>
      change weight (cappedUpdate _)≤_
      exact (cappedUpdate_weight _).trans (Nat.le_add_left _ _)
    | cons l' ls =>

      clear ih h
      have hs : ∀ (as : List ℕ) (v : CappedState) (j : ℕ),
          weight ((as.foldl (fun z l=>cappedStep (l,z)) (cappedStep (j,v))).2.2.2)≤tableWeightBound v.1 := by
        intro as
        induction as with
        | nil => intro v j; exact cappedUpdate_weight _
        | cons a as ih =>
          intro v j
          simp only [List.foldl_cons]
          exact ih (cappedStep (j,v)) a
      exact (hs ls (cappedStep (l,z)) l').trans (Nat.le_add_left _ _)

lemma weight_cappedState (z : CappedState) : weight z=3+weight z.1+weight z.2.1+weight z.2.2.1+weight z.2.2.2 := by
  rcases z with ⟨o,k,bs,t⟩
  simp only [weight_prod]
  omega

lemma polynomial_cappedFold : PolynomialTime (fold cappedStepRealizer) := by
  let P : Polynomial ℕ := 1+X*(2+(X^2+1)*(4*(X^2+X^5+1)+2))
  apply polynomial_fold polynomial_cappedStep (8*X+10+P)
  intro ls z pre _ _
  let S:=weight (ls,z)
  let r:=pre.foldl (fun z l=>cappedStep (l,z)) z
  have hi:=cappedFold_invariant pre z
  change r.1=z.1 ∧ r.2.1≤z.2.1 ∧ r.2.2.1.Sublist z.2.2.1 ∧ weight r.2.2.2≤weight z.2.2.2+tableWeightBound z.1 at hi
  have hz : weight z≤S := weight_snd (ls,z)
  have ho : weight z.1≤S := (weight_fst z).trans hz
  have hr : weight z.2.1≤S := (weight_fst z.2).trans ((weight_snd z).trans hz)
  have hb : weight z.2.2.1≤S := (weight_fst z.2.2).trans ((weight_snd z.2).trans ((weight_snd z).trans hz))
  have ht : weight z.2.2.2≤S := (weight_snd z.2.2).trans ((weight_snd z.2).trans ((weight_snd z).trans hz))
  have h0 : weight r.1≤S := by rw [hi.1]; exact ho
  have h1 : weight r.2.1≤4*S+1 := by
    have hh:=weight_nat_le r.2.1
    have hh':=(Nat.size_le_size hi.2.1).trans (size_le_weight z.2.1)
    omega
  have h2 : weight r.2.2.1≤S := (weight_sublist hi.2.2.1).trans hb
  have htable:tableWeightBound z.1≤P.eval S := by
    apply (tableWeightBound_polynomial z.1).trans
    simpa only [P, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat, Polynomial.eval_pow, Polynomial.eval_X] using polynomial_eval_monotone P ho
  change weight r≤_
  rw [weight_cappedState r]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change _≤8*S+10+P.eval S
  omega

lemma polynomial_finishFast : PolynomialTime finishFast := by
  unfold finishFast
  apply polynomial_composition _ polynomial_listProd
  apply polynomial_composition
  · apply polynomial_pair polynomial_second
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_nLabels) X
    intro x
    simp only [Function.comp_apply,Polynomial.eval_X]
    exact (input_lengths x.1).2.1.trans (weight_fst x)
  · apply polynomial_mapWith
    apply polynomial_composition _ polynomial_readFast
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_cappedCount : PolynomialTime cappedCountRealizer := by
  unfold cappedCountRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_finishFast
  apply polynomial_pair polynomial_identity
  apply polynomial_composition _ (polynomial_snd (polynomial_snd polynomial_second))
  apply polynomial_composition _ polynomial_cappedFold
  apply polynomial_pair polynomial_second
  apply polynomial_pair polynomial_identity
  apply polynomial_pair polynomial_nPlan
  exact polynomial_pair (polynomial_fst polynomial_first) polynomial_initialFast
end MatchingFPRAS.ExecutableDP

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastUnit
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

lemma polynomial_skipFast : PolynomialTime skipFast := by
  unfold skipFast skipRealizer
  apply polynomial_congr
  exact polynomial_choose polynomial_less polynomial_first
    (polynomial_composition polynomial_first polynomial_successor)

lemma polynomial_residualFast : PolynomialTime residualFast := by
  unfold residualFast Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  apply polynomial_composition
  · apply polynomial_pair polynomial_identity
    apply polynomial_boundedRange (by ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))) X
    intro x
    simpa only [Polynomial.eval_X] using (Nat.sub_le x.1.length 2).trans ((list_length_le_weight x.1).trans (weight_fst x))
  · apply polynomial_mapWith
    apply polynomial_composition _ (polynomial_getDFast [])
    have := polynomial_skipFast
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_validFast : PolynomialTime validFast := by
  unfold validFast Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_getDFast ([] : Bag)
  have := polynomial_membership
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_fastBranch : PolynomialTime fastBranchRealizer := by
  unfold fastBranchRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  apply polynomial_composition _ polynomial_cappedCount
  have := polynomial_residualFast
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_fastEdgeCount : PolynomialTime fastEdgeCountRealizer := by
  unfold fastEdgeCountRealizer
  apply polynomial_congr
  exact polynomial_choose polynomial_validFast
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_fst polynomial_second)) polynomial_fastBranch)
    (polynomial_constant 0)

lemma polynomial_fastProbability : PolynomialTime fastProbabilityRealizer := by
  unfold fastProbabilityRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_pair _ (polynomial_composition polynomial_first polynomial_cappedCount)
  apply polynomial_composition _ polynomial_fastEdgeCount
  apply polynomial_pair polynomial_first
  apply polynomial_composition _ polynomial_division
  exact polynomial_pair polynomial_second
    (polynomial_composition (polynomial_snd (polynomial_fst polynomial_first)) polynomial_listLength)

lemma polynomial_fastProbabilities : PolynomialTime fastProbabilitiesRealizer := by
  unfold fastProbabilitiesRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_mapWith polynomial_fastProbability)
  apply polynomial_pair polynomial_identity
  apply polynomial_boundedRange (by ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))) (X^2)
  intro x
  simp only [Function.comp_apply,Polynomial.eval_pow,Polynomial.eval_X]
  simpa only [pow_two] using Nat.mul_le_mul ((list_length_le_weight x.1.1).trans ((weight_fst x.1).trans (weight_fst x)))
      ((list_length_le_weight x.1.2).trans ((weight_snd x.1).trans (weight_fst x)))

lemma polynomial_fastDraw : PolynomialTime fastDrawRealizer := by
  unfold fastDrawRealizer decodeIndexRealizer
  apply polynomial_congr
  apply polynomial_composition _ polynomial_division
  apply polynomial_pair _ (polynomial_composition (polynomial_snd (polynomial_fst polynomial_first)) polynomial_listLength)
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_fastProbabilities) polynomial_second) ExecutableChoice.polynomial_chooseBitsFast
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeCappedAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

lemma polynomial_assembleAtFast : PolynomialTime assembleAtFast := by
  unfold assembleAtFast Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have : PolynomialTime unskipRealizer := by
    unfold unskipRealizer
    apply polynomial_congr
    exact polynomial_choose polynomial_less polynomial_first (polynomial_composition polynomial_first polynomial_predecessor)
  have := polynomial_successor
  have := polynomial_getDFast ((0,0) : ℕ×ℕ)
  have := polynomial_skipFast
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_capacity : PolynomialTime capacityRealizer := by
  unfold capacityRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_clippedAt : PolynomialTime clippedAtRealizer := by
  unfold clippedAtRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_assembleAtFast
  have := polynomial_capacity
  have := polynomial_minNat
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_clippedAssemble : PolynomialTime clippedAssembleRealizer := by
  unfold clippedAssembleRealizer Realizer.fst
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_mapWith polynomial_clippedAt)
  apply polynomial_pair polynomial_identity
  apply polynomial_boundedRange (by have := polynomial_minNat; ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))) (X+2)
  intro x
  simpa only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat] using
    (min_le_right (x.2.1.1+2) (x.1.1.1.length+2)).trans
    (Nat.add_le_add_right ((list_length_le_weight _).trans ((weight_fst x.1.1).trans ((weight_fst x.1).trans (weight_fst x)))) 2)
lemma clippedAssemble_weight (ctx : Context) (f : Frame) (r : Result) :
    weight (clippedAssemble (ctx,(f,r)))≤64*(weight ctx+1)^2 := by
  have hh :=weight_map_bound (as:=List.range (min (f.1+2) (ctx.1.1.length+2)))
    (f:=fun i=>clippedAt ((ctx,(f,r)),i)) (N:=8*capacity ctx+3) (by
      intro i hi
      let z:=assembleAt ((f,r),i)
      have h1:=weight_nat_numeric (min z.1 (capacity ctx))
      have h2:=weight_nat_numeric (min z.2 (capacity ctx))
      have h3:=min_le_right z.1 (capacity ctx)
      have h4:=min_le_right z.2 (capacity ctx)
      change weight (min z.1 (capacity ctx),min z.2 (capacity ctx))≤_
      rw [weight_prod]
      omega)
  have hn : ctx.1.1.length≤weight ctx := (list_length_le_weight _).trans ((weight_fst ctx.1).trans (weight_fst ctx))
  have hm : ctx.1.2.length≤weight ctx := (list_length_le_weight _).trans ((weight_snd ctx.1).trans (weight_fst ctx))
  have hc : capacity ctx≤2*weight ctx+2 := by unfold capacity; omega
  have hl : min (f.1+2) (ctx.1.1.length+2)≤weight ctx+2 := (min_le_right _ _).trans (by omega)
  simp only [List.length_range] at hh
  have hp :=Nat.mul_le_mul hl (show 8*capacity ctx+3+1≤16*weight ctx+20 by omega)
  change weight (clippedAssemble (ctx,(f,r)))≤_ at hh
  nlinarith

lemma polynomial_assemblyFoldStep : PolynomialTime assemblyFoldStepRealizer := by
  unfold assemblyFoldStepRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_clippedAssemble
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))
lemma assemblyFold_fst (pre : List Frame) (ctx : Context) (r : Result) :
    (pre.foldl (fun z f=>assemblyFoldStep (f,z)) (ctx,r)).1=ctx := by
  induction pre generalizing r with
  | nil => rfl
  | cons f pre ih => exact ih _
lemma assemblyFold_weight (pre : List Frame) (ctx : Context) (r : Result) :
    weight (pre.foldl (fun z f=>assemblyFoldStep (f,z)) (ctx,r)).2 ≤
      weight r+pre.length*(64*(weight ctx+1)^2) := by
  induction pre generalizing r with
  | nil => simp
  | cons f pre ih =>
    have hh:=ih (clippedAssemble (ctx,(f,r)))
    have hw:=clippedAssemble_weight ctx f r
    change weight (pre.foldl _ (ctx,clippedAssemble (ctx,(f,r)))).2≤_
    simp only [List.length_cons]
    nlinarith
lemma polynomial_assemblyFold : PolynomialTime (fold assemblyFoldStepRealizer) := by
  apply polynomial_fold polynomial_assemblyFoldStep (70*(X+1)^3)
  rintro fs ⟨ctx,r⟩ pre post he
  let S:=weight (fs,(ctx,r))
  have hp:pre.length≤S := (list_length_le_weight _).trans ((weight_prefix he).trans (weight_fst (fs,(ctx,r))))
  have hc:weight ctx≤S := (weight_fst (ctx,r)).trans (weight_snd (fs,(ctx,r)))
  have hr:weight r≤S := (weight_snd (ctx,r)).trans (weight_snd (fs,(ctx,r)))
  have hh:=assemblyFold_weight pre ctx r
  have hf:=assemblyFold_fst pre ctx r
  rw [←Prod.eta (pre.foldl (fun z f=>assemblyFoldStep (f,z)) (ctx,r)),weight_prod,hf]
  have hm:= Nat.mul_le_mul hp (show 64*(weight ctx+1)^2 ≤64*(S+1)^2 by gcongr)
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤70*(S+1)^3
  nlinarith

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]

omit [BEq A] [LawfulBEq A] in
lemma polynomial_indexStep [BEq A] [LawfulBEq A] {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (indexStepRealizer E) := by
  unfold indexStepRealizer
  apply polynomial_congr
  exact polynomial_pair (polynomial_fst polynomial_second)
    (polynomial_choose (polynomial_composition (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hE)
      (polynomial_constant 0) (polynomial_composition (polynomial_snd polynomial_second) polynomial_successor))
omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_first [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (i : ℕ) :
    (xs.foldl (fun z x=>indexStep (x,z)) (a,i)).1=a := by
  induction xs generalizing i with
  | nil=>rfl
  | cons x xs ih=>exact ih _
omit [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A] in
lemma indexStep_fold_le [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    (xs : List A) (a : A) (i : ℕ) :
    (xs.foldl (fun z x=>indexStep (x,z)) (a,i)).2 ≤ i+xs.length := by
  induction xs generalizing i with
  | nil=>simp
  | cons x xs ih=>
    have h:=ih (if a=x then 0 else i+1)
    change (xs.foldl _ (a,if a=x then 0 else i+1)).2 ≤ _
    have hb : (if a=x then 0 else i+1) ≤ i+1 := by split_ifs <;> omega
    simpa only [List.length_cons] using h.trans (by omega)
lemma polynomial_indexFold {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (fold (indexStepRealizer E)) := by
  apply polynomial_fold (polynomial_indexStep hE) (10*X+20)
  rintro xs ⟨a,i⟩ pre post he
  have hp:=(list_length_le_weight pre).trans (weight_prefix he)
  have hb:=indexStep_fold_le pre a i
  have hi:=Nat.size_le_size hb
  have hs:=nat_size_add i pre.length
  have hn : pre.length.size ≤ pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [←Prod.eta (pre.foldl _ (a,i)),weight_prod,indexStep_fold_first]
  have hw:=weight_nat_le (pre.foldl (fun z x=>indexStep (x,z)) (a,i)).2
  have ha:=weight_pos a
  have hn':=size_le_weight i
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma polynomial_indexOf {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (indexOf E) := by
  unfold indexOf
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_reverse)
      (polynomial_pair polynomial_first (polynomial_constant 0)))
      (polynomial_indexFold hE)) polynomial_second
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastDescent
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP Polynomial

lemma polynomial_fastSelected : PolynomialTime fastSelectedRealizer := by
  unfold fastSelectedRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_fastDraw
  have := polynomial_getDFast ([] : List Bool)
  have := polynomial_predecessor
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_nextContextFast : PolynomialTime nextContextFast := by
  unfold nextContextFast
  apply polynomial_congr
  have := polynomial_residualFast
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma polynomial_fastStep : PolynomialTime fastStepRealizer := by
  unfold fastStepRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_fastSelected
  have := polynomial_nextContextFast
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))

lemma chooseBits_le_length (x : List TreeFraction.Fraction×List Bool) : ExecutableChoice.chooseBits x≤x.1.length := by
  exact TreeTyped.listMin_le_default _ _
lemma fastDraw_bounds (x : Context×List Bool) :
    (fastDraw x).1≤x.1.1.1.length*x.1.1.2.length ∧ (fastDraw x).2≤x.1.1.1.length*x.1.1.2.length := by
  have h:=chooseBits_le_length (fastProbabilities x.1,x.2)
  simp only [fastProbabilities,List.length_map,List.length_range] at h
  exact ⟨(Nat.div_le_self _ _).trans h,(Nat.mod_le _ _).trans h⟩
lemma fastSelected_bounds (x : Context×Bits) :
    (fastSelected x).1≤x.1.1.1.length*x.1.1.2.length ∧ (fastSelected x).2≤x.1.1.1.length*x.1.1.2.length :=
  fastDraw_bounds _
lemma residual_length (bs : Bags) (b : ℕ) : (residual (bs,b)).length=bs.length-2 := by
  simp [residual]
lemma residual_mem {bs : Bags} {b : ℕ} {a : Bag} (ha : a∈residual (bs,b)) : a∈bs := by
  simp only [residual,List.mem_map,List.mem_range] at ha
  obtain ⟨i,hi,rfl⟩:=ha
  have hj : skip (i,b)<bs.length := by simp only [skip]; split_ifs <;> omega
  rw [List.getD_eq_getElem _ _ hj]
  exact List.getElem_mem _

lemma descent_init (a : Context×Bits) : DescentInvariant a a.1.1.1.length (a.1,(a.2,[])) := by
  simp only [DescentInvariant,List.length_nil,Nat.zero_add,List.not_mem_nil,IsEmpty.forall_iff,le_refl,implies_true,true_and,and_true]
  exact fun b h=>h
lemma descent_step (a : Context×Bits) (k : ℕ) (z : State) (hz : DescentInvariant a (k+1) z) :
    DescentInvariant a k (fastStep z) := by
  obtain ⟨hl,hb,hp,ho,ht,hf,hm⟩:=hz
  by_cases hn : 2≤z.1.1.1.length
  · rw [fastStep,ite_eq_left hn]
    have hc:=fastSelected_bounds (z.1,z.2.1)
    rw [hp] at hc
    have hmul:=Nat.mul_le_mul_right a.1.1.2.length hl
    refine ⟨?_,?_,hp,ho,ht,?_,?_⟩
    · change (residual (z.1.1.1,(fastSelected (z.1,z.2.1)).1)).length≤_
      rw [residual_length]; omega
    · intro b hb'
      exact hb b (residual_mem hb')
    · change ( _ :: z.2.2).length+k≤_
      simp only [List.length_cons]; omega
    · intro f hh
      rcases List.mem_cons.mp hh with rfl | hh
      · exact ⟨(Nat.sub_le _ _).trans hl,hc.1.trans hmul,hc.2.trans hmul⟩
      · exact hm f hh
  · rw [fastStep,ite_eq_right hn]
    exact ⟨hl,hb,hp,ho,ht,by omega,hm⟩

lemma descent_weight (a : Context×Bits) (k : ℕ) (z : State) (hz : DescentInvariant a k z) :
    weight z≤ 20*(weight a+1)^3 := by
  obtain ⟨hl,hb,hp,ho,ht,hf,hm⟩:=hz
  let S:=weight a
  have hn : a.1.1.1.length≤S := (list_length_le_weight _).trans ((weight_fst a.1.1).trans ((weight_fst a.1).trans (weight_fst a)))
  have hn' : a.1.1.2.length≤S := (list_length_le_weight _).trans ((weight_snd a.1.1).trans ((weight_fst a.1).trans (weight_fst a)))
  have hbn:weight z.1.1.1≤S*(S+1)+1 := by
    have hh:=weight_map_bound (as:=z.1.1.1) (f:=id) (N:=S) (fun b hh=>(weight_mem (hb b hh)).trans ((weight_fst a.1.1).trans ((weight_fst a.1).trans (weight_fst a))))
    simpa only [List.map_id] using hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right (S+1) (hl.trans hn)) 1)
  have hmfn:weight z.2.2≤S*(8*S*S+4*S+6)+1 := by
    have hh:=weight_map_bound (as:=z.2.2) (f:=id) (N:=8*S*S+4*S+5) (by
      intro f hh
      obtain ⟨h1,h2,h3⟩:=hm f hh
      have hm:=Nat.mul_le_mul hn hn'
      have hf1:=weight_nat_numeric f.1
      have hf2:=weight_nat_numeric f.2.1
      have hf3:=weight_nat_numeric f.2.2
      change weight f≤_
      rw [←Prod.eta f,weight_prod,←Prod.eta f.2,weight_prod]
      nlinarith)
    simp only [List.map_id] at hh
    have hlen :z.2.2.length≤S:=by omega
    have he : 8*S*S+4*S+5+1=8*S*S+4*S+6 := by omega
    rw [he] at hh
    exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hpar :weight a.1.1.2≤S := (weight_snd a.1.1).trans ((weight_fst a.1).trans (weight_fst a))
  have hplan :weight a.1.2≤S := (weight_snd a.1).trans (weight_fst a)
  have hbits :weight a.2≤S := weight_snd a
  rw [←Prod.eta z,weight_prod,←Prod.eta z.1,weight_prod,←Prod.eta z.1.1,weight_prod,←Prod.eta z.2,weight_prod,hp,ho,ht]
  change _≤20*(S+1)^3
  nlinarith

lemma polynomial_fastDescend : PolynomialTime fastDescendRealizer := by
  unfold fastDescendRealizer
  apply polynomial_congr
  apply polynomial_boundedRepeat (by dsimp only [Realizer.fst,Realizer.snd]; ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe))))
    (polynomial_composition polynomial_second polynomial_fastStep)
    X (20*(X+1)^3) DescentInvariant
  · intro a
    simpa only [Function.comp_apply,Polynomial.eval_X] using (list_length_le_weight a.1.1.1).trans ((weight_fst a.1.1).trans ((weight_fst a.1).trans (weight_fst a)))
  · exact descent_init
  · intro a k _hk z hz
    exact descent_step a k z hz
  · intro a k z hz
    simpa only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using descent_weight a k z hz
end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeFastSample
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableUnit
open TreeTyped ExecutableDP

lemma polynomial_fastSample : PolynomialTime fastSampleRealizer := by
  unfold fastSampleRealizer
  apply polynomial_congr
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_assemblyFold
  exact polynomial_pair (polynomial_snd (polynomial_snd polynomial_fastDescend))
    (polynomial_pair polynomial_first (polynomial_constant []))

open UnitRefresh.Materialized

end MatchingFPRAS.ExecutableUnit

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshIndexed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableUnit Polynomial

lemma polynomial_ordered : PolynomialTime orderedRealizer := by
  unfold orderedRealizer; apply polynomial_congr; ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_rowKey : PolynomialTime rowKeyRealizer := by
  unfold rowKeyRealizer; apply polynomial_congr
  have := polynomial_getDFast ((0,0) : ℕ×ℕ)
  have := polynomial_ordered
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_entryIndex : PolynomialTime entryIndexRealizer := by
  unfold entryIndexRealizer entryIndex
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_rowKey
  have := polynomial_indexOf (polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_matching : PolynomialTime matchingRealizer := by
  have hr : PolynomialTime (composition (composition (second (A:=List Key) (B:=Result)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
    intro x
    simpa only [eval_X,Function.comp_apply] using (list_length_le_weight x.2).trans (weight_snd x)
  unfold matchingRealizer; apply polynomial_congr
  have := polynomial_entryIndex
  have := polynomial_listFinset polynomial_natEqual polynomial_leNat
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_refresh : PolynomialTime refreshRealizer := by
  unfold refreshRealizer refresh
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_fastSample
  have := polynomial_matching
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericLadder
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder

lemma polynomial_refresh_oai : PolynomialTime refreshRealizer := by
  unfold refreshRealizer refresh Realizer.fst Realizer.snd
  have := ExecutableRefresh.polynomial_refresh
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.NumericLadder

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.NumericLadder.polynomial_refresh_oai := @OAI.MatchingFPRAS.NumericLadder.polynomial_refresh_oai
