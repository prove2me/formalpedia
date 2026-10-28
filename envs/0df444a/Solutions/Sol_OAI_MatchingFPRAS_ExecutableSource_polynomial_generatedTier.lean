-- Prove2me | solution 1 for OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedTier
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:20:33.448987+00:00
-- url     : https://prove2.me/submissions/50b469b6-a94a-4248-8446-ac60cb518cfa

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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSum
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

omit [Codec C] [Codec D] in
lemma polynomial_inl [Inhabited A] [Inhabited B] : PolynomialTime (inl (A:=A) (B:=B)) := by
  unfold inl
  apply polynomial_recode
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
omit [Codec C] [Codec D] in
lemma polynomial_inr [Inhabited A] [Inhabited B] : PolynomialTime (inr (A:=A) (B:=B)) := by
  unfold inr
  apply polynomial_recode
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_sumCases [Inhabited A] [Inhabited B] {f : C×A→D} {g : C×B→D}
    {F : Realizer f} {G : Realizer g} (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (sumCases F G) := by
  unfold sumCases
  apply polynomial_recode
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Codec C] [Codec D] in
lemma polynomial_sumEqual [Inhabited A] [Inhabited B] [DecidableEq A] [DecidableEq B]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))}
    {F : Realizer (fun x : B×B=>decide (x.1=x.2))}
    (hE : PolynomialTime E) (hF : PolynomialTime F) : PolynomialTime (sumEqual E F) := by
  unfold sumEqual
  apply polynomial_congr
  apply polynomial_sumCases
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases hE (polynomial_constant false))
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases (polynomial_constant false) hF)

end MatchingFPRAS.TreeTyped

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
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeDyadic
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction Polynomial

lemma polynomial_level : PolynomialTime levelRealizer := by
  exact polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_second
      polynomial_quotient) polynomial_bitSize) polynomial_predecessor)) polynomial_minNat
lemma polynomial_threshold : PolynomialTime thresholdRealizer := by
  unfold thresholdRealizer
  exact polynomial_pair (polynomial_composition polynomial_takeFast polynomial_bitDenominator) (polynomial_constant 1)
end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma polynomial_maximum : PolynomialTime maximumRealizer := by
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_second polynomial_first)
lemma polynomial_minimum : PolynomialTime minimumRealizer := by
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)
lemma maximum_eq (x y : Fraction) : maximum (x,y)=x ∨ maximum (x,y)=y := by
  unfold maximum; split_ifs <;> simp
lemma minimum_eq (x y : Fraction) : minimum (x,y)=x ∨ minimum (x,y)=y := by
  unfold minimum; split_ifs <;> simp
lemma maximum_weight (x y : Fraction) : weight (maximum (x,y))≤ max (weight x) (weight y) := by
  rcases maximum_eq x y with h|h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma minimum_weight (x y : Fraction) : weight (minimum (x,y))≤ max (weight x) (weight y) := by
  rcases minimum_eq x y with h|h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _
lemma maximum_fold_weight (xs : List Fraction) (z : Fraction) (B : ℕ)
    (hz : weight z≤B) (hx : ∀ x∈xs,weight x≤B) :
    weight (xs.foldl (fun z x=>maximum (x,z)) z)≤B := by
  induction xs generalizing z with
  | nil => exact hz
  | cons x xs ih =>
    apply ih _ ((maximum_weight x z).trans (max_le (hx x (by simp)) hz))
    intro x hx'; exact hx x (by simp [hx'])
lemma polynomial_maximumFold : PolynomialTime (fold maximumRealizer) := by
  apply polynomial_fold polynomial_maximum Polynomial.X
  intro xs z pre post he
  simp only [Polynomial.eval_X]
  apply maximum_fold_weight pre z _ (weight_snd (xs,z))
  intro x hx
  exact (weight_mem hx).trans ((weight_prefix he).trans (weight_fst (xs,z)))
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableBottleneck
open TreeTyped TreeFraction Polynomial

lemma polynomial_cell : PolynomialTime cellRealizer := by
  unfold cellRealizer
  have h₁:=polynomial_getDFast ([] : List Fraction)
  have h₂:=polynomial_getDFast one
  exact polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_fst polynomial_second)) h₁)
      (polynomial_snd polynomial_second)) h₂

lemma polynomial_square {A B : Type} [Codec A] [Codec B] {n : A→ℕ} {f : A×(ℕ×ℕ)→B}
    {N : Realizer n} {F : Realizer f} (hN : PolynomialTime N) (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,n a≤p.eval (weight a)) : PolynomialTime (squareRealizer N F) := by
  have hR:=polynomial_boundedRange hN p hn
  unfold squareRealizer
  dsimp only
  exact polynomial_composition (polynomial_pair polynomial_identity hR)
    (polynomial_mapWith (polynomial_composition
      (polynomial_pair polynomial_identity (polynomial_composition polynomial_first hR))
      (polynomial_mapWith (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_first)
          (polynomial_pair (polynomial_snd polynomial_first) polynomial_second)) hF))))

lemma cell_weight {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) (i j : ℕ) : weight (cell (M,(i,j)))≤B := by
  unfold cell
  dsimp only
  by_cases hi : i<M.length
  · rw [List.getD_eq_getElem _ _ hi]
    by_cases hj : j<(M[i]).length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hM _ (List.getElem_mem hi) _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]; exact h₁
  · rw [List.getD_eq_default M [] (by omega)]
    simpa using h₁

lemma polynomial_via : PolynomialTime viaRealizer := by
  unfold viaRealizer
  apply polynomial_composition _ TreeFraction.polynomial_minimum
  apply polynomial_pair
  · apply polynomial_composition _ polynomial_cell
    exact polynomial_pair (polynomial_fst polynomial_first)
      (polynomial_pair (polynomial_fst (polynomial_snd polynomial_first)) polynomial_second)
  · apply polynomial_composition _ polynomial_cell
    exact polynomial_pair (polynomial_fst polynomial_first)
      (polynomial_pair polynomial_second (polynomial_snd (polynomial_snd polynomial_first)))

lemma polynomial_entry : PolynomialTime entryRealizer := by
  have hR : PolynomialTime (composition (composition (first (A:=Matrix) (B:=ℕ×ℕ)) listLength) range) := by
    apply polynomial_boundedRange (by ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_congr | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe)))) X
    intro x; simpa using (list_length_le_weight x.1).trans (weight_fst x)
  unfold entryRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_choose (polynomial_composition polynomial_second polynomial_natEqual) (polynomial_constant one)
  apply polynomial_composition _ polynomial_maximumFold
  apply polynomial_pair _ polynomial_cell
  exact polynomial_composition (polynomial_pair polynomial_identity hR) (polynomial_mapWith polynomial_via)

lemma polynomial_advance : PolynomialTime advanceRealizer := by
  exact polynomial_square polynomial_listLength polynomial_entry X (fun a=>by simpa using list_length_le_weight a)
lemma advance_length (M : Matrix) : (advance M).length=M.length := by
  simp [advance,square]
lemma entry_weight {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) (i j : ℕ) : weight (entry (M,(i,j)))≤B := by
  unfold entry
  dsimp only
  split_ifs
  · exact h₁
  · apply maximum_fold_weight _ _ _ (cell_weight h₁ hM i j)
    intro x hx
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hx
    exact (minimum_weight _ _).trans (max_le (cell_weight h₁ hM i c) (cell_weight h₁ hM c j))
lemma advance_entries {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) : ∀ r∈advance M,∀ x∈r,weight x≤B := by
  intro r hr x hx
  obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
  obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hx
  exact entry_weight h₁ hM i j
lemma advance_weight {M : Matrix} {B : ℕ} (h₁ : weight one≤B)
    (hM : ∀ r∈M,∀ x∈r,weight x≤B) : weight (advance M)≤1+M.length*(2+M.length*(B+1)) := by
  unfold advance square
  have h:=weight_map_bound (as:=List.range M.length)
    (N:=1+M.length*(B+1)) (f:=fun i=>(List.range M.length).map fun j=>entry (M,(i,j))) (by
      intro i _
      simpa [List.length_range,Nat.add_comm] using weight_map_bound (as:=List.range M.length)
        (f:=fun j=>entry (M,(i,j))) (fun j _=>entry_weight h₁ hM i j))
  simp only [List.length_range] at h
  exact h.trans_eq (by ring)

lemma polynomial_seedEntry : PolynomialTime seedEntryRealizer := by
  unfold seedEntryRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_choose (polynomial_composition polynomial_second polynomial_natEqual)
    (polynomial_constant one)
  apply polynomial_composition _ TreeFraction.polynomial_maximum
  apply polynomial_pair (polynomial_constant one)
  apply polynomial_composition _ polynomial_cell
  apply polynomial_pair polynomial_first
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition polynomial_second TreeTyped.polynomial_less)
    polynomial_second (polynomial_pair (polynomial_snd polynomial_second)
      (polynomial_fst polynomial_second))

lemma polynomial_seed : PolynomialTime seedRealizer :=
  polynomial_square polynomial_listLength polynomial_seedEntry X (fun a=>by simpa using list_length_le_weight a)

lemma fold_advance_invariant (ls : List (List Fraction)) (M : Matrix) (B : ℕ)
    (h₁ : weight one≤B) (hM : ∀ r∈M,∀ x∈r,weight x≤B) :
    let R:=ls.foldl (fun z _=>advance z) M
    R.length=M.length ∧ (∀ r∈R,∀ x∈r,weight x≤B) ∧
      weight R≤weight M+1+M.length*(2+M.length*(B+1)) := by
  have hInv : ∀ (ls : List (List Fraction)) (M : Matrix),
      (∀ r∈M,∀ x∈r,weight x≤B) →
      (ls.foldl (fun z _=>advance z) M).length=M.length ∧
        (∀ r∈ls.foldl (fun z _=>advance z) M,∀ x∈r,weight x≤B) := by
    intro ls
    induction ls with
    | nil => intro M hm; exact ⟨rfl,hm⟩
    | cons r ls ih =>
      intro M hm
      obtain ⟨hl,hR⟩:=ih (advance M) (advance_entries h₁ hm)
      exact ⟨hl.trans (advance_length M),hR⟩
  refine ⟨(hInv ls M hM).1,(hInv ls M hM).2,?_⟩
  cases ls using List.reverseRecOn with
  | nil => simpa only [List.foldl_nil,Nat.add_assoc] using (Nat.le_add_right (weight M) (1+M.length*(2+M.length*(B+1))))
  | append_singleton ls r ih =>
    rw [List.foldl_append]
    dsimp only [List.foldl]
    have hw:=advance_weight h₁ (hInv ls M hM).2
    rw [(hInv ls M hM).1] at hw
    omega

lemma polynomial_closeFold : PolynomialTime (fold (composition (second (A:=List Fraction)) advanceRealizer)) := by
  apply polynomial_fold (polynomial_composition polynomial_second polynomial_advance)
    (X+1+X*(2+X*(X+C (weight one)+1)))
  intro ls M pre _ _
  let S:=weight (ls,M)
  have hM : weight M≤S := weight_snd (ls,M)
  have hn : M.length≤S := (list_length_le_weight M).trans hM
  have hi:=fold_advance_invariant pre M (S+weight one) (by omega) (by
    intro r hr x hx
    exact ((weight_mem hx).trans ((weight_mem hr).trans hM)).trans (Nat.le_add_right _ _))
  have hb := hi.2.2
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_C]
  change weight (pre.foldl (fun z _=>advance z) M)≤S+1+S*(2+S*(S+weight one+1))
  have hp:=Nat.mul_le_mul hn (Nat.add_le_add_left (Nat.mul_le_mul_right (S+weight one+1) hn) 2)
  omega
lemma polynomial_close : PolynomialTime closeRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_seed) polynomial_closeFold

end MatchingFPRAS.ExecutableBottleneck

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHierarchyRoot
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma polynomial_related : PolynomialTime relatedRealizer := by
  unfold relatedRealizer Realizer.fst Realizer.snd
  have hc:=polynomial_cell
  have hl:=TreeFraction.polynomial_less
  apply polynomial_composition _ polynomial_boolOr
  apply polynomial_pair
  · apply polynomial_composition _ polynomial_natEqual
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
  · apply polynomial_composition _ polynomial_boolNot
    apply polynomial_composition _ hl
    apply polynomial_pair
    · apply polynomial_composition _ hc
      ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
    · ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_component : PolynomialTime componentRealizer := by
  have hr : PolynomialTime (composition (composition (first (A:=Matrix×Fraction) (B:=ℕ)).fst listLength) range) := by
    apply polynomial_boundedRange (by unfold Realizer.fst; ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))) X
    intro x
    simpa using (list_length_le_weight x.1.1).trans ((weight_fst x.1).trans (weight_fst x))
  unfold componentRealizer
  have:=polynomial_related
  apply polynomial_composition _ (polynomial_filterWith this)
  exact polynomial_pair polynomial_identity hr

lemma polynomial_root : PolynomialTime rootRealizer := by
  unfold rootRealizer
  apply polynomial_composition _ polynomial_listMin
  exact polynomial_pair polynomial_component (polynomial_composition (polynomial_fst polynomial_first) polynomial_listLength)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
lemma polynomial_filterWithList {A B : Type} [Codec A] [Codec B] {p : A×B→Bool}
    {P : Realizer p} (hP : PolynomialTime P) : PolynomialTime (filterWith P) := by
  unfold filterWith
  exact polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_mapWith (polynomial_pair polynomial_second hP))
      (polynomial_filter polynomial_second)) (polynomial_map polynomial_first))
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma polynomial_labelRoot : PolynomialTime labelRootRealizer := by
  apply polynomial_composition _ polynomial_root
  apply polynomial_pair _ (polynomial_snd polynomial_second)
  exact polynomial_pair (polynomial_fst polynomial_first) (polynomial_composition
    (polynomial_pair (polynomial_snd polynomial_first) (polynomial_fst polynomial_second)) polynomial_threshold)

lemma polynomial_fixedRoot : PolynomialTime fixedRootRealizer :=
  polynomial_composition (polynomial_pair polynomial_labelRoot (polynomial_snd polynomial_second)) polynomial_natEqual

lemma polynomial_labels : PolynomialTime labelsRealizer := by
  have hk : PolynomialTime (composition (composition (composition (second (A:=Matrix) (B:=List Bool)) listLength) successor) range) := by
    apply polynomial_boundedRange (polynomial_composition (polynomial_composition polynomial_second polynomial_listLength) polynomial_successor) (X+1)
    intro x
    have h:=(list_length_le_weight x.2).trans (weight_snd x)
    simpa only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,Function.comp_apply,Nat.succ_eq_add_one] using Nat.add_le_add_right h 1
  have hv : PolynomialTime (composition (composition (first (A:=Matrix) (B:=List Bool)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    intro x
    simpa using (list_length_le_weight x.1).trans (weight_fst x)
  unfold labelsRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ (polynomial_filterWithList polynomial_fixedRoot)
  apply polynomial_pair polynomial_identity
  apply polynomial_composition _ polynomial_flatten
  apply polynomial_composition (polynomial_pair polynomial_identity hk)
  apply polynomial_mapWith
  apply polynomial_composition _ (polynomial_mapWith (polynomial_pair polynomial_first polynomial_second))
  exact polynomial_pair polynomial_second (polynomial_composition polynomial_first hv)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeParentTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck

lemma polynomial_parentKey : PolynomialTime parentKeyRealizer := by
  unfold parentKeyRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_predecessor
  have := polynomial_labelRoot
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_parentEntry : PolynomialTime parentEntryRealizer := by
  unfold parentEntryRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_parentKey
  have := polynomial_indexOf (polynomial_pairEqual polynomial_natEqual polynomial_natEqual)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_parents : PolynomialTime parentsRealizer := by
  unfold parentsRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_identity polynomial_labels) polynomial_labels)
    (polynomial_mapWith polynomial_parentEntry)

lemma polynomial_ranks : PolynomialTime ranksRealizer := polynomial_composition polynomial_labels (polynomial_map polynomial_first)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagTable
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeFraction ExecutableBottleneck Polynomial

lemma polynomial_edgeKey : PolynomialTime edgeKeyRealizer := by
  unfold edgeKeyRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_labelRoot
  have := polynomial_level
  have := polynomial_cell
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_incident : PolynomialTime incidentRealizer := by
  unfold incidentRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_edgeIndex : PolynomialTime edgeIndexRealizer := by
  unfold edgeIndexRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_fst polynomial_first) polynomial_second) polynomial_edgeKey)
    (polynomial_snd polynomial_first)) (polynomial_indexOf (polynomial_pairEqual polynomial_natEqual polynomial_natEqual))

lemma polynomial_bag : PolynomialTime bagRealizer := by
  unfold bagRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_labels
  have := polynomial_filterWithList polynomial_incident
  have := polynomial_mapWith polynomial_edgeIndex
  have := polynomial_dedup polynomial_natEqual
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_bagTable : PolynomialTime bagTableRealizer := by
  have hr : PolynomialTime (composition (composition (first (A:=HierarchyInput) (B:=List (ℕ×ℕ))).fst listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition (polynomial_fst polynomial_first) polynomial_listLength) X
    intro x
    simpa using (list_length_le_weight x.1.1).trans ((weight_fst x.1).trans (weight_fst x))
  exact polynomial_composition (polynomial_pair polynomial_identity hr) (polynomial_mapWith polynomial_bag)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeQuad
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B : Type} [Codec A] [Codec B]

lemma polynomial_listProduct : PolynomialTime (listProduct (A:=A) (B:=B)) := by
  unfold listProduct
  apply polynomial_congr
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped Polynomial Enlargement RealGeometry

lemma polynomial_logicalEdges : PolynomialTime logicalEdgesRealizer := by
  unfold logicalEdgesRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_identity) polynomial_listProduct)
    (polynomial_filter polynomial_less)

lemma polynomial_internalCount : PolynomialTime internalCountRealizer := by
  unfold internalCountRealizer; apply polynomial_congr; ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma internalCount_bound (x : GeometryInput) : internalCount x≤(4*X).eval (weight x) := by
  have h: x.2.length≤weight x := (list_length_le_weight x.2).trans (weight_snd x)
  simpa [internalCount] using Nat.mul_le_mul_left 4 h

lemma polynomial_realEdges : PolynomialTime realEdgesRealizer := by
  have hr:PolynomialTime (composition (composition internalCountRealizer successor) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_internalCount polynomial_successor) (4*X+1)
    intro x
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one,Function.comp_apply]
    have h:=internalCount_bound x
    simpa only [eval_mul,eval_ofNat,eval_X] using Nat.add_le_add_right h 1
  unfold realEdgesRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_logicalEdges) hr) polynomial_listProduct

lemma polynomial_vertices : PolynomialTime verticesRealizer := by
  have hr:=polynomial_boundedRange polynomial_internalCount (4*X) internalCount_bound
  unfold verticesRealizer
  apply polynomial_congr
  have := polynomial_logicalEdges
  have := polynomial_listProduct (A:=RawLogical) (B:=ℕ)
  have := polynomial_inl (A:=ℕ) (B:=RawReal)
  have := polynomial_inr (A:=ℕ) (B:=RawReal)
  have := polynomial_successor
  have := polynomial_predecessor
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_at : PolynomialTime atRealizer := by
  unfold atRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_inl (A:=ℕ) (B:=RawReal)
  have := polynomial_inr (A:=ℕ) (B:=RawReal)
  have := polynomial_successor
  have := polynomial_predecessor
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_left : PolynomialTime leftRealizer := by
  unfold leftRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_internalCount)
    polynomial_second) polynomial_at
lemma polynomial_right : PolynomialTime rightRealizer := by
  unfold rightRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_successor
  have := polynomial_internalCount
  have := polynomial_at
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshCatalog
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableRefresh
open TreeTyped ExecutableDP ExecutableSource Polynomial

lemma polynomial_sharedKey : PolynomialTime sharedKeyRealizer := by
  unfold sharedKeyRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_getDFast ([] : List ℕ)
  have := polynomial_membership
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_storedCatalog : PolynomialTime storedCatalogRealizer := by
  have hr : PolynomialTime (composition (composition (first (A:=Bags) (B:=List ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
    intro x
    simpa only [eval_X,Function.comp_apply] using (list_length_le_weight x.1).trans (weight_fst x)
  unfold storedCatalogRealizer
  apply polynomial_congr
  have := polynomial_filterWithList polynomial_sharedKey
  have := polynomial_sharedKey
  have := polynomial_logicalEdges
  have := polynomial_listProduct (A:=ℕ×ℕ) (B:=ℕ)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open Transport UnitRefresh

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype Transport.prodOrder
end MatchingFPRAS.ExecutableRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeRankPlan
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped ExecutableDP Polynomial

lemma polynomial_rankLe : PolynomialTime rankLeRealizer := by
  unfold rankLeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_rankEntries : PolynomialTime rankEntriesRealizer := by
  unfold rankEntriesRealizer
  apply polynomial_congr
  have hr : PolynomialTime (composition (listLength (A:=ℕ)) range) :=
    polynomial_boundedRange polynomial_listLength X (fun x=>by simpa using list_length_le_weight x)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_mapWith (polynomial_pair (polynomial_getDFast 0) polynomial_second))
lemma polynomial_rankPlan : PolynomialTime rankPlanRealizer :=
  polynomial_composition (polynomial_composition polynomial_rankEntries (polynomial_insertionSort rankLe polynomial_rankLe)) (polynomial_map polynomial_second)

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRefreshTables
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableHierarchy
open TreeTyped TreeTyped.Numbered ExecutableDP ExecutableRefresh NumberedHierarchy

lemma polynomial_labelIndices : PolynomialTime labelIndicesRealizer := by
  unfold labelIndicesRealizer
  apply polynomial_congr
  have h : PolynomialTime (composition (listLength (A:=LabelKey)) range) :=
    polynomial_boundedRange polynomial_listLength Polynomial.X (fun x=>by
      simpa using list_length_le_weight x)
  exact polynomial_composition polynomial_labels h

lemma polynomial_refreshTables : PolynomialTime refreshTablesRealizer := by
  unfold refreshTablesRealizer
  apply polynomial_congr
  have := polynomial_bagTable
  have := polynomial_labelIndices
  have := polynomial_storedCatalog
  have := polynomial_parents
  have := polynomial_ranks
  have := polynomial_rankPlan
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

open TreePost Turing

end MatchingFPRAS.ExecutableHierarchy

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeScaling
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableScaling
open TreeTyped TreeFraction ExecutableBottleneck ExecutableLadder Polynomial

lemma polynomial_ratio : PolynomialTime ratioRealizer := by
  unfold ratioRealizer
  apply polynomial_composition _ polynomial_div
  apply polynomial_pair _ (polynomial_snd polynomial_second)
  apply polynomial_composition _ polynomial_cell
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_rowMax : PolynomialTime rowMaxRealizer := by
  unfold rowMaxRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_maximumFold
  have := polynomial_ratio
  have : PolynomialTime (composition (composition (pair (second (A:=ℕ) (B:=ℕ×Fraction)).fst first) natEqual) boolNot) := by
    dsimp only [Realizer.fst,Realizer.snd]
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableScaling

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeProfile
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Polynomial

lemma polynomial_profile : PolynomialTime profileRealizer := by
  unfold profileRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_threshold
  have := polynomial_quotient
  have := polynomial_div
  have := polynomial_maximum
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_height : PolynomialTime heightRealizer := by
  unfold heightRealizer
  have hh : PolynomialTime (composition (composition (first (A:=Matrix) (B:=ℕ)) listLength) range) := by
    apply polynomial_boundedRange (by ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))) X
    intro x
    simpa only [eval_X,Function.comp_apply] using (list_length_le_weight x.1).trans (weight_fst x)
  apply polynomial_composition _ ExecutableScaling.polynomial_rowMax
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_maxHeight : PolynomialTime maxHeightRealizer := by
  unfold maxHeightRealizer
  apply polynomial_congr
  have hr:PolynomialTime (composition (listLength (A:=List Fraction)) range) := by
    apply polynomial_boundedRange polynomial_listLength X
    intro M; simpa only [eval_X] using list_length_le_weight M
  have := polynomial_height
  have := polynomial_maximumFold
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Polynomial Enlargement RealGeometry

lemma polynomial_path : PolynomialTime pathRealizer := by
  unfold pathRealizer
  apply polynomial_congr
  have := polynomial_cell
  have := polynomial_height
  have := polynomial_profile
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_vertexEqual : PolynomialTime vertexEqual :=
  polynomial_sumEqual polynomial_natEqual (polynomial_pairEqual
    (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual)

lemma polynomial_sameEnds : PolynomialTime sameEndsRealizer := by
  unfold sameEndsRealizer
  apply polynomial_congr
  have := polynomial_vertexEqual
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_pathRow : PolynomialTime pathRowRealizer := by
  unfold pathRowRealizer
  apply polynomial_congr
  have := polynomial_left
  have := polynomial_right
  have := polynomial_path
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_pathTable : PolynomialTime pathTableRealizer := by
  unfold pathTableRealizer
  apply polynomial_congr
  have := polynomial_realEdges
  have := polynomial_mapWith polynomial_pathRow
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_contribution : PolynomialTime contributionRealizer := by
  unfold contributionRealizer
  apply polynomial_congr
  have := polynomial_sameEnds
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_activity : PolynomialTime activityRealizer := by
  unfold activityRealizer
  apply polynomial_congr
  have := polynomial_mapWith polynomial_contribution
  have := polynomial_sum
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeMatrix
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

lemma polynomial_activityRow : PolynomialTime activityRowRealizer := by
  unfold activityRowRealizer
  apply polynomial_congr
  have := polynomial_activity
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_activityMatrix : PolynomialTime activityMatrixRealizer := by
  exact polynomial_composition (polynomial_pair polynomial_identity polynomial_second)
    (polynomial_mapWith polynomial_activityRow)

lemma polynomial_materialize : PolynomialTime materializeRealizer := by
  unfold materializeRealizer
  apply polynomial_congr
  have := polynomial_pathTable
  have := polynomial_vertices
  have := polynomial_activityMatrix
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBuild
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

lemma polynomial_prepare : PolynomialTime prepareRealizer := by
  unfold prepareRealizer
  apply polynomial_congr
  have := polynomial_close
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_buildMatrix : PolynomialTime buildMatrixRealizer :=
  polynomial_composition polynomial_prepare polynomial_materialize

lemma polynomial_buildClosure : PolynomialTime buildClosureRealizer :=
  polynomial_composition polynomial_buildMatrix polynomial_close

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeBagBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instBEqRawVertex
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLawfulBEqRawVertex
lemma polynomial_endpointEntry : PolynomialTime endpointEntryRealizer := by
  unfold endpointEntryRealizer
  apply polynomial_congr
  have := polynomial_indexOf polynomial_vertexEqual
  have := polynomial_left
  have := polynomial_right
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_endpointList : PolynomialTime endpointListRealizer := by
  unfold endpointListRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_identity
    polynomial_vertices) polynomial_realEdges) (polynomial_mapWith polynomial_endpointEntry)

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_TreeHeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

lemma polynomial_hierarchyFuel : PolynomialTime hierarchyFuelRealizer := by
  unfold hierarchyFuelRealizer
  apply polynomial_congr
  have := polynomial_close
  have := polynomial_maxHeight
  have := polynomial_level
  have := polynomial_takeFast (A:=Bool)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

attribute [local instance] NumberedHierarchy.labelOrder
end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeInitial
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy Enlargement RealGeometry

lemma polynomial_setupHierarchy : PolynomialTime setupHierarchyRealizer := by
  unfold setupHierarchyRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_buildClosure
  have := polynomial_hierarchyFuel
  have := polynomial_endpointList
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_sourceTables : PolynomialTime sourceTablesRealizer :=
  polynomial_composition polynomial_setupHierarchy polynomial_refreshTables

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeColor
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma polynomial_coloredKey : PolynomialTime coloredKeyRealizer := by
  unfold coloredKeyRealizer
  apply polynomial_congr
  have := polynomial_labels
  have := polynomial_edgeIndex
  have hmax : PolynomialTime TreeTyped.maximum := by
    unfold TreeTyped.maximum
    exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_second polynomial_first)
  have hmin := TreeTyped.polynomial_minimum
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_sourceRealKey : PolynomialTime sourceRealKeyRealizer := by
  unfold sourceRealKeyRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_setupHierarchy
  have := polynomial_vertices
  have := polynomial_endpointEntry
  have := polynomial_coloredKey
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePortion
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma polynomial_coloredRow : PolynomialTime coloredRowRealizer := by
  unfold coloredRowRealizer Realizer.fst
  apply polynomial_congr
  have := polynomial_sourceRealKey
  have := polynomial_prepare
  have := polynomial_path
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_coloredRows : PolynomialTime coloredRowsRealizer := by
  unfold coloredRowsRealizer
  have := polynomial_realEdges
  have := polynomial_coloredRow
  exact polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair (polynomial_snd polynomial_first)
      (polynomial_snd (polynomial_fst polynomial_first))) polynomial_realEdges))
    (polynomial_mapWith polynomial_coloredRow)

lemma polynomial_colorContribution : PolynomialTime colorContributionRealizer := by
  unfold colorContributionRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_pairEqual (polynomial_pairEqual polynomial_natEqual polynomial_natEqual) polynomial_natEqual
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_realPart : PolynomialTime realPartRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_coloredRows))
    (polynomial_mapWith polynomial_colorContribution)) polynomial_sum

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreePhantom
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma polynomial_sourceRanks : PolynomialTime sourceRanksRealizer :=
  polynomial_composition (polynomial_fst polynomial_setupHierarchy) polynomial_ranks
lemma polynomial_sourceRank : PolynomialTime sourceRankRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_sourceRanks)
    (polynomial_snd polynomial_second)) (polynomial_getDFast 0)
lemma polynomial_phantomHeight : PolynomialTime phantomHeightRealizer :=
  polynomial_composition (polynomial_pair (polynomial_snd polynomial_first) polynomial_sourceRank)
    polynomial_threshold
lemma polynomial_sourceBagWeight : PolynomialTime sourceBagWeightRealizer := by
  unfold sourceBagWeightRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_realPart
  have := polynomial_phantomHeight
  have := polynomial_div
  have := TreeFraction.polynomial_add
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeWeightTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma polynomial_rowsWith {A B C : Type} [Codec A] [Codec B] [Codec C]
    {f : A×B→C} {g : A→List B} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (rowsWith F G) :=
  polynomial_composition (polynomial_pair polynomial_identity hG) (polynomial_mapWith hF)
lemma polynomial_sourceWeights : PolynomialTime sourceWeightsRealizer :=
  polynomial_rowsWith polynomial_sourceBagWeight
    (polynomial_fst (polynomial_composition polynomial_first polynomial_sourceTables))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedPrepared
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma polynomial_sourceVertices : PolynomialTime sourceVerticesRealizer :=
  polynomial_composition (polynomial_pair (polynomial_snd polynomial_first)
    (polynomial_snd (polynomial_fst polynomial_first))) polynomial_vertices
lemma polynomial_generatedTier_oai : PolynomialTime generatedTierRealizer := by
  unfold generatedTierRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  have := polynomial_sourceVertices
  have := polynomial_sourceWeights
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedTier_oai := @OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedTier_oai
