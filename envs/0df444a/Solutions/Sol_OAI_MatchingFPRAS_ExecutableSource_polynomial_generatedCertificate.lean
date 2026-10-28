-- Prove2me | solution 1 for OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedCertificate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:12:10.784106+00:00
-- url     : https://prove2.me/submissions/733fbb0e-2e8e-4b30-abcb-71738156f926

import Mathlib
import Definitions.Def_OAIQ051M004
import Theorems.Thm_OAI_MatchingFPRAS_ExecutableSource_polynomial_generatedContext
import Theorems.Thm_OAI_MatchingFPRAS_ExecutableSource_polynomial_sourceReweights
import Theorems.Thm_OAI_MatchingFPRAS_NumericLadder_polynomial_pair
import Theorems.Thm_OAI_MatchingFPRAS_NumericLadder_polynomial_refresh

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
lemma polynomial_isEmpty : PolynomialTime (isEmpty (A:=A)) := polynomial_listCase true (polynomial_constant false)
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

omit [Codec C] [Codec D] in
lemma polynomial_sumLexLe [Inhabited A] [Inhabited B] [LinearOrder A] [LinearOrder B]
    {R : Realizer (fun x : A×A=>decide (x.1≤x.2))}
    {S : Realizer (fun x : B×B=>decide (x.1≤x.2))}
    (hR : PolynomialTime R) (hS : PolynomialTime S) : PolynomialTime (sumLexLe R S) := by
  unfold sumLexLe
  apply polynomial_congr
  apply polynomial_sumCases
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases (polynomial_composition (polynomial_pair polynomial_second polynomial_first) hR)
        (polynomial_constant false))
  · exact polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_sumCases (polynomial_constant true)
        (polynomial_composition (polynomial_pair polynomial_second polynomial_first) hS))

omit [Codec B] [Codec C] [Codec D] in
lemma polynomial_some [Inhabited A] : PolynomialTime (some (A:=A)) := by
  unfold some
  apply polynomial_recode
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Codec B] in
lemma polynomial_optionCases [Inhabited A] {f : C→D} {g : C×A→D}
    {F : Realizer f} {G : Realizer g} (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (optionCases F G) := by
  unfold optionCases
  apply polynomial_recode
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
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
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
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
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeFractionExtra
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

lemma polynomial_sub : PolynomialTime subRealizer := by
  unfold subRealizer Realizer.fst Realizer.snd
  apply polynomial_composition _ polynomial_normalize
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma height_mul (a b : Fraction) : height (mul (a,b))≤height a+height b+1 := by
  have hn:=normalize_size_num (a.1*b.1,a.2*b.2)
  have hd:=normalize_size_den (a.1*b.1,a.2*b.2)
  have hm:=nat_size_mul a.1 b.1
  have hm':=nat_size_mul a.2 b.2
  have ha:=le_max_left a.1.size a.2.size
  have ha':=le_max_right a.1.size a.2.size
  have hb:=le_max_left b.1.size b.2.size
  have hb':=le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (mul (a,b)).1.size≤_ at hn
  change (mul (a,b)).2.size≤_ at hd
  unfold height
  apply max_le <;> omega
lemma fractionProduct_height (xs : List Fraction) (a : Fraction) (M : ℕ)
    (hx : ∀ b∈xs,height b≤M) :
    height (xs.foldl (fun a b=>mul (b,a)) a)≤height a+xs.length*(M+1) := by
  induction xs generalizing a with
  | nil => simp
  | cons b bs ih =>
    have hh:=height_mul b a
    have hb:=hx b (by simp)
    have ht:=ih (mul (b,a)) (fun c h=>hx c (by simp [h]))
    simp only [List.foldl_cons,List.length_cons]
    nlinarith
lemma polynomial_fractionProduct : PolynomialTime (fold mulRealizer) := by
  apply polynomial_fold polynomial_mul (8*X+8*X*(X+1)+3)
  intro xs a pre post he
  let S:=weight (xs,a)
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (xs,a)))
  have hb : ∀ b∈pre,height b≤S := by
    intro b hb
    exact (height_le_weight b).trans ((weight_mem (as:=xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have ha : height a≤S := (height_le_weight a).trans (weight_snd (xs,a))
  have hh:=fractionProduct_height pre a S hb
  have hw:=weight_le_height (pre.foldl (fun a b=>mul (b,a)) a)
  have hm:=Nat.mul_le_mul_right (S+1) hpre
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _≤8*S+8*S*(S+1)+3
  nlinarith

lemma polynomial_product : PolynomialTime productRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_fractionProduct)
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptions
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A B C Ω : Type} [Codec A] [Codec B] [Codec C]

omit [Codec B] [Codec C] in
lemma polynomial_listSingleton : PolynomialTime (listSingleton (A:=A)) :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_listCons

omit [Codec B] [Codec C] in
lemma polynomial_pure : PolynomialTime (pureRealizer (A:=A)) :=
  polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _)) polynomial_listSingleton)
omit [Codec B] [Codec C] in
lemma polynomial_scale : PolynomialTime (scaleRealizer (A:=A)) := by
  unfold scaleRealizer
  apply polynomial_congr
  exact polynomial_mapWith (polynomial_pair (polynomial_fst polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_first (polynomial_snd polynomial_second)) polynomial_mul))

omit [Codec B] [Codec C] in
lemma polynomial_mix : PolynomialTime (mixRealizer (A:=A)) := by
  unfold mixRealizer
  apply polynomial_composition _ polynomial_append
  have := polynomial_scale (A:=A)
  have := polynomial_sub
  dsimp only [Realizer.fst, Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_map {f : C×A→B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (mapRealizer F) := by
  unfold mapRealizer
  apply polynomial_congr
  exact polynomial_mapWith (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_fst polynomial_second)) hF) (polynomial_snd polynomial_second))
omit [Codec B] [Codec C] in
lemma polynomial_draw (d : A) : PolynomialTime (drawRealizer d) := by
  unfold drawRealizer
  dsimp only
  apply polynomial_congr
  have := ExecutableChoice.polynomial_chooseBitsFast
  have := polynomial_getDFast d
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeOptionsFinite
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableOptions
open TreeTyped TreeFraction

variable {A : Type} [Codec A] [LinearOrder A]

lemma polynomial_uniform : PolynomialTime (uniformRealizer (A:=A)) := by
  unfold uniformRealizer
  apply polynomial_congr
  have := polynomial_normalize
  have := polynomial_mapWith (polynomial_pair (polynomial_second (A:=Fraction) (B:=A)) polynomial_first)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
end MatchingFPRAS.ExecutableOptions

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeReach
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited _root_.OAI.MatchingFPRAS.TreeTyped.instCodecSumOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
open Polynomial

variable {A C : Type} [Codec A] [Codec C] [LinearOrder A]
omit [LinearOrder A] in
lemma weight_subperm {as bs : List A} (h : as.Subperm bs) : weight as≤weight bs := by
  obtain ⟨cs,hc,hs⟩:=h
  rw [← weight_perm hc]
  exact weight_sublist hs
lemma weight_finset_subset {s t : Finset A} (h : s⊆t) : weight s≤weight t := by
  apply weight_subperm
  apply (Finset.sort_nodup s (·≤·)).subperm
  intro a ha
  simpa only [Finset.mem_sort] using h (by simpa only [Finset.mem_sort] using ha)
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeSlotWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma polynomial_fuelPower : PolynomialTime fuelPowerRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_first) polynomial_product
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped TreeFraction

lemma polynomial_tierBase : PolynomialTime tierBaseRealizer := by
  unfold tierBaseRealizer
  apply polynomial_congr
  have := TreeFraction.polynomial_add
  have := polynomial_div
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_tierPower : PolynomialTime tierPowerRealizer := by
  unfold tierPowerRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_tierBase
  have := polynomial_takeFast (A:=Bool)
  have := polynomial_fuelPower
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_slotWeight : PolynomialTime slotWeightRealizer := by
  unfold slotWeightRealizer
  dsimp only
  apply polynomial_congr
  have := polynomial_tierPower
  have := polynomial_div
  have := TreeFraction.polynomial_minimum
  have := TreeFraction.polynomial_maximum
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStateTable
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A : Type} [Codec I] [Codec A] [DecidableEq I] [Inhabited I]
lemma polynomial_lookup (d : A) {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (lookupRealizer d E) := by
  unfold lookupRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition
  · exact polynomial_pair polynomial_second (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first)
      (polynomial_filterWithList (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_second) polynomial_first) hE)))
  · apply polynomial_congr
    have := polynomial_isEmpty (A:=I×A)
    have := polynomial_head ((default : I),d)
    ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Inhabited I] in
lemma polynomial_setState {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (setStateRealizer (A:=A) E) := by
  unfold setStateRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
omit [Inhabited I] in
lemma polynomial_setPair {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hE : PolynomialTime E) : PolynomialTime (setPairRealizer (A:=A) E) := by
  unfold setPairRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_setState (A:=A) hE
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_TreeStateNormalize
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E : Type} [Codec I] [Codec E] [DecidableEq I] [Inhabited I] [LinearOrder E]
lemma polynomial_normalizeState {Eq : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hEq : PolynomialTime Eq) (hE : PolynomialTime EqE) : PolynomialTime (normalizeStateRealizer Eq EqE) := by
  unfold normalizeStateRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_lookup (∅ : Finset E) hEq
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Inhabited I] in
lemma normalizeState_weight (keys : List I) (univ : Finset E) (s : StateTable I (Finset E)) :
    weight (normalizeState ((keys,univ),s))≤(weight keys+1)*(weight univ+3) := by
  induction keys with
  | nil=>simp only [normalizeState,List.map_nil,weight_nil]; omega
  | cons i keys ih=>
    have hu : weight (lookup ∅ (s,i)∩univ)≤weight univ := weight_finset_subset Finset.inter_subset_right
    change weight ((i,lookup ∅ (s,i)∩univ)::normalizeState ((keys,univ),s))≤_
    rw [weight_cons,weight_prod,weight_cons]
    nlinarith

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeLocalSampler
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [DecidableEq I] [Inhabited I] [Inhabited A]
lemma polynomial_localPair {p : LocalPairInput C I A B→A×A} {P : Realizer p}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hP : PolynomialTime P) (hE : PolynomialTime E) : PolynomialTime (localPairRealizer P E) := by
  unfold localPairRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_lookup (default : A) hE
  have := polynomial_setPair (A:=A) hE
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Inhabited I] [Inhabited A] in
lemma polynomial_localRefresh {r : LocalRefreshInput C I B→A} {R : Realizer r}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hR : PolynomialTime R) (hE : PolynomialTime E) : PolynomialTime (localRefreshRealizer R E) := by
  unfold localRefreshRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_setState (A:=A) hE
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

attribute [local instance] OAI.MatchingFPRAS.ExecutableLadder.treeLocalSamplerUpdateInhabited
lemma polynomial_localSampler {p : LocalPairInput C I A B→A×A} {r : LocalRefreshInput C I B→A}
    {P : Realizer p} {R : Realizer r} {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    (hP : PolynomialTime P) (hR : PolynomialTime R) (hE : PolynomialTime E) :
    PolynomialTime (localSamplerRealizer P R E) := by
  unfold localSamplerRealizer
  apply polynomial_congr
  exact polynomial_optionCases (polynomial_fst polynomial_second)
    (polynomial_sumCases (polynomial_localPair hP hE) (polynomial_localRefresh hR hE))

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanChoice
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I C : Type} [Codec I] [Codec C] [Inhabited I] [LinearOrder I]
attribute [local instance] Transport.prodOrder Transport.sumOrder
lemma polynomial_updateList {g : C×(I×I)→Bool} {G : Realizer g} (hG : PolynomialTime G) :
    PolynomialTime (updateListRealizer G) := by
  unfold updateListRealizer
  dsimp only [Realizer.fst, Realizer.snd]
  apply polynomial_congr
  have := polynomial_listProduct (A:=I) (B:=I)
  have := polynomial_filterWithList hG
  have := polynomial_inl (A:=I×I) (B:=I)
  have := polynomial_inr (A:=I×I) (B:=I)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Codec C] in
lemma polynomial_updateEqual {E : Realizer (fun x : I×I=>decide (x.1=x.2))} (hE : PolynomialTime E) :
    PolynomialTime (updateEqual E) :=
  polynomial_congr _ (polynomial_sumEqual (polynomial_pairEqual hE hE) hE)

lemma polynomial_updateSet {g : C×(I×I)→Bool} {G : Realizer g}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {R : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (updateSetRealizer G E R) := by
  unfold updateSetRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_updateList hG)
    (polynomial_listFinset (polynomial_updateEqual hE)
      (polynomial_sumLexLe (polynomial_lexLe hE hR hR) hR))

attribute [local instance] OAI.MatchingFPRAS.ExecutableLadder.instInhabitedUpdate
lemma polynomial_scanChoice {g : C×(I×I)→Bool} {G : Realizer g}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {R : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime E) (hR : PolynomialTime R) :
    PolynomialTime (scanChoiceRealizer G E R) := by
  unfold scanChoiceRealizer
  apply polynomial_congr
  have := polynomial_updateSet hG hE hR
  have := polynomial_uniform (A:=Replica.Update I)
  have := polynomial_pure (A:=Option (Replica.Update I))
  have := polynomial_mix (A:=Option (Replica.Update I))
  have := ExecutableOptions.polynomial_map (polynomial_composition (polynomial_second (A:=Bool) (B:=Replica.Update I)) (polynomial_some (A:=Replica.Update I)))
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScan
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped ExecutableOptions

variable {I A B C : Type} [Codec I] [Codec A] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [Inhabited A]
attribute [local instance] Transport.prodOrder Transport.sumOrder
attribute [local instance] OAI.MatchingFPRAS.ExecutableLadder.treeScanUpdateInhabited
lemma polynomial_scan {g : C×(I×I)→Bool} {p : LocalPairInput C I A B→A×A}
    {r : LocalRefreshInput C I B→A} {G : Realizer g} {P : Realizer p} {R : Realizer r}
    {E : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {L : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    (hG : PolynomialTime G) (hP : PolynomialTime P) (hR : PolynomialTime R)
    (hE : PolynomialTime E) (hL : PolynomialTime L) : PolynomialTime (scanRealizer G P R E L) := by
  unfold scanRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_scanChoice hG hE hL
  have := polynomial_draw (none : Option (Replica.Update I))
  have := polynomial_localSampler hP hR hE
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeScanRun
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableLadder
open TreeTyped Polynomial

variable {I E B C : Type} [Codec I] [Codec E] [Codec B] [Codec C]
variable [LinearOrder I] [Inhabited I] [LinearOrder E]
attribute [local instance] Transport.prodOrder Transport.sumOrder
lemma polynomial_runStep {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} {G : Realizer g} {P : Realizer p} {R : Realizer r}
    {Eq : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {Le : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hP : PolynomialTime P) (hR : PolynomialTime R)
    (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) (hE : PolynomialTime EqE) :
    PolynomialTime (runStepRealizer G P R Eq Le EqE) := by
  unfold runStepRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_scan hG hP hR hEq hLe
  have := polynomial_normalizeState hEq hE
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [Codec I] [Codec E] [Codec B] [Codec C] [Inhabited I] in
lemma fold_runStep {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} (bs : List (List Bool×B)) (c : RunSetup C I E)
    (s : StateTable I (Finset E)) :
    bs.foldl (fun z b=>runStep g p r (b,z)) (c,s)=
      (c,bs.foldl (fun t b=>normalizeState (c.2,scan g p r ((c.1,t),b))) s) := by
  induction bs generalizing s with
  | nil=>rfl
  | cons b bs ih=>exact ih _

omit [Codec B] [Codec C] [Inhabited I] in
lemma fold_normalized_weight {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} (bs : List (List Bool×B)) (c : RunSetup C I E)
    (s : StateTable I (Finset E)) :
    weight (bs.foldl (fun t b=>normalizeState (c.2,scan g p r ((c.1,t),b))) s)≤
      max (weight s) ((weight c.2.1+1)*(weight c.2.2+3)) := by
  induction bs generalizing s with
  | nil=>exact le_max_left _ _
  | cons b bs ih=>
    exact (ih _).trans (max_le (le_trans (normalizeState_weight _ _ _) (le_max_right _ _)) (le_max_right _ _))

lemma polynomial_scanRun {g : C×(I×I)→Bool} {p : LocalPairInput C I (Finset E) B→Finset E×Finset E}
    {r : LocalRefreshInput C I B→Finset E} {G : Realizer g} {P : Realizer p} {R : Realizer r}
    {Eq : Realizer (fun x : I×I=>decide (x.1=x.2))}
    {Le : Realizer (fun x : I×I=>decide (x.1≤x.2))}
    {EqE : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hP : PolynomialTime P) (hR : PolynomialTime R)
    (hEq : PolynomialTime Eq) (hLe : PolynomialTime Le) (hE : PolynomialTime EqE) :
    PolynomialTime (fold (runStepRealizer G P R Eq Le EqE)) := by
  apply polynomial_fold (polynomial_runStep hG hP hR hEq hLe hE) (2*X+(X+1)*(X+3))
  intro _ ⟨c,s⟩ pre _ _
  rw [fold_runStep,weight_prod]
  have h:=fold_normalized_weight (g:=g) (p:=p) (r:=r) pre c s
  simp only [eval_mul,eval_add,eval_X,eval_one,eval_ofNat,weight_prod]
  have hm : max (weight s) ((weight c.2.1+1)*(weight c.2.2+3))≤
      weight s+(weight c.2.1+1)*(weight c.2.2+3) := max_le (by omega) (by omega)
  have hc1 : weight c.2.1≤weight c := by rcases c with ⟨a,⟨k,u⟩⟩; simp only [weight_prod]; omega
  have hc2 : weight c.2.2≤weight c := by rcases c with ⟨a,⟨k,u⟩⟩; simp only [weight_prod]; omega
  have hp : (weight c.2.1+1)*(weight c.2.2+3)≤(weight c+1)*(weight c+3) := Nat.mul_le_mul (by omega) (by omega)
  calc
    _ ≤ 1+weight c+weight s+(weight c+1)*(weight c+3) := by omega
    _ ≤ _ := Nat.add_le_add (by omega) (Nat.mul_le_mul (by omega) (by omega))

end MatchingFPRAS.ExecutableLadder

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

lemma polynomial_guide : PolynomialTime guideRealizer := by
  unfold guideRealizer guide Realizer.fst Realizer.snd
  have := polynomial_membership
  have := polynomial_getDFast ([] : List ℕ)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_execute : PolynomialTime executeRealizer :=
  polynomial_scanRun polynomial_guide polynomial_pair polynomial_refresh polynomial_natEqual
    polynomial_leNat polynomial_natEqual

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeTierWeights
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
lemma polynomial_slotCount : PolynomialTime slotCountRealizer := by
  unfold slotCountRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_successor
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma slotCount_bound (x : TierData) : slotCount x≤((X+1)*X : Polynomial ℕ).eval (weight x) := by
  have ht := (list_length_le_weight x.1.2).trans ((weight_snd x.1).trans (weight_fst x))
  have hq := (list_length_le_weight x.2.1).trans ((weight_fst x.2).trans (weight_snd x))
  simpa [slotCount] using Nat.mul_le_mul (Nat.add_le_add_right ht 1) hq

lemma polynomial_slots : PolynomialTime slotsRealizer :=
  polynomial_boundedRange polynomial_slotCount ((X+1)*X) slotCount_bound

lemma polynomial_weightRow : PolynomialTime weightRowRealizer := by
  unfold weightRowRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_slotWeight
  have := polynomial_quotient
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_weightRows : PolynomialTime weightRowsRealizer := by
  unfold weightRowsRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity polynomial_slots)
    (polynomial_mapWith polynomial_weightRow)

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeGuideTables
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

lemma polynomial_slotUniverse : PolynomialTime slotUniverseRealizer :=
  polynomial_composition polynomial_slots (polynomial_listFinset polynomial_natEqual polynomial_leNat)

lemma polynomial_guideTest : PolynomialTime guideTestRealizer := by
  unfold guideTestRealizer Realizer.fst Realizer.snd
  dsimp only
  apply polynomial_congr
  have := polynomial_quotient
  have := polynomial_successor
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_guideSet : PolynomialTime guideSetRealizer := by
  unfold guideSetRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_slotUniverse)) (polynomial_finsetFilterWith polynomial_guideTest)

lemma polynomial_guideRows : PolynomialTime guideRowsRealizer := by
  unfold guideRowsRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity polynomial_slots)
    (polynomial_mapWith (polynomial_composition polynomial_guideSet polynomial_finsetList))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePrepareLadder
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericLadder
open TreeTyped TreeFraction ExecutableLadder Polynomial TreeTyped.Numbered Replica.Ladder

lemma polynomial_prepareContext : PolynomialTime prepareContextRealizer := by
  unfold prepareContextRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_weightRows
  have := polynomial_guideRows
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_baseTest : PolynomialTime baseTestRealizer := by
  unfold baseTestRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_quotient
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_baseSet : PolynomialTime baseSetRealizer := by
  unfold baseSetRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_identity polynomial_slotUniverse)
    (polynomial_finsetFilterWith polynomial_baseTest)
lemma polynomial_prepareSetup : PolynomialTime prepareSetupRealizer := by
  unfold prepareSetupRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_prepareContext
  have := polynomial_slotUniverse
  have := polynomial_baseSet
  have := polynomial_slots
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_prepareState : PolynomialTime prepareStateRealizer := by
  unfold prepareStateRealizer
  dsimp only [Realizer.fst,Realizer.snd]
  apply polynomial_congr
  have := polynomial_prepareSetup
  have := polynomial_slots
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_preparedRun : PolynomialTime preparedRunRealizer := by
  unfold preparedRunRealizer
  exact polynomial_composition (TreeTyped.polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_prepareState)) polynomial_execute

lemma polynomial_preparedTop : PolynomialTime preparedTopRealizer := by
  unfold preparedTopRealizer
  apply polynomial_congr
  have := polynomial_preparedRun
  have := polynomial_lookup (∅ : Finset ℕ) polynomial_natEqual
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.NumericLadder

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction ExecutableOptions ExecutableLadder

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]
lemma polynomial_markEdge {g : C×E→Options ℕ} {G : Realizer g}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime Eq) : PolynomialTime (markEdgeRealizer G Eq) := by
  unfold markEdgeRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_lookup ([] : List Bool) hE
  have := polynomial_draw (0 : ℕ)
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_assign {g : C×E→Options ℕ} {G : Realizer g}
    {Eq : Realizer (fun x : E×E=>decide (x.1=x.2))}
    (hG : PolynomialTime G) (hE : PolynomialTime Eq) : PolynomialTime (assignRealizer G Eq) := by
  unfold assignRealizer
  exact polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_finsetList))
    (polynomial_mapWith (polynomial_markEdge hG hE))

end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreeNumericMarking
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder ExecutableMarking ExecutableOptions TreeTyped.Numbered UnitRefresh

lemma polynomial_table : PolynomialTime tableRealizer := polynomial_getDFast []
lemma polynomial_assign : PolynomialTime assignRealizer :=
  ExecutableMarking.polynomial_assign polynomial_table polynomial_natEqual

end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_TreePreparedMarked
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

lemma polynomial_sample : PolynomialTime sampleRealizer := by
  unfold sampleRealizer Realizer.fst Realizer.snd
  apply polynomial_congr
  have := polynomial_preparedTop
  have := polynomial_assign
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedMarked
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma polynomial_generatedMarked : PolynomialTime generatedMarkedRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_generatedContext) polynomial_second)
    polynomial_sample)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeObservables
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableMarking
open TreeTyped TreeFraction

variable {C E : Type} [Codec C] [Codec E] [LinearOrder E] [Inhabited E]

omit [Codec C] [LinearOrder E] [Inhabited E] in
lemma polynomial_zeroMarks : PolynomialTime (zeroMarksRealizer (E:=E)) := by
  unfold zeroMarksRealizer
  apply polynomial_congr
  have := polynomial_all
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [LinearOrder E] [Inhabited E] in
lemma polynomial_weighted {q : C×E→Fraction} {Q : Realizer q} (hQ : PolynomialTime Q) :
    PolynomialTime (weightedRealizer Q) := by
  unfold weightedRealizer Realizer.fst
  apply polynomial_congr
  have := polynomial_product
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

omit [LinearOrder E] [Inhabited E] in
lemma polynomial_observableD {q : C×E→Fraction} {Q : Realizer q} (hQ : PolynomialTime Q) :
    PolynomialTime (observableDRealizer Q) := by
  unfold observableDRealizer
  apply polynomial_congr
  have := polynomial_zeroMarks (E:=E)
  have := polynomial_weighted hQ
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

end MatchingFPRAS.ExecutableMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeNumericStatistics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableMarking ExecutableStatistics

variable {E : Type} [Fintype E] [LinearOrder E]
lemma polynomial_reweight : PolynomialTime reweightRealizer := ExecutableLadder.polynomial_lookup (1,1) polynomial_natEqual
end MatchingFPRAS.NumericMarking

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedStage
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma polynomial_generatedReweightArg : PolynomialTime generatedReweightArg := by
  unfold generatedReweightArg
  apply polynomial_congr
  dsimp only [Realizer.fst, Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma polynomial_generatedReweights : PolynomialTime generatedReweightsRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_generatedReweightArg polynomial_sourceReweights)

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_TreeGeneratedCertificate
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
lemma polynomial_applyFirst {f : A→C} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (applyFirst (B:=B) F) := polynomial_composition polynomial_first hF
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableMarking ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics ExecutableScaling ExecutableAdaptive

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma polynomial_certificateSampleArg : PolynomialTime certificateSampleArgRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair (polynomial_fst polynomial_first) polynomial_second)
lemma polynomial_certificateSample : PolynomialTime certificateSampleRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_certificateSampleArg polynomial_generatedMarked)
lemma polynomial_certificateReweights : PolynomialTime certificateReweightsRealizer :=
  polynomial_applyFirst polynomial_generatedReweights
lemma polynomial_certificateArgs : PolynomialTime certificateArgsRealizer :=
  polynomial_congr _ (TreeTyped.polynomial_pair polynomial_certificateReweights polynomial_certificateSample)
lemma polynomial_generatedCertificate_oai : PolynomialTime generatedCertificateRealizer :=
  polynomial_congr _ (polynomial_composition polynomial_certificateArgs (polynomial_observableD polynomial_reweight))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedCertificate_oai := @OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedCertificate_oai
