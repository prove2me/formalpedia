-- Prove2me | solution 1 for OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:42:31.402998+00:00
-- url     : https://prove2.me/submissions/9988b5e5-ee1f-4cb4-a2e8-13a22f3f495c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A011

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
end MatchingFPRAS.TreeTyped

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
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeNumericCosts
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
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

lemma polynomial_columnRead : PolynomialTime columnReadRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first) (polynomial_getDFast 0)

theorem polynomial_columnTotal : PolynomialTime columnTotalRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_columnRead)) polynomial_listSum

theorem polynomial_rowTotal : PolynomialTime rowTotalRealizer :=
  polynomial_composition (polynomial_getDFast []) polynomial_listSum

theorem polynomial_matrixTotal : PolynomialTime matrixTotalRealizer :=
  polynomial_composition (polynomial_map polynomial_listSum) polynomial_listSum

theorem polynomial_matrixEntry : PolynomialTime matrixEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Signed dependent entries from binary margin and matrix lists -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators

theorem polynomial_completionParts : PolynomialTime completionPartsRealizer := by
  have hR : PolynomialTime (composition
      (composition (first (A := CompletionData) (B := ℕ×ℕ)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first
  have hC : PolynomialTime (composition
      (composition (first (A := CompletionData) (B := ℕ×ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have hZ : PolynomialTime (composition
      (first (A := CompletionData) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hI : PolynomialTime (composition
      (second (A := CompletionData) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hJ : PolynomialTime (composition
      (second (A := CompletionData) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_second polynomial_second
  have hi := polynomial_composition (polynomial_pair hI (polynomial_constant 0)) polynomial_natEqual
  have hj := polynomial_composition (polynomial_pair hJ (polynomial_constant 0)) polynomial_natEqual
  have him := polynomial_composition (polynomial_pair hI (polynomial_constant 1)) polynomial_subtract
  have hjm := polynomial_composition (polynomial_pair hJ (polynomial_constant 1)) polynomial_subtract
  have hr := polynomial_composition (polynomial_pair hR hI) (polynomial_getDFast 0)
  have hc := polynomial_composition (polynomial_pair hC hJ) (polynomial_getDFast 0)
  have hrs := polynomial_composition (polynomial_pair hZ him) polynomial_rowTotal
  have hcs := polynomial_composition (polynomial_pair hZ hjm) polynomial_columnTotal
  have ht := polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition hR (polynomial_head 0))
    (polynomial_composition hZ polynomial_matrixTotal)) polynomial_add)
    (polynomial_composition (polynomial_composition hC polynomial_tail) polynomial_listSum)
  have he := polynomial_pair (polynomial_composition
    (polynomial_pair hZ (polynomial_pair him hjm)) polynomial_matrixEntry) (polynomial_constant 0)
  unfold completionPartsRealizer
  exact polynomial_congr _ (polynomial_choose hi (polynomial_choose hj ht
    (polynomial_pair hc hcs)) (polynomial_choose hj (polynomial_pair hr hrs) he))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileExchangeCandidates
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program listing all coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_profileIndices : PolynomialTime profileIndices := by
  apply polynomial_boundedRange polynomial_listLength X
  intro xs
  simpa only [Polynomial.eval_X] using list_length_le_weight xs

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeIndex
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallCellIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable indices for small cells and their crossing cells -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_cellLookup : PolynomialTime cellLookupRealizer :=
  polynomial_indexOf (polynomial_pairEqual polynomial_natEqual polynomial_natEqual)

end ContingencyTables.ProfilePrograms

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

lemma polynomial_smallCellTest : PolynomialTime smallCellTestRealizer := by
  unfold smallCellTestRealizer
  apply polynomial_congr
  apply polynomial_choose
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast 0))
      (polynomial_composition polynomial_first polynomial_second)) polynomial_less
  · exact polynomial_constant true
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0))
      (polynomial_composition polynomial_first polynomial_second)) polynomial_less

theorem polynomial_smallCellCatalog : PolynomialTime smallCellCatalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_cellPairs))
    (polynomial_filterWith polynomial_smallCellTest)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallViewLookupProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lookup of the sparse small-cell view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_lookupView : PolynomialTime lookupViewRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_first)) polynomial_cellLookup))
    (polynomial_getDFast 0)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallLineSumProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column sums of the sparse stored view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators

lemma polynomial_lineEntry (row : Bool) : PolynomialTime (lineEntryRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_choose (polynomial_constant row)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_second))))
    polynomial_lookupView

lemma polynomial_lineIndices : PolynomialTime lineIndices := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) X
  intro z
  have hw : weight z.1.2≤weight z := by
    rcases z with ⟨⟨lookupData,coords⟩,i⟩
    simp only [weight_prod]
    omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.2).trans hw

theorem polynomial_lineSum (row : Bool) : PolynomialTime (lineSumRealizer row) :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_lineIndices)
    (polynomial_mapWith (polynomial_lineEntry row))) polynomial_listSum

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallComplementProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the complemented small column view -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_complementValues : PolynomialTime complementValuesRealizer :=
  polynomial_mapWith polynomial_subtract

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallMarginTestProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial residual-margin inequality and equality tests -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_marginList (row : Bool) : PolynomialTime (marginListRealizer row) :=
  polynomial_choose (polynomial_constant row)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)

lemma polynomial_lineArgument (row : Bool) : PolynomialTime (lineArgumentRealizer row) :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition polynomial_first (polynomial_marginList (!row)))) polynomial_second

lemma polynomial_marginValue (row : Bool) : PolynomialTime (marginValueRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_marginList row)) polynomial_second)
    (polynomial_getDFast 0)

lemma polynomial_lineValue (row : Bool) : PolynomialTime (lineValueRealizer row) :=
  polynomial_composition (polynomial_lineArgument row) (polynomial_lineSum row)

lemma polynomial_marginIndices (row : Bool) : PolynomialTime (marginIndices row) := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_marginList row) polynomial_listLength) X
  intro z
  have hw : weight (marginList row z)≤weight z := by
    rcases z with ⟨⟨lookupData,⟨r,c⟩⟩,U⟩
    cases row <;> simp only [marginList,Bool.false_eq_true,ite_false,ite_true, if_true,weight_prod] <;> omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight (marginList row z)).trans hw

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileValidator
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary validator for the positive profile space -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_profileViews : PolynomialTime profileViews :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second

lemma polynomial_profileCatalog : PolynomialTime profileCatalog :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

lemma polynomial_profileMargins : PolynomialTime profileMargins :=
  polynomial_composition polynomial_first polynomial_second

lemma polynomial_profileView (row : Bool) : PolynomialTime (profileView row) :=
  polynomial_choose (polynomial_constant row)
    (polynomial_composition polynomial_profileViews polynomial_first)
    (polynomial_composition polynomial_profileViews polynomial_second)

lemma polynomial_profileColumnView : PolynomialTime profileColumnView :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_profileViews polynomial_second)) polynomial_complementValues

lemma polynomial_profileLineData (row : Bool) : PolynomialTime (profileLineData row) :=
  polynomial_pair (polynomial_pair (polynomial_pair polynomial_profileCatalog
    (polynomial_choose (polynomial_constant row) (polynomial_profileView true)
      polynomial_profileColumnView)) polynomial_profileMargins) polynomial_second

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallProfileFlatCode
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Flattening the two stored views for coordinate exchanges -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_flattenViews : PolynomialTime flattenViewsRealizer := polynomial_append

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileCodeEquality
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality and duplicate removal for profile codes -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_listEntryEqual : PolynomialTime listEntryEqualRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_natEqual

lemma polynomial_equalityIndices : PolynomialTime equalityIndices :=
  polynomial_composition polynomial_first polynomial_profileIndices

lemma polynomial_listNatTest : PolynomialTime listNatTestRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listLength)
      (polynomial_composition polynomial_second polynomial_listLength)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_identity polynomial_equalityIndices)
      (polynomial_mapWith polynomial_listEntryEqual)) polynomial_all)) polynomial_boolAnd)

theorem polynomial_listNatEqual : PolynomialTime listNatEqual :=
  polynomial_congr _ polynomial_listNatTest

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeNeighbors
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program for the full physical neighbor list -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_candidateData : PolynomialTime candidateDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_profileCatalog) polynomial_second)
    (polynomial_composition polynomial_first polynomial_profileMargins))
    (polynomial_composition polynomial_first polynomial_second)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperComputedCatalog
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The small-cell ordering is computed from the encoded margins -/

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "small" => paperSmall r c

/-- The proof-level cell equivalence enumerates exactly the list made
by the polynomial catalog program, in the same order. -/
theorem computedCellEquiv_catalog :
    cellCatalog small (computedCellEquiv r c)=computedCatalog r c := by
  apply List.ext_getElem
  · simp only [cellCatalog,List.length_ofFn]
  · intro i hi hj
    simp only [cellCatalog,List.getElem_ofFn]
    exact catalogCell_coordinates r c ⟨i,hj⟩

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPreparedProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the complete proposal input from binary margin lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_squareNat : PolynomialTime squareNat :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_identity) polynomial_multiply

lemma polynomial_fourthPower : PolynomialTime fourthPower :=
  polynomial_congr _ (polynomial_composition polynomial_squareNat polynomial_squareNat)

lemma polynomial_fifthPower : PolynomialTime fifthPower :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_fourthPower polynomial_identity) polynomial_multiply)

lemma polynomial_twentiethPower : PolynomialTime twentiethPower :=
  polynomial_congr _ (polynomial_composition polynomial_fifthPower polynomial_fourthPower)

theorem polynomial_marginDimension : PolynomialTime marginDimensionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 10)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_listLength)
        polynomial_successor)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_listLength)
        polynomial_successor)) polynomial_multiply)) polynomial_add

theorem polynomial_marginThreshold : PolynomialTime marginThresholdRealizer :=
  polynomial_composition polynomial_marginDimension polynomial_twentiethPower

theorem polynomial_marginCatalog : PolynomialTime marginCatalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_marginThreshold)
    polynomial_smallCellCatalog

theorem polynomial_prepareProfileInput : PolynomialTime prepareProfileInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_marginCatalog) polynomial_second)
    polynomial_first) (polynomial_composition polynomial_first polynomial_marginThreshold)

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open scoped Classical
open SmallContextCoordinates ProfilePrograms FirstPaperPhysicalMarginal CompletionCounts

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma prepareProfileInput_eq (x : PaperStates r c) :
    prepareProfileInput ((List.ofFn r,List.ofFn c),stateCode r c (computedCellEquiv r c) x)=
      stateCodeData r c (computedCellEquiv r c) x := by
  unfold prepareProfileInput stateCodeData codeCheckData
  rw [computedCellEquiv_catalog]
  simp only [marginCatalog,marginThreshold_ofFn,computedCatalog]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of one dense exponent component -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms

lemma polynomial_eighthPower : PolynomialTime eighthPower :=
  polynomial_congr _ (polynomial_composition polynomial_fourthPower polynomial_squareNat)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseExponentListProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing all dense exponent components and their maximum -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ContingencyTables.ProfilePrograms Polynomial
open scoped BigOperators

lemma polynomial_maximum : PolynomialTime maximum := by
  unfold maximum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_second polynomial_first)

lemma foldMaximum_size (xs : List ℕ) (a S : ℕ) (ha : a.size≤S)
    (hx : ∀ b∈xs,b.size≤S) :
    (xs.foldl (fun a b => max b a) a).size≤S := by
  induction xs generalizing a with
  | nil => exact ha
  | cons b bs ih =>
    apply ih
    · rcases le_total b a with h|h
      · simpa only [max_eq_right h] using ha
      · simpa only [max_eq_left h] using hx b (by simp)
    · intro c hc
      exact hx c (by simp [hc])

theorem polynomial_listMaximum : PolynomialTime listMaximumRealizer := by
  apply polynomial_fold polynomial_maximum (4*X+1)
  intro xs a pre post he
  let S := weight (xs,a)
  have ha : a.size≤S := (size_le_weight a).trans (weight_snd (xs,a))
  have hb : ∀ b∈pre,b.size≤S := by
    intro b hb
    exact (size_le_weight b).trans ((weight_mem (as := xs) (by simp [he,hb])).trans
      (weight_fst (xs,a)))
  have hs := foldMaximum_size pre a S ha hb
  have hw := weight_nat_le (pre.foldl (fun a b => max b a) a)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  change _≤4*S+1
  omega

theorem polynomial_exponentCellData : PolynomialTime exponentCellDataRealizer := by
  unfold exponentCellDataRealizer
  apply polynomial_pair
  · apply polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    apply polynomial_composition _ polynomial_minimum
    apply polynomial_pair
    · apply polynomial_composition _ (polynomial_getDFast 0)
      exact polynomial_pair (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_first)
        (polynomial_composition polynomial_second polynomial_first)
    · apply polynomial_composition _ (polynomial_getDFast 0)
      exact polynomial_pair (polynomial_composition
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
          polynomial_first) polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_completionParts

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleCellProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary conversion from a grid coordinate to a free integer entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped
open GridBoundary

lemma polynomial_shiftedCell : PolynomialTime shiftedCellRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_successor)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_successor))

theorem polynomial_gridCellWidth : PolynomialTime gridCellWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_shiftedCell polynomial_exponentCellData) polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_eighthPower)) polynomial_quotient

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMatrixLayoutProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial conversion between flat and rectangular grid encodings -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_sliceRow : PolynomialTime sliceRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply))
      polynomial_dropFast)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_takeFast

theorem polynomial_layoutRows : PolynomialTime layoutRowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_tail) polynomial_listLength) X
  intro z
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans ((list_length_le_weight z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z)))

theorem polynomial_layoutRow : PolynomialTime layoutRowRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_tail) polynomial_listLength)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second) polynomial_sliceRow

theorem polynomial_unflattenGrid : PolynomialTime unflattenGridRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_layoutRows)
    (polynomial_mapWith polynomial_layoutRow)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseFlatExponentProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Evaluating the dense exponent on the flat coordinate encoding -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

theorem polynomial_flatToGridData : PolynomialTime flatToGridDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_first polynomial_unflattenGrid)) polynomial_second

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetWidths
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the actual variable-width offset word layout -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary FairBits

theorem polynomial_freeCells : PolynomialTime freeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_tail)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second) polynomial_tail))
    polynomial_cellPairs

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The complete dense trial as a polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

theorem polynomial_fiftiethPower : PolynomialTime fiftiethPower :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition polynomial_fifthPower polynomial_squareNat) polynomial_fifthPower)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FirstSuccessProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial first-success selection for a supplied list of trial words -/

namespace ContingencyTables.FirstSuccessProgram
open MatchingFPRAS.TreeTyped

variable {A B W : Type} [Codec A] [Codec B] [Codec W] [Inhabited B]

theorem polynomial_default : PolynomialTime (defaultRealizer (B := B)) := by
  unfold defaultRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

end ContingencyTables.FirstSuccessProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MaximalListProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a maximal margin in binary -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_maximumIndex : PolynomialTime maximumIndexRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 0))
      polynomial_listMaximum) polynomial_identity) (polynomial_indexOf polynomial_natEqual)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseSwapProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column permutations for dense input normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_swapZeroIndex : PolynomialTime swapZeroIndexRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0)) polynomial_natEqual)
    polynomial_first (polynomial_choose
      (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_natEqual)
      (polynomial_constant 0) polynomial_second))

variable {A : Type} [Codec A] [Inhabited A]

theorem polynomial_swapZeroEntry : PolynomialTime (swapZeroEntryRealizer (A := A)) :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_swapZeroIndex)) (polynomial_getDFast default)

omit [Inhabited A] in
theorem polynomial_swapZeroIndices : PolynomialTime (swapZeroIndicesRealizer (A := A)) := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.2).trans (weight_snd z)

theorem polynomial_swapZeroList : PolynomialTime (swapZeroListRealizer (A := A)) :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_swapZeroIndices)
    (polynomial_mapWith polynomial_swapZeroEntry)

theorem polynomial_swapMatrixColumns : PolynomialTime swapMatrixColumnsRealizer :=
  polynomial_mapWith polynomial_swapZeroList

theorem polynomial_swapMatrix : PolynomialTime swapMatrixRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_swapZeroList)) polynomial_swapMatrixColumns

open scoped Classical

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseNormalizeProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Moving maximal margins into the distinguished positions -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_swapMargins : PolynomialTime swapMarginsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) polynomial_swapZeroList)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_swapZeroList)

theorem polynomial_marginIndices : PolynomialTime marginIndicesRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_maximumIndex)
    (polynomial_composition polynomial_second polynomial_maximumIndex)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyRowComplexity
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary cost of a greedy row pass -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_cellMinimum : PolynomialTime minimum := by
  unfold minimum
  exact polynomial_congr _ (polynomial_choose polynomial_less polynomial_first polynomial_second)

lemma polynomial_rowCell : PolynomialTime rowCellRealizer := by
  have hA : PolynomialTime (composition
      (second (A := ℕ) (B := RowAccumulator)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hC : PolynomialTime (first (A := ℕ) (B := RowAccumulator)) := polynomial_first
  have hQ := polynomial_composition (polynomial_pair hA hC) polynomial_cellMinimum
  have hX : PolynomialTime (composition
      (composition (second (A := ℕ) (B := RowAccumulator)) second) first) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first
  have hY : PolynomialTime (composition
      (composition (second (A := ℕ) (B := RowAccumulator)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second
  unfold rowCellRealizer
  exact polynomial_congr _ (polynomial_pair
    (polynomial_composition (polynomial_pair hA hQ) polynomial_subtract)
    (polynomial_pair (polynomial_composition (polynomial_pair hQ hX) polynomial_listCons)
      (polynomial_composition
        (polynomial_pair (polynomial_composition (polynomial_pair hC hQ) polynomial_subtract) hY)
        polynomial_listCons)))

/-- No entry produced by a row pass exceeds its original column bound;
the binary list sizes therefore grow by only a constant factor. -/
lemma listSplitRow_bounds (a : ℕ) (cs : List ℕ) :
    (listSplitRow a cs).1≤a ∧
    weight (listSplitRow a cs).2.1≤4*weight cs ∧
    weight (listSplitRow a cs).2.2≤4*weight cs := by
  induction cs generalizing a with
  | nil => simp [listSplitRow,weight_nil]
  | cons c cs ih =>
    have ht := ih (a-min a c)
    have hq := weight_nat_small (min_le_right a c)
    have hc := weight_nat_small (Nat.sub_le c (min a c))
    simp only [listSplitRow,weight_cons]
    exact ⟨ht.1.trans (Nat.sub_le _ _),by omega,by omega⟩

lemma polynomial_rowFold : PolynomialTime (fold rowCellRealizer) := by
  apply polynomial_fold polynomial_rowCell (12*X+10)
  rintro cs ⟨a,xs,ys⟩ pre post he
  have ht := listSplitRow_bounds a pre
  have ha := weight_nat_small ht.1
  have hpre := weight_prefix he
  have hx := weight_append (listSplitRow a pre).2.1.reverse xs
  have hy := weight_append (listSplitRow a pre).2.2.reverse ys
  rw [weight_reverse] at hx hy
  rw [fold_rowCell]
  simp only [weight_prod,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

theorem polynomial_rowSplit : PolynomialTime rowSplitRealizer := by
  unfold rowSplitRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition
  · apply polynomial_composition
    · exact polynomial_pair polynomial_second
        (polynomial_pair polynomial_first (polynomial_constant ([],[])))
    · exact polynomial_rowFold
  · exact polynomial_pair polynomial_first (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_reverse)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_second)
        polynomial_reverse))

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyTableMachine
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A fixed binary list program constructing the greedy table -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped

lemma listSplitRow_ofFn {n : ℕ} (a : ℕ) (cs : Fin n → ℕ) :
    listSplitRow a (List.ofFn cs)=
      ((splitRow a cs).unused,
        (List.ofFn (splitRow a cs).assigned,List.ofFn (splitRow a cs).remaining)) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [List.ofFn_succ,listSplitRow,splitRow,ih,Fin.cons_zero,Fin.cons_succ]

/-- The compiled list program computes the same feasible matrix used
by the probability analysis. -/
theorem listMatrix_ofFn {m n : ℕ} (rs : Fin m → ℕ) (cs : Fin n → ℕ) :
    listMatrix (List.ofFn rs) (List.ofFn cs)=
      List.ofFn (fun i => List.ofFn (matrix rs cs i)) := by
  induction m generalizing cs with
  | zero => rfl
  | succ m ih =>
    simp only [List.ofFn_succ,listMatrix,listSplitRow_ofFn,ih,matrix,Fin.cons_zero,
      Fin.cons_succ]

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_GreedyTableComplexity
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary cost of the full greedy table constructor -/

namespace ContingencyTables.GreedyFeasibleTable
open MatchingFPRAS.TreeTyped Polynomial

private lemma listLE_trans {as bs cs : List ℕ}
    (hab : List.Forall₂ (·≤·) as bs) (hbc : List.Forall₂ (·≤·) bs cs) :
    List.Forall₂ (·≤·) as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact .nil
  | cons hab htail ih =>
    cases hbc with
    | cons hbc hrest => exact .cons (hab.trans hbc) (ih hrest)

private lemma weight_listLE {as bs : List ℕ} (h : List.Forall₂ (·≤·) as bs) :
    weight as≤4*weight bs := by
  induction h with
  | nil => simp
  | cons hab htail ih =>
    have hn := weight_nat_small hab
    simp only [weight_cons]
    omega

lemma listSplitRow_le (a : ℕ) (cs : List ℕ) :
    List.Forall₂ (·≤·) (listSplitRow a cs).2.1 cs ∧
    List.Forall₂ (·≤·) (listSplitRow a cs).2.2 cs := by
  induction cs generalizing a with
  | nil => exact ⟨.nil,.nil⟩
  | cons c cs ih =>
    exact ⟨.cons (min_le_right _ _) (ih (a-min a c)).1,
      .cons (Nat.sub_le _ _) (ih (a-min a c)).2⟩

private lemma tableFold_bounds (rs cs base : List ℕ) (rows : List (List ℕ))
    (hc : List.Forall₂ (·≤·) cs base) :
    List.Forall₂ (·≤·) (rs.foldl (fun z a => tableRow (a,z)) (cs,rows)).1 base ∧
    weight (rs.foldl (fun z a => tableRow (a,z)) (cs,rows)).2≤
      rs.length*(4*weight base+1)+weight rows := by
  induction rs generalizing cs rows with
  | nil => exact ⟨hc,by simp⟩
  | cons a rs ih =>
    have hr := listSplitRow_le a cs
    have hout := weight_listLE (listLE_trans hr.1 hc)
    have ht := ih (listSplitRow a cs).2.2 ((listSplitRow a cs).2.1::rows)
      (listLE_trans hr.2 hc)
    refine ⟨ht.1,?_⟩
    change weight (rs.foldl (fun z a => tableRow (a,z))
      ((listSplitRow a cs).2.2,(listSplitRow a cs).2.1::rows)).2≤_
    simp only [List.length_cons,weight_cons] at ht ⊢
    nlinarith [ht.2]

lemma polynomial_tableRow : PolynomialTime tableRowRealizer := by
  have hrow : PolynomialTime (composition
      (pair (first (A := ℕ) (B := TableAccumulator)) (composition second first))
      rowSplitRealizer) :=
    polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_rowSplit
  have hrows : PolynomialTime (composition
      (second (A := ℕ) (B := TableAccumulator)) second) :=
    polynomial_composition polynomial_second polynomial_second
  unfold tableRowRealizer
  exact polynomial_congr _ (polynomial_pair
    (polynomial_composition (polynomial_composition hrow polynomial_second) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition hrow polynomial_second) polynomial_first)
      hrows) polynomial_listCons))

lemma polynomial_tableFold : PolynomialTime (fold tableRowRealizer) := by
  apply polynomial_fold polynomial_tableRow (12*(X+1)^2)
  rintro rs ⟨cs,rows⟩ pre post he
  have hc : List.Forall₂ (·≤·) cs cs := by
    induction cs with
    | nil => exact .nil
    | cons c cs ih => exact .cons le_rfl ih
  have ht := tableFold_bounds pre cs cs rows hc
  have hw := weight_listLE ht.1
  have hp := (list_length_le_weight pre).trans (weight_prefix he)
  let S := weight (rs,(cs,rows))
  have hrs : weight rs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hcs : weight cs≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hrows : weight rows≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hpre : pre.length≤S := hp.trans hrs
  change weight (pre.foldl (fun z a => tableRow (a,z)) (cs,rows))≤_
  rw [←Prod.eta (pre.foldl (fun z a => tableRow (a,z)) (cs,rows)),weight_prod]
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _≤12*(S+1)^2
  have hm := Nat.mul_le_mul hpre (show 4*weight cs+1≤4*S+1 by omega)
  nlinarith [ht.2]

/-- The single fixed program has polynomial bit cost, uniformly in both
dimensions and all binary margin values. -/
theorem polynomial_table : PolynomialTime tableRealizer := by
  unfold tableRealizer
  dsimp only
  apply polynomial_congr
  apply polynomial_composition _ polynomial_reverse
  apply polynomial_composition _ polynomial_second
  apply polynomial_composition _ polynomial_tableFold
  exact polynomial_pair polynomial_first
    (polynomial_pair polynomial_second (polynomial_constant []))

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCanonicalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dense sampling from margins with a computed grid and fallback -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

theorem polynomial_zeroGrid : PolynomialTime zeroGridRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_first polynomial_tail)
      (polynomial_composition polynomial_second polynomial_tail)) polynomial_cellPairs)
    (polynomial_map (polynomial_constant 0))

end ContingencyTables.DensePrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_FiniteGridWords
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit finite-box state enumeration, independent of sampling precision -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

lemma polynomial_clippedGridPowerInput : PolynomialTime clippedGridPowerInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_listLength)) polynomial_minNat)

lemma polynomial_clippedGridPower : PolynomialTime clippedGridPowerRealizer := by
  apply work_composition polynomial_clippedGridPowerInput BinaryPowerPrograms.work_power
    (2*Polynomial.X)
  intro z
  have hl := (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))
  have hw := (weight_snd z.1).trans (weight_fst z)
  have hm := min_le_right z.2 z.1.1.length
  simp only [clippedGridPowerInput,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

lemma gridStateCount_eq (z : GridEnumerationData) : gridStateCount z=z.2^z.1.length := by
  simp [gridStateCount,clippedGridPower,clippedGridPowerInput,BinaryPowerPrograms.power_eq]

private lemma map_range_eq_ofFn {A : Type*} (f : ℕ → A) (N : ℕ) :
    (List.range N).map f=List.ofFn (fun i : Fin N => f i.val) := by
  simpa using (List.ofFn_getElem_eq_map (List.range N) f).symm

lemma gridCoordinates_eq (z : GridEnumerationData) (x : ℕ) :
    gridCoordinates (z,x)=List.ofFn
      (fun i : Fin z.1.length => x/z.2^i.val % z.2) := by
  rw [gridCoordinates,gridCoordinateIndices,map_range_eq_ofFn]
  apply congrArg List.ofFn
  funext i
  simp [gridCoordinate,clippedGridPower,clippedGridPowerInput,
    BinaryPowerPrograms.power_eq]

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_UnaryMarkers
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the bounded unary loop markers used in tabulation -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma unaryMarkers_length (n : ℕ) : (unaryMarkers n).length=n := by
  simp only [unaryMarkers,List.length_map,List.length_range]

/-- Unary markers are charged by the actual requested loop length. -/
lemma work_unaryMarkers : WorkBound unaryMarkersRealizer id :=
  work_then_polynomial range_numeric_work (polynomial_map (polynomial_constant false))

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_GridIndexProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary indexing into the explicitly enumerated grid -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators

lemma polynomial_gridIndexPowerInput : PolynomialTime gridIndexPowerInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_map (polynomial_constant false)))
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second

lemma polynomial_gridIndexTerm : PolynomialTime gridIndexTermRealizer := by
  unfold gridIndexTermRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition polynomial_gridIndexPowerInput polynomial_clippedGridPower))
    polynomial_multiply

lemma polynomial_gridIndexIndices : PolynomialTime gridIndexIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength)
    Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

/-- Index computation is polynomial in the binary grid coordinates and
base; the exponent loops are bounded by the coordinate list length. -/
theorem polynomial_gridIndex : PolynomialTime gridIndexRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_gridIndexIndices)
    (polynomial_mapWith polynomial_gridIndexTerm)) polynomial_listSum

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CompletionEnumerationProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit free-box enumeration with binary completion tests -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open scoped BigOperators Classical

lemma polynomial_completionEnumerationData : PolynomialTime completionEnumerationDataRealizer := by
  unfold completionEnumerationDataRealizer
  exact polynomial_pair (polynomial_composition polynomial_zeroGrid
    (polynomial_map (polynomial_constant false)))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_listSum)
      polynomial_successor)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the full integer law of an initialized dense draw -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary
open scoped BigOperators Classical

lemma polynomial_rawDrawParameters : PolynomialTime rawDrawParametersRealizer := by
  unfold rawDrawParametersRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_first polynomial_zeroGrid))
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_composition polynomial_second polynomial_second)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCheck
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary row and column checks for original-table candidates -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma polynomial_originalColumnTotals : PolynomialTime originalColumnTotalsRealizer := by
  unfold originalColumnTotalsRealizer
  apply polynomial_composition _ (polynomial_mapWith polynomial_columnTotal)
  apply polynomial_pair polynomial_second
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma polynomial_originalTableTest : PolynomialTime originalTableTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second (polynomial_map polynomial_listSum))
      (polynomial_composition polynomial_first polynomial_first)) polynomial_listNatEqual)
    (polynomial_composition (polynomial_pair polynomial_originalColumnTotals
      (polynomial_composition polynomial_first polynomial_second)) polynomial_listNatEqual)) polynomial_boolAnd

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating original tables by all their bounded entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma polynomial_originalLayoutMargins : PolynomialTime originalLayoutMarginsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_first) polynomial_listCons)
    (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_second) polynomial_listCons)

lemma polynomial_originalFreeMatrix : PolynomialTime originalFreeMatrixRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_originalLayoutMargins) polynomial_second)
    polynomial_unflattenGrid

lemma polynomial_originalCandidate : PolynomialTime originalCandidateRealizer :=
  polynomial_choose (polynomial_composition
    (polynomial_pair polynomial_first polynomial_originalFreeMatrix) polynomial_originalTableTest)
    (polynomial_composition polynomial_originalFreeMatrix polynomial_some) (polynomial_constant none)

lemma polynomial_originalEnumerationData : PolynomialTime originalEnumerationDataRealizer :=
  polynomial_composition polynomial_originalLayoutMargins polynomial_completionEnumerationData

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperBinaryParameters
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary lengths for the small-chain capacity bound -/

namespace ContingencyTables.SmallGraphProfiles

open scoped BigOperators Classical
open CompletionCounts

universe u
variable {I J : Type u} [Fintype I] [Fintype J]
variable (r : I → ℕ) (c : J → ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)

lemma stateBound_clog_le :
    Nat.clog 2 (stateBound r c+2) ≤ Nat.clog 2 ((∑ i,r i)+1)+20*d+2 := by
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have h13 : d^13 ≤ 2^(20*d) :=
    (nat_pow_le_two_pow d 13).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have h20 : d^20 ≤ 2^(20*d) := by simpa only [Nat.mul_comm] using nat_pow_le_two_pow d 20
  have h4 : 4 ≤ 2^(20*d) := by
    exact (by decide : 4 ≤ 2^2).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hrest : d*d^12+d^20+4 ≤ 2^(20*d+2) := by
    have he : d*d^12=d^13 := by ring
    rw [he,pow_add]
    norm_num
    omega
  have hpow : 1 ≤ 2^(20*d+2) := one_le_pow₀ (by decide)
  have hn := Nat.le_pow_clog (by decide : 1<2) ((∑ i,r i)+1)
  apply Nat.clog_le_of_le_pow
  calc
    stateBound r c+2=(∑ i,r i)+(d*d^12+d^20+4) := by unfold stateBound; omega
    _ ≤ (∑ i,r i)+2^(20*d+2) := Nat.add_le_add_left hrest _
    _ ≤ ((∑ i,r i)+1)*2^(20*d+2) := by
      have hm := Nat.mul_le_mul_left (∑ i,r i) hpow
      simpa only [mul_one,add_mul,one_mul] using Nat.add_le_add_right hm (2^(20*d+2))
    _ ≤ 2^(Nat.clog 2 ((∑ i,r i)+1))*2^(20*d+2) := Nat.mul_le_mul_right _ hn
    _ = 2^(Nat.clog 2 ((∑ i,r i)+1)+20*d+2) := by
      rw [←pow_add]
      congr 1

lemma smallBinaryLength_le :
    smallBinaryLength r c ≤ 21*d+Nat.clog 2 ((∑ i,r i)+1)+2 := by
  have h := stateBound_clog_le r c
  unfold smallBinaryLength
  omega

end ContingencyTables.SmallGraphProfiles

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

namespace MatchingFPRAS.TreeTyped
variable {A B A' B' : Type} [Codec A] [Codec B] [Codec A'] [Codec B']
lemma polynomial_reencode {f : A→B} (F : Realizer f) (i : A'→A) (g : A'→B')
    (hi : ∀ a,encode (i a)=encode a) (hg : ∀ a,encode (g a)=encode (f (i a)))
    (hF : PolynomialTime F) : PolynomialTime (F.reencode i g hi hg) := by
  obtain ⟨p,hp⟩:=hF
  refine ⟨p,fun a=>?_⟩
  have h:=hp (i a)
  simpa only [Realizer.reencode,weight,hi a,←hg a] using h
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.LiteralCodec
open TreeTyped TreeData TreeFunction

lemma weight_word (as : List Symbol) : weight as=18*as.length+1 := by
  induction as with
  | nil => rfl
  | cons a as ih => rw [weight_cons,weight_symbol,ih,List.length_cons]; omega

lemma polynomial_val : PolynomialTime valRealizer :=
  polynomial_reencode _ _ _ _ _ (polynomial_composition polynomial_first polynomial_listLength)

end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Tapes_Parse
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralParse
open TreeTyped TreeData TreeFunction Polynomial LiteralCodec

lemma polynomial_eqSymbol (a : Symbol) : PolynomialTime (eqSymbol a) := by
  unfold eqSymbol; apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_val (polynomial_constant _)) polynomial_natEqual

lemma polynomial_numStep : PolynomialTime numStepRealizer := by
  unfold numStepRealizer
  apply polynomial_congr
  have := polynomial_eqSymbol 3
  have := polynomial_eqSymbol 2
  have := polynomial_eqSymbol 1
  have := polynomial_head (0:ℕ)
  have := polynomial_tail (A:=ℕ)
  simp only [Realizer.mulNat, Realizer.addNat]
  ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe | apply polynomial_congr)))

lemma weight_double (n : ℕ) : weight (2*n)≤weight n+2 := by
  by_cases hn:n=0
  · subst n; simp only [Nat.mul_zero]; omega
  rw [weight_nat,Nat.bit0_bits n hn]
  rw [weight_cons]
  change 1+1+weight n≤_
  omega
lemma weight_double_one (n : ℕ) : weight (2*n+1)≤weight n+4 := by
  rw [weight_nat,Nat.bit1_bits,weight_cons]
  change 1+3+weight n≤_
  omega

lemma numStep_weight (a : Symbol) (ns : List ℕ) : weight (numStep (a,ns))≤weight ns+6 := by
  unfold numStep
  dsimp only
  split_ifs
  · rw [weight_cons]; change 1+1+weight ns≤_; omega
  · cases ns with
    | nil => change 3≤1+6; omega
    | cons n ns =>
      simp only [List.headD_cons,List.tail_cons,weight_cons]
      have h:=weight_double n
      omega
  · cases ns with
    | nil => change 7≤7; omega
    | cons n ns =>
      simp only [List.headD_cons,List.tail_cons,weight_cons]
      have h:=weight_double_one n
      omega
  · omega

lemma fold_weight (as : List Symbol) (ns : List ℕ) :
    weight (as.foldl (fun ns a=>numStep (a,ns)) ns)≤weight ns+6*as.length := by
  induction as generalizing ns with
  | nil => simp
  | cons a as ih =>
    have h:=ih (numStep (a,ns))
    have h':=numStep_weight a ns
    simp only [List.foldl_cons,List.length_cons]
    omega
lemma polynomial_numFold : PolynomialTime (fold numStepRealizer) := by
  apply polynomial_fold polynomial_numStep (7*X)
  intro as ns pre post he
  have h:=fold_weight pre ns
  have hlen : pre.length≤as.length := by rw [he,List.length_append]; omega
  have hlen':=list_length_le_weight as
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

lemma polynomial_parse : PolynomialTime parseRealizer := by
  unfold parseRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair polynomial_reverse (polynomial_constant _)) polynomial_numFold

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

lemma polynomial_marginLists : PolynomialTime marginListsRealizer := by
  have hM : PolynomialTime (head (A := ℕ) 0) := polynomial_head 0
  have hN : PolynomialTime (composition (tail (A := ℕ)) (head 0)) :=
    polynomial_composition polynomial_tail (polynomial_head 0)
  have hD : PolynomialTime (composition (tail (A := ℕ)) tail) :=
    polynomial_composition polynomial_tail polynomial_tail
  unfold marginListsRealizer
  exact polynomial_congr _ (polynomial_pair
    (polynomial_composition (polynomial_pair hD hM) polynomial_takeFast)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair hD hM) polynomial_dropFast) hN)
      polynomial_takeFast))

lemma natWords_fold (ns tail : List ℕ) :
    (ns.flatMap encodeNat).foldr (fun a ns => numStep (a,ns)) tail=ns++tail := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold,List.cons_append]

lemma parse_natWords (ns : List ℕ) : parse (ns.flatMap encodeNat)=ns := by
  simpa only [parse,List.append_nil] using natWords_fold ns []

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

end ContingencyTables.GreedyFeasibleTable

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_StateSuccessEntries
attribute [-instance] _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The successful state-to-table map removes precisely the large padding -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma originalStateSuccessEquiv_symm_entry (r : I → ℕ) (c : J → ℕ)
    (a : SuccessfulStateJoint r c) (i : I) (j : J) :
    ((originalStateSuccessEquiv r c).symm a).val i j=
      a.val.2.val.val.1 i j-
        largePadding (paperLarge r c) ((dimensionAllowance (I := I) (J := J))^12) i j := by
  change (unpadSuccessfulJoint r c ((successStateEquiv r c).symm a)).val i j=_
  rw [unpadSuccessfulJoint_val]
  apply congrArg (fun t : ℕ => t-_)
  exact congrArg (fun t => t.val.1 i j)
    (balancedJointFromState_projection r c a.val a.property.1)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileEntries
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The initial profile is read directly from the original table -/

namespace ContingencyTables.SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open PaddedCompletions CompletionCounts SmallContextCoordinates
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma tableState_first (X : Table r c) (i : Fin m) (j : Fin n)
    (hs : paperSmall r c i j=true) :
    physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) (tableState r c X)
      (⟨(i,j),hs⟩,false)=X.val i j := by
  let a := originalStateSuccessEquiv r c X
  have he := originalStateSuccessEquiv_symm_entry r c a i j
  rw [Equiv.symm_apply_apply] at he
  have hp : largePadding (paperLarge r c) (d^12) i j=0 := by
    simp only [paperLarge,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,hs,
      Bool.true_eq_false,ite_false]
  rw [hp,Nat.sub_zero] at he
  exact (a.val.2.property.2.2.1 i j hs).1.symm.trans he.symm

lemma tableState_second (X : Table r c) (a : Cells (paperSmall r c)) :
    physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) (tableState r c X)
      (a,true)=d^20-X.val a.val.1 a.val.2 := by
  have hb := (originalStateSuccessEquiv r c X).property.1
  have hsum := (balanced_iff_cellSums (paperSmall r c) (stateCapacity r c)
    (physicalProfile (paperSmall r c) (stateCapacity r c) r c (d^12) (tableState r c X))
    (fun a => (physicalProfile_feasible r c (tableState r c X)).bounded (a,true))).mp hb a
  have he := tableState_first r c X a.val.1 a.val.2 a.property
  have hcap := stateCapacity_small r c a.val.1 a.val.2 a.property
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells (paperSmall r c))=a :=
    Subtype.ext (Prod.eta a.val)
  rw [heta] at he
  rw [he,hcap] at hsum
  omega

lemma tableState_code (e : Fin q ≃ Cells (paperSmall r c)) (X : Table r c) :
    stateCode r c e (tableState r c X)=
      (List.ofFn (fun i => X.val (e i).val.1 (e i).val.2),
        List.ofFn (fun i => d^20-X.val (e i).val.1 (e i).val.2)) := by
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact tableState_first r c X _ _ (e i).property
  · apply congrArg List.ofFn
    funext i
    exact tableState_second r c X (e i)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the initial profile directly from the greedy table -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_originalFirstView : PolynomialTime originalFirstViewRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_first)) (polynomial_mapWith polynomial_matrixEntry)

theorem polynomial_originalViews : PolynomialTime originalViewsRealizer :=
  polynomial_pair polynomial_originalFirstView
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      polynomial_originalFirstView) polynomial_complementValues)

theorem polynomial_initialViewInput : PolynomialTime initialViewInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_marginCatalog polynomial_marginThreshold)
    GreedyFeasibleTable.polynomial_table

theorem polynomial_initialViews : PolynomialTime initialViewsRealizer :=
  polynomial_composition polynomial_initialViewInput polynomial_originalViews

theorem polynomial_initialCheck : PolynomialTime initialCheckRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_initialViews) polynomial_prepareProfileInput

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts SmallContextCoordinates FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma originalViews_code (e : Fin q ≃ Cells (paperSmall r c)) (X : Table r c) :
    originalViews ((cellCatalog (paperSmall r c) e,d^20),matrixCode X.val)=
      stateCode r c e (tableState r c X) := by
  rw [tableState_code]
  have he : originalFirstView ((cellCatalog (paperSmall r c) e,d^20),matrixCode X.val)=
      List.ofFn (fun i => X.val (e i).val.1 (e i).val.2) := by
    simp only [originalFirstView,cellCatalog,List.map_ofFn]
    congr 1
    funext i
    exact matrixEntry_code X.val (e i).val.1 (e i).val.2
  unfold originalViews
  rw [he,complementValues_ofFn]

lemma initialViews_code (htotal : (∑ i,r i)=∑ j,c j) :
    initialViews (List.ofFn r,List.ofFn c)=stateCode r c (computedCellEquiv r c)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialViews initialViewInput
  rw [GreedyFeasibleTable.listMatrix_ofFn]
  have hc : marginCatalog (List.ofFn r,List.ofFn c)=cellCatalog (paperSmall r c) (computedCellEquiv r c) := by
    rw [computedCellEquiv_catalog]
    unfold marginCatalog
    rw [marginThreshold_ofFn]
    rfl
  rw [hc,marginThreshold_ofFn]
  exact originalViews_code r c (computedCellEquiv r c) (GreedyFeasibleTable.table r c htotal)

lemma initialCheck_code (htotal : (∑ i,r i)=∑ j,c j) :
    initialCheck (List.ofFn r,List.ofFn c)=stateCodeData r c (computedCellEquiv r c)
      (tableState r c (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialCheck
  rw [initialViews_code r c htotal,prepareProfileInput_eq]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedResidualProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing padded residual margins from the stored small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_largeFlag : PolynomialTime largeFlagRealizer :=
  polynomial_congr _ (polynomial_choose polynomial_leNat (polynomial_constant 1) (polynomial_constant 0))

theorem polynomial_largeCount : PolynomialTime largeCountRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_largeFlag) polynomial_listSum

theorem polynomial_paddedMarginAt (row : Bool) : PolynomialTime (paddedMarginAtRealizer row) := by
  have ha : PolynomialTime (pair (composition
      (first (A := PaddingData) (B := ℕ)) first) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have ht : PolynomialTime (composition (composition
      (first (A := PaddingData) (B := ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold paddedMarginAtRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition ha (polynomial_marginValue row))
      (polynomial_composition ha (polynomial_lineValue row))) polynomial_subtract)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_pair ht
          (polynomial_composition ha (polynomial_marginValue row))) polynomial_largeFlag)
        (polynomial_composition (polynomial_pair ht
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
            (polynomial_marginList (!row)))) polynomial_largeCount)) polynomial_multiply)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)) polynomial_add

theorem polynomial_paddedMargins (row : Bool) : PolynomialTime (paddedMarginsRealizer row) :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first (polynomial_marginIndices row)))
    (polynomial_mapWith (polynomial_paddedMarginAt row))

open scoped BigOperators

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_LargeMarginProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the large rectangle and its padded margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_largeIndexTest : PolynomialTime largeIndexTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_leNat

theorem polynomial_largeIndices : PolynomialTime largeIndicesRealizer := by
  have hr : PolynomialTime (composition (composition
      (second (A := ℕ) (B := List ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength)
      Polynomial.X
    intro z
    simpa only [Function.comp_apply,Polynomial.eval_X] using
      (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_filterWith polynomial_largeIndexTest)

theorem polynomial_selectList {A : Type} [Codec A] (a : A) :
    PolynomialTime (selectListRealizer a) :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith (polynomial_getDFast a))

theorem polynomial_largePaddedMargins (row : Bool) :
    PolynomialTime (largePaddedMarginsRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_first (polynomial_marginList row)))
      polynomial_largeIndices) (polynomial_paddedMargins row)) (polynomial_selectList 0)

theorem polynomial_profilePaddedMargins (row : Bool) :
    PolynomialTime (profilePaddedMarginsRealizer row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_profileLineData row)) polynomial_second)
    (polynomial_largePaddedMargins row)

lemma largePaddedMargins_eq (row : Bool) (z : PaddingData) :
    largePaddedMargins row z=
      (largeIndices (z.1.2,marginList row z.1)).map (fun i => paddedMarginAt row (z,i)) := by
  change (largeIndices (z.1.2,marginList row z.1)).map
    (fun i => (paddedMargins row z).getD i 0)=_
  apply List.map_congr_left
  intro i hi
  have hi' := (mem_largeIndices _ _ _).mp hi
  rw [List.getD_eq_getElem (l := paddedMargins row z) (n := i) (d := 0)
    (by simpa only [paddedMargins,List.length_map,List.length_range] using hi'.1)]
  simp only [paddedMargins,List.getElem_map,List.getElem_range]

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualDenseProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed dense completion call from a retained small profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_residualParameters : PolynomialTime residualParametersRealizer := by
  unfold residualParametersRealizer
  exact polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_profilePaddedMargins true))
    (polynomial_composition polynomial_first (polynomial_profilePaddedMargins false)))
    polynomial_second

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete outer sampling schedule from binary margins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_squarePower : PolynomialTime squarePower :=
  polynomial_congr _ polynomial_squareNat

theorem polynomial_cubicPower : PolynomialTime cubicPower :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_squareNat polynomial_identity) polynomial_multiply)

theorem polynomial_twelfthPower : PolynomialTime twelfthPower :=
  polynomial_congr _ (polynomial_composition polynomial_fourthPower polynomial_cubicPower)

theorem polynomial_twoHundredthPower : PolynomialTime twoHundredthPower :=
  polynomial_congr _ (polynomial_composition polynomial_fiftiethPower polynomial_fourthPower)

theorem polynomial_sixtySecondPower : PolynomialTime sixtySecondPower :=
  polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_twentiethPower polynomial_cubicPower)
    polynomial_squareNat) polynomial_multiply)

theorem polynomial_marginPadding : PolynomialTime marginPaddingRealizer :=
  polynomial_composition (f := fun z : List ℕ×List ℕ => marginDimension z) (g := fun n : ℕ => n^12) (polynomial_marginDimension) polynomial_twelfthPower

theorem polynomial_marginStateBound : PolynomialTime marginStateBoundRealizer :=
  polynomial_composition (f := fun z : List ℕ×List ℕ => (((z.1.sum+(marginDimension z*marginPadding z))+marginThreshold z),2)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : List ℕ×List ℕ => ((z.1.sum+(marginDimension z*marginPadding z)),marginThreshold z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : List ℕ×List ℕ => (z.1.sum,(marginDimension z*marginPadding z))) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : List ℕ×List ℕ => z.1) (g := List.sum) polynomial_first polynomial_listSum) (polynomial_composition (f := fun z : List ℕ×List ℕ => (marginDimension z,marginPadding z)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_marginDimension) (polynomial_marginPadding)) polynomial_multiply)) polynomial_add) (polynomial_marginThreshold)) polynomial_add) (polynomial_constant 2)) polynomial_add

theorem polynomial_marginBinaryLength : PolynomialTime marginBinaryLengthRealizer :=
  polynomial_composition (f := fun z : List ℕ×List ℕ => (marginDimension z,(Nat.clog 2) ((marginStateBound z+2)))) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_marginDimension) (polynomial_composition (f := fun z : List ℕ×List ℕ => (marginStateBound z+2)) (g := Nat.clog 2) (polynomial_composition (f := fun z : List ℕ×List ℕ => (marginStateBound z,2)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_marginStateBound) (polynomial_constant 2)) polynomial_add) polynomial_ceilLogTwo)) polynomial_add

theorem polynomial_parameterDimension : PolynomialTime parameterDimensionRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => z.1) (g := marginDimension) polynomial_first polynomial_marginDimension

theorem polynomial_parameterBinaryLength : PolynomialTime parameterBinaryLengthRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => z.1) (g := marginBinaryLength) polynomial_first polynomial_marginBinaryLength

theorem polynomial_parameterTrials : PolynomialTime parameterTrialsRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,(z.2+1))) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (polynomial_parameterDimension) polynomial_fourthPower) (polynomial_composition (f := fun z : SamplingParameters => (z.2,1)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_second) (polynomial_constant 1)) polynomial_add)) polynomial_multiply

theorem polynomial_parameterSteps : PolynomialTime parameterStepsRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z)^200,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^200) (polynomial_parameterDimension) polynomial_twoHundredthPower) (polynomial_composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (polynomial_composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_second) (polynomial_parameterBinaryLength)) polynomial_add) polynomial_squarePower)) polynomial_multiply

theorem polynomial_parameterAccuracy : PolynomialTime parameterAccuracyRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z)^4,((z.2+parameterBinaryLength z))^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^4) (polynomial_parameterDimension) polynomial_fourthPower) (polynomial_composition (f := fun z : SamplingParameters => (z.2+parameterBinaryLength z)) (g := fun n : ℕ => n^2) (polynomial_composition (f := fun z : SamplingParameters => (z.2,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_second) (polynomial_parameterBinaryLength)) polynomial_add) polynomial_squarePower)) polynomial_multiply

theorem polynomial_parameterProposalWidth : PolynomialTime parameterProposalWidthRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => (32*(parameterDimension z)^2)) (g := Nat.clog 2) (polynomial_composition (f := fun z : SamplingParameters => (32,(parameterDimension z)^2)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_constant 32) (polynomial_composition (f := fun z : SamplingParameters => parameterDimension z) (g := fun n : ℕ => n^2) (polynomial_parameterDimension) polynomial_squarePower)) polynomial_multiply) polynomial_ceilLogTwo

theorem polynomial_parameterCompletionWidth : PolynomialTime parameterCompletionWidthRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => (25,((((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1))^62)) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_constant 25) (polynomial_composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z)+1)) (g := fun n : ℕ => n^62) (polynomial_composition (f := fun z : SamplingParameters => (((parameterDimension z+parameterBinaryLength z)+parameterAccuracy z),1)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => ((parameterDimension z+parameterBinaryLength z),parameterAccuracy z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => (parameterDimension z,parameterBinaryLength z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_parameterDimension) (polynomial_parameterBinaryLength)) polynomial_add) (polynomial_parameterAccuracy)) polynomial_add) (polynomial_constant 1)) polynomial_add) polynomial_sixtySecondPower)) polynomial_multiply

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfilePublicProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampler's public binary parser and matrix printer -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralParse MatchingFPRAS.LiteralCodec
open DensePrograms

theorem polynomial_samplingPrecision : PolynomialTime samplingPrecisionRealizer := by
  unfold samplingPrecisionRealizer
  exact polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2) (polynomial_head 0))
        polynomial_add)
      (polynomial_composition polynomial_tail (polynomial_head 0))) polynomial_add))
    polynomial_dropFast) (polynomial_head 0)

theorem polynomial_samplingInput : PolynomialTime samplingInputRealizer :=
  polynomial_pair GreedyFeasibleTable.polynomial_marginLists polynomial_samplingPrecision

theorem polynomial_parsedSampling : PolynomialTime parsedSamplingRealizer :=
  polynomial_composition polynomial_parse polynomial_samplingInput

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_AllSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single computed sampler for large and all-small rectangles -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

attribute [local irreducible] parameterUnitWords

theorem polynomial_parameterLargeIndices (row : Bool) : PolynomialTime (parameterLargeIndicesRealizer row) := by
  cases row with
  | false => exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginThreshold)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_largeIndices
  | true => exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginThreshold)
      (polynomial_composition polynomial_first polynomial_first)) polynomial_largeIndices

theorem polynomial_hasLargeRectangle : PolynomialTime hasLargeRectangleRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition (polynomial_parameterLargeIndices true) polynomial_listLength)) polynomial_less)
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition (polynomial_parameterLargeIndices false) polynomial_listLength)) polynomial_less))
    polynomial_boolAnd

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CanonicalDrawTabulation
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact dense counts after computed maximal-margin normalization -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped GridBoundary
open scoped BigOperators Classical

lemma polynomial_canonicalCountInput : PolynomialTime canonicalCountInputRealizer := by
  unfold canonicalCountInputRealizer
  exact polynomial_pair
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginIndices) polynomial_first)
      polynomial_swapMargins) polynomial_second)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_marginIndices)
      (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table))
      polynomial_swapMatrix)

attribute [local irreducible] canonicalCountInputRealizer suppliedDrawCountsRealizer

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A computed finite-box index for the two small-profile views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_profileBoxIndex : PolynomialTime profileBoxIndexRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_profileViews polynomial_flattenViews)
    (polynomial_composition polynomial_second polynomial_successor)) polynomial_gridIndex

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileMatrixEntry
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable entries of the finite profile transition matrix -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_matrixData : PolynomialTime matrixDataRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first

lemma polynomial_sourceData : PolynomialTime sourceDataRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_matrixData)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_candidateData

lemma polynomial_entryCacheParameters : PolynomialTime entryCacheParametersRealizer := by
  unfold entryCacheParametersRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair polynomial_sourceData
    (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first) polynomial_first) polynomial_second))
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTrialVector
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma polynomial_optionalTrialInput : PolynomialTime optionalTrialInputRealizer :=
  polynomial_pair polynomial_first (polynomial_composition
    (polynomial_pair (polynomial_constant []) polynomial_second) FirstSuccessProgram.polynomial_default)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileScheduleSemantics
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed schedule and initializer equal the proved sampler data -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
attribute [local irreducible] profileRetry listedOuterDraw tableState
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)

lemma parameterTrials_ofFn (k : ℕ) :
    parameterTrials ((List.ofFn r,List.ofFn c),k)=outerTrials d k := by
  rw [parameterTrials,parameterDimension_ofFn]
  rfl

lemma parameterWordCount_ofFn (k : ℕ) :
    parameterWordCount ((List.ofFn r,List.ofFn c),k)=finiteSamplerBits r c k := by
  rw [parameterWordCount,parameterTrials_ofFn,parameterSteps_ofFn,parameterProposalWidth_ofFn,
    parameterCompletionWidth_ofFn]

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledCountInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Supplying the finite count evaluator from the public sampling parameters -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] initialCheck marginPadding parameterDimension parameterAccuracy
  parameterCompletionWidth parameterSteps parameterProposalWidth hasLargeRectangle parameterTrials
  profileBoxIndex outerVector UnitCountPrograms.outerVector

lemma polynomial_scheduledCacheParameters : PolynomialTime scheduledCacheParametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_initialCheck)
    (polynomial_composition polynomial_first polynomial_marginPadding))
    (polynomial_pair polynomial_parameterDimension polynomial_parameterAccuracy))
    polynomial_parameterCompletionWidth

lemma polynomial_scheduledDenseWidth : PolynomialTime scheduledDenseWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_parameterSteps (polynomial_composition
      (polynomial_pair polynomial_parameterProposalWidth polynomial_parameterCompletionWidth)
      polynomial_add)) polynomial_multiply) polynomial_parameterCompletionWidth) polynomial_add

lemma polynomial_scheduledUnitWidth : PolynomialTime scheduledUnitWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_parameterSteps polynomial_parameterProposalWidth)
    polynomial_multiply

attribute [local irreducible] scheduledDenseWidth scheduledUnitWidth

lemma polynomial_scheduledTrialWidth : PolynomialTime scheduledTrialWidthRealizer :=
  polynomial_choose polynomial_hasLargeRectangle polynomial_scheduledDenseWidth polynomial_scheduledUnitWidth

attribute [local irreducible] scheduledTrialWidth

lemma weight_le_scheduledCountInputMeasure (z : SamplingParameters) :
    weight z ≤ X.eval (scheduledCountInputMeasure z) := by
  simp only [eval_X,scheduledCountInputMeasure]
  omega

attribute [local irreducible] scheduledMatrixParameters

lemma work_scheduledMatrixParameters :
    WorkBound scheduledMatrixParametersRealizer scheduledCountInputMeasure := by
  unfold scheduledMatrixParametersRealizer scheduledMatrixParameters
  have hm : WorkBound (composition parameterProposalWidthRealizer unaryMarkersRealizer)
      scheduledCountInputMeasure := by
    apply work_composition (work_of_polynomial polynomial_parameterProposalWidth X
      weight_le_scheduledCountInputMeasure) work_unaryMarkers X
    intro z
    simp only [id_eq,eval_X,scheduledCountInputMeasure]
    omega
  exact work_pair (work_of_polynomial polynomial_scheduledCacheParameters X
    weight_le_scheduledCountInputMeasure) hm X weight_le_scheduledCountInputMeasure

lemma polynomial_scheduledStartIndex : PolynomialTime scheduledStartIndexRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_initialCheck)
    polynomial_profileBoxIndex

attribute [local irreducible] scheduledWalkInput

lemma work_scheduledWalkInput : WorkBound scheduledWalkInputRealizer scheduledCountInputMeasure := by
  unfold scheduledWalkInputRealizer scheduledWalkInput
  exact work_pair work_scheduledMatrixParameters
    (work_of_polynomial (polynomial_pair polynomial_parameterSteps polynomial_scheduledStartIndex)
      X weight_le_scheduledCountInputMeasure) X weight_le_scheduledCountInputMeasure

attribute [local irreducible] scheduledTrialInput

lemma work_scheduledTrialInput : WorkBound scheduledTrialInputRealizer scheduledCountInputMeasure := by
  unfold scheduledTrialInputRealizer scheduledTrialInput
  exact work_pair work_scheduledWalkInput (work_of_polynomial polynomial_first X
    weight_le_scheduledCountInputMeasure) X weight_le_scheduledCountInputMeasure

attribute [local irreducible] scheduledTrialDenominator

lemma work_scheduledTrialDenominator :
    WorkBound scheduledTrialDenominatorRealizer scheduledCountInputMeasure := by
  unfold scheduledTrialDenominatorRealizer scheduledTrialDenominator
  apply work_composition (work_of_polynomial
    (polynomial_pair (polynomial_constant 2) polynomial_scheduledTrialWidth)
      X weight_le_scheduledCountInputMeasure) BinaryPowerPrograms.work_power (X+C (weight (2:ℕ)))
  intro z
  simp only [eval_add,eval_X,eval_C,scheduledCountInputMeasure]
  omega

attribute [local irreducible] scheduledOuterInput

lemma work_scheduledOuterInput : WorkBound scheduledOuterInputRealizer scheduledCountInputMeasure := by
  unfold scheduledOuterInputRealizer scheduledOuterInput
  have hm : WorkBound (composition parameterTrialsRealizer unaryMarkersRealizer)
      scheduledCountInputMeasure := by
    apply work_composition (work_of_polynomial polynomial_parameterTrials X
      weight_le_scheduledCountInputMeasure) work_unaryMarkers X
    intro z
    simp only [id_eq,eval_X,scheduledCountInputMeasure]
    omega
  exact work_pair work_scheduledTrialInput
    (work_pair (work_pair hm work_scheduledTrialDenominator X weight_le_scheduledCountInputMeasure)
      (work_of_polynomial (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table)
        X weight_le_scheduledCountInputMeasure) X weight_le_scheduledCountInputMeasure)
    X weight_le_scheduledCountInputMeasure

attribute [local irreducible] scheduledCounts

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PublicInputLength
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary input lengths for the sampling machine -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS
open scoped BigOperators

lemma encodeNat_length (n : ℕ) : (encodeNat n).length=n.size+1 := by
  simp only [encodeNat,List.length_append,List.length_map,List.length_singleton,Nat.size_eq_bits_len]

lemma encodeNat_length_le (n N : ℕ) (hn : n ≤ N) :
    (encodeNat n).length ≤ Nat.clog 2 (N+1)+1 := by
  rw [encodeNat_length]
  have hs : n.size ≤ Nat.clog 2 (N+1) := Nat.size_le.mpr
    ((Nat.lt_succ_of_le hn).trans_le (Nat.le_pow_clog (by decide) (N+1)))
  omega

private lemma natWords_length (ns : List ℕ) (N : ℕ) (h : ∀ n∈ns,n ≤ N) :
    (ns.flatMap encodeNat).length ≤ ns.length*(Nat.clog 2 (N+1)+1) := by
  induction ns with
  | nil => simp
  | cons n ns ih =>
    have hn := encodeNat_length_le n N (h n (by simp))
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma encodeMargins_length {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) :
    (encodeMargins r c).length ≤ m+n+2+(m+n)*(Nat.clog 2 ((∑ i,r i)+1)+1) := by
  have hm : (encodeNat m).length ≤ m+1 := by
    rw [encodeNat_length]
    exact Nat.add_le_add_right (Nat.size_le.mpr (Nat.lt_two_pow_self)) 1
  have hn : (encodeNat n).length ≤ n+1 := by
    rw [encodeNat_length]
    exact Nat.add_le_add_right (Nat.size_le.mpr (Nat.lt_two_pow_self)) 1
  have hr := natWords_length (List.ofFn r) (∑ i,r i) (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hc := natWords_length (List.ofFn c) (∑ i,r i) (by
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    rw [htotal]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
  simp only [List.length_ofFn] at hr hc
  simp only [List.flatMap_def,←List.ofFn_comp'] at hr hc
  unfold encodeMargins
  simp only [List.length_append]
  nlinarith

/-- The bit input length is polynomial in the parameters used by the
paper's public sampling statement. -/
theorem encodeSamplingInput_length {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (k : ℕ) :
    (encodeSamplingInput r c k).length ≤ 5*(samplingSize n r k)^2 := by
  have hM := encodeMargins_length r c htotal
  have hk : (encodeNat k).length ≤ k+1 := by
    rw [encodeNat_length]
    exact Nat.add_le_add_right (Nat.size_le.mpr (Nat.lt_two_pow_self)) 1
  rw [encodeSamplingInput,List.length_append]
  let S := samplingSize n r k
  have hS : 1 ≤ S := by dsimp [S,samplingSize]; omega
  have hmn : m+n ≤ S := by dsimp [S,samplingSize]; omega
  have hl : Nat.clog 2 ((∑ i,r i)+1)+1 ≤ S := by dsimp [S,samplingSize]; omega
  have hkS : k+1 ≤ S := by dsimp [S,samplingSize]; omega
  have hp := Nat.mul_le_mul hmn hl
  change _ ≤ 5*S^2
  nlinarith

end ContingencyTables.Algorithms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperWordBudget
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial bound for the full first-paper Boolean word -/

namespace ContingencyTables

private lemma double_power_le {S : ℕ} (hS : 2 ≤ S) (n : ℕ) :
    2*S^n ≤ S^(n+1) := by
  rw [pow_succ']
  exact Nat.mul_le_mul_right _ hS

private lemma one_mul_power (S a b : ℕ) : S*(S^a)^b=S^(a*b+1) := by
  rw [←pow_mul,pow_succ']

private lemma natPower_mul (S a b c : ℕ) (hc : a+b=c) : S^a*S^b=S^c := by
  rw [←pow_add,hc]

private lemma natPower_mono (S i j : ℕ) (hS : 1 ≤ S) (hij : i ≤ j) : S^i ≤ S^j :=
  Nat.pow_le_pow_right hS hij

private theorem wordBudget_bound (d b k S : ℕ) (hinput : d+b+k+100 ≤ S) :
    smallSamplerWordBudget d b k ≤ S^644 := by
  have hS : 2 ≤ S := by omega
  have hS1 : 1 ≤ S := by omega
  have hd : d ≤ S := by omega
  have hb : k+b ≤ S := by omega
  have hk : k+1 ≤ S := by omega
  have hn : outerSteps d b k ≤ S^202 := by
    unfold outerSteps
    calc
      _ ≤ S^200*S^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
      _ = _ := (pow_add S 200 2).symm
  have hh : outerAccuracy d b k ≤ S^6 := by
    unfold outerAccuracy
    calc
      _ ≤ S^4*S^2 := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
      _ = _ := (pow_add S 4 2).symm
  have hlin : d+b+outerAccuracy d b k+1 ≤ S^7 := by
    have hp := Nat.le_self_pow (by decide : 6≠0) S
    exact (show d+b+outerAccuracy d b k+1 ≤ 2*S^6 by omega).trans (double_power_le hS 6)
  have hf : 25*(d+b+outerAccuracy d b k+1)^62 ≤ S^435 := by
    have hm := Nat.mul_le_mul (show 25 ≤ S by omega) (Nat.pow_le_pow_left hlin 62)
    have he := one_mul_power S 7 62
    have hp : S^(7*62+1)=S^435 := congrArg (fun n => S^n) (by decide)
    exact hm.trans_eq (he.trans hp)
  have hs : Nat.clog 2 (32*d^2) ≤ S^3 := by
    calc
      _ ≤ 32*d^2 := Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
      _ ≤ S*S^2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hd _)
      _ = _ := (pow_succ' S 2).symm
  have hsum : Nat.clog 2 (32*d^2)+25*(d+b+outerAccuracy d b k+1)^62 ≤ S^436 := by
    have hp : S^3 ≤ S^435 := natPower_mono S 3 435 hS1 (by decide)
    calc
      _ ≤ S^435+S^435 := Nat.add_le_add (hs.trans hp) hf
      _ = 2*S^435 := (two_mul _).symm
      _ ≤ S^(435+1) := double_power_le hS 435
      _ = S^436 := congrArg (fun n => S^n) (by decide)
  have hinner : outerSteps d b k*(Nat.clog 2 (32*d^2)+25*(d+b+outerAccuracy d b k+1)^62)+
      25*(d+b+outerAccuracy d b k+1)^62 ≤ S^639 := by
    have hp : S^435 ≤ S^638 := natPower_mono S 435 638 hS1 (by decide)
    calc
      _ ≤ S^638+S^638 := Nat.add_le_add
        ((Nat.mul_le_mul hn hsum).trans_eq (natPower_mul S 202 436 638 (by decide))) (hf.trans hp)
      _ = 2*S^638 := (two_mul _).symm
      _ ≤ S^(638+1) := double_power_le hS 638
      _ = S^639 := congrArg (fun n => S^n) (by decide)
  have hJ : outerTrials d k ≤ S^5 := by
    unfold outerTrials
    calc
      _ ≤ S^4*S := Nat.mul_le_mul (Nat.pow_le_pow_left hd _) hk
      _ = _ := (pow_succ S 4).symm
  unfold smallSamplerWordBudget
  exact (Nat.mul_le_mul hJ hinner).trans_eq (natPower_mul S 5 639 644 (by decide))


theorem smallSamplerWordBudget_polynomial (d b k : ℕ) :
    smallSamplerWordBudget d b k ≤ (d+b+k+100)^644 :=
  wordBudget_bound d b k (d+b+k+100) le_rfl

end ContingencyTables

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperInputWordBudget
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel _root_.OAI.MatchingFPRAS.RegisterControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The sampler's bit budget in the original binary input parameters -/

namespace ContingencyTables.SmallGraphProfiles
open scoped BigOperators
open CompletionCounts Algorithms

private lemma scaled_square_pow (a x n : ℕ) : (a*x^2)^n=a^n*x^(2*n) := by
  rw [mul_pow,←pow_mul]

private lemma scaled_square_pow644 (a x : ℕ) : (a*x^2)^644=a^644*x^1288 := by
  have h := scaled_square_pow a x 644
  have he : a^644*x^(2*644)=a^644*x^1288 :=
    congrArg (fun t => a^644*x^t) (by decide)
  exact h.trans he

private lemma power_mono_left (a b e : ℕ) (h : a ≤ b) : a^e ≤ b^e :=
  Nat.pow_le_pow_left h e

private lemma word_budget_scaled (d b k a S : ℕ) (hsize : d+b+k+100 ≤ a*S^2) :
    smallSamplerWordBudget d b k ≤ a^644*S^1288 := by
  calc
    _ ≤ (d+b+k+100)^644 := smallSamplerWordBudget_polynomial d b k
    _ ≤ (a*S^2)^644 := power_mono_left (d+b+k+100) (a*S^2) 644 hsize
    _ = a^644*S^1288 := scaled_square_pow644 a S

lemma sampling_dimension_bound (m n l k : ℕ) :
    dimensionAllowance (I := Fin m) (J := Fin n) ≤ 11*(m+n+l+k+1)^2 := by
  let S := m+n+l+k+1
  have hm : m+1 ≤ S := by omega
  have hn : n+1 ≤ S := by omega
  have hp : (m+1)*(n+1) ≤ S^2 := by simpa only [pow_two] using Nat.mul_le_mul hm hn
  have hS : 1 ≤ S^2 := one_le_pow₀ (by omega : 1 ≤ S)
  simp only [dimensionAllowance,Fintype.card_fin]
  change 10+(m+1)*(n+1) ≤ 11*S^2
  omega

lemma sampling_internal_size_bound {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) :
    dimensionAllowance (I := Fin m) (J := Fin n)+smallBinaryLength r c+k+1 ≤
      245*(samplingSize n r k)^2 := by
  let l := Nat.clog 2 ((∑ i,r i)+1)
  let S := samplingSize n r k
  have hb := smallBinaryLength_le r c
  have hd := sampling_dimension_bound m n l k
  change dimensionAllowance (I := Fin m) (J := Fin n) ≤ 11*S^2 at hd
  have hS : S ≤ S^2 := Nat.le_self_pow (by decide) S
  have hk : l+k+3 ≤ 3*S := by dsimp [S,samplingSize,l]; omega
  change dimensionAllowance (I := Fin m) (J := Fin n)+smallBinaryLength r c+k+1 ≤ 245*S^2
  omega

/-- All fixed random-bit segments together have a uniform polynomial
bound in dimensions, binary total margin, and requested accuracy. -/
theorem sampling_word_budget_polynomial {m n : ℕ}
    (r : Fin m → ℕ) (c : Fin n → ℕ) (k : ℕ) :
    smallSamplerWordBudget (dimensionAllowance (I := Fin m) (J := Fin n))
      (smallBinaryLength r c) k ≤
      344^644*(samplingSize n r k)^1288 := by
  have hs : 1 ≤ (samplingSize n r k)^2 := one_le_pow₀ (by unfold samplingSize; omega)
  have hi := sampling_internal_size_bound r c k
  have hb : dimensionAllowance (I := Fin m) (J := Fin n)+smallBinaryLength r c+k+100 ≤
      344*(samplingSize n r k)^2 := by omega
  exact word_budget_scaled (dimensionAllowance (I := Fin m) (J := Fin n))
    (smallBinaryLength r c) k 344 (samplingSize n r k) hb

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactSamplingParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the exact sampler's precision from its margin-only input -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] marginDimension marginBinaryLength parameterWordCount

lemma polynomial_sixthPower : PolynomialTime sixthPower :=
  polynomial_congr _ (polynomial_composition polynomial_cubicPower polynomial_squarePower)

lemma polynomial_exactPrecision : PolynomialTime exactPrecisionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_marginDimension polynomial_sixthPower)
    (polynomial_composition polynomial_marginBinaryLength polynomial_squarePower)) polynomial_multiply

attribute [local irreducible] exactPrecision

lemma polynomial_exactSamplingParameters : PolynomialTime exactSamplingParametersRealizer :=
  polynomial_pair polynomial_identity (polynomial_composition
    (polynomial_pair (polynomial_constant 2) polynomial_exactPrecision) polynomial_multiply)

lemma work_exactBranchDenominator : WorkBound exactBranchDenominatorRealizer exactParameterMeasure := by
  unfold exactBranchDenominatorRealizer
  apply work_composition (work_of_polynomial (polynomial_pair (polynomial_constant 2)
    polynomial_exactPrecision) X (by intro z; simp only [eval_X,exactParameterMeasure]; omega))
    BinaryPowerPrograms.work_power (X+C (weight (2:ℕ)))
  intro z
  simp only [eval_add,eval_X,eval_C,exactParameterMeasure]
  omega

lemma work_exactResidualInput : WorkBound exactResidualInputRealizer exactParameterMeasure :=
  work_pair (work_of_polynomial polynomial_exactSamplingParameters X
    (by intro z; simp only [eval_X,exactParameterMeasure]; omega))
    work_exactBranchDenominator X (by intro z; simp only [eval_X,exactParameterMeasure]; omega)

lemma polynomial_exactParsedMargins : PolynomialTime exactParsedMarginsRealizer :=
  polynomial_composition polynomial_parsedSampling polynomial_first

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms MatchingFPRAS.LiteralParse
open scoped BigOperators

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

lemma exactPrecision_ofFn : exactPrecision (List.ofFn r,List.ofFn c)=correctionPrecision r c := by
  rw [exactPrecision,marginDimension_ofFn,marginBinaryLength_ofFn]
  rfl

lemma exactSamplingParameters_ofFn :
    exactSamplingParameters (List.ofFn r,List.ofFn c)=
      ((List.ofFn r,List.ofFn c),2*correctionPrecision r c) := by
  rw [exactSamplingParameters,exactPrecision_ofFn]

lemma exactOrdinaryBits_ofFn :
    exactOrdinaryBits (List.ofFn r,List.ofFn c)=finiteSamplerBits r c (2*correctionPrecision r c) := by
  rw [exactOrdinaryBits,exactSamplingParameters_ofFn,parameterWordCount_ofFn]

lemma exactParsedMargins_spec :
    exactParsedMargins (Algorithms.encodeMargins r c)=(List.ofFn r,List.ofFn c) := by
  unfold exactParsedMargins parsedSampling samplingInput
  rw [GreedyFeasibleTable.encodeMargins_natWords,GreedyFeasibleTable.parse_natWords]
  have h := GreedyFeasibleTable.marginLists_spec m n (List.ofFn r) (List.ofFn c) []
    List.length_ofFn List.length_ofFn
  simpa only [List.append_nil] using h

end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactPrintCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform printing cost for every feasible exact-sampling output -/

namespace ContingencyTables.ExactPrintCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms SmallGraphProfiles Polynomial
open scoped BigOperators Classical
noncomputable section

lemma weight_ofFn {A : Type} [Codec A] {n B : ℕ} (f : Fin n → A)
    (h : ∀ i,weight (f i) ≤ B) : weight (List.ofFn f) ≤ n*(B+1)+1 := by
  have hb := weight_map_bound (f := f) (as := List.finRange n) (fun i _ => h i)
  simpa only [←List.ofFn_eq_map,List.length_finRange] using hb

end
end ContingencyTables.ExactPrintCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_EnumerationPointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Individual enumeration points have polynomial binary size -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma gridCoordinates_weight (z : GridEnumerationData) (hz : 0 < z.2) (i : ℕ) :
    weight (gridCoordinates (z,i)) ≤ z.1.length*(4*weight z.2+2)+1 := by
  rw [gridCoordinates_eq]
  apply ExactPrintCost.weight_ofFn
  intro j
  exact weight_nat_small (Nat.le_of_lt (Nat.mod_lt _ hz))

lemma gridWords_point_weight (z : GridEnumerationData) (hz : 0 < z.2)
    (w : List ℕ) (hw : w∈gridWords z) :
    weight w ≤ z.1.length*(4*weight z.2+2)+1 := by
  rw [gridWords] at hw
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hw
  exact gridCoordinates_weight z hz i

lemma splitViews_weight (n : ℕ) (w : List ℕ) : weight (splitViews (n,w))=weight w+2 := by
  have h := weight_append (w.take n) (w.drop n)
  rw [List.take_append_drop] at h
  simp only [splitViews,weight_prod]
  omega

lemma profileBoxViews_length (z : ProfileCheckData) :
    (profileBoxViews z).length=gridStateCount (profileEnumerationData z) := by
  simp only [profileBoxViews,List.length_map,gridWords,List.length_range]

lemma profileBoxViews_point_weight (z : ProfileCheckData) (v : List ℕ×List ℕ)
    (hv : v∈profileBoxViews z) :
    weight v ≤ (2*z.1.1.1.length)*(4*weight (z.2+1)+2)+3 := by
  rw [profileBoxViews] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  have hb := gridWords_point_weight (profileEnumerationData z) (by
    change 0 < z.2+1
    omega) w hw
  simp only [profileEnumerationData,List.length_map,List.length_append] at hb
  rw [←two_mul] at hb
  rw [splitViews_weight]
  omega

/-- Exponentially many enumerated points do not make any one point's
binary representation exponentially large. -/
theorem profileBoxViews_point_polynomial : ∃ p : Polynomial ℕ,
    ∀ z v,v∈profileBoxViews z → weight v ≤ p.eval (weight z) := by
  obtain ⟨p,hp⟩ := polynomial_successor
  refine ⟨2*X*(4*p+2)+3,?_⟩
  intro z v hv
  have hw : weight z.2 ≤ weight z := weight_snd z
  have hu : weight (z.2+1) ≤ p.eval (weight z) :=
    (Nat.le_add_left _ _).trans ((hp z.2).trans (polynomial_eval_monotone p hw))
  have hc : z.1.1.1.length ≤ weight z :=
    (list_length_le_weight _).trans ((weight_fst _).trans ((weight_fst _).trans (weight_fst z)))
  have h := profileBoxViews_point_weight z v hv
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul
    (Nat.mul_le_mul_left 2 hc) (by omega)) 3)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PaddedEnumerationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumeration bounds uniform over all proposed small profiles -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma list_getD_le_sum (as : List ℕ) (i : ℕ) : as.getD i 0 ≤ as.sum := by
  induction as generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero => simp
    | succ i =>
      simpa only [List.getD_cons_succ,List.sum_cons] using
        (ih i).trans (Nat.le_add_left as.sum a)

lemma list_sum_le_length_mul (as : List ℕ) (B : ℕ) (h : ∀ a∈as,a ≤ B) :
    as.sum ≤ as.length*B := by
  induction as with
  | nil => simp
  | cons a as ih =>
    have ha := h a (by simp)
    have hs := ih (by intro b hb; exact h b (by simp [hb]))
    simp only [List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

lemma largeCount_le_length (U : ℕ) (as : List ℕ) : largeCount (U,as) ≤ as.length := by
  unfold largeCount
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    change (as.map (fun a => if U ≤ a then 1 else 0)).sum ≤ as.length at ih
    change (if U ≤ a then 1 else 0)+(as.map (fun a => if U ≤ a then 1 else 0)).sum ≤ as.length+1
    split_ifs <;> omega

/-- Rejected profiles can decrease residual margins but cannot enlarge
them beyond the original margin and its deterministic padding. -/
lemma paddedMarginAt_le (row : Bool) (z : PaddingData) (i : ℕ) :
    paddedMarginAt row (z,i) ≤
      (marginList row z.1).sum+(marginList (!row) z.1).length*z.2 := by
  have ha := list_getD_le_sum (marginList row z.1) i
  have hc := largeCount_le_length z.1.2 (marginList (!row) z.1)
  have hs : (marginList row z.1).getD i 0-lineSum row (lineArgument row (z.1,i)) ≤
      (marginList row z.1).sum := (Nat.sub_le _ _).trans ha
  unfold paddedMarginAt largeFlag
  dsimp only
  split_ifs
  · simpa only [one_mul] using Nat.add_le_add hs (Nat.mul_le_mul_right z.2 hc)
  · simpa only [zero_mul,add_zero] using hs.trans (Nat.le_add_right _ _)

lemma largePaddedMargins_length (row : Bool) (z : PaddingData) :
    (largePaddedMargins row z).length ≤ (marginList row z.1).length := by
  rw [largePaddedMargins_eq,List.length_map]
  exact (List.length_filter_le _ _).trans_eq List.length_range

lemma largePaddedMargins_entry (row : Bool) (z : PaddingData) (a : ℕ)
    (ha : a∈largePaddedMargins row z) :
    a ≤ (marginList row z.1).sum+(marginList (!row) z.1).length*z.2 := by
  rw [largePaddedMargins_eq] at ha
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  exact paddedMarginAt_le row z i

lemma largePaddedMargins_sum (row : Bool) (z : PaddingData) :
    (largePaddedMargins row z).sum ≤ (marginList row z.1).length*
      ((marginList row z.1).sum+(marginList (!row) z.1).length*z.2) := by
  exact (list_sum_le_length_mul _ _ (largePaddedMargins_entry row z)).trans
    (Nat.mul_le_mul_right _ (largePaddedMargins_length row z))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseTabulationScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Numeric dense-tabulation schedules versus binary margin size -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary Polynomial

lemma clog_succ_le_weight (n : ℕ) : Nat.clog 2 (n+1) ≤ weight n := by
  exact (Nat.clog_le_of_le_pow (Nat.succ_le_iff.mpr (Nat.lt_size_self n))).trans
    (size_le_weight n)

theorem offsetLengths_sum_polynomial : ∃ p : Polynomial ℕ,∀ z,
    (offsetLengths z).sum ≤ p.eval (offsetNumericMeasure z) := by
  obtain ⟨p,hp⟩ := polynomial_freeCells
  obtain ⟨q,hq⟩ := polynomial_gridCellWidth
  let input : Polynomial ℕ := 1+X+p
  let entry : Polynomial ℕ := q.comp input+4*X
  refine ⟨p*entry,?_⟩
  intro z
  let M := offsetNumericMeasure z
  have hz : weight z ≤ M := by unfold M offsetNumericMeasure; omega
  have hfree := (hp z).trans (polynomial_eval_monotone p hz)
  have hlen : (freeCells z).length ≤ p.eval M :=
    (list_length_le_weight _).trans ((Nat.le_add_left _ _).trans hfree)
  have he (ij : ℕ×ℕ) (hij : ij∈freeCells z) : offsetLength (z,ij) ≤ entry.eval M := by
    have hw : weight ij ≤ p.eval M := (weight_mem hij).trans ((Nat.le_add_left _ _).trans hfree)
    have hi : weight (z.1,ij) ≤ input.eval M := by
      have hfirst : weight z.1 ≤ M := (weight_fst z).trans hz
      simp only [weight_prod,input,eval_add,eval_one,eval_X]
      omega
    have hg : weight (gridCellWidth (z.1,ij)) ≤ q.eval (input.eval M) :=
      (Nat.le_add_left _ _).trans ((hq _).trans (polynomial_eval_monotone q hi))
    have hn : z.2+z.1.2 ≤ M := by unfold M offsetNumericMeasure; omega
    have hc := (clog_succ_le_weight (gridCellWidth (z.1,ij))).trans hg
    change Nat.clog 2 (gridCellWidth (z.1,ij)+1)+4*(z.2+z.1.2) ≤ _
    simp only [entry,eval_add,eval_comp,eval_mul,eval_ofNat,eval_X]
    omega
  have hs := list_sum_le_length_mul (offsetLengths z) (entry.eval M) (by
    intro a ha
    rw [offsetLengths] at ha
    obtain ⟨ij,hij,rfl⟩ := List.mem_map.mp ha
    exact he ij hij)
  simp only [offsetLengths,List.length_map] at hs
  exact hs.trans (by rw [eval_mul]; exact Nat.mul_le_mul_right _ hlen)

theorem trialWidth_polynomial : ∃ p : Polynomial ℕ,∀ z,
    trialWidth z ≤ p.eval (trialNumericMeasure z) := by
  have ht : PolynomialTime
      (pair (composition (first (B := ℕ)) flatToGridDataRealizer) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_flatToGridData) polynomial_second
  obtain ⟨p,hp⟩ := ht
  obtain ⟨q,hq⟩ := offsetLengths_sum_polynomial
  let walk : Polynomial ℕ := X^50*(X+1)^2*(16*X^5)
  refine ⟨walk+q.comp (X+p),?_⟩
  intro z
  let M := trialNumericMeasure z
  have hz : weight z ≤ M := by unfold M trialNumericMeasure; omega
  have hd : z.1.2 ≤ M := by unfold M trialNumericMeasure; omega
  have hh : z.2 ≤ M := by unfold M trialNumericMeasure; omega
  have hp' := (hp z).trans (polynomial_eval_monotone p hz)
  have hw : weight (flatToGridData z.1,z.2) ≤ p.eval M := (Nat.le_add_left _ _).trans hp'
  have hm : offsetNumericMeasure (flatToGridData z.1,z.2) ≤ (X+p).eval M := by
    change z.1.2+z.2+weight (flatToGridData z.1,z.2) ≤ _
    simp only [eval_add,eval_X]
    unfold M trialNumericMeasure at *
    omega
  have ho := (hq (flatToGridData z.1,z.2)).trans (polynomial_eval_monotone q hm)
  have hb := denseStepBits_upper z.1.2
  have hwalk : trialWalkBits (z,[]) ≤ walk.eval M := by
    simp only [trialWalkBits,walk,eval_mul,eval_pow,eval_add,eval_X,eval_one,eval_ofNat]
    exact Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left (by omega) _))
      (hb.trans (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left hd _)))
  simpa only [trialWidth,eval_add,eval_comp] using Nat.add_le_add hwalk ho

theorem rawTrialBits_polynomial : ∃ p : Polynomial ℕ,∀ z,
    rawTrialBits z ≤ p.eval (canonicalNumericMeasure z) := by
  obtain ⟨p,hp⟩ := polynomial_rawDrawParameters
  obtain ⟨q,hq⟩ := trialWidth_polynomial
  refine ⟨q.comp (X+p),?_⟩
  intro z
  have hz : weight z ≤ canonicalNumericMeasure z := by unfold canonicalNumericMeasure; omega
  have hw : weight (rawDrawParameters z) ≤ p.eval (canonicalNumericMeasure z) :=
    (Nat.le_add_left _ _).trans ((hp z).trans (polynomial_eval_monotone p hz))
  have hm : trialNumericMeasure (rawDrawParameters z) ≤ (X+p).eval (canonicalNumericMeasure z) := by
    change z.2.1+z.2.2+weight (rawDrawParameters z) ≤ _
    simp only [eval_add,eval_X]
    unfold canonicalNumericMeasure at hw ⊢
    omega
  simpa only [rawTrialBits,eval_comp] using
    (hq (rawDrawParameters z)).trans (polynomial_eval_monotone q hm)

theorem rawTabulationMeasure_polynomial : ∃ p : Polynomial ℕ,∀ z,
    rawTabulationMeasure z ≤ p.eval (rawBoxMeasure z) := by
  obtain ⟨p,hp⟩ := rawTrialBits_polynomial
  refine ⟨4*X+24*X^5+X^50*(X+1)^2+p+X^4*(X+1),?_⟩
  intro z
  let M := rawBoxMeasure z
  have hd : z.2.1 ≤ M := by unfold M rawBoxMeasure canonicalNumericMeasure; omega
  have hh : z.2.2 ≤ M := by unfold M rawBoxMeasure canonicalNumericMeasure; omega
  have hw : weight z ≤ M := by unfold M rawBoxMeasure canonicalNumericMeasure; omega
  have hg : (4*z.2.1^8)^tabulationDimension z ≤ M := by unfold M rawBoxMeasure; omega
  have hc : gridStateCount (completionEnumerationData z.1) ≤ M := by unfold M rawBoxMeasure; omega
  have ha : 8*z.2.1^5 ≤ 8*M^5 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _)
  have hb : denseStepBits z.2.1 ≤ 16*M^5 :=
    (denseStepBits_upper _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hd _))
  have hs : z.2.1^50*(z.2.2+1)^2 ≤ M^50*(M+1)^2 :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left (by omega) _)
  have hr : z.2.1^4*(z.2.2+1) ≤ M^4*(M+1) :=
    Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (by omega)
  have ht : rawTrialBits z ≤ p.eval M :=
    (hp z).trans (polynomial_eval_monotone p (by unfold M rawBoxMeasure; omega))
  change (4*z.2.1^8)^tabulationDimension z+8*z.2.1^5+denseStepBits z.2.1+
    z.2.1^50*(z.2.2+1)^2+weight z+gridStateCount (completionEnumerationData z.1)+
    rawTrialBits z+z.2.1^4*(z.2.2+1) ≤ _
  change _ ≤ (4*X+24*X^5+X^50*(X+1)^2+p+X^4*(X+1)).eval M
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_pow,eval_one]
  omega

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactInputBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact-sampler parameters in the public binary input size -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.LiteralCodec
open ProfilePrograms DensePrograms Algorithms Polynomial
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "S" => samplingSize n r 0

lemma exact_public_length (htotal : (∑ i,r i)=∑ j,c j) :
    (encodeMargins r c).length ≤ 5*S^2 := by
  have h := encodeSamplingInput_length r c htotal 0
  have he : (encodeMargins r c).length ≤ (encodeSamplingInput r c 0).length := by
    simp only [encodeSamplingInput,List.length_append]
    omega
  exact he.trans h

lemma exact_public_weight (htotal : (∑ i,r i)=∑ j,c j) :
    weight (encodeMargins r c) ≤ 91*S^2 := by
  have h := exact_public_length r c htotal
  have hS : 1 ≤ S^2 := one_le_pow₀ (by unfold samplingSize; omega)
  rw [weight_word]
  omega

lemma exact_precision_bound : correctionPrecision r c ≤ 245^8*S^16 := by
  let dim := CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)
  have hi := sampling_internal_size_bound r c 0
  have hd : dim ≤ 245*S^2 := by dsimp only [dim]; omega
  have hb : smallBinaryLength r c ≤ 245*S^2 := by omega
  change dim^6*(smallBinaryLength r c)^2 ≤ _
  calc
    _ ≤ (245*S^2)^6*(245*S^2)^2 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hd _) (Nat.pow_le_pow_left hb _)
    _ = 245^8*S^16 := by ring

lemma exact_margin_weight_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → weight (List.ofFn r,List.ofFn c) ≤ p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := polynomial_exactParsedMargins
  refine ⟨p.comp (91*X^2),?_⟩
  intro m n r c htotal
  have h := (Nat.le_add_left _ _).trans (hp (encodeMargins r c))
  rw [exactParsedMargins_spec] at h
  exact h.trans (by
    rw [eval_comp]
    simp only [eval_mul,eval_ofNat,eval_pow,eval_X]
    exact polynomial_eval_monotone p (exact_public_weight r c htotal))

lemma exact_parameter_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → exactParameterMeasure (List.ofFn r,List.ofFn c) ≤
        p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := exact_margin_weight_polynomial
  refine ⟨C (245^8)*X^16+p,?_⟩
  intro m n r c htotal
  simp only [exactParameterMeasure,exactPrecision_ofFn,eval_add,eval_mul,eval_C,eval_pow,eval_X]
  exact Nat.add_le_add (exact_precision_bound r c) (hp m n r c htotal)

lemma exact_ordinary_bits_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      exactOrdinaryBits (List.ofFn r,List.ofFn c) ≤ p.eval (samplingSize n r 0) := by
  let q : Polynomial ℕ := X+2*(C (245^8)*X^16)
  refine ⟨C (344^644)*q^1288,?_⟩
  intro m n r c
  have hD := exact_precision_bound r c
  have hS : samplingSize n r (2*correctionPrecision r c) ≤ q.eval (samplingSize n r 0) := by
    simp only [q,eval_add,eval_mul,eval_ofNat,eval_C,eval_pow,eval_X]
    unfold samplingSize at *
    omega
  rw [exactOrdinaryBits_ofFn]
  have hf : finiteSamplerBits r c (2*correctionPrecision r c) ≤
      344^644*(samplingSize n r (2*correctionPrecision r c))^1288 :=
    sampling_word_budget_polynomial r c (2*correctionPrecision r c)
  have hp (k : ℕ) :
      344^644*(samplingSize n r (2*correctionPrecision r c))^k ≤
        (C (344^644)*q^k).eval (samplingSize n r 0) := by
    rw [eval_mul,eval_C,eval_pow]
    exact Nat.mul_le_mul_left (344^644) (Nat.pow_le_pow_left hS k)
  exact hf.trans (hp 1288)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledScalarBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Charging scalar tabulation loops to the ordinary sampler's word -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma parameterDimension_pos (z : SamplingParameters) : 0 < parameterDimension z := by
  unfold parameterDimension marginDimension
  omega

lemma parameterBinaryLength_pos (z : SamplingParameters) : 0 < parameterBinaryLength z := by
  have h := parameterDimension_pos z
  unfold parameterBinaryLength marginBinaryLength parameterDimension at *
  omega

lemma parameterSteps_pos (z : SamplingParameters) : 0 < parameterSteps z := by
  unfold parameterSteps
  exact Nat.mul_pos (pow_pos (parameterDimension_pos z) _)
    (pow_pos (by have := parameterBinaryLength_pos z; omega) _)

lemma parameterTrials_pos (z : SamplingParameters) : 0 < parameterTrials z := by
  unfold parameterTrials
  exact Nat.mul_pos (pow_pos (parameterDimension_pos z) _) (by omega)

lemma parameterCompletionWidth_pos (z : SamplingParameters) : 0 < parameterCompletionWidth z := by
  unfold parameterCompletionWidth
  exact Nat.mul_pos (by decide) (pow_pos (by omega) _)

lemma parameterDimension_le_steps (z : SamplingParameters) :
    parameterDimension z ≤ parameterSteps z := by
  have hd : 1 ≤ parameterDimension z := parameterDimension_pos z
  have hb : 1 ≤ z.2+parameterBinaryLength z := by have := parameterBinaryLength_pos z; omega
  exact (Nat.le_self_pow (by decide : 200 ≠ 0) _).trans (by
    unfold parameterSteps
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((parameterDimension z)^200)
      (one_le_pow₀ hb : 1 ≤ (z.2+parameterBinaryLength z)^2))

lemma parameterBinaryLength_le_steps (z : SamplingParameters) :
    parameterBinaryLength z ≤ parameterSteps z := by
  have hd : 1 ≤ (parameterDimension z)^200 := one_le_pow₀ (parameterDimension_pos z)
  have hb : parameterBinaryLength z ≤ (z.2+parameterBinaryLength z)^2 :=
    (Nat.le_add_left _ _).trans (Nat.le_self_pow (by decide) _)
  unfold parameterSteps
  exact hb.trans (by simpa only [Nat.one_mul] using
    Nat.mul_le_mul_right ((z.2+parameterBinaryLength z)^2) hd)

lemma parameterAccuracy_le_steps (z : SamplingParameters) :
    parameterAccuracy z ≤ parameterSteps z := by
  unfold parameterAccuracy parameterSteps
  exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (parameterDimension_pos z) (by decide))

theorem schedule_numeric_polynomial : ∃ p : Polynomial ℕ,∀ z,
    parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤
      p.eval (scheduledCountInputMeasure z) := by
  refine ⟨2*X+25*(3*X+1)^62,?_⟩
  intro z
  let M := scheduledCountInputMeasure z
  have hs : parameterSteps z ≤ M := by unfold M scheduledCountInputMeasure; omega
  have hd := (parameterDimension_le_steps z).trans hs
  have hb := (parameterBinaryLength_le_steps z).trans hs
  have ha := (parameterAccuracy_le_steps z).trans hs
  have hf : parameterCompletionWidth z ≤ 25*(3*M+1)^62 := by
    unfold parameterCompletionWidth
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
  simp only [eval_add,eval_mul,eval_pow,eval_ofNat,eval_X,eval_one]
  change _ ≤ 2*M+25*(3*M+1)^62
  omega

lemma scheduledCountInputMeasure_le (z : SamplingParameters) :
    scheduledCountInputMeasure z ≤ 4*parameterWordCount z+weight z := by
  let N := parameterSteps z
  let J := parameterTrials z
  let P := parameterProposalWidth z
  let F := parameterCompletionWidth z
  let A := N*(P+F)+F
  have hN : 1 ≤ N := parameterSteps_pos z
  have hJ : 1 ≤ J := parameterTrials_pos z
  have hF : 1 ≤ F := parameterCompletionWidth_pos z
  have hNF : N ≤ N*(P+F) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left N (show 1 ≤ P+F by omega)
  have hPF : P+F ≤ N*(P+F) := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (P+F) hN
  have hA : 1 ≤ A := by unfold A; omega
  have hAW : A ≤ J*A := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right A hJ
  have hJW : J ≤ J*A := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left J hA
  have hT : scheduledTrialWidth z ≤ A := by
    unfold scheduledTrialWidth scheduledDenseWidth scheduledUnitWidth
    change (if hasLargeRectangle z then N*(P+F)+F else N*P) ≤ A
    split_ifs
    · exact le_rfl
    · unfold A
      exact (Nat.mul_le_mul_left N (Nat.le_add_right P F)).trans (Nat.le_add_right _ _)
  change N+J+P+scheduledTrialWidth z+weight z ≤ 4*(J*A)+weight z
  have hNA : N ≤ A := by unfold A; omega
  have hPA : P ≤ A := by unfold A; omega
  have hnw := hNA.trans hAW
  have hpw := hPA.trans hAW
  have htw := hT.trans hAW
  omega

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms Polynomial
open scoped BigOperators Classical
noncomputable section

theorem exact_count_input_measure_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j →
      scheduledCountInputMeasure (exactSamplingParameters (List.ofFn r,List.ofFn c)) ≤
        p.eval (Algorithms.samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := exact_ordinary_bits_polynomial
  obtain ⟨q,hq⟩ := exact_margin_weight_polynomial
  obtain ⟨u,hu⟩ := polynomial_exactSamplingParameters
  refine ⟨4*p+u.comp q,?_⟩
  intro m n r c htotal
  have hw : weight (exactSamplingParameters (List.ofFn r,List.ofFn c)) ≤
      u.eval (q.eval (Algorithms.samplingSize n r 0)) :=
    (Nat.le_add_left _ _).trans ((hu (List.ofFn r,List.ofFn c)).trans
    (polynomial_eval_monotone u (hq m n r c htotal)))
  have hb : parameterWordCount (exactSamplingParameters (List.ofFn r,List.ofFn c)) ≤
      p.eval (Algorithms.samplingSize n r 0) := hp m n r c
  have hs := scheduledCountInputMeasure_le (exactSamplingParameters (List.ofFn r,List.ofFn c))
  simp only [eval_add,eval_mul,eval_ofNat,eval_comp]
  omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactBoxBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The boxes actually enumerated by the exact correction have singly exponential size -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts SmallContextCoordinates
open PhysicalCompletionFibres FirstPaperPhysicalMarginal
open scoped BigOperators Classical
noncomputable section

variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "b" => smallBinaryLength r c

lemma originalEnumeration_count :
    gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn c))=((∑ i,r i)+1)^(m*n) := by
  rw [gridStateCount_eq]
  simp only [originalEnumerationData,originalLayoutMargins,completionEnumerationData,
    zeroGrid,List.tail_cons,cellPairs,List.length_map,List.length_range,List.length_ofFn,
    List.sum_cons,List.sum_ofFn,zero_add]

lemma originalEnumeration_count_bound :
    gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn c))≤2^(d*b) := by
  rw [originalEnumeration_count]
  have hN : (∑ i,r i)+1≤2^b :=
    (show (∑ i,r i)+1≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hdim : m*n≤d := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  calc
    ((∑ i,r i)+1)^(m*n) ≤ (2^b)^(m*n) := Nat.pow_le_pow_left hN _
    _ = 2^(b*(m*n)) := (pow_mul _ _ _).symm
    _ ≤ 2^(d*b) := Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma profileEnumeration_count (e : Fin q ≃ Cells (paperSmall r c)) (x : PaperStates r c) :
    gridStateCount (profileEnumerationData (stateCodeData r c e x))=(d^20+1)^(q+q) := by
  rw [gridStateCount_eq]
  simp only [profileEnumerationData,stateCodeData,codeCheckData,cellCatalog,List.length_map,
    List.length_append,List.length_ofFn]

lemma profileEnumeration_count_bound (e : Fin q ≃ Cells (paperSmall r c)) (x : PaperStates r c) :
    gridStateCount (profileEnumerationData (stateCodeData r c e x))≤2^(2*(d*b)) := by
  rw [profileEnumeration_count]
  have hU : d^20+1≤2^b :=
    (show d^20+1≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hq : q≤d := by
    have he : q=Fintype.card (Cells (paperSmall r c)) := by
      simpa only [Fintype.card_fin] using Fintype.card_congr e
    rw [he]
    exact (RowMajorEnumeration.small_card_le_dimension (paperSmall r c)).trans dimension_le_allowance
  calc
    (d^20+1)^(q+q) ≤ (2^b)^(q+q) := Nat.pow_le_pow_left hU _
    _ = 2^(b*(q+q)) := (pow_mul _ _ _).symm
    _ ≤ 2^(2*(d*b)) := Nat.pow_le_pow_right (by decide) (by nlinarith)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_CacheBoxBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite boxes controlling one cached transition entry -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms Polynomial

theorem completionWeightMeasure_polynomial : ∃ p : Polynomial ℕ,∀ z,
    completionWeightMeasure z ≤ p.eval (completionBoxMeasure z) := by
  obtain ⟨p,hp⟩ := polynomial_canonicalCountInput
  obtain ⟨q,hq⟩ := rawTabulationMeasure_polynomial
  refine ⟨q+p+2*X,?_⟩
  intro z
  let M := completionBoxMeasure z
  have hz : weight z ≤ M := by unfold M completionBoxMeasure; omega
  have hw : weight (canonicalCountInput z) ≤ p.eval M :=
    (Nat.le_add_left _ _).trans ((hp z).trans (polynomial_eval_monotone p hz))
  have hb : rawBoxMeasure (canonicalCountInput z).1 ≤ M := by
    unfold M completionBoxMeasure; omega
  have hr : rawTabulationMeasure (canonicalCountInput z).1 ≤ q.eval M :=
    (hq (canonicalCountInput z).1).trans (polynomial_eval_monotone q hb)
  have hc : gridStateCount (completionEnumerationData z.1)+weight z.1 ≤ M := by
    have := weight_fst z
    unfold M completionBoxMeasure
    omega
  change rawTabulationMeasure (canonicalCountInput z).1+weight (canonicalCountInput z)+
    weight z+(gridStateCount (completionEnumerationData z.1)+weight z.1) ≤ _
  change _ ≤ (q+p+2*X).eval M
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  omega

end ContingencyTables.DensePrograms

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma polynomial_entryResidual : PolynomialTime entryResidualRealizer :=
  polynomial_composition (polynomial_composition polynomial_entryCacheParameters polynomial_first)
    polynomial_residualParameters

/-- Separating binary preparation size from the four enumerated boxes. -/
theorem matrixEntryBox_bound : ∃ p : Polynomial ℕ,∀ z,
    let r := entryResidualParameters z
    let a := (canonicalCountInput r).1
    matrixEntryBox z ≤ (4*a.2.1^8)^tabulationDimension a+
      gridStateCount (completionEnumerationData a.1)+
      gridStateCount (completionEnumerationData r.1)+gridStateCount (z.1.2,2)+
      r.2.1+r.2.2+(entryCacheParameters z).2+p.eval (weight z) := by
  obtain ⟨p,hp⟩ := polynomial_entryResidual
  obtain ⟨q,hq⟩ := polynomial_canonicalCountInput
  refine ⟨q.comp p+p+X,?_⟩
  intro z
  dsimp only
  have hr : weight (entryResidualParameters z) ≤ p.eval (weight z) :=
    (Nat.le_add_left _ _).trans (hp z)
  have ha : weight (canonicalCountInput (entryResidualParameters z)) ≤
      q.eval (p.eval (weight z)) :=
    (Nat.le_add_left _ _).trans ((hq _).trans (polynomial_eval_monotone q hr))
  have hf := (weight_fst (canonicalCountInput (entryResidualParameters z))).trans ha
  change weight (canonicalCountInput (entryResidualParameters z)).1 ≤
    q.eval (p.eval (weight z)) at hf
  simp only [eval_add,eval_comp,eval_X]
  change (4*((canonicalCountInput (entryResidualParameters z)).1).2.1^8)^
      tabulationDimension (canonicalCountInput (entryResidualParameters z)).1+
      gridStateCount (completionEnumerationData (canonicalCountInput (entryResidualParameters z)).1.1)+
      ((entryResidualParameters z).2.1+(entryResidualParameters z).2.2+
        weight (canonicalCountInput (entryResidualParameters z)).1)+
      gridStateCount (completionEnumerationData (entryResidualParameters z).1)+
      weight (entryResidualParameters z)+(entryCacheParameters z).2+
      gridStateCount (z.1.2,2)+weight z ≤ _
  omega

theorem matrixEntryMeasure_polynomial : ∃ p : Polynomial ℕ,∀ z,
    matrixEntryMeasure z ≤ p.eval (matrixEntryBox z) := by
  obtain ⟨p,hp⟩ := polynomial_entryCacheParameters
  obtain ⟨q,hq⟩ := completionWeightMeasure_polynomial
  refine ⟨q+p+X,?_⟩
  intro z
  let M := matrixEntryBox z
  have hz : weight z ≤ M := by unfold M matrixEntryBox; omega
  have hw : weight (entryCacheParameters z) ≤ p.eval M :=
    (Nat.le_add_left _ _).trans ((hp z).trans (polynomial_eval_monotone p hz))
  have hc : completionBoxMeasure (residualParameters (entryCacheParameters z).1) ≤ M := by
    unfold M matrixEntryBox; omega
  have hq' : completionWeightMeasure (residualParameters (entryCacheParameters z).1) ≤
      q.eval M := (hq _).trans (polynomial_eval_monotone q hc)
  have hs : (entryCacheParameters z).2+gridStateCount (z.1.2,2)+weight z ≤ M := by
    unfold M matrixEntryBox; omega
  change (entryCacheParameters z).2+
    completionWeightMeasure (residualParameters (entryCacheParameters z).1)+
    weight (entryCacheParameters z)+gridStateCount (z.1.2,2)+weight z ≤ _
  change _ ≤ (q+p+X).eval M
  simp only [eval_add,eval_X]
  omega

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualEnumerationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The completion boxes used at arbitrary enumerated profiles -/

namespace ContingencyTables.ProfilePrograms
open DensePrograms

lemma completionEnumeration_count (z : CompletionMargins) :
    gridStateCount (completionEnumerationData z)=
      (z.1.sum+1)^(z.1.tail.length*z.2.tail.length) := by
  rw [gridStateCount_eq]
  simp only [completionEnumerationData,List.length_map,zeroGrid,cellPairs,List.length_range]

lemma completionEnumeration_count_le (z : CompletionMargins) (m n N : ℕ)
    (hr : z.1.length ≤ m) (hc : z.2.length ≤ n) (hN : z.1.sum ≤ N) :
    gridStateCount (completionEnumerationData z) ≤ (N+1)^(m*n) := by
  rw [completionEnumeration_count]
  have hr' : z.1.tail.length ≤ m := by simp only [List.length_tail]; omega
  have hc' : z.2.tail.length ≤ n := by simp only [List.length_tail]; omega
  exact (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) _).trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul hr' hc'))

lemma swapZeroList_length {A : Type} [MatchingFPRAS.TreeTyped.Codec A] [Inhabited A]
    (i : ℕ) (as : List A) : (DensePrograms.swapZeroList (i,as)).length=as.length := by
  simp only [swapZeroList,swapZeroIndices,List.length_map,List.length_range]

lemma swapZeroList_sum_le (i : ℕ) (as : List ℕ) :
    (DensePrograms.swapZeroList (i,as)).sum ≤ as.length*as.sum := by
  have h := list_sum_le_length_mul (DensePrograms.swapZeroList (i,as)) as.sum (by
    intro a ha
    rw [swapZeroList] at ha
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp ha
    exact list_getD_le_sum as (swapZeroIndex (i,j)))
  simpa only [swapZeroList_length] using h

lemma normalizedCompletion_count_le (z : CompletionMargins) (ij : ℕ×ℕ) :
    gridStateCount (completionEnumerationData (swapMargins (ij,z))) ≤
      (z.1.length*z.1.sum+1)^(z.1.length*z.2.length) := by
  apply completionEnumeration_count_le
  · simp only [swapMargins,swapZeroList_length,le_refl]
  · simp only [swapMargins,swapZeroList_length,le_refl]
  · exact swapZeroList_sum_le ij.1 z.1

lemma canonicalCompletion_count_le (z : CanonicalParameters) :
    gridStateCount (completionEnumerationData (canonicalCountInput z).1.1) ≤
      (z.1.1.length*z.1.1.sum+1)^(z.1.1.length*z.1.2.length) := by
  exact normalizedCompletion_count_le z.1 (DensePrograms.marginIndices z.1)

lemma profilePaddedMargins_length (row : Bool) (z : ProfileCheckData×ℕ) :
    (profilePaddedMargins row z).length ≤
      (if row then z.1.1.2.1 else z.1.1.2.2).length := by
  exact largePaddedMargins_length row (profilePaddingData row z)

lemma profilePaddedMargins_sum (row : Bool) (z : ProfileCheckData×ℕ) :
    (profilePaddedMargins row z).sum ≤
      (if row then z.1.1.2.1 else z.1.1.2.2).length*
        ((if row then z.1.1.2.1 else z.1.1.2.2).sum+
          (if !row then z.1.1.2.1 else z.1.1.2.2).length*z.2) := by
  exact largePaddedMargins_sum row (profilePaddingData row z)

lemma profilePaddedMargins_sum_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (v : ProfileCheckData) (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) (pad : ℕ) :
    (profilePaddedMargins true (v,pad)).sum+1 ≤ m*((List.ofFn r).sum+n*pad)+1 := by
  have hsum := profilePaddedMargins_sum true (v,pad)
  simp only [hr,hc,List.length_ofFn,ite_true, if_true,Bool.not_true,Bool.false_eq_true,ite_false] at hsum
  exact Nat.add_le_add_right hsum 1

/-- This bound is independent of the values in the two proposed small
views. In particular it applies before the validity test accepts them. -/
lemma profileCompletion_count (z : ProfileCheckData×ℕ) :
    gridStateCount (completionEnumerationData
      (profilePaddedMargins true z,profilePaddedMargins false z)) ≤
      (z.1.1.2.1.length*(z.1.1.2.1.sum+z.1.1.2.2.length*z.2)+1)^
        (z.1.1.2.1.length*z.1.1.2.2.length) := by
  apply completionEnumeration_count_le
  · simpa using profilePaddedMargins_length true z
  · simpa using profilePaddedMargins_length false z
  · simpa using profilePaddedMargins_sum true z

end ContingencyTables.ProfilePrograms

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] profilePaddedMargins

private lemma padded_base_bound (d b N m n : ℕ) (hd : 1 ≤ d) (hb : 1 ≤ b)
    (hm : m ≤ d) (hn : n ≤ d) (hN : N+1 ≤ 2^b) (hD : d^20+1 ≤ 2^b) :
    m*(N+n*d^12)+1 ≤ 2^(4*b) := by
  have hd20 : d ≤ d^20 := Nat.le_self_pow (by decide) d
  have hmP : m ≤ 2^b := hm.trans (hd20.trans (by omega))
  have hd14 : d^14 ≤ d^20 := Nat.pow_le_pow_right hd (by decide)
  have hpad : m*n*d^12 ≤ 2^b := by
    calc
      _ ≤ d*d*d^12 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hm hn)
      _ = d^14 := by ring
      _ ≤ 2^b := hd14.trans (by omega)
  have hprod : m*N ≤ (2^b)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hmP (show N ≤ 2^b by omega)
  have hP : 1 ≤ 2^b := one_le_pow₀ (by decide)
  have hP2 : 2^b ≤ (2^b)^2 := Nat.le_self_pow (by decide) _
  calc
    _ ≤ 4*(2^b)^2 := by nlinarith
    _ = 2^(2*b+2) := by rw [show 2*b=b*2 by omega,pow_add,pow_mul]; norm_num; ring
    _ ≤ 2^(4*b) := Nat.pow_le_pow_right (by decide) (by omega)

/-- All profile proposals have a singly exponential completion box,
including proposals rejected by the chain's validity test. -/
lemma arbitrary_profile_margin_sum {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) :
    let dim := dimensionAllowance (I := Fin m) (J := Fin n)
    (profilePaddedMargins true (v,dim^12)).sum+1 ≤ 2^(4*smallBinaryLength r c) := by
  dsimp only
  let dim := dimensionAllowance (I := Fin m) (J := Fin n)
  let bits := smallBinaryLength r c
  have hd : 1 ≤ dim := by unfold dim dimensionAllowance; omega
  have hm : m ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hn : n ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hN : (∑ i,r i)+1 ≤ 2^bits :=
    (show (∑ i,r i)+1 ≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hD : dim^20+1 ≤ 2^bits :=
    (show dim^20+1 ≤ stateBound r c+1 by unfold dim stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hbase := padded_base_bound dim bits (∑ i,r i) m n hd hb hm hn hN hD
  have hsum := profilePaddedMargins_sum_ofFn r c v hr hc (dim^12)
  rw [List.sum_ofFn] at hsum
  exact hsum.trans hbase

lemma arbitrary_profile_completion_count {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) :
    let dim := dimensionAllowance (I := Fin m) (J := Fin n)
    gridStateCount (completionEnumerationData
      (profilePaddedMargins true (v,dim^12),profilePaddedMargins false (v,dim^12))) ≤
      2^(4*(dim^2*smallBinaryLength r c)) := by
  dsimp only
  let dim := dimensionAllowance (I := Fin m) (J := Fin n)
  let bits := smallBinaryLength r c
  have hd : 1 ≤ dim := by unfold dim dimensionAllowance; omega
  have hm : m ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hn : n ≤ dim := by unfold dim dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hN : (∑ i,r i)+1 ≤ 2^bits :=
    (show (∑ i,r i)+1 ≤ stateBound r c+1 by unfold stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hD : dim^20+1 ≤ 2^bits :=
    (show dim^20+1 ≤ stateBound r c+1 by unfold dim stateBound; omega).trans
      (smallBinaryLength_parameters r c).2.2
  have hbase := padded_base_bound dim bits (∑ i,r i) m n hd hb hm hn hN hD
  have hcount := profileCompletion_count (v,dim^12)
  simp only [hr,hc,List.length_ofFn,List.sum_ofFn] at hcount
  calc
    _ ≤ (m*((∑ i,r i)+n*dim^12)+1)^(m*n) := hcount
    _ ≤ (2^(4*bits))^(m*n) := Nat.pow_le_pow_left hbase _
    _ = 2^((4*bits)*(m*n)) := (pow_mul _ _ _).symm
    _ ≤ 2^(4*(dim^2*bits)) := Nat.pow_le_pow_right (by decide) (by
      have hh : m*n ≤ dim^2 := by simpa only [pow_two] using Nat.mul_le_mul hm hn
      nlinarith)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ResidualBoxScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One scale for all boxes in the rare exact correction -/

namespace ContingencyTables.SmallGraphProfiles
open ProfilePrograms DensePrograms CompletionCounts
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] profilePaddedMargins

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "dim" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "bits" => smallBinaryLength r c

private lemma normalized_base_bound (b l s : ℕ) (hb : 1 ≤ b)
    (hl : l ≤ 2^b) (hs : s+1 ≤ 2^(4*b)) : l*s+1 ≤ 2^(6*b) := by
  have hm := Nat.mul_le_mul hl (show s ≤ 2^(4*b) by omega)
  have he : (2:ℕ)^b*2^(4*b)=2^(5*b) := by
    calc
      _ = 2^(b+4*b) := (pow_add 2 b (4*b)).symm
      _ = _ := congrArg (fun k : ℕ => (2:ℕ)^k) (by omega)
  rw [he] at hm
  have hp : 1 ≤ (2:ℕ)^(5*b) := one_le_pow₀ (by decide)
  calc
    _ ≤ 2*2^(5*b) := by omega
    _ = 2^(5*b+1) := by rw [pow_succ]; omega
    _ ≤ 2^(6*b) := Nat.pow_le_pow_right (by decide) (by omega)

lemma exactBoxScale_pos : 1 ≤ exactBoxScale r c := by
  exact one_le_pow₀ (by decide)

lemma normalized_profile_completion_count (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) (h : ℕ) :
    gridStateCount (completionEnumerationData
      (canonicalCountInput (residualParameters ((v,dim^12),(dim,h)))).1.1) ≤
      exactBoxScale r c := by
  let R := profilePaddedMargins true (v,dim^12)
  let C := profilePaddedMargins false (v,dim^12)
  have hd : 1 ≤ dim := by unfold dimensionAllowance; omega
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hdb : dim ≤ 2^bits := by
    have h1 : dim ≤ bits := (smallBinaryLength_parameters r c).2.1
    exact h1.trans (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hR : R.length ≤ dim := by
    have ht := profilePaddedMargins_length true (v,dim^12)
    simp only [hr,ite_true, if_true,List.length_ofFn] at ht
    have hm : m ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
    exact ht.trans hm
  have hC : C.length ≤ dim := by
    have ht := profilePaddedMargins_length false (v,dim^12)
    simp only [Bool.false_eq_true,ite_false,hc,List.length_ofFn] at ht
    have hn : n ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
    exact ht.trans hn
  have hsum : R.sum+1 ≤ 2^(4*bits) := arbitrary_profile_margin_sum r c v hr hc
  have hbase : R.length*R.sum+1 ≤ 2^(6*bits) :=
    normalized_base_bound bits R.length R.sum hb (hR.trans hdb) hsum
  have hn := canonicalCompletion_count_le (residualParameters ((v,dim^12),(dim,h)))
  change _ ≤ (R.length*R.sum+1)^(R.length*C.length) at hn
  have hprod : R.length*C.length ≤ dim^2 := by simpa only [pow_two] using Nat.mul_le_mul hR hC
  have h23 : dim^2 ≤ dim^3 := Nat.pow_le_pow_right hd (by decide)
  calc
    _ ≤ (R.length*R.sum+1)^(R.length*C.length) := hn
    _ ≤ (2^(6*bits))^(dim^2) :=
      (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) hprod)
    _ = 2^((6*bits)*dim^2) := (pow_mul _ _ _).symm
    _ ≤ exactBoxScale r c := Nat.pow_le_pow_right (by decide) (by nlinarith)

lemma normalized_profile_dense_grid (v : ProfileCheckData)
    (hr : v.1.2.1=List.ofFn r) (hc : v.1.2.2=List.ofFn c) (h : ℕ) :
    let z := (canonicalCountInput (residualParameters ((v,dim^12),(dim,h)))).1
    (4*z.2.1^8)^tabulationDimension z ≤ exactBoxScale r c := by
  let z := (canonicalCountInput (residualParameters ((v,dim^12),(dim,h)))).1
  have hd : 1 ≤ dim := by unfold dimensionAllowance; omega
  have hb : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have hr' := profilePaddedMargins_length true (v,dim^12)
  have hc' := profilePaddedMargins_length false (v,dim^12)
  simp only [hr,ite_true, if_true,List.length_ofFn] at hr'
  simp only [Bool.false_eq_true,ite_false,hc,List.length_ofFn] at hc'
  have hm : m ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hn : n ≤ dim := by unfold dimensionAllowance; simp only [Fintype.card_fin]; nlinarith
  have hq : tabulationDimension z ≤ dim^2 := by
    unfold tabulationDimension z canonicalCountInput swapMargins residualParameters
    simp only [swapZeroList_length,List.length_tail]
    simpa only [pow_two] using Nat.mul_le_mul
      ((Nat.sub_le _ _).trans (hr'.trans hm)) ((Nat.sub_le _ _).trans (hc'.trans hn))
  have hbase : 4*dim^8 ≤ 2^(10*dim) := by
    have hdim : dim ≤ 2^dim := Nat.le_of_lt (Nat.lt_two_pow_self)
    calc
      _ ≤ 4*(2^dim)^8 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hdim 8)
      _ = 2^(dim*8+2) := by rw [←pow_mul,pow_add]; norm_num; ring
      _ ≤ 2^(10*dim) := Nat.pow_le_pow_right (by decide) (by omega)
  change (4*dim^8)^tabulationDimension z ≤ exactBoxScale r c
  calc
    _ ≤ (2^(10*dim))^(dim^2) :=
      (Nat.pow_le_pow_left hbase _).trans (Nat.pow_le_pow_right (by positivity) hq)
    _ = 2^((10*dim)*dim^2) := (pow_mul _ _ _).symm
    _ ≤ exactBoxScale r c := Nat.pow_le_pow_right (by decide) (by
      have hbits : dim^3 ≤ dim^3*bits := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (dim^3) hb
      nlinarith)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalPointBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary size of one candidate in the original-table enumeration -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma originalCandidates_length (z : CompletionMargins) :
    (originalCandidates z).length=gridStateCount (originalEnumerationData z) := by
  simp only [originalCandidates,List.length_map,gridWords,List.length_range]

theorem originalCandidates_point_polynomial : ∃ p : Polynomial ℕ,∀ z v,
    v∈originalCandidates z → weight v ≤ p.eval (weight z) := by
  obtain ⟨p,hp⟩ := polynomial_originalEnumerationData
  obtain ⟨q,hq⟩ := polynomial_originalCandidate
  let word : Polynomial ℕ := p*(4*p+2)+1
  refine ⟨q.comp (1+X+word),?_⟩
  intro z v hv
  rw [originalCandidates] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  have hdata : weight (originalEnumerationData z) ≤ p.eval (weight z) :=
    (Nat.le_add_left _ _).trans (hp z)
  have hlen : (originalEnumerationData z).1.length ≤ p.eval (weight z) :=
    (list_length_le_weight _).trans ((weight_fst _).trans hdata)
  have hbase : weight (originalEnumerationData z).2 ≤ p.eval (weight z) :=
    (weight_snd _).trans hdata
  have hword := gridWords_point_weight (originalEnumerationData z) (by
    change 0 < (originalLayoutMargins z).1.sum+1
    omega) w hw
  have hw' : weight w ≤ word.eval (weight z) := by
    apply hword.trans
    simp only [word,eval_add,eval_mul,eval_ofNat,eval_one]
    exact Nat.add_le_add_right (Nat.mul_le_mul hlen (by omega)) 1
  have hin : weight (z,w) ≤ (1+X+word).eval (weight z) := by
    simp only [weight_prod,eval_add,eval_one,eval_X]
    omega
  simpa only [eval_comp] using
    (Nat.le_add_left _ _).trans ((hq (z,w)).trans (polynomial_eval_monotone q hin))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TabulationMeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounding the nested measures of the executed profile tabulation -/

namespace ContingencyTables.MeasuredMap
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma listMeasure_le {A B : Type} [Codec A] [Codec B] (μ : A×B → ℕ)
    (a : A) (bs : List B) (M : ℕ) (h : ∀ b∈bs,μ (a,b) ≤ M) :
    listMeasure μ (a,bs) ≤ weight (a,bs)+bs.length*M := by
  have hs := ProfilePrograms.list_sum_le_length_mul
    (bs.map (fun b => μ (a,b))) M (by
      intro n hn
      obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hn
      exact h b hb)
  simpa only [listMeasure,List.length_map] using Nat.add_le_add_left hs (weight (a,bs))

lemma listMeasure_mono {A B : Type} [Codec A] [Codec B] (μ ν : A×B → ℕ)
    (a : A) (bs : List B) (h : ∀ b∈bs,μ (a,b) ≤ ν (a,b)) :
    listMeasure μ (a,bs) ≤ listMeasure ν (a,bs) := by
  have hs : (bs.map (fun b => μ (a,b))).sum ≤ (bs.map (fun b => ν (a,b))).sum := by
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons,List.sum_cons]
      exact Nat.add_le_add (h b (by simp))
        (ih (by intro c hc; exact h c (by simp [hc])))
  exact Nat.add_le_add_left hs _

end ContingencyTables.MeasuredMap

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma list_weight_bound {A : Type} [Codec A] (as : List A) (W : ℕ)
    (h : ∀ a∈as,weight a ≤ W) : weight as ≤ as.length*(W+1)+1 := by
  simpa only [List.map_id,id_eq] using weight_map_bound (f := id) (as := as) h

/-- The two loops over the profile box cost a polynomial in its
cardinality and the uniform measure of a single transition entry. -/
lemma profileMatrixMeasure_le (z : MatrixParameters) (W M : ℕ)
    (hz : weight z ≤ W)
    (hv : ∀ v∈profileBoxViews (matrixData z),weight v ≤ W)
    (he : ∀ u∈profileBoxViews (matrixData z),∀ v∈profileBoxViews (matrixData z),
      matrixEntryMeasure (z,(u,v)) ≤ M) :
    let N := gridStateCount (profileEnumerationData (matrixData z))
    profileMatrixMeasure z ≤ (N+1)^2*(M+3*W+7) := by
  let vs := profileBoxViews (matrixData z)
  let N := gridStateCount (profileEnumerationData (matrixData z))
  have hlen : vs.length=N := profileBoxViews_length _
  have hvs : weight vs ≤ N*(W+1)+1 := by
    simpa only [hlen] using list_weight_bound vs W hv
  have hc (v : List ℕ×List ℕ) (hv' : v∈vs) :
      matrixColumnMeasure (z,v) ≤ (N+1)*(M+2*W+4) := by
    have hpair : weight ((z,v),vs) ≤ (N+1)*(2*W+3) := by
      have hw := hv v hv'
      simp only [weight_prod]
      nlinarith
    have hsum := MeasuredMap.listMeasure_le columnEntryMeasure (z,v) vs M (by
      intro u hu
      exact he u hu v hv')
    have hh : matrixColumnMeasure (z,v) ≤ N+(N+1)*(2*W+3)+N*M := by
      unfold matrixColumnMeasure
      change N+MeasuredMap.listMeasure columnEntryMeasure ( (z,v),vs) ≤ _
      rw [hlen] at hsum
      omega
    exact hh.trans (by nlinarith)
  have hout : weight (z,vs) ≤ (N+1)*(W+2) := by
    simp only [weight_prod]
    nlinarith
  have hs := MeasuredMap.listMeasure_le matrixColumnMeasure z vs
    ((N+1)*(M+2*W+4)) hc
  rw [hlen] at hs
  have hm : profileMatrixMeasure z ≤
      N+(N+1)*(W+2)+N*((N+1)*(M+2*W+4)) := by
    unfold profileMatrixMeasure
    change N+MeasuredMap.listMeasure matrixColumnMeasure (z,vs) ≤ _
    omega
  have h1 : N ≤ (N+1)^2 := by nlinarith
  have h2 : N+1 ≤ (N+1)^2 := Nat.le_self_pow (by decide) _
  have h3 : N*(N+1) ≤ (N+1)^2 := by nlinarith
  calc
    _ ≤ N+(N+1)*(W+2)+N*((N+1)*(M+2*W+4)) := hm
    _ ≤ (N+1)^2+(N+1)^2*(W+2)+(N+1)^2*(M+2*W+4) := by
      exact Nat.add_le_add (Nat.add_le_add h1 (Nat.mul_le_mul_right _ h2))
        (by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h3)
    _ = (N+1)^2*(M+3*W+7) := by ring

lemma unitMatrixMeasure_le (z : MatrixParameters) :
    UnitCountPrograms.profileMatrixMeasure z ≤ profileMatrixMeasure z := by
  unfold UnitCountPrograms.profileMatrixMeasure profileMatrixMeasure
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro v _
  unfold UnitCountPrograms.matrixColumnMeasure matrixColumnMeasure
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro u _
  change UnitCountPrograms.entryMeasure (columnEntryInput ((z,v),u)) ≤
    matrixEntryMeasure (columnEntryInput ((z,v),u))
  unfold UnitCountPrograms.entryMeasure matrixEntryMeasure
  omega

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileVectorMeasureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform bounds for the executed nested trial-vector loops -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma terminalColumnMeasure_le (z : TerminalColumnInput) (M : ℕ)
    (hz : weight z.1 ≤ M) (hT : weight z.2 ≤ M)
    (hN : gridStateCount (profileEnumerationData (matrixData z.1)) ≤ M)
    (hv : ∀ v∈profileBoxViews (matrixData z.1),weight v ≤ M)
    (he : ∀ v∈profileBoxViews (matrixData z.1),matrixEntryMeasure (z.1,(v,v)) ≤ M) :
    terminalColumnMeasure z ≤ (M+1)*(8*M+8) := by
  let vs := profileBoxViews (matrixData z.1)
  have hzz : weight z=1+weight z.1+weight z.2 := by
    rcases z with ⟨z,T⟩
    simp only [weight_prod]
  have hlen : vs.length ≤ M := (profileBoxViews_length _).le.trans hN
  have hvs : weight vs ≤ M*(M+1)+1 :=
    (list_weight_bound vs M hv).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hentry (v : List ℕ×List ℕ) (hv' : v∈vs) :
      terminalColumnEntryMeasure (z,v) ≤ 7*M+4 := by
    have hw := hv v hv'
    have hm := he v hv'
    change matrixEntryMeasure (z.1,(v,v))+weight (z.1,(v,z.2))+weight (z,v) ≤ _
    simp only [weight_prod]
    rw [hzz]
    nlinarith
  have hs := MeasuredMap.listMeasure_le terminalColumnEntryMeasure z vs (7*M+4) hentry
  have hp : weight (z,vs) ≤ 3+2*M+M*(M+1) := by
    simp only [weight_prod]
    rw [hzz]
    omega
  have hm : terminalColumnMeasure z ≤ M+(3+2*M+M*(M+1))+M*(7*M+4) := by
    have hb := Nat.mul_le_mul_right (7*M+4) hlen
    change gridStateCount (profileEnumerationData (matrixData z.1))+
      MeasuredMap.listMeasure terminalColumnEntryMeasure (z,vs) ≤ _
    omega
  exact hm.trans (by nlinarith)

lemma unit_terminalColumnMeasure_le (z : TerminalColumnInput) :
    UnitCountPrograms.terminalColumnMeasure z ≤ terminalColumnMeasure z := by
  unfold UnitCountPrograms.terminalColumnMeasure terminalColumnMeasure
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro v _
  change weight (z.1,(v,z.2))+weight (z,v) ≤
    (matrixEntryMeasure (terminalSourceInput (z.1,(v,z.2)))+weight (z.1,(v,z.2)))+weight (z,v)
  omega

lemma unit_outerVectorMeasure_le (z : OuterVectorInput) :
    UnitCountPrograms.outerVectorMeasure z ≤ outerVectorMeasure z := by
  apply Nat.add_le_add_right
  unfold UnitCountPrograms.trialVectorMeasure trialVectorMeasure
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply MeasuredMap.listMeasure_mono
  intro o _
  change UnitCountPrograms.trialCountMeasure (optionalTrialInput (z.1.1,o))+weight (z.1.1,o) ≤
    trialCountMeasure (optionalTrialInput (z.1.1,o))+weight (z.1.1,o)
  apply Nat.add_le_add_right
  unfold UnitCountPrograms.trialCountMeasure trialCountMeasure
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · unfold UnitCountPrograms.walkCountMeasure walkCountMeasure
    exact Nat.add_le_add_right (Nat.add_le_add_left (unitMatrixMeasure_le _) _) _
  · exact unit_terminalColumnMeasure_le _

theorem outerVectorMeasure_bound (z : OuterVectorInput) (M : ℕ)
    (hz : weight z ≤ M) (hsteps : z.1.1.2.1 ≤ M)
    (hO : gridStateCount (originalEnumerationData z.1.2) ≤ M)
    (hN : gridStateCount (profileEnumerationData (matrixData z.1.1.1)) ≤ M)
    (hv : ∀ v∈profileBoxViews (matrixData z.1.1.1),weight v ≤ M)
    (ho : ∀ o∈originalCandidates z.1.2,weight o ≤ M ∧ weight (o.getD []) ≤ M)
    (he : ∀ u∈profileBoxViews (matrixData z.1.1.1),
      ∀ v∈profileBoxViews (matrixData z.1.1.1),matrixEntryMeasure (z.1.1.1,(u,v)) ≤ M) :
    outerVectorMeasure z ≤ vectorMeasurePolynomial.eval M := by
  let mat := (M+1)^2*(4*M+7)
  let terminal := (M+1)*(8*M+8)
  let B := mat+terminal+6*M+2
  let os := originalCandidates z.1.2
  have hw : weight z.1.1 ≤ M := (weight_fst _).trans ((weight_fst _).trans hz)
  have hm : weight z.1.1.1 ≤ M := (weight_fst _).trans hw
  have hr : weight z.1.2 ≤ M := (weight_snd _).trans ((weight_fst _).trans hz)
  have hmat : profileMatrixMeasure z.1.1.1 ≤ mat := by
    have h := profileMatrixMeasure_le z.1.1.1 M M hm hv he
    exact h.trans (Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.add_le_add_right hN 1) 2)
      (by omega))
  have hlen : os.length ≤ M := (originalCandidates_length _).le.trans hO
  have hos : weight os ≤ M*(M+1)+1 :=
    (list_weight_bound os M (fun o ho' => (ho o ho').1)).trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)
  have hop (o : Option MatrixCode) (ho' : o∈os) : optionalTrialMeasure (z.1.1,o) ≤ B := by
    have hT := (ho o ho').2
    have how := (ho o ho').1
    have ht : terminalColumnMeasure (z.1.1.1,o.getD []) ≤ terminal :=
      terminalColumnMeasure_le _ M hm hT hN hv (fun v hv' => he v hv' v hv')
    change (z.1.1.2.1+profileMatrixMeasure z.1.1.1+weight z.1.1)+
      terminalColumnMeasure (z.1.1.1,o.getD [])+weight (z.1.1,o.getD [])+weight (z.1.1,o) ≤ B
    simp only [weight_prod]
    unfold B
    omega
  have hs := MeasuredMap.listMeasure_le optionalTrialMeasure z.1.1 os B hop
  have hmul := Nat.mul_le_mul_right B hlen
  have hpair : weight (z.1.1,os) ≤ 2+M+M*(M+1) := by
    simp only [weight_prod]
    omega
  change originalEnumerationMeasure z.1.2+
    MeasuredMap.listMeasure optionalTrialMeasure (z.1.1,os)+weight z.1+weight z ≤ _
  have hz1 : weight z.1 ≤ M := (weight_fst _).trans hz
  have horig : originalEnumerationMeasure z.1.2 ≤ 2*M := by
    unfold originalEnumerationMeasure
    omega
  simp only [vectorMeasurePolynomial,eval_add,eval_mul,eval_pow,eval_X,eval_one,eval_ofNat]
  change _ ≤ M*B+M*(M+1)+5*M+2
  omega

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_TabulationPreparationBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary sizes before finite tabulation begins -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

theorem tabulation_preparation_polynomial : ∃ p : Polynomial ℕ,∀ z,
    let M := p.eval (scheduledCountInputMeasure z)
    weight (scheduledOuterInput z) ≤ M ∧
    parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤ M ∧
    (∀ v∈profileBoxViews (initialCheck z.1),weight v ≤ M) ∧
    (∀ o∈originalCandidates z.1,weight o ≤ M ∧ weight (o.getD []) ≤ M) ∧
    (∀ u∈profileBoxViews (initialCheck z.1),∀ v∈profileBoxViews (initialCheck z.1),
      weight (scheduledMatrixParameters z,(u,v)) ≤ M) := by
  obtain ⟨a,ha⟩ := work_scheduledOuterInput
  obtain ⟨b,hb⟩ := schedule_numeric_polynomial
  obtain ⟨c,hc⟩ := polynomial_initialCheck
  obtain ⟨v,hv⟩ := profileBoxViews_point_polynomial
  obtain ⟨o,ho⟩ := originalCandidates_point_polynomial
  obtain ⟨t,ht⟩ := polynomial_optionalTrialInput
  let w := a+b+v.comp c+o+X+1
  let g := w+t.comp (1+2*w)+2+3*w
  refine ⟨g,?_⟩
  intro z
  let K := scheduledCountInputMeasure z
  have hz : weight z ≤ K := by unfold K scheduledCountInputMeasure; omega
  have hmargin : weight z.1 ≤ K := (weight_fst z).trans hz
  have houter : weight (scheduledOuterInput z) ≤ a.eval K :=
    (Nat.le_add_left _ _).trans (ha z)
  have hnum : parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤ b.eval K := hb z
  have hcheck : weight (initialCheck z.1) ≤ c.eval K :=
    (Nat.le_add_left _ _).trans ((hc z.1).trans (polynomial_eval_monotone c hmargin))
  have hview (u : List ℕ×List ℕ) (hu : u∈profileBoxViews (initialCheck z.1)) :
      weight u ≤ (v.comp c).eval K := by
    rw [eval_comp]
    exact (hv _ u hu).trans (polynomial_eval_monotone v hcheck)
  have horig (u : Option MatrixCode) (hu : u∈originalCandidates z.1) :
      weight u ≤ o.eval K := (ho _ u hu).trans (polynomial_eval_monotone o hmargin)
  have hwa : a.eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwb : b.eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwv : (v.comp c).eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwo : o.eval K ≤ w.eval K := by simp only [w,eval_add,eval_one,eval_X]; omega
  have hwg : w.eval K ≤ g.eval K := by simp only [g,eval_add,eval_mul,eval_ofNat]; omega
  have hwalk : weight (scheduledWalkInput z) ≤ w.eval K := by
    have hp : (scheduledOuterInput z).1.1=scheduledWalkInput z := rfl
    rw [←hp]
    exact ((weight_fst _).trans (weight_fst _)).trans (houter.trans hwa)
  refine ⟨(houter.trans hwa).trans hwg,(hnum.trans hwb).trans hwg,
    (fun u hu => ((hview u hu).trans hwv).trans hwg),?_,?_⟩
  · intro u hu
    have hou : weight u ≤ w.eval K := (horig u hu).trans hwo
    refine ⟨hou.trans hwg,?_⟩
    have hi : weight (scheduledWalkInput z,u) ≤ (1+2*w).eval K := by
      simp only [weight_prod,eval_add,eval_one,eval_mul,eval_ofNat]
      omega
    have hdef : weight (u.getD []) ≤ t.eval ((1+2*w).eval K) :=
      (weight_snd (optionalTrialInput (scheduledWalkInput z,u))).trans
        ((Nat.le_add_left _ _).trans ((ht _).trans (polynomial_eval_monotone t hi)))
    apply hdef.trans
    change t.eval ((1+2*w).eval K) ≤ g.eval K
    simp only [g,eval_add,eval_comp,eval_mul,eval_ofNat,eval_one]
    omega
  · intro u hu v' hv'
    have hu' := (hview u hu).trans hwv
    have hv'' := (hview v' hv').trans hwv
    have hm : weight (scheduledMatrixParameters z) ≤ w.eval K := by
      have hp : (scheduledWalkInput z).1=scheduledMatrixParameters z := rfl
      rw [←hp]
      exact (weight_fst _).trans hwalk
    change weight (scheduledMatrixParameters z,(u,v')) ≤ g.eval K
    simp only [weight_prod,g,eval_add,eval_mul,eval_ofNat]
    omega

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactEntryBoxBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual transition-cache boxes in the exact sampler -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

attribute [local irreducible] unaryMarkers parameterProposalWidth scheduledCacheParameters
  residualParameters canonicalCountInput

private lemma proposalBox_eq (z : SamplingParameters) (u v : List ℕ×List ℕ) :
    gridStateCount ((scheduledMatrixParameters z,(u,v)).1.2,2)=2^(parameterProposalWidth z) := by
  have hm : (scheduledMatrixParameters z,(u,v)).1.2=unaryMarkers (parameterProposalWidth z) := by
    unfold scheduledMatrixParameters
    rfl
  rw [hm,gridStateCount_eq,unaryMarkers_length]

theorem exact_entry_box_bound : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    ∀ u∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn c)),
    ∀ v∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn c)),
    matrixEntryBox (scheduledMatrixParameters (exactSamplingParameters (List.ofFn r,List.ofFn c)),(u,v)) ≤
      p.eval (Algorithms.samplingSize n r 0)*exactBoxScale r c := by
  obtain ⟨a,ha⟩ := exact_count_input_measure_polynomial
  obtain ⟨b,hb⟩ := tabulation_preparation_polynomial
  obtain ⟨p,hp⟩ := matrixEntryBox_bound
  let A := b.comp a
  refine ⟨p.comp A+A+4,?_⟩
  intro m n r c htotal u hu v hv
  let z := exactSamplingParameters (List.ofFn r,List.ofFn c)
  let e : MatrixEntryInput := (scheduledMatrixParameters z,(u,v))
  let V := candidateData (initialCheck (List.ofFn r,List.ofFn c),u)
  let dim := dimensionAllowance (I := Fin m) (J := Fin n)
  let bits := smallBinaryLength r c
  let S := Algorithms.samplingSize n r 0
  let E := exactBoxScale r c
  have hd : 1 ≤ dim := by unfold dim dimensionAllowance; omega
  have hbits : 1 ≤ bits := hd.trans (smallBinaryLength_parameters r c).2.1
  have h23 : dim^2 ≤ dim^3 := Nat.pow_le_pow_right hd (by decide)
  have he : 1 ≤ E := exactBoxScale_pos r c
  have hdim : parameterDimension z=dim := by
    change marginDimension (List.ofFn r,List.ofFn c)=dim
    exact marginDimension_ofFn r c
  have hVrow : V.1.2.1=List.ofFn r := rfl
  have hVcol : V.1.2.2=List.ofFn c := rfl
  have hres : entryResidualParameters e=residualParameters ((V,dim^12),(dim,parameterAccuracy z)) := by
    unfold entryResidualParameters
    dsimp only [e,entryCacheParameters,sourceData,scheduledMatrixParameters,scheduledCacheParameters,matrixData]
    unfold scheduledCacheParameters
    dsimp only
    rw [show z.1=(List.ofFn r,List.ofFn c) from rfl,marginPadding_ofFn,hdim]
  have hnorm := normalized_profile_completion_count r c V hVrow hVcol (parameterAccuracy z)
  have hdense := normalized_profile_dense_grid r c V hVrow hVcol (parameterAccuracy z)
  have horig : gridStateCount (completionEnumerationData (entryResidualParameters e).1) ≤ E := by
    rw [hres]
    unfold residualParameters
    have hh := arbitrary_profile_completion_count r c V hVrow hVcol
    apply hh.trans
    apply Nat.pow_le_pow_right (by decide)
    have hmul : dim^2*bits ≤ dim^3*bits := Nat.mul_le_mul_right bits h23
    change 4*(dim^2*bits) ≤ 40*(dim^3*bits)
    omega
  have hprop : gridStateCount (e.1.2,2) ≤ E := by
    rw [proposalBox_eq z u v,parameterProposalWidth,hdim]
    apply Nat.pow_le_pow_right (by decide)
    have hc : Nat.clog 2 (32*dim^2) ≤ 32*dim^2 :=
      Nat.clog_le_of_le_pow (Nat.le_of_lt Nat.lt_two_pow_self)
    have hmul : dim^3 ≤ dim^3*bits := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (dim^3) hbits
    exact hc.trans (by change 32*dim^2 ≤ 40*(dim^3*bits); nlinarith)
  have hprepare := hb z
  have hnum : parameterDimension z+parameterAccuracy z+parameterCompletionWidth z ≤ A.eval S :=
    hprepare.2.1.trans (by simp only [A,eval_comp]; exact polynomial_eval_monotone b (ha m n r c htotal))
  have hw : weight e ≤ A.eval S := (hprepare.2.2.2.2 u hu v hv).trans (by
    simp only [A,eval_comp]; exact polynomial_eval_monotone b (ha m n r c htotal))
  have hpoly : p.eval (weight e) ≤ p.eval (A.eval S) := polynomial_eval_monotone p hw
  have hbound := hp e
  dsimp only at hbound
  have hn : gridStateCount (completionEnumerationData (canonicalCountInput (entryResidualParameters e)).1.1) ≤ E := by
    rw [hres]
    exact hnorm
  have hg : (4*(canonicalCountInput (entryResidualParameters e)).1.2.1^8)^
      tabulationDimension (canonicalCountInput (entryResidualParameters e)).1 ≤ E := by
    rw [hres]
    exact hdense
  change matrixEntryBox e ≤ _
  have hrs : (entryResidualParameters e).2=(parameterDimension z,parameterAccuracy z) := by
    rw [hres]
    unfold residualParameters
    rw [hdim]
  have hcache : (entryCacheParameters e).2=parameterCompletionWidth z := by
    unfold e entryCacheParameters scheduledMatrixParameters
    unfold scheduledCacheParameters
    rfl
  have hnum' : (entryResidualParameters e).2.1+(entryResidualParameters e).2.2+
      (entryCacheParameters e).2 ≤ A.eval S := by
    rw [hrs,hcache]
    exact hnum
  have hfirst : matrixEntryBox e ≤ 4*E+A.eval S+p.eval (A.eval S) := by
    omega
  apply hfirst.trans
  have hA : A.eval S ≤ A.eval S*E := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (A.eval S) he
  have hpA : p.eval (A.eval S) ≤ p.eval (A.eval S)*E := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (p.eval (A.eval S)) he
  simp only [eval_add,eval_comp,eval_ofNat]
  nlinarith

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactRareMeasureBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A single exponential scale for the executed rare-branch measure -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

lemma originalEnumeration_scale {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn c)) ≤ exactBoxScale r c := by
  apply (originalEnumeration_count_bound r c).trans
  have hd : 1 ≤ dimensionAllowance (I := Fin m) (J := Fin n) := by unfold dimensionAllowance; omega
  have hp := Nat.le_self_pow (by decide : 3 ≠ 0) (dimensionAllowance (I := Fin m) (J := Fin n))
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

lemma initialProfile_scale {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) :
    gridStateCount (profileEnumerationData (initialCheck (List.ofFn r,List.ofFn c))) ≤ exactBoxScale r c := by
  rw [initialCheck_code r c htotal]
  apply (profileEnumeration_count_bound r c _ _).trans
  have hp := Nat.le_self_pow (by decide : 3 ≠ 0) (dimensionAllowance (I := Fin m) (J := Fin n))
  apply Nat.pow_le_pow_right (by decide)
  nlinarith

theorem exact_rare_measure_bound_oai : ∃ p a : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    exactRareMeasure (List.ofFn r,List.ofFn c) ≤
      p.eval (a.eval (Algorithms.samplingSize n r 0)*exactBoxScale r c) := by
  obtain ⟨a,ha⟩ := exact_count_input_measure_polynomial
  obtain ⟨b,hb⟩ := tabulation_preparation_polynomial
  obtain ⟨c,hc⟩ := exact_entry_box_bound
  obtain ⟨d,hd⟩ := exact_parameter_polynomial
  obtain ⟨e,he⟩ := work_exactResidualInput
  obtain ⟨q,hq⟩ := matrixEntryMeasure_polynomial
  let base : Polynomial ℕ := a+b.comp a+c+d+e.comp d+1
  let Q : Polynomial ℕ := q+X
  refine ⟨8*X+2*vectorMeasurePolynomial.comp Q,base,?_⟩
  intro m n r cols htotal
  let z := exactSamplingParameters (List.ofFn r,List.ofFn cols)
  let E := exactBoxScale r cols
  let S := Algorithms.samplingSize n r 0
  let W := base.eval S*E
  let M := Q.eval W
  have hE : 1 ≤ E := exactBoxScale_pos r cols
  have hbase : 1 ≤ base.eval S := by simp only [base,eval_add,eval_one]; omega
  have hEW : E ≤ W := by simpa only [Nat.one_mul] using Nat.mul_le_mul_right E hbase
  have hbaseW : base.eval S ≤ W := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (base.eval S) hE
  have hWM : W ≤ M := by unfold M Q; simp only [eval_add,eval_X]; omega
  have haW : a.eval S ≤ W := (by simp only [base,eval_add,eval_one]; omega : a.eval S ≤ base.eval S).trans hbaseW
  have hbW : (b.comp a).eval S ≤ W :=
    (by simp only [base,eval_add,eval_one]; omega : (b.comp a).eval S ≤ base.eval S).trans hbaseW
  have hcW : c.eval S*E ≤ W := Nat.mul_le_mul_right E (by simp only [base,eval_add,eval_one]; omega)
  have hdW : d.eval S ≤ W := (by simp only [base,eval_add,eval_one]; omega : d.eval S ≤ base.eval S).trans hbaseW
  have heW : (e.comp d).eval S ≤ W :=
    (by simp only [base,eval_add,eval_one]; omega : (e.comp d).eval S ≤ base.eval S).trans hbaseW
  have hcount : scheduledCountInputMeasure z ≤ W := (ha m n r cols htotal).trans haW
  have hparam : exactParameterMeasure (List.ofFn r,List.ofFn cols) ≤ W := (hd m n r cols htotal).trans hdW
  have hres : weight (exactResidualInput (List.ofFn r,List.ofFn cols)) ≤ W := by
    have ht : weight (exactResidualInput (List.ofFn r,List.ofFn cols)) ≤
        e.eval (d.eval S) :=
      (Nat.le_add_left _ _).trans ((he _).trans (polynomial_eval_monotone e (hd m n r cols htotal)))
    exact ht.trans (by simpa only [eval_comp] using heW)
  have hz : weight (List.ofFn r,List.ofFn cols) ≤ W := by
    have hz' : weight z ≤ scheduledCountInputMeasure z := by
      simpa only [eval_X] using weight_le_scheduledCountInputMeasure z
    exact ((weight_fst z).trans hz').trans hcount
  have hprep := hb z
  have hprep_bound : b.eval (scheduledCountInputMeasure z) ≤ W :=
    (polynomial_eval_monotone b (ha m n r cols htotal)).trans (by simpa only [eval_comp] using hbW)
  have houter : weight (scheduledOuterInput z) ≤ M := (hprep.1.trans hprep_bound).trans hWM
  have hN : gridStateCount (profileEnumerationData (initialCheck (List.ofFn r,List.ofFn cols))) ≤ M :=
    (initialProfile_scale r cols htotal).trans (hEW.trans hWM)
  have hO : gridStateCount (originalEnumerationData (List.ofFn r,List.ofFn cols)) ≤ W :=
    (originalEnumeration_scale r cols).trans hEW
  have hv : ∀ v∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn cols)),weight v ≤ M := by
    intro v hv
    exact ((hprep.2.2.1 v hv).trans hprep_bound).trans hWM
  have ho : ∀ o∈originalCandidates (List.ofFn r,List.ofFn cols),weight o ≤ M ∧ weight (o.getD []) ≤ M := by
    intro o ho
    exact ⟨((hprep.2.2.2.1 o ho).1.trans hprep_bound).trans hWM,
      ((hprep.2.2.2.1 o ho).2.trans hprep_bound).trans hWM⟩
  have hentry : ∀ u∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn cols)),
      ∀ v∈profileBoxViews (initialCheck (List.ofFn r,List.ofFn cols)),
      matrixEntryMeasure (scheduledMatrixParameters z,(u,v)) ≤ M := by
    intro u hu v hv
    have hx := (hc m n r cols htotal u hu v hv).trans hcW
    have ht := (hq (scheduledMatrixParameters z,(u,v))).trans (polynomial_eval_monotone q hx)
    apply ht.trans
    unfold M Q
    simp only [eval_add,eval_X]
    omega
  have hsteps : parameterSteps z ≤ M := by
    have hs : parameterSteps z ≤ scheduledCountInputMeasure z := by unfold scheduledCountInputMeasure; omega
    exact hs.trans (hcount.trans hWM)
  have hvector : outerVectorMeasure (scheduledOuterInput z) ≤ vectorMeasurePolynomial.eval M :=
    outerVectorMeasure_bound _ M houter hsteps (hO.trans hWM) hN hv ho hentry
  have hunit := (unit_outerVectorMeasure_le (scheduledOuterInput z)).trans hvector
  have hen : originalEnumerationMeasure (List.ofFn r,List.ofFn cols) ≤ 2*W := by
    unfold originalEnumerationMeasure
    omega
  change _ ≤ (8*X+2*vectorMeasurePolynomial.comp Q).eval W
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_comp]
  change exactParameterMeasure (List.ofFn r,List.ofFn cols)+
    (scheduledCountInputMeasure z+outerVectorMeasure (scheduledOuterInput z)+
      UnitCountPrograms.outerVectorMeasure (scheduledOuterInput z)+
      originalEnumerationMeasure (List.ofFn r,List.ofFn cols)+
      weight (exactResidualInput (List.ofFn r,List.ofFn cols)))+
    originalEnumerationMeasure (List.ofFn r,List.ofFn cols)+weight (List.ofFn r,List.ofFn cols) ≤ _
  change _ ≤ 8*W+2*vectorMeasurePolynomial.eval M
  omega

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound_oai := @OAI.ContingencyTables.SmallGraphProfiles.exact_rare_measure_bound_oai
