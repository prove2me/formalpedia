-- Prove2me | solution 1 for OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:09:07.284063+00:00
-- url     : https://prove2.me/submissions/6b86d6b6-c70f-4dd3-8979-5bff6c8f6b43

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A006
import Definitions.Def_OAIQ089A010
import Theorems.Thm_OAI_ContingencyTables_CompanionObservedUpdateProgram_polynomial_output
import Theorems.Thm_OAI_ContingencyTables_RootedEstimatorMedianProgram_polynomial_output

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

end ContingencyTables.ProfilePrograms

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

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_BinaryExchangeProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial enumeration of exchanges of a binary profile

The program scans at most the square of the list length. It retains only
an absent receiving coordinate and a present donating coordinate, so every
retained natural-number update is again a binary profile.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial
open scoped BigOperators Classical

theorem polynomial_binaryExchangeTest : PolynomialTime binaryExchangeTestRealizer := by
  unfold binaryExchangeTestRealizer
  apply polynomial_congr
  apply polynomial_choose
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast 0))
      (polynomial_constant 0)) polynomial_natEqual
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0))
      (polynomial_constant 1)) polynomial_natEqual
  · exact polynomial_constant false

theorem polynomial_binaryExchangeIndices : PolynomialTime binaryExchangeIndicesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_binaryExchangeTest)

theorem polynomial_binaryExchanges : PolynomialTime binaryExchangesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_binaryExchangeIndices)
    (polynomial_mapWith polynomial_listExchange)

end ContingencyTables.ProfilePrograms

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
end MatchingFPRAS.TreeFraction

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ListWordProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the finite-list proposal

The list is scanned only up to its own length. A binary index beyond the
end produces `none`; its numerical magnitude never determines a loop bound.
-/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {A : Type} [Codec A] [Inhabited A]

theorem polynomial_getOptionFast : PolynomialTime (getOptionFast (A := A)) := by
  unfold getOptionFast
  exact polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_listLength)) polynomial_less)
    (polynomial_composition (polynomial_getDFast default) polynomial_some)
    (polynomial_constant none))

theorem polynomial_listWordChoice : PolynomialTime (listWordChoiceRealizer (A := A)) :=
  polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_bitValue))
    polynomial_getOptionFast

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallPatternProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial tests for the two allowed small-profile patterns -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_pairSum : PolynomialTime pairSumRealizer := by
  unfold pairSumRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_second) (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second) (polynomial_getDFast 0))) polynomial_add

lemma polynomial_indexIndicator : PolynomialTime indexIndicator := by
  unfold indexIndicator
  exact polynomial_congr _ (polynomial_choose polynomial_natEqual
    (polynomial_constant 1) (polynomial_constant 0))

lemma polynomial_patternIndices : PolynomialTime patternIndices := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength) X
  intro z
  have hw : weight z.1.1≤weight z := by
    rcases z with ⟨⟨xs,ys⟩,U⟩
    simp only [weight_prod]
    omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.1).trans hw

lemma polynomial_balancedAt : PolynomialTime balancedAtRealizer :=
  polynomial_composition (polynomial_pair polynomial_pairSum
    (polynomial_composition polynomial_first polynomial_second)) polynomial_natEqual

lemma polynomial_balancedTest : PolynomialTime balancedTestRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_patternIndices)
    (polynomial_mapWith polynomial_balancedAt)) polynomial_all)

lemma polynomial_defectAt : PolynomialTime defectAtRealizer := by
  unfold defectAtRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_pairSum)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
        polynomial_indexIndicator)) polynomial_add)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
        polynomial_indexIndicator)) polynomial_add)) polynomial_natEqual

lemma polynomial_defectTest : PolynomialTime defectTestRealizer := by
  unfold defectTestRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_natEqual) polynomial_boolNot)
    (polynomial_composition (polynomial_composition
      (polynomial_pair polynomial_identity (polynomial_composition polynomial_first polynomial_patternIndices))
      (polynomial_mapWith polynomial_defectAt)) polynomial_all)) polynomial_boolAnd)

theorem polynomial_patternTest : PolynomialTime patternTestRealizer := by
  unfold patternTestRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair polynomial_balancedTest
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first)
        (polynomial_composition polynomial_first polynomial_first)) polynomial_cellPairs))
      (polynomial_mapWith polynomial_defectTest)) polynomial_any)) polynomial_boolOr)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionChainValidator
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial validation of paired binary states

The bounded-profile arithmetic test specializes to width one.
Thus the companion's state filter is a concrete list program on the two
coordinates of every labelled pair.
-/

namespace ContingencyTables.CompanionChainValidator
open CommonBasesFPRAS TwoLiftStates ProfilePrograms
open MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma polynomial_pairFirstLookup : PolynomialTime pairFirstLookup :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast 0)

lemma polynomial_pairSecondLookup : PolynomialTime pairSecondLookup :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)

theorem polynomial_pairedStateTest : PolynomialTime pairedStateTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_mapWith polynomial_pairFirstLookup))
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      (polynomial_mapWith polynomial_pairSecondLookup))) (polynomial_constant 1)) polynomial_patternTest

end ContingencyTables.CompanionChainValidator

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionNeighborProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable valid-neighbor lists and their binary draw

This composes the actual integer-exchange program with the paired-state
validator and the bounded list-index program. The output code is exactly
the encoding of the semantic proposal, including its failure outcome.
-/

namespace ContingencyTables.CompanionNeighborProgram
open CompanionChainValidator CompanionArithmeticProposal CompanionFactorialApplication
open CompanionBooleanPhase ProfilePrograms MatchingFPRAS.TreeTyped
open CommonBasesFPRAS
open scoped BigOperators Classical

theorem polynomial_validExchanges : PolynomialTime validExchangesRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_binaryExchanges))
    (polynomial_filterWith polynomial_pairedStateTest)

/-- All loops traverse the supplied profile, pair catalog or quadratic
coordinate list. A large binary draw index never determines a loop. -/
theorem polynomial_codeProposal : PolynomialTime codeProposalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_validExchanges) polynomial_second)
    polynomial_listWordChoice

end ContingencyTables.CompanionNeighborProgram

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

omit [Codec B] [Codec C] in
lemma polynomial_boundedFactorial {f : A → ℕ} {F : Realizer f} (hF : PolynomialTime F)
    (p : Polynomial ℕ) (hn : ∀ a,f a≤p.eval (weight a)) : PolynomialTime (composition F factorial) :=
  work_composition hF factorial_numeric_work p hn
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCellCatalogProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

end ContingencyTables.CompanionCellCatalog

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedCatalogProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing paired-coordinate metadata from a binary profile

Consecutive coordinates are paired by the bounded list scan
(0,1),(2,3),.... This is the exact metadata of the canonical paired-label
order, rather than a catalog supplied as an external oracle.
-/

namespace ContingencyTables.PairedCatalogProgram

open MatchingFPRAS.TreeTyped ProfilePrograms

lemma polynomial_indexPair : PolynomialTime indexPairRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
      polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
        polynomial_multiply) (polynomial_constant 1)) polynomial_add)

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
      polynomial_quotient) Polynomial.X
  intro xs
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (Nat.div_le_self xs.length 2).trans (list_length_le_weight xs)

theorem polynomial_catalog : PolynomialTime catalogRealizer :=
  polynomial_composition polynomial_indices (polynomial_map polynomial_indexPair)

end ContingencyTables.PairedCatalogProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The companion proposal with computed metadata

The executable proposal receives only a binary profile and fresh bits.
It computes the consecutive-pair catalog itself and scans coordinate
exchanges. Its semantic law is the same ordered proposal law.
-/

namespace ContingencyTables.CompanionComputedProposal

open MatchingFPRAS.TreeTyped CompanionFactorialApplication CompanionComputedInitial
open CompanionArithmeticProposal CompanionOrderedProposal CompanionNeighborProgram
open CompanionBooleanPhase
open scoped Classical

theorem polynomial_proposalProgram : PolynomialTime proposalProgramRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first PairedCatalogProgram.polynomial_catalog)
    polynomial_first) polynomial_second) polynomial_codeProposal

end ContingencyTables.CompanionComputedProposal

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseCounts
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable counts in an outer counting phase

The stored trajectory is scanned directly. Both the transversal count
and each labelled defect count use the actual polynomial occupancy
tests. No set-state enumeration is performed.
-/

namespace ContingencyTables.CompanionPhaseCounts

open MatchingFPRAS.TreeTyped ProfilePrograms CompanionChainValidator
open CompanionTraceProgram CompanionOrderedProposal CompanionArithmeticProposal
open CompanionFactorialApplication CompanionBooleanPhase
open CommonBasesFPRAS TwoLiftStates
open scoped Classical

theorem polynomial_pairedDefectTest : PolynomialTime pairedDefectTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_first polynomial_first))
      (polynomial_mapWith polynomial_pairFirstLookup))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_first polynomial_first))
      (polynomial_mapWith polynomial_pairSecondLookup))) (polynomial_constant 1))
    polynomial_second) polynomial_defectTest

end ContingencyTables.CompanionPhaseCounts

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMultiplierMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The full multiplier update and abort test as list programs

Only the polynomial list of labelled pairs is traversed. Every matrix
entry is updated from the actual plain and defect counts of the stored
trajectory. The count check includes every off-diagonal labelled type.
-/

namespace ContingencyTables.CompanionMultiplierMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionPhaseCounts CompanionMultiplierProgram CompanionOrderedProposal CompanionTraceProgram
open CompanionFactorialApplication CompanionArithmeticProposal CompanionRationalUpdates
open CommonBasesFPRAS
open scoped Classical

lemma polynomial_readEntry : PolynomialTime readEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast (0,1))

end ContingencyTables.CompanionMultiplierMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStateMultiplierProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the multiplier of an actual encoded chain state

The at most quadratic list of labelled defect types is searched using
the proved occupancy test. Uniqueness of defect labels identifies the
selected matrix entry with the mathematical chain multiplier.
-/

namespace ContingencyTables.CompanionStateMultiplierProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms
open CompanionChainValidator CompanionPhaseCounts CompanionMultiplierMatrixProgram

lemma polynomial_coordinates : PolynomialTime coordinatesRealizer :=
  polynomial_composition polynomial_first (polynomial_map polynomial_first)

lemma polynomial_candidates : PolynomialTime candidatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_coordinates polynomial_coordinates) polynomial_cellPairs

lemma polynomial_found : PolynomialTime foundRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_candidates)
    (polynomial_filterWith polynomial_pairedDefectTest)

lemma polynomial_noDefect : PolynomialTime noDefectRealizer :=
  polynomial_composition (polynomial_composition polynomial_second polynomial_found) polynomial_isEmpty

lemma polynomial_readDefect : PolynomialTime readDefectRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_found) (polynomial_constant 0))
      (polynomial_getDFast (0,0)))) polynomial_readEntry

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_choose polynomial_noDefect (polynomial_constant (1,1)) polynomial_readDefect

end ContingencyTables.CompanionStateMultiplierProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixSubtractProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Entrywise natural subtraction on a supplied matrix shape -/

namespace ContingencyTables.MatrixSubtractProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

lemma polynomial_entry : PolynomialTime entryRealizer := by
  unfold entryRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_first)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_matrixEntry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second)
      (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
        polynomial_second)) polynomial_matrixEntry)) polynomial_subtract

lemma polynomial_sourceRow : PolynomialTime sourceRowRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_getDFast [])

lemma polynomial_columns : PolynomialTime columnsRealizer := by
  apply polynomial_composition polynomial_sourceRow
  apply polynomial_boundedRange polynomial_listLength X
  intro xs
  simpa only [eval_X] using list_length_le_weight xs

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_entry)

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

theorem polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_row)

end ContingencyTables.MatrixSubtractProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_SparseViewMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Materializing a sparse retained-cell view in a rectangular matrix -/

namespace ContingencyTables.SparseViewMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial ProfilePrograms DensePrograms

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_lookupView

lemma polynomial_columns : PolynomialTime columnsRealizer := by
  apply polynomial_boundedRange (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.1.2).trans
    ((weight_snd z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_columns)
    (polynomial_mapWith polynomial_entry)

lemma polynomial_rowIndices : PolynomialTime rowIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))

theorem polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_rowIndices)
    (polynomial_mapWith polynomial_row)

end ContingencyTables.SparseViewMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionAcceptanceProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of the rational acceptance coin

The integer quotient computes the exact floor threshold used by the
finite-word acceptance law. The word length controls all powering and
word traversal, even for malformed fraction inputs.
-/

namespace ContingencyTables.FractionAcceptanceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

lemma polynomial_scaledNumerator : PolynomialTime scaledNumeratorRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_bitDenominator)) polynomial_multiply

lemma polynomial_threshold : PolynomialTime thresholdRealizer :=
  polynomial_composition (polynomial_pair polynomial_scaledNumerator
    (polynomial_composition polynomial_first polynomial_second)) polynomial_quotient

theorem polynomial_acceptCode : PolynomialTime acceptCodeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_bitValue)
    polynomial_threshold) polynomial_less

end ContingencyTables.FractionAcceptanceProgram

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

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange polynomial_listLength Polynomial.X
  intro xs
  simpa only [Polynomial.eval_X] using list_length_le_weight xs

open CompanionFactorialApplication RootedCompletion ForestAssignmentSplit

end ContingencyTables.RootedTreeInputProgram

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_NaturalBlockProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded scans of natural-number blocks

Numeric widths select bounded slices of the supplied list. They never
control an allocation, so malformed widths preserve polynomial cost.
-/

namespace ContingencyTables.NaturalBlockProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_start : PolynomialTime startRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_takeFast) polynomial_listSum

lemma polynomial_block : PolynomialTime blockRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_start)
      polynomial_dropFast)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))) polynomial_takeFast

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

theorem polynomial_blocks : PolynomialTime blocksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_block)

end ContingencyTables.NaturalBlockProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedProfileProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reading the two cell counts from the actual paired code

The block widths come from the stored capacity list. Each count scans
only supplied code entries and clips them to one, including on malformed
input. No numeric capacity controls an unbounded allocation.
-/

namespace ContingencyTables.PairedProfileProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_sideValue : PolynomialTime sideValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_choose (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition polynomial_second polynomial_second)
        (polynomial_composition polynomial_second polynomial_first))) (polynomial_getDFast 0))
    (polynomial_constant 1)) polynomial_minimum

lemma polynomial_sideEntries : PolynomialTime sideEntriesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first PairedCatalogProgram.polynomial_catalog))
    (polynomial_mapWith polynomial_sideValue)

lemma polynomial_sideCount : PolynomialTime sideCountRealizer :=
  polynomial_composition polynomial_sideEntries polynomial_listSum

lemma sideCount_le (xs : List ℕ) (side : Bool) : sideCount (xs,side) ≤ xs.length := by
  have hs : (sideEntries (xs,side)).sum ≤ (sideEntries (xs,side)).length := by
    simpa using (List.sum_le_card_nsmul (sideEntries (xs,side)) 1 (by
      intro a ha
      obtain ⟨p,_,rfl⟩ := List.mem_map.mp ha
      exact Nat.min_le_right _ _))
  exact hs.trans (by
    simp only [sideEntries,PairedCatalogProgram.catalog,List.length_map,List.length_range]
    exact Nat.div_le_self _ _)

lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
    polynomial_multiply

lemma polynomial_rows : PolynomialTime rowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_map polynomial_width)) polynomial_second)
    NaturalBlockProgram.polynomial_blocks

lemma polynomial_counts : PolynomialTime countsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
      polynomial_sideCount)
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant true))
      polynomial_sideCount)

theorem polynomial_profileRows : PolynomialTime profileRowsRealizer :=
  polynomial_composition polynomial_rows (polynomial_map polynomial_counts)

end ContingencyTables.PairedProfileProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedDemandProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Replacing the oracle demand by the current encoded paired state

Only the retained-cell catalog and the supplied state are scanned. The
large cells receive zero in each sparse view and hence retain their full
capacity in the complemented column demand.
-/

namespace ContingencyTables.PairedDemandProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_cellInput : PolynomialTime cellInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_second) (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)

lemma polynomial_cells : PolynomialTime cellsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_cellInput

lemma polynomial_counts : PolynomialTime countsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_cells CompanionCellCatalog.polynomial_capacities)
    polynomial_second) PairedProfileProgram.polynomial_profileRows

lemma polynomial_sideEntry : PolynomialTime sideEntryRealizer :=
  polynomial_choose polynomial_first
    (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition polynomial_second polynomial_first)

lemma polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_counts))
    (polynomial_mapWith polynomial_sideEntry)

lemma polynomial_viewInput : PolynomialTime viewInputRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
        polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_cells)
      CompanionCellCatalog.polynomial_catalog) polynomial_values)

lemma polynomial_viewMatrix : PolynomialTime viewMatrixRealizer :=
  polynomial_composition polynomial_viewInput SparseViewMatrixProgram.polynomial_matrix

lemma polynomial_complement : PolynomialTime complementRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant true))
      polynomial_viewMatrix)) MatrixSubtractProgram.polynomial_matrix

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_pair (polynomial_composition
        (polynomial_pair polynomial_identity (polynomial_constant false)) polynomial_viewMatrix)
        polynomial_complement))

end ContingencyTables.PairedDemandProgram

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_PairedFactorialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact factorial multiplier from the encoded paired state

Every factorial argument is bounded by the supplied code length. In a
valid code each cell block has length twice its capacity, so the computed
denominator is exactly the manuscript's capacity factorial.
-/

namespace ContingencyTables.PairedFactorialProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial PairedProfileProgram
open scoped BigOperators Classical

lemma polynomial_sideFactor : PolynomialTime sideFactorRealizer := by
  apply polynomial_boundedFactorial polynomial_sideCount X
  intro z
  simpa only [eval_X] using (sideCount_le z.1 z.2).trans
    ((list_length_le_weight z.1).trans (weight_fst z))

lemma polynomial_pairCount : PolynomialTime pairCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
    polynomial_quotient

lemma polynomial_denominator : PolynomialTime denominatorRealizer := by
  apply polynomial_boundedFactorial polynomial_pairCount X
  intro xs
  simpa only [eval_X,pairCount] using (Nat.div_le_self xs.length 2).trans (list_length_le_weight xs)

lemma polynomial_numerator : PolynomialTime numeratorRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
      polynomial_sideFactor)
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant true))
      polynomial_sideFactor)) polynomial_multiply

lemma polynomial_rowRatio : PolynomialTime rowRatioRealizer :=
  polynomial_composition (polynomial_pair polynomial_numerator polynomial_denominator)
    TreeFraction.polynomial_normalize

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_composition polynomial_rows
    (polynomial_map polynomial_rowRatio)) FractionAggregateProgram.polynomial_product

end ContingencyTables.PairedFactorialProgram

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

end ContingencyTables.BinVectorProgram

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

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary

end ContingencyTables.RootedBinFramesProgram

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

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary FirstSuccess ResidualMixture

end ContingencyTables.RootedOracleWalkProgram

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

attribute [local irreducible] rangeValue rangeValues

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedLabelWeightProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed weight oracle at a current paired state

The immutable schedule and graph are shared. Each call reconstructs the
two small-cell views from its actual state, runs the independent median
estimator, and multiplies by the exact factorial ratio.
-/

namespace ContingencyTables.RootedLabelWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open RootedEstimatorLayoutProgram

lemma polynomial_replaceState : PolynomialTime replaceStateRealizer := by
  unfold replaceStateRealizer
  exact polynomial_pair
    (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition
          (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition
            (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
          polynomial_second) PairedDemandProgram.polynomial_output)))
    (polynomial_composition polynomial_first polynomial_second)

lemma polynomial_stateInput : PolynomialTime stateInputRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)

lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_pair (polynomial_composition polynomial_stateInput polynomial_replaceState)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)

lemma polynomial_medianInput : PolynomialTime medianInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_context
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition polynomial_second polynomial_second))

lemma polynomial_demandInput : PolynomialTime demandInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_stateInput
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
    (polynomial_composition polynomial_second polynomial_first)

lemma polynomial_factorialInput : PolynomialTime factorialInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_demandInput
    (polynomial_composition PairedDemandProgram.polynomial_cells CompanionCellCatalog.polynomial_capacities))
    (polynomial_composition polynomial_second polynomial_first)

attribute [local irreducible] medianInput factorialInput

lemma polynomial_medianResult : PolynomialTime medianResultRealizer :=
  polynomial_composition polynomial_medianInput RootedEstimatorMedianProgram.polynomial_output

lemma polynomial_factorialResult : PolynomialTime factorialResultRealizer :=
  polynomial_composition polynomial_factorialInput PairedFactorialProgram.polynomial_output

attribute [local irreducible] medianResult factorialResult

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_medianResult polynomial_factorialResult) TreeFraction.polynomial_mul

end ContingencyTables.RootedLabelWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionEvaluatedWeightProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The executed multiplier times labelled weight

Both factors are computed from the supplied current state. The matrix
lookup and the oracle consume no hidden finite-state enumeration.
-/

namespace ContingencyTables.CompanionEvaluatedWeightProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

lemma polynomial_multiplierInput : PolynomialTime multiplierInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      PairedCatalogProgram.polynomial_catalog) (polynomial_composition polynomial_first polynomial_second))

lemma polynomial_multiplier : PolynomialTime multiplierRealizer :=
  polynomial_composition polynomial_multiplierInput CompanionStateMultiplierProgram.polynomial_output

lemma polynomial_weightInput : PolynomialTime weightInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second)

attribute [local irreducible] weightInput RootedLabelWeightProgram.output

lemma polynomial_weight : PolynomialTime weightRealizer :=
  polynomial_composition polynomial_weightInput RootedLabelWeightProgram.polynomial_output

attribute [local irreducible] multiplier weight

lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_multiplier polynomial_weight) TreeFraction.polynomial_mul

attribute [local irreducible] output

end ContingencyTables.CompanionEvaluatedWeightProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FractionMetropolisProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Clipped rational Metropolis acceptance as a binary program -/

namespace ContingencyTables.FractionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_ratio : PolynomialTime ratioRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_first polynomial_first)) TreeFraction.polynomial_div

lemma polynomial_belowOne : PolynomialTime belowOneRealizer :=
  polynomial_composition (polynomial_pair polynomial_ratio (polynomial_constant _)) TreeFraction.polynomial_less

lemma polynomial_probability : PolynomialTime probabilityRealizer :=
  polynomial_choose polynomial_belowOne polynomial_ratio (polynomial_constant _)

attribute [local irreducible] probability

lemma polynomial_accept : PolynomialTime acceptRealizer :=
  polynomial_composition (polynomial_pair polynomial_probability polynomial_second)
    FractionAcceptanceProgram.polynomial_acceptCode

end ContingencyTables.FractionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One physical companion-chain step with independent word fields

The proposed state is computed by the quadratic arithmetic candidate
list. Two disjoint words evaluate the current and candidate states, and
a third field supplies the rational acceptance coin.
-/

namespace ContingencyTables.CompanionMetropolisProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_proposed : PolynomialTime proposedRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first))
    CompanionComputedProposal.polynomial_proposalProgram

private lemma polynomial_defaultCode : PolynomialTime defaultCodeRealizer := by
  unfold defaultCodeRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    polynomial_proposed) polynomial_defaultCode

attribute [local irreducible] candidate

lemma polynomial_currentInput : PolynomialTime currentInputRealizer :=
  polynomial_pair polynomial_first (polynomial_composition
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_second polynomial_second) polynomial_second) polynomial_first) polynomial_first)

lemma polynomial_targetInput : PolynomialTime targetInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_candidate)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_second) polynomial_first) polynomial_second)

attribute [local irreducible] currentInput targetInput CompanionEvaluatedWeightProgram.output

lemma polynomial_currentValue : PolynomialTime currentValueRealizer :=
  polynomial_composition polynomial_currentInput CompanionEvaluatedWeightProgram.polynomial_output

lemma polynomial_targetValue : PolynomialTime targetValueRealizer :=
  polynomial_composition polynomial_targetInput CompanionEvaluatedWeightProgram.polynomial_output

attribute [local irreducible] currentValue targetValue

lemma polynomial_acceptanceInput : PolynomialTime acceptanceInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_currentValue polynomial_targetValue)
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_second polynomial_second) polynomial_second) polynomial_second)

lemma polynomial_accepted : PolynomialTime acceptedRealizer :=
  polynomial_composition polynomial_acceptanceInput FractionMetropolisProgram.polynomial_accept

attribute [local irreducible] accepted

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_choose (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_choose polynomial_accepted polynomial_candidate
      (polynomial_composition polynomial_first polynomial_second))

end ContingencyTables.CompanionMetropolisProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionMetropolisWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded slicing of one flat companion transition word -/

namespace ContingencyTables.CompanionMetropolisWordProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  unfold proposalWidthRealizer
  apply polynomial_composition _ polynomial_ceilLogTwo
  apply polynomial_congr
  apply polynomial_composition _ polynomial_multiply
  apply polynomial_pair
  all_goals exact (polynomial_composition
      (polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_listLength) (polynomial_constant 2)) polynomial_quotient)

lemma polynomial_context : PolynomialTime contextRealizer := by
  unfold contextRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_first) polynomial_first) polynomial_first

lemma polynomial_queryWidth : PolynomialTime queryWidthRealizer :=
  polynomial_composition (polynomial_pair (by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe))))
    (polynomial_composition polynomial_context RootedEstimatorLayoutProgram.polynomial_wordWidth)) polynomial_multiply

attribute [local irreducible] context queryWidth proposalWidth

lemma polynomial_firstOffset : PolynomialTime firstOffsetRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 1) polynomial_proposalWidth) polynomial_add

attribute [local irreducible] firstOffset

lemma polynomial_secondOffset : PolynomialTime secondOffsetRealizer :=
  polynomial_composition (polynomial_pair polynomial_firstOffset polynomial_queryWidth) polynomial_add

attribute [local irreducible] secondOffset

lemma polynomial_coinOffset : PolynomialTime coinOffsetRealizer :=
  polynomial_composition (polynomial_pair polynomial_secondOffset polynomial_queryWidth) polynomial_add

private lemma polynomial_slice {start count : Input → ℕ}
    (S : Realizer start) (C : Realizer count) (hS : PolynomialTime S) (hC : PolynomialTime C) :
    PolynomialTime (sliceRealizer S C) :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_second hS) polynomial_dropFast) hC) polynomial_takeFast

lemma polynomial_fields : PolynomialTime fieldsRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_second (polynomial_constant 0))
    (polynomial_getDFast false))
    (polynomial_pair (polynomial_slice _ _ (polynomial_constant 1) polynomial_proposalWidth)
      (polynomial_pair (polynomial_pair
        (polynomial_slice _ _ polynomial_firstOffset polynomial_queryWidth)
        (polynomial_slice _ _ polynomial_secondOffset polynomial_queryWidth))
        (polynomial_slice _ _ polynomial_coinOffset (by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))))))

lemma polynomial_stepInput : PolynomialTime stepInputRealizer :=
  polynomial_pair (polynomial_pair (by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))) (polynomial_composition polynomial_first polynomial_second))
    polynomial_fields

attribute [local irreducible] stepInput

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_stepInput CompanionMetropolisProgram.polynomial_output

end ContingencyTables.CompanionMetropolisWordProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BoundedProfileWalk
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop for the encoded small-profile walk -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_capView : PolynomialTime capViewRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_first)) polynomial_takeFast))
    (polynomial_mapWith (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      polynomial_minimum))

lemma capView_weight (q U : ℕ) (xs : List ℕ) :
    weight (capView ((q,U),xs))≤q*(4*U.size+2)+1 := by
  have hw := weight_map_bound (f := fun a => min a U) (as := xs.take q) (N := 4*U.size+1)
    (fun a _ => (weight_nat_le _).trans (by
      have hs := Nat.size_le_size (min_le_right a U)
      omega))
  change weight (capView ((q,U),xs))≤(xs.take q).length*(4*U.size+2)+1 at hw
  exact hw.trans (by
    have hl : (xs.take q).length≤q := by simp only [List.length_take]; exact min_le_left _ _
    gcongr)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionBoundedWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial iteration of the physical companion transition

Clipping is redundant on the encoded binary chain states. It gives a
uniform bound on malformed inputs, so repeated calls remain polynomial.
-/

namespace ContingencyTables.CompanionBoundedWalkProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_transitionInput : PolynomialTime transitionInputRealizer :=
  polynomial_pair (polynomial_pair (by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))) (polynomial_composition polynomial_second polynomial_second))
    polynomial_first

lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition polynomial_transitionInput CompanionMetropolisWordProgram.polynomial_output

lemma polynomial_bound : PolynomialTime boundRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition
    polynomial_second polynomial_first) polynomial_second) polynomial_listLength

attribute [local irreducible] candidate

lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_bound (polynomial_constant 1))
    polynomial_candidate) ProfilePrograms.polynomial_capView

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_next

lemma advance_weight (word : List Bool) (state : State) (S : ℕ) (hs : weight state.1 ≤ S) :
    weight (advance (word,state)) ≤ 10*(S+1) := by
  have hb : state.1.2.length ≤ S :=
    (list_length_le_weight _).trans ((weight_snd state.1).trans hs)
  have hn := ProfilePrograms.capView_weight state.1.2.length 1 (candidate (word,state))
  change weight (next (word,state)) ≤ _ at hn
  norm_num only [Nat.size_one] at hn
  change weight (state.1,next (word,state)) ≤ _
  rw [weight_prod]
  omega

lemma polynomial_recordAdvance : PolynomialTime recordAdvanceRealizer := by
  unfold recordAdvanceRealizer
  have hn : PolynomialTime (composition
      (f := fun z : List Bool × RecordState => (z.1,z.2.1)) (g := advance)
      (pair first (composition second first)) advanceRealizer) :=
    polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) polynomial_advance
  exact polynomial_pair hn (polynomial_composition (polynomial_pair
    (polynomial_composition hn polynomial_second) (polynomial_composition polynomial_second polynomial_second))
    polynomial_listCons)

lemma recordFold_bounds_fixed (words : List (List Bool)) (state : RecordState) (S : ℕ)
    (hfixed : weight state.1.1 ≤ S) (hcurrent : weight state.1 ≤ 10*(S+1)) :
    let out := words.foldl (fun state bits => recordAdvance (bits,state)) state
    out.1.1=state.1.1 ∧ weight out.1 ≤ 10*(S+1) ∧
      weight out.2 ≤ weight state.2+words.length*(10*(S+1)+1) := by
  induction words generalizing state with
  | nil => exact ⟨rfl,hcurrent,by simp⟩
  | cons word words ih =>
    have hn := advance_weight word state.1 S hfixed
    have hh := ih (recordAdvance (word,state)) hfixed hn
    simp only [List.foldl_cons]
    dsimp only at hh ⊢
    refine ⟨hh.1,hh.2.1,?_⟩
    have hb : weight (advance (word,state.1)).2 ≤ 10*(S+1) := (weight_snd _).trans hn
    simp only [recordAdvance,weight_cons,List.length_cons] at hh ⊢
    simp only [Nat.add_mul,Nat.one_mul] at *
    omega

lemma recordFold_weight (words : List (List Bool)) (state : RecordState) (S : ℕ)
    (hw : words.length ≤ S) (hs : weight state ≤ S) :
    weight (words.foldl (fun state bits => recordAdvance (bits,state)) state) ≤ 30*(S+1)^2 := by
  have hc : weight state.1 ≤ S := (weight_fst state).trans hs
  have hf : weight state.1.1 ≤ S := (weight_fst state.1).trans hc
  have hh : weight state.2 ≤ S := (weight_snd state).trans hs
  have hb := recordFold_bounds_fixed words state S hf (hc.trans (by omega))
  dsimp only at hb
  rw [weight_prod]
  have hmul : words.length*(10*(S+1)+1) ≤ S*(10*(S+1)+1) :=
    Nat.mul_le_mul_right _ hw
  nlinarith [hb.2.1,hb.2.2]

theorem polynomial_recordWalk : PolynomialTime recordWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_recordAdvance (30*(X+1)^2)
  intro words state pre post he
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one,eval_pow]
  apply recordFold_weight pre state (weight (words,state))
  · have hp : pre.length ≤ words.length := by rw [he,List.length_append]; omega
    exact hp.trans ((list_length_le_weight words).trans (weight_fst (words,state)))
  · exact weight_snd (words,state)

lemma polynomial_initialRecord : PolynomialTime initialRecordRealizer :=
  polynomial_pair polynomial_identity (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_constant [])) polynomial_listCons)

theorem polynomial_history : PolynomialTime historyRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_initialRecord) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_recordWalk polynomial_second)
      polynomial_reverse)

end ContingencyTables.CompanionBoundedWalkProgram

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


end ContingencyTables.ScalarScheduleProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTransitionWidth
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the exact companion transition word length -/

namespace ContingencyTables.CompanionTransitionWidth

open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram
open CompanionMetropolisWordProgram

attribute [local irreducible] proposalWidth queryWidth
lemma polynomial_values : PolynomialTime valuesRealizer := by
  unfold valuesRealizer
  exact polynomial_composition (polynomial_pair polynomial_proposalWidth
    (polynomial_composition (polynomial_pair polynomial_queryWidth
      (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        (polynomial_constant [])) polynomial_listCons)) polynomial_listCons)) polynomial_listCons

theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition polynomial_values expression.polynomial

end ContingencyTables.CompanionTransitionWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionFlatReturnProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A bounded flat word for the actual capped-return program -/

namespace ContingencyTables.CompanionFlatReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_widthInput : PolynomialTime widthInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_constant [])

lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition polynomial_widthInput CompanionTransitionWidth.polynomial_width

lemma polynomial_words : PolynomialTime wordsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_width polynomial_second) polynomial_wordChunks)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_takeFast

lemma polynomial_returnInput : PolynomialTime returnInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_words

end ContingencyTables.CompanionFlatReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionTrajectoryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The flat executed observation trajectory, including its initial state -/
namespace ContingencyTables.CompanionTrajectoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition CompanionFlatReturnProgram.polynomial_returnInput
    CompanionBoundedWalkProgram.polynomial_history

open CommonBasesFPRAS CompanionFactorialApplication CompanionComputedInitial CompanionComputedProposal
open CompanionArithmeticProposal CompanionOracleDensity CompanionWeightOracle
open CompanionEvaluatedWeightProgram CompanionMultiplierMatrixProgram FiniteObservableTransport
open TwoLiftStates GridBoundary
open scoped Classical
end ContingencyTables.CompanionTrajectoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete executed trajectory and fresh-observation phase trial -/
namespace ContingencyTables.CompanionPhaseTrialProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecConfigs
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecBase
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecProdConfigsBase
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecInput
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecFrame
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecProdFrameInput
attribute [local instance] OAI.ContingencyTables.CompanionPhaseTrialProgram.instCodecInput_1
lemma polynomial_trajectory : PolynomialTime trajectoryRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    CompanionTrajectoryProgram.polynomial_output

lemma polynomial_catalogue : PolynomialTime catalogueRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      polynomial_first) polynomial_second) PairedCatalogProgram.polynomial_catalog

attribute [local irreducible] trajectory catalogue

lemma polynomial_returnInput : PolynomialTime returnInputRealizer :=
  polynomial_pair polynomial_catalogue polynomial_trajectory

lemma polynomial_storedInput : PolynomialTime storedInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_returnInput
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_second) polynomial_first))
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_second) polynomial_second)

lemma polynomial_updateInput : PolynomialTime updateInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_storedInput)
    polynomial_second

attribute [local irreducible] updateInput

lemma polynomial_output_oai : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_updateInput CompanionObservedUpdateProgram.polynomial_output

end ContingencyTables.CompanionPhaseTrialProgram

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output_oai := @OAI.ContingencyTables.CompanionPhaseTrialProgram.polynomial_output_oai
