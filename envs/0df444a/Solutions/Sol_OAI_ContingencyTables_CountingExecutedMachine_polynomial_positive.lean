-- Prove2me | solution 1 for OAI.ContingencyTables.CountingExecutedMachine.polynomial_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:24:16.332073+00:00
-- url     : https://prove2.me/submissions/e653db27-ba9f-48af-9efa-ceeea4847b84

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009
import Definitions.Def_OAIQ089A010
import Theorems.Thm_OAI_ContingencyTables_CompanionObservationQueriesProgram_polynomial_output
import Theorems.Thm_OAI_ContingencyTables_CompanionPhaseTrialProgram_polynomial_output
import Theorems.Thm_OAI_ContingencyTables_CompanionRepeatedReturnProgram_polynomial_output

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial binary arithmetic for sequential subset inclusion

The rational inclusion threshold is computed by an integer product and
quotient. In particular the denominator is never expanded into a
unary loop; the only exponential integer has the supplied word length
as its binary length.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

theorem polynomial_include : PolynomialTime includeRealizer := by
  unfold includeRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_second polynomial_bitValue)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_bitDenominator)
        (polynomial_composition (polynomial_pair
          (polynomial_composition polynomial_first polynomial_second)
          (polynomial_composition polynomial_first polynomial_first)) polynomial_minimum))
        polynomial_multiply)
      (polynomial_composition polynomial_first polynomial_first)) polynomial_quotient))
    polynomial_less)

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFold
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial sequential list program for the subset draw

The accumulator retains the remaining population and requested size,
and records one inclusion bit per input word. Both counters decrease;
only the output list grows. The final program reverses that list once.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_advance : PolynomialTime advanceRealizer := by
  unfold advanceRealizer
  have hn : PolynomialTime (composition
      (composition (second (A := List Bool) (B := DrawState)) first) first) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first
  have hk : PolynomialTime (composition
      (composition (second (A := List Bool) (B := DrawState)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second
  have hb : PolynomialTime (composition
      (pair (composition (second (A := List Bool) (B := DrawState)) first) first)
      includeRealizer) := polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_first)
    polynomial_include
  have hr := polynomial_composition (polynomial_pair hn (polynomial_constant 1)) polynomial_subtract
  exact polynomial_pair
    (polynomial_pair hr (polynomial_choose hb
      (polynomial_composition (polynomial_pair hk (polynomial_constant 1)) polynomial_subtract)
      (polynomial_composition (polynomial_pair hk hr) polynomial_minimum)))
    (polynomial_composition (polynomial_pair hb
      (polynomial_composition polynomial_second polynomial_second)) polynomial_listCons)

lemma advance_bounds (word : List Bool) (s : DrawState) :
    (advance (word,s)).1.1 ≤ s.1.1 ∧ (advance (word,s)).1.2 ≤ s.1.2 ∧
      weight (advance (word,s)).2 ≤ weight s.2+4 := by
  refine ⟨Nat.sub_le _ _,?_,?_⟩
  · change (if includeCode (s.1,word) then s.1.2-1 else min s.1.2 (s.1.1-1)) ≤ s.1.2
    split_ifs
    · exact Nat.sub_le _ _
    · exact min_le_left _ _
  · change weight (includeCode (s.1,word)::s.2)≤_
    rw [weight_cons]
    have h := weight_bool (includeCode (s.1,word))
    omega

lemma fold_bounds (words : List (List Bool)) (s : DrawState) :
    let out := words.foldl (fun s word => advance (word,s)) s
    out.1.1 ≤ s.1.1 ∧ out.1.2 ≤ s.1.2 ∧ weight out.2 ≤ weight s.2+4*words.length := by
  induction words generalizing s with
  | nil => exact ⟨le_rfl,le_rfl,by simp⟩
  | cons w ws ih =>
    have hs := advance_bounds w s
    have ht := ih (advance (w,s))
    refine ⟨ht.1.trans hs.1,ht.2.1.trans hs.2.1,?_⟩
    simp only [List.foldl_cons,List.length_cons]
    omega

theorem polynomial_drawWords : PolynomialTime drawWordsRealizer := by
  have hf : PolynomialTime (fold advanceRealizer) := by
    apply polynomial_fold polynomial_advance (20*(X+1))
    intro words s pre post he
    let S := weight (words,s)
    let out := pre.foldl (fun s word => advance (word,s)) s
    have hs : weight s≤S := weight_snd (words,s)
    have hn : s.1.1.size≤S :=
      (size_le_weight _).trans ((weight_fst s.1).trans ((weight_fst s).trans hs))
    have hk : s.1.2.size≤S :=
      (size_le_weight _).trans ((weight_snd s.1).trans ((weight_fst s).trans hs))
    have hb : weight s.2≤S := (weight_snd s).trans hs
    have hp : pre.length≤S := (list_length_le_weight pre).trans
      ((weight_prefix he).trans (weight_fst (words,s)))
    have ht := fold_bounds pre s
    have hon : weight out.1.1≤4*out.1.1.size+1 := weight_nat_le out.1.1
    have hok : weight out.1.2≤4*out.1.2.size+1 := weight_nat_le out.1.2
    have hsn : out.1.1.size≤S := (Nat.size_le_size ht.1).trans hn
    have hsk : out.1.2.size≤S := (Nat.size_le_size ht.2.1).trans hk
    have hlist : weight out.2≤weight s.2+4*pre.length := ht.2.2
    have hnweight : weight out.1.1≤4*S+1 := hon.trans (by omega)
    have hkweight : weight out.1.2≤4*S+1 := hok.trans (by omega)
    have hlweight : weight out.2≤5*S := by omega
    have hw : weight out=weight out.1.1+weight out.1.2+weight out.2+2 := by
      change weight ((out.1.1,out.1.2),out.2)=_
      simp only [weight_prod]
      omega
    simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
    change weight out≤20*(S+1)
    rw [hw]
    omega
  unfold drawWordsRealizer runWordsRealizer prepareWordsRealizer outputRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_second (polynomial_pair polynomial_first (polynomial_constant []))) hf)
    (polynomial_composition polynomial_second polynomial_reverse)

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_FixedCardinalityFlat
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A flat-word program for a local initial subset

The first B bits select the size. The remaining word is partitioned
into B-bit inclusion rows, so the input list bounds the number of loop
iterations even on malformed inputs.
-/

namespace ContingencyTables.FixedCardinalityProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms

theorem polynomial_subsetCode : PolynomialTime subsetCodeRealizer := by
  unfold subsetCodeRealizer
  have hn : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := List Bool)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hb : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  exact polynomial_composition (polynomial_pair
    (polynomial_pair hn (polynomial_composition
      (polynomial_pair (polynomial_composition hn polynomial_successor)
        (polynomial_composition (polynomial_pair polynomial_second hb) polynomial_takeFast))
      polynomial_scaledWord))
    (polynomial_composition (polynomial_pair hb
      (polynomial_composition (polynomial_pair polynomial_second hb) polynomial_dropFast))
      polynomial_wordChunks)) polynomial_drawWords

end ContingencyTables.FixedCardinalityProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_InitialChoiceProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial independent-cell initialization program

The capacities are a supplied list. A polynomial index scan extracts
each disjoint variable-width word block and runs the local subset
program. The resulting rows are exactly the independent cell choices
in the initial finite-word law.
-/

namespace ContingencyTables.InitialChoiceProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open DensePrograms FixedCardinalityProgram

theorem polynomial_cellWidth : PolynomialTime cellWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_multiply))
    polynomial_add

theorem polynomial_widths : PolynomialTime widthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_cellWidth)

theorem polynomial_cellCode : PolynomialTime cellCodeRealizer := by
  unfold cellCodeRealizer
  have hc : PolynomialTime (composition
      (pair (composition (composition (first (A := Input) (B := ℕ)) first) first) second)
      (getDFast 0)) := polynomial_composition
    (polynomial_pair (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    (polynomial_getDFast 0)
  have hb : PolynomialTime (composition
      (composition (first (A := Input) (B := ℕ)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  have hs := polynomial_composition
    (polynomial_composition (polynomial_first (A := Input) (B := ℕ)) polynomial_first) polynomial_widths
  exact polynomial_composition (polynomial_pair (polynomial_pair hc hb)
    (polynomial_composition (polynomial_pair (polynomial_pair hs
      (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
      polynomial_dependentChunk)) polynomial_subsetCode

theorem polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

theorem polynomial_choiceCode : PolynomialTime choiceCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_cellCode)

end ContingencyTables.InitialChoiceProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CanonicalInitialEncoding
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Canonical paired-label order for the initial binary program

The order is the explicit list of cells, then their copies, then the
two sides of each pair. The code is obtained directly from the sampled
Boolean rows, so no enumeration of the set-valued state space occurs.
-/

namespace ContingencyTables.CanonicalInitialEncoding

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CommonBasesFPRAS InitialTransversals FixedCardinalityMixture InitialFactorialBits
open scoped BigOperators Classical

theorem polynomial_pairValue : PolynomialTime pairValueRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_choose polynomial_identity (polynomial_constant 1) (polynomial_constant 0))
    (polynomial_composition (polynomial_pair
      (polynomial_choose polynomial_identity (polynomial_constant 0) (polynomial_constant 1))
      (polynomial_constant [])) polynomial_listCons)) polynomial_listCons

theorem polynomial_pairedCode : PolynomialTime pairedCodeRealizer :=
  polynomial_composition polynomial_flatten (polynomial_flatMapPoly polynomial_pairValue)

theorem polynomial_initialCode : PolynomialTime initialCodeRealizer :=
  polynomial_composition InitialChoiceProgram.polynomial_choiceCode polynomial_pairedCode

end ContingencyTables.CanonicalInitialEncoding

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionComputedInitial
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization from the computed small-cell catalog

The proof-level equivalence follows the actual catalog program. It is
used only to identify the output of the binary list initializer with a
paired transversal and to transfer its distributional error bound.
-/

namespace ContingencyTables.CompanionComputedInitial

open MatchingFPRAS.TreeTyped CompanionFactorialApplication
open InitialTransversals InitialFactorialBits CompanionInitialDraw
open FirstSuccess ResidualMixture TwoLiftStates CommonBasesFPRAS
open CompanionArithmeticProposal
open scoped BigOperators Classical

theorem polynomial_initialProgram : PolynomialTime initialProgramRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      CompanionCellCatalog.polynomial_capacities)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
    CanonicalInitialEncoding.polynomial_initialCode

end ContingencyTables.CompanionComputedInitial

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

lemma polynomial_natural : PolynomialTime naturalRealizer :=
  polynomial_pair polynomial_identity (polynomial_constant 1)
lemma polynomial_sampleBase : PolynomialTime sampleBaseRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_constant 65536)
    (polynomial_composition polynomial_first polynomial_successor)) polynomial_multiply) polynomial_natural

lemma polynomial_sampleDenominator : PolynomialTime sampleDenominatorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition polynomial_second polynomial_first)) TreeFraction.polynomial_mul))
    TreeFraction.polynomial_mul

lemma polynomial_sampleRatio : PolynomialTime sampleRatioRealizer :=
  polynomial_composition (polynomial_pair polynomial_sampleBase polynomial_sampleDenominator)
    TreeFraction.polynomial_div

lemma polynomial_sampleCount : PolynomialTime sampleCountRealizer :=
  polynomial_composition polynomial_sampleRatio polynomial_ceiling

lemma polynomial_offsetBase : PolynomialTime offsetBaseRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 4096) polynomial_first) polynomial_multiply) polynomial_natural

lemma polynomial_offsetRatio : PolynomialTime offsetRatioRealizer :=
  polynomial_composition (polynomial_pair polynomial_offsetBase polynomial_second) TreeFraction.polynomial_div

lemma polynomial_offsetAccuracy : PolynomialTime offsetAccuracyRealizer :=
  polynomial_composition polynomial_offsetRatio polynomial_ceiling

lemma polynomial_timeBase : PolynomialTime timeBaseRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_multiply) polynomial_natural

lemma polynomial_timeNumerator : PolynomialTime timeNumeratorRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_constant 16)
    (polynomial_composition polynomial_first polynomial_first)) polynomial_multiply) polynomial_natural

lemma polynomial_timeExtra : PolynomialTime timeExtraRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeNumerator polynomial_second) TreeFraction.polynomial_div

lemma polynomial_timeTotal : PolynomialTime timeTotalRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeBase polynomial_timeExtra) TreeFraction.polynomial_add

lemma polynomial_oracleTime : PolynomialTime oracleTimeRealizer :=
  polynomial_composition polynomial_timeTotal polynomial_ceiling

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

lemma polynomial_vector (es : List Expr) : PolynomialTime (vectorRealizer es) := by
  induction es with
  | nil => exact polynomial_constant []
  | cons e es ih => exact polynomial_composition (polynomial_pair e.polynomial ih) polynomial_listCons


end ContingencyTables.ScalarScheduleProgram

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

lemma polynomial_reciprocalTolerance : PolynomialTime reciprocalToleranceRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant (1,1)) polynomial_tolerance)
    TreeFraction.polynomial_div

lemma polynomial_reciprocalCeiling : PolynomialTime reciprocalCeilingRealizer :=
  polynomial_composition polynomial_reciprocalTolerance polynomial_ceiling

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_pair (polynomial_scalar CountingPhaseScalarProgram.precisionBase)
    polynomial_reciprocalCeiling) polynomial_add

lemma polynomial_noise : PolynomialTime noiseRealizer :=
  polynomial_pair (polynomial_constant 1) polynomial_precision

end ContingencyTables.CountingPhaseParametersProgram

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

lemma polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2) polynomial_identity)
    polynomial_multiply

lemma polynomial_rows : PolynomialTime rowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first (polynomial_map polynomial_width)) polynomial_second)
    NaturalBlockProgram.polynomial_blocks

end ContingencyTables.PairedProfileProgram

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

lemma polynomial_pairCount : PolynomialTime pairCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant 2))
    polynomial_quotient

end ContingencyTables.PairedFactorialProgram

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_RootedOracleConfigProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition polynomial_fields e.polynomial

lemma polynomial_inner : PolynomialTime innerRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_scalar relativeDenominator) polynomial_natural))
    TreeFraction.polynomial_div

lemma polynomial_correction : PolynomialTime correctionRealizer :=
  polynomial_composition (polynomial_pair polynomial_inner (polynomial_constant _)) TreeFraction.polynomial_div

lemma polynomial_samples : PolynomialTime samplesRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_pair polynomial_inner (polynomial_constant _))) polynomial_sampleCount

lemma polynomial_timeInput : PolynomialTime timeInputRealizer :=
  polynomial_pair (polynomial_scalar mixing) (polynomial_scalar allowance)

lemma polynomial_ratioTime : PolynomialTime ratioTimeRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeInput polynomial_inner) polynomial_oracleTime

lemma polynomial_correctionTime : PolynomialTime correctionTimeRealizer :=
  polynomial_composition (polynomial_pair polynomial_timeInput polynomial_correction) polynomial_oracleTime

lemma polynomial_offsetAccuracy : PolynomialTime offsetAccuracyRealizer :=
  polynomial_composition (polynomial_pair (polynomial_scalar dim) polynomial_inner)
    CountingOracleScheduleProgram.polynomial_offsetAccuracy

lemma polynomial_normalizedNoise : PolynomialTime normalizedNoiseRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) TreeFraction.polynomial_normalize

lemma polynomial_repeats : PolynomialTime repeatsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 64)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_normalizedNoise polynomial_second) polynomial_toBits)
      polynomial_listLength) polynomial_successor)) polynomial_multiply

lemma polynomial_rootDegree : PolynomialTime rootDegreeRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant _) polynomial_inner) TreeFraction.polynomial_div) polynomial_ceiling

lemma polynomial_depth : PolynomialTime depthRealizer :=
  polynomial_composition polynomial_rootDegree polynomial_ceilLogTwo

lemma polynomial_markers : PolynomialTime markersRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair polynomial_second polynomial_rootDegree) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_depth) polynomial_takeFast)

lemma polynomial_schedule : PolynomialTime scheduleRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_samples)
    (polynomial_pair (polynomial_pair polynomial_ratioTime polynomial_correctionTime) polynomial_offsetAccuracy)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_schedule) polynomial_repeats) polynomial_markers

attribute [local irreducible] output

lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_composition (polynomial_composition polynomial_output polynomial_first) polynomial_first
attribute [local irreducible] context

lemma polynomial_contextWidth : PolynomialTime contextWidthRealizer :=
  polynomial_composition polynomial_context RootedEstimatorLayoutProgram.polynomial_wordWidth
attribute [local irreducible] contextWidth

theorem polynomial_wordWidth : PolynomialTime wordWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_repeats polynomial_contextWidth) polynomial_multiply

end ContingencyTables.RootedOracleConfigProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseContextProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing a phase configuration from immutable prepared data

The reserve is used only through its length. All precision-marker bits
are false, so the physical configuration is independent of the random
contents of the word that provides its bounded allocation.
-/

namespace ContingencyTables.CompanionPhaseContextProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_noise : PolynomialTime noiseRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) CountingPhaseParametersProgram.polynomial_noise

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) CountingPhaseParametersProgram.polynomial_precision

lemma polynomial_scalar (e : ScalarScheduleProgram.Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) (CountingPhaseParametersProgram.polynomial_scalar e)

lemma polynomial_falseReserve : PolynomialTime falseReserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

lemma polynomial_configInput : PolynomialTime configInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_noise) (polynomial_composition polynomial_first polynomial_second)) polynomial_falseReserve

theorem polynomial_config : PolynomialTime configRealizer :=
  polynomial_composition polynomial_configInput RootedOracleConfigProgram.polynomial_output

end ContingencyTables.CompanionPhaseContextProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartInitializer
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The computed finite initializer used before every restart experiment -/
namespace ContingencyTables.CompanionRestartInitializer
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms

lemma polynomial_forest : PolynomialTime forestRealizer := by
  unfold forestRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second)
    polynomial_first

lemma polynomial_cellInput : PolynomialTime cellInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_forest (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_forest polynomial_second))
    (polynomial_composition polynomial_forest
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))

lemma polynomial_fields : PolynomialTime fieldsRealizer := by
  unfold fieldsRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second) polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_listCons

lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition polynomial_fields e.polynomial

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_scalar initialBound) polynomial_ceilLogTwo)
    (polynomial_scalar initialExponent)) polynomial_add

lemma polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition polynomial_cellInput CompanionCellCatalog.polynomial_capacities

theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_capacities polynomial_precision)
    InitialChoiceProgram.polynomial_widths) polynomial_listSum

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_cellInput)
    (polynomial_composition polynomial_first polynomial_precision)) polynomial_second

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CompanionComputedInitial.polynomial_initialProgram

end ContingencyTables.CompanionRestartInitializer

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

attribute [local irreducible] firstOffset

attribute [local irreducible] secondOffset

attribute [local irreducible] stepInput

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRepeatedReturnProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Bounded iteration of the executed capped-return routine

The numeric repetition count only truncates chunks of the supplied
word. The stored profile is clipped to the fixed initial dimension,
which is redundant on every actual encoded state.
-/

namespace ContingencyTables.CompanionRepeatedReturnProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms

attribute [local irreducible] candidate

lemma polynomial_widthInput : PolynomialTime widthInputRealizer := by
  unfold widthInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_first polynomial_second)) (polynomial_constant [])

lemma polynomial_blockWidth : PolynomialTime blockWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_successor)
    (polynomial_composition polynomial_widthInput CompanionTransitionWidth.polynomial_width)) polynomial_multiply

end ContingencyTables.CompanionRepeatedReturnProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartStageProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One executed warm-restart stage

The context supplies the phase, immutable oracle metadata and deterministic
precision markers. The matrix is the stored multiplier for that phase.
-/
namespace ContingencyTables.CompanionRestartStageProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped
open CompanionMultiplierMatrixProgram

lemma polynomial_context : PolynomialTime contextRealizer :=
  polynomial_composition polynomial_first polynomial_first

lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_context CompanionPhaseContextProgram.polynomial_config)
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_context CompanionPhaseContextProgram.polynomial_precision)

lemma polynomial_cap : PolynomialTime capRealizer :=
  polynomial_composition polynomial_context (CompanionPhaseContextProgram.polynomial_scalar _)

lemma polynomial_repetitions : PolynomialTime repetitionsRealizer :=
  polynomial_composition polynomial_context (CompanionPhaseContextProgram.polynomial_scalar _)

attribute [local irreducible] frame cap repetitions

lemma polynomial_fixed : PolynomialTime fixedRealizer :=
  polynomial_pair (polynomial_pair polynomial_frame polynomial_second) polynomial_cap

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_fixed)
    (polynomial_composition polynomial_first polynomial_second))
    (polynomial_composition polynomial_first polynomial_repetitions)) polynomial_second

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CompanionRepeatedReturnProgram.polynomial_output

theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair polynomial_repetitions
    (polynomial_composition polynomial_fixed CompanionRepeatedReturnProgram.polynomial_blockWidth))
    polynomial_multiply

end ContingencyTables.CompanionRestartStageProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed restart stages with disjoint variable-width words

The supplied stage list determines the number of iterations. The current
encoded profile is bounded by the original profile length after every stage.
-/
namespace ContingencyTables.CompanionRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial DensePrograms
open CompanionMultiplierMatrixProgram

lemma polynomial_request : PolynomialTime requestRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) (polynomial_getDFast default))
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_indexedWidth : PolynomialTime indexedWidthRealizer :=
  polynomial_composition polynomial_request CompanionRestartStageProgram.polynomial_width

lemma polynomial_widths : PolynomialTime widthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_indexedWidth)

lemma polynomial_stageWord : PolynomialTime stageWordRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_widths)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second)
    polynomial_dependentChunk

lemma polynomial_stageInput : PolynomialTime stageInputRealizer := by
  unfold stageInputRealizer
  apply polynomial_pair
  · apply polynomial_pair
    · exact polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition (polynomial_composition
          polynomial_second polynomial_first) polynomial_first) polynomial_first)
        polynomial_first) (polynomial_getDFast default)
    · exact polynomial_composition polynomial_second polynomial_second
  · exact polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_stageWord

lemma polynomial_candidate : PolynomialTime candidateRealizer :=
  polynomial_composition polynomial_stageInput CompanionRestartStageProgram.polynomial_output

lemma polynomial_bound : PolynomialTime boundRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_second)
    polynomial_listLength

attribute [local irreducible] candidate

lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_bound (polynomial_constant 1))
    polynomial_candidate) ProfilePrograms.polynomial_capView

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_next

lemma advance_weight (i : ℕ) (state : State) (S : ℕ) (hs : weight state.1 ≤ S) :
    weight (advance (i,state)) ≤ 10*(S+1) := by
  have hb : state.1.1.2.length ≤ S := (list_length_le_weight _).trans
    ((weight_snd state.1.1).trans ((weight_fst state.1).trans hs))
  have hn := ProfilePrograms.capView_weight state.1.1.2.length 1 (candidate (i,state))
  change weight (next (i,state)) ≤ _ at hn
  norm_num only [Nat.size_one] at hn
  change weight (state.1,next (i,state)) ≤ _
  rw [weight_prod]
  omega

lemma fold_fixed (is : List ℕ) (state : State) :
    (is.foldl (fun state i => advance (i,state)) state).1=state.1 := by
  induction is generalizing state with
  | nil => rfl
  | cons i is ih => exact ih _

lemma fold_weight (is : List ℕ) (state : State) (S : ℕ) (hs : weight state ≤ S) :
    weight (is.foldl (fun state i => advance (i,state)) state) ≤ 10*(S+1) := by
  induction is using List.reverseRecOn with
  | nil => simpa using hs.trans (by omega : S ≤ 10*(S+1))
  | append_singleton is i _ =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply advance_weight
    rw [fold_fixed]
    exact (weight_fst state).trans hs

theorem polynomial_walk : PolynomialTime walkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (10*(X+1))
  intro is state pre post _
  simp only [eval_mul,eval_ofNat,eval_add,eval_X,eval_one]
  exact fold_weight pre state (weight (is,state)) (weight_snd (is,state))

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_second)) polynomial_indices)
    (polynomial_composition polynomial_walk polynomial_second)

end ContingencyTables.CompanionRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitializedRestartProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Initialization and all stored-multiplier restart stages

Past entries are stored in chronological order. Entry i contains the
multiplier for restart phase i+1. Initialization and restart stages take
disjoint slices of the supplied word.
-/
namespace ContingencyTables.CompanionInitializedRestartProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_reserve : PolynomialTime reserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma polynomial_stageAt : PolynomialTime stageAtRealizer := by
  unfold stageAtRealizer
  apply polynomial_pair
  · exact polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition polynomial_second polynomial_successor))
      (polynomial_composition polynomial_first polynomial_reserve)
  · exact polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second) (polynomial_getDFast default)) polynomial_first

lemma polynomial_stages : PolynomialTime stagesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_stageAt)

lemma polynomial_initialWidth : PolynomialTime initialWidthRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    CompanionRestartInitializer.polynomial_width

lemma polynomial_initialInput : PolynomialTime initialInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_initialWidth) polynomial_takeFast)

lemma polynomial_initialCode : PolynomialTime initialCodeRealizer :=
  polynomial_composition polynomial_initialInput CompanionRestartInitializer.polynomial_output

attribute [local irreducible] stages initialCode initialWidth

lemma polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_pair (polynomial_pair polynomial_stages polynomial_initialCode)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_initialWidth) polynomial_dropFast)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_prepare CompanionRestartProgram.polynomial_output

end ContingencyTables.CompanionInitializedRestartProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionRestartSchedule
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A deterministic bit allocation for initialized restart experiments -/
namespace ContingencyTables.CompanionRestartSchedule
open MatchingFPRAS MatchingFPRAS.TreeTyped ScalarScheduleProgram DensePrograms Polynomial

lemma polynomial_configInput : PolynomialTime configInputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_successor)) (polynomial_constant []))
    CompanionPhaseContextProgram.polynomial_configInput

lemma polynomial_queryWidth : PolynomialTime queryWidthRealizer :=
  polynomial_composition polynomial_configInput RootedOracleConfigProgram.polynomial_wordWidth

lemma polynomial_scalar (e : Expr) : PolynomialTime (scalarRealizer e) :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    (CountingPhaseParametersProgram.polynomial_scalar e)

lemma polynomial_proposalWidth : PolynomialTime proposalWidthRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair (polynomial_scalar _) (polynomial_scalar _))
    polynomial_multiply) polynomial_ceilLogTwo

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    CountingPhaseParametersProgram.polynomial_precision

 private lemma polynomial_consR {f : StageInput→ℕ} {g : StageInput→List ℕ}
    (F : Realizer f) (G : Realizer g) (hF : PolynomialTime F) (hG : PolynomialTime G) :
    PolynomialTime (consR F G) := polynomial_composition (polynomial_pair hF hG) polynomial_listCons

lemma polynomial_fields : PolynomialTime fieldsRealizer := by
  unfold fieldsRealizer
  exact polynomial_consR _ _ polynomial_proposalWidth (polynomial_consR _ _ polynomial_queryWidth
    (polynomial_consR _ _ polynomial_precision (polynomial_consR _ _ (polynomial_scalar _)
      (polynomial_consR _ _ (polynomial_scalar _) (polynomial_constant [])))))

theorem polynomial_stageWidth : PolynomialTime stageWidthRealizer :=
  polynomial_composition polynomial_fields expression.polynomial

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.2).trans (weight_snd z)

lemma polynomial_indexedWidth : PolynomialTime indexedWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_second) polynomial_stageWidth

theorem polynomial_restartWidth : PolynomialTime restartWidthRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith polynomial_indexedWidth)) polynomial_listSum

theorem polynomial_width : PolynomialTime widthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first CompanionRestartInitializer.polynomial_width)
    polynomial_restartWidth) polynomial_add

end ContingencyTables.CompanionRestartSchedule

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterPhaseProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # One complete adaptive phase from the stored chronological history -/
namespace ContingencyTables.CompanionOuterPhaseProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
attribute [local instance] OAI.ContingencyTables.CompanionOuterPhaseProgram.instCodecConfigs
local instance instCodecBase_r492cf7_1 : Codec CompanionObservedUpdateProgram.Base := inferInstance
local instance instCodecProdConfigsBase_r492cf7_1 : Codec (CompanionObservedUpdateProgram.Configs×CompanionObservedUpdateProgram.Base) := inferInstance
local instance instCodecInput_r492cf7_1 : Codec CompanionObservedUpdateProgram.Input := inferInstance
attribute [local instance] OAI.ContingencyTables.CompanionOuterPhaseProgram.instCodecProdPreparedStored
attribute [local instance] OAI.ContingencyTables.CompanionOuterPhaseProgram.instCodecRequest
attribute [local instance] OAI.ContingencyTables.CompanionOuterPhaseProgram.instCodecInput_1
lemma polynomial_history : PolynomialTime historyRealizer :=
  polynomial_composition polynomial_first polynomial_second

lemma polynomial_phase : PolynomialTime phaseRealizer :=
  polynomial_composition polynomial_history polynomial_listLength

lemma polynomial_old : PolynomialTime oldRealizer := by
  unfold oldRealizer
  apply polynomial_congr
  exact polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_phase (polynomial_constant 0)) polynomial_natEqual)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_pair polynomial_history
      (polynomial_composition (polynomial_pair polynomial_phase (polynomial_constant 1)) polynomial_subtract))
      (polynomial_getDFast default))

lemma polynomial_reserve : PolynomialTime reserveRealizer :=
  polynomial_composition polynomial_second (polynomial_map (polynomial_constant false))

lemma polynomial_contextInput : PolynomialTime contextInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_phase)
      polynomial_second) polynomial_add)) (polynomial_composition polynomial_first polynomial_reserve)

lemma polynomial_configAt (i : ℕ) : PolynomialTime (configAtRealizer i) :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant i))
    polynomial_contextInput) CompanionPhaseContextProgram.polynomial_config

lemma polynomial_restartRequest : PolynomialTime restartRequestRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_first) polynomial_history

lemma polynomial_restartWidth : PolynomialTime restartWidthRealizer :=
  polynomial_composition polynomial_restartRequest CompanionRestartSchedule.polynomial_width

lemma polynomial_restartInput : PolynomialTime restartInputRealizer :=
  polynomial_pair polynomial_restartRequest polynomial_second

lemma polynomial_startCode : PolynomialTime startCodeRealizer :=
  polynomial_composition polynomial_restartInput CompanionInitializedRestartProgram.polynomial_output

lemma polynomial_parameters : PolynomialTime parametersRealizer :=
  polynomial_composition (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
    polynomial_first) polynomial_second

lemma polynomial_precision : PolynomialTime precisionRealizer :=
  polynomial_composition polynomial_parameters CountingPhaseParametersProgram.polynomial_precision

lemma polynomial_observations : PolynomialTime observationsRealizer :=
  polynomial_composition polynomial_parameters CountingPhaseParametersProgram.polynomial_observations

attribute [local irreducible] old startCode configAt

lemma polynomial_walkState : PolynomialTime walkStateRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair (polynomial_pair (polynomial_configAt 0)
    (polynomial_composition polynomial_old polynomial_first)) polynomial_precision) polynomial_startCode)
    polynomial_startCode

lemma polynomial_widthInput : PolynomialTime widthInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition (polynomial_composition polynomial_walkState
    polynomial_first) polynomial_first) (polynomial_composition polynomial_walkState polynomial_second))
    (polynomial_constant [])

lemma polynomial_trajectoryWidth : PolynomialTime trajectoryWidthRealizer :=
  polynomial_composition (polynomial_pair polynomial_observations
    (polynomial_composition polynomial_widthInput CompanionTransitionWidth.polynomial_width)) polynomial_multiply

lemma polynomial_afterRestart : PolynomialTime afterRestartRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_restartWidth) polynomial_dropFast

lemma polynomial_trajectoryInput : PolynomialTime trajectoryInputRealizer :=
  polynomial_pair (polynomial_pair polynomial_walkState polynomial_observations)
    (polynomial_composition (polynomial_pair polynomial_afterRestart polynomial_trajectoryWidth) polynomial_takeFast)

lemma polynomial_trialInput : PolynomialTime trialInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair (polynomial_pair (polynomial_configAt 0)
    (polynomial_configAt 1)) polynomial_old) polynomial_trajectoryInput)
    (polynomial_composition (polynomial_pair polynomial_afterRestart polynomial_trajectoryWidth) polynomial_dropFast)

attribute [local irreducible] trialInput

lemma polynomial_fallback : PolynomialTime fallbackRealizer := by
  unfold fallbackRealizer
  apply polynomial_congr
  exact polynomial_optionCases polynomial_identity polynomial_second

lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair polynomial_old (polynomial_composition polynomial_trialInput
    CompanionPhaseTrialProgram.polynomial_output)) polynomial_fallback

end ContingencyTables.CompanionOuterPhaseProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionCodeBounds
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Encoded profile bounds independent of learned multiplier sizes -/
namespace ContingencyTables.CompanionCodeBounds
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma restart_next (i : ℕ) (s : CompanionRestartProgram.State) :
    weight (CompanionRestartProgram.next (i,s)) ≤ 6*s.1.1.2.length+1 := by
  simpa only [CompanionRestartProgram.next,CompanionRestartProgram.bound,Nat.size_one, Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using
    ProfilePrograms.capView_weight s.1.1.2.length 1 (CompanionRestartProgram.candidate (i,s))

lemma restart_fold (is : List ℕ) (s : CompanionRestartProgram.State) :
    weight ((is.foldl (fun s i => CompanionRestartProgram.advance (i,s)) s).2) ≤
      max (weight s.2) (6*s.1.1.2.length+1) := by
  induction is using List.reverseRecOn with
  | nil => exact le_max_left _ _
  | append_singleton is i _ =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply (restart_next _ _).trans
    rw [CompanionRestartProgram.fold_fixed]
    exact le_max_right _ _

lemma restart_output (z : CompanionRestartProgram.Input) :
    weight (CompanionRestartProgram.output z) ≤ 7*weight z.1.2+1 := by
  have h := restart_fold (CompanionRestartProgram.indices z) (z,z.1.2)
  change weight (CompanionRestartProgram.output z) ≤ _ at h
  dsimp only at h
  have hl := list_length_le_weight z.1.2
  exact h.trans (max_le (by omega) (by omega))

lemma initialized_output (z : CompanionInitializedRestartProgram.Input) :
    weight (CompanionInitializedRestartProgram.output z) ≤
      7*weight (CompanionInitializedRestartProgram.initialCode z)+1 :=
  restart_output (CompanionInitializedRestartProgram.prepare z)

lemma walk_next (bits : List Bool) (s : CompanionBoundedWalkProgram.State) :
    weight (CompanionBoundedWalkProgram.next (bits,s)) ≤ 6*s.1.2.length+1 := by
  simpa only [CompanionBoundedWalkProgram.next,CompanionBoundedWalkProgram.bound,Nat.size_one,Nat.reduceMul,Nat.reduceAdd,Nat.mul_comm] using
    ProfilePrograms.capView_weight s.1.2.length 1 (CompanionBoundedWalkProgram.candidate (bits,s))

lemma record_bound (words : List (List Bool)) (s : CompanionBoundedWalkProgram.RecordState)
    (B : ℕ) (hc : weight s.1.2 ≤ B) (hf : 6*s.1.1.2.length+1 ≤ B)
    (hh : ∀ code∈s.2,weight code ≤ B) :
    let out := words.foldl (fun s bits => CompanionBoundedWalkProgram.recordAdvance (bits,s)) s
    (∀ code∈out.2,weight code ≤ B) ∧ out.2.length=s.2.length+words.length := by
  induction words generalizing s with
  | nil => exact ⟨hh,by simp⟩
  | cons word words ih =>
    have hn := (walk_next word s.1).trans hf
    have h := ih (CompanionBoundedWalkProgram.recordAdvance (word,s)) hn hf (by
      intro code hcode
      rcases List.mem_cons.mp hcode with he | he
      · subst code; exact hn
      · exact hh code he)
    exact ⟨h.1,by simpa only [List.foldl_cons,CompanionBoundedWalkProgram.recordAdvance,
      List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.2⟩

lemma history_bound (s : CompanionBoundedWalkProgram.State) (words : List (List Bool))
    (B : ℕ) (hc : weight s.2 ≤ B) (hf : 6*s.1.2.length+1 ≤ B) :
    (∀ code∈CompanionBoundedWalkProgram.history (s,words),weight code ≤ B) ∧
      (CompanionBoundedWalkProgram.history (s,words)).length=words.length+1 := by
  have h := record_bound words (s,[s.2]) B hc hf (by simpa only [List.mem_singleton] using
    fun code he => he ▸ hc)
  constructor
  · intro code hcode
    exact h.1 code (List.mem_reverse.mp hcode)
  · simpa only [CompanionBoundedWalkProgram.history,CompanionBoundedWalkProgram.recordWalk,
      CompanionBoundedWalkProgram.initialRecord,List.length_reverse,List.length_cons,List.length_nil,
      Nat.add_comm] using h.2

lemma trajectory_length (z : CompanionTrajectoryProgram.Input) :
    (CompanionTrajectoryProgram.output z).length ≤ z.2.length+1 := by
  let s := z.1.1
  let words := CompanionFlatReturnProgram.words z
  have h := history_bound s words (weight s.2+6*s.1.2.length+1) (by omega) (by omega)
  have hlen : (CompanionTrajectoryProgram.output z).length=words.length+1 := h.2
  have hl : words.length ≤ z.2.length := by
    unfold words CompanionFlatReturnProgram.words DensePrograms.wordChunks DensePrograms.completeWordRows
    simp only [List.length_take,List.length_map,List.length_range]
    exact (min_le_right _ _).trans (Nat.div_le_self _ _)
  omega

lemma trajectory_codes (z : CompanionTrajectoryProgram.Input) (B : ℕ)
    (hc : weight z.1.1.2 ≤ B) (hf : 6*z.1.1.1.2.length+1 ≤ B) :
    ∀ code∈CompanionTrajectoryProgram.output z,weight code ≤ B :=
  (history_bound z.1.1 (CompanionFlatReturnProgram.words z) B hc hf).1

end ContingencyTables.CompanionCodeBounds

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionFractionSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Additive binary-size bounds for stored phase arithmetic -/
namespace ContingencyTables.CompanionFractionSize
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierProgram CompanionPhaseCounts

lemma height_mul (a b : TreeFraction.Fraction) :
    TreeFraction.height (TreeFraction.mul (a,b)) ≤ TreeFraction.height a+TreeFraction.height b+1 := by
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

lemma height_div (a b : TreeFraction.Fraction) :
    TreeFraction.height (TreeFraction.div (a,b)) ≤ TreeFraction.height a+TreeFraction.height b+1 := by
  have hn := TreeFraction.normalize_size_num (a.1*b.2,a.2*b.1)
  have hd := TreeFraction.normalize_size_den (a.1*b.2,a.2*b.1)
  have hnum := nat_size_mul a.1 b.2
  have hden := nat_size_mul a.2 b.1
  have ha := le_max_left a.1.size a.2.size
  have ha' := le_max_right a.1.size a.2.size
  have hb := le_max_left b.1.size b.2.size
  have hb' := le_max_right b.1.size b.2.size
  dsimp only at hn hd
  change (TreeFraction.div (a,b)).1.size ≤ _ at hn
  change (TreeFraction.div (a,b)).2.size ≤ _ at hd
  unfold TreeFraction.height
  apply max_le <;> omega

lemma countRatio_height (z : DefectCountInput) : TreeFraction.height (countRatio z) ≤ z.1.2.length := by
  have hp : plainCountCode z.1 ≤ z.1.2.length := List.length_filter_le _ _
  have hd : defectCountCode z ≤ z.1.2.length := List.length_filter_le _ _
  have hs (n : ℕ) : n.size ≤ n := Nat.size_le.mpr Nat.lt_two_pow_self
  exact max_le ((hs _).trans hp) ((hs _).trans hd)

lemma updateCode_height (z : UpdateInput) :
    TreeFraction.height (updateCode z) ≤ TreeFraction.height z.2+z.1.1.2.length+1 := by
  unfold updateCode
  split_ifs
  · omega
  · exact (height_mul _ _).trans (Nat.add_le_add_right
      (Nat.add_le_add_left (countRatio_height _) _) 1)

lemma sum_height (xs : List TreeFraction.Fraction) (M : ℕ)
    (hm : ∀ x∈xs,TreeFraction.height x ≤ M) :
    TreeFraction.height (TreeFraction.sum xs) ≤ 1+xs.length*(M+2) := by
  simpa only [TreeFraction.sum,TreeFraction.height,Nat.size_zero,Nat.size_one,Nat.zero_max] using
    TreeFraction.fractionFold_height xs (0,1) M hm

lemma term_height (z : CompanionPhaseFinishProgram.TermInput) (M : ℕ)
    (h₁ : TreeFraction.height z.2.1 ≤ M) (h₂ : TreeFraction.height z.2.2 ≤ M) :
    TreeFraction.height (CompanionPhaseFinishProgram.term z) ≤ 2*M+1 := by
  unfold CompanionPhaseFinishProgram.term
  split_ifs
  · have h := height_div z.2.2 z.2.1
    omega
  · norm_num [TreeFraction.height]

end ContingencyTables.CompanionFractionSize

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionOuterHistoryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Chronological execution of all counting phases -/
namespace ContingencyTables.CompanionOuterHistoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped
attribute [local instance] OAI.ContingencyTables.CompanionOuterHistoryProgram.instCodecFixed
attribute [local instance] OAI.ContingencyTables.CompanionOuterHistoryProgram.instCodecState
attribute [local instance] OAI.ContingencyTables.CompanionOuterHistoryProgram.instCodecInput
lemma polynomial_phaseInput : PolynomialTime phaseInputRealizer :=
  polynomial_pair polynomial_second polynomial_first

lemma polynomial_next : PolynomialTime nextRealizer :=
  polynomial_composition polynomial_phaseInput CompanionOuterPhaseProgram.polynomial_output

lemma polynomial_advance : PolynomialTime advanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
      (polynomial_composition (polynomial_pair polynomial_next (polynomial_constant [])) polynomial_listCons))
      polynomial_append)

end ContingencyTables.CompanionOuterHistoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStoredSize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A phase adds a bounded amount to each stored fraction's binary height -/
namespace ContingencyTables.CompanionStoredSize
open MatchingFPRAS CompanionFractionSize CompanionMultiplierMatrixProgram
open CompanionPhaseFinishProgram CompanionMultiplierProgram CompanionPhaseCounts

private lemma getD_property {X : Type} (P : X→Prop) (xs : List X) (i : ℕ) (d : X)
    (hx : ∀ x∈xs,P x) (hd : P d) : P (xs.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : xs[i]? with
  | none => exact hd
  | some x => exact hx x (List.mem_of_getElem? he)

lemma readEntry_height (M : ℕ) (hM : 1 ≤ M) (w : FractionMatrix) (hw : MatrixHeight M w)
    (ij : ℕ×ℕ) : TreeFraction.height (readEntry (w,ij)) ≤ M := by
  have hr : ∀ x∈w.getD ij.1 [],TreeFraction.height x ≤ M :=
    getD_property (fun row => ∀ x∈row,TreeFraction.height x ≤ M) w ij.1 [] hw
      (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true])
  exact getD_property (fun x => TreeFraction.height x ≤ M) _ ij.2 (0,1) hr
    (by simpa only [TreeFraction.height,Nat.size_zero,Nat.size_one,Nat.zero_max] using hM)

lemma updateMatrix_height (M : ℕ) (hM : 1 ≤ M) (z : CompanionMultiplierMatrixProgram.Input)
    (hw : MatrixHeight M z.2) : MatrixHeight (M+z.1.2.length+1) (updateMatrix z) := by
  intro row hr x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  change TreeFraction.height (updateCode ((z.1,(i,j)),readEntry (z.2,(i,j)))) ≤ _
  exact (updateCode_height _).trans (by
    have h := readEntry_height M hM z.2 hw (i,j)
    dsimp only
    omega)

lemma terms_length (z : CompanionPhaseFinishProgram.Input) :
    (terms z).length=(trajectory z).2.length := by
  simp only [terms,CompanionPhaseFinishProgram.indices,List.length_map,List.length_range]

lemma terms_height (z : CompanionPhaseFinishProgram.Input) (V : ℕ) (hV : 1 ≤ V)
    (hv : ∀ x∈z.2,TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V) :
    ∀ x∈terms z,TreeFraction.height x ≤ 2*V+1 := by
  intro x hx
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
  have hb := getD_property
    (fun x : TreeFraction.Fraction×TreeFraction.Fraction =>
      TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V)
    z.2 i ((0,1),(0,1)) hv (by
      simpa only [TreeFraction.height,Nat.size_zero,Nat.size_one,Nat.zero_max,and_self] using hV)
  exact term_height (termInput (z,i)) V hb.1 hb.2

lemma ratio_height (z : CompanionPhaseFinishProgram.Input) (V : ℕ) (hV : 1 ≤ V)
    (hv : ∀ x∈z.2,TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V) :
    TreeFraction.height (ratio z) ≤ (trajectory z).2.length*(2*V+3)+(trajectory z).2.length+3 := by
  have ht := sum_height (terms z) (2*V+1) (terms_height z V hV hv)
  rw [terms_length] at ht
  have hconst : 2*V+1+2=2*V+3 := by omega
  rw [hconst] at ht
  have hc : TreeFraction.height (count z) ≤ (trajectory z).2.length+1 := by
    have hp : plainCountCode (trajectory z) ≤ (trajectory z).2.length := List.length_filter_le _ _
    have hs : (plainCountCode (trajectory z)).size ≤ plainCountCode (trajectory z) :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    change max (plainCountCode (trajectory z)).size (1:ℕ).size ≤ _
    norm_num only [Nat.size_one]
    omega
  have hr := height_div (total z) (count z)
  change TreeFraction.height (ratio z) ≤ _ at hr
  change TreeFraction.height (total z) ≤ _ at ht
  omega

/-- This bound is additive in the old stored height; iterating phases
therefore preserves a polynomial representation size. -/
lemma next_height (z : CompanionPhaseFinishProgram.Input) (M V : ℕ) (hM : 1 ≤ M) (hV : 1 ≤ V)
    (hw : MatrixHeight M z.1.1.2) (he : TreeFraction.height z.1.2 ≤ M)
    (hv : ∀ x∈z.2,TreeFraction.height x.1 ≤ V ∧ TreeFraction.height x.2 ≤ V) :
    StoredHeight (M+(trajectory z).2.length*(2*V+3)+(trajectory z).2.length+5) (next z) := by
  constructor
  · have hm := updateMatrix_height M hM z.1.1 hw
    intro row hr x hx
    have h := hm row hr x hx
    change TreeFraction.height x ≤ M+(trajectory z).2.length+1 at h
    omega
  · have hr := ratio_height z V hV hv
    have hm := height_mul z.1.2 (ratio z)
    change TreeFraction.height (estimate z) ≤ _ at hm
    change TreeFraction.height (estimate z) ≤ _
    omega

end ContingencyTables.CompanionStoredSize

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionStoredShape
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Height and shape invariants for chronological stored values -/
namespace ContingencyTables.CompanionStoredSize
open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram
open CompanionPhaseFinishProgram

lemma height_mono {M N : ℕ} (h : M ≤ N) {s : Stored} (hs : StoredHeight M s) : StoredHeight N s :=
  ⟨fun row hr x hx => (hs.1 row hr x hx).trans h,hs.2.trans h⟩

lemma shape_mono {M N : ℕ} (h : M ≤ N) {s : Stored} (hs : StoredShape M s) : StoredShape N s :=
  ⟨hs.1.trans h,fun row hr => (hs.2 row hr).trans h⟩

lemma shape_of_weight (s : Stored) : StoredShape (weight s) s := by
  refine ⟨(list_length_le_weight _).trans (weight_fst s),?_⟩
  intro row hr
  exact (list_length_le_weight _).trans ((weight_mem hr).trans (weight_fst s))

lemma height_of_weight (s : Stored) : StoredHeight (weight s) s := by
  refine ⟨?_,(TreeFraction.height_le_weight _).trans (weight_snd s)⟩
  intro row hr x hx
  exact (TreeFraction.height_le_weight _).trans
    ((weight_mem hx).trans ((weight_mem hr).trans (weight_fst s)))

lemma weight_of_bounds (s : Stored) (R M : ℕ) (hR : StoredShape R s) (hM : StoredHeight M s) :
    weight s ≤ R*(R*(8*M+4)+2)+8*M+5 := by
  have rows (row : List TreeFraction.Fraction) (hr : row∈s.1) :
      weight row ≤ R*(8*M+4)+1 := by
    have h := weight_map_bound (f := id) (as := row) (N := 8*M+3) (by
      intro x hx
      exact (TreeFraction.weight_le_height x).trans (by have := hM.1 row hr x hx; omega))
    simp only [List.map_id] at h
    exact h.trans (by gcongr; exact hR.2 row hr)
  have h := weight_map_bound (f := id) (as := s.1) (N := R*(8*M+4)+1) rows
  simp only [List.map_id] at h
  have hm := TreeFraction.weight_le_height s.2
  have hn : weight s.1 ≤ R*(R*(8*M+4)+2)+1 := h.trans (by gcongr; exact hR.1)
  conv_lhs => rw [show s=(s.1,s.2) from rfl,weight_prod]
  nlinarith [hM.2]

lemma next_shape (z : CompanionPhaseFinishProgram.Input) :
    StoredShape (trajectory z).1.length (next z) := by
  constructor
  · simp only [next,updateMatrix,CompanionMultiplierMatrixProgram.indices,List.length_map,
      List.length_range]
    exact le_rfl
  · intro row hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    simp only [updateRow,CompanionMultiplierMatrixProgram.indices,List.length_map,List.length_range]
    exact le_rfl

end ContingencyTables.CompanionStoredSize

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionPhaseSize
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Phase query sizes do not depend on the heights of old multipliers -/
namespace ContingencyTables.CompanionPhaseSize
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open CompanionOuterPhaseProgram

lemma list_weight_bound {X : Type} [Codec X] (xs : List X) (B : ℕ)
    (hx : ∀ x∈xs,weight x ≤ B) : weight xs ≤ xs.length*(B+1)+1 := by
  have h := weight_map_bound (f := id) (as := xs) hx
  simpa only [List.map_id] using h

lemma initialInput_bound (z : Input) :
    weight (CompanionInitializedRestartProgram.initialInput (restartInput z)) ≤
      weight (z.1.1.1,z.2) := by
  have ht := weight_sublist (List.take_sublist
    (CompanionInitializedRestartProgram.initialWidth (restartInput z)) z.2)
  change weight (z.1.1.1,z.2.take _) ≤ weight (z.1.1.1,z.2)
  simp only [weight_prod]
  omega

lemma start_bound : ∃ p : Polynomial ℕ,∀ z : Input,
    weight (startCode z) ≤ p.eval (weight (z.1.1.1,z.2)) := by
  obtain ⟨p,hp⟩ := CompanionRestartInitializer.polynomial_output
  refine ⟨7*p+1,?_⟩
  intro z
  have hi := hp (CompanionInitializedRestartProgram.initialInput (restartInput z))
  have hm := polynomial_eval_monotone p (initialInput_bound z)
  dsimp only at hm
  have hs := CompanionCodeBounds.initialized_output (restartInput z)
  change weight (startCode z) ≤ _ at hs
  change _+weight (CompanionInitializedRestartProgram.initialCode (restartInput z)) ≤ _ at hi
  simp only [eval_add,eval_mul,eval_ofNat,eval_one]
  omega

lemma config_bound : ∃ p : Polynomial ℕ,∀ (z : Input) (S : ℕ),
    weight z.1.1.1 ≤ S → z.2.length ≤ S → (history z).length ≤ S →
      weight (configAt 0 z) ≤ p.eval S ∧ weight (configAt 1 z) ≤ p.eval S := by
  obtain ⟨p,hp⟩ := CompanionPhaseContextProgram.polynomial_config
  refine ⟨p.comp (9*X+12),?_⟩
  intro z S hprep hbits hhist
  have hreserve : weight (reserve z) ≤ 4*S+1 := by
    have h := weight_map_bound (f := fun _ : Bool => false) (as := z.2)
      (fun _ _ => weight_bool false)
    change weight (reserve z) ≤ _ at h
    omega
  have hb (i : ℕ) (hi : i ≤ 1) : weight (contextInput (z,i)) ≤ 9*S+12 := by
    have hj := weight_nat_numeric (phase z+i)
    have hlen : phase z ≤ S := hhist
    change weight ((z.1.1.1,phase z+i),reserve z) ≤ _
    simp only [weight_prod]
    omega
  constructor
  · have h := hp (contextInput (z,0))
    have hm := polynomial_eval_monotone p (hb 0 (by omega))
    dsimp only at hm
    simp only [eval_comp,eval_add,eval_mul,eval_ofNat,eval_X]
    change _+weight (configAt 0 z) ≤ _ at h
    omega
  · have h := hp (contextInput (z,1))
    have hm := polynomial_eval_monotone p (hb 1 (by omega))
    dsimp only at hm
    simp only [eval_comp,eval_add,eval_mul,eval_ofNat,eval_X]
    change _+weight (configAt 1 z) ≤ _ at h
    omega

lemma trajectory_bounds : ∃ p : Polynomial ℕ,∀ (z : Input) (S : ℕ),
    weight z.1.1.1 ≤ S → weight z.2 ≤ S →
      (CompanionPhaseTrialProgram.trajectory (trialInput z)).length ≤ S+1 ∧
      (∀ code∈CompanionPhaseTrialProgram.trajectory (trialInput z),weight code ≤ p.eval S) ∧
      (CompanionPhaseTrialProgram.catalogue (trialInput z)).length ≤ p.eval S := by
  obtain ⟨p,hp⟩ := start_bound
  refine ⟨6*(p.comp (1+2*X))+1,?_⟩
  intro z S hprep hbits
  have harg : weight (z.1.1.1,z.2) ≤ 1+2*S := by simp only [weight_prod]; omega
  have hstart : weight (startCode z) ≤ p.eval (1+2*S) :=
    (hp z).trans (polynomial_eval_monotone p harg)
  have hsize : (startCode z).length ≤ p.eval (1+2*S) :=
    (list_length_le_weight _).trans hstart
  have hc := CompanionCodeBounds.trajectory_codes (trajectoryInput z) (6*p.eval (1+2*S)+1)
    (by change weight (startCode z) ≤ _; omega)
    (by change 6*(startCode z).length+1 ≤ _; omega)
  have hl := CompanionCodeBounds.trajectory_length (trajectoryInput z)
  have hlen : (trajectoryInput z).2.length ≤ S := by
    have h := list_length_le_weight z.2
    change ((z.2.drop _).take _).length ≤ S
    simp only [List.length_take,List.length_drop]
    omega
  refine ⟨by change (CompanionTrajectoryProgram.output (trajectoryInput z)).length ≤ _; omega,?_,?_⟩
  · change ∀ code∈CompanionTrajectoryProgram.output (trajectoryInput z),weight code ≤ _
    simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_comp,eval_X] using hc
  · change (PairedCatalogProgram.catalog (startCode z)).length ≤ _
    simp only [PairedCatalogProgram.catalog,List.length_map,List.length_range,
      eval_add,eval_mul,eval_ofNat,eval_one,eval_comp,eval_X]
    have hd := Nat.div_le_self (startCode z).length 2
    omega


lemma query_bound : ∃ q : Polynomial ℕ,∀ (z : Input) (S : ℕ),
    weight z.1.1.1 ≤ S → weight z.2 ≤ S → (history z).length ≤ S →
      weight (CompanionObservationQueriesProgram.output
        (CompanionObservedUpdateProgram.queryInput
          (CompanionPhaseTrialProgram.updateInput (trialInput z)))) ≤ q.eval S := by
  obtain ⟨p,hp⟩ := config_bound
  obtain ⟨r,hr⟩ := trajectory_bounds
  obtain ⟨q,hq⟩ := CompanionObservationQueriesProgram.polynomial_output
  refine ⟨q.comp (2*p+(X+1)*(r+1)+X+5),?_⟩
  intro z S hprep hbits hhist
  have hb : z.2.length ≤ S := (list_length_le_weight _).trans hbits
  have hc := hp z S hprep hb hhist
  have ht := hr z S hprep hbits
  have hcodes := list_weight_bound _ (r.eval S) ht.2.1
  have hcodeweight : weight (CompanionPhaseTrialProgram.trajectory (trialInput z)) ≤
      (S+1)*(r.eval S+1)+1 := hcodes.trans (by gcongr; exact ht.1)
  have htail : weight ((afterRestart z).drop (trajectoryWidth z)) ≤ S :=
    ((weight_sublist (List.drop_sublist _ _)).trans
      (weight_sublist (List.drop_sublist _ _))).trans hbits
  have hin : weight (CompanionObservedUpdateProgram.queryInput
      (CompanionPhaseTrialProgram.updateInput (trialInput z))) ≤
      2*p.eval S+(S+1)*(r.eval S+1)+S+5 := by
    change weight ((configAt 0 z,configAt 1 z),
      (CompanionPhaseTrialProgram.trajectory (trialInput z),
        (afterRestart z).drop (trajectoryWidth z))) ≤ _
    simp only [weight_prod]
    omega
  have hout := hq (CompanionObservedUpdateProgram.queryInput
    (CompanionPhaseTrialProgram.updateInput (trialInput z)))
  have hm := polynomial_eval_monotone q hin
  simp only [eval_comp,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  exact (Nat.le_add_left _ _).trans (hout.trans hm)



open CompanionStoredSize

/-- A uniform additive increment and dimension bound for an entire phase.
The polynomial depends only on immutable data, word length and phase number. -/
lemma phase_bounds : ∃ p : Polynomial ℕ,∀ (z : Input) (S M R : ℕ),
    weight z.1.1.1 ≤ S → weight z.2 ≤ S → (history z).length ≤ S → 1 ≤ M →
    StoredHeight M (old z) → StoredShape R (old z) → p.eval S ≤ R →
      StoredHeight (M+p.eval S) (output z) ∧ StoredShape R (output z) := by
  obtain ⟨q,hq⟩ := query_bound
  obtain ⟨r,hr⟩ := trajectory_bounds
  let p := r+(X+1)*(2*(q+1)+3)+(X+1)+5
  refine ⟨p,?_⟩
  intro z S M R hprep hbits hhist hM hm hshape hR
  let d := CompanionObservedUpdateProgram.finishInput
    (CompanionPhaseTrialProgram.updateInput (trialInput z))
  have ht := hr z S hprep hbits
  have hq' := hq z S hprep hbits hhist
  have hv : ∀ x∈d.2,TreeFraction.height x.1 ≤ q.eval S+1 ∧
      TreeFraction.height x.2 ≤ q.eval S+1 := by
    intro x hx
    have hxw : weight x ≤ q.eval S := (weight_mem hx).trans hq'
    exact ⟨(TreeFraction.height_le_weight _).trans ((weight_fst x).trans (by omega)),
      (TreeFraction.height_le_weight _).trans ((weight_snd x).trans (by omega))⟩
  have hn := next_height d M (q.eval S+1) hM (by omega) hm.1 hm.2 hv
  have hlen : (CompanionPhaseFinishProgram.trajectory d).2.length ≤ S+1 := ht.1
  have hp : r.eval S+(S+1)*(2*(q.eval S+1)+3)+(S+1)+5=p.eval S := by
    simp only [p,eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  have hmul := Nat.mul_le_mul_right (2*(q.eval S+1)+3) hlen
  have hn' : StoredHeight (M+p.eval S) (CompanionPhaseFinishProgram.next d) :=
    height_mono (by omega) hn
  have hns := next_shape d
  have hcat : (CompanionPhaseFinishProgram.trajectory d).1.length ≤ r.eval S := ht.2.2
  have hns' : StoredShape R (CompanionPhaseFinishProgram.next d) :=
    shape_mono (hcat.trans (by omega)) hns
  change StoredHeight (M+p.eval S) ((CompanionPhaseFinishProgram.output d).getD (old z)) ∧
    StoredShape R ((CompanionPhaseFinishProgram.output d).getD (old z))
  unfold CompanionPhaseFinishProgram.output
  split_ifs
  · exact ⟨hn',hns'⟩
  · exact ⟨height_mono (Nat.le_add_right M _) hm,hshape⟩

end ContingencyTables.CompanionPhaseSize

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionHistorySize
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial stored size throughout the adaptive history fold -/
namespace ContingencyTables.CompanionOuterHistoryProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial CompanionStoredSize

private lemma getD_property {X : Type} (P : X→Prop) (xs : List X) (i : ℕ) (d : X)
    (hx : ∀ x∈xs,P x) (hd : P d) : P (xs.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases he : xs[i]? with
  | none => exact hd
  | some x => exact hx x (List.mem_of_getElem? he)

lemma old_property (P : Stored→Prop) (state : State) (bits : List Bool)
    (hi : P state.1.2) (hs : ∀ s∈state.2,P s) (hd : P default) :
    P (CompanionOuterPhaseProgram.old (state,bits)) := by
  unfold CompanionOuterPhaseProgram.old
  split_ifs
  · exact hi
  · exact getD_property P state.2 _ default hs hd

lemma default_height (M : ℕ) : StoredHeight M (default : Stored) := by
  constructor
  · intro row hr
    exact False.elim (List.not_mem_nil hr)
  · change max (0:ℕ).size (0:ℕ).size ≤ M
    simp only [Nat.size_zero,max_self,Nat.zero_le]

lemma default_shape (R : ℕ) : StoredShape R (default : Stored) := by
  exact ⟨Nat.zero_le _,fun row hr => False.elim (List.not_mem_nil hr)⟩

lemma fold_length (words : List (List Bool)) (state : State) :
    (words.foldl (fun s bits => advance (bits,s)) state).2.length=state.2.length+words.length := by
  induction words generalizing state with
  | nil => simp
  | cons word words ih =>
    simp only [List.foldl_cons]
    rw [ih]
    change (state.2++[next (word,state)]).length+words.length=state.2.length+(word::words).length
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega

lemma fold_fixed (words : List (List Bool)) (state : State) :
    (words.foldl (fun s bits => advance (bits,s)) state).1=state.1 := by
  induction words generalizing state with
  | nil => rfl
  | cons word words ih => exact ih _

lemma fold_bounds (p : Polynomial ℕ)
    (hp : ∀ (z : CompanionOuterPhaseProgram.Input) (S M R : ℕ),
      weight z.1.1.1 ≤ S → weight z.2 ≤ S → z.1.2.length ≤ S → 1 ≤ M →
      StoredHeight M (CompanionOuterPhaseProgram.old z) →
      StoredShape R (CompanionOuterPhaseProgram.old z) → p.eval S ≤ R →
      StoredHeight (M+p.eval S) (CompanionOuterPhaseProgram.output z) ∧
        StoredShape R (CompanionOuterPhaseProgram.output z))
    (words : List (List Bool)) (state : State) (S M R : ℕ)
    (hprep : weight state.1.1 ≤ S) (hwords : ∀ bits∈words,weight bits ≤ S)
    (hlen : state.2.length+words.length ≤ S) (hM : 1 ≤ M)
    (hi : StoredHeight M state.1.2) (hs : ∀ s∈state.2,StoredHeight M s)
    (hri : StoredShape R state.1.2) (hrs : ∀ s∈state.2,StoredShape R s)
    (hR : p.eval S ≤ R) :
    let out := words.foldl (fun s bits => advance (bits,s)) state
    StoredHeight (M+words.length*p.eval S) out.1.2 ∧
      (∀ s∈out.2,StoredHeight (M+words.length*p.eval S) s) ∧
      StoredShape R out.1.2 ∧ (∀ s∈out.2,StoredShape R s) := by
  induction words generalizing state M with
  | nil => simpa only [List.foldl_nil,List.length_nil,Nat.zero_mul,Nat.add_zero] using ⟨hi,hs,hri,hrs⟩
  | cons word words ih =>
    have hmold := old_property (StoredHeight M) state word hi hs (default_height M)
    have hrold := old_property (StoredShape R) state word hri hrs (default_shape R)
    have hn := hp (state,word) S M R hprep (hwords word (by simp)) (by
      change state.2.length ≤ S
      simp only [List.length_cons] at hlen
      omega) hM hmold hrold hR
    have hnew : ∀ s∈(advance (word,state)).2,StoredHeight (M+p.eval S) s := by
      intro s hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact height_mono (Nat.le_add_right _ _) (hs s hmem)
      · have he := List.mem_singleton.mp hmem
        subst s
        exact hn.1
    have hrnew : ∀ s∈(advance (word,state)).2,StoredShape R s := by
      intro s hmem
      rcases List.mem_append.mp hmem with hmem | hmem
      · exact hrs s hmem
      · have he := List.mem_singleton.mp hmem
        subst s
        exact hn.2
    have hh := ih (advance (word,state)) (M+p.eval S) hprep
      (fun bits hb => hwords bits (by simp [hb]))
      (by simpa only [advance,List.length_append,List.length_singleton,List.length_cons,List.length_nil,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hlen)
      (by omega) (height_mono (Nat.le_add_right _ _) hi) hnew hri hrnew
    simpa only [List.foldl_cons,List.length_cons,Nat.add_mul,Nat.one_mul,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh


/-- The loop's live representation has a fixed polynomial bound even on
malformed inputs; the only changing numeric values are additive-height fractions. -/
theorem polynomial_historyFold : PolynomialTime (fold advanceRealizer) := by
  obtain ⟨p,hp⟩ := CompanionPhaseSize.phase_bounds
  let s : Polynomial ℕ := 2*X+1
  let r : Polynomial ℕ := s+p.comp s
  let h : Polynomial ℕ := s+s*(p.comp s)
  let w : Polynomial ℕ := r*(r*(8*h+4)+2)+8*h+5
  let out : Polynomial ℕ := 2+s+s*(w+1)
  apply polynomial_fold polynomial_advance out
  intro words state pre post he
  let B := weight (words,state)
  let S := 2*B+1
  let R := S+p.eval S
  let M := S+S*p.eval S
  have hstate : weight state ≤ B := weight_snd (words,state)
  have hwords : weight words ≤ B := weight_fst (words,state)
  have hpre : pre.length ≤ B :=
    (list_length_le_weight pre).trans ((weight_prefix he).trans hwords)
  have histlen : state.2.length ≤ B :=
    (list_length_le_weight _).trans ((weight_snd state).trans hstate)
  have hprep : weight state.1.1 ≤ S :=
    ((weight_fst state.1).trans ((weight_fst state).trans hstate)).trans (by dsimp [S]; omega)
  have hmem : ∀ bits∈pre,weight bits ≤ S := by
    intro bits hb
    have hb' : bits∈words := by rw [he]; exact List.mem_append_left post hb
    exact ((weight_mem hb').trans hwords).trans (by dsimp [S]; omega)
  have hn : state.2.length+pre.length ≤ S := by dsimp [S]; omega
  have hinit : StoredHeight S state.1.2 :=
    height_mono (by have := (weight_snd state.1).trans ((weight_fst state).trans hstate); dsimp [S]; omega)
      (height_of_weight _)
  have hinits : ∀ x∈state.2,StoredHeight S x := by
    intro x hx
    have hxw := (weight_mem hx).trans ((weight_snd state).trans hstate)
    exact height_mono (by dsimp [S]; omega) (height_of_weight x)
  have hrinit : StoredShape R state.1.2 :=
    shape_mono (by have := (weight_snd state.1).trans ((weight_fst state).trans hstate); dsimp [R,S]; omega)
      (shape_of_weight _)
  have hrinits : ∀ x∈state.2,StoredShape R x := by
    intro x hx
    have hxw := (weight_mem hx).trans ((weight_snd state).trans hstate)
    exact shape_mono (by dsimp [R,S]; omega) (shape_of_weight x)
  have hp' : ∀ (z : CompanionOuterPhaseProgram.Input) (S M R : ℕ),
      weight z.1.1.1 ≤ S → weight z.2 ≤ S → z.1.2.length ≤ S → 1 ≤ M →
      StoredHeight M (CompanionOuterPhaseProgram.old z) →
      StoredShape R (CompanionOuterPhaseProgram.old z) → p.eval S ≤ R →
      StoredHeight (M+p.eval S) (CompanionOuterPhaseProgram.output z) ∧
        StoredShape R (CompanionOuterPhaseProgram.output z) := hp
  have hb := fold_bounds p hp' pre state S S R hprep hmem hn (by dsimp [S]; omega)
    hinit hinits hrinit hrinits (by dsimp [R]; omega)
  let result := pre.foldl (fun s bits => advance (bits,s)) state
  have hm : S+pre.length*p.eval S ≤ M := by
    have hle : pre.length ≤ S := by dsimp [S]; omega
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hle) S
  have hstored : ∀ x∈result.2,weight x ≤ R*(R*(8*M+4)+2)+8*M+5 := by
    intro x hx
    exact weight_of_bounds x R M (hb.2.2.2 x hx) (height_mono hm (hb.2.1 x hx))
  have hw := weight_map_bound (f := id) (as := result.2) hstored
  simp only [List.map_id] at hw
  have hlen : result.2.length ≤ S := (fold_length pre state).trans_le hn
  have hw' : weight result.2 ≤ S*(R*(R*(8*M+4)+2)+8*M+5+1)+1 :=
    hw.trans (by gcongr)
  have hf : weight result.1 ≤ S := by
    change weight ((pre.foldl (fun s bits => advance (bits,s)) state).1) ≤ S
    rw [fold_fixed]
    exact ((weight_fst state).trans hstate).trans (by dsimp [S]; omega)
  change weight result ≤ out.eval B
  conv_lhs => rw [show result=(result.1,result.2) from rfl,weight_prod]
  have hout : out.eval B=2+S+S*(R*(R*(8*M+4)+2)+8*M+5+1) := by
    simp only [out,w,r,h,s,R,M,S,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
  rw [hout]
  omega

lemma polynomial_run : PolynomialTime runRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_pair polynomial_first (polynomial_constant []))) polynomial_historyFold

lemma polynomial_storedHistory : PolynomialTime storedHistoryRealizer :=
  polynomial_composition polynomial_run polynomial_second

lemma polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair polynomial_first polynomial_storedHistory)
    (polynomial_constant [])) CompanionOuterPhaseProgram.polynomial_old

end ContingencyTables.CompanionOuterHistoryProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionLabelMetadataProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Recovering each paired label's cell and capacity

The multiplicities come from the actual bounded profile blocks. A
large numeric capacity never causes an allocation beyond the supplied
profile code. On a canonical code, the resulting order is exactly the
copy order used by the initializer and arithmetic proposals.
-/

namespace ContingencyTables.CompanionLabelMetadataProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
open PairedProfileProgram PairedFactorialProgram

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_pairCount) X
  intro z
  simpa only [Function.comp_apply,eval_X,pairCount] using
    (Nat.div_le_self z.2.length 2).trans ((list_length_le_weight z.2).trans (weight_snd z))

lemma polynomial_labelRow : PolynomialTime labelRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_pairCount)))

lemma polynomial_rowInput : PolynomialTime rowInputRealizer :=
  polynomial_pair polynomial_second (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_rows) polynomial_second) (polynomial_getDFast []))

lemma polynomial_indexedRow : PolynomialTime indexedRowRealizer :=
  polynomial_composition polynomial_rowInput polynomial_labelRow

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    NaturalBlockProgram.polynomial_indices) (polynomial_mapWith polynomial_indexedRow)) polynomial_flatten

end ContingencyTables.CompanionLabelMetadataProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing the initial canonical multiplier matrix -/

namespace ContingencyTables.CompanionInitialMatrixProgram

open MatchingFPRAS MatchingFPRAS.TreeTyped CompanionMultiplierMatrixProgram

lemma polynomial_numerator : PolynomialTime numeratorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 6)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
      polynomial_successor)) polynomial_multiply

lemma polynomial_denominator : PolynomialTime denominatorRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_constant 2)) polynomial_add

lemma polynomial_sameCell : PolynomialTime sameCellRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_second polynomial_first)) polynomial_natEqual

lemma polynomial_entry : PolynomialTime entryRealizer :=
  polynomial_choose polynomial_sameCell (polynomial_constant (6,1))
    (polynomial_composition (polynomial_pair polynomial_numerator polynomial_denominator)
      TreeFraction.polynomial_normalize)

lemma polynomial_row : PolynomialTime rowRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_first)
    (polynomial_mapWith polynomial_entry)

lemma polynomial_matrix : PolynomialTime matrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
    (polynomial_mapWith polynomial_row)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition CompanionLabelMetadataProgram.polynomial_output polynomial_matrix

end ContingencyTables.CompanionInitialMatrixProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CompanionInitialStoredProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The literal initial count and stored multiplier matrix

The integer count is the product of the free-cell ranges and the small-cell
ranges. Both lists come from the executed forest and cell catalogs.
-/
namespace ContingencyTables.CompanionInitialStoredProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms

lemma polynomial_rangeAt : PolynomialTime rangeAtRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_second)
    polynomial_matrixEntry) polynomial_successor

lemma polynomial_freeRanges : PolynomialTime freeRangesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant false))
      RootedForestCatalog.polynomial_catalog)) (polynomial_mapWith polynomial_rangeAt)

lemma polynomial_freeProduct : PolynomialTime freeProductRealizer :=
  polynomial_composition polynomial_freeRanges polynomial_listProd

lemma polynomial_smallProduct : PolynomialTime smallProductRealizer :=
  polynomial_composition (polynomial_map polynomial_successor) polynomial_listProd

lemma polynomial_total : PolynomialTime totalRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_freeProduct)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_smallProduct)) polynomial_multiply) (polynomial_constant 1)

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair (polynomial_composition polynomial_second
    CompanionInitialMatrixProgram.polynomial_output) polynomial_total

end ContingencyTables.CompanionInitialStoredProgram

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

end ContingencyTables.CompanionUniformPhaseWidth

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingLabelCountProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

lemma polynomial_frame : PolynomialTime frameRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_capacityBits)
    (polynomial_composition polynomial_first polynomial_dimension))
    (polynomial_composition polynomial_second polynomial_half)

lemma polynomial_coefficient : PolynomialTime coefficientRealizer :=
  polynomial_composition polynomial_frame CountingCoefficientProgram.polynomial_coefficient

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

end ContingencyTables.CountingTerminalProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Rooted_ComputedRootedInput
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

end ContingencyTables.ComputedRootedInput

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingComputedSettings
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

end ContingencyTables.CountingComputedSettings

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingPreparedState
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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
end ContingencyTables.FractionRepetitionProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Counting_CountingAdaptiveInputProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original-input preparation for a positive-label counting run -/
namespace ContingencyTables.CountingAdaptiveInputProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_prepared : PolynomialTime preparedRealizer :=
  polynomial_composition polynomial_first CountingPreparedState.polynomial_output

lemma polynomial_capacities : PolynomialTime capacitiesRealizer :=
  polynomial_composition polynomial_prepared CompanionRestartInitializer.polynomial_capacities

lemma polynomial_labelWidth : PolynomialTime labelWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_constant 2)
    (polynomial_composition polynomial_first CountingComputedSettings.polynomial_labelCount)) polynomial_multiply

lemma polynomial_zeroCode : PolynomialTime zeroCodeRealizer :=
  polynomial_composition (polynomial_composition (polynomial_pair polynomial_second polynomial_labelWidth)
    polynomial_takeFast) (polynomial_map (polynomial_constant 0))

lemma polynomial_initialInput : PolynomialTime initialInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first CountingPreparedState.polynomial_catalog)
    (polynomial_pair polynomial_capacities polynomial_zeroCode)

lemma polynomial_initial : PolynomialTime initialRealizer :=
  polynomial_composition polynomial_initialInput CompanionInitialStoredProgram.polynomial_output

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_pair polynomial_prepared polynomial_initial

theorem polynomial_runInput : PolynomialTime runInputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_output) polynomial_second

end ContingencyTables.CountingAdaptiveInputProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RepeatedFractionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Independent repetition of a finite-word rational program

The public confidence amplification only groups bits already supplied
on the tape. Its binary count cannot cause an unbounded allocation.
-/

namespace ContingencyTables.RepeatedFractionProgram
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

variable {X : Type} [Codec X]
lemma polynomial_words : PolynomialTime (wordsRealizer (X:=X)) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_second) polynomial_wordChunks)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first))
    polynomial_takeFast

variable {f : X×List Bool→TreeFraction.Fraction}

lemma polynomial_sample (F : Realizer f) (hF : PolynomialTime F) :
    PolynomialTime (sampleRealizer F) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) hF

lemma polynomial_samples (F : Realizer f) (hF : PolynomialTime F) :
    PolynomialTime (samplesRealizer F) :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_words)
    (polynomial_mapWith (polynomial_sample F hF))

attribute [local irreducible] samples

lemma polynomial_output (F : Realizer f) (hF : PolynomialTime F) :
    PolynomialTime (outputRealizer F) :=
  polynomial_composition (polynomial_samples F hF) MedianFractionProgram.polynomial_median

open GridBoundary CommonBasesFPRAS

end ContingencyTables.RepeatedFractionProgram

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

lemma polynomial_prepared (hN : PolynomialTime N) : PolynomialTime (preparedRealizer width N) :=
  polynomial_pair (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_first polynomial_repeats)
    (polynomial_composition polynomial_first hN))) polynomial_second

attribute [local irreducible] prepared

lemma polynomial_output (hF : PolynomialTime F) (hN : PolynomialTime N) :
    PolynomialTime (outputRealizer single F width N) :=
  polynomial_composition (polynomial_prepared width N hN) (RepeatedFractionProgram.polynomial_output F hF)

end ContingencyTables.CountingAmplifiedProgram

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

lemma polynomial_words : PolynomialTime wordsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_phaseWidth) polynomial_second)
      polynomial_wordChunks)
    (polynomial_composition polynomial_first polynomial_phaseCount)) polynomial_takeFast

lemma polynomial_start : PolynomialTime startRealizer :=
  polynomial_composition CountingAdaptiveInputProgram.polynomial_runInput polynomial_first

lemma polynomial_historyInput : PolynomialTime historyInputRealizer :=
  polynomial_pair polynomial_start polynomial_words

attribute [local irreducible] historyInput

lemma polynomial_finalStored : PolynomialTime finalStoredRealizer :=
  polynomial_composition polynomial_historyInput CompanionOuterHistoryProgram.polynomial_output

theorem polynomial_output : PolynomialTime outputRealizer :=
  polynomial_composition polynomial_finalStored polynomial_second

end ContingencyTables.CountingPositiveProgram

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

lemma polynomial_positive_oai : PolynomialTime positiveRealizer :=
  CountingAmplifiedProgram.polynomial_output CountingPositiveProgram.output
    CountingPositiveProgram.outputRealizer CountingPositiveProgram.bitCount
    CountingPositiveProgram.bitCountRealizer CountingPositiveProgram.polynomial_output
    CountingPositiveProgram.polynomial_bitCount

end
end ContingencyTables.CountingExecutedMachine

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.CountingExecutedMachine.polynomial_positive_oai := @OAI.ContingencyTables.CountingExecutedMachine.polynomial_positive_oai
