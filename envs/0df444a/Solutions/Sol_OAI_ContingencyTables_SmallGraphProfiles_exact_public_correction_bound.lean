-- Prove2me | solution 1 for OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:41:24.671188+00:00
-- url     : https://prove2.me/submissions/da2dca94-937e-48fa-a343-ddba3e38b2d3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_ContingencyTables
import Definitions.Def_OAIQ089A011
import Theorems.Thm_OAI_ContingencyTables_ProfilePrograms_work_exactMatrixInput
import Theorems.Thm_OAI_ContingencyTables_SmallGraphProfiles_exact_rare_measure_bound

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
-- module Solutions.OAIQ089_CT.MatchingCount_Machines_TreeListMore
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty
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

end MatchingFPRAS.ExecutableChoice

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for the literal small-profile repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_differenceEntry : PolynomialTime differenceEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_getDFast 0))
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      (polynomial_getDFast 0))) polynomial_subtract

lemma polynomial_listDifference : PolynomialTime listDifferenceRealizer := by
  have hr : PolynomialTime (composition
      (composition (second (A := List ℕ) (B := List ℕ)) listLength) range) := by
    apply polynomial_boundedRange (polynomial_composition polynomial_second polynomial_listLength) X
    intro z
    simp only [Polynomial.eval_X]
    exact (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  exact polynomial_composition (polynomial_pair polynomial_identity hr)
    (polynomial_mapWith polynomial_differenceEntry)

lemma polynomial_repairRows : PolynomialTime repairRowsRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first)))
    polynomial_listExchange

theorem polynomial_repairedViews : PolynomialTime repairedViewsRealizer :=
  polynomial_pair polynomial_repairRows (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first) polynomial_repairRows)
    polynomial_listDifference)

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallBoundsProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary program checking every stored coordinate bound -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_boundedValues : PolynomialTime boundedValuesRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_mapWith (polynomial_composition
      (polynomial_pair polynomial_second polynomial_first) polynomial_leNat)) polynomial_all)

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

lemma polynomial_validMarginAt (row : Bool) : PolynomialTime (validMarginAtRealizer row) := by
  unfold validMarginAtRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_lineValue row)
      (polynomial_marginValue row)) polynomial_leNat)
    (polynomial_choose (polynomial_composition (polynomial_pair (polynomial_marginValue row)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_less)
      (polynomial_composition (polynomial_pair (polynomial_lineValue row)
        (polynomial_marginValue row)) polynomial_natEqual) (polynomial_constant true))) polynomial_boolAnd)

lemma polynomial_marginIndices (row : Bool) : PolynomialTime (marginIndices row) := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_marginList row) polynomial_listLength) X
  intro z
  have hw : weight (marginList row z)≤weight z := by
    rcases z with ⟨⟨lookupData,⟨r,c⟩⟩,U⟩
    cases row <;> simp only [marginList,Bool.false_eq_true,ite_false,ite_true, if_true,weight_prod] <;> omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight (marginList row z)).trans hw

theorem polynomial_validMargins (row : Bool) : PolynomialTime (validMarginsRealizer row) := by
  unfold validMarginsRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_marginIndices row))
    (polynomial_mapWith (polynomial_validMarginAt row))) polynomial_all)

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

lemma polynomial_profileBound (row : Bool) : PolynomialTime (profileBound row) :=
  polynomial_composition (polynomial_pair polynomial_second (polynomial_profileView row))
    polynomial_boundedValues

lemma polynomial_profileShape (row : Bool) : PolynomialTime (profileShape row) :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_profileView row) polynomial_listLength)
    (polynomial_composition polynomial_profileCatalog polynomial_listLength)) polynomial_natEqual

lemma polynomial_profilePattern : PolynomialTime profilePattern :=
  polynomial_composition (polynomial_pair polynomial_profileViews polynomial_second)
    polynomial_patternTest

lemma polynomial_profileColumnView : PolynomialTime profileColumnView :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_profileViews polynomial_second)) polynomial_complementValues

lemma polynomial_profileLineData (row : Bool) : PolynomialTime (profileLineData row) :=
  polynomial_pair (polynomial_pair (polynomial_pair polynomial_profileCatalog
    (polynomial_choose (polynomial_constant row) (polynomial_profileView true)
      polynomial_profileColumnView)) polynomial_profileMargins) polynomial_second

lemma polynomial_profileLineTest (row : Bool) : PolynomialTime (profileLineTest row) :=
  polynomial_composition (polynomial_profileLineData row) (polynomial_validMargins row)

theorem polynomial_profileTest : PolynomialTime profileTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_profileShape true)
    (polynomial_composition (polynomial_pair (polynomial_profileShape false)
    (polynomial_composition (polynomial_pair (polynomial_profileBound true)
    (polynomial_composition (polynomial_pair (polynomial_profileBound false)
    (polynomial_composition (polynomial_pair polynomial_profilePattern
    (polynomial_composition (polynomial_pair (polynomial_profileLineTest true)
      (polynomial_profileLineTest false)) polynomial_boolAnd)) polynomial_boolAnd))
      polynomial_boolAnd)) polynomial_boolAnd)) polynomial_boolAnd)) polynomial_boolAnd

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

theorem polynomial_splitViews : PolynomialTime splitViewsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_dropFast)

theorem polynomial_codeExchange : PolynomialTime codeExchangeRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_listLength)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_flattenViews) polynomial_second)
      polynomial_listExchange)) polynomial_splitViews

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallExchangeListProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating all directed unit exchanges of a stored profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_positiveExchangeTest : PolynomialTime positiveExchangeTestRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_natEqual)
      polynomial_boolNot)
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition (polynomial_pair polynomial_first
        (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)))
      polynomial_less)) polynomial_boolAnd)

lemma polynomial_positiveExchangeIndices : PolynomialTime positiveExchangeIndicesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_pair polynomial_identity polynomial_identity)
      polynomial_cellPairs)) (polynomial_filterWith polynomial_positiveExchangeTest)

theorem polynomial_codeExchangeList : PolynomialTime codeExchangeListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_flattenViews polynomial_positiveExchangeIndices))
    (polynomial_mapWith polynomial_codeExchange)

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

theorem polynomial_profileCodeEqual : PolynomialTime profileCodeEqual :=
  polynomial_pairEqual polynomial_listNatEqual polynomial_listNatEqual

theorem polynomial_profileCodeDedup : PolynomialTime profileCodeDedup :=
  polynomial_dedup polynomial_profileCodeEqual

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileInverseRepairProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for each labelled inverse repair -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_backwardRows : PolynomialTime backwardRowsRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_second))
    polynomial_listExchange

lemma polynomial_backwardColumns : PolynomialTime backwardColumnsRealizer :=
  polynomial_composition (polynomial_pair polynomial_backwardRows (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_second polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_second) polynomial_second) polynomial_first)))
    polynomial_listExchange

theorem polynomial_backwardViews : PolynomialTime backwardViewsRealizer :=
  polynomial_pair polynomial_backwardRows (polynomial_composition
    (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      polynomial_backwardColumns) polynomial_listDifference)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairGeometryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of repair crossing cells and capacities -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_sourceCell : PolynomialTime sourceCell :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast (0,0))

lemma polynomial_targetCell : PolynomialTime targetCell :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast (0,0))

theorem polynomial_crossingIndex : PolynomialTime crossingIndexRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_targetCell polynomial_first)
    (polynomial_composition polynomial_sourceCell polynomial_second)) polynomial_first)
    polynomial_cellLookup

theorem polynomial_capacityList : PolynomialTime capacityListRealizer :=
  polynomial_mapWith polynomial_first

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairCodeProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Forward and inverse repairs on the stored pair of integer lists -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_repairDataCatalog : PolynomialTime repairDataCatalog :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

lemma polynomial_repairDataRows : PolynomialTime repairDataRows :=
  polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first

lemma polynomial_repairDataCaps : PolynomialTime repairDataCaps :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second) polynomial_repairDataRows)
    polynomial_capacityList

lemma polynomial_repairDataCross : PolynomialTime repairDataCross :=
  polynomial_composition (polynomial_pair polynomial_repairDataCatalog polynomial_second)
    polynomial_crossingIndex

theorem polynomial_forwardRepairCode : PolynomialTime forwardRepairCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_repairDataRows
    (polynomial_pair polynomial_repairDataCaps
      (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
        polynomial_repairDataCross))) polynomial_repairedViews

theorem polynomial_inverseRepairCode : PolynomialTime inverseRepairCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_repairDataRows
    (polynomial_pair polynomial_repairDataCaps
      (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
        (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
          polynomial_repairDataCross)))) polynomial_backwardViews

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallDefectCodeTest
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The labelled defect predicate on two binary-coded views -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_repairLabelTest : PolynomialTime repairLabelTestRealizer :=
  polynomial_composition (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second) polynomial_defectTest

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallRepairListProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial lists of encoded forward and inverse repairs -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_repairRowsData : PolynomialTime repairRows :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first

lemma polynomial_repairPairs : PolynomialTime repairPairsRealizer :=
  polynomial_composition (polynomial_pair polynomial_repairRowsData polynomial_repairRowsData)
    polynomial_cellPairs

lemma polynomial_forwardRepairLabels : PolynomialTime forwardRepairLabelsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_repairPairs)
    (polynomial_filterWith polynomial_repairLabelTest)

theorem polynomial_forwardRepairList : PolynomialTime forwardRepairListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_forwardRepairLabels)
    (polynomial_mapWith polynomial_forwardRepairCode)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_SmallInverseRepairList
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Checking inverse repair candidates against their forward image -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_inverseLabelInput : PolynomialTime inverseLabelInputRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_pair polynomial_repairDataCatalog polynomial_inverseRepairCode)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_second

lemma polynomial_inverseLabelTest : PolynomialTime inverseLabelTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_inverseLabelInput polynomial_repairLabelTest)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_inverseLabelInput polynomial_forwardRepairCode)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
        polynomial_second)) polynomial_profileCodeEqual)) polynomial_boolAnd

lemma polynomial_inverseRepairLabels : PolynomialTime inverseRepairLabelsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_repairPairs)
    (polynomial_filterWith polynomial_inverseLabelTest)

theorem polynomial_checkedInverseRepairList : PolynomialTime checkedInverseRepairListRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_inverseRepairLabels)
    (polynomial_mapWith polynomial_inverseRepairCode)

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

lemma polynomial_repairInput : PolynomialTime repairInput :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second

lemma polynomial_rawCodeNeighbors : PolynomialTime rawCodeNeighborsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_profileViews polynomial_codeExchangeList)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_repairInput polynomial_forwardRepairList)
      (polynomial_composition polynomial_repairInput polynomial_checkedInverseRepairList))
      polynomial_append)) polynomial_append

lemma polynomial_candidateData : PolynomialTime candidateDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_profileCatalog) polynomial_second)
    (polynomial_composition polynomial_first polynomial_profileMargins))
    (polynomial_composition polynomial_first polynomial_second)

theorem polynomial_codeNeighbors : PolynomialTime codeNeighborsRealizer :=
  polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity polynomial_rawCodeNeighbors)
    (polynomial_filterWith (polynomial_composition polynomial_candidateData polynomial_profileTest)))
    polynomial_profileCodeDedup

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperCodeProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The compiled neighbor draw has the small-chain proposal law -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_codeNeighborProposal : PolynomialTime codeNeighborProposalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_codeNeighbors) polynomial_second)
    polynomial_listWordChoice

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_FirstPaperPreparedProposal
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
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

/-- Cost is polynomial in the binary data, even when the represented
margin values and the quotient are large. -/
theorem polynomial_component : PolynomialTime componentRealizer := by
  have hD : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hS : PolynomialTime (composition
      (first (A := ℕ×ℕ) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hP : PolynomialTime (composition
      (second (A := ℕ×ℕ) (B := ℕ×ℕ)) first) :=
    polynomial_composition polynomial_second polynomial_first
  have hN : PolynomialTime (composition
      (second (A := ℕ×ℕ) (B := ℕ×ℕ)) second) :=
    polynomial_composition polynomial_second polynomial_second
  have h4 := polynomial_composition hD polynomial_fourthPower
  have h8 := polynomial_composition hD polynomial_eighthPower
  have hp := polynomial_composition (polynomial_pair h4
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair h8 hP) polynomial_multiply)
      (polynomial_composition (polynomial_pair hD hS) polynomial_multiply)) polynomial_add))
    polynomial_multiply
  have hn := polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair h4 h8) polynomial_multiply) hN) polynomial_multiply
  have hd := polynomial_composition (polynomial_pair hS h8) polynomial_multiply
  unfold componentRealizer
  exact polynomial_congr _ (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair hn hp) polynomial_subtract) hd) polynomial_quotient)

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

theorem polynomial_exponentCell : PolynomialTime exponentCellRealizer :=
  polynomial_composition polynomial_exponentCellData polynomial_component

theorem polynomial_exponentCells : PolynomialTime exponentCellsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_cellPairs

theorem polynomial_exponentValues : PolynomialTime exponentValuesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_exponentCells)
    (polynomial_mapWith polynomial_exponentCell)

/-- The exponent evaluation traverses only the supplied matrix dimensions. -/
theorem polynomial_fullExponent : PolynomialTime fullExponentRealizer :=
  polynomial_composition (polynomial_pair polynomial_exponentValues (polynomial_constant 0))
    polynomial_listMaximum

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

theorem polynomial_gridCellValue : PolynomialTime gridCellValueRealizer :=
  polynomial_composition (polynomial_pair polynomial_gridCellWidth
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_second) polynomial_matrixEntry)) polynomial_multiply

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseScaleMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Scaling a binary grid matrix to its integer bin corner -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial GridBoundary

lemma polynomial_scaleRows : PolynomialTime scaleRowsRealizer := by
  change PolynomialTime (composition _ range)
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_tail) polynomial_listLength) X
  intro z
  have h := list_length_le_weight z.1.1.1
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans (h.trans ((weight_fst z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))))

lemma polynomial_scaleColumns : PolynomialTime scaleColumnsRealizer := by
  change PolynomialTime (composition _ range)
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_tail) polynomial_listLength) X
  intro z
  have h := list_length_le_weight z.1.1.2
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans (h.trans ((weight_snd z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))))

lemma polynomial_scaleRowEntry : PolynomialTime scaleRowEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_gridCellValue

lemma polynomial_scaleRow : PolynomialTime scaleRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_scaleColumns))
    (polynomial_mapWith polynomial_scaleRowEntry)

theorem polynomial_scaleMatrix : PolynomialTime scaleMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_scaleRows)
    (polynomial_mapWith polynomial_scaleRow)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseGridExponentProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the dense exponent directly from a binary grid matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary

theorem polynomial_scaledData : PolynomialTime scaledDataRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_scaleMatrix) polynomial_second

theorem polynomial_gridExponent : PolynomialTime gridExponentRealizer :=
  polynomial_composition polynomial_scaledData polynomial_fullExponent

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

theorem polynomial_flatExponent : PolynomialTime flatExponentRealizer :=
  polynomial_composition polynomial_flatToGridData polynomial_gridExponent

end ContingencyTables.DensePrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseMetropolisProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial binary program for a full dense Metropolis step -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_replaceFlat : PolynomialTime replaceFlatRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) (polynomial_composition polynomial_first polynomial_second)

theorem polynomial_flatAcceptCandidate : PolynomialTime flatAcceptCandidateRealizer := by
  have hd : PolynomialTime (composition
      (first (A := FlatStepData) (B := List ℕ)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hc := polynomial_composition (polynomial_composition
    (polynomial_pair hd polynomial_second) polynomial_replaceFlat) polynomial_flatExponent
  have hx := polynomial_composition hd polynomial_flatExponent
  have hg := polynomial_composition (polynomial_pair hc hx) polynomial_subtract
  have hb : PolynomialTime (composition
      (composition (first (A := FlatStepData) (B := List ℕ)) second) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second
  unfold flatAcceptCandidateRealizer
  exact polynomial_choose (polynomial_composition (polynomial_pair hb hg) polynomial_dyadicWordAccept)
    polynomial_second (polynomial_composition (polynomial_composition hd polynomial_first) polynomial_second)

theorem polynomial_flatStepCandidate : PolynomialTime flatStepCandidateRealizer := by
  have hd : PolynomialTime (composition
      (first (A := FlatExponentData) (B := List Bool×List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  have hK := polynomial_composition (polynomial_pair (polynomial_constant 4)
    (polynomial_composition hd polynomial_eighthPower)) polynomial_multiply
  unfold flatStepCandidateRealizer
  exact polynomial_composition (polynomial_pair (polynomial_pair hK
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_composition polynomial_second polynomial_first)) polynomial_axisWordStep

/-- Includes proposal decoding, exact integer exponent evaluation and the
independent acceptance word. Every finite input terminates in polynomial time. -/
theorem polynomial_flatMetropolisStep : PolynomialTime flatMetropolisStepRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_flatStepCandidate)
    (polynomial_optionCases
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_flatAcceptCandidate)

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

theorem polynomial_proposalWidth : PolynomialTime proposalWidthRealizer := by
  have hd : PolynomialTime (composition
      (first (A := FlatExponentData) (B := List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  unfold proposalWidthRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_pair (polynomial_constant 8) hd) polynomial_multiply) polynomial_ceilLogTwo

theorem polynomial_flatWordStep : PolynomialTime flatWordStepRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_proposalWidth) polynomial_dropFast)))
    polynomial_flatMetropolisStep

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

lemma flatMetropolisStep_growth (z : FlatStepData) (S : ℕ)
    (hx : ∀ a∈z.1.1.2,a.size≤S) :
    (flatMetropolisStep z).length=z.1.1.2.length ∧
      ∀ a∈flatMetropolisStep z,a.size≤S+2 := by
  have hstay : z.1.1.2.length=z.1.1.2.length ∧ ∀ a∈z.1.1.2,a.size≤S+2 :=
    ⟨rfl,fun a ha => (hx a ha).trans (Nat.le_add_right _ _)⟩
  unfold flatMetropolisStep
  cases h : flatStepCandidate z with
  | none => exact hstay
  | some ys =>
    have hy := axisListStep_growth
      (((4*z.1.2^8,z.1.1.2),MatchingFPRAS.StackAddition.value z.2.1/2),
        decide (MatchingFPRAS.StackAddition.value z.2.1%2=1)) ys S h hx
    simp only [Option.elim_some,flatAcceptCandidate]
    split <;> assumption

lemma flatWordStep_growth (z : FlatExponentData×List Bool) (S : ℕ)
    (hx : ∀ a∈z.1.1.2,a.size≤S) :
    (flatWordStep z).length=z.1.1.2.length ∧
      ∀ a∈flatWordStep z,a.size≤S+2 :=
  flatMetropolisStep_growth _ S hx

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial loop of binary dense transition words -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_advance : PolynomialTime advanceRealizer := by
  unfold advanceRealizer
  exact polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_flatWordStep))
    polynomial_replaceFlat

lemma advance_growth (data : FlatExponentData) (bits : List Bool) (S : ℕ)
    (h : ∀ a∈data.1.2,a.size≤S) :
    (advance (bits,data)).1.2.length=data.1.2.length ∧
      ∀ a∈(advance (bits,data)).1.2,a.size≤S+2 := flatWordStep_growth _ S h

lemma fold_advance_parameters (bits : List (List Bool)) (data : FlatExponentData) :
    let out := bits.foldl (fun data bits => advance (bits,data)) data
    out.1.1=data.1.1 ∧ out.2=data.2 ∧ out.1.2.length=data.1.2.length := by
  induction bits generalizing data with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons b bs ih =>
    have h := ih (advance (b,data))
    have hl : (advance (b,data)).1.2.length=data.1.2.length := by
      have hx := advance_growth data b (data.1.2.map Nat.size).sum
        (fun a ha => List.single_le_sum (fun _ _ => Nat.zero_le _) a.size
          (List.mem_map.mpr ⟨a,ha,rfl⟩))
      exact hx.1
    exact ⟨h.1,h.2.1,h.2.2.trans hl⟩

lemma fold_advance_sizes (bits : List (List Bool)) (data : FlatExponentData) (S : ℕ)
    (h : ∀ a∈data.1.2,a.size≤S) :
    ∀ a∈(bits.foldl (fun data bits => advance (bits,data)) data).1.2,
      a.size≤S+2*bits.length := by
  induction bits generalizing data S with
  | nil => simpa using h
  | cons b bs ih =>
    have hg := advance_growth data b S h
    have ht := ih (advance (b,data)) (S+2) hg.2
    intro a ha
    have h := ht a ha
    simpa only [List.length_cons,List.foldl_cons] using
      h.trans_eq (by omega : S+2+2*bs.length=S+2*(bs.length+1))

theorem polynomial_walkWords : PolynomialTime walkWordsRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advance (20*(X+1)^2)
  intro bits data pre post he
  let S := weight (bits,data)
  let out := pre.foldl (fun data bits => advance (bits,data)) data
  have hd : weight data≤S := weight_snd (bits,data)
  have hp : pre.length≤S := (list_length_le_weight pre).trans
    ((weight_prefix he).trans (weight_fst (bits,data)))
  have hxs : weight data.1.2≤S := (weight_snd data.1).trans ((weight_fst data).trans hd)
  have hn : data.1.2.length≤S := (list_length_le_weight _).trans hxs
  have hi : ∀ a∈data.1.2,a.size≤S := fun a ha =>
    (size_le_weight a).trans ((weight_mem ha).trans hxs)
  have hs := fold_advance_sizes pre data S hi
  have ht := fold_advance_parameters pre data
  have hw : weight out.1.2≤out.1.2.length*(4*(S+2*pre.length)+2)+1 := by
    have h := weight_map_bound (f := id) (as := out.1.2) (N := 4*(S+2*pre.length)+1)
      (fun a ha => (weight_nat_le a).trans (by have h := hs a ha; omega))
    simpa only [List.map_id_fun,id_eq,Nat.add_assoc] using h
  have hm : weight out.1.1≤S := by
    rw [ht.1]
    exact (weight_fst data.1).trans ((weight_fst data).trans hd)
  have hd' : weight out.2≤S := by
    rw [ht.2.1]
    exact (weight_snd data).trans hd
  have hl : out.1.2.length≤S := ht.2.2.trans_le hn
  have hmul : out.1.2.length*(4*(S+2*pre.length)+2)≤S*(12*S+2) :=
    Nat.mul_le_mul hl (by omega)
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change weight out≤20*(S+1)^2
  have heq : weight out=1+(1+weight out.1.1+weight out.1.2)+weight out.2 := by
    rw [weight_prod,weight_prod]
  nlinarith

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseBooleanWalkProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial program for the complete flat-word dense walk -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped GridBoundary ProfilePrograms

theorem polynomial_denseWidth : PolynomialTime denseWidthRealizer := by
  unfold denseWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_pair (polynomial_constant 8) polynomial_identity) polynomial_multiply)
      polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 8) polynomial_fifthPower)
      polynomial_multiply)) polynomial_add

theorem polynomial_flatWordWalk : PolynomialTime flatWordWalkRealizer :=
  polynomial_composition (polynomial_pair polynomial_first (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_denseWidth)
    polynomial_second) polynomial_wordChunks)) polynomial_walkWords

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletionTest
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial exact acceptance test for a free integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

theorem polynomial_completionNonnegative : PolynomialTime completionNonnegativeRealizer :=
  polynomial_composition (polynomial_composition polynomial_completionParts
    (polynomial_pair polynomial_second polynomial_first)) polynomial_leNat

theorem polynomial_completionValid : PolynomialTime completionValidRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_composition polynomial_first polynomial_cellPairs))
    (polynomial_mapWith polynomial_completionNonnegative)) polynomial_all)

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseCompletedMatrixProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary construction of the completed integer matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped Polynomial

theorem polynomial_completedEntry : PolynomialTime completedEntryRealizer :=
  polynomial_composition (polynomial_composition polynomial_completionParts
    (polynomial_pair polynomial_first polynomial_second)) polynomial_subtract

lemma polynomial_completionRows : PolynomialTime completionRowsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_completionColumns : PolynomialTime completionColumnsRealizer := by
  apply polynomial_boundedRange
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_listLength) X
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma polynomial_completedRowEntry : PolynomialTime completedRowEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_completedEntry

lemma polynomial_completedRow : PolynomialTime completedRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_completionColumns))
    (polynomial_mapWith polynomial_completedRowEntry)

theorem polynomial_completedMatrix : PolynomialTime completedMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_completionRows)
    (polynomial_mapWith polynomial_completedRow)

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseOffsetProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary quotient offsets and the resulting free matrix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms GridBoundary

theorem polynomial_offsetBits : PolynomialTime offsetBitsRealizer := by
  unfold offsetBitsRealizer
  apply polynomial_composition _ (polynomial_getDFast [])
  apply polynomial_pair (polynomial_composition polynomial_first polynomial_second)
  apply polynomial_composition _ polynomial_add
  apply polynomial_pair _ (polynomial_composition polynomial_second polynomial_second)
  apply polynomial_composition _ polynomial_multiply
  apply polynomial_pair (polynomial_composition polynomial_second polynomial_first)
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_second)
      polynomial_tail) polynomial_listLength

theorem polynomial_offsetFreeEntry : PolynomialTime offsetFreeEntryRealizer := by
  have hc : PolynomialTime (pair
      (composition (first (A := OffsetData) (B := ℕ×ℕ)) first) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold offsetFreeEntryRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition hc polynomial_gridCellValue)
    (polynomial_composition (polynomial_pair
      (polynomial_composition hc polynomial_gridCellWidth) polynomial_offsetBits)
      polynomial_scaledWord)) polynomial_add

theorem polynomial_offsetRowEntry : PolynomialTime offsetRowEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_offsetFreeEntry

theorem polynomial_offsetRow : PolynomialTime offsetRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_scaleColumns))
    (polynomial_mapWith polynomial_offsetRowEntry)

theorem polynomial_offsetMatrix : PolynomialTime offsetMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_scaleRows)) (polynomial_mapWith polynomial_offsetRow)

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

theorem polynomial_chunkIndices : PolynomialTime chunkIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

theorem polynomial_dependentChunks : PolynomialTime dependentChunksRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_chunkIndices)
    (polynomial_mapWith polynomial_dependentChunk)

open scoped BigOperators

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

theorem polynomial_offsetLength : PolynomialTime offsetLengthRealizer := by
  have hc : PolynomialTime (pair
      (composition (first (A := OffsetWidthData) (B := ℕ×ℕ)) first) second) :=
    polynomial_pair (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold offsetLengthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition hc polynomial_gridCellWidth) polynomial_successor) polynomial_ceilLogTwo)
    (polynomial_composition (polynomial_pair (polynomial_constant 4)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_second)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
        polynomial_add)) polynomial_multiply)) polynomial_add

theorem polynomial_freeCells : PolynomialTime freeCellsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_tail)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second) polynomial_tail))
    polynomial_cellPairs

theorem polynomial_offsetLengths : PolynomialTime offsetLengthsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_freeCells)
    (polynomial_mapWith polynomial_offsetLength)

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

theorem polynomial_trialWalkBits : PolynomialTime trialWalkBitsRealizer := by
  have hd : PolynomialTime (composition
      (composition (first (A := FlatExponentData×ℕ) (B := List Bool)) first) second) :=
    polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second
  unfold trialWalkBitsRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition hd polynomial_fiftiethPower)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_second) polynomial_successor)
        polynomial_squareNat)) polynomial_multiply)
    (polynomial_composition hd polynomial_denseWidth)) polynomial_multiply

theorem polynomial_trialGrid : PolynomialTime trialGridRealizer := by
  unfold trialGridRealizer
  exact polynomial_composition (polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_trialWalkBits) polynomial_takeFast))
    polynomial_flatWordWalk) polynomial_flatToGridData

theorem polynomial_trialOffsets : PolynomialTime trialOffsetsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_trialGrid
      (polynomial_composition polynomial_first polynomial_second)) polynomial_offsetLengths)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_trialWalkBits) polynomial_dropFast))
    polynomial_dependentChunks

theorem polynomial_trialCompletion : PolynomialTime trialCompletionRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition polynomial_trialGrid polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_trialGrid polynomial_trialOffsets) polynomial_offsetMatrix)

theorem polynomial_acceptCompletion : PolynomialTime acceptCompletionRealizer :=
  polynomial_choose polynomial_completionValid
    (polynomial_composition polynomial_completedMatrix polynomial_some) (polynomial_constant none)

/-- Includes the full walk, every quotient offset, signed-entry checking,
and binary output construction. Runtime is polynomial for every input. -/
theorem polynomial_denseTrialCode : PolynomialTime denseTrialCodeRealizer :=
  polynomial_composition polynomial_trialCompletion polynomial_acceptCompletion

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

theorem polynomial_isSome : PolynomialTime (isSomeRealizer (B := B)) := by
  unfold isSomeRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_constant false) polynomial_identity)
    (polynomial_optionCases (polynomial_constant false) (polynomial_constant true))

theorem polynomial_firstSome : PolynomialTime (firstSomeRealizer (B := B)) :=
  polynomial_congr _ (polynomial_composition (polynomial_filter polynomial_isSome) (polynomial_head none))

theorem polynomial_default : PolynomialTime (defaultRealizer (B := B)) := by
  unfold defaultRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

theorem polynomial_retry {f : A×W → Option B} {F : Realizer f} (hF : PolynomialTime F) :
    PolynomialTime (retryRealizer F) := by
  unfold retryRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_mapWith hF)) polynomial_firstSome)) polynomial_default

end ContingencyTables.FirstSuccessProgram

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseDrawProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded dense draw as a single polynomial binary program -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms

theorem polynomial_trialWidth : PolynomialTime trialWidthRealizer := by
  unfold trialWidthRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant []))
      polynomial_trialWalkBits)
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_flatToGridData) polynomial_second)
      polynomial_offsetLengths) polynomial_listSum)) polynomial_add

theorem polynomial_drawChunks : PolynomialTime drawChunksRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_trialWidth) polynomial_second) polynomial_wordChunks

/-- Every finite input has polynomial binary cost. On a valid dense input,
the first successful trial is selected, or the supplied feasible fallback. -/
theorem polynomial_denseDrawCode : PolynomialTime denseDrawCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_drawChunks)
    (FirstSuccessProgram.polynomial_retry polynomial_denseTrialCode)

end ContingencyTables.DensePrograms

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

theorem polynomial_swapFlatData : PolynomialTime swapFlatDataRealizer := by
  unfold swapFlatDataRealizer
  exact polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first))
      polynomial_swapMargins)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second))
    (polynomial_composition polynomial_second polynomial_second)

theorem polynomial_permuteDrawData : PolynomialTime permuteDrawDataRealizer := by
  unfold permuteDrawDataRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
        polynomial_first) polynomial_first)) polynomial_swapFlatData)
    (polynomial_composition (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_first) polynomial_second))
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second))
      polynomial_swapMatrix)) (polynomial_composition polynomial_second polynomial_second)

theorem polynomial_marginIndices : PolynomialTime marginIndicesRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_maximumIndex)
    (polynomial_composition polynomial_second polynomial_maximumIndex)

theorem polynomial_drawIndices : PolynomialTime drawIndicesRealizer := by
  unfold drawIndicesRealizer
  exact polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition (polynomial_composition
      polynomial_first polynomial_first) polynomial_first) polynomial_first) polynomial_first)
    polynomial_marginIndices

theorem polynomial_preparedDraw : PolynomialTime preparedDrawRealizer :=
  polynomial_composition (polynomial_pair polynomial_drawIndices polynomial_identity)
    polynomial_permuteDrawData

theorem polynomial_normalizedDraw : PolynomialTime normalizedDrawRealizer :=
  polynomial_composition polynomial_preparedDraw polynomial_denseDrawCode

/-- Maximal-margin selection, forward permutation, the full dense draw,
and the inverse permutation all have polynomial binary cost. -/
theorem polynomial_normalizedDenseCode : PolynomialTime normalizedDenseCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_drawIndices polynomial_normalizedDraw)
    polynomial_swapMatrix

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

theorem polynomial_canonicalInput : PolynomialTime canonicalInputRealizer := by
  have hm : PolynomialTime (composition
      (first (A := CanonicalParameters) (B := List Bool)) first) :=
    polynomial_composition polynomial_first polynomial_first
  have hp : PolynomialTime (composition
      (first (A := CanonicalParameters) (B := List Bool)) second) :=
    polynomial_composition polynomial_first polynomial_second
  unfold canonicalInputRealizer
  exact polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_pair (polynomial_pair hm (polynomial_composition hm polynomial_zeroGrid))
      (polynomial_composition hp polynomial_first))
    (polynomial_composition hp polynomial_second))
    (polynomial_composition hm GreedyFeasibleTable.polynomial_table)) polynomial_second

theorem polynomial_canonicalDenseDraw : PolynomialTime canonicalDenseDrawRealizer :=
  polynomial_composition polynomial_canonicalInput polynomial_normalizedDenseCode

end ContingencyTables.DensePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Dense_DenseReservedWord
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing and consuming the exact dense-word prefix -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms FirstSuccess

theorem polynomial_denseParameterBits : PolynomialTime denseParameterBitsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
        polynomial_fourthPower) (polynomial_composition polynomial_second polynomial_successor))
      polynomial_multiply) polynomial_trialWidth) polynomial_multiply

theorem polynomial_preparedCanonicalParameters : PolynomialTime preparedCanonicalParametersRealizer := by
  unfold preparedCanonicalParametersRealizer
  exact polynomial_composition (polynomial_composition (polynomial_composition
    (polynomial_pair polynomial_identity (polynomial_constant [])) polynomial_canonicalInput)
    polynomial_preparedDraw) (polynomial_composition polynomial_first polynomial_first)

theorem polynomial_canonicalBitCount : PolynomialTime canonicalBitCountRealizer :=
  polynomial_composition polynomial_preparedCanonicalParameters polynomial_denseParameterBits

theorem polynomial_reservedCanonicalDraw : PolynomialTime reservedCanonicalDrawRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition (polynomial_pair polynomial_second
      (polynomial_composition polynomial_first polynomial_canonicalBitCount)) polynomial_takeFast))
    polynomial_canonicalDenseDraw

open GridBoundary
open scoped BigOperators Classical
end ContingencyTables.DensePrograms

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
lemma polynomial_composition {f : A→Experiment B} {g : B→Experiment C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (composition F G) := work_then_polynomial hF hG
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
lemma polynomial_pair {f : A→Experiment B} {g : A→Experiment C} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (pair F G) :=
  work_pair hF hG X (by intro a; simp)
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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_IntegerMatrixProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary integer matrix propagation for exact law tabulation -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma sum_size_le_weight (v : List ℕ) : v.sum.size ≤ weight v := by
  induction v with
  | nil => simp
  | cons a v ih =>
    have ha:=size_le_weight a
    have hs:=nat_size_add a v.sum
    rw [List.sum_cons,weight_cons]
    have hm : max a.size v.sum.size ≤ weight a+weight v := max_le (by omega) (by omega)
    omega

end ContingencyTables.IntegerMatrixPrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_TranslationDecisionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary arithmetic for the completion translation test -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped ProfilePrograms CompletionTranslation
open scoped BigOperators

theorem polynomial_starParts : PolynomialTime starPartsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_pair polynomial_first (polynomial_constant [])) polynomial_second)
    polynomial_completionParts

theorem polynomial_translationParts : PolynomialTime translationPartsRealizer := by
  have ho : PolynomialTime (composition (pair (composition
      (first (A := MarginPair×MarginPair) (B := ℕ×ℕ)) first) second) starPartsRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_starParts
  have hn : PolynomialTime (composition (pair (composition
      (first (A := MarginPair×MarginPair) (B := ℕ×ℕ)) second) second) starPartsRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second) polynomial_starParts
  unfold translationPartsRealizer
  exact polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition hn polynomial_first)
      (polynomial_composition ho polynomial_second)) polynomial_add)
    (polynomial_composition (polynomial_pair (polynomial_composition hn polynomial_second)
      (polynomial_composition ho polynomial_first)) polynomial_add)

theorem polynomial_translatedCell : PolynomialTime translatedCellRealizer := by
  have hp : PolynomialTime (composition (pair (composition
      (first (A := TranslationData) (B := ℕ×ℕ)) first) second) translationPartsRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      polynomial_translationParts
  have he : PolynomialTime (composition (pair (composition
      (first (A := TranslationData) (B := ℕ×ℕ)) second) second) matrixEntryRealizer) :=
    polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_matrixEntry
  unfold translatedCellRealizer
  exact polynomial_composition (polynomial_pair (polynomial_composition hp polynomial_second)
    (polynomial_composition (polynomial_pair he (polynomial_composition hp polynomial_first))
      polynomial_add)) polynomial_leNat

theorem polynomial_translationValid : PolynomialTime translationValidRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_cellPairs)) (polynomial_mapWith polynomial_translatedCell)) polynomial_all)

end ContingencyTables.DensePrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalProfileProgram
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

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_ListedReservedDraw
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A common fixed word for all computed residual completion draws -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_reservedResidualDraw : PolynomialTime reservedResidualDrawRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_residualParameters) polynomial_second)
    DensePrograms.polynomial_reservedCanonicalDraw

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTransitionProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A binary small-profile transition with a fresh dense completion -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_stepCheck : PolynomialTime stepCheck :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first

theorem polynomial_stepViews : PolynomialTime stepViews :=
  polynomial_composition polynomial_stepCheck polynomial_profileViews

theorem polynomial_stepProposal : PolynomialTime stepProposalRealizer :=
  polynomial_composition (polynomial_pair polynomial_stepCheck
    (polynomial_composition polynomial_second polynomial_first)) polynomial_codeNeighborProposal

theorem polynomial_stepCandidateViews : PolynomialTime stepCandidateViewsRealizer :=
  polynomial_composition (polynomial_pair polynomial_stepViews polynomial_stepProposal)
    FirstSuccessProgram.polynomial_default

theorem polynomial_stepCandidate : PolynomialTime stepCandidateRealizer :=
  polynomial_composition (polynomial_pair polynomial_stepCheck polynomial_stepCandidateViews)
    polynomial_candidateData

theorem polynomial_stepCandidateParameters : PolynomialTime stepCandidateParametersRealizer :=
  polynomial_pair (polynomial_pair polynomial_stepCandidate
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

theorem polynomial_stepOldMargins : PolynomialTime stepOldMarginsRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_residualParameters)
    polynomial_first

theorem polynomial_stepNewMargins : PolynomialTime stepNewMarginsRealizer :=
  polynomial_composition (polynomial_composition polynomial_stepCandidateParameters
    polynomial_residualParameters) polynomial_first

theorem polynomial_stepCompletion : PolynomialTime stepCompletionRealizer :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second)) polynomial_reservedResidualDraw

theorem polynomial_stepTranslation : PolynomialTime stepTranslationRealizer :=
  polynomial_pair (polynomial_pair polynomial_stepOldMargins polynomial_stepNewMargins)
    polynomial_stepCompletion

theorem polynomial_profileStep : PolynomialTime profileStepRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition polynomial_stepTranslation DensePrograms.polynomial_translationValid)
    polynomial_stepCandidateViews polynomial_stepViews)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTableProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Reconstructing and testing an original table from an outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

theorem polynomial_outputCellPosition : PolynomialTime outputCellPositionRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first))
    polynomial_cellLookup

theorem polynomial_outputSmallEntry : PolynomialTime outputSmallEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_first) polynomial_outputCellPosition) (polynomial_getDFast 0)

theorem polynomial_outputDensePosition : PolynomialTime outputDensePositionRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_first)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first))
      (polynomial_indexOf polynomial_natEqual))
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
      (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
      (polynomial_indexOf polynomial_natEqual))

theorem polynomial_outputLargeEntry : PolynomialTime outputLargeEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
      polynomial_outputDensePosition) polynomial_matrixEntry)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_second) polynomial_first) polynomial_second))
    polynomial_subtract

theorem polynomial_outputEntry : PolynomialTime outputEntryRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_pair polynomial_outputCellPosition
      (polynomial_composition (polynomial_composition (polynomial_composition
        (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
        polynomial_listLength)) polynomial_less)
    polynomial_outputSmallEntry polynomial_outputLargeEntry)

theorem polynomial_paddingTest : PolynomialTime paddingTestRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_mapWith (polynomial_composition (polynomial_mapWith polynomial_leNat) polynomial_all))
    polynomial_all)

theorem polynomial_outerSuccess : PolynomialTime outerSuccessRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_first))
      polynomial_balancedTest)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_paddingTest)) polynomial_boolAnd

theorem polynomial_outputShape : PolynomialTime outputShapeRealizer :=
  polynomial_pair polynomial_first (polynomial_constant [])

theorem polynomial_outputRows : PolynomialTime outputRowsRealizer :=
  polynomial_composition polynomial_outputShape polynomial_completionRows
theorem polynomial_outputColumns : PolynomialTime outputColumnsRealizer :=
  polynomial_composition polynomial_outputShape polynomial_completionColumns

theorem polynomial_outputRowEntry : PolynomialTime outputRowEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_outputEntry

theorem polynomial_outputRow : PolynomialTime outputRowRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_outputColumns))
    (polynomial_mapWith polynomial_outputRowEntry)

theorem polynomial_outputMatrix : PolynomialTime outputMatrixRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_outputRows)
    (polynomial_mapWith polynomial_outputRow)

theorem polynomial_acceptedTable : PolynomialTime acceptedTableRealizer :=
  polynomial_choose (polynomial_composition polynomial_second polynomial_outerSuccess)
    (polynomial_composition polynomial_outputMatrix polynomial_some) (polynomial_constant none)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OuterTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing the original-table return from a residual draw -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_outputLargeRows : PolynomialTime outputLargeRowsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_first)) polynomial_largeIndices
theorem polynomial_outputLargeColumns : PolynomialTime outputLargeColumnsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
      polynomial_second)) polynomial_largeIndices

theorem polynomial_outputData : PolynomialTime outputDataRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_pair polynomial_outputLargeRows polynomial_outputLargeColumns))
    (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_second)

theorem polynomial_prepareOutput : PolynomialTime prepareOutputRealizer :=
  polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_second)
    polynomial_outputData

theorem polynomial_outerTrial : PolynomialTime outerTrialRealizer :=
  polynomial_composition polynomial_prepareOutput polynomial_acceptedTable

end ContingencyTables.ProfilePrograms

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

theorem polynomial_capBounds : PolynomialTime capBoundsRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_profileCatalog) polynomial_listLength)
    (polynomial_composition polynomial_first polynomial_second)

theorem polynomial_capViews : PolynomialTime capViewsRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_capBounds
      (polynomial_composition polynomial_second polynomial_first)) polynomial_capView)
    (polynomial_composition (polynomial_pair polynomial_capBounds
      (polynomial_composition polynomial_second polynomial_second)) polynomial_capView)

theorem polynomial_currentParameters : PolynomialTime currentParametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_second) polynomial_candidateData)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second))
    (polynomial_composition polynomial_first polynomial_second)

theorem polynomial_boundedNext : PolynomialTime boundedNextRealizer := by
  unfold boundedNextRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_currentParameters) polynomial_second)
      polynomial_profileStep)) polynomial_capViews

theorem polynomial_advanceProfile : PolynomialTime advanceProfileRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_boundedNext)

lemma advanceProfile_weight (word : ProfileWord) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z.1≤S) : weight (advanceProfile (word,z))≤20*(S+1)^3 := by
  let q := z.1.1.1.1.1.1.length
  let U := z.1.1.1.2
  have hq : q≤S := (list_length_le_weight _).trans ((weight_fst z.1.1.1.1.1).trans
    ((weight_fst z.1.1.1.1).trans ((weight_fst z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))))
  have hU : U.size≤S := (size_le_weight U).trans
    ((weight_snd z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))
  have hx := capView_weight q U (profileStep (currentParameters z,word)).1
  have hy := capView_weight q U (profileStep (currentParameters z,word)).2
  change weight (z.1,(capView ((q,U),(profileStep (currentParameters z,word)).1),
    capView ((q,U),(profileStep (currentParameters z,word)).2)))≤20*(S+1)^3
  rw [weight_prod z.1 _,weight_prod (capView ((q,U),(profileStep (currentParameters z,word)).1))
    (capView ((q,U),(profileStep (currentParameters z,word)).2))]
  have hm : q*(4*U.size+2)≤S*(4*S+2) := by gcongr
  nlinarith

lemma profileFold_fixed (words : List ProfileWord) (z : ProfileConfiguration) :
    (words.foldl (fun state word => advanceProfile (word,state)) z).1=z.1 := by
  induction words generalizing z with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma profileFold_weight (words : List ProfileWord) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z≤S) :
    weight (words.foldl (fun state word => advanceProfile (word,state)) z)≤20*(S+1)^3 := by
  induction words using List.reverseRecOn with
  | nil =>
    have hpow : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
    simpa using hz.trans (by omega : S≤20*(S+1)^3)
  | append_singleton words w _ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply advanceProfile_weight
    rw [profileFold_fixed]
    exact (weight_fst z).trans hz

theorem polynomial_profileWalk : PolynomialTime profileWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advanceProfile (20*(X+1)^3)
  intro words z pre post _
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  exact profileFold_weight pre z (weight (words,z)) (weight_snd (words,z))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTrialProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A complete polynomial outer trial on supplied independent words -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped

theorem polynomial_trialState : PolynomialTime trialStateRealizer :=
  polynomial_composition polynomial_first polynomial_profileWalk

theorem polynomial_trialParameters : PolynomialTime trialParametersRealizer :=
  polynomial_composition polynomial_trialState polynomial_currentParameters

theorem polynomial_trialCompletion : PolynomialTime trialCompletionRealizer :=
  polynomial_composition (polynomial_pair polynomial_trialParameters polynomial_second)
    polynomial_reservedResidualDraw

theorem polynomial_trialOutputInput : PolynomialTime trialOutputInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_trialParameters polynomial_first)
    polynomial_trialCompletion

theorem polynomial_profileTrial : PolynomialTime profileTrialRealizer :=
  polynomial_composition polynomial_trialOutputInput polynomial_outerTrial

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileWordProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Parsing the independent words of the physical outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_splitProfileWord : PolynomialTime splitProfileWordRealizer :=
  polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_takeFast)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_dropFast)

theorem polynomial_profileWordWidth : PolynomialTime profileWordWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    (polynomial_composition polynomial_first polynomial_second)) polynomial_add

theorem polynomial_profileWalkWidth : PolynomialTime profileWalkWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_profileWordWidth) polynomial_multiply

theorem polynomial_profileWalkChunks : PolynomialTime profileWalkChunksRealizer :=
  polynomial_composition (polynomial_pair polynomial_profileWordWidth
    (polynomial_composition (polynomial_pair polynomial_second polynomial_profileWalkWidth)
      polynomial_takeFast)) polynomial_wordChunks

theorem polynomial_profileWalkWords : PolynomialTime profileWalkWordsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_profileWalkChunks) (polynomial_mapWith polynomial_splitProfileWord)

theorem polynomial_profileTerminalWord : PolynomialTime profileTerminalWordRealizer :=
  polynomial_composition (polynomial_pair polynomial_second polynomial_profileWalkWidth) polynomial_dropFast

theorem polynomial_profileTrialWords : PolynomialTime profileTrialWordsRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_second) polynomial_second

theorem polynomial_prepareProfileTrial : PolynomialTime prepareProfileTrialRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_composition polynomial_profileTrialWords polynomial_profileWalkWords))
    (polynomial_composition polynomial_profileTrialWords polynomial_profileTerminalWord)

theorem polynomial_packedProfileTrial : PolynomialTime packedProfileTrialRealizer :=
  polynomial_composition polynomial_prepareProfileTrial polynomial_profileTrial

open FairBits GridBoundary
open scoped Classical
end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileRetryProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A polynomial retry loop for the complete binary outer trial -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_profileRetryWordInput : PolynomialTime profileRetryWordInputRealizer :=
  polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second

theorem polynomial_profileTrialWidth : PolynomialTime profileTrialWidthRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_profileRetryWordInput polynomial_profileWalkWidth)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_second))
    polynomial_add

theorem polynomial_profileRetryWords : PolynomialTime profileRetryWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_profileTrialWidth polynomial_second)
    polynomial_wordChunks

theorem polynomial_profileRetry : PolynomialTime profileRetryRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_profileRetryWords)
    (FirstSuccessProgram.polynomial_retry polynomial_packedProfileTrial)

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

theorem polynomial_parameterWordCount : PolynomialTime parameterWordCountRealizer :=
  polynomial_composition (f := fun z : SamplingParameters => (parameterTrials z,((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z))+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_parameterTrials) (polynomial_composition (f := fun z : SamplingParameters => ((parameterSteps z*(parameterProposalWidth z+parameterCompletionWidth z)),parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_composition (f := fun z : SamplingParameters => (parameterSteps z,(parameterProposalWidth z+parameterCompletionWidth z))) (g := fun t : ℕ×ℕ => t.1*t.2) (polynomial_pair (polynomial_parameterSteps) (polynomial_composition (f := fun z : SamplingParameters => (parameterProposalWidth z,parameterCompletionWidth z)) (g := fun t : ℕ×ℕ => t.1+t.2) (polynomial_pair (polynomial_parameterProposalWidth) (polynomial_parameterCompletionWidth)) polynomial_add)) polynomial_multiply) (polynomial_parameterCompletionWidth)) polynomial_add)) polynomial_multiply

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileSamplingProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Preparing and executing the complete profile sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_initialConfiguration : PolynomialTime initialConfigurationRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_initialCheck)
    (polynomial_composition polynomial_first polynomial_marginPadding))
    (polynomial_pair polynomial_parameterDimension polynomial_parameterAccuracy))
    (polynomial_composition polynomial_first polynomial_initialViews)

theorem polynomial_samplingSchedule : PolynomialTime samplingScheduleRealizer :=
  polynomial_pair (polynomial_pair polynomial_parameterSteps polynomial_parameterProposalWidth)
    polynomial_parameterCompletionWidth

theorem polynomial_samplingRetryParameters : PolynomialTime samplingRetryParametersRealizer :=
  polynomial_pair (polynomial_pair polynomial_initialConfiguration polynomial_samplingSchedule)
    (polynomial_composition polynomial_first GreedyFeasibleTable.polynomial_table)

theorem polynomial_samplingMatrix : PolynomialTime samplingMatrixRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_samplingRetryParameters) polynomial_second)
    polynomial_profileRetry

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitProfileProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The bounded profile program for the all-small branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms Polynomial

theorem polynomial_unitCandidateInput : PolynomialTime unitCandidateInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_currentParameters)
    (polynomial_pair polynomial_second (polynomial_constant []))

theorem polynomial_unitNext : PolynomialTime unitNextRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition polynomial_unitCandidateInput polynomial_stepCandidateViews)) polynomial_capViews

theorem polynomial_unitAdvance : PolynomialTime unitAdvanceRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_unitNext)

lemma unitAdvance_weight (word : List Bool) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z.1≤S) : weight (unitAdvance (word,z))≤20*(S+1)^3 := by
  let q := z.1.1.1.1.1.1.length
  let U := z.1.1.1.2
  have hq : q≤S := (list_length_le_weight _).trans ((weight_fst z.1.1.1.1.1).trans
    ((weight_fst z.1.1.1.1).trans ((weight_fst z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))))
  have hU : U.size≤S := (size_le_weight U).trans
    ((weight_snd z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))
  have hx := capView_weight q U (stepCandidateViews (unitCandidateInput (z,word))).1
  have hy := capView_weight q U (stepCandidateViews (unitCandidateInput (z,word))).2
  change weight (z.1,(capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).1),
    capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).2)))≤20*(S+1)^3
  rw [weight_prod z.1 _,weight_prod (capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).1))
    (capView ((q,U),(stepCandidateViews (unitCandidateInput (z,word))).2))]
  have hm : q*(4*U.size+2)≤S*(4*S+2) := by gcongr
  nlinarith

lemma unitFold_fixed (words : List (List Bool)) (z : ProfileConfiguration) :
    (words.foldl (fun state word => unitAdvance (word,state)) z).1=z.1 := by
  induction words generalizing z with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma unitFold_weight (words : List (List Bool)) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z≤S) :
    weight (words.foldl (fun state word => unitAdvance (word,state)) z)≤20*(S+1)^3 := by
  induction words using List.reverseRecOn with
  | nil =>
    have hpow : S+1≤(S+1)^3 := Nat.le_self_pow (by decide) _
    simpa using hz.trans (by omega : S≤20*(S+1)^3)
  | append_singleton words w _ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    apply unitAdvance_weight
    rw [unitFold_fixed]
    exact (weight_fst z).trans hz

theorem polynomial_unitProfileWalk : PolynomialTime unitProfileWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_unitAdvance (20*(X+1)^3)
  intro words z pre post _
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  exact unitFold_weight pre z (weight (words,z)) (weight_snd (words,z))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTrialProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-small trials and retries use only the stored profile entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS.TreeTyped DensePrograms

theorem polynomial_unitPackedWords : PolynomialTime unitPackedWordsRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    polynomial_second) polynomial_second) polynomial_wordChunks

theorem polynomial_unitPackedState : PolynomialTime unitPackedStateRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    polynomial_unitPackedWords) polynomial_unitProfileWalk

theorem polynomial_unitPackedTrial : PolynomialTime unitPackedTrialRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_unitPackedState polynomial_currentParameters) polynomial_first)
    (polynomial_constant [])) polynomial_outerTrial

theorem polynomial_unitRetryWidth : PolynomialTime unitRetryWidthRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition (polynomial_composition
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
    polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) polynomial_first)
      polynomial_second)) polynomial_multiply

theorem polynomial_unitRetryWords : PolynomialTime unitRetryWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_unitRetryWidth polynomial_second) polynomial_wordChunks

theorem polynomial_unitProfileRetry : PolynomialTime unitProfileRetryRealizer :=
  polynomial_composition (polynomial_pair polynomial_first polynomial_unitRetryWords)
    (FirstSuccessProgram.polynomial_retry polynomial_unitPackedTrial)

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

theorem polynomial_parameterUnitWords : PolynomialTime parameterUnitWordsRealizer :=
  polynomial_composition (polynomial_pair polynomial_parameterTrials
    (polynomial_composition (polynomial_pair polynomial_parameterSteps polynomial_parameterProposalWidth)
      polynomial_multiply)) polynomial_multiply

attribute [local irreducible] parameterUnitWords

theorem polynomial_unitSamplingBits : PolynomialTime unitSamplingBitsRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_first polynomial_parameterUnitWords)) polynomial_takeFast

theorem polynomial_unitSamplingInput : PolynomialTime unitSamplingInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_samplingRetryParameters)
    polynomial_unitSamplingBits

theorem polynomial_unitSamplingMatrix : PolynomialTime unitSamplingMatrixRealizer :=
  polynomial_composition polynomial_unitSamplingInput polynomial_unitProfileRetry

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

theorem polynomial_samplingMatrixAll : PolynomialTime samplingMatrixAllRealizer :=
  polynomial_choose (polynomial_composition polynomial_first polynomial_hasLargeRectangle)
    polynomial_samplingMatrix polynomial_unitSamplingMatrix

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

lemma polynomial_exactOrdinaryBits : PolynomialTime exactOrdinaryBitsRealizer :=
  polynomial_composition polynomial_exactSamplingParameters polynomial_parameterWordCount

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactBranchChoice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact dyadic gate that selects the rare correction branch -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream DensePrograms Polynomial

lemma polynomial_rareWord : PolynomialTime rareWordRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_bitValue)
    (polynomial_constant 0)) polynomial_natEqual

lemma work_rareBranch : OnlineTree.WorkBound rareBranchRealizer exactParameterMeasure := by
  apply OnlineTree.work_remeasure
    (FiniteWordExecution.work_realizer polynomial_exactPrecision polynomial_rareWord) X
  intro z
  simp only [FiniteWordExecution.wordMeasure,exactParameterMeasure,eval_X]
  omega

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary execution of an exact integer-weighted rejection trial -/

namespace ContingencyTables.ExactIntegerPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms

lemma polynomial_weightsCode : PolynomialTime weightsCodeRealizer :=
  polynomial_composition (polynomial_pair polynomial_listSum polynomial_identity)
    (polynomial_mapWith (polynomial_composition (polynomial_pair polynomial_second polynomial_first)
      TreeFraction.polynomial_normalize))

lemma polynomial_choiceInput : PolynomialTime choiceInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_weightsCode)
    (polynomial_pair (polynomial_composition polynomial_second polynomial_bitValue)
      (polynomial_composition polynomial_first polynomial_listSum))

lemma polynomial_weightedIndex : PolynomialTime weightedIndexRealizer := by
  unfold weightedIndexRealizer
  apply polynomial_congr
  exact polynomial_choose
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_second polynomial_bitValue)
      (polynomial_composition polynomial_first polynomial_listSum)) polynomial_less)
    (polynomial_composition
      (polynomial_composition polynomial_choiceInput ExecutableChoice.polynomial_chooseFast)
      polynomial_some) (polynomial_constant none)

end ContingencyTables.ExactIntegerPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactIntegerOnline
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The concrete fair-bit integer trial used by exact correction -/

namespace ContingencyTables.ExactIntegerOnline
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ExactIntegerChoice ExactIntegerPrograms FirstSuccess ResidualMixture
open scoped BigOperators Classical

lemma polynomial_trialBits : PolynomialTime trialBitsRealizer :=
  polynomial_composition polynomial_listSum DensePrograms.polynomial_ceilLogTwo

lemma trialBits_le_weight (w : List ℕ) : trialBits w ≤ weight w := by
  rw [trialBits,DensePrograms.clog_two_eq_size_pred]
  exact (Nat.size_le_size (Nat.sub_le _ _)).trans (IntegerMatrixPrograms.sum_size_le_weight w)

theorem polynomial_trial : OnlineTree.PolynomialTime trialRealizer := by
  apply OnlineTree.work_remeasure
    (FiniteWordExecution.work_realizer polynomial_trialBits polynomial_weightedIndex)
    (2*Polynomial.X)
  intro w
  have hb:=trialBits_le_weight w
  simp only [FiniteWordExecution.wordMeasure,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

end ContingencyTables.ExactIntegerOnline

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactMatrixTrial
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Returning a matrix from the exact integer-weighted trial -/

namespace ContingencyTables.ExactMatrixTrial
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open DensePrograms ProfilePrograms

lemma polynomial_lookup : PolynomialTime lookupRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_pair (polynomial_composition polynomial_first polynomial_first)
      polynomial_second) (polynomial_getDFast none))) FirstSuccessProgram.polynomial_default

lemma polynomial_decode : PolynomialTime decodeRealizer := by
  unfold decodeRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition polynomial_second FirstSuccessProgram.polynomial_isSome)
    (polynomial_composition (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition (polynomial_pair (polynomial_constant 0) polynomial_second)
        FirstSuccessProgram.polynomial_default)) polynomial_lookup) polynomial_some)
    (polynomial_constant none)

lemma polynomial_trial : OnlineTree.PolynomialTime trialRealizer := by
  unfold trialRealizer
  apply OnlineTree.work_congr
  exact OnlineTree.polynomial_composition
    (OnlineTree.polynomial_pair (OnlineTree.polynomial_deterministic polynomial_first)
      (OnlineTree.polynomial_composition (OnlineTree.polynomial_deterministic polynomial_second)
        ExactIntegerOnline.polynomial_trial))
    (OnlineTree.polynomial_deterministic polynomial_decode)

end ContingencyTables.ExactMatrixTrial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactOrdinaryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite ordinary branch of the exact sampler -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream DensePrograms Polynomial

lemma polynomial_exactOrdinaryWord : PolynomialTime exactOrdinaryWordRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_exactSamplingParameters) polynomial_second)
    polynomial_samplingMatrixAll

lemma work_exactOrdinary : OnlineTree.WorkBound exactOrdinaryRealizer
    (FiniteWordExecution.wordMeasure exactOrdinaryBits) :=
  FiniteWordExecution.work_realizer polynomial_exactOrdinaryBits polynomial_exactOrdinaryWord

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactGateCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial cost before the rare branch starts -/

namespace ContingencyTables.ExactGateCost
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma budget_polynomial : ∃ p : Polynomial ℕ,
    ∀ z,ExactGatePrefix.budget z ≤ p.eval (measure z) := by
  obtain ⟨p,hp⟩ := work_rareBranch
  obtain ⟨q,hq⟩ := work_exactOrdinary
  refine ⟨p+q+10*X+50,?_⟩
  intro z
  have h1 : rareBranchRealizer.cost z ≤ p.eval (measure z) :=
    (Nat.le_add_right _ _).trans ((hp z).trans (polynomial_eval_monotone p (Nat.le_add_right _ _)))
  have h2 : exactOrdinaryRealizer.cost z ≤ q.eval (measure z) :=
    (Nat.le_add_right _ _).trans ((hq z).trans (polynomial_eval_monotone q (Nat.le_add_left _ _)))
  have h3 : weight z ≤ measure z := by unfold measure exactParameterMeasure; omega
  change rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+10*weight z+50 ≤ _
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  omega

end ContingencyTables.ExactGateCost

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

lemma exact_total_weight : weight (∑ i,r i) ≤ 4*S+1 := by
  have hs : (∑ i,r i).size ≤ Nat.clog 2 ((∑ i,r i)+1) :=
    Nat.size_le.mpr (Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
      (Nat.le_pow_clog (by decide) _))
  have hw := weight_nat_le (∑ i,r i)
  unfold samplingSize
  omega

lemma exact_matrix_size : ExactPrintCost.matrixSize (n := n) r ≤ 25*S^3 := by
  have hS : 1 ≤ S := by unfold samplingSize; omega
  have hm : m ≤ S := by unfold samplingSize; omega
  have hn : n ≤ S := by unfold samplingSize; omega
  have hw : 4*weight (∑ i,r i)+2 ≤ 22*S := by
    have := exact_total_weight (n := n) r
    omega
  have hpow : S ≤ S^3 := Nat.le_self_pow (by decide) _
  calc
    _ ≤ S*(S*(22*S)+2)+1 := by unfold ExactPrintCost.matrixSize; gcongr
    _ ≤ 25*S^3 := by nlinarith

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

lemma exact_gate_measure_polynomial : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i,r i)=∑ j,c j → ExactGateCost.measure (List.ofFn r,List.ofFn c) ≤
        p.eval (samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := exact_parameter_polynomial
  obtain ⟨q,hq⟩ := exact_margin_weight_polynomial
  obtain ⟨u,hu⟩ := exact_ordinary_bits_polynomial
  refine ⟨p+q+u,?_⟩
  intro m n r c htotal
  simpa only [ExactGateCost.measure,FiniteWordExecution.wordMeasure,eval_add,add_assoc]
    using Nat.add_le_add (hp m n r c htotal)
      (Nat.add_le_add (hq m n r c htotal) (hu m n r c))

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_PhysicalCostPolynomial
attribute [-instance] _root_.OAI.ContingencyTables.BalancedEnumeration.assignmentsFintype _root_.OAI.ContingencyTables.BalancedFamily.coordinatesFintype _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.ContingencyTables.GridBoundary.instFintypeCutEdge _root_.OAI.ContingencyTables.GridBoundary.instFintypeSelected _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial arithmetic for the physical compiler's explicit cost -/

namespace ContingencyTables.PhysicalCostPolynomial
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial
noncomputable section

theorem bound (a o : ℕ) (t : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ H C N B M : ℕ,H ≤ M → C ≤ t.eval M → N ≤ M → B ≤ M →
      LiteralProgram.packTime N+C*(o*(1+2*a*(H+C*a+1))+1)+LiteralProgram.postTime B ≤
        p.eval M := by
  let fac : Polynomial ℕ := C o*(1+2*C a*(X+t*C a+1))+1
  let pk : Polynomial ℕ := (1+LiteralProgram.budgetPolynomial 1 (18*LiteralPacked.width) X 0)*
    C (MachineCost.programCost LiteralPacked.packCode)
  let out : Polynomial ℕ := C (MachineCost.programCost (LiteralTape.eraseCode LiteralPacked.header.length))+
    (1+LiteralProgram.budgetPolynomial (18*LiteralPacked.width) 1 X 0)*
      C (MachineCost.programCost LiteralPacked.unpackCode)
  refine ⟨pk+t*fac+out,?_⟩
  intro H K N B M hH hK hN hB
  have hf : o*(1+2*a*(H+K*a+1))+1 ≤ fac.eval M := by
    simp only [fac,eval_add,eval_mul,eval_C,eval_ofNat,eval_X,eval_one]
    gcongr
  have hpk : pk.eval M=LiteralProgram.packTime M := by
    simp only [pk,eval_mul,eval_add,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.packTime]
  have hout : out.eval M=LiteralProgram.postTime M := by
    simp only [out,eval_add,eval_mul,eval_one,eval_C,LiteralProgram.eval_budgetPolynomial,
      eval_X,eval_zero,LiteralProgram.postTime]
  simp only [eval_add,eval_mul,hpk,hout]
  exact Nat.add_le_add (Nat.add_le_add (LiteralProgram.packTime_mono hN)
    (Nat.mul_le_mul hK hf)) (LiteralProgram.postTime_mono hB)

end
end ContingencyTables.PhysicalCostPolynomial

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactRareCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial dependence of the correction cost on its finite tabulation measure -/

namespace ContingencyTables.ExactRareCost
open MatchingFPRAS MatchingFPRAS.TreeTyped MatchingFPRAS.PhysicalStream
open ProfilePrograms DensePrograms Polynomial
noncomputable section

attribute [local irreducible] ExactTypedProgram.program exactParsedMargins
  ExactGateCost.measure exactRareMeasure exactMatrixInput

theorem core_polynomial : ∃ p : Polynomial ℕ,∀ z,
    ExactCoreCost.budget z 1 ≤ p.eval (measure z) := by
  obtain ⟨g,hg⟩ := ExactGateCost.budget_polynomial
  obtain ⟨p,hp⟩ := work_exactMatrixInput
  obtain ⟨q,hq⟩ := ExactMatrixTrial.polynomial_trial
  refine ⟨g+p+q.comp p+12*p+C (weight (default : MatrixCode)+40),?_⟩
  intro z
  have hgate : ExactGatePrefix.budget z ≤ g.eval (measure z) :=
    (hg z).trans (polynomial_eval_monotone g (Nat.le_add_right _ _))
  have hmatrix : exactMatrixInputRealizer.cost z+weight (exactMatrixInput z) ≤ p.eval (measure z) :=
    (hp z).trans (polynomial_eval_monotone p (Nat.le_add_left _ _))
  have hw : weight (exactMatrixInput z) ≤ p.eval (measure z) :=
    (Nat.le_add_left _ _).trans hmatrix
  have htrial := (Nat.le_add_right _ _).trans
    ((hq (exactMatrixInput z)).trans (polynomial_eval_monotone q hw))
  change ExactMatrixTrial.trialRealizer.cost (exactMatrixInput z) ≤ q.eval (p.eval (measure z)) at htrial
  change rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+exactMatrixInputRealizer.cost z+
    1*(ExactMatrixTrial.trialRealizer.cost (exactMatrixInput z)+12*weight (exactMatrixInput z)+
      weight (default : MatrixCode)+40)+10*weight z+50 ≤ _
  change rareBranchRealizer.cost z+exactOrdinaryRealizer.cost z+10*weight z+50 ≤ _ at hgate
  simp only [eval_add,eval_mul,eval_ofNat,eval_C,eval_comp]
  omega

/-- All copying and physical simulation costs are polynomial in the
already explicit finite-tabulation measure. -/
theorem public_polynomial : ∃ p : Polynomial ℕ,∀ as B,
    LiteralProgram.packTime as.length+ExactPhysicalCost.budget as 1 B+
      LiteralProgram.postTime B+1 ≤ p.eval (publicMeasure as B) := by
  obtain ⟨p,hp⟩ := polynomial_exactParsedMargins
  obtain ⟨q,hq⟩ := core_polynomial
  let t : Polynomial ℕ := p+q+X
  obtain ⟨v,hv⟩ := PhysicalCostPolynomial.bound
    (OnlineStack.accesses ExactTypedProgram.program.code)
    (OnlineStack.overhead ExactTypedProgram.program.code) t
  refine ⟨v+1,?_⟩
  intro as B
  let M := publicMeasure as B
  have hw : weight as ≤ M := by unfold M publicMeasure; omega
  have hg : measure (exactParsedMargins as) ≤ M := by unfold M publicMeasure; omega
  have hB : B ≤ M := by unfold M publicMeasure; omega
  have ht : ExactPhysicalCost.typedBudget as 1 B ≤ t.eval M := by
    have hp' := (Nat.le_add_right _ _).trans ((hp as).trans (polynomial_eval_monotone p hw))
    have hq' := (hq _).trans (polynomial_eval_monotone q hg)
    simpa only [ExactPhysicalCost.typedBudget,t,eval_add,eval_X] using
      Nat.add_le_add (Nat.add_le_add hp' hq') hB
  have hb := hv (weight as) (ExactPhysicalCost.typedBudget as 1 B) as.length B M hw ht
    ((list_length_le_weight as).trans hw) hB
  simpa only [ExactPhysicalCost.budget,OnlineStack.Executes.factor,eval_add,eval_one]
    using Nat.add_le_add_right hb 1

end
end ContingencyTables.ExactRareCost

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_RareBranchRuntime
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The correction probability absorbs the cost of finite tabulation -/

namespace ContingencyTables.RareBranchRuntime
open Polynomial ProfilePrograms

/-- The coefficient in a fixed exponential running-time bound need not be
smaller than the coefficient used in the sampler's precision schedule. -/
lemma linear_le_square_add (k s : ℕ) : k * s ≤ s ^ 2 + k ^ 2 := by
  have h := two_mul_le_add_sq (k : ℤ) (s : ℤ)
  have : (k : ℤ)*s≤(s : ℤ)^2+(k : ℤ)^2 := by nlinarith
  exact_mod_cast this

lemma dyadic_linear_bound (k s D : ℕ) (hD : s^2≤D) :
    (2:ℕ)^(k*s)≤2^D*2^(k^2) := by
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) ((linear_le_square_add k s).trans
    (Nat.add_le_add_right hD _))

/-- A polynomial in an exponential tabulation size remains affordable
after multiplying by the rare-branch probability `2⁻ᴰ`. -/
theorem polynomial_tabulation_bound (p : Polynomial ℕ) (A s a D : ℕ)
    (hD : s^2≤D) :
    p.eval (A*2^(a*s))≤2^D*(p.eval A*2^((a*p.natDegree)^2)) := by
  calc
    p.eval (A*2^(a*s))≤p.eval A*2^((a*s)*p.natDegree) :=
      polynomial_scaled_power p A 2 (a*s) (by decide)
    _ = p.eval A*2^((a*p.natDegree)*s) := by
      rw [Nat.mul_right_comm a s p.natDegree]
    _ ≤ p.eval A*(2^D*2^((a*p.natDegree)^2)) :=
      Nat.mul_le_mul_left _ (dyadic_linear_bound (a*p.natDegree) s D hD)
    _ = 2^D*(p.eval A*2^((a*p.natDegree)^2)) := by ring

end ContingencyTables.RareBranchRuntime

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

lemma exactBoxScale_pos : 1 ≤ exactBoxScale r c := by
  exact one_le_pow₀ (by decide)

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactRarePublicBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Absorbing the actual public correction cost by its branch probability -/

namespace ContingencyTables.SmallGraphProfiles
open MatchingFPRAS MatchingFPRAS.TreeTyped ProfilePrograms DensePrograms CompletionCounts Polynomial
open scoped BigOperators Classical
noncomputable section

lemma exact_scale_absorbed {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (p : Polynomial ℕ) (A : ℕ) :
    p.eval (A*exactBoxScale r c) ≤ 2^(correctionPrecision r c)*
      (p.eval A*2^((40*p.natDegree)^2)) := by
  apply RareBranchRuntime.polynomial_tabulation_bound
  change ((dimensionAllowance (I := Fin m) (J := Fin n))^3*smallBinaryLength r c)^2 ≤
    (dimensionAllowance (I := Fin m) (J := Fin n))^6*(smallBinaryLength r c)^2
  rw [mul_pow,←pow_mul]

theorem exact_public_correction_bound_oai (print : Polynomial ℕ) : ∃ p : Polynomial ℕ,
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ), (∑ i,r i)=∑ j,c j →
    let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
    ExactPublicCost.budget r c 1 B B+1 ≤
      2^(correctionPrecision r c)*p.eval (Algorithms.samplingSize n r 0) := by
  obtain ⟨p,hp⟩ := ExactRareCost.public_polynomial
  obtain ⟨q,a,hq⟩ := exact_rare_measure_bound
  obtain ⟨g,hg⟩ := exact_gate_measure_polynomial
  let H := a+g+91*X^2+print.comp (25*X^3)+1
  let P := p.comp (X+q)
  refine ⟨C (2^((40*P.natDegree)^2))*(P.comp H),?_⟩
  intro m n r c htotal
  let B := print.eval (ExactPrintCost.matrixSize (n := n) r)
  let S := Algorithms.samplingSize n r 0
  let E := exactBoxScale r c
  let W := H.eval S*E
  have hE : 1 ≤ E := exactBoxScale_pos r c
  have hHW : H.eval S ≤ W := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (H.eval S) hE
  have ha : a.eval S ≤ H.eval S := by simp only [H,eval_add,eval_one]; omega
  have hrare : exactRareMeasure (List.ofFn r,List.ofFn c) ≤ q.eval W :=
    (hq m n r c htotal).trans (polynomial_eval_monotone q (Nat.mul_le_mul_right E ha))
  have hscalar : weight (Algorithms.encodeMargins r c)+
      ExactGateCost.measure (List.ofFn r,List.ofFn c)+B ≤ H.eval S := by
    have hw := exact_public_weight r c htotal
    have hgate := hg m n r c htotal
    have hprint : print.eval (ExactPrintCost.matrixSize (n := n) r) ≤ print.eval (25*S^3) :=
      polynomial_eval_monotone print (exact_matrix_size (n := n) r)
    simp only [H,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_comp,eval_one]
    unfold B S at *
    omega
  have hmeasure : ExactRareCost.publicMeasure (Algorithms.encodeMargins r c) B ≤ (X+q).eval W := by
    change weight (Algorithms.encodeMargins r c)+
      (ExactGateCost.measure (ProfilePrograms.exactParsedMargins (Algorithms.encodeMargins r c))+
        exactRareMeasure (ProfilePrograms.exactParsedMargins (Algorithms.encodeMargins r c)))+B ≤ _
    rw [exactParsedMargins_spec]
    simp only [eval_add,eval_X]
    omega
  have hcost : ExactPublicCost.budget r c 1 B B+1 ≤ P.eval W := by
    have ht := (hp (Algorithms.encodeMargins r c) B).trans (polynomial_eval_monotone p hmeasure)
    simpa only [ExactPublicCost.budget,ExactTablePrefix.input,P,eval_comp] using ht
  have habsorb := exact_scale_absorbed r c P (H.eval S)
  apply hcost.trans (habsorb.trans_eq ?_)
  simp only [eval_mul,eval_C,eval_comp]
  ring

end
end ContingencyTables.SmallGraphProfiles

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound_oai := @OAI.ContingencyTables.SmallGraphProfiles.exact_public_correction_bound_oai
