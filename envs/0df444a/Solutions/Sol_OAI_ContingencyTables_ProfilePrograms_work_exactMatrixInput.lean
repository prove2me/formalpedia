-- Prove2me | solution 1 for OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T04:27:24.423992+00:00
-- url     : https://prove2.me/submissions/4b4ee67a-60a6-4cb0-a2ce-292faf2dbe4c

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009
import Definitions.Def_OAIQ089A010
import Theorems.Thm_OAI_ContingencyTables_ProfilePrograms_work_optionalTrialCount

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
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
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

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.MatchingCount_Complexity_TreeNumericCosts
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
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

theorem polynomial_matrixEntry : PolynomialTime matrixEntryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair polynomial_first
      (polynomial_composition polynomial_second polynomial_first)) (polynomial_getDFast []))
    (polynomial_composition polynomial_second polynomial_second)) (polynomial_getDFast 0)

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

theorem polynomial_isSome : PolynomialTime (isSomeRealizer (B := B)) := by
  unfold isSomeRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_constant false) polynomial_identity)
    (polynomial_optionCases (polynomial_constant false) (polynomial_constant true))

theorem polynomial_default : PolynomialTime (defaultRealizer (B := B)) := by
  unfold defaultRealizer
  apply polynomial_recode
  exact polynomial_optionCases polynomial_identity polynomial_second

end ContingencyTables.FirstSuccessProgram

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

lemma polynomial_gridCoordinate : PolynomialTime gridCoordinateRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_second)
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_first polynomial_first) polynomial_second)
        polynomial_clippedGridPower)) polynomial_quotient)
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      polynomial_second)) polynomial_remainder

lemma polynomial_gridCoordinateIndices : PolynomialTime gridCoordinateIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    polynomial_first polynomial_first) polynomial_listLength) Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_gridCoordinates : PolynomialTime gridCoordinatesRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_gridCoordinateIndices)
    (polynomial_mapWith polynomial_gridCoordinate)

lemma polynomial_gridStateCount : PolynomialTime gridStateCountRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity
    (polynomial_composition polynomial_first polynomial_listLength)) polynomial_clippedGridPower

/-- State enumeration is polynomial in its output count, not in the
precision or number of fair random words of the sampler. -/
theorem work_gridWords : WorkBound gridWordsRealizer
    (fun z => gridStateCount z+weight z) := by
  have hp : WorkBound gridStateCountRealizer (fun z => gridStateCount z+weight z) :=
    work_of_polynomial polynomial_gridStateCount Polynomial.X (fun z => by simp)
  have hr : WorkBound (composition gridStateCountRealizer range)
      (fun z => gridStateCount z+weight z) :=
    work_composition hp range_numeric_work Polynomial.X (fun z => by simp)
  unfold gridWordsRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_gridCoordinates)
  apply work_pair
    (work_of_polynomial polynomial_identity Polynomial.X (fun z => by simp)) hr
    Polynomial.X (fun z => by simp)

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_MatrixCodeEquality
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Polynomial equality of explicitly stored rectangular arrays -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS.TreeTyped

lemma polynomial_matrixSignature : PolynomialTime matrixSignatureRealizer :=
  polynomial_pair (polynomial_map polynomial_listLength) polynomial_flatten

lemma polynomial_matrixEqual : PolynomialTime matrixEqual := by
  unfold matrixEqual
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_matrixSignature)
    (polynomial_composition polynomial_second polynomial_matrixSignature))
    ProfilePrograms.polynomial_profileCodeEqual

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

/-- Unary markers are charged by the actual requested loop length. -/
lemma work_unaryMarkers : WorkBound unaryMarkersRealizer id :=
  work_then_polynomial range_numeric_work (polynomial_map (polynomial_constant false))

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_RetryNumeratorProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary first-success numerators via a two-coordinate recurrence -/

namespace ContingencyTables.RetryNumeratorPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped

lemma polynomial_twoEntries {A : Type} [Codec A] : PolynomialTime (twoEntries (A := A)) :=
  polynomial_composition (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second BinaryPowerPrograms.polynomial_singleton))
    polynomial_listCons

lemma polynomial_setup : PolynomialTime setupRealizer := by
  have hQ : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) first) first) := by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
  have hphi : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) first) second) := by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
  have halpha : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) second) first) := by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
  have hhit : PolynomialTime (composition (composition
      (second (A := List Bool) (B := (ℕ×ℕ)×(ℕ×Bool))) second) second) := by ((with_reducible repeat' (first | assumption | exact polynomial_identity | exact polynomial_first | exact polynomial_second | exact polynomial_boolAnd | exact polynomial_boolOr | exact polynomial_boolNot | exact polynomial_add | exact polynomial_subtract | exact polynomial_multiply | exact polynomial_less | exact polynomial_leNat | exact polynomial_natEqual | exact polynomial_finsetList | exact polynomial_finsetCard | exact polynomial_finsetSingleton | exact polynomial_listCons | exact polynomial_listLength | exact polynomial_append | exact polynomial_reverse | exact polynomial_flatten | apply polynomial_congr | apply polynomial_recode | apply polynomial_composition | apply polynomial_pair | apply polynomial_choose | apply polynomial_constant | apply polynomial_fst | apply polynomial_snd | apply polynomial_map | apply polynomial_mapWith | apply polynomial_flatMapPoly | apply polynomial_filter | apply polynomial_filterWith | apply polynomial_finsetBiUnion | apply polynomial_finsetFilter | apply polynomial_finsetFilterWith | apply polynomial_finsetImage | apply polynomial_finsetUnion | apply polynomial_finsetSDiff | apply polynomial_finsetInter | apply polynomial_finsetErase | apply polynomial_finsetInsert | apply polynomial_finsetEqual | apply polynomial_finsetSubset | apply polynomial_finsetMember | apply polynomial_finsetAny | apply polynomial_finsetAll | apply polynomial_pairEqual | apply polynomial_lexLe | apply polynomial_colexLe)))
  unfold setupRealizer
  exact polynomial_pair (polynomial_composition polynomial_first polynomial_listLength)
    (polynomial_pair (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair hphi halpha) polynomial_twoEntries)
      (polynomial_composition (polynomial_pair (polynomial_constant 0) hQ) polynomial_twoEntries))
      polynomial_twoEntries)
      (polynomial_composition (polynomial_pair
        (polynomial_choose hhit (polynomial_constant 1) (polynomial_constant 0))
        (polynomial_constant 1)) polynomial_twoEntries))

/-- All stored numbers are binary; only the supplied trial marker controls
iteration, so evaluation is polynomial in that marker and binary data. -/
theorem polynomial_count : PolynomialTime countRealizer := by
  have hi : PolynomialTime (composition setupRealizer IntegerMatrixPrograms.iterateRealizer) := by
    obtain ⟨p,hp⟩ := polynomial_setup
    apply work_composition ⟨p,hp⟩ IntegerMatrixPrograms.work_iterate (Polynomial.X+p)
    intro z
    have hl := (list_length_le_weight z.1).trans (weight_fst z)
    have hw := weight_snd (setup z)
    have hc := hp z
    simp only [Polynomial.eval_add,Polynomial.eval_X,setup] at *
    omega
  exact polynomial_composition hi (polynomial_head 0)

end ContingencyTables.RetryNumeratorPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_VectorRetryProgram
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # First-success propagation of an entire vector of integer counts -/

namespace ContingencyTables.VectorRetryPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators

lemma polynomial_failure : PolynomialTime failureRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first)
      polynomial_listSum)) polynomial_subtract

lemma polynomial_entryInput : PolynomialTime entryInputRealizer := by
  unfold entryInputRealizer
  exact polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_pair (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
      (polynomial_composition polynomial_first polynomial_failure))
      (polynomial_pair (polynomial_composition (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
        polynomial_second) (polynomial_getDFast 0))
        (polynomial_composition (polynomial_pair polynomial_second
          (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
            polynomial_second)) polynomial_natEqual)))

lemma polynomial_indices : PolynomialTime indicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    polynomial_second polynomial_first) polynomial_listLength) Polynomial.X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.2.1).trans ((weight_fst z.2).trans (weight_snd z))

/-- Binary vector propagation uses time polynomial in the success-vector
encoding and in the supplied number of trial markers. -/
theorem polynomial_counts : PolynomialTime countsRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_indices)
    (polynomial_mapWith (polynomial_composition polynomial_entryInput
      RetryNumeratorPrograms.polynomial_count))

end ContingencyTables.VectorRetryPrograms

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

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_BooleanEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Enumerating only the short proposal word -/

namespace ContingencyTables.DensePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma polynomial_digitBool : PolynomialTime digitBoolRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant 1))
    polynomial_natEqual

lemma work_booleanWords : WorkBound booleanWordsRealizer
    (fun xs => gridStateCount (xs,2)+weight xs) := by
  have hi : WorkBound (pair (identity (A := List Bool)) (constant 2))
      (fun xs => gridStateCount (xs,2)+weight xs) :=
    work_of_polynomial (polynomial_pair polynomial_identity (polynomial_constant 2))
      Polynomial.X (fun xs => by simp)
  have hg : WorkBound (composition (pair (identity (A := List Bool)) (constant 2))
      gridWordsRealizer) (fun xs => gridStateCount (xs,2)+weight xs) := by
    apply work_composition hi work_gridWords (Polynomial.X+10)
    intro xs
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,weight_prod,id_eq]
    have hc : weight (2:ℕ)≤9 := by simpa using weight_nat_numeric 2
    omega
  unfold booleanWordsRealizer
  exact work_then_polynomial hg (polynomial_map (polynomial_map polynomial_digitBool))

end ContingencyTables.DensePrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_CachedTerminalCount
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Exact terminal counts from the retained dense-completion cache -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_successfulWeight : PolynomialTime successfulWeightRealizer := by
  unfold successfulWeightRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_pair (polynomial_pair polynomial_first
    (polynomial_composition polynomial_second polynomial_second))
    (polynomial_composition polynomial_second polynomial_first))
    (polynomial_optionCases (polynomial_constant 0) (polynomial_choose
      (polynomial_composition (polynomial_pair polynomial_second
        (polynomial_composition polynomial_first polynomial_first)) polynomial_matrixEqual)
      (polynomial_composition polynomial_first polynomial_second) (polynomial_constant 0)))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ResidualWeightProgram
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary computation of the rare branch's integer weights -/

namespace ContingencyTables.ResidualWeightPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped
open scoped BigOperators Classical

lemma polynomial_count : PolynomialTime countRealizer := by
  unfold countRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first)
      (polynomial_composition polynomial_first polynomial_second)) polynomial_multiply)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_pair
        (polynomial_composition polynomial_second polynomial_first)
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second)
          polynomial_predecessor)) polynomial_multiply)
      (polynomial_composition polynomial_second polynomial_second)) polynomial_multiply))
    polynomial_subtract

end ContingencyTables.ResidualWeightPrograms

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

lemma work_originalCandidates : WorkBound originalCandidatesRealizer originalEnumerationMeasure := by
  have hp : WorkBound originalEnumerationDataRealizer originalEnumerationMeasure :=
    work_of_polynomial polynomial_originalEnumerationData X
      (fun z => by simp only [Polynomial.eval_X,originalEnumerationMeasure]; omega)
  obtain ⟨p,hp'⟩ := hp
  have hg : WorkBound (composition originalEnumerationDataRealizer gridWordsRealizer)
      originalEnumerationMeasure := by
    apply work_composition ⟨p,hp'⟩ work_gridWords (X+p)
    intro z
    have hw := hp' z
    simp only [Polynomial.eval_add,Polynomial.eval_X]
    change gridStateCount (originalEnumerationData z)+weight (originalEnumerationData z) ≤ _
    unfold originalEnumerationMeasure at hw ⊢
    omega
  unfold originalCandidatesRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_originalCandidate)
  exact work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simp only [Polynomial.eval_X,originalEnumerationMeasure]; omega)) hg X
    (fun z => by simp only [Polynomial.eval_X,originalEnumerationMeasure]; omega)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableIndex
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Binary lookup of an original table's finite-box index -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_originalIndexInput : PolynomialTime originalIndexInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_flatten)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_listSum) polynomial_successor)

lemma polynomial_originalIndex : PolynomialTime originalIndexRealizer :=
  polynomial_composition polynomial_originalIndexInput polynomial_gridIndex

end ContingencyTables.ProfilePrograms

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
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileBoxEnumeration
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executable enumeration of the bounded two-view profile box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_profileEnumerationData : PolynomialTime profileEnumerationDataRealizer := by
  unfold profileEnumerationDataRealizer
  exact polynomial_pair (polynomial_composition
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first))
      polynomial_append) (polynomial_map (polynomial_constant false)))
    (polynomial_composition polynomial_second polynomial_successor)

lemma work_profileBoxViews : WorkBound profileBoxViewsRealizer
    (fun z => gridStateCount (profileEnumerationData z)+weight z) := by
  have hp : WorkBound profileEnumerationDataRealizer
      (fun z => gridStateCount (profileEnumerationData z)+weight z) :=
    work_of_polynomial polynomial_profileEnumerationData Polynomial.X (fun z => by simp)
  obtain ⟨p,hp'⟩ := hp
  have hw : WorkBound (composition profileEnumerationDataRealizer gridWordsRealizer)
      (fun z => gridStateCount (profileEnumerationData z)+weight z) := by
    apply work_composition ⟨p,hp'⟩ work_gridWords (Polynomial.X+p)
    intro z
    have h := hp' z
    simp only [Polynomial.eval_add,Polynomial.eval_X]
    change gridStateCount (profileEnumerationData z)+weight (profileEnumerationData z)≤_
    change _≤p.eval (gridStateCount (profileEnumerationData z)+weight z) at h
    omega
  unfold profileBoxViewsRealizer
  apply work_then_polynomial _ (polynomial_mapWith polynomial_splitViews)
  apply work_pair _ hw Polynomial.X (fun z => by simp)
  apply work_of_polynomial _ Polynomial.X (fun z => by simp)
  exact polynomial_composition (polynomial_composition
    (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    polynomial_listLength

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

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MeasuredFold
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # List folds with the cost of each cached computation accounted for -/

namespace ContingencyTables.MeasuredFold
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

variable {A B : Type} [Codec A] [Codec B]

/-- The loop cost is polynomial in one common external measure whenever
each reached call and each stored accumulator satisfy such a bound. -/
lemma work_fold {f : A×B → B} (F : Realizer f) (measure : List A×B → ℕ)
    (p q : Polynomial ℕ)
    (hinput : ∀ z,weight z ≤ measure z)
    (hcall : ∀ (as : List A) (b : B) pre a post,as=pre++a::post →
      F.cost (a,pre.foldl (fun z c => f (c,z)) b) ≤ p.eval (measure (as,b)))
    (hstate : ∀ (as : List A) (b : B) pre post,as=pre++post →
      weight (pre.foldl (fun z a => f (a,z)) b) ≤ q.eval (measure (as,b))) :
    WorkBound (fold F) measure := by
  refine ⟨X*(p+14*X+34)+10+q,?_⟩
  rintro ⟨as,b⟩
  let S := measure (as,b)
  have hs : weight as ≤ S := by
    have hi := hinput (as,b)
    rw [weight_prod] at hi
    exact le_trans (by omega : weight as≤1+weight as+weight b) hi
  have hc := Fold.cost_prefix_bound (f := f) F.cost as b (p.eval S) S hs
    (hcall as b)
  have hout := hstate as b as [] (by simp)
  have hlen : as.length ≤ S := (list_length_le_weight as).trans hs
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  change Fold.cost f F.cost as b+weight (as.foldl (fun z a => f (a,z)) b) ≤ _
  change _ ≤ S*(p.eval S+14*S+34)+10+q.eval S
  have hm := Nat.mul_le_mul_right (p.eval S+14*S+34) hlen
  change _ ≤ q.eval S at hout
  omega

end ContingencyTables.MeasuredFold

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_MeasuredMap
attribute [-instance] _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.instCodecOptionOfInhabited
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Costs for mapping cached computations over a finite list -/

namespace ContingencyTables.MeasuredMap
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

variable {A B C : Type} [Codec A] [Codec B] [Codec C]

/-- The map accumulator adds linear copying overhead to one call of the
underlying computation. Its cost may use an external finite-box measure. -/
lemma mapStep_cost {f : A×B → C} (F : Realizer f) (a : A) (b : B) (cs : List C) :
    (mapStepRealizer F).cost (b,(a,cs)) ≤
      F.cost (a,b)+500*(weight a+weight b+weight cs+weight (f (a,b))+1) := by
  simp only [mapStepRealizer,composition,pair,first,second,listCons,Function.comp_apply]
  simp only [weight,encode_prod,MatchingFPRAS.TreeFunction.size_cons]
  omega

private lemma measure_entry (μ : A×B → ℕ) (as : List B) (a : A) (cs : List C)
    (b : B) (hb : b∈as) : μ (a,b) ≤ foldMeasure μ (as,(a,cs)) := by
  have h := List.single_le_sum (fun _ _ => Nat.zero_le _) (μ (a,b))
    (List.mem_map.mpr ⟨b,hb,rfl⟩ : μ (a,b)∈as.map (fun b => μ (a,b)))
  exact h.trans (Nat.le_add_left _ _)

/-- Mapping a finite list costs a polynomial in its encoded size and
in the sum of the work measures of its individual cached computations. -/
lemma work_mapWith {f : A×B → C} (F : Realizer f) (μ : A×B → ℕ)
    (hF : WorkBound F μ) : WorkBound (mapWith F) (listMeasure μ) := by
  obtain ⟨p,hp⟩ := hF
  let q : Polynomial ℕ := 2*X+X*(p+1)+2
  have hstate (as : List B) (a : A) (cs : List C) (pre post : List B)
      (he : as=pre++post) :
      weight (pre.foldl (fun z b => mapStep f (b,z)) (a,cs)) ≤
        q.eval (foldMeasure μ (as,(a,cs))) := by
    let S := foldMeasure μ (as,(a,cs))
    have hi : weight (as,(a,cs)) ≤ S := Nat.le_add_right _ _
    have hbs : weight as ≤ S := by rw [weight_prod] at hi; omega
    have ha : weight a ≤ S := by simp only [weight_prod] at hi; omega
    have hc : weight cs ≤ S := by simp only [weight_prod] at hi; omega
    have hl : pre.length ≤ S := (list_length_le_weight pre).trans ((weight_prefix he).trans hbs)
    have hm := weight_map_bound (as := pre) (f := fun b => f (a,b)) (N := p.eval S) (by
      intro b hb
      have hμ := measure_entry μ as a cs b (by rw [he]; exact List.mem_append_left _ hb)
      have ht := polynomial_eval_monotone p hμ
      have hf := hp (a,b)
      change p.eval (μ (a,b)) ≤ p.eval S at ht
      omega)
    rw [mapStep_fold,weight_prod]
    have happ := weight_append (pre.map (fun b => f (a,b))).reverse cs
    rw [weight_reverse] at happ
    change _ ≤ q.eval S
    simp only [q,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
      Polynomial.eval_ofNat,Polynomial.eval_one]
    have hlm := Nat.mul_le_mul_right (p.eval S+1) hl
    omega
  have hfold : WorkBound (fold (mapStepRealizer F)) (foldMeasure μ) := by
    apply MeasuredFold.work_fold _ _ (p+500*(2*X+q+p+1)) q
    · intro z
      exact Nat.le_add_right _ _
    · rintro as ⟨a,cs⟩ pre b post he
      let S := foldMeasure μ (as,(a,cs))
      have hz := hstate as a cs pre (b::post) he
      have hi : weight (as,(a,cs)) ≤ S := Nat.le_add_right _ _
      have ha : weight a ≤ S := by simp only [weight_prod] at hi; omega
      have hb : weight b ≤ S := (weight_mem (show b∈as by rw [he]; simp)).trans (by
        simp only [weight_prod] at hi; omega)
      have hμ := measure_entry μ as a cs b (by rw [he]; simp)
      have ht := polynomial_eval_monotone p hμ
      have hf := hp (a,b)
      change p.eval (μ (a,b)) ≤ p.eval S at ht
      rw [mapStep_fold] at hz ⊢
      have hcs : weight ((pre.map (fun b => f (a,b))).reverse++cs) ≤ q.eval S := by
        rw [weight_prod] at hz
        exact (Nat.le_add_left _ _).trans hz
      have hm := mapStep_cost F a b ((pre.map (fun b => f (a,b))).reverse++cs)
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
        Polynomial.eval_X,Polynomial.eval_one]
      change _ ≤ p.eval S+500*(2*S+q.eval S+p.eval S+1)
      apply hm.trans
      have hcost : F.cost (a,b) ≤ p.eval S := (Nat.le_add_right _ _).trans (hf.trans ht)
      have hout : weight (f (a,b)) ≤ p.eval S := (Nat.le_add_left _ _).trans (hf.trans ht)
      omega
    · rintro as ⟨a,cs⟩ pre post he
      exact hstate as a cs pre post he
  unfold mapWith
  apply work_congr
  apply work_then_polynomial _ (polynomial_composition polynomial_second polynomial_reverse)
  have hi : WorkBound (pair (second (A := A)) (pair first (constant ([] : List C))))
      (listMeasure μ) :=
    work_of_polynomial
      (polynomial_pair polynomial_second (polynomial_pair polynomial_first (polynomial_constant []))) X
      (fun z => by simp only [Polynomial.eval_X,listMeasure]; omega)
  apply work_composition hi hfold (X+2)
  rintro ⟨a,bs⟩
  simp only [foldMeasure,listMeasure,weight_prod,weight_nil,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

end ContingencyTables.MeasuredMap

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ProfileTerminalProgram
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing terminal success weights at every enumerated profile -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma polynomial_terminalSourceInput : PolynomialTime terminalSourceInputRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_first))

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Transport_IntegerMatrixPoint
attribute [-instance] _root_.OAI.ContingencyTables.BalancedFamily.coordinatesDecidableEq _root_.OAI.ContingencyTables.FirstSuccess.dependentJointNonempty _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Propagating an executable point mass through an integer matrix -/

namespace ContingencyTables.IntegerMatrixPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped Polynomial

lemma polynomial_pointEntry : PolynomialTime pointEntryRealizer := by
  unfold pointEntryRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition
    (polynomial_pair polynomial_second polynomial_first) polynomial_natEqual)
    (polynomial_constant 1) (polynomial_constant 0)

lemma polynomial_pointVector : PolynomialTime pointVectorRealizer := by
  unfold pointVectorRealizer
  apply polynomial_composition _ (polynomial_mapWith polynomial_pointEntry)
  apply polynomial_pair polynomial_second
  apply polynomial_boundedRange (polynomial_composition polynomial_first polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1).trans (weight_fst z)

lemma polynomial_fromPointInput : PolynomialTime fromPointInputRealizer :=
  polynomial_pair polynomial_first (polynomial_pair
    (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition polynomial_second polynomial_pointVector))

lemma work_fromPoint : WorkBound fromPointRealizer (fun z => z.1+weight z.2) := by
  have hi : WorkBound fromPointInputRealizer (fun z => z.1+weight z.2) :=
    work_of_polynomial polynomial_fromPointInput (4*X+2) (by
      intro z
      have hn := weight_nat_numeric z.1
      rw [←Prod.eta z,weight_prod]
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      omega)
  obtain ⟨p,hp⟩ := hi
  unfold fromPointRealizer
  apply work_composition ⟨p,hp⟩ work_iterate (X+p)
  intro z
  have hz := hp z
  dsimp only at hz
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  change z.1+weight (z.2.1,pointVector z.2) ≤ _
  have hw : weight (z.2.1,pointVector z.2) ≤ weight (z.1,(z.2.1,pointVector z.2)) :=
    weight_snd (z.1,(z.2.1,pointVector z.2))
  omega

end ContingencyTables.IntegerMatrixPrograms

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

lemma work_trialVector : WorkBound trialVectorRealizer trialVectorMeasure := by
  have hi (z : TrialVectorInput) : weight z ≤ X.eval (trialVectorMeasure z) := by
    simp only [Polynomial.eval_X,trialVectorMeasure]
    omega
  have he : WorkBound (composition (second (A := WalkCountInput)) originalCandidatesRealizer)
      trialVectorMeasure := by
    apply work_composition (work_of_polynomial polynomial_second X hi) work_originalCandidates X
    intro z
    simp only [Polynomial.eval_X,trialVectorMeasure]
    omega
  unfold trialVectorRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_first X hi) he X hi)
    (MeasuredMap.work_mapWith _ _ work_optionalTrialCount) X
  intro z
  simp only [Polynomial.eval_X,trialVectorMeasure,Function.comp_apply]
  omega

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalOuterVector
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma work_outerVectorInput : WorkBound outerVectorInputRealizer outerVectorMeasure := by
  have hi (z : OuterVectorInput) : weight z ≤ X.eval (outerVectorMeasure z) := by
    simp only [Polynomial.eval_X,outerVectorMeasure]
    omega
  have hv : WorkBound (composition (first (B := (List Bool×ℕ)×MatrixCode)) trialVectorRealizer)
      outerVectorMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_trialVector X
    intro z
    simp only [Polynomial.eval_X,outerVectorMeasure]
    omega
  have hp : PolynomialTime (composition
      (f := fun z : OuterVectorInput => (z.1.2,z.2.2)) (g := originalIndex)
      (pair (composition first second) (composition second second)) originalIndexRealizer) :=
    polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_originalIndex
  unfold outerVectorInputRealizer
  exact work_pair (work_of_polynomial (polynomial_composition polynomial_second polynomial_first) X hi)
    (work_pair hv (work_of_polynomial hp X hi) X hi) X hi

attribute [local irreducible] outerVectorInput

lemma work_outerVector : WorkBound outerVectorRealizer outerVectorMeasure := by
  unfold outerVectorRealizer
  exact work_then_polynomial work_outerVectorInput VectorRetryPrograms.polynomial_counts

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitMatrixEntry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Integer transition entries for the all-small walk -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma polynomial_wordViews : PolynomialTime wordViewsRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_sourceData) polynomial_second)
      polynomial_codeNeighborProposal)) FirstSuccessProgram.polynomial_default

lemma polynomial_wordCount : PolynomialTime wordCountRealizer := by
  unfold wordCountRealizer
  apply polynomial_congr
  exact polynomial_choose (polynomial_composition (polynomial_pair polynomial_wordViews
    (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second))
    polynomial_profileCodeEqual) (polynomial_constant 1) (polynomial_constant 0)

lemma polynomial_wordSum : PolynomialTime wordSumRealizer :=
  polynomial_composition (polynomial_mapWith polynomial_wordCount) polynomial_listSum

attribute [local irreducible] wordCount wordViews wordCountRealizer wordViewsRealizer

lemma work_entryWords : WorkBound entryWordsRealizer entryMeasure := by
  have hi (z : MatrixEntryInput) : weight z ≤ X.eval (entryMeasure z) := by
    simp only [Polynomial.eval_X,entryMeasure]
    omega
  have hw : WorkBound (composition (f := fun z : MatrixEntryInput => z.1.2)
      (g := booleanWords) (composition first second) booleanWordsRealizer) entryMeasure := by
    apply work_composition (work_of_polynomial
      (polynomial_composition polynomial_first polynomial_second) X hi) work_booleanWords X
    intro z
    have hh : weight z.1.2 ≤ weight z := (weight_snd z.1).trans (weight_fst z)
    simp only [Polynomial.eval_X,entryMeasure,Function.comp_apply]
    omega
  unfold entryWordsRealizer
  exact work_pair (work_of_polynomial polynomial_identity X hi) hw X hi

lemma work_validEntry : WorkBound validEntryRealizer entryMeasure := by
  obtain ⟨p,hp⟩ := work_entryWords
  obtain ⟨q,hq⟩ := polynomial_wordSum
  refine ⟨p+q.comp p,fun z => ?_⟩
  have h1 := hp z
  have h2 := hq (entryWords z)
  have h3 := polynomial_eval_monotone q ((Nat.le_add_left _ _).trans h1)
  dsimp only at h3
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  unfold validEntryRealizer validEntry
  change entryWordsRealizer.cost z+wordSumRealizer.cost (entryWords z)+
    weight (wordSum (entryWords z))≤_
  omega

lemma work_denominator : WorkBound denominatorRealizer (fun z => weight z) := by
  unfold denominatorRealizer
  apply work_composition (work_of_polynomial (polynomial_pair (polynomial_constant 2)
    (polynomial_composition polynomial_second polynomial_listLength)) X (fun _ => by simp))
    BinaryPowerPrograms.work_power (X+9)
  intro z
  change z.2.length+weight (2:ℕ) ≤ (X+9).eval (weight z)
  have htwo : weight (2:ℕ) ≤ 9 := by simpa using weight_nat_numeric 2
  have hl := (list_length_le_weight z.2).trans (weight_snd z)
  simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

lemma work_diagonalEntry : WorkBound diagonalEntryRealizer entryMeasure := by
  have hi (z : MatrixEntryInput) : weight z ≤ X.eval (entryMeasure z) := by
    simp only [Polynomial.eval_X,entryMeasure]
    omega
  have hd : WorkBound (composition (first (B := (List ℕ×List ℕ)×(List ℕ×List ℕ)))
      denominatorRealizer) entryMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_denominator X
    intro z
    simpa only [Polynomial.eval_X,Function.comp_apply] using (weight_fst z).trans (hi z)
  unfold diagonalEntryRealizer
  apply work_congr
  exact work_choose (work_of_polynomial (polynomial_composition polynomial_second
    polynomial_profileCodeEqual) X hi) hd (work_of_polynomial (polynomial_constant 0) X hi) X hi

lemma work_matrixEntry : WorkBound matrixEntryRealizer entryMeasure := by
  unfold matrixEntryRealizer
  exact work_choose (work_of_polynomial (polynomial_composition polynomial_sourceData
    polynomial_profileTest) X (fun z => by simp only [Polynomial.eval_X,entryMeasure]; omega))
    work_validEntry work_diagonalEntry X (fun z => by simp only [Polynomial.eval_X,entryMeasure]; omega)

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitMatrixProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Constructing the finite transition matrix by deterministic enumeration -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma polynomial_columnEntryInput : PolynomialTime columnEntryInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_second))

lemma work_columnEntry : WorkBound columnEntryRealizer columnEntryMeasure := by
  unfold columnEntryRealizer
  apply work_composition (work_of_polynomial polynomial_columnEntryInput X _) work_matrixEntry X
  · intro z
    simp only [columnEntryMeasure,Polynomial.eval_X]
    exact le_rfl
  · intro z
    have hz : weight z=weight (columnEntryInput z) := by
      rcases z with ⟨⟨p,t⟩,s⟩
      simp only [columnEntryInput,weight_prod]
      omega
    simp only [Polynomial.eval_X,columnEntryMeasure,entryMeasure]
    omega

lemma work_matrixColumn : WorkBound matrixColumnRealizer matrixColumnMeasure := by
  have hin (z : MatrixColumnInput) : weight z ≤ matrixColumnMeasure z := by
    have hw : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) := weight_fst (z,profileBoxViews (matrixData z.1))
    simp only [matrixColumnMeasure,MeasuredMap.listMeasure]
    omega
  have hd : PolynomialTime (composition (first (B := List ℕ×List ℕ)) matrixDataRealizer) :=
    polynomial_composition polynomial_first polynomial_matrixData
  have hv : WorkBound (composition (composition first matrixDataRealizer) profileBoxViewsRealizer)
      matrixColumnMeasure := by
    apply work_composition (work_of_polynomial hd X (fun z => by simpa using hin z))
      work_profileBoxViews (X+1)
    intro z
    have hw : weight (matrixData z.1) ≤ weight z := by
      unfold matrixData
      exact (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans
        ((weight_fst _).trans (weight_fst z))))
    simp only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      matrixColumnMeasure,MeasuredMap.listMeasure]
    have hpair : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) := weight_fst (z,profileBoxViews (matrixData z.1))
    omega
  unfold matrixColumnRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simpa using hin z)) hv X (fun z => by simpa using hin z))
    (MeasuredMap.work_mapWith _ _ work_columnEntry) X
  intro z
  simp only [Polynomial.eval_X,matrixColumnMeasure,Function.comp_apply,id_eq]
  omega

lemma work_profileMatrix : WorkBound profileMatrixRealizer profileMatrixMeasure := by
  have hin (z : MatrixParameters) : weight z ≤ profileMatrixMeasure z := by
    have hw : weight z ≤ weight (z,profileBoxViews (matrixData z)) := weight_fst (z,profileBoxViews (matrixData z))
    simp only [profileMatrixMeasure,MeasuredMap.listMeasure]
    omega
  have hv : WorkBound (composition matrixDataRealizer profileBoxViewsRealizer)
      profileMatrixMeasure := by
    apply work_composition (work_of_polynomial polynomial_matrixData X
      (fun z => by simpa using hin z)) work_profileBoxViews (X+1)
    intro z
    have hw : weight (matrixData z) ≤ weight z := by
      unfold matrixData
      exact (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans (weight_fst z)))
    simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      profileMatrixMeasure,MeasuredMap.listMeasure]
    have hpair : weight z ≤ weight (z,profileBoxViews (matrixData z)) := weight_fst (z,profileBoxViews (matrixData z))
    omega
  unfold profileMatrixRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simpa using hin z)) hv X (fun z => by simpa using hin z))
    (MeasuredMap.work_mapWith _ _ work_matrixColumn) X
  intro z
  simp only [Polynomial.eval_X,profileMatrixMeasure,Function.comp_apply,id_eq]
  omega

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTerminalProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Deterministic terminal weights for the all-small branch -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma polynomial_terminalData : PolynomialTime terminalDataRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_terminalSourceInput polynomial_sourceData)
    (polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
      polynomial_second)) (polynomial_constant [])

lemma polynomial_terminalEntry : PolynomialTime terminalEntryRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition polynomial_second polynomial_second)
    (polynomial_pair (polynomial_composition polynomial_terminalData polynomial_outerTrial)
      (polynomial_constant 1))) polynomial_successfulWeight

lemma work_terminalEntry : WorkBound terminalEntryRealizer terminalEntryMeasure :=
  work_of_polynomial polynomial_terminalEntry X (fun _ => by simp [terminalEntryMeasure])

lemma polynomial_terminalColumnEntryInput : PolynomialTime terminalColumnEntryInputRealizer :=
  polynomial_pair (polynomial_composition polynomial_first polynomial_first)
    (polynomial_pair polynomial_second (polynomial_composition polynomial_first polynomial_second))

lemma work_terminalColumnEntry : WorkBound terminalColumnEntryRealizer terminalColumnEntryMeasure := by
  unfold terminalColumnEntryRealizer
  apply work_composition (work_of_polynomial polynomial_terminalColumnEntryInput X
    (fun z => by simp only [Polynomial.eval_X,terminalColumnEntryMeasure]; omega))
    work_terminalEntry X
  intro z
  simp only [Polynomial.eval_X,terminalColumnEntryMeasure]
  omega

lemma work_terminalColumn : WorkBound terminalColumnRealizer terminalColumnMeasure := by
  have hin (z : TerminalColumnInput) : weight z ≤ terminalColumnMeasure z := by
    have hw : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) :=
      weight_fst (z,profileBoxViews (matrixData z.1))
    simp only [terminalColumnMeasure,MeasuredMap.listMeasure]
    omega
  have hd : PolynomialTime (composition (first (B := MatrixCode)) matrixDataRealizer) :=
    polynomial_composition polynomial_first polynomial_matrixData
  have hv : WorkBound (composition (composition first matrixDataRealizer) profileBoxViewsRealizer)
      terminalColumnMeasure := by
    apply work_composition (work_of_polynomial hd X (fun z => by simpa using hin z))
      work_profileBoxViews (X+1)
    intro z
    have hw : weight (matrixData z.1) ≤ weight z := by
      unfold matrixData
      exact (weight_fst _).trans ((weight_fst _).trans ((weight_fst _).trans
        ((weight_fst _).trans (weight_fst z))))
    simp only [Function.comp_apply,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
      terminalColumnMeasure,MeasuredMap.listMeasure]
    have hpair : weight z ≤ weight (z,profileBoxViews (matrixData z.1)) :=
      weight_fst (z,profileBoxViews (matrixData z.1))
    omega
  unfold terminalColumnRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_identity X
    (fun z => by simpa using hin z)) hv X (fun z => by simpa using hin z))
    (MeasuredMap.work_mapWith _ _ work_terminalColumnEntry) X
  intro z
  simp only [Polynomial.eval_X,terminalColumnMeasure,Function.comp_apply,id_eq]
  omega

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitTrialCountProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executed walk-and-terminal integer trial counts -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma work_walkCountData : WorkBound walkCountDataRealizer walkCountMeasure := by
  have hi (z : WalkCountInput) : weight z ≤ X.eval (walkCountMeasure z) := by
    simp only [Polynomial.eval_X,walkCountMeasure]
    omega
  have hm : WorkBound (composition (first (B := ℕ×ℕ)) profileMatrixRealizer) walkCountMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_profileMatrix X
    intro z
    simp only [Polynomial.eval_X,walkCountMeasure]
    omega
  unfold walkCountDataRealizer
  exact work_pair (work_of_polynomial (polynomial_composition polynomial_second polynomial_first) X hi)
    (work_pair hm (work_of_polynomial
      (polynomial_composition polynomial_second polynomial_second) X hi) X hi) X hi

lemma work_walkCounts : WorkBound walkCountsRealizer walkCountMeasure := by
  obtain ⟨p,hp⟩ := work_walkCountData
  unfold walkCountsRealizer
  apply work_composition ⟨p,hp⟩ IntegerMatrixPrograms.work_fromPoint (X+p)
  intro z
  have hw := hp z
  have hs : weight (profileMatrix z.1,z.2.2) ≤ weight (walkCountData z) := by
    exact weight_snd (walkCountData z)
  have hn : z.2.1 ≤ walkCountMeasure z := by unfold walkCountMeasure; omega
  simp only [Polynomial.eval_add,Polynomial.eval_X]
  change z.2.1+weight (profileMatrix z.1,z.2.2) ≤ _
  omega

lemma work_trialCount : WorkBound trialCountRealizer trialCountMeasure := by
  have hi (z : TrialCountInput) : weight z ≤ X.eval (trialCountMeasure z) := by
    simp only [Polynomial.eval_X,trialCountMeasure]
    omega
  have hw : WorkBound (composition (first (B := MatrixCode)) walkCountsRealizer) trialCountMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_walkCounts X
    intro z
    simp only [Polynomial.eval_X,trialCountMeasure]
    omega
  have ht : WorkBound (composition (pair (composition first first) second)
      terminalColumnRealizer) trialCountMeasure := by
    apply work_composition (work_of_polynomial (polynomial_pair
      (polynomial_composition polynomial_first polynomial_first) polynomial_second) X hi)
      work_terminalColumn X
    intro z
    simp only [Polynomial.eval_X,trialCountMeasure,Function.comp_apply]
    omega
  unfold trialCountRealizer
  exact work_then_polynomial (work_pair hw ht X hi) IntegerMatrixPrograms.polynomial_dot

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOriginalVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing trial counts on every original-table candidate -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma polynomial_optionalTrialInput : PolynomialTime optionalTrialInputRealizer :=
  polynomial_pair polynomial_first (polynomial_composition
    (polynomial_pair (polynomial_constant []) polynomial_second) FirstSuccessProgram.polynomial_default)

lemma work_optionalTrialCount : WorkBound optionalTrialCountRealizer optionalTrialMeasure := by
  have hi (z : OptionalTrialInput) : weight z ≤ X.eval (optionalTrialMeasure z) := by
    simp only [Polynomial.eval_X,optionalTrialMeasure]
    omega
  have ht : WorkBound (composition optionalTrialInputRealizer trialCountRealizer)
      optionalTrialMeasure := by
    apply work_composition (work_of_polynomial polynomial_optionalTrialInput X hi) work_trialCount X
    intro z
    simp only [Polynomial.eval_X,optionalTrialMeasure]
    omega
  unfold optionalTrialCountRealizer
  exact work_choose (work_of_polynomial (polynomial_composition polynomial_second
    FirstSuccessProgram.polynomial_isSome) X hi) ht
    (work_of_polynomial (polynomial_constant 0) X hi) X hi

lemma work_trialVector : WorkBound trialVectorRealizer trialVectorMeasure := by
  have hi (z : TrialVectorInput) : weight z ≤ X.eval (trialVectorMeasure z) := by
    simp only [Polynomial.eval_X,trialVectorMeasure]
    omega
  have he : WorkBound (composition (second (A := WalkCountInput)) originalCandidatesRealizer)
      trialVectorMeasure := by
    apply work_composition (work_of_polynomial polynomial_second X hi) work_originalCandidates X
    intro z
    simp only [Polynomial.eval_X,trialVectorMeasure]
    omega
  unfold trialVectorRealizer
  apply work_composition (work_pair (work_of_polynomial polynomial_first X hi) he X hi)
    (MeasuredMap.work_mapWith _ _ work_optionalTrialCount) X
  intro z
  simp only [Polynomial.eval_X,trialVectorMeasure,Function.comp_apply]
  omega

end ContingencyTables.UnitCountPrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_UnitOuterVector
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computed first-success counts over the original-table box -/

namespace ContingencyTables.UnitCountPrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms ProfilePrograms Polynomial

lemma work_outerVectorInput : WorkBound outerVectorInputRealizer outerVectorMeasure := by
  have hi (z : OuterVectorInput) : weight z ≤ X.eval (outerVectorMeasure z) := by
    simp only [Polynomial.eval_X,outerVectorMeasure]
    omega
  have hv : WorkBound (composition (first (B := (List Bool×ℕ)×MatrixCode)) trialVectorRealizer)
      outerVectorMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_trialVector X
    intro z
    simp only [Polynomial.eval_X,outerVectorMeasure]
    omega
  have hp : PolynomialTime (composition
      (f := fun z : OuterVectorInput => (z.1.2,z.2.2)) (g := originalIndex)
      (pair (composition first second) (composition second second)) originalIndexRealizer) :=
    polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_second)
    (polynomial_composition polynomial_second polynomial_second)) polynomial_originalIndex
  unfold outerVectorInputRealizer
  exact work_pair (work_of_polynomial (polynomial_composition polynomial_second polynomial_first) X hi)
    (work_pair hv (work_of_polynomial hp X hi) X hi) X hi

attribute [local irreducible] outerVectorInput

lemma work_outerVector : WorkBound outerVectorRealizer outerVectorMeasure := by
  unfold outerVectorRealizer
  exact work_then_polynomial work_outerVectorInput VectorRetryPrograms.polynomial_counts

end ContingencyTables.UnitCountPrograms

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

lemma work_scheduledCounts : WorkBound scheduledCountsRealizer scheduledCountsMeasure := by
  have hi (z : SamplingParameters) : scheduledCountInputMeasure z ≤ X.eval (scheduledCountsMeasure z) := by
    simp only [eval_X,scheduledCountsMeasure]
    omega
  have hb := work_remeasure work_scheduledOuterInput X hi
  have hw (z : SamplingParameters) : weight z ≤ X.eval (scheduledCountsMeasure z) :=
    (weight_le_scheduledCountInputMeasure z).trans (by simpa only [eval_X] using hi z)
  unfold scheduledCountsRealizer scheduledCounts
  apply work_choose (work_of_polynomial polynomial_hasLargeRectangle X hw)
  · apply work_composition hb work_outerVector X
    intro z
    simp only [eval_X,scheduledCountsMeasure]
    omega
  · apply work_composition hb UnitCountPrograms.work_outerVector X
    intro z
    simp only [eval_X,scheduledCountsMeasure]
    omega
  · exact hw

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalTableCardinality
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the number of feasible original-table box entries -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms

lemma polynomial_originalCardEntry : PolynomialTime originalCardEntryRealizer :=
  polynomial_choose FirstSuccessProgram.polynomial_isSome (polynomial_constant 1) (polynomial_constant 0)

lemma work_originalCardinality : WorkBound originalCardinalityRealizer originalEnumerationMeasure := by
  unfold originalCardinalityRealizer
  exact work_then_polynomial work_originalCandidates
    (polynomial_composition (polynomial_map polynomial_originalCardEntry) polynomial_listSum)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_OriginalResidualVector
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Explicit integer correction weights on the original-table box -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

lemma polynomial_residualVectorEntry : PolynomialTime residualVectorEntryRealizer := by
  unfold residualVectorEntryRealizer
  exact polynomial_choose
    (polynomial_composition (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
      polynomial_second) (polynomial_getDFast none)) FirstSuccessProgram.polynomial_isSome)
    (polynomial_composition (polynomial_pair
      (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_first)
      (polynomial_pair
        (polynomial_composition (polynomial_composition polynomial_first polynomial_second) polynomial_second)
        (polynomial_composition (polynomial_pair
          (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_second)
          polynomial_second) (polynomial_getDFast 0)))) ResidualWeightPrograms.polynomial_count)
    (polynomial_constant 0)

lemma polynomial_residualVectorIndices : PolynomialTime residualVectorIndicesRealizer := by
  apply polynomial_boundedRange (polynomial_composition (polynomial_composition
    polynomial_first polynomial_first) polynomial_listLength) X
  intro z
  simpa only [Function.comp_apply,Polynomial.eval_X] using
    (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma polynomial_residualVector : PolynomialTime residualVectorRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_residualVectorIndices)
    (polynomial_mapWith polynomial_residualVectorEntry)

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Machines_ScheduledResidualProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Executing residual weights from margins, precision, and branch denominator -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] scheduledCounts residualVector originalCandidates originalCardinality

lemma work_scheduledResidualCache :
    WorkBound scheduledResidualCacheRealizer scheduledResidualMeasure := by
  have hi (z : SamplingParameters×ℕ) : weight z ≤ X.eval (scheduledResidualMeasure z) := by
    simp only [eval_X,scheduledResidualMeasure]
    omega
  have hc : WorkBound (composition (first (B := ℕ)) scheduledCountsRealizer)
      scheduledResidualMeasure := by
    apply work_composition (work_of_polynomial polynomial_first X hi) work_scheduledCounts X
    intro z
    simp only [eval_X,scheduledResidualMeasure]
    omega
  exact work_pair hc (work_of_polynomial (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) polynomial_second) X hi) X hi

lemma work_cachedResidualInput : WorkBound cachedResidualInputRealizer cachedResidualMeasure := by
  have hi (z : ScheduledResidualCache) : weight z ≤ X.eval (cachedResidualMeasure z) := by
    simp only [eval_X,cachedResidualMeasure]
    omega
  have he : WorkBound (composition (composition (second (A := List ℕ)) first)
      originalCandidatesRealizer) cachedResidualMeasure := by
    apply work_composition (work_of_polynomial (polynomial_composition polynomial_second polynomial_first)
      X hi) work_originalCandidates X
    intro z
    simp only [eval_X,cachedResidualMeasure,Function.comp_apply]
    omega
  have hn : WorkBound (composition (composition (second (A := List ℕ)) first)
      originalCardinalityRealizer) cachedResidualMeasure := by
    apply work_composition (work_of_polynomial (polynomial_composition polynomial_second polynomial_first)
      X hi) work_originalCardinality X
    intro z
    simp only [eval_X,cachedResidualMeasure,Function.comp_apply]
    omega
  exact work_pair (work_pair he (work_of_polynomial polynomial_first X hi) X hi)
    (work_pair (work_of_polynomial (polynomial_pair
      (polynomial_composition polynomial_first polynomial_listSum)
      (polynomial_composition polynomial_second polynomial_second)) X hi) hn X hi) X hi

lemma work_cachedResidualCounts : WorkBound cachedResidualCountsRealizer cachedResidualMeasure :=
  work_then_polynomial work_cachedResidualInput polynomial_residualVector

attribute [local irreducible] scheduledResidualCache cachedResidualCounts

lemma work_scheduledResidualCounts :
    WorkBound scheduledResidualCountsRealizer scheduledResidualMeasure := by
  unfold scheduledResidualCountsRealizer scheduledResidualCounts
  obtain ⟨p,hp⟩ := work_scheduledResidualCache
  apply work_composition ⟨p,hp⟩ work_cachedResidualCounts (X+p)
  intro z
  have hw := hp z
  simp only [scheduledResidualCache] at hw
  simp only [eval_add,eval_X,cachedResidualMeasure,scheduledResidualCache]
  have hm : originalEnumerationMeasure z.1.1 ≤ scheduledResidualMeasure z := by
    unfold scheduledResidualMeasure
    omega
  omega

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

end ContingencyTables.ProfilePrograms

end OAI
end

section
-- module Solutions.OAIQ089_CT.ContingencyTables_Sampling_ExactResidualInput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Computing the complete input to the exact matrix rejection loop -/

namespace ContingencyTables.ProfilePrograms
open MatchingFPRAS MatchingFPRAS.TreeTyped DensePrograms Polynomial

attribute [local irreducible] exactResidualInput scheduledResidualCounts originalCandidates

lemma work_exactRareWeights : WorkBound exactRareWeightsRealizer exactRareMeasure := by
  unfold exactRareWeightsRealizer
  have hp : WorkBound exactResidualInputRealizer exactRareMeasure :=
    work_remeasure work_exactResidualInput X (by
      intro z
      simp only [eval_X,exactRareMeasure]
      omega)
  apply work_composition hp work_scheduledResidualCounts X
  intro z
  simp only [eval_X,exactRareMeasure]
  omega

attribute [local irreducible] exactRareWeights

lemma work_exactMatrixInput_oai : WorkBound exactMatrixInputRealizer exactRareMeasure := by
  have hi (z : CompletionMargins) : weight z ≤ X.eval (exactRareMeasure z) := by
    simp only [eval_X,exactRareMeasure]
    omega
  have he : WorkBound originalCandidatesRealizer exactRareMeasure :=
    work_remeasure work_originalCandidates X (by
      intro z
      simp only [eval_X,exactRareMeasure]
      omega)
  exact work_pair (work_pair he (work_of_polynomial GreedyFeasibleTable.polynomial_table X hi) X hi)
    work_exactRareWeights X hi

end ContingencyTables.ProfilePrograms

end OAI
end

theorem solution : type_of% @OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput_oai := @OAI.ContingencyTables.ProfilePrograms.work_exactMatrixInput_oai
