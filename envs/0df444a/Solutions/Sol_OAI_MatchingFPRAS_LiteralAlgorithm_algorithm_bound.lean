-- Prove2me | solution 1 for OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:22:29.622999+00:00
-- url     : https://prove2.me/submissions/1ee16027-8105-4433-a5c5-fa2d06489098

import Mathlib
import Definitions.Def_MatchingFPRAS
import Definitions.Def_OAIQ051M004
import Theorems.Thm_OAI_MatchingFPRAS_OnlineGuard_trial_bound
import Theorems.Thm_OAI_MatchingFPRAS_OnlineInitial_work_initializeInput

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_EndpointPair
attribute [-instance] _root_.OAI.MatchingFPRAS.Transport.Sparse.decideMatching _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

variable {inc : E → V → Prop}

omit [DecidableEq V] [Fintype E] [DecidableEq E] in
lemma PM.card_le_vertices (hinc : ∀ e, ∃ v, inc e v) (A : PM inc) : A.val.card ≤ Fintype.card V := by
  classical
  let vertex : ↥A.val → V := fun e => Classical.choose (hinc e.val)
  have hv (e : ↥A.val) : inc e.val (vertex e) := Classical.choose_spec (hinc e.val)
  have hinj : Function.Injective vertex := by
    intro e f h
    apply Subtype.ext
    exact A.property.unique (Finset.mem_univ (vertex e)) e.property (hv e) f.property (h ▸ hv f)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective vertex hinj

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_Incident
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Representation

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.Enlargement
open Finset

variable {V : Type*} [Fintype V] [LinearOrder V]

variable (R : Finset V) (s : LogicalEdge V → Bool)
    (hs : LogicalHoles source target R ∅ s)

variable {R s hs}

lemma selection_weight (w : V → V → ℝ) (m : Mate V) :
    (∏ e : LogicalEdge V, if select m e then logicalActivity w e else 1)=weight w m := by
  classical
  unfold weight
  rw [← Finset.prod_filter,← Finset.prod_filter]
  apply Finset.prod_bij (fun e _ => source e)
  · intro e he
    have hh := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hh]
    exact e.property
  · intro e he f hf h
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    have hf' := (select_eq_true m f).mp (Finset.mem_filter.mp hf).2
    exact Subtype.ext (Prod.ext h (he'.symm.trans ((congrArg m.val h).trans hf')))
  · intro x hx
    have hx' := (Finset.mem_filter.mp hx).2
    refine ⟨⟨(x,m.val x),hx'⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [select,source,target]⟩
  · intro e he
    have he' := (select_eq_true m e).mp (Finset.mem_filter.mp he).2
    simp only [logicalActivity,edgeActivity,show source e < target e from e.property,ite_true,he']

lemma asMate_weight (w : V → V → ℝ) :
    (∏ e : LogicalEdge V, if s e then logicalActivity w e else 1)=weight w (asMate R s hs) := by
  rw [← selection_weight,select_asMate]

theorem logical_partition_eq (w : V → V → ℝ) (R : Finset V) :
    logicalHolePartition source target R ∅ (logicalActivity w)=partition w R := by
  classical
  let := Fintype.ofFinite {s : LogicalEdge V → Bool // LogicalHoles source target R ∅ s}
  let := Fintype.ofFinite {m : Mate V // HasHoles m R}
  unfold logicalHolePartition partition
  rw [Finset.sum_subtype (matchings R) (fun m => mem_matchings m R)]
  apply Fintype.sum_equiv (matchingEquiv R)
  intro s
  exact asMate_weight w

end MatchingFPRAS.Representation

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Certify
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting

lemma sigma_nonneg (D K : ℕ) (epsilon : ℚ) (he : 0 ≤ epsilon) : 0  ≤  sigma D K epsilon := by
  unfold sigma alpha; positivity

end MatchingFPRAS.Counting

end OAI
end

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

lemma less_val (x y : Fraction) (hx : 0<x.2) (hy : 0<y.2) :
    less (x,y)=decide (val x<val y) := by
  unfold less
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  rw [val,val,div_lt_div_iff₀ (by exact_mod_cast hx) (by exact_mod_cast hy)]
  norm_cast

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
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.TreeFraction
open TreeTyped

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
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_ExperimentSupport
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
lemma all_map (p : Experiment α) (f : α → β) (P : β → Prop) :
    All (p.map f) P ↔ All p (fun a=>P (f a)) := by
  rw [map,all_bind]; rfl

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
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_LabelOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport

open Finset MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]

variable {bags : V → Finset J}



open Finset Replica Replica.Ladder Variation

noncomputable local instance instDecidableEqPMBagEdgeIncident_5_rec8920_1 : DecidableEq (PM (BagEdge.Incident (bags := bags))) := Classical.decEq _
lemma endpoint_reaches (N D K : ℕ) (hN : 0<N) :
    max (D:ℝ) (3*4^K)≤(1+((N:ℝ)^2)⁻¹)^(endpoint N D K hN) := by
  rw [endpoint_eq]; exact ladderTier_spec N D K hN

end MatchingFPRAS.Transport

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_CompleteGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

lemma mem_perfectMatchings (G : GraphInput) (M) : M ∈ perfectMatchings G ↔ Perfect G M := by
  classical
  simp only [perfectMatchings, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1,h⟩⟩

end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RatWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace MatchingFPRAS.RealStage

open Finset



open Finset

variable {n : ℕ}

lemma ScaleInvariant.pos {G : Fin n → Fin n → ℝ} {v : Fin n → ℝ}
    (hv : ScaleInvariant G v) (i) : 0 < v i := lt_of_lt_of_le (by norm_num [alpha]) (hv.lower i)

lemma rowMaximum_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) : rowMaximum hn G v i ≤ v i := by
  apply Finset.sup'_le
  intro j hj
  exact (div_le_iff₀ (hv.pos j)).mpr (hv.feasible i j (mem_erase.mp hj).1.symm)

lemma ratio_le_rowMaximum (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (i j) (hji : j≠i) : G i j/v j ≤ rowMaximum hn G v i :=
  Finset.le_sup' (fun j => G i j/v j) (mem_erase.mpr ⟨hji,mem_univ _⟩)

lemma rowMaximum_lower (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hG : ∀ i j, i≠j → alpha ≤ G i j) (hv : ScaleInvariant G v) (i) :
    alpha/2 ≤ rowMaximum hn G v i := by
  obtain ⟨j,hj⟩ := others_nonempty hn i
  have hji := (mem_erase.mp hj).1
  apply le_trans _ (ratio_le_rowMaximum hn G v i j hji)
  apply (le_div_iff₀ (hv.pos j)).mpr
  have hGi := hG i j hji.symm
  have hvi := hv.upper j
  norm_num [alpha] at *
  linarith

lemma scaleUpdate_le (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i j) : scaleUpdate hn G v i j ≤ v j := by
  by_cases hji : j=i
  · subst j; simpa [scaleUpdate] using rowMaximum_le hn G v hv i
  · simp [scaleUpdate,Function.update_of_ne hji]

lemma scaleUpdate_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j)
    (hv : ScaleInvariant G v) (i) : ScaleInvariant G (scaleUpdate hn G v i) := by
  constructor
  · intro j
    by_cases hji : j=i
    · subst j; simpa [scaleUpdate] using rowMaximum_lower hn G v hG hv i
    · simpa [scaleUpdate,Function.update_of_ne hji] using hv.lower j
  · intro j; exact (scaleUpdate_le hn G v hv i j).trans (hv.upper j)
  · intro a b hab
    by_cases hai : a=i
    · subst a
      have hb := (div_le_iff₀ (hv.pos b)).mp (ratio_le_rowMaximum hn G v i b hab.symm)
      simpa [scaleUpdate,Function.update_of_ne hab.symm] using hb
    · by_cases hbi : b=i
      · subst b
        have ha := (div_le_iff₀ (hv.pos a)).mp (ratio_le_rowMaximum hn G v i a hai)
        simpa [scaleUpdate,Function.update_of_ne hai,hsym i a,mul_comm] using ha
      · simpa [scaleUpdate,Function.update_of_ne hai,Function.update_of_ne hbi] using hv.feasible a b hab

lemma scaleUpdate_tight (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ) (v : Fin n → ℝ)
    (hv : ScaleInvariant G v) (i) :
    ∃ j, j≠i ∧ scaleUpdate hn G v i i*scaleUpdate hn G v i j=G i j := by
  obtain ⟨j,hj,heq⟩ := Finset.exists_mem_eq_sup' (others_nonempty hn i) (fun j => G i j/v j)
  have hji := (mem_erase.mp hj).1
  refine ⟨j,hji,?_⟩
  change rowMaximum hn G v i = G i j/v j at heq
  simp only [scaleUpdate,Function.update_self,Function.update_of_ne hji]
  rw [heq]
  exact div_mul_cancel₀ _ (hv.pos j).ne'

lemma tight_persists (G : Fin n → Fin n → ℝ) (v v' : Fin n → ℝ)
    (hv : ScaleInvariant G v) (hv' : ScaleInvariant G v') (hdown : ∀ i, v' i ≤ v i)
    (i j) (hji : j≠i) (hij : v i*v j=G i j) : v' i*v' j=G i j := by
  apply le_antisymm
  · calc
      _ ≤ v i*v j := mul_le_mul (hdown i) (hdown j) (hv'.pos j).le (hv.pos i).le
      _ = _ := hij
  · exact hv'.feasible i j hji.symm

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_RowPeak
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace MatchingFPRAS.RealStage

open Finset

variable {n : ℕ}

lemma scalingTrace_invariant (hn : 2 ≤ n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, G i j=G j i) (hG : ∀ i j, i≠j → alpha ≤ G i j ∧ G i j ≤ 3)
    (k : ℕ) : ScaleInvariant G (scalingTrace hn G k) ∧
      ∀ i, i.val<k → ∃ j, j≠i ∧ scalingTrace hn G k i*scalingTrace hn G k j=G i j := by
  induction k with
  | zero =>
    constructor
    · constructor
      · intro i; norm_num [scalingTrace,alpha]
      · intro i; simp [scalingTrace]
      · intro i j h; have := (hG i j h).2; simp only [scalingTrace]; linarith
    · intro i hi; omega
  | succ k ih =>
    by_cases hk : k<n
    · let i : Fin n := ⟨k,hk⟩
      have hinv := scaleUpdate_invariant hn G (scalingTrace hn G k) hsym (fun i j h => (hG i j h).1) ih.1 i
      have htrace : scalingTrace hn G (k+1)=scaleUpdate hn G (scalingTrace hn G k) i := by
        simp [scalingTrace,hk,i]
      rw [htrace]
      refine ⟨hinv,?_⟩
      intro a ha
      by_cases hak : a.val<k
      · obtain ⟨j,hj,he⟩ := ih.2 a hak
        refine ⟨j,hj,?_⟩
        exact tight_persists G _ _ ih.1 hinv (scaleUpdate_le hn G _ ih.1 i) a j hj he
      · have hai : a=i := Fin.ext (by dsimp [i]; omega)
        subst a
        exact scaleUpdate_tight hn G _ ih.1 i
    · have htrace : scalingTrace hn G (k+1)=scalingTrace hn G k := by simp [scalingTrace,hk]
      rw [htrace]
      refine ⟨ih.1,?_⟩
      intro i _
      exact ih.2 i (by have := i.isLt; omega)



open Finset

end MatchingFPRAS.RealStage

end

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_FinitePMF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Enlargement

open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport MatchingFPRAS.StageAnalysis Finset
open scoped Classical

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]

variable {n K T S : ℕ} [Nontrivial (Fin n)]

attribute [local instance] OAI.MatchingFPRAS.Enlargement.instDecidableEqSourceLabel_8
lemma StageData.sigma_pos (c : StageData n K T) : 0 < RealStage.sigma (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold RealStage.sigma RealStage.alpha
  have hD : 0 < sourceD (V:=Fin n) K := sourceD_one K
  have ht : 0 < T := c.stages
  have he := c.epsilon_positive
  exact lt_min (by positivity) (by positivity)

lemma StageData.sampleCount_pos (c : StageData n K T) :
    0 < stageSampleCount n (sourceD (V:=Fin n) K) T c.epsilon := by
  unfold stageSampleCount
  apply Nat.ceil_pos.mpr
  have hs := c.sigma_pos
  positivity



open MatchingFPRAS.Switching MatchingFPRAS.Subdivision MatchingFPRAS.RealGeometry
open MatchingFPRAS.Hierarchy MatchingFPRAS.Transport Finset
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder
open scoped Classical

end MatchingFPRAS.Enlargement

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.GraphBridge

open Finset MatchingFPRAS.Enlargement MatchingFPRAS.Subdivision MatchingFPRAS.Representation MatchingFPRAS.Switching

variable {n : ℕ}

lemma selected_prod {A : Type*} [CommMonoid A] (s : LogicalEdge (Fin n) → Bool)
    (w : Fin n × Fin n → A) :
    (∏ e ∈ selectedEdges s,w e)=∏ e : LogicalEdge (Fin n),if s e then w e.val else 1 := by
  rw [selectedEdges,prod_map]
  exact prod_filter (fun e => s e=true) (fun e => w e.val)

theorem weighted_partition (w : Fin n → Fin n → ℝ) :
    (∑ M ∈ perfectMatchings (completeGraph n),∏ e ∈ M,w e.1 e.2)=partition w ∅ := by
  classical
  rw [←logical_partition_eq w ∅]
  let := Fintype.ofFinite {s : LogicalEdge (Fin n) → Bool // LogicalHoles source target ∅ ∅ s}
  let := Fintype.ofFinite {M : Finset (Fin n × Fin n) // Perfect (completeGraph n) M}
  rw [Finset.sum_subtype (perfectMatchings (completeGraph n)) (mem_perfectMatchings _)]
  unfold logicalHolePartition
  symm
  apply Fintype.sum_equiv perfectEquiv
  intro s
  rw [show (perfectEquiv s).val=selectedEdges s.val from rfl,selected_prod]
  apply prod_congr rfl
  intro e _
  simp [logicalActivity,edgeActivity,source,target,e.property]

theorem complete_count :
    Z (completeGraph n)=UnitRefresh.pairingCount n := by
  have h := weighted_partition (n:=n) (fun _ _ => 1)
  simp only [prod_const_one,sum_const,nsmul_eq_mul,mul_one] at h
  rw [Initializer.uniform_partition,card_empty,Nat.sub_zero,one_pow,mul_one,Fintype.card_fin] at h
  exact_mod_cast h

end MatchingFPRAS.GraphBridge

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Probability_AdaptiveLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh

lemma pairingCount_le_half_power (n : ℕ) : pairingCount n ≤ n^(n/2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih ih' =>
    rw [pairingCount_add_two,show (n+2)/2=n/2+1 by omega,pow_succ]
    calc
      (n+1)*pairingCount n ≤ (n+2)*((n+2)^(n/2)) :=
        Nat.mul_le_mul (by omega) (ih.trans (Nat.pow_le_pow_left (by omega) (n/2)))
      _ = (n+2)^(n/2)*(n+2) := Nat.mul_comm _ _

end MatchingFPRAS.UnitRefresh

namespace MatchingFPRAS.Trial

open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis
open MatchingFPRAS.Replica MatchingFPRAS.Replica.Ladder MatchingFPRAS.Adaptive
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]

noncomputable local instance instDecidableEqSourceLabelFinN_1_rec8920_1 (w : Fin G.n → Fin G.n → ℝ) (K : ℕ) : DecidableEq (SourceLabel w K) := Classical.decEq _
lemma Parameters.S_pos (p : Parameters G) : 0<p.S := p.initialData.sampleCount_pos

attribute [instance] Layer.finite

end MatchingFPRAS.Trial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_MarkBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_1
noncomputable local instance instDecidableEqBagPMSourceVertexLabelBags_3_rec8920_1 (w : V → V → ℚ) (K : ℕ) :
    DecidableEq (BagPM (bags w K)) := Classical.decEq _
lemma sourceEdgeEquiv_central (w : V → V → ℚ) (K : ℕ) (q : LogicalEdge V) :
    sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K q)=centralEdge w K q :=
  sourceEdgeEquiv_real w K _
end MatchingFPRAS.RationalSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalObservables
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Transport
open Finset

variable {V E F I : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F] [Fintype I]
variable {inc : E → V → Prop} {j : F → V → Prop}
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma markedEquiv_probe (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v)
    (a : Marking.Marked (I:=Fin 3) inc) (u : E) :
    ({e u}⊆(markedEquiv e he a).1.val ∧
      (markedEquiv e he a).2=(fun x=>if x.val∈({e u}:Finset _) then 2 else 0)) ↔
    ({u}⊆a.1.val ∧ a.2=(fun x=>if x.val∈({u}:Finset _) then 2 else 0)) := by
  rw [markedEquiv_marks_eq e he a (fun x=>if x∈({e u}:Finset F) then 2 else 0)]
  rw [singleton_subset_iff,singleton_subset_iff]
  change (e u∈a.1.val.image e ∧ _) ↔ (u∈a.1.val ∧ _)
  simp only [mem_singleton,e.injective.eq_iff,
    mem_image,exists_eq_right]
omit [DecidableEq V] [Fintype E] [Fintype F] in
lemma pmEquiv_product_erase {R : Type*} [CommMonoid R]
    (e : E ≃ F) (he : ∀ a v,j (e a) v ↔ inc a v) (M : PM inc) (u : E) (f : F → R) :
    (∏ x ∈ (pmEquiv e he M).val \ {e u},f x)=∏ x ∈ M.val \ {u},f (e x) := by
  have hh : (pmEquiv e he M).val \ {e u}=(M.val \ {u}).image e := by
    change M.val.image e \ {e u}=(M.val \ {u}).image e
    ext x
    simp only [mem_sdiff,mem_image,mem_singleton]
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hu⟩
      exact ⟨y,⟨hy,fun h=>hu (congrArg e h)⟩,rfl⟩
    · rintro ⟨y,⟨hy,hu⟩,rfl⟩
      exact ⟨⟨y,hy,rfl⟩,fun h=>hu (e.injective h)⟩
  rw [hh]
  exact prod_image (fun _ _ _ _ h=>e.injective h)
end MatchingFPRAS.Transport
namespace MatchingFPRAS.RationalSource
open Finset Transport Variation Enlargement

variable {V : Type*} [Fintype V] [LinearOrder V] [Nontrivial V]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
attribute [local instance] OAI.MatchingFPRAS.RationalSource.instDecidableEqSourceLabelCastReal_3
lemma observableProbe_cast (w w₁ : V → V → ℚ) (K : ℕ) (u : LogicalEdge V)
    (a : SourceMarked (fun x y=>(w x y:ℝ)) K) :
    (observableProbe w w₁ K u (sourceMarkedEquiv w K a):ℝ)=
      Enlargement.observableProbe (fun x y=>(w x y:ℝ)) (fun x y=>(w₁ x y:ℝ)) K u a := by
  have hh:=markedEquiv_probe (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a
    (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)
  rw [sourceEdgeEquiv_central] at hh
  change ({centralEdge w K u}⊆(sourceMarkedEquiv w K a).1.val ∧
    (sourceMarkedEquiv w K a).2=(fun e=>if e.val∈({centralEdge w K u}:Finset _) then 2 else 0)) ↔ _ at hh
  simp only [observableProbe,Enlargement.observableProbe,hh]
  simp only [mem_singleton] at hh ⊢
  split_ifs <;> try contradiction
  · push_cast
    rw [←sourceEdgeEquiv_central w K u]
    change (∏ e ∈ (pmEquiv (inc:=BagEdge.Incident (bags:=sourceBags (fun x y=>(w x y:ℝ)) K))
    (j:=BagEdge.Incident (bags:=bags w K)) (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K) a.1).val \
      {sourceEdgeEquiv w K (Enlargement.centralEdge (fun x y=>(w x y:ℝ)) K u)},
      (bagReweight w w₁ K e:ℝ))=_
    rw [pmEquiv_product_erase (sourceEdgeEquiv w K) (sourceEdgeEquiv_incidence w K)]
    refine prod_congr (by ext; simp) ?_
    intro e _
    exact bagReweight_cast w w₁ K e
  · norm_cast
end MatchingFPRAS.RationalSource

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

lemma listMin_le {as : List ℕ} {d a : ℕ} (ha : a∈as) : listMin (as,d)≤a := by
  induction as generalizing d with
  | nil => simp at ha
  | cons b bs ih =>
    simp only [List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact (listMin_le_default bs (min d a)).trans (min_le_right _ _)
    · exact ih ha

lemma le_listMin {as : List ℕ} {d a : ℕ} (hd : a≤d) (ha : ∀ b∈as,a≤b) :
    a≤listMin (as,d) := by
  induction as generalizing d with
  | nil => exact hd
  | cons b bs ih =>
    apply ih (le_min hd (ha b (by simp)))
    intro c hc; exact ha c (by simp [hc])
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

lemma mul_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    mul (repr x,repr y)=repr (x*y) := by
  have h:=mul_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold mul at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma div_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    div (repr x,repr y)=repr (x/y) := by
  have h:=div_val (repr x) (repr y)
  rw [val_repr hx,val_repr hy] at h
  unfold div at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
end MatchingFPRAS.TreeFraction

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

variable {n m : ℕ}
lemma logicalRepr_injective : Function.Injective (logicalRepr (n:=n)) := by
  intro a b h
  apply Subtype.ext
  exact Prod.ext (Fin.ext (congrArg Prod.fst h)) (Fin.ext (congrArg Prod.snd h))
lemma vertexRepr_injective : Function.Injective (vertexRepr (n:=n) (m:=m)) := by
  intro a b h
  cases a with
  | inl a => cases b with
    | inl b => exact congrArg Sum.inl (Fin.ext (Sum.inl.inj h))
    | inr b => cases h
  | inr a => cases b with
    | inl b => cases h
    | inr b =>
      have h':(logicalRepr a.1,a.2.val)=(logicalRepr b.1,b.2.val):=Sum.inr.inj h
      exact congrArg Sum.inr (Prod.ext (logicalRepr_injective (congrArg Prod.fst h'))
        (Fin.ext (congrArg Prod.snd h')))

lemma mem_logicalEdges (vs : List ℕ) (e : RawLogical) :
    e∈logicalEdges vs ↔ e.1∈vs ∧ e.2∈vs ∧ e.1<e.2 := by
  rcases e with ⟨a,b⟩
  simp [logicalEdges,and_assoc]
lemma logicalRepr_mem (e : LogicalEdge (Fin n)) : logicalRepr e∈logicalEdges (List.range n) := by
  rw [mem_logicalEdges]
  exact ⟨List.mem_range.mpr e.val.1.isLt,List.mem_range.mpr e.val.2.isLt,e.property⟩
lemma logicalEdges_complete (e : RawLogical) (h : e∈logicalEdges (List.range n)) :
    ∃ a : LogicalEdge (Fin n),logicalRepr a=e := by
  rw [mem_logicalEdges] at h
  exact ⟨⟨(⟨e.1,List.mem_range.mp h.1⟩,⟨e.2,List.mem_range.mp h.2.1⟩),h.2.2⟩,rfl⟩
lemma vertexRepr_mem (fuel : List Bool) (v : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) :
    vertexRepr v∈vertices (List.range n,fuel) := by
  cases v with
  | inl v => simp only [vertices,List.mem_append,List.mem_map]; exact Or.inl ⟨v.val,List.mem_range.mpr v.isLt,rfl⟩
  | inr q =>
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨(logicalRepr q.1,q.2.val),List.mem_product.mpr ⟨logicalRepr_mem q.1,List.mem_range.mpr q.2.isLt⟩,rfl⟩
lemma vertices_complete (fuel : List Bool) (v : RawVertex) (h : v∈vertices (List.range n,fuel)) :
    ∃ a : Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length),vertexRepr a=v := by
  simp only [vertices,List.mem_append,List.mem_map] at h
  rcases h with ⟨i,hi,rfl⟩|⟨⟨e,i⟩,hi,rfl⟩
  · exact ⟨.inl ⟨i,List.mem_range.mp hi⟩,rfl⟩
  · obtain ⟨he,hj⟩:=List.mem_product.mp hi
    obtain ⟨a,rfl⟩:=logicalEdges_complete e he
    exact ⟨.inr (a,⟨i,List.mem_range.mp hj⟩),rfl⟩
end MatchingFPRAS.ExecutableSource

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
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBottleneck
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped

lemma maximum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    maximum (repr x,repr y)=repr (max x y) := by
  unfold maximum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [max_eq_right (le_of_lt h)]
  · rw [max_eq_left (le_of_not_gt h)]
lemma minimum_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    minimum (repr x,repr y)=repr (min x y) := by
  unfold minimum
  rw [less_val _ _ x.pos y.pos,val_repr hx,val_repr hy]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [min_eq_left (le_of_lt h)]
  · rw [min_eq_right (le_of_not_gt h)]
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeLabelCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.UnitRefresh
lemma ofFn_orderedEnum (A : Type) [Fintype A] [LinearOrder A] :
    List.ofFn (orderedEnum A)=(Finset.univ : Finset A).sort (· ≤ ·) := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp only [List.getElem_ofFn]
    rfl
end MatchingFPRAS.UnitRefresh

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeEnumeration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTProdOfLinearOrder_solutions
lemma pairwise_product {A B : Type} [LinearOrder A] [LinearOrder B]
    {as : List A} {bs : List B} (ha : as.Pairwise (· < ·)) (hb : bs.Pairwise (· < ·)) :
    (as.product bs).Pairwise (· < ·) := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a _
    apply List.pairwise_map.mpr
    exact hb.imp (fun h=>Prod.Lex.right _ h)
  · apply ha.imp
    intro a b hab x hx y hy
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp hx
    obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hy
    exact Prod.Lex.left _ _ hab

lemma logicalEdges_pairwise (n : ℕ) :
    (logicalEdges (List.range n)).Pairwise (· < ·) :=
  List.Pairwise.filter _ (pairwise_product (List.pairwise_lt_range) (List.pairwise_lt_range))
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLTSumOfLinearOrder_solutions
lemma vertices_pairwise (n : ℕ) (fuel : List Bool) :
    (vertices (List.range n,fuel)).Pairwise (· < ·) := by
  unfold vertices
  apply List.pairwise_append.mpr
  refine ⟨?_,?_,?_⟩
  · apply List.pairwise_map.mpr
    exact (List.pairwise_lt_range (n:=n)).imp (fun h=>Sum.Lex.inl h)
  · apply List.pairwise_map.mpr
    exact (pairwise_product (logicalEdges_pairwise n) List.pairwise_lt_range).imp
      (fun h=>Sum.Lex.inr h)
  · intro a ha b hb
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp ha
    obtain ⟨e,he,rfl⟩:=List.mem_map.mp hb
    exact Sum.Lex.sep _ _

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLEProdOfLinearOrder_solutions
lemma logicalRepr_le {n : ℕ} (a b : LogicalEdge (Fin n)) :
    logicalRepr a ≤ logicalRepr b ↔ a ≤ b := by
  change toLex (logicalRepr a) ≤ toLex (logicalRepr b) ↔ toLex a.val ≤ toLex b.val
  simp only [Prod.Lex.le_iff,logicalRepr,ofLex_toLex,Fin.lt_def,Fin.le_def,Fin.val_inj]
attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instLESumOfLinearOrder_solutions
lemma vertexRepr_le {n m : ℕ} (a b : Vertex (Fin n) (LogicalEdge (Fin n)) m) :
    vertexRepr a ≤ vertexRepr b ↔ a ≤ b := by
  cases a with
  | inl a => cases b with
    | inl b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inl_le_inl_iff,Fin.le_def]
    | inr b =>
      change toLex (Sum.inl a.val : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inl a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
  | inr a => cases b with
    | inl b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inl b.val : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inl b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp
    | inr b =>
      change toLex (Sum.inr (logicalRepr a.1,a.2.val) : ℕ⊕RawReal) ≤ toLex (Sum.inr (logicalRepr b.1,b.2.val) : ℕ⊕RawReal) ↔
        toLex (Sum.inr a : Fin n⊕LogicalEdge (Fin n)×Fin m) ≤ toLex (Sum.inr b : Fin n⊕LogicalEdge (Fin n)×Fin m)
      simp only [Sum.Lex.inr_le_inr_iff]
      change toLex (logicalRepr a.1,a.2.val) ≤ toLex (logicalRepr b.1,b.2.val) ↔ toLex a ≤ toLex b
      simp only [Prod.Lex.le_iff,ofLex_toLex,Fin.le_def,logicalRepr_injective.eq_iff]
      have hlt : logicalRepr a.1 < logicalRepr b.1 ↔ a.1 < b.1 := by
        rw [lt_iff_not_ge,lt_iff_not_ge,logicalRepr_le]
      rw [hlt]

attribute [local instance] OAI.MatchingFPRAS.ExecutableSource.instPreorderSumOfLinearOrder_solutions
lemma vertices_eq_ofFn (n : ℕ) (fuel : List Bool) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)) i)) := by
  classical
  let V:=Vertex (Fin n) (LogicalEdge (Fin n)) (4*fuel.length)
  rw [show (fun i=>vertexRepr (UnitRefresh.orderedEnum V i))=vertexRepr ∘ UnitRefresh.orderedEnum V from rfl,
    ←List.map_ofFn,UnitRefresh.ofFn_orderedEnum]
  have ha : (vertices (List.range n,fuel)).Pairwise (· ≤ ·) :=
    (vertices_pairwise n fuel).imp (fun h=>le_of_lt h)
  have hb : (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr).Pairwise (· ≤ ·) := by
    apply List.pairwise_map.mpr
    exact (Finset.pairwise_sort _ _).imp (fun h=>(vertexRepr_le _ _).mpr h)
  have hn : (vertices (List.range n,fuel)).Nodup := (vertices_pairwise n fuel).imp (fun h=>h.ne)
  have hm := (Finset.sort_nodup (Finset.univ : Finset V) (· ≤ ·)).map vertexRepr_injective
  have hp : (vertices (List.range n,fuel)).Perm (((Finset.univ : Finset V).sort (· ≤ ·)).map vertexRepr) := by
    apply List.perm_of_nodup_nodup_toFinset_eq hn hm
    ext v
    simp only [List.mem_toFinset,List.mem_map,Finset.mem_sort,Finset.mem_univ,true_and]
    constructor
    · exact vertices_complete fuel v
    · rintro ⟨a,rfl⟩; exact vertexRepr_mem fuel a
  apply hp.eq_of_pairwise (fun _ _ _ _ h₁ h₂=>@le_antisymm _ Transport.sumOrder.toPartialOrder _ _ h₁ h₂) ha hb
end MatchingFPRAS.ExecutableSource

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
end MatchingFPRAS.TreeTyped

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeRationalWeight
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
lemma fold_product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) (a : ℚ) (ha : 0≤a) :
    ((xs.map repr).foldl (fun a b=>mul (b,a)) (repr a))=repr (xs.prod*a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    have h : 0≤x:=hx x (by simp)
    simp only [List.map_cons,List.foldl_cons,mul_repr h ha]
    rw [ih (fun y hy=>hx y (by simp [hy])) (x*a) (mul_nonneg h ha)]
    congr 1
    simp only [List.prod_cons]
    ring
lemma product_repr (xs : List ℚ) (hx : ∀ x∈xs,0≤x) : product (xs.map repr)=repr xs.prod := by
  unfold product
  have h:=fold_product_repr xs hx 1 (by decide)
  simpa only [mul_one,show repr (1:ℚ)=(1,1) from rfl] using h
end MatchingFPRAS.TreeFraction

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

lemma add_repr {x y : ℚ} (hx : 0≤x) (hy : 0≤y) :
    add (repr x,repr y)=repr (x+y) := by
  have h:=add_val (repr x) (repr y) x.pos.ne' y.pos.ne'
  rw [val_repr hx,val_repr hy] at h
  unfold add at h ⊢
  rw [normalize_val] at h
  rw [normalize_repr,h]
lemma repr_nat (n : ℕ) : repr (n:ℚ)=(n,1) := by simp [repr]

lemma fuelPower_repr (q : ℚ) (hq : 0≤q) (fuel : List Bool) :
    fuelPower (repr q,fuel)=repr (q^fuel.length) := by
  unfold fuelPower
  have he : fuel.map (fun _=>repr q)=(fuel.map (fun _=>q)).map repr := by simp
  rw [he,product_repr _ (by intro t ht; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ht; exact hq)]
  congr 1
  simp
end MatchingFPRAS.TreeFraction

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeBuild
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableBottleneck Enlargement RealGeometry

attribute [local instance] Transport.prodOrder Transport.sumOrder

lemma vertices_eq_ofFn_length (n : ℕ) (fuel : List Bool) (m : ℕ) (h : 4*fuel.length=m) :
    vertices (List.range n,fuel)=List.ofFn (fun i=>vertexRepr
      (UnitRefresh.orderedEnum (Vertex (Fin n) (LogicalEdge (Fin n)) m) i)) := by
  subst m
  exact vertices_eq_ofFn n fuel

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype

lemma polynomial_evenTest : PolynomialTime evenTest := by
  unfold evenTest
  have := polynomial_remainder
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalScale
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting
open Finset

variable {n : ℕ}
lemma rowMaximum_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i : Fin n) :
    (rowMaximum hn G v i:ℝ)=RealStage.rowMaximum hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i := by
  unfold rowMaximum RealStage.rowMaximum
  rw [Finset.apply_sup'_eq_sup'_comp _ (fun q : ℚ=>(q:ℝ)) (by intro a b; exact Rat.cast_max a b)]
  simp only [Function.comp_apply,Rat.cast_div]
lemma scaleUpdate_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (v : Fin n → ℚ) (i j : Fin n) :
    (scaleUpdate hn G v i j:ℝ)=RealStage.scaleUpdate hn (fun i j=>(G i j:ℝ)) (fun i=>(v i:ℝ)) i j := by
  by_cases h : j=i
  · subst j
    simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_self,rowMaximum_cast]
  · simp only [scaleUpdate,RealStage.scaleUpdate,Function.update_of_ne h]
lemma scalingTrace_cast (hn : 2≤n) (G : Fin n → Fin n → ℚ) (k : ℕ) (i : Fin n) :
    (scalingTrace hn G k i:ℝ)=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k i := by
  induction k generalizing i with
  | zero => norm_num [scalingTrace,RealStage.scalingTrace]
  | succ k ih =>
    simp only [scalingTrace,RealStage.scalingTrace]
    split_ifs with h
    · rw [scaleUpdate_cast]
      have hi : (fun j=>(Counting.scalingTrace hn G k j:ℝ))=RealStage.scalingTrace hn (fun i j=>(G i j:ℝ)) k := by
        funext j
        exact ih j
      rw [hi]
    · exact ih i
lemma upperEstimate_cast (D : ℕ) (d z : ℚ) :
    (upperEstimate D d z:ℝ)=RealStage.upperEstimate D d z := by
  simp only [upperEstimate,RealStage.upperEstimate]
  have hp : (0:ℝ)<d ↔ (0:ℚ)<d := by exact_mod_cast Iff.rfl
  simp only [hp]
  split_ifs <;> push_cast <;> norm_num [alpha,RealStage.alpha]
lemma sigma_cast (D K : ℕ) (e : ℚ) : (sigma D K e:ℝ)=RealStage.sigma D K e := by
  simp only [sigma,RealStage.sigma,alpha,RealStage.alpha]
  push_cast
  rfl
end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalEstimator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport

variable {V : Type*} [LinearOrder V]
lemma estimateMatrix_cast (D : ℕ) (dbar : ℚ) (zbar : LogicalEdge V → ℚ) (i j : V) :
    (estimateMatrix D dbar zbar i j:ℝ)=Enlargement.estimateMatrix D dbar (fun e=>(zbar e:ℝ)) i j := by
  rw [estimateMatrix,Counting.upperEstimate_cast,probeMatrix_cast]
  rfl

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_rec8920_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
omit [Nontrivial (Fin G.n)] in
lemma sourceD_eq (K : ℕ) : sourceD (G:=G) K=Enlargement.sourceD (V:=Fin G.n) K := by
  simp only [sourceD,Enlargement.sourceD,Fintype.card_fin]

lemma average_Probe (w w₁ : Fin G.n → Fin G.n → ℚ) (K : ℕ) (e : LogicalEdge (Fin G.n))
    (x : Fin S → SourceMarked (fun a b=>(w a b:ℝ)) K) :
    (sampleAverage (RationalSource.observableProbe w w₁ K e) (RationalSource.sourceMarkedEquiv w K ∘ x):ℝ)=
      Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(w a b:ℝ)) (fun a b=>(w₁ a b:ℝ)) K e) x := by
  simp only [sampleAverage,Enlargement.sampleAverage,Rat.cast_div,Rat.cast_sum,Rat.cast_natCast,Function.comp_apply,
    RationalSource.observableProbe_cast]
lemma ScaleState.matrix_cast (s : ScaleState G j)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    (fun a b=>(s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ))=
      Enlargement.estimateMatrix (sourceD (G:=G) K)
        (Enlargement.sampleAverage (Enlargement.observableD (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K) x)
        (fun e=>Enlargement.sampleAverage (Enlargement.observableProbe (fun a b=>(s.activity a b:ℝ))
          (fun a b=>(s.nextActivity a b:ℝ)) K e) x) := by
  funext a b
  simp only [ScaleState.matrix,estimateMatrix_cast,average_D,average_Probe]
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_SortedList
attribute [-instance] _root_.OAI.MatchingFPRAS.TreeTyped.SparseProgram.decideMatchingOn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Amplification
open Finset

variable {k : ℕ}

open Finset MatchingFPRAS.Adaptive MatchingFPRAS.Transport
open scoped Classical

variable {Ω : Type*} [Fintype Ω]

open Finset MatchingFPRAS.Adaptive
open scoped Classical

lemma repetitions_source (δ : ℚ) : 2*halfRepetitions δ+1=10*(Nat.clog 2 ⌈δ⁻¹⌉₊+1)+1 := by
  unfold halfRepetitions
  ring
end MatchingFPRAS.Amplification

namespace MatchingFPRAS.Counting
lemma leastSchedule_le (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1)
    (k : ℕ) (hk : scheduleAdmissible n e k) : leastSchedule n hn e he he1≤k := Nat.find_min' _ hk
end MatchingFPRAS.Counting

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma FractionBound.mono {B C : ℕ} {x : ℝ} (h : FractionBound B x) (hBC : B≤C) : FractionBound C x := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := h
  exact ⟨a,b,hb,ha.trans hBC,hbb.trans hBC,rfl⟩
lemma FractionBound.zero {B : ℕ} (hB : 1≤B) : FractionBound B 0 :=
  ⟨0,1,by omega,by omega,hB,by simp⟩
lemma FractionBound.one {B : ℕ} (hB : 1≤B) : FractionBound B 1 :=
  ⟨1,1,by omega,hB,hB,by simp⟩
lemma FractionBound.nat (a : ℕ) : FractionBound (a+1) a :=
  ⟨a,1,by omega,by omega,by omega,by simp⟩
lemma FractionBound.mul {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y) :
    FractionBound (B*C) (x*y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  refine ⟨a*c,b*d,Nat.mul_pos hb hd,Nat.mul_le_mul ha hc,Nat.mul_le_mul hbb hdd,?_⟩
  push_cast
  ring
lemma FractionBound.div {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y)
    (hy0 : 0<y) : FractionBound (B*C) (x/y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  have hc0 : 0 < c := by
    have hd0 : (0:ℝ)<d := by exact_mod_cast hd
    have hcr := (lt_div_iff₀ hd0).mp hy0
    exact_mod_cast (by simpa using hcr : (0:ℝ) < c)
  refine ⟨a*d,b*c,Nat.mul_pos hb hc0,Nat.mul_le_mul ha hdd,Nat.mul_le_mul hbb hc,?_⟩
  push_cast
  field_simp
lemma FractionBound.add {B C : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound C y) :
    FractionBound (2*B*C) (x+y) := by
  obtain ⟨a,b,hb,ha,hbb,rfl⟩ := hx
  obtain ⟨c,d,hd,hc,hdd,rfl⟩ := hy
  refine ⟨a*d+c*b,b*d,Nat.mul_pos hb hd,?_,?_,?_⟩
  · have h₁ := Nat.mul_le_mul ha hdd
    have h₂ := Nat.mul_le_mul hc hbb
    nlinarith
  · have h₁ := Nat.mul_le_mul hbb hdd
    nlinarith
  · have hb0 : (b:ℝ)≠0 := by exact_mod_cast hb.ne'
    have hd0 : (d:ℝ)≠0 := by exact_mod_cast hd.ne'
    push_cast
    field_simp
lemma FractionBound.sup' {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈s,FractionBound B (f i)) : FractionBound B (s.sup' hs f) := by
  obtain ⟨i,hi,he⟩ := exists_mem_eq_sup' hs f
  rw [he]
  exact h i hi
lemma FractionBound.max {B : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound B y) :
    FractionBound B (max x y) := by
  rcases le_total x y with h|h
  · simpa [max_eq_right h] using hy
  · simpa [max_eq_left h] using hx
lemma FractionBound.min {B : ℕ} {x y : ℝ} (hx : FractionBound B x) (hy : FractionBound B y) :
    FractionBound B (min x y) := by
  rcases le_total x y with h|h
  · simpa [min_eq_left h] using hx
  · simpa [min_eq_right h] using hy
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma cooling_fraction (n : ℕ) (hn : 0<n) : cooling n=(n:ℝ)/(n+1) := by
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold cooling
  field_simp
omit [Nontrivial (Fin G.n)] in
lemma ScaleState.edge_ratio (s : ScaleState G j) (a b : Fin G.n) :
    s.nextActivity a b/s.activity a b=1 ∨ s.nextActivity a b/s.activity a b=Trial.cooling G.n := by
  have hs₀ := (s.positive a).ne'
  have hs₁ := (s.positive b).ne'
  have hr := (raw_pos G j a b).ne'
  have he : s.nextActivity a b/s.activity a b=raw G (j+1) a b/raw G j a b := by
    unfold ScaleState.nextActivity ScaleState.activity
    field_simp
  rw [he]
  unfold raw GraphBridge.rawActivity
  split_ifs
  · left; simp
  · right
    rw [pow_succ]
    exact mul_div_cancel_left₀ _ (pow_pos (cooling_pos G.n) j).ne'
lemma ScaleState.bag_reweight (s : ScaleState G j) (e : BagEdge (sourceBags s.activity K)) :
    bagReweight s.activity s.nextActivity K e=1 ∨
      bagReweight s.activity s.nextActivity K e=Trial.cooling G.n := by
  unfold bagReweight
  split_ifs with he
  · unfold rawReweight
    split_ifs
    · unfold logicalActivity edgeActivity
      split_ifs <;> exact s.edge_ratio _ _
    · exact Or.inl rfl
  · exact Or.inl rfl
lemma product_binary_power {E : Type*} (A : Finset E) (f : E → ℝ) (c : ℝ)
    (hf : ∀ e∈A,f e=1 ∨ f e=c) : ∃ a≤A.card,∏ e∈A,f e=c^a := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨0,by simp,by simp⟩
  | @insert e A he ih =>
    obtain ⟨a,ha,hea⟩ := ih (fun i hi=>hf i (mem_insert_of_mem hi))
    rcases hf e (mem_insert_self _ _) with h|h
    · refine ⟨a,by simpa [card_insert_of_notMem he] using (Nat.le_succ_of_le ha),?_⟩
      rw [prod_insert he,h,one_mul,hea]
    · refine ⟨a+1,by simpa [card_insert_of_notMem he] using Nat.succ_le_succ ha,?_⟩
      rw [prod_insert he,h,hea,pow_succ,mul_comm]
lemma ScaleState.pm_card (s : ScaleState G j) (a : SourceMarked s.activity K) :
    a.1.val.card≤ Fintype.card (SourceVertex (Fin G.n) K) := by
  let : Fintype (BagEdge (sourceBags s.activity K)) := Fintype.ofFinite _
  apply PM.card_le_vertices
  intro e
  exact ⟨e.val.val.1.out.1,by
    change e.val.val.1.out.1∈e.val.val.1
    exact Sym2.out_fst_mem _⟩
lemma ScaleState.observable_power (s : ScaleState G j) (a : SourceMarked s.activity K) :
    (observableA s.activity K a=0 ∨ observableA s.activity K a=1) ∧
    (observableD s.activity s.nextActivity K a=0 ∨
      ∃ t≤Fintype.card (SourceVertex (Fin G.n) K),observableD s.activity s.nextActivity K a=Trial.cooling G.n^t) ∧
    (∀ e₀,observableProbe s.activity s.nextActivity K e₀ a=0 ∨
      ∃ t≤Fintype.card (SourceVertex (Fin G.n) K),observableProbe s.activity s.nextActivity K e₀ a=Trial.cooling G.n^t) := by
  refine ⟨?_,?_,?_⟩
  · unfold observableA
    split_ifs <;> simp
  · unfold observableD
    split_ifs
    · right
      obtain ⟨t,ht,he⟩ := product_binary_power a.1.val _ (Trial.cooling G.n) (fun e _=>s.bag_reweight e)
      exact ⟨t,ht.trans (s.pm_card a),he⟩
    · exact Or.inl rfl
  · intro e₀
    unfold observableProbe
    split_ifs
    · right
      obtain ⟨t,ht,he⟩ := product_binary_power (a.1.val\{centralEdge s.activity K e₀}) _
        (Trial.cooling G.n) (fun e _=>s.bag_reweight e)
      refine ⟨t,ht.trans ((card_le_card sdiff_subset).trans (s.pm_card a)),?_⟩
      convert he using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ext e
      simp only [mem_sdiff,mem_singleton]
    · exact Or.inl rfl
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma GridFraction.zero (Q : ℕ) : GridFraction Q 0 := ⟨0,Nat.zero_le _,by simp⟩
lemma GridFraction.one {Q : ℕ} (hQ : 0<Q) : GridFraction Q 1 :=
  ⟨Q,le_rfl,(div_self (by exact_mod_cast hQ.ne')).symm⟩
lemma GridFraction.fractionBound {Q : ℕ} {x : ℝ} (hQ : 0<Q) (h : GridFraction Q x) :
    FractionBound Q x := by
  obtain ⟨a,ha,he⟩ := h
  exact ⟨a,Q,hQ,ha,le_rfl,he⟩
lemma GridFraction.average {Ω : Type*} {S Q : ℕ} (f : Ω → ℝ) (x : Fin S → Ω)
    (h : ∀ i,GridFraction Q (f (x i))) :
    GridFraction (S*Q) (Enlargement.sampleAverage f x) := by
  classical
  choose a ha he using h
  refine ⟨∑ i,a i,?_,?_⟩
  · calc
      _ ≤ ∑ _i : Fin S,Q := sum_le_sum fun i _=>ha i
      _ = S*Q := by simp
  · unfold Enlargement.sampleAverage
    simp_rw [he]
    rw [← sum_div]
    push_cast
    ring
lemma GridFraction.cooling_power (n N t : ℕ) (ht : t≤N) :
    GridFraction ((n+1)^N) (((n:ℝ)/(n+1))^t) := by
  refine ⟨n^t*(n+1)^(N-t),?_,?_⟩
  · calc
      _ ≤ (n+1)^t*(n+1)^(N-t) := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
      _ = (n+1)^N := by rw [←pow_add,Nat.add_sub_of_le ht]
  · have hpos : (0:ℝ)<n+1 := by positivity
    have he : ((n+1:ℕ):ℝ)=n+1 := by push_cast; rfl
    push_cast
    rw [div_pow,show N=t+(N-t) from (Nat.add_sub_of_le ht).symm,pow_add]
    field_simp
    congr 2
    omega

lemma FractionBound.prod {ι : Type*} (A : Finset ι) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈A,FractionBound B (f i)) : FractionBound (B^A.card) (∏ i∈A,f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using FractionBound.one (B:=1) le_rfl
  | @insert i A hi ih =>
    simpa [prod_insert hi,card_insert_of_notMem hi,pow_succ,Nat.mul_comm] using
      (h i (mem_insert_self _ _)).mul (ih (fun j hj=>h j (mem_insert_of_mem hj)))
end MatchingFPRAS.BitArithmetic

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_EmpiricalDenom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma empiricalDenom_pos (G : GraphInput) (K : ℕ) : 0<empiricalDenom G K := by unfold empiricalDenom; positivity
lemma ScaleState.observables_grid (hn : 0<G.n) (s : ScaleState G j) (a : SourceMarked s.activity K) :
    GridFraction (empiricalDenom G K) (observableA s.activity K a) ∧
    GridFraction (empiricalDenom G K) (observableD s.activity s.nextActivity K a) ∧
    ∀ e₀,GridFraction (empiricalDenom G K) (observableProbe s.activity s.nextActivity K e₀ a) := by
  have h := s.observable_power a
  refine ⟨?_,?_,?_⟩
  · rcases h.1 with he|he
    · rw [he]; exact GridFraction.zero _
    · rw [he]; exact GridFraction.one (empiricalDenom_pos G K)
  · rcases h.2.1 with he|⟨t,ht,he⟩
    · rw [he]; exact GridFraction.zero _
    · rw [he,cooling_fraction G.n hn]
      exact GridFraction.cooling_power G.n _ t ht
  · intro e₀
    rcases h.2.2 e₀ with he|⟨t,ht,he⟩
    · rw [he]; exact GridFraction.zero _
    · rw [he,cooling_fraction G.n hn]
      exact GridFraction.cooling_power G.n _ t ht
lemma ScaleState.means_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) :
    FractionBound (S*empiricalDenom G K) (sampleAverage (observableA s.activity K) x) ∧
    FractionBound (S*empiricalDenom G K) (sampleAverage (observableD s.activity s.nextActivity K) x) ∧
    ∀ e₀,FractionBound (S*empiricalDenom G K) (sampleAverage (observableProbe s.activity s.nextActivity K e₀) x) := by
  have hpos := Nat.mul_pos hS (empiricalDenom_pos G K)
  refine ⟨?_,?_,?_⟩
  · exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).1)).fractionBound hpos
  · exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).2.1)).fractionBound hpos
  · intro e₀
    exact (GridFraction.average _ x (fun i=>(s.observables_grid hn (x i)).2.2 e₀)).fractionBound hpos
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
open Finset

lemma alpha_bits : FractionBound 100000 RealStage.alpha := by
  exact ⟨1,100000,by norm_num,by norm_num,le_rfl,by norm_num [RealStage.alpha]⟩
lemma matrixBound_large (D B : ℕ) (hB : 1≤B) : 100000 ≤ matrixBound D B := by
  unfold matrixBound
  have hb2 : 1≤B^2 := one_le_pow₀ hB
  nlinarith
lemma ratioEstimate_bits {B : ℕ} {a d : ℝ} (hB : 1≤B)
    (ha : FractionBound B a) (hd : FractionBound B d) :
    FractionBound (B^2) (RealStage.ratioEstimate a d) := by
  unfold RealStage.ratioEstimate
  split_ifs with h
  · simpa [pow_two] using hd.div ha h
  · exact FractionBound.one (one_le_pow₀ hB)
lemma upperEstimate_bits (D : ℕ) {B : ℕ} {d z : ℝ} (hB : 1≤B)
    (hd : FractionBound B d) (hz : FractionBound B z) :
    FractionBound (matrixBound D B) (RealStage.upperEstimate D d z) := by
  have hlarge := matrixBound_large D B hB
  unfold RealStage.upperEstimate
  split_ifs with h
  · have ht : FractionBound (matrixBound D B) ((D:ℝ)*z/d+RealStage.alpha) := by
      convert (((FractionBound.nat D).mul hz).div hd h).add alpha_bits using 1
      all_goals try with_reducible_and_instances rfl
      unfold matrixBound
      ring
    exact (alpha_bits.mono hlarge).max
      ((FractionBound.nat 3 |>.mono (by omega)).min ht)
  · exact FractionBound.one (by omega)
lemma scalingTrace_bits {n : ℕ} (hn : 2≤n) (G : Fin n → Fin n → ℝ)
    (hsym : ∀ i j,G i j=G j i) (hG : ∀ i j,i≠j → RealStage.alpha≤G i j ∧ G i j≤3)
    (B : ℕ) (hB : 2≤B) (hb : ∀ i j,FractionBound B (G i j)) (k : ℕ) :
    ∀ i,FractionBound (B^(k+1)) (RealStage.scalingTrace hn G k i) := by
  have hB1 : 1≤B := by omega
  induction k with
  | zero =>
    intro i
    change FractionBound (B^(0+1)) 2
    simpa using (show FractionBound B (2:ℝ) from ⟨2,1,by omega,hB,hB1,by norm_num⟩)
  | succ k ih =>
    intro i
    have hmono : B^(k+1)≤B^(k+1+1) := Nat.pow_le_pow_right hB1 (by omega)
    dsimp only [RealStage.scalingTrace]
    split_ifs with hk
    · unfold RealStage.scaleUpdate
      by_cases hi : i=⟨k,hk⟩
      · subst i
        simp only [Function.update_self]
        unfold RealStage.rowMaximum
        have hpos := (RealStage.scalingTrace_invariant hn G hsym hG k).1.pos
        convert FractionBound.sup' (univ.erase (⟨k,hk⟩ : Fin n)) (RealStage.others_nonempty hn _)
          (fun j=>G ⟨k,hk⟩ j / RealStage.scalingTrace hn G k j) (B*B^(k+1))
          (fun j _=>(hb ⟨k,hk⟩ j).div (ih j) (hpos j)) using 1
        all_goals try with_reducible_and_instances rfl
        rw [pow_succ,Nat.mul_comm]
      · rw [Function.update_of_ne hi]
        exact (ih i).mono hmono
    · exact (ih i).mono hmono
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Trial
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
lemma ScaleState.ratioEstimate_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) :
    FractionBound ((S*empiricalDenom G K)^2) (s.ratioEstimate x) := by
  have hb := s.means_bits hn hS x
  exact BitArithmetic.ratioEstimate_bits (Nat.mul_pos hS (empiricalDenom_pos G K)) hb.1 hb.2.1
lemma ScaleState.matrix_bits (hn : 0<G.n) (s : ScaleState G j)
    (hS : 0<S) (x : Fin S → SourceMarked s.activity K) (a b : Fin G.n) :
    FractionBound (matrixBound (sourceD (V:=Fin G.n) K) (S*empiricalDenom G K)) (s.matrix x a b) := by
  have hb := s.means_bits hn hS x
  unfold ScaleState.matrix estimateMatrix
  apply upperEstimate_bits _ (Nat.mul_pos hS (empiricalDenom_pos G K)) hb.2.1
  unfold probeMatrix
  split_ifs
  · exact FractionBound.zero (Nat.mul_pos hS (empiricalDenom_pos G K))
  · exact hb.2.2 _
open Finset Switching Subdivision RealGeometry Hierarchy Transport Enlargement StageAnalysis BitArithmetic
open scoped Classical

variable {G : GraphInput} [Nontrivial (Fin G.n)]
omit [Nontrivial (Fin G.n)] in
lemma initial_scale_bits (hn : 2≤G.n) (a : Fin G.n) :
    FractionBound (G.n+1) ((initialScaleState G hn).scale a) := by
  refine ⟨1,Nat.sqrt (G.n-1),?_,by omega,?_,?_⟩
  · exact Nat.le_sqrt.mpr (by omega)
  · exact (Nat.sqrt_le_self _).trans (by omega)
  · change (Initializer.initialScale G.n:ℝ)=_
    simp [Initializer.initialScale]

end MatchingFPRAS.Trial

namespace MatchingFPRAS.FiniteTrial
open Finset Enlargement Transport BitArithmetic
open scoped Classical

variable {G : GraphInput} {j K S : ℕ} [Nontrivial (Fin G.n)]
attribute [local instance] NumberedHierarchy.labelOrder sym2Order bagEdgeOrder bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec prodOrder sumOrder
noncomputable local instance instDecidableEqSourceLabelFinNCastReal_3_rec8920_1 (w : Fin G.n → Fin G.n → ℚ) (K : ℕ) :
    DecidableEq (SourceLabel (fun x y=>(w x y:ℝ)) K) := Classical.decEq _
lemma ScaleState.ratioEstimate_bits (hn : 0<G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) :
    FractionBound ((S*Trial.empiricalDenom G K)^2)
      (s.ratioEstimate (RationalSource.sourceMarkedEquiv s.activity K ∘ x):ℝ) := by
  have hb := s.toReal.ratioEstimate_bits (K:=K) (S:=S) hn hS
  unfold Trial.ScaleState.ratioEstimate at hb
  rw [←s.activity_cast,←s.nextActivity_cast] at hb
  rw [s.ratioEstimate_cast]
  exact hb x
lemma ScaleState.matrix_bits (hn : 0<G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) (a b : Fin G.n) :
    FractionBound (matrixBound (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K))
      (s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ) := by
  have hb := s.toReal.matrix_bits (K:=K) (S:=S) hn hS
  unfold Trial.ScaleState.matrix at hb
  rw [←s.activity_cast,←s.nextActivity_cast] at hb
  have he := congrFun (congrFun (s.matrix_cast x) a) b
  rw [he,sourceD_eq]
  exact hb x a b
lemma ScaleState.updateVector_bits (hn : 2≤G.n) (s : ScaleState G j) (hS : 0<S)
    (x : Fin S → SourceMarked (fun a b=>(s.activity a b:ℝ)) K) (a : Fin G.n) :
    FractionBound ((matrixBound (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K))^(G.n+1))
      (s.updateVector hn (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a:ℝ) := by
  rw [ScaleState.updateVector,Counting.scalingTrace_cast]
  apply scalingTrace_bits hn _ _ _ _ _ _ _ a
  · intro a b
    exact_mod_cast s.matrix_symm _ a b
  · intro a b _
    have h:=s.matrix_bounds (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b
    constructor
    · have hh : ((Counting.alpha:ℚ):ℝ) ≤ (s.matrix (RationalSource.sourceMarkedEquiv s.activity K ∘ x) a b:ℝ) := by exact_mod_cast h.1
      simpa [Counting.alpha,RealStage.alpha] using hh
    · exact_mod_cast h.2
  · have h:=matrixBound_large (Enlargement.sourceD (V:=Fin G.n) K) (S*Trial.empiricalDenom G K)
      (Nat.mul_pos hS (Trial.empiricalDenom_pos G K))
    omega
  · intro a b
    exact s.matrix_bits (by omega) hS x a b
omit [Nontrivial (Fin G.n)] in
lemma initial_scale_bits (hn : 2≤G.n) (a : Fin G.n) :
    FractionBound (G.n+1) ((initialScaleState G hn).scale a:ℝ) := by
  exact Trial.initial_scale_bits hn a
lemma layers_scale_bits (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (a : Fin G.n) :
    FractionBound (p.scaleBound j) ((layers p j hj).state x |>.scale a:ℝ) := by
  induction j with
  | zero => simpa [layers,firstLayer,Trial.Parameters.scaleBound] using initial_scale_bits p.hn a
  | succ j ih =>
    change FractionBound _ ((((layers p j (by omega)).state x.1).scale a *
      ((layers p j (by omega)).state x.1).updateVector p.hn
        (RationalSource.sourceMarkedEquiv ((layers p j (by omega)).state x.1).activity p.K ∘ x.2) a:ℚ):ℝ)
    rw [Rat.cast_mul]
    have hv := ((layers p j (by omega)).state x.1).updateVector_bits p.hn p.S_pos x.2 a
    have hh := (ih (by omega) x.1).mul hv
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    change (G.n+1)*p.matrixBound^((j+1)*(G.n+1))=
      ((G.n+1)*p.matrixBound^(j*(G.n+1)))*p.matrixBound^(G.n+1)
    rw [add_mul,one_mul,pow_add]
    ring
lemma layers_ratio_bits (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K)
    (x : (layers p j hj).Ω) (i : Fin j) :
    FractionBound (p.empiricalBound^2) ((layers p j hj).ratios x i:ℝ) := by
  induction j with
  | zero => exact Fin.elim0 i
  | succ j ih =>
    refine Fin.lastCases ?_ (fun i=>?_) i
    · simpa only [layers,Layer.append,Fin.snoc_last,Trial.Parameters.empiricalBound] using
        ((layers p j (by omega)).state x.1).ratioEstimate_bits (by have := p.hn; omega) p.S_pos x.2
    · simpa only [layers,Layer.append,Fin.snoc_castSucc] using ih (by omega) x.1 i
end MatchingFPRAS.FiniteTrial

namespace MatchingFPRAS.BitArithmetic
lemma FractionBound.num_den {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    q.num.natAbs≤B ∧ q.den≤B := by
  obtain ⟨a,b,hb,ha,hbb,he⟩:=h
  have hq : q=(a:ℚ)/b := by
    apply Rat.cast_injective (α:=ℝ)
    simpa only [Rat.cast_div,Rat.cast_natCast] using he
  have hq' : q=Rat.divInt (a:ℤ) (b:ℤ) := by simpa only [Rat.divInt_eq_div,Int.cast_natCast] using hq
  have hb0 : (b:ℤ)≠0 := by exact_mod_cast hb.ne'
  have hd : q.den∣b := by
    have hh:=Rat.den_dvd (a:ℤ) (b:ℤ)
    rw [←hq'] at hh
    exact_mod_cast hh
  refine ⟨?_,(Nat.le_of_dvd hb hd).trans hbb⟩
  by_cases ha0 : a=0
  · simp [ha0] at hq
    simp [hq]
  · have hh:=Rat.num_dvd (a:ℤ) hb0
    rw [←hq'] at hh
    have hn : q.num.natAbs∣a := by simpa using Int.natAbs_dvd_natAbs.mpr hh
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) hn).trans ha
lemma size_mul_le (a b : ℕ) : (a*b).size≤a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  have h₁:=Nat.lt_size_self a
  have h₂:=Nat.lt_size_self b
  have h₃ : 0<(2:ℕ)^a.size := by positivity
  nlinarith
lemma size_pow_le (a k : ℕ) : (a^k).size≤k*a.size+1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have h:=size_mul_le (a^k) a
    rw [Nat.succ_mul]
    omega
lemma size_empiricalBound {G : GraphInput} (p : Trial.Parameters G) :
    p.empiricalBound.size≤p.S.size+Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1 := by
  unfold Trial.Parameters.empiricalBound Trial.empiricalDenom
  exact (size_mul_le _ _).trans (by have h:=size_pow_le (G.n+1) (Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)); omega)
lemma size_matrixBound {G : GraphInput} (p : Trial.Parameters G) :
    p.matrixBound.size≤19+(p.D+1).size+2*p.empiricalBound.size := by
  unfold Trial.Parameters.matrixBound matrixBound
  have h₁:=size_mul_le (200000*(p.D+1)) (p.empiricalBound^2)
  have h₂:=size_mul_le 200000 (p.D+1)
  have h₃:=size_pow_le p.empiricalBound 2
  have h₄ : (200000:ℕ).size=18 := by decide
  omega
lemma size_scaleBound {G : GraphInput} (p : Trial.Parameters G) (j : ℕ) :
    (p.scaleBound j).size≤(G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := by
  unfold Trial.Parameters.scaleBound
  have h₁:=size_mul_le (G.n+1) (p.matrixBound^(j*(G.n+1)))
  have h₂:=size_pow_le p.matrixBound (j*(G.n+1))
  omega
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.Counting

lemma polynomial_schedule (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) :
    scheduleAdmissible n e (schedulePolynomial n e) := by
  have hn0 : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have hnz : (n:ℚ)≠0 := ne_of_gt hn0
  have hb : (2:ℚ)≤(1+1/n)^n := by
    have hh:=one_add_mul_le_pow (a:=(1/(n:ℚ))) (le_trans (by norm_num : (-2:ℚ)≤0) (by positivity : (0:ℚ)≤1/n)) n
    norm_num [mul_inv_cancel₀ hnz] at hh
    simpa only [one_div] using hh
  have hec : e⁻¹≤(⌈e⁻¹⌉₊:ℚ) := Nat.le_ceil _
  have hecp : 0<⌈e⁻¹⌉₊ := by
    by_contra h
    have hz : ⌈e⁻¹⌉₊=0 := by omega
    rw [hz] at hec
    have hp : 0<e⁻¹ := inv_pos.mpr he
    norm_num at hec
    linarith
  have hnp : (n:ℚ)≤2^n := by exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hp₁ : (n:ℚ)^(n/2)≤2^(n*n) := by
    calc
      _ ≤ (2^n:ℚ)^(n/2) := pow_le_pow_left₀ hn0.le hnp _
      _ = (2:ℚ)^(n*(n/2)) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left n (Nat.div_le_self _ _))
  have hp₂ : (32:ℚ)/e≤2^(32*⌈e⁻¹⌉₊) := by
    calc
      _ = 32*e⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 32*(⌈e⁻¹⌉₊:ℚ) := mul_le_mul_of_nonneg_left hec (by norm_num)
      _ ≤ (2:ℚ)^(32*⌈e⁻¹⌉₊) := by exact_mod_cast (Nat.lt_two_pow_self (n:=32*⌈e⁻¹⌉₊)).le
  have hp : (n:ℚ)^(n/2)*(32/e) ≤ (1+1/n)^schedulePolynomial n e := by
    calc
      _ ≤ (2:ℚ)^(n*n)*2^(32*⌈e⁻¹⌉₊) := mul_le_mul hp₁ hp₂ (by positivity) (by positivity)
      _ = (2:ℚ)^(n*n+32*⌈e⁻¹⌉₊) := (pow_add _ _ _).symm
      _ ≤ ((1+1/n:ℚ)^n)^(n*n+32*⌈e⁻¹⌉₊) := pow_le_pow_left₀ (by norm_num) hb _
      _ = _ := by rw [←pow_mul]; rfl
  refine ⟨by unfold schedulePolynomial; have := Nat.mul_pos (show 0<n by omega) (show 0<n*n+32*⌈e⁻¹⌉₊ by positivity); omega,?_⟩
  have hbase : (0:ℚ)<1+1/n := by positivity
  apply (div_le_iff₀ (pow_pos hbase _)).mpr
  have hh := (div_le_iff₀ he).mp (show (n:ℚ)^(n/2)*32/e≤(1+1/n)^schedulePolynomial n e by simpa [mul_div_assoc] using hp)
  nlinarith
lemma leastSchedule_polynomial (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    leastSchedule n hn e he he1 ≤ schedulePolynomial n e :=
  leastSchedule_le n hn e he he1 _ (polynomial_schedule n hn e he)
end MatchingFPRAS.Counting

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_RationalCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.FiniteTrial
variable {G : GraphInput} [Nontrivial (Fin G.n)]
omit [Nontrivial (Fin G.n)] in
lemma sampleCount_eq (p : Trial.Parameters G) : sampleCount p=p.S := by
  unfold sampleCount Trial.Parameters.S Enlargement.stageSampleCount
  apply Nat.ceil_congr
  intro s
  unfold Trial.Parameters.D
  rw [←sourceD_eq (G:=G)]
  have hh:=Counting.sigma_cast (sourceD (G:=G) p.K) p.K p.epsilon
  rw [←hh]
  exact_mod_cast Iff.rfl
end MatchingFPRAS.FiniteTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OutputLengthBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.Counting
lemma sigma_inv_polynomial (D K : ℕ) (e : ℚ) (he : 0<e) :
    (sigma D K e)⁻¹ ≤ 10000000*D+1000*K*(⌈e⁻¹⌉₊:ℚ) := by
  have hec : e⁻¹≤(⌈e⁻¹⌉₊:ℚ) := Nat.le_ceil _
  unfold sigma
  rw [min_def]
  split_ifs
  · have hh : (alpha/(100*(D:ℚ)))⁻¹=10000000*D := by norm_num [alpha,div_eq_mul_inv,mul_inv_rev]; ring
    rw [hh]
    exact le_add_of_nonneg_right (by positivity)
  · rw [inv_div]
    calc
      (1000*(K:ℚ))/e = 1000*K*e⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ 1000*K*(⌈e⁻¹⌉₊:ℚ) := mul_le_mul_of_nonneg_left hec (by positivity)
      _ ≤ _ := le_add_of_nonneg_left (by positivity)
end MatchingFPRAS.Counting
namespace MatchingFPRAS.Trial
open Enlargement

lemma Parameters.N_polynomial {G : GraphInput} (p : Parameters G) :
    p.N≤G.n+G.n^2*(4*(2*p.K+2)) := by
  have h := Fintype.card_subtype_le (fun a : Fin G.n × Fin G.n=>a.1<a.2)
  change Fintype.card (LogicalEdge (Fin G.n))≤Fintype.card (Fin G.n × Fin G.n) at h
  simp only [Fintype.card_prod,Fintype.card_fin] at h
  simp only [Parameters.N,SourceVertex,RealGeometry.Vertex,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  simpa only [pow_two] using Nat.add_le_add_left (Nat.mul_le_mul_right (4*(2*p.K+2)) h) G.n
lemma Parameters.D_polynomial {G : GraphInput} (p : Parameters G) :
    p.D=100*p.N^2*(100000000*(G.n+1)^4) := by
  simp only [Parameters.D,sourceD,Parameters.N,Fintype.card_fin]
lemma Parameters.S_polynomial {G : GraphInput} [Nontrivial (Fin G.n)] (p : Parameters G) :
    p.S≤10*(10000000*p.D+1000*p.K*⌈p.epsilon⁻¹⌉₊)^2*(G.n+p.K+1) := by
  rw [←FiniteTrial.sampleCount_eq p]
  unfold FiniteTrial.sampleCount
  apply Nat.ceil_le.mpr
  have hh:=Counting.sigma_inv_polynomial p.D p.K p.epsilon p.epsilon_pos
  have heq : FiniteTrial.sourceD (G:=G) p.K=p.D := FiniteTrial.sourceD_eq (G:=G) p.K
  rw [←heq] at hh
  have hh0 : 0≤(Counting.sigma (FiniteTrial.sourceD (G:=G) p.K) p.K p.epsilon)⁻¹ :=
    inv_nonneg.mpr (Counting.sigma_nonneg _ _ _ p.epsilon_pos.le)
  push_cast
  gcongr
  simpa only [heq] using hh
end MatchingFPRAS.Trial

namespace MatchingFPRAS.BitArithmetic
lemma size_add_le (a b : ℕ) : (a+b).size≤a.size+b.size+1 := by
  apply Nat.size_le.mpr
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have h₁ : (2:ℕ)^a.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
  have h₂ : (2:ℕ)^b.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_succ]
  omega
lemma complete_count_size (n : ℕ) : (Z (completeGraph n)+1).size≤(n/2)*n.size+3 := by
  have hb : Z (completeGraph n)≤n^(n/2) := by
    rw [GraphBridge.complete_count]
    exact UnitRefresh.pairingCount_le_half_power n
  have hh:=size_add_le (Z (completeGraph n)) 1
  have hs:=Nat.size_le_size hb
  have hp:=size_pow_le n (n/2)
  have h1 : (1:ℕ).size=1 := by decide
  omega
end MatchingFPRAS.BitArithmetic

namespace MatchingFPRAS.BitComplexity

lemma PolynomiallyBounded.const (c : ℕ) : PolynomiallyBounded (fun _=>c) := by
  exact ⟨c,0,fun _ _=>by simp⟩
lemma PolynomiallyBounded.id : PolynomiallyBounded (fun x=>x) := by
  exact ⟨1,1,fun _ _=>by simp⟩
lemma PolynomiallyBounded.add {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>f x+g x) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨E,k,hg⟩:=hg
  refine ⟨C+E,d+k,fun x hx=>?_⟩
  have h₁ : x^d≤x^(d+k) := Nat.pow_le_pow_right hx (by omega)
  have h₂ : x^k≤x^(d+k) := Nat.pow_le_pow_right hx (by omega)
  calc
    _ ≤ C*x^d+E*x^k := Nat.add_le_add (hf x hx) (hg x hx)
    _ ≤ C*x^(d+k)+E*x^(d+k) := Nat.add_le_add (Nat.mul_le_mul_left C h₁) (Nat.mul_le_mul_left E h₂)
    _ = _ := (Nat.add_mul _ _ _).symm
lemma PolynomiallyBounded.mul {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>f x*g x) := by
  obtain ⟨C,d,hf⟩:=hf
  obtain ⟨E,k,hg⟩:=hg
  refine ⟨C*E,d+k,fun x hx=>?_⟩
  calc
    _ ≤ (C*x^d)*(E*x^k) := Nat.mul_le_mul (hf x hx) (hg x hx)
    _ = _ := by rw [pow_add]; ac_rfl
lemma PolynomiallyBounded.pow {f : ℕ → ℕ} (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun x=>(f x)^k) := by
  obtain ⟨C,d,hf⟩:=hf
  refine ⟨C^k,d*k,fun x hx=>?_⟩
  calc
    _ ≤ (C*x^d)^k := Nat.pow_le_pow_left (hf x hx) k
    _ = _ := by rw [mul_pow,pow_mul]
private lemma c (n : ℕ) : PolynomiallyBounded (fun _=>n) := PolynomiallyBounded.const n
private lemma X : PolynomiallyBounded (fun n=>n) := PolynomiallyBounded.id
lemma boundK_polynomial : PolynomiallyBounded boundK := by
  exact ((c 2).mul X).mul ((((c 2).mul X).mul ((c 2).mul X)).add ((c 32).mul X))
lemma boundN_polynomial : PolynomiallyBounded boundN := by
  exact ((c 2).mul X).add (((((c 2).mul X).pow 2)).mul ((c 4).mul (((c 2).mul boundK_polynomial).add (c 2))))
lemma boundD_polynomial : PolynomiallyBounded boundD := by
  exact ((c 100).mul (boundN_polynomial.pow 2)).mul ((c 100000000).mul ((((c 2).mul X).add (c 1)).pow 4))
lemma boundS_polynomial : PolynomiallyBounded boundS := by
  exact ((c 10).mul ((((c 10000000).mul boundD_polynomial).add (((c 1000).mul boundK_polynomial).mul X)).pow 2)).mul ((((c 2).mul X).add boundK_polynomial).add (c 1))
open Transport

lemma ladderL_polynomial {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>ladderL (f x) (g x)) := by
  exact (((c (10^4)).mul hf).mul hg).pow 100
lemma ladderQ_polynomial {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun x=>ladderQ (f x) (g x)) := by
  exact (c 32).mul (ladderL_polynomial hf hg)
lemma tier_polynomial {f g h : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g)
    (hh : PolynomiallyBounded h) : PolynomiallyBounded (fun x=>tierPolynomial (f x) (g x) (h x)) := by
  exact (hf.pow 2).mul ((hg.add ((c 2).mul hh)).add (c 2))
end MatchingFPRAS.BitComplexity

namespace MatchingFPRAS.BitComplexity
open FiniteTrial Trial Transport Amplification

lemma parameters_K_le {G : GraphInput} (hn : 2 ≤ G.n) (heven : Even G.n)
    (e : ℚ) (he : 0<e) (he1 : e<1) (x : ℕ) (hnx : G.n ≤ 2*x) (hex : ⌈e⁻¹⌉₊ ≤ x) :
    (parameters G hn heven e he he1).K ≤ boundK x := by
  apply (Counting.leastSchedule_polynomial G.n hn e he he1).trans
  unfold Counting.schedulePolynomial boundK
  gcongr
lemma parameters_N_le {G : GraphInput} (p : Parameters G)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hk : p.K ≤ boundK x) : p.N ≤ boundN x := by
  apply p.N_polynomial.trans
  unfold boundN
  gcongr
lemma parameters_D_le {G : GraphInput} (p : Parameters G)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hN : p.N ≤ boundN x) : p.D ≤ boundD x := by
  rw [p.D_polynomial]
  unfold boundD
  gcongr
lemma parameters_S_le {G : GraphInput} [Nontrivial (Fin G.n)] (p : Parameters G)
    (x : ℕ) (hnx : G.n ≤ 2*x) (hk : p.K ≤ boundK x) (hD : p.D ≤ boundD x) (he : ⌈p.epsilon⁻¹⌉₊ ≤ x) :
    p.S ≤ boundS x := by
  apply p.S_polynomial.trans
  unfold boundS
  gcongr
end MatchingFPRAS.BitComplexity

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineMedian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineMedian
open TreeTyped TreeFraction

lemma polynomial_compare : PolynomialTime compareRealizer := by
  unfold compareRealizer; apply polynomial_congr
  exact polynomial_composition (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_less) polynomial_boolNot

lemma polynomial_sorted : PolynomialTime sortedRealizer := polynomial_insertionSort relation polynomial_compare

lemma polynomial_median : PolynomialTime medianRealizer :=
  polynomial_composition (polynomial_pair polynomial_sorted
    (polynomial_composition (polynomial_pair polynomial_listLength (polynomial_constant _)) polynomial_quotient)) (polynomial_getDFast _)

end MatchingFPRAS.OnlineMedian

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlinePowerSearch
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

lemma powerCandidate_repr (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (i : ℕ)
    (hi : i≤fuel.length) :
    powerCandidate (((repr a,repr b),fuel),i)=decide (b≤a^i) := by
  unfold powerCandidate
  rw [fuelPower_repr a ha,List.length_take,min_eq_left hi]
  rw [less_val _ _ (a^i).pos b.pos,
    val_repr (by positivity),val_repr hb]
  apply Bool.eq_iff_iff.mpr
  simp
lemma findPower_le (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (i : ℕ)
    (hi : i≤fuel.length) (hr : b ≤ a ^ i) : findPower ((repr a, repr b), fuel) ≤ i := by
  apply listMin_le
  simp only [List.mem_filter,List.mem_range,powerCandidate_repr a b ha hb fuel i hi,
    decide_eq_true_eq]
  exact ⟨by omega,hr⟩
lemma le_findPower (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (i : ℕ)
    (hi : i≤fuel.length)
    (hmin : ∀ j,j≤fuel.length→b≤a^j→i≤j) : i≤findPower ((repr a,repr b),fuel) := by
  apply le_listMin hi
  intro j hj
  simp only [List.mem_filter,List.mem_range] at hj
  have hj' : j≤fuel.length := by omega
  rw [powerCandidate_repr a b ha hb fuel j hj',decide_eq_true_eq] at hj
  exact hmin j hj' hj.2
lemma findPower_eq (a b : ℚ) (ha : 0≤a) (hb : 0≤b) (fuel : List Bool) (T : ℕ)
    (hT : T≤fuel.length) (hr : b≤a^T) (hmin : ∀ j,b≤a^j→T≤j) :
    findPower ((repr a,repr b),fuel)=T :=
  Nat.le_antisymm (findPower_le a b ha hb fuel T hT hr)
    (le_findPower a b ha hb fuel T hT (fun j _ hj=>hmin j hj))

lemma endpoint_le_bound (N D K : ℕ) (hN : 0<N) :
    Transport.endpoint N D K hN≤Transport.tierBound N D K := by
  rw [Transport.endpoint_eq]
  exact Transport.ladderTier_le N D K hN
lemma endpoint_power_spec (N D K : ℕ) (hN : 0<N) :
    max (D:ℚ) (3*4^K)≤(Transport.rationalBase N)^(Transport.endpoint N D K hN) := by
  have h:=Transport.endpoint_reaches N D K hN
  rw [←Transport.rationalBase_cast] at h
  exact_mod_cast h
lemma endpoint_power_min (N D K : ℕ) (hN : 0<N) (t : ℕ)
    (ht : max (D:ℚ) (3*4^K)≤(Transport.rationalBase N)^t) :
    Transport.endpoint N D K hN≤t := by
  rw [Transport.endpoint_eq]
  apply Nat.find_min'
  rw [←Transport.rationalBase_cast]
  exact_mod_cast ht
lemma findPower_endpoint (N D K : ℕ) (hN : 0<N) (fuel : List Bool)
    (hf : Transport.tierBound N D K≤fuel.length) :
    findPower ((repr (Transport.rationalBase N),repr (max (D:ℚ) (3*4^K))),fuel)=
      Transport.endpoint N D K hN := by
  apply findPower_eq
  · unfold Transport.rationalBase; positivity
  · positivity
  · exact (endpoint_le_bound N D K hN).trans hf
  · exact endpoint_power_spec N D K hN
  · exact endpoint_power_min N D K hN
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Arithmetic_OnlineFractionParam
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.TreeFraction
open TreeTyped Polynomial

lemma natCeil_eq (x : Fraction) : natCeil x=⌈val x⌉₊ := by
  by_cases hd : x.2=0
  · simp [natCeil,val,hd]
  have hd' : (0:ℚ)<x.2 := by exact_mod_cast (Nat.pos_of_ne_zero hd)
  have h (m : ℕ) : ⌈val x⌉₊ ≤ m ↔ natCeil x ≤ m := by
    rw [Nat.ceil_le]
    unfold val natCeil
    rw [div_le_iff₀ hd',←Nat.cast_mul,Nat.cast_le,Nat.div_le_iff_le_mul (Nat.pos_of_ne_zero hd)]
    omega
  exact Nat.le_antisymm ((h _).mp le_rfl) ((h _).mpr le_rfl)
lemma natCeil_repr (q : ℚ) (hq : 0≤q) : natCeil (repr q)=⌈q⌉₊ := by
  rw [natCeil_eq,val_repr hq]

lemma inverse_repr (q : ℚ) (hq : 0≤q) : inverse (repr q)=repr q⁻¹ := by
  unfold inverse
  rw [normalize_repr]
  congr 1
  change (q.den:ℚ)/q.num.natAbs=q⁻¹
  calc
    _ = (val (repr q))⁻¹ := by simp [val,repr]
    _ = q⁻¹ := by rw [val_repr hq]
end MatchingFPRAS.TreeFraction

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

lemma findRoot_eq (n : ℕ) (fuel : List Bool) (hf : n.sqrt≤fuel.length) :
    findRoot (n,fuel)=n.sqrt := by
  apply Nat.le_antisymm
  · apply listMin_le
    simp only [List.mem_filter,List.mem_range,rootCandidate,decide_eq_true_eq]
    exact ⟨by omega,by simpa [pow_two,Nat.succ_eq_add_one] using Nat.lt_succ_sqrt n⟩
  · apply le_listMin hf
    intro i hi
    simp only [List.mem_filter,List.mem_range,rootCandidate,decide_eq_true_eq,pow_two] at hi
    have h:=Nat.sqrt_lt.mpr hi.2
    omega
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineCoolingSchedule
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

lemma scheduleBound_repr (n : ℕ) (e : ℚ) (he : 0≤e) :
    scheduleBound (n,TreeFraction.repr e)=Counting.schedulePolynomial n e := by
  unfold scheduleBound Counting.schedulePolynomial
  rw [inverse_repr e he,natCeil_repr _ (by positivity)]

lemma coolingPowerPlan_repr (n : ℕ) (e : ℚ) (he : 0≤e) (fuel : List Bool) :
    coolingPowerPlan ((n,TreeFraction.repr e),fuel)=
      (TreeFraction.repr (1+1/(n:ℚ)),TreeFraction.repr (32*(n:ℚ)^fuel.length/e)) := by
  unfold coolingPowerPlan
  rw [←repr_nat n,show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    show ((32,1) : Fraction)=TreeFraction.repr (32:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    fuelPower_repr _ (by positivity),mul_repr (by decide) (by positivity),
    div_repr (by positivity) he]

lemma schedule_power_iff (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) (k : ℕ) :
    Counting.scheduleAdmissible n e k ↔ 32*(n:ℚ)^(n/2)/e≤(1+1/(n:ℚ))^k := by
  have hn0 : (0:ℚ)<n := by exact_mod_cast (show 0<n by omega)
  have hb : (0:ℚ)<1+1/(n:ℚ) := by positivity
  have hp : (0:ℚ)<(1+1/(n:ℚ))^k := pow_pos hb _
  have hn1 : (1:ℚ)≤(n:ℚ)^(n/2) := one_le_pow₀ (by exact_mod_cast (show 1≤n by omega))
  unfold Counting.scheduleAdmissible
  constructor
  · rintro ⟨_,h⟩
    apply (div_le_iff₀ he).mpr
    have h':=(div_le_iff₀ hp).mp h
    nlinarith
  · intro h
    have h':=(div_le_iff₀ he).mp h
    constructor
    · by_contra hk
      have hk0 : k=0 := by omega
      rw [hk0,pow_zero,one_mul] at h'
      linarith
    · apply (div_le_iff₀ hp).mpr
      nlinarith
lemma coolingSchedule_eq (n : ℕ) (hn : 2≤n) (e : ℚ) (he : 0<e) (he1 : e<1) :
    coolingSchedule (n,TreeFraction.repr e)=Counting.leastSchedule n hn e he he1 := by
  unfold coolingSchedule coolingSearchInput
  rw [coolingPowerPlan_repr n e he.le,List.length_replicate,scheduleBound_repr n e he.le]
  apply findPower_eq
  · positivity
  · positivity
  · simpa using Counting.leastSchedule_polynomial n hn e he he1
  · exact (schedule_power_iff n hn e he he1 _).mp (Counting.leastSchedule_spec n hn e he he1)
  · intro k hk
    exact Counting.leastSchedule_le n hn e he he1 k ((schedule_power_iff n hn e he he1 k).mpr hk)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineLadderSchedule
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial ExecutableSource Transport Enlargement

lemma vertexNumber_eq (n K : ℕ) : vertexNumber (n,K)=Fintype.card (SourceVertex (Fin n) K) := by
  unfold vertexNumber
  rw [vertices_eq_ofFn_length n _ (4*(2*K+2)) (by simp),List.length_ofFn]
lemma distortion_source {G : GraphInput} [Nontrivial (Fin G.n)] (K : ℕ) :
    distortion (G.n,vertexNumber (G.n,K))=FiniteTrial.sourceD (G:=G) K := by
  simp only [distortion,vertexNumber_eq,FiniteTrial.sourceD]

lemma ladderPowerPlan_repr (N D : ℕ) (fuel : List Bool) :
    ladderPowerPlan ((N,D),fuel)=
      (TreeFraction.repr (rationalBase N),TreeFraction.repr (max (D:ℚ) (3*4^fuel.length))) := by
  unfold ladderPowerPlan
  rw [←repr_nat (N^2),←repr_nat D,
    show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,
    show ((3,1) : Fraction)=TreeFraction.repr (3:ℚ) from rfl,
    show ((4,1) : Fraction)=TreeFraction.repr (4:ℚ) from rfl,
    div_repr (by decide) (by positivity),add_repr (by decide) (by positivity),
    fuelPower_repr _ (by positivity),mul_repr (by decide) (by positivity),
    maximum_repr (by positivity) (by positivity)]
  simp only [rationalBase,Nat.cast_pow,one_div]

lemma ladderSchedule_eq (N D K : ℕ) (hN : 0<N) :
    ladderSchedule ((N,D),K)=endpoint N D K hN := by
  unfold ladderSchedule ladderSearchInput
  rw [ladderPowerPlan_repr,List.length_replicate]
  exact findPower_endpoint N D K hN _ (by simp)
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineSampleCount
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped TreeFraction Polynomial

lemma sigma_repr (D K : ℕ) (e : ℚ) (he : 0≤e) :
    sigma ((D,K),TreeFraction.repr e)=TreeFraction.repr (Counting.sigma D K e) := by
  unfold sigma
  rw [←repr_nat (100*D),←repr_nat (1000*K),
    show ((1,100000) : Fraction)=TreeFraction.repr ((1:ℚ)/100000) from by norm_num [TreeFraction.repr],
    div_repr (by positivity) (by positivity), div_repr he (by positivity),
    minimum_repr (by positivity) (by positivity)]
  congr 1
  simp only [Counting.sigma,Counting.alpha,Nat.cast_mul,Nat.cast_ofNat]

lemma sampleCount_repr (n D K : ℕ) (e : ℚ) (he : 0≤e) :
    sampleCount (n,((D,K),TreeFraction.repr e))=
      ⌈10*(Counting.sigma D K e)⁻¹^2*((n:ℚ)+K+1)⌉₊ := by
  have hs := Counting.sigma_nonneg D K e he
  unfold sampleCount sampleProduct sampleFactorFn sampleSumFn invSigma
  rw [sigma_repr D K e he,inverse_repr _ (Counting.sigma_nonneg D K e he),
    show ((10,1) : Fraction)=TreeFraction.repr (10:ℚ) from rfl,
    ←repr_nat (n+K+1),mul_repr (by positivity) (by positivity),
    mul_repr (by positivity) (by positivity),mul_repr (by positivity) (by positivity),
    natCeil_repr _ (by positivity)]
  congr 1
  simp only [Nat.cast_add,Nat.cast_one,pow_two]

variable {G : GraphInput} [Nontrivial (Fin G.n)]
omit [Nontrivial (Fin G.n)] in
lemma sampleCount_source (p : Trial.Parameters G) :
    sampleCount (G.n,((FiniteTrial.sourceD (G:=G) p.K,p.K),TreeFraction.repr p.epsilon))=p.S := by
  rw [sampleCount_repr _ _ _ _ p.epsilon_pos.le]
  exact FiniteTrial.sampleCount_eq p

lemma repetitions_repr (d : ℚ) (hd : 0≤d) :
    repetitions (TreeFraction.repr d)=2*Amplification.halfRepetitions d+1 := by
  unfold repetitions
  rw [inverse_repr d hd,natCeil_repr _ (by positivity)]
  unfold Amplification.halfRepetitions
  omega
end MatchingFPRAS.OnlineSchedule

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineInitial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource OnlineSchedule

lemma root_eq (n : ℕ) : root n=(n-1).sqrt := by
  apply findRoot_eq
  simpa using (Nat.sqrt_le_self (n-1)).trans (Nat.sub_le n 1)
lemma initialScale_repr (n : ℕ) : initialScale n=TreeFraction.repr (Initializer.initialScale n) := by
  unfold initialScale
  rw [root_eq,←repr_nat ((n-1).sqrt),show ((1,1) : Fraction)=TreeFraction.repr (1:ℚ) from rfl,div_repr (by decide) (by positivity)]
  rfl

lemma scaleVector_source (G : GraphInput) (hn : 2≤G.n) :
    scaleVector (List.range G.n)=vectorRep (FiniteTrial.initialScaleState G hn).scale := by
  unfold scaleVector vectorRep
  rw [List.length_range,initialScale_repr]
  apply List.ext_getElem
  · simp
  · intro _ _ _
    simp [FiniteTrial.initialScaleState]

end MatchingFPRAS.OnlineInitial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineInitialLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource OnlineSchedule
open Transport Enlargement

variable {G : GraphInput} [Nontrivial (Fin G.n)]
variable (hn : 2≤G.n) (heven : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1)
local notation "p" => FiniteTrial.parameters G hn heven ε he he1
lemma config_source : config (sourceSeed (G:=G) ε δ)=
    ((sourceSeed (G:=G) ε δ,(p).K),((p).N,FiniteTrial.sourceD (G:=G) (p).K)) := by
  have hl : (graphRep G).1.length=G.n := by simp [graphRep]
  unfold config seedK seedN seedD sourceSeed
  dsimp only
  rw [hl,coolingSchedule_eq G.n hn ε he he1]
  change ((_,(p).K),(vertexNumber (G.n,(p).K),distortion (G.n,vertexNumber (G.n,(p).K))))=_
  rw [distortion_source,vertexNumber_eq]
  rfl
lemma data_source : data (config (sourceSeed (G:=G) ε δ))=
    OnlineStage.fixedData p (FiniteTrial.initialScaleState G hn) := by
  rw [config_source hn heven ε δ he he1]
  unfold data sourceSeed OnlineStage.fixedData OnlineStage.data
  dsimp only
  rw [show (graphRep G).1=List.range G.n from rfl,scaleVector_source G hn,ladderSchedule_eq _ _ _ (p).N_pos]
  rfl
lemma count_source : count (config (sourceSeed (G:=G) ε δ))=(p).S := by
  rw [config_source hn heven ε δ he he1]
  unfold count sourceSeed
  dsimp only
  have hl : (graphRep G).1.length=G.n := by simp [graphRep]
  rw [hl]
  exact sampleCount_source p
lemma trialInput_source : trialInput (config (sourceSeed (G:=G) ε δ))=OnlineAmplification.initial p := by
  unfold trialInput
  rw [data_source hn heven ε δ he he1,count_source hn heven ε δ he he1,config_source hn heven ε δ he he1]
  unfold OnlineAmplification.initial OnlineTrial.represent OnlineTrial.product
  simp only [FiniteTrial.firstLayer,Fin.prod_univ_zero,mul_one]
  have hg : (sourceSeed (G:=G) ε δ).1.1.length=G.n := by simp [sourceSeed,graphRep]
  rw [hg,GraphBridge.complete_count]
  rw [TreeFraction.repr_nat]
lemma initializeInput_source (hd : 0≤δ) : initializeInput (sourceSeed (G:=G) ε δ)=
    (2*Amplification.halfRepetitions δ+1,OnlineAmplification.initial p) := by
  unfold initializeInput runInput
  rw [trialInput_source hn heven ε δ he he1,config_source hn heven ε δ he he1]
  dsimp only [sourceSeed]
  rw [repetitions_repr δ hd]
end MatchingFPRAS.OnlineInitial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Graphs_OnlineGraphInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineGraph
open TreeTyped TreeFraction ExecutableAdaptive ExecutableScaling ExecutableSource
open PhysicalStream OnlineSchedule

variable (f : Edges→Edges) (hf : ∀ es e,e∈f es↔e∈es)
include hf
omit hf in
lemma initialize_eq (x : OnlineInitial.Seed) :
    OnlineInitial.initializeInput (seed f x)=
      ((OnlineInitial.initializeInput x).1,((OnlineInitial.initializeInput x).2.1,state f (OnlineInitial.initializeInput x).2.2)) := rfl
end MatchingFPRAS.OnlineGraph

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Sampling_Endpoints2
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS

lemma edgeCard_le_input_length (G : GraphInput) (ε δ : ℚ) :
    G.edges.card≤(encodeInput G ε δ).length := by
  have hl (l : List (Fin G.n ×ₗ Fin G.n)) : l.length≤
      (l.flatMap fun e=>encodeNat (ofLex e).1.val++encodeNat (ofLex e).2.val).length := by
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      have ha : 1≤(encodeNat (ofLex a).1.val).length := by
        simp only [encodeNat,List.length_append,List.length_map,List.length_singleton]
        omega
      omega
  have h:=hl ((G.edges.map toLex.toEmbedding).sort (·≤·))
  simp only [Finset.length_sort,Finset.card_map] at h
  simp only [encodeInput,List.length_append]
  omega

namespace ExecutableInput
open TreeTyped TreeFunction

lemma polynomial_tooSparse : PolynomialTime tooSparseRealizer := by
  unfold tooSparseRealizer
  apply polynomial_congr
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

open TreePost Turing

end ExecutableInput
end MatchingFPRAS

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Codec
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
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

lemma polynomial_fromBit : PolynomialTime fromBitRealizer :=
  polynomial_choose polynomial_identity (polynomial_constant _) (polynomial_constant _)
lemma polynomial_natWord : PolynomialTime natWordRealizer := by
  unfold natWordRealizer
  apply polynomial_congr
  have := polynomial_fromBit
  have := polynomial_toBits
  have := polynomial_map polynomial_fromBit
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma polynomial_ratWord : PolynomialTime ratWordRealizer := by
  unfold ratWordRealizer
  apply polynomial_congr
  have := polynomial_natWord
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
end MatchingFPRAS.LiteralCodec

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Parse
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
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

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
-- module Solutions.OAIQ051_MC.MatchingCount_Tapes_Input
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralInput
open TreeTyped TreeFunction Polynomial LiteralParse

lemma polynomial_pairStep : PolynomialTime pairStepRealizer := by
  unfold pairStepRealizer
  apply polynomial_congr
  dsimp only [Realizer.fst,Realizer.snd]
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))
lemma pairStep_weight (n : ℕ) (s : PairState) : weight (pairStep (n,s)) ≤ weight s+weight n+4 := by
  rcases s with ⟨⟨b,m⟩,es⟩
  cases b
  · change weight ((true,n),es) ≤ weight ((false,m),es)+weight n+4
    simp only [weight_prod]
    change 1+(1+3+weight n)+weight es ≤ 1+(1+1+weight m)+weight es+weight n+4
    omega
  · change weight ((false,0),(n,m)::es) ≤ weight ((true,m),es)+weight n+4
    simp only [weight_prod,weight_cons]
    change 1+(1+1+1)+(1+(1+weight n+weight m)+weight es) ≤
      1+(1+3+weight m)+weight es+weight n+4
    omega
lemma pairFold_weight (ns : List ℕ) (s : PairState) :
    weight (ns.foldl (fun s n=>pairStep (n,s)) s) ≤ weight s+5*weight ns := by
  induction ns generalizing s with
  | nil => simp
  | cons n ns ih =>
    have h := ih (pairStep (n,s))
    have h' := pairStep_weight n s
    simp only [List.foldl_cons,weight_cons]
    omega
lemma polynomial_pairFold : PolynomialTime (fold pairStepRealizer) := by
  apply polynomial_fold polynomial_pairStep (6*X)
  intro as s pre post he
  have h := pairFold_weight pre s
  have hw : weight pre ≤ weight as := by
    have ha := weight_append pre post
    have hp := weight_pos post
    rw [he]
    omega
  simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,weight_prod]
  omega

lemma polynomial_pairs : PolynomialTime pairsRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_composition (polynomial_pair polynomial_identity (polynomial_constant _))
    polynomial_pairFold) polynomial_second)
lemma pair_pair (i j : ℕ) (es : List (ℕ×ℕ)) :
    pairStep (i,pairStep (j,((false,0),es)))=((false,0),(i,j)::es) := rfl
lemma pairs_reverse (es : List (ℕ×ℕ)) (acc : List (ℕ×ℕ)) :
    ((es.flatMap (fun e=>[e.1,e.2])).reverse.foldl (fun s n=>pairStep (n,s)) ((false,0),acc))=
      ((false,0),es++acc) := by
  induction es generalizing acc with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.nil_append,List.singleton_append,List.foldl_append,ih,List.foldl_cons,List.foldl_nil,pair_pair]
    rfl

lemma polynomial_ratTail : PolynomialTime ratTailRealizer := by
  unfold ratTailRealizer
  exact TreeTyped.polynomial_pair
    (TreeTyped.polynomial_pair
      (polynomial_composition (polynomial_composition (polynomial_composition polynomial_tail polynomial_tail)
        polynomial_tail) (polynomial_head _))
      (polynomial_composition (polynomial_composition polynomial_tail polynomial_tail) (polynomial_head _)))
    (TreeTyped.polynomial_pair (polynomial_composition polynomial_tail (polynomial_head _)) (polynomial_head _))

lemma polynomial_reversedTail : PolynomialTime reversedTailRealizer :=
  polynomial_composition (polynomial_composition polynomial_tail polynomial_tail) polynomial_reverse
lemma polynomial_fromNumbers : PolynomialTime fromNumbersRealizer := by
  unfold fromNumbersRealizer
  apply polynomial_congr
  apply polynomial_pair (polynomial_head _)
  apply polynomial_pair
  · exact polynomial_composition (polynomial_composition (polynomial_composition
      (polynomial_composition (polynomial_composition polynomial_reversedTail polynomial_tail) polynomial_tail)
        polynomial_tail) polynomial_tail) polynomial_pairs
  · exact polynomial_composition polynomial_reversedTail polynomial_ratTail

lemma polynomial_parseInput : PolynomialTime parseInputRealizer :=
  polynomial_composition LiteralParse.polynomial_parse polynomial_fromNumbers

lemma edges_fold (es : List (ℕ×ℕ)) (ns : List ℕ) :
    (es.flatMap (fun e=>encodeNat e.1++encodeNat e.2)).foldr (fun a ns=>numStep (a,ns)) ns=
      es.flatMap (fun e=>[e.1,e.2])++ns := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.flatMap_cons,List.foldr_append,ih,encodeNat_fold]
    rfl
lemma parse_source (G : GraphInput) (ε δ : ℚ) : LiteralParse.parse (encodeInput G ε δ)=
    G.n::G.edges.card::(edgeNumbers G).flatMap (fun e=>[e.1,e.2])++[ε.num.natAbs,ε.den,δ.num.natAbs,δ.den] := by
  unfold encodeInput LiteralParse.parse
  simp only [List.foldr_append,encodeNat_fold,encodeRat_fold]
  rw [show (((G.edges.map toLex.toEmbedding).sort (·≤·)).flatMap fun e=>encodeNat (ofLex e).1.val++encodeNat (ofLex e).2.val)=
    (edgeNumbers G).flatMap (fun e=>encodeNat e.1++encodeNat e.2) by simp only [edgeNumbers,List.flatMap_map]]
  rw [edges_fold]
  rfl
lemma parseInput_source (G : GraphInput) (ε δ : ℚ) :
    parseInput (encodeInput G ε δ)=(G.n,(edgeNumbers G,(TreeFraction.repr ε,TreeFraction.repr δ))) := by
  rw [parseInput,parse_source]
  unfold fromNumbers
  simp only [List.cons_append,List.headD_cons,List.tail_cons,
    List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append]
  unfold ratTail
  simp only [List.headD_cons,List.tail_cons]
  unfold pairs
  rw [pairs_reverse]
  simp only [List.append_nil]
  rfl
end MatchingFPRAS.LiteralInput

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_Algorithm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

lemma polynomial_empty : PolynomialTime emptyRealizer := by
  exact polynomial_composition (polynomial_pair polynomial_first (polynomial_constant 0)) polynomial_natEqual

lemma polynomial_invalid : PolynomialTime invalidRealizer := by
  unfold invalidRealizer Realizer.fst
  apply polynomial_congr
  have := ExecutableSource.polynomial_evenTest
  have := ExecutableInput.polynomial_tooSparse
  ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr)))

lemma work_materialize : WorkBound materializeRealizer (fun x=>x.1+weight x) := by
  have lift {A : Type} [Codec A] {f : Parsed→A} {F : Realizer f} (hF : PolynomialTime F) :
      WorkBound F (fun x=>x.1+weight x) := work_of_polynomial hF X (by intro x;simp)
  unfold materializeRealizer Realizer.fst Realizer.snd
  apply work_pair _ (lift (by ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr))))) X (by intro x;simp)
  apply work_pair _ (lift (by ((with_reducible repeat' (first | assumption | exact MatchingFPRAS.TreeTyped.polynomial_identity | exact MatchingFPRAS.TreeTyped.polynomial_first | exact MatchingFPRAS.TreeTyped.polynomial_second | exact MatchingFPRAS.TreeTyped.polynomial_boolAnd | exact MatchingFPRAS.TreeTyped.polynomial_boolOr | exact MatchingFPRAS.TreeTyped.polynomial_boolNot | exact MatchingFPRAS.TreeTyped.polynomial_add | exact MatchingFPRAS.TreeTyped.polynomial_subtract | exact MatchingFPRAS.TreeTyped.polynomial_multiply | exact MatchingFPRAS.TreeTyped.polynomial_less | exact MatchingFPRAS.TreeTyped.polynomial_leNat | exact MatchingFPRAS.TreeTyped.polynomial_natEqual | exact MatchingFPRAS.TreeTyped.polynomial_finsetList | exact MatchingFPRAS.TreeTyped.polynomial_finsetCard | exact MatchingFPRAS.TreeTyped.polynomial_finsetSingleton | exact MatchingFPRAS.TreeTyped.polynomial_listCons | exact MatchingFPRAS.TreeTyped.polynomial_listLength | exact MatchingFPRAS.TreeTyped.polynomial_append | exact MatchingFPRAS.TreeTyped.polynomial_reverse | exact MatchingFPRAS.TreeTyped.polynomial_flatten | apply MatchingFPRAS.TreeTyped.polynomial_recode | apply MatchingFPRAS.TreeTyped.polynomial_composition | apply MatchingFPRAS.TreeTyped.polynomial_pair | apply MatchingFPRAS.TreeTyped.polynomial_choose | apply MatchingFPRAS.TreeTyped.polynomial_constant | apply MatchingFPRAS.TreeTyped.polynomial_fst | apply MatchingFPRAS.TreeTyped.polynomial_snd | apply MatchingFPRAS.TreeTyped.polynomial_map | apply MatchingFPRAS.TreeTyped.polynomial_mapWith | apply MatchingFPRAS.TreeTyped.polynomial_flatMapPoly | apply MatchingFPRAS.TreeTyped.polynomial_filter | apply MatchingFPRAS.TreeTyped.polynomial_filterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetBiUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilter | apply MatchingFPRAS.TreeTyped.polynomial_finsetFilterWith | apply MatchingFPRAS.TreeTyped.polynomial_finsetImage | apply MatchingFPRAS.TreeTyped.polynomial_finsetUnion | apply MatchingFPRAS.TreeTyped.polynomial_finsetSDiff | apply MatchingFPRAS.TreeTyped.polynomial_finsetInter | apply MatchingFPRAS.TreeTyped.polynomial_finsetErase | apply MatchingFPRAS.TreeTyped.polynomial_finsetInsert | apply MatchingFPRAS.TreeTyped.polynomial_finsetEqual | apply MatchingFPRAS.TreeTyped.polynomial_finsetSubset | apply MatchingFPRAS.TreeTyped.polynomial_finsetMember | apply MatchingFPRAS.TreeTyped.polynomial_finsetAny | apply MatchingFPRAS.TreeTyped.polynomial_finsetAll | apply MatchingFPRAS.TreeTyped.polynomial_pairEqual | apply MatchingFPRAS.TreeTyped.polynomial_lexLe | apply MatchingFPRAS.TreeTyped.polynomial_colexLe | apply MatchingFPRAS.TreeTyped.polynomial_congr))))) X (by intro x;simp)
  apply work_composition (lift polynomial_first) range_numeric_work X
  intro x;simp

lemma edgeNumbers_length (G : GraphInput) : (edgeNumbers G).length=G.edges.card := by
  simp only [edgeNumbers,List.length_map,Finset.length_sort,Finset.card_map]
lemma edgeNumbers_mem (G : GraphInput) (e : ℕ×ℕ) :
    e∈edgeNumbers G ↔ e∈(ExecutableAdaptive.graphRep G).2 := by
  classical
  simp only [edgeNumbers,ExecutableAdaptive.graphRep,List.mem_map,Finset.mem_sort,
    Finset.mem_map,Finset.mem_toList]
  constructor
  · rintro ⟨a,⟨b,hb,rfl⟩,he⟩
    exact ⟨b,hb,he⟩
  · rintro ⟨b,hb,he⟩
    exact ⟨toLex b,⟨b,hb,rfl⟩,he⟩
lemma reorder_mem (G : GraphInput) (es : OnlineGraph.Edges) (e : ℕ×ℕ) :
    e∈reorder G es ↔ e∈es := by
  classical
  unfold reorder
  split
  · rename_i he;rw [he];exact edgeNumbers_mem G e
  · rfl
lemma materialize_source (G : GraphInput) (ε δ : ℚ) :
    materialize (parseInput (encodeInput G ε δ))=
      OnlineGraph.seed (reorder G) (OnlineInitial.sourceSeed (G:=G) ε δ) := by
  rw [parseInput_source]
  unfold materialize OnlineGraph.seed OnlineGraph.graph OnlineInitial.sourceSeed reorder
  simp only [ite_true]
  rfl
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineFoldCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
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
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.PhysicalStream.Experiment
variable {A B : Type}
lemma worst_mono (p : Experiment A) (f g : A→ℕ) (h : p.All (fun a=>f a≤g a)) :
    p.worst f≤p.worst g := by
  induction p with
  | done a => exact h
  | read p ih => exact max_le_max (ih false h.1) (ih true h.2)
  | delay n p ih => exact ih h
lemma worst_const (p : Experiment A) (n : ℕ) : p.worst (fun _=>n)=n := by
  induction p with
  | done a => rfl
  | read p ih => simp only [worst,ih, max_self]
  | delay n p ih => exact ih
lemma worst_bind (p : Experiment A) (f : A→Experiment B) (h : B→ℕ) :
    (p.bind f).worst h=p.worst (fun a=>(f a).worst h) := by
  induction p with
  | done a => rfl
  | read p ih => simp only [bind,worst,ih]
  | delay n p ih => exact ih
lemma worst_map (p : Experiment A) (f : A→B) (h : B→ℕ) :
    (p.map f).worst h=p.worst (h ∘ f) := worst_bind _ _ _
end MatchingFPRAS.PhysicalStream.Experiment

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineFrameCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
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
end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineTraverseCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol _root_.OAI.MatchingFPRAS.TreeTyped.Numbered.codec
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTree
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma collectStep_cost {f : A→Experiment B} (F : Realizer f) (a : A) (bs : List B) :
    (collectStepRealizer F).cost (a,bs)=F.cost a+54*weight a+46*weight bs+
      26*(f a).worst weight+201 := by
  change (pair (composition (deterministic TreeTyped.first) F) (deterministic TreeTyped.second)).cost (a,bs)+
    (((f a).bind (fun b=>Experiment.done (b,bs))).worst (fun _=>1))=_
  rw [pair_cost,Experiment.worst_const]
  simp only [composition,deterministic,TreeTyped.first,TreeTyped.second,Experiment.worst,
    Experiment.bind,weight_prod]
  change (6*weight a+weight bs+11+F.cost a)+(3*weight a+7)+45*(1+weight a+weight bs)+
    26*(f a).worst weight+137+1=_
  omega

lemma traverse_bound {f : A→Experiment B} (F : Realizer f) :
    ∃ p : Polynomial ℕ,∀ as M,weight as≤M→(∀ a∈as,F.cost a+(f a).worst weight≤M)→
      (traverse F).cost as+(traverseM f as).worst weight≤p.eval M := by
  obtain ⟨q,hq⟩:=TreeTyped.polynomial_pair (TreeTyped.polynomial_identity (A:=List A))
    (TreeTyped.polynomial_constant ([] : List B))
  obtain ⟨r,hr⟩:=TreeTyped.polynomial_reverse (A:=B)
  let H : Polynomial ℕ := X*(X+1)+1
  let D : Polynomial ℕ := 27*X+54*X+46*H+201
  refine ⟨q+X*(D+14*X+34)+10+r.comp H+H,?_⟩
  intro as M hw ht
  have hl : as.length≤M := (list_length_le_weight as).trans hw
  have hH : H.eval M=M*(M+1)+1 := by simp [H]
  have hD : D.eval M=27*M+54*M+46*H.eval M+201 := by simp [D]
  have hf := fold_cost_bound (collectStep f) (collectStepRealizer F).cost as ([] : List B)
    (fun k bs=>weight bs+k*(M+1)≤as.length*(M+1)+1) (D.eval M) M
    (by simp; omega) hw
    (by
      intro a ha k _bounded bs hb
      rw [collectStep,Experiment.all_map]
      exact (Experiment.all_worst (f a) weight).mono (fun c hc=>by
        have hc':=ht a ha
        simp only [weight_cons,Nat.add_mul,Nat.one_mul] at *
        omega))
    (by
      intro a ha k _bounded bs hb
      rw [collectStep_cost]
      have ha':=(weight_mem ha).trans hw
      have hc':=ht a ha
      have hmul:=Nat.mul_le_mul_right (M+1) hl
      rw [hD,hH]
      omega)
  have hout : (foldM (collectStep f) as []).All (fun bs=>weight bs≤H.eval M) :=
    hf.2.mono (fun bs hb=>by
      have hmul:=Nat.mul_le_mul_right (M+1) hl
      rw [hH];simp only [Nat.zero_mul,Nat.add_zero] at hb;omega)
  have hrev : (foldM (collectStep f) as []).worst TreeTyped.reverse.cost ≤ r.eval (H.eval M) := by
    apply Experiment.worst_le _ _ _
    exact hout.mono (fun bs hb=>(Nat.le_add_right _ _).trans
      ((hr bs).trans (polynomial_eval_monotone r hb)))
  have hfinal : (traverseM f as).worst weight≤H.eval M := by
    apply Experiment.worst_le _ _ _
    apply Experiment.all_of_mean_eq (p:=(foldM (collectStep f) as []).map List.reverse)
      (fun h=>by
        rw [Experiment.mean_map,mean_fold_collect]
        simp only [List.append_nil,List.reverse_reverse]) _
    rw [Experiment.all_map]
    exact hout.mono (fun bs hb=>by simpa only [weight_reverse] using hb)
  have hpre:=(hq as).trans (polynomial_eval_monotone q hw)
  dsimp only at hpre
  have hmul:=Nat.mul_le_mul_right (D.eval M+14*M+34) hl
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List B))).cost as+
    Fold.cost (collectStep f) (collectStepRealizer F).cost as []+
    (foldM (collectStep f) as []).worst TreeTyped.reverse.cost+(traverseM f as).worst weight≤_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

end MatchingFPRAS.OnlineTree

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineSampleCost
attribute [-instance] _root_.OAI.MatchingFPRAS.LiteralCodec.instCodecSymbol
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSample
open TreeTyped PhysicalStream Polynomial

variable {A B : Type} [Codec A] [Codec B]
lemma work_repeatInput : TreeTyped.WorkBound (repeatInputRealizer (A:=A)) (fun x=>x.1+weight x) := by
  unfold repeatInputRealizer
  apply TreeTyped.work_congr
  apply TreeTyped.work_then_polynomial _ (polynomial_mapWith polynomial_first)
  apply TreeTyped.work_pair _ _ X (by intro x; simp only [Polynomial.eval_X];omega)
  · exact TreeTyped.work_of_polynomial polynomial_second X (fun x=>by simp only [Polynomial.eval_X];omega)
  · apply TreeTyped.work_composition
      (TreeTyped.work_of_polynomial polynomial_first X (fun x=>by simp only [Polynomial.eval_X];omega))
      range_numeric_work X
    intro x
    simp only [Polynomial.eval_X,id_eq]
    omega

lemma weight_replicate (n : ℕ) (a : A) : weight (List.replicate n a)=n*(1+weight a)+1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ,weight_cons,ih,Nat.succ_mul];omega
end MatchingFPRAS.OnlineSample

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineStageCost
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample

lemma weight_le_stateSize (x : State) : weight x ≤ stateSize x := by unfold stateSize;omega
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_TreeHistorySize
attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction ExecutableScaling BitArithmetic

lemma fraction_weight_of_bound {B : ℕ} {q : ℚ} (h : FractionBound B (q:ℝ)) :
    TreeTyped.weight (TreeFraction.repr q)≤8*B.size+3 := by
  obtain ⟨hn,hd⟩:=h.num_den
  have hn':=Nat.size_le_size hn
  have hd':=Nat.size_le_size hd
  have h₁:=weight_nat_le q.num.natAbs
  have h₂:=weight_nat_le q.den
  simp only [TreeFraction.repr,weight_prod]
  omega

lemma vectorRep_weight_of_bound {n B : ℕ} (s : Fin n→ℚ)
    (h : ∀ i,FractionBound B (s i:ℝ)) :
    TreeTyped.weight (vectorRep s)≤n*(4*n.size+8*B.size+6)+1 := by
  have hb : ∀ i : Fin n,TreeTyped.weight (i.val,TreeFraction.repr (s i))≤4*n.size+8*B.size+5 := by
    intro i
    have h₁:=fraction_weight_of_bound (h i)
    have h₂:=weight_nat_le i.val
    have h₃:=Nat.size_le_size i.isLt.le
    simp only [weight_prod]
    omega
  unfold vectorRep
  rw [List.ofFn_eq_map]
  have hh:=weight_map_bound (as:=List.finRange n)
    (f:=fun i : Fin n=>(i.val,TreeFraction.repr (s i))) (N:=4*n.size+8*B.size+5)
    (fun i _=>hb i)
  simpa only [List.length_finRange] using hh

lemma history_vector_weight {G : GraphInput} [Nontrivial (Fin G.n)]
    (p : Trial.Parameters G) (j : ℕ) (hj : j≤p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    TreeTyped.weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)≤
      G.n*(4*G.n.size+8*((G.n+1).size+j*(G.n+1)*
        (19+(p.D+1).size+2*(p.S.size+
          Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1)+6)+1 := by
  have h:=vectorRep_weight_of_bound ((FiniteTrial.layers p j hj).state x).scale
    (FiniteTrial.layers_scale_bits p j hj x)
  have h₁:=size_scaleBound p j
  have h₂:=size_matrixBound p
  have h₃:=size_empiricalBound p
  have hb : (p.scaleBound j).size≤
      (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*(p.S.size+
        Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K)*(G.n+1).size+1))+1 := by
    calc
      _ ≤ (G.n+1).size+j*(G.n+1)*p.matrixBound.size+1 := h₁
      _ ≤ (G.n+1).size+j*(G.n+1)*(19+(p.D+1).size+2*p.empiricalBound.size)+1 := by gcongr
      _ ≤ _ := by gcongr
  exact h.trans (by gcongr)

end MatchingFPRAS.ExecutableSource

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_OnlineHistorySize
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped TreeFraction PhysicalStream ExecutableSource ExecutableScaling
open BitArithmetic Polynomial OnlineStage OnlineSchedule OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]

lemma product_bits (p : Trial.Parameters G) (j : ℕ) (hj : j ≤ p.K)
    (x : (FiniteTrial.layers p j hj).Ω) :
    FractionBound ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^j)
      (product p (FiniteTrial.layers p j hj) x : ℝ) := by
  have h := FractionBound.prod Finset.univ (fun i=>((FiniteTrial.layers p j hj).ratios x i : ℝ)) (p.empiricalBound^2)
    (fun i _=>FiniteTrial.layers_ratio_bits p j hj x i)
  simpa only [product,Rat.cast_mul,Rat.cast_natCast,Rat.cast_prod,Finset.card_univ,Fintype.card_fin] using
    (FractionBound.nat (Z (completeGraph G.n))).mul h

omit [Nontrivial (Fin G.n)] in
lemma sizeNorm_fields (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData) :
    G.n ≤ sizeNorm p g ∧ p.K ≤ sizeNorm p g ∧ p.N ≤ sizeNorm p g ∧ p.D ≤ sizeNorm p g ∧
    p.S ≤ sizeNorm p g ∧ p.T ≤ sizeNorm p g ∧ p.q ≤ sizeNorm p g ∧ weight g ≤ sizeNorm p g ∧
    (Z (completeGraph G.n)+1).size ≤ sizeNorm p g := by
  unfold sizeNorm;omega

lemma vector_weight_bound (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale) ≤ vectorPolynomial.eval (sizeNorm p g) := by
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have hn' := (Nat.size_le.mpr Nat.lt_two_pow_self : G.n.size ≤ G.n)
  have hn1 := (Nat.size_le.mpr Nat.lt_two_pow_self : (G.n+1).size ≤ G.n+1)
  have hd1 := (Nat.size_le.mpr Nat.lt_two_pow_self : (p.D+1).size ≤ p.D+1)
  have hs' := (Nat.size_le.mpr Nat.lt_two_pow_self : p.S.size ≤ p.S)
  have hv:=history_vector_weight p j hj x
  have hj' : j ≤ sizeNorm p g+1 := by omega
  simp only [vectorPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ (sizeNorm p g+1)*(4*(sizeNorm p g+1)+8*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)*
    (19+(sizeNorm p g+1)+2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1))+1)+6)+1
  apply hv.trans
  have hNN : Fintype.card (Enlargement.SourceVertex (Fin G.n) p.K) ≤ sizeNorm p g+1 := by
    change p.N ≤ _;omega
  gcongr <;> omega
lemma product_weight_bound (p : Trial.Parameters G) (g : ExecutableAdaptive.GraphData)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    weight (TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ productPolynomial.eval (sizeNorm p g) := by
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have he := size_empiricalBound p
  have hS:=(Nat.size_le.mpr Nat.lt_two_pow_self : p.S.size ≤ p.S)
  have hnn:=(Nat.size_le.mpr Nat.lt_two_pow_self : (G.n+1).size ≤ G.n+1)
  have he' : p.empiricalBound.size ≤ (sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1 := by
    apply he.trans
    change p.S.size+p.N*(G.n+1).size+1 ≤ _
    gcongr <;> omega
  have hp2:=size_pow_le p.empiricalBound 2
  have hpj:=size_pow_le (p.empiricalBound^2) j
  have hmul:=size_mul_le (Z (completeGraph G.n)+1) ((p.empiricalBound^2)^j)
  have hb : ((Z (completeGraph G.n)+1)*(p.empiricalBound^2)^j).size ≤
      (sizeNorm p g+1)+(sizeNorm p g+1)*(2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1)+1)+1 := by
    calc
      _ ≤ (Z (completeGraph G.n)+1).size+j*(2*p.empiricalBound.size+1)+1 := by
        have h:=Nat.mul_le_mul_left j hp2;omega
      _ ≤ _ := by gcongr <;> omega
  have hw:=fraction_weight_of_bound (product_bits p j hj x)
  simp only [productPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 8*((sizeNorm p g+1)+(sizeNorm p g+1)*(2*((sizeNorm p g+1)+(sizeNorm p g+1)*(sizeNorm p g+1)+1)+1)+1)+3
  omega

lemma data_weight (g : ExecutableAdaptive.GraphData) (j K D T Q : ℕ) (v : Vector) :
    weight ((((g,List.replicate j false),(((List.replicate (2*K+2) false,List.replicate (2*K) false),D),
      (List.replicate T false,List.replicate Q false))),v))=
      weight g+2*j+8*K+weight D+2*T+2*Q+weight v+16 := by
  simp only [weight_prod,weight_replicate,show weight false=1 from rfl]
  omega
lemma stateSize_mk (d : SparseStageData) (S : ℕ) (q : Fraction) :
    stateSize ((d,S),q)=d.1.2.1.2+S+3+2*weight d+2*weight S+weight q := by
  unfold stateSize requestSize
  simp only [weight_prod]
  omega
lemma state_weight_bound (f : OnlineGraph.Edges→OnlineGraph.Edges) (p : Trial.Parameters G)
    (j : ℕ) (hj : j ≤ p.K) (x : (FiniteTrial.layers p j hj).Ω) :
    stateSize (OnlineGraph.state f (represent p (FiniteTrial.layers p j hj) x)) ≤
      statePolynomial.eval (sizeNorm p (OnlineGraph.graph f (ExecutableAdaptive.graphRep G))) := by
  let g:=OnlineGraph.graph f (ExecutableAdaptive.graphRep G)
  obtain ⟨hn,hk,hN,hd,hs,ht,hq,hg,hz⟩:=sizeNorm_fields p g
  have hv:=vector_weight_bound p g j hj x
  have hp:=product_weight_bound p g j hj x
  have hD : FiniteTrial.sourceD (G:=G) p.K=p.D := FiniteTrial.sourceD_eq p.K
  have hT : tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)=p.T := by
    rw [hD];exact Transport.endpoint_eq p.N p.D p.K _
  have hQ : copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)=p.q := by rw [hD];rfl
  have hwd:=weight_nat_numeric p.D
  have hws:=weight_nat_numeric p.S
  change stateSize ((OnlineGraph.data f (fixedData p ((FiniteTrial.layers p j hj).state x)),p.S),
    TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ _
  rw [stateSize_mk]
  have hw : weight (OnlineGraph.data f (fixedData p ((FiniteTrial.layers p j hj).state x)))=
      weight g+2*j+8*p.K+weight p.D+2*p.T+2*p.q+
      weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)+16 := by
    change weight ((((g,List.replicate j false),(((List.replicate (2*p.K+2) false,List.replicate (2*p.K) false),
      FiniteTrial.sourceD (G:=G) p.K),(List.replicate (tierCount (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false,
        List.replicate (copies (n:=G.n) p.K (FiniteTrial.sourceD (G:=G) p.K)) false))),
      vectorRep ((FiniteTrial.layers p j hj).state x).scale))=_
    rw [data_weight,hT,hQ,hD]
  rw [hw]
  change FiniteTrial.sourceD (G:=G) p.K+p.S+3+2*(weight g+2*j+8*p.K+weight p.D+2*p.T+2*p.q+
    weight (vectorRep ((FiniteTrial.layers p j hj).state x).scale)+16)+2*weight p.S+
      weight (TreeFraction.repr (product p (FiniteTrial.layers p j hj) x)) ≤ statePolynomial.eval (sizeNorm p g)
  rw [hD]
  simp only [statePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
  omega
end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineHistoryCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma history_initial (f : Edges→Edges) (p : Trial.Parameters G) : History f p p.K (initial f p).2 := by
  exact ⟨0,by omega,PUnit.unit,by omega,rfl⟩
lemma history_size (f : Edges→Edges) (p : Trial.Parameters G) (k : ℕ) (s : State)
    (hs : History f p k s) : stateSize s≤ statePolynomial.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨j,hj,x,_,rfl⟩:=hs
  exact state_weight_bound f p j hj x

open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

end MatchingFPRAS.OnlineTrial

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Algorithm_AlgorithmLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open scoped Classical
open TreeTyped TreeFraction PhysicalStream LiteralInput

lemma empty_source (G : GraphInput) (ε δ : ℚ) : empty (parseInput (encodeInput G ε δ))=decide (G.n=0) := by
  rw [parseInput_source];rfl
lemma invalid_source (G : GraphInput) (ε δ : ℚ) : invalid (parseInput (encodeInput G ε δ))=
    (!(decide (G.n%2=0)) || decide (2*G.edges.card<G.n)) := by
  rw [parseInput_source]
  simp only [invalid,ExecutableInput.tooSparse,edgeNumbers_length]
lemma valid_even (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=false) : Even G.n := by
  rw [invalid_source] at h
  by_contra he
  have he' : ¬G.n%2=0 := fun hm=>he (Nat.even_iff.mpr hm)
  simp only [he',decide_false,Bool.not_false,Bool.true_or,Bool.true_eq_false] at h
lemma valid_size (G : GraphInput) (ε δ : ℚ) (h : invalid (parseInput (encodeInput G ε δ))=false) :
    G.n≤2*(encodeInput G ε δ).length := by
  rw [invalid_source] at h
  have hh : ¬2*G.edges.card<G.n := by
    intro hc
    simp only [hc,decide_true,Bool.or_true,Bool.true_eq_false] at h
  exact (show G.n≤2*G.edges.card by omega).trans (Nat.mul_le_mul_left 2 (edgeCard_le_input_length G ε δ))
lemma valid_two (G : GraphInput) (ε δ : ℚ) (he : empty (parseInput (encodeInput G ε δ))=false)
    (hi : invalid (parseInput (encodeInput G ε δ))=false) : 2≤G.n := by
  have h0 := of_decide_eq_false (show decide (G.n=0)=false by rwa [empty_source] at he)
  have hev:=Nat.even_iff.mp (valid_even G ε δ hi)
  omega

end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OnlineRunCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineSample

lemma initial_weight {G : GraphInput} [Nontrivial (Fin G.n)] (f : Edges→Edges) (p : Trial.Parameters G) :
    weight (initial f p) ≤ initialWeightPolynomial.eval (sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  have hs:=history_size f p p.K (initial f p).2 (history_initial f p)
  have hw:=weight_le_stateSize (initial f p).2
  have hk:=(sizeNorm_fields p (graph f (ExecutableAdaptive.graphRep G))).2.1
  rw [weight_prod]
  have hl : weight (initial f p).1=2*p.K+1 := by simp only [initial,weight_replicate,show weight false=1 from rfl];omega
  rw [hl]
  simp only [initialWeightPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega
end MatchingFPRAS.OnlineTrial

namespace MatchingFPRAS.OnlineAmplification
open TreeTyped PhysicalStream Polynomial OnlineGraph OnlineTrial OnlineSample

lemma run_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (f : Edges→Edges) (_hf : ∀ es e,e∈f es↔e∈es) (p : Trial.Parameters G) (r : ℕ),
    runRealizer.cost (r,OnlineTrial.initial f p)+(run (r,OnlineTrial.initial f p)).worst weight≤
      q.eval (r+sizeNorm p (graph f (ExecutableAdaptive.graphRep G))) := by
  obtain ⟨q,hq⟩:=OnlineGuard.trial_bound
  obtain ⟨s,hs⟩:=OnlineTree.traverse_bound OnlineGuard.trialRealizer
  obtain ⟨u,hu⟩:=work_repeatInput (A:=TrialInput)
  obtain ⟨v,hv⟩:=OnlineMedian.polynomial_median
  let I := initialWeightPolynomial
  let R : Polynomial ℕ := 5*X+2+I
  let B : Polynomial ℕ := X*(I+1)+1+q
  let T := u.comp R+s.comp B
  refine ⟨T+2*(v.comp T),?_⟩
  intro G inst f hf p r
  let n:=sizeNorm p (graph f (ExecutableAdaptive.graphRep G))
  let z:=r+n
  let x : TrialInput:=OnlineTrial.initial f p
  have hn:n≤z := by dsimp [z];omega
  have hr:r≤z := by dsimp [z];omega
  have hx : weight x≤I.eval z := (initial_weight f p).trans (polynomial_eval_monotone I hn)
  have hinput : r+weight (r,x) ≤R.eval z := by
    have hw:=weight_nat_numeric r
    simp only [weight_prod,R,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
    omega
  have hrep := (hu (r,x)).trans (polynomial_eval_monotone u hinput)
  have hwrep : weight (List.replicate r x)≤B.eval z := by
    rw [weight_replicate]
    simp only [B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one]
    nlinarith
  have ht : ∀ a∈List.replicate r x,OnlineGuard.trialRealizer.cost a+(OnlineGuard.trial a).worst weight≤B.eval z := by
    intro a ha
    have he: a=x := (List.mem_replicate.mp ha).2
    rw [he]
    exact ((hq G f hf p).trans (polynomial_eval_monotone q hn)).trans (by
      simp only [B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_one];omega)
  have htrav:=hs (List.replicate r x) (B.eval z) hwrep ht
  have htrial : trialsRealizer.cost (r,x)+(trials (r,x)).worst weight≤T.eval z := by
    change repeatInputRealizer.cost (r,x)+(OnlineTree.traverse OnlineGuard.trialRealizer).cost (List.replicate r x)+
      (OnlineTree.traverseM OnlineGuard.trial (List.replicate r x)).worst weight≤_
    simp only [T,Polynomial.eval_add,Polynomial.eval_comp]
    change repeatInputRealizer.cost (r,x)+weight (List.replicate r x)≤u.eval (R.eval z) at hrep
    omega
  have htail : (trials (r,x)).worst (fun as=>OnlineMedian.medianRealizer.cost as+weight (OnlineMedian.median as))≤v.eval (T.eval z) := by
    apply Experiment.worst_le _ _ _
    exact (Experiment.all_worst (trials (r,x)) weight).mono (fun as hw=>(hv as).trans
      (polynomial_eval_monotone v (hw.trans (by omega))))
  have hcost : (trials (r,x)).worst OnlineMedian.medianRealizer.cost≤v.eval (T.eval z) :=
    (Experiment.worst_mono _ _ _ ((Experiment.all_true _).mono (fun _ _=>Nat.le_add_right _ _))).trans htail
  have hout : (trials (r,x)).worst (weight ∘ OnlineMedian.median)≤v.eval (T.eval z) :=
    (Experiment.worst_mono _ _ _ ((Experiment.all_true _).mono (fun _ _=>Nat.le_add_left _ _))).trans htail

  have hboth : (trials (r,x)).worst OnlineMedian.medianRealizer.cost+
      (trials (r,x)).worst (weight ∘ OnlineMedian.median)≤2*v.eval (T.eval z) := by omega

  clear hcost hout htail
  change trialsRealizer.cost (r,x)+(trials (r,x)).worst OnlineMedian.medianRealizer.cost+
    (run (r,x)).worst weight≤_
  rw [run,Experiment.worst_map]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  change _ ≤ T.eval z+2*v.eval (T.eval z)
  omega
end MatchingFPRAS.OnlineAmplification

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Machines_OnlineBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSourceBounds
open BitComplexity Transport Polynomial TreeTyped

lemma normBound_polynomial : PolynomiallyBounded normBound := by
  have hn := (PolynomiallyBounded.const 2).mul PolynomiallyBounded.id
  exact ((((((((hn.add boundK_polynomial).add boundN_polynomial).add boundD_polynomial).add boundS_polynomial).add
    (tier_polynomial boundN_polynomial boundD_polynomial boundK_polynomial)).add
    (ladderQ_polynomial boundN_polynomial boundD_polynomial)).add (hn.pow 2)).add (PolynomiallyBounded.const 3))
lemma polynomial_bound {f : ℕ→ℕ} (h : PolynomiallyBounded f) :
    ∃ q : Polynomial ℕ,∀ x,1≤x→f x≤q.eval x := by
  obtain ⟨C,d,h⟩:=h
  exact ⟨Polynomial.C C*Polynomial.X^d,fun x hx=>by simpa using h x hx⟩
variable {G : GraphInput} [Nontrivial (Fin G.n)]
lemma norm_le (hn : 2≤G.n) (hev : Even G.n) (ε : ℚ) (he : 0<ε) (he1 : ε<1)
    (x : ℕ) (hnx : G.n≤2*x) (hex : ⌈ε⁻¹⌉₊≤x) (g : ExecutableAdaptive.GraphData) :
    OnlineTrial.sizeNorm (FiniteTrial.parameters G hn hev ε he he1) g≤normBound x+weight g := by
  let p:=FiniteTrial.parameters G hn hev ε he he1
  have hk:=parameters_K_le hn hev ε he he1 x hnx hex
  have hN:=parameters_N_le p x hnx hk
  have hD:=parameters_D_le p x hnx hN
  have hS:=parameters_S_le p x hnx hk hD hex
  have hT : p.T≤tierPolynomial (boundN x) (boundD x) (boundK x) := by
    have ht := endpoint_le_polynomial p.N p.D p.K p.N_pos
    rw [endpoint_eq] at ht
    apply ht.trans
    unfold tierPolynomial
    gcongr
  have hq : p.q≤ladderQ (boundN x) (boundD x) := by
    change ladderQ p.N p.D≤_
    unfold ladderQ ladderL
    gcongr
  have hz : (Z (completeGraph G.n)+1).size≤(2*x)^2+3 := by
    apply (BitArithmetic.complete_count_size G.n).trans
    have hs : G.n.size≤G.n := Nat.size_le.mpr Nat.lt_two_pow_self
    have hd : G.n/2≤G.n := Nat.div_le_self _ _
    calc
      _≤G.n*G.n+3 := by gcongr
      _≤(2*x)^2+3 := by rw [pow_two];gcongr
  unfold OnlineTrial.sizeNorm normBound
  dsimp only [p] at *
  omega

lemma numeric_le (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1)
    (x : ℕ) (hnx : G.n≤2*x) (hex : ⌈ε⁻¹⌉₊≤x) :
    OnlineInitial.configNumeric (OnlineInitial.config (OnlineInitial.sourceSeed (G:=G) ε δ))≤normBound x := by
  let p:=FiniteTrial.parameters G hn hev ε he he1
  rw [OnlineInitial.config_source hn hev ε δ he he1]
  dsimp only [OnlineInitial.configNumeric,OnlineInitial.sourceSeed]
  have hl : (ExecutableAdaptive.graphRep G).1.length=G.n := by simp [ExecutableAdaptive.graphRep]
  rw [hl,OnlineSchedule.ladderSchedule_eq _ _ _ p.N_pos,endpoint_eq,FiniteTrial.sourceD_eq]
  have hs:=norm_le hn hev ε he he1 x hnx hex (ExecutableAdaptive.graphRep G)
  unfold OnlineTrial.sizeNorm at hs
  change G.n+p.K+p.N+p.D+p.T+p.q≤normBound x
  dsimp only [p] at *
  omega
end MatchingFPRAS.OnlineSourceBounds

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_ComputeCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream Polynomial OnlineSourceBounds LiteralInput

lemma initialize_materialize {G : GraphInput} [Nontrivial (Fin G.n)]
    (hn : 2≤G.n) (hev : Even G.n) (ε δ : ℚ) (he : 0<ε) (he1 : ε<1) (hd : 0≤δ) :
    OnlineInitial.initializeInput (materialize (parseInput (encodeInput G ε δ)))=
      (2*Amplification.halfRepetitions δ+1,
        OnlineTrial.initial (reorder G) (FiniteTrial.parameters G hn hev ε he he1)) := by
  rw [materialize_source,OnlineGraph.initialize_eq,
    OnlineInitial.initializeInput_source hn hev ε δ he he1 hd]
  rfl
lemma numeric_materialize (G : GraphInput) (ε δ : ℚ) :
    OnlineInitial.configNumeric (OnlineInitial.config (materialize (parseInput (encodeInput G ε δ))))=
      OnlineInitial.configNumeric (OnlineInitial.config (OnlineInitial.sourceSeed (G:=G) ε δ)) := by
  rw [materialize_source]
  rfl
lemma materialize_vertices (G : GraphInput) (ε δ : ℚ) :
    (materialize (parseInput (encodeInput G ε δ))).1.1.length=G.n := by
  rw [LiteralInput.parseInput_source];simp only [materialize,List.length_range]
lemma materialize_epsilon (G : GraphInput) (ε δ : ℚ) :
    (materialize (parseInput (encodeInput G ε δ))).2.1=TreeFraction.repr ε := by
  rw [LiteralInput.parseInput_source];rfl
lemma graph_weight_materialize (G : GraphInput) (ε δ : ℚ) :
    weight (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))≤
      weight (materialize (parseInput (encodeInput G ε δ))) := by
  rw [materialize_source]
  change weight _≤weight (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G),_)
  rw [weight_prod (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))]
  omega

lemma compute_cost (a : Parsed) : computeRealizer.cost a=
    materializeRealizer.cost a+OnlineInitial.initializeInputRealizer.cost (materialize a)+
      OnlineAmplification.runRealizer.cost (OnlineInitial.initializeInput (materialize a)) := rfl

lemma compute_bound : ∃ q : Polynomial ℕ,∀ (G : GraphInput) [Nontrivial (Fin G.n)]
    (_hn : 2≤G.n) (_hev : Even G.n) (ε δ : ℚ) (_he : 0<ε) (_he1 : ε<1) (_hd : 0≤δ)
    (x : ℕ),1≤x→G.n≤x→⌈ε⁻¹⌉₊≤x→Nat.clog 2 ⌈δ⁻¹⌉₊≤x→
    weight (parseInput (encodeInput G ε δ))≤x→
    computeRealizer.cost (parseInput (encodeInput G ε δ))+
      (compute (parseInput (encodeInput G ε δ))).worst weight≤q.eval x := by
  obtain ⟨m,hm⟩:=work_materialize
  obtain ⟨i,hi⟩:=OnlineInitial.work_initializeInput
  obtain ⟨r,hr⟩:=OnlineAmplification.run_bound
  obtain ⟨b,hb⟩:=polynomial_bound normBound_polynomial
  let M:=m.comp (2*X)
  let S:Polynomial ℕ:=2*X+b+M
  let R:Polynomial ℕ:=11*X+11+b+M
  refine ⟨M+i.comp S+r.comp R,?_⟩
  intro G inst hn hev ε δ he he1 hd x hx hnx hex hdx hwx
  let a:=parseInput (encodeInput G ε δ)
  let seed:=materialize a
  let p:=FiniteTrial.parameters G hn hev ε he he1
  have hn2:G.n≤2*x := by omega
  have ha:a.1=G.n := by dsimp only [a];rw [LiteralInput.parseInput_source]
  have hmat:materializeRealizer.cost a+weight seed≤M.eval x := by
    apply (hm a).trans
    apply (polynomial_eval_monotone m (show a.1+weight a≤2*x by dsimp only [a] at *;omega)).trans
    simp only [M,Polynomial.eval_comp,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X];rfl
  have hseed:OnlineInitial.seedSize seed≤S.eval x := by
    have hnum:OnlineInitial.configNumeric (OnlineInitial.config seed)≤b.eval x := by
      dsimp only [seed,a]
      rw [numeric_materialize]
      exact (numeric_le hn hev ε δ he he1 x hn2 hex).trans (hb x hx)
    have hlen:(seed.1.1).length=G.n:=materialize_vertices G ε δ
    have hep:natCeil (inverse seed.2.1)=⌈ε⁻¹⌉₊ := by
      rw [show seed.2.1=TreeFraction.repr ε from materialize_epsilon G ε δ,inverse_repr ε he.le,natCeil_repr _ (inv_nonneg.mpr he.le)]
    simp only [OnlineInitial.seedSize,hlen,hep,S,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have hini:OnlineInitial.initializeInputRealizer.cost seed ≤ i.eval (S.eval x) :=
    (Nat.le_trans (Nat.le_add_right _ _) (hi seed)).trans (polynomial_eval_monotone i hseed)
  have hnorm:OnlineTrial.sizeNorm p (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))≤b.eval x+M.eval x := by
    apply (norm_le hn hev ε he he1 x hn2 hex _).trans
    have hg:=graph_weight_materialize G ε δ
    have hnb:=hb x hx
    dsimp only [seed,a] at hmat
    omega
  have hrep:2*Amplification.halfRepetitions δ+1≤10*x+11:=by
    rw [Amplification.repetitions_source];omega
  have harg:2*Amplification.halfRepetitions δ+1+
      OnlineTrial.sizeNorm p (OnlineGraph.graph (reorder G) (ExecutableAdaptive.graphRep G))≤R.eval x := by
    simp only [R,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega
  have hrun:= (hr G (reorder G) (reorder_mem G) p (2*Amplification.halfRepetitions δ+1)).trans
    (polynomial_eval_monotone r harg)
  have hinput:=initialize_materialize hn hev ε δ he he1 hd
  rw [compute_cost]
  unfold compute
  rw [hinput]
  simp only [Polynomial.eval_add,Polynomial.eval_comp]
  dsimp only [a,seed,p] at hini hmat hrun
  omega
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

section
-- module Solutions.OAIQ051_MC.MatchingCount_Complexity_OriginalCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.LiteralAlgorithm
open TreeTyped TreeFraction PhysicalStream LiteralInput Polynomial

lemma count_cost (a : Parsed) : countRealizer.cost a=
    (pair emptyRealizer identity).cost a+
      (if empty a then (constant ((1,1) : Fraction)).cost a else
        (pair invalidRealizer identity).cost a+
          (if invalid a then (constant ((0,1) : Fraction)).cost a else computeRealizer.cost a)+30)+30 := by
  simp only [countRealizer,OnlineTree.Realizer.congr,OnlineTree.conditional,
    OnlineTree.composition,OnlineTree.deterministic,Experiment.worst,OnlineTree.caseBool,id_eq]
  split <;> omega
lemma algorithm_cost (as : List Symbol) : algorithmRealizer.cost as=
    parseInputRealizer.cost as+countRealizer.cost (parseInput as)+
      (count (parseInput as)).worst LiteralCodec.ratWordRealizer.cost := rfl
lemma algorithm_bound_oai : ∃ q : Polynomial ℕ,∀ (G : GraphInput) (ε δ : ℚ)
    (_he : 0<ε) (_he1 : ε<1) (_hd : 0≤δ) (x : ℕ),1≤x→
    (encodeInput G ε δ).length≤x→⌈ε⁻¹⌉₊≤x→Nat.clog 2 ⌈δ⁻¹⌉₊≤x→
    algorithmRealizer.cost (encodeInput G ε δ)+(algorithm (encodeInput G ε δ)).worst weight≤q.eval x := by
  obtain ⟨p,hp⟩:=polynomial_parseInput
  obtain ⟨e,he⟩:=polynomial_pair polynomial_empty polynomial_identity
  obtain ⟨j,hj⟩:=polynomial_pair polynomial_invalid polynomial_identity
  obtain ⟨c,hc⟩:=polynomial_constant ((1,1) : Fraction) (A:=Parsed)
  obtain ⟨d,hd⟩:=polynomial_constant ((0,1) : Fraction) (A:=Parsed)
  obtain ⟨k,hk⟩:=compute_bound
  obtain ⟨v,hv⟩:=LiteralCodec.polynomial_ratWord
  let P:=p.comp (18*X+1)
  let B:Polynomial ℕ:=2*X+P+1
  let Q:=e.comp P+j.comp P+c.comp P+d.comp P+k.comp B+60
  refine ⟨P+Q+2*(v.comp Q),?_⟩
  intro G ε δ hε hε1 hδ x hx hl hεx hδx
  let as:=encodeInput G ε δ
  let a:=parseInput as
  have hparse : parseInputRealizer.cost as+weight a≤P.eval x := by
    apply (hp as).trans
    rw [LiteralCodec.weight_word]
    simpa only [P,Polynomial.eval_comp,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one] using
      polynomial_eval_monotone p (show 18*as.length+1≤18*x+1 by dsimp only [as];omega)
  have hwa : weight a≤P.eval x := by omega
  have hep : (pair emptyRealizer identity).cost a≤e.eval (P.eval x) :=
    (Nat.le_add_right _ _).trans ((he a).trans (polynomial_eval_monotone e hwa))
  have hjp : (pair invalidRealizer identity).cost a≤j.eval (P.eval x) :=
    (Nat.le_add_right _ _).trans ((hj a).trans (polynomial_eval_monotone j hwa))
  have hcp : (constant ((1,1) : Fraction)).cost a+weight ((1,1) : Fraction) ≤ c.eval (P.eval x) :=
    (hc a).trans (polynomial_eval_monotone c hwa)
  have hdp : (constant ((0,1) : Fraction)).cost a+weight ((0,1) : Fraction)≤d.eval (P.eval x) :=
    (hd a).trans (polynomial_eval_monotone d hwa)
  have hb : x≤B.eval x ∧ 2*x≤B.eval x ∧ P.eval x≤B.eval x := by
    simp only [B,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one]
    omega
  have hcount : countRealizer.cost a+(count a).worst weight≤Q.eval x := by
    cases hE:empty a with
    | true =>
      rw [count_cost]
      simp only [count,hE,ite_true,Experiment.worst,Q,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_ofNat]
      omega
    | false =>
      cases hI:invalid a with
      | true =>
        rw [count_cost]
        simp only [count,hE,hI,Bool.false_eq_true,ite_false,ite_true,Experiment.worst,Q,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_ofNat]
        omega
      | false =>
        have hn:=valid_two G ε δ hE hI
        have hev:=valid_even G ε δ hI
        let : Nontrivial (Fin G.n):=Fin.nontrivial_iff_two_le.mpr hn
        have hnx : G.n≤B.eval x := (valid_size G ε δ hI).trans ((Nat.mul_le_mul_left 2 hl).trans hb.2.1)
        have hcompute:=hk G hn hev ε δ hε hε1 hδ (B.eval x) (hx.trans hb.1) hnx (hεx.trans hb.1) (hδx.trans hb.1) (hwa.trans hb.2.2)
        rw [count_cost]
        simp only [count,hE,hI,Bool.false_eq_true,ite_false,Q,Polynomial.eval_add,Polynomial.eval_comp,Polynomial.eval_ofNat]
        dsimp only [as,a] at *
        omega
  have hout : (count a).All (fun z=>LiteralCodec.ratWordRealizer.cost z+weight (LiteralCodec.ratWord z)≤v.eval (Q.eval x)) :=
    (Experiment.all_worst (count a) weight).mono (fun z hz=>(hv z).trans
      (polynomial_eval_monotone v (hz.trans (by omega))))
  have htail : (count a).worst LiteralCodec.ratWordRealizer.cost≤v.eval (Q.eval x) :=
    Experiment.worst_le _ _ _ (hout.mono (fun z hz=>(Nat.le_add_right _ _).trans hz))
  have hword : (count a).worst (weight ∘ LiteralCodec.ratWord)≤v.eval (Q.eval x) :=
    Experiment.worst_le _ _ _ (hout.mono (fun z hz=>(Nat.le_add_left _ _).trans hz))
  rw [algorithm_cost]
  unfold algorithm
  rw [Experiment.worst_map]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_comp]
  dsimp only [a,as] at *
  omega
end MatchingFPRAS.LiteralAlgorithm

end OAI
end

theorem solution : type_of% @OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound_oai := @OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound_oai
