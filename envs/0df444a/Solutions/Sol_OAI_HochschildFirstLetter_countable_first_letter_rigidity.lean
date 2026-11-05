-- Prove2me | solution 1 for OAI.HochschildFirstLetter.countable_first_letter_rigidity
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T14:44:44.174355+00:00
-- url     : https://prove2.me/submissions/a4f350a1-0d6e-4722-96bf-d5f573a9a3f2

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

set_option Elab.async false
set_option linter.all false

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildCatalanWords
noncomputable section
open List BinaryTree
variable {α : Type*}

def word : BinaryTree α → List α
  | .nil => []
  | .node a l r => a :: (word l ++ a :: word r)

@[simp] lemma length_word (t : BinaryTree α) : (word t).length = 2*t.numNodes := by
  induction t with
  | nil => simp [word]
  | node a l r hl hr => simp [word, hl, hr]; omega

def unorientedReduce [DecidableEq α] : List α → List α
  | [] => []
  | a::l => match unorientedReduce l with
    | [] => [a]
    | b::k => if a=b then k else a::b::k

def signed : Bool → List α → List (α × Bool)
  | _, [] => []
  | b, a::l => (a,b)::signed (!b) l

@[simp] lemma signed_eq_nil (b : Bool) (l : List α) : signed b l = [] ↔ l = [] := by
  cases l <;> simp [signed]

lemma reduce_signed [DecidableEq α] (b : Bool) (l : List α) :
    FreeGroup.reduce (signed b l) = signed b (unorientedReduce l) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
    simp only [signed, FreeGroup.reduce.cons, ih, unorientedReduce]
    cases h : unorientedReduce l with
    | nil => simp [signed]
    | cons c l =>
      simp only [signed]
      by_cases hac : a=c
      · simp [hac, Bool.not_not]
      · simp [hac, signed]

def render (p : BinaryTree α × List (α × BinaryTree α)) : List α :=
  word p.1 ++ p.2.flatMap (fun p => p.1 :: word p.2)

def parse [DecidableEq α] : List α → BinaryTree α × List (α × BinaryTree α)
  | [] => (.nil, [])
  | a::l => match parse l with
    | (t,[]) => (.nil,[(a,t)])
    | (t,(b,u)::xs) => if a=b then (.node a t u,xs) else (.nil,(a,t)::(b,u)::xs)

lemma render_parse [DecidableEq α] (l : List α) : render (parse l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [parse]
    cases hp : parse l with
    | mk t xs =>
      rw [hp] at ih
      cases xs with
      | nil => simpa [render, word] using congrArg (a :: ·) ih
      | cons p xs =>
        rcases p with ⟨b,u⟩
        by_cases hab : a=b
        · simp only [hab]
          simpa [render, word, List.append_assoc] using congrArg (b :: ·) ih
        · simp only [hab, ite_false]
          simpa [render, word, List.append_assoc] using congrArg (a :: ·) ih

lemma unmatched_parse [DecidableEq α] (l : List α) :
    (parse l).2.map Prod.fst = unorientedReduce l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [parse, unorientedReduce, ← ih]
    cases hp : parse l with
    | mk t xs =>
      cases xs with
      | nil => rfl
      | cons p xs =>
        rcases p with ⟨b,u⟩
        by_cases hab : a=b <;> simp [hab]

theorem exists_tree_of_reduce_signed_eq_nil [DecidableEq α]
    (l : List α) (b : Bool) (hl : FreeGroup.reduce (signed b l) = []) :
    ∃ t : BinaryTree α, word t = l := by
  rw [reduce_signed, signed_eq_nil] at hl
  have h := unmatched_parse l
  rw [hl, List.map_eq_nil_iff] at h
  refine ⟨(parse l).1, ?_⟩
  have hp := render_parse l
  simpa only [render, h, flatMap_nil, append_nil] using hp

lemma signed_append_even {l : List α} (hl : 2 ∣ l.length) (k : List α) (b : Bool) :
    signed b (l++k) = signed b l ++ signed b k := by
  induction l using List.twoStepInduction generalizing b with
  | nil => simp [signed]
  | singleton a => simp at hl
  | cons_cons a c l ih _ =>
    have hl' : 2 ∣ l.length := by simpa using hl
    simpa [signed] using congrArg ((a,b) :: (c,!b) :: ·) (ih hl' b)

lemma signed_word_node (a : α) (l r : BinaryTree α) (b : Bool) :
    signed b (word (.node a l r)) =
      (a,b) :: (signed (!b) (word l) ++ (a,!b) :: signed b (word r)) := by
  simp only [word, signed]
  rw [signed_append_even (by simp)]; simp [signed]

lemma reduce_signed_word [DecidableEq α] (t : BinaryTree α) (b : Bool) :
    FreeGroup.reduce (signed b (word t)) = [] := by
  induction t generalizing b with
  | nil => simp [word, signed]
  | node a l r hl hr =>
    rw [signed_word_node]
    have happ : FreeGroup.reduce (signed (!b) (word l) ++ (a,!b) :: signed b (word r)) =
        [(a,!b)] := by
      rw [← FreeGroup.reduce_append_reduce_reduce, hl]
      simp [FreeGroup.reduce.cons, hr]
    simp only [FreeGroup.reduce.cons, happ, Bool.not_not, and_self, ite_true]

def labels : BinaryTree α → List α
  | .nil => []
  | .node a l r => a :: (labels l ++ labels r)

@[simp] lemma length_labels (t : BinaryTree α) : (labels t).length = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [labels, hl, hr]

@[simp] lemma mem_word_iff (a : α) (t : BinaryTree α) : a ∈ word t ↔ a ∈ labels t := by
  induction t with
  | nil => rfl
  | node b l r hl hr => simp [word, labels, hl, hr, or_left_comm]

lemma delimiter_split {a : α} {l r l' r' : List α}
    (hl : a ∉ l) (hl' : a ∉ l') (he : l ++ a::r = l' ++ a::r') :
    l=l' ∧ r=r' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simpa using he
    | cons b l' =>
      have hab : a=b := List.head_eq_of_cons_eq he
      subst b
      simp at hl'
  | cons b l ih =>
    cases l' with
    | nil =>
      have hba : b=a := List.head_eq_of_cons_eq he
      subst b
      simp at hl
    | cons c l' =>
      have hbc : b=c := List.head_eq_of_cons_eq he
      subst c
      have he' := List.tail_eq_of_cons_eq he
      obtain ⟨rfl, rfl⟩ := ih (by simpa using fun h => hl (List.mem_cons_of_mem _ h))
        (by simpa using fun h => hl' (List.mem_cons_of_mem _ h)) he'
      exact ⟨rfl,rfl⟩

theorem word_injective_on_nodup {t u : BinaryTree α}
    (ht : (labels t).Nodup) (hu : (labels u).Nodup) (he : word t = word u) : t=u := by
  induction t generalizing u with
  | nil =>
    cases u with
    | nil => rfl
    | node b l r => simp [word] at he
  | node a l r ihl ihr =>
    cases u with
    | nil => simp [word] at he
    | node b l' r' =>
      simp only [word, List.cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      have ht' := List.nodup_cons.mp ht
      have hu' := List.nodup_cons.mp hu
      have htl := List.nodup_append.mp ht'.2
      have hul := List.nodup_append.mp hu'.2
      obtain ⟨hel, her⟩ := delimiter_split
        (fun h => ht'.1 (List.mem_append_left _ ((mem_word_iff _ _).mp h)))
        (fun h => hu'.1 (List.mem_append_left _ ((mem_word_iff _ _).mp h))) he
      rw [ihl htl.1 hul.1 hel, ihr htl.2.1 hul.2.1 her]

def shape : BinaryTree α → BinaryTree Unit := BinaryTree.map (fun _ => ())

@[simp] lemma numNodes_shape (t : BinaryTree α) : (shape t).numNodes = t.numNodes := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simpa [shape, BinaryTree.map] using congrArg₂ (fun x y=> x+y) hl hr

def decorate : BinaryTree Unit → List α → BinaryTree α
  | .nil, _ => .nil
  | .node _ _ _, [] => .nil
  | .node _ l r, a::as => .node a (decorate l (as.take l.numNodes))
      (decorate r (as.drop l.numNodes))

lemma decorate_spec (t : BinaryTree Unit) (as : List α) (h : as.length=t.numNodes) :
    shape (decorate t as) = t ∧ labels (decorate t as) = as := by
  induction t generalizing as with
  | nil => simp only [BinaryTree.numNodes] at h; have := List.length_eq_zero_iff.mp h
           subst as; exact ⟨rfl,rfl⟩
  | node a l r hl hr =>
    cases a
    cases as with
    | nil => simp at h
    | cons a as =>
      have llen : l.numNodes ≤ as.length := by simp at h; omega
      obtain ⟨hls,hll⟩ := hl (as.take l.numNodes) (by simp [llen])
      obtain ⟨hrs,hrl⟩ := hr (as.drop l.numNodes) (by simp; simp at h; omega)
      constructor
      · simp only [decorate, shape, BinaryTree.map]
        change BinaryTree.node () (shape _) (shape _) = _
        rw [hls, hrs]
      · simp only [decorate, labels, hll, hrl, List.take_append_drop]

lemma decorate_shape_labels (t : BinaryTree α) : decorate (shape t) (labels t) = t := by
  induction t with
  | nil => rfl
  | node a l r hl hr =>
    change BinaryTree.node a (decorate (shape l) ((labels l ++ labels r).take (shape l).numNodes))
      (decorate (shape r) ((labels l ++ labels r).drop (shape l).numNodes)) = _
    rw [numNodes_shape, ← length_labels, List.take_left, List.drop_left, hl, hr]

abbrev Shapes (n : ℕ) := ↥(BinaryTree.treesOfNumNodesEq n)

@[simp] lemma card_shapes (n : ℕ) : Fintype.card (Shapes n) = catalan n := by
  rw [Fintype.card_coe, treesOfNumNodesEq_card_eq_catalan]

@[simp] lemma nodes_shape (n : ℕ) (t : Shapes n) : t.val.numNodes = n :=
  BinaryTree.mem_treesOfNumNodesEq.mp t.property

def listFunction {n : ℕ} (l : List α) (h : l.length=n) : Fin n → α :=
  fun i => l.get (i.cast h.symm)

@[simp] lemma ofFn_listFunction {n : ℕ} (l : List α) (h : l.length=n) :
    List.ofFn (listFunction l h) = l := by
  subst n
  exact List.ofFn_get l

abbrev ReturnWords (α : Type*) [DecidableEq α] (n : ℕ) :=
  {f : Fin (2*n) → α // FreeGroup.reduce (signed false (List.ofFn f)) = []}

def treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) : BinaryTree α :=
  decorate t.val (List.ofFn f)

@[simp] lemma shape_treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) :
    shape (treeFrom t f) = t.val :=
  (decorate_spec _ _ (by simp)).1

@[simp] lemma labels_treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) :
    labels (treeFrom t f) = List.ofFn f :=
  (decorate_spec _ _ (by simp)).2

@[simp] lemma nodes_treeFrom {n : ℕ} (t : Shapes n) (f : Fin n → α) :
    (treeFrom t f).numNodes = n := by
  rw [← numNodes_shape, shape_treeFrom, nodes_shape]

variable [DecidableEq α]

def fromTree {n : ℕ} (p : Shapes n × (Fin n → α)) : ReturnWords α n :=
  ⟨listFunction (word (treeFrom p.1 p.2)) (by simp), by
    rw [ofFn_listFunction]; exact reduce_signed_word _ _⟩

@[simp] lemma ofFn_fromTree {n : ℕ} (p : Shapes n × (Fin n → α)) :
    List.ofFn (fromTree p).val = word (treeFrom p.1 p.2) := by
  exact ofFn_listFunction _ (by simp)

lemma fromTree_surjective (n : ℕ) : Function.Surjective (@fromTree α _ n) := by
  intro f
  obtain ⟨t,ht⟩ := exists_tree_of_reduce_signed_eq_nil _ _ f.property
  have hn : t.numNodes = n := by
    have h := congrArg List.length ht
    simp only [length_word, List.length_ofFn] at h
    omega
  let s : Shapes n := ⟨shape t, by simp [hn]⟩
  let g : Fin n → α := listFunction (labels t) (by simp [hn])
  refine ⟨(s,g), Subtype.ext ?_⟩
  apply List.ofFn_injective
  rw [ofFn_fromTree]
  change word (decorate (shape t) (List.ofFn g)) = List.ofFn f.val
  rw [ofFn_listFunction, decorate_shape_labels, ht]

def fromDistinctTree {n : ℕ} (p : Shapes n × (Fin n ↪ α)) : ReturnWords α n :=
  fromTree (p.1, p.2)

lemma fromDistinctTree_injective (n : ℕ) :
    Function.Injective (@fromDistinctTree α _ n) := by
  rintro ⟨s,f⟩ ⟨t,g⟩ h
  have hw : word (treeFrom s f) = word (treeFrom t g) := by
    have h' := congrArg (fun x : ReturnWords α n => List.ofFn x.val) h
    simpa only [fromDistinctTree, ofFn_fromTree] using h'
  have he := word_injective_on_nodup
    (by rw [labels_treeFrom]; exact List.nodup_ofFn_ofInjective f.injective)
    (by rw [labels_treeFrom]; exact List.nodup_ofFn_ofInjective g.injective) hw
  have hs : s=t := Subtype.ext (by simpa only [shape_treeFrom] using congrArg shape he)
  have hf : f=g := by
    apply DFunLike.ext
    intro i
    have hh : (f : Fin n → α) = g := List.ofFn_injective
      (by simpa only [labels_treeFrom] using congrArg labels he)
    exact congrFun hh i
  subst t; subst g; rfl

theorem returnWord_count_bounds [Fintype α] (n : ℕ) :
    catalan n * (Fintype.card α).descFactorial n ≤ Fintype.card (ReturnWords α n) ∧
    Fintype.card (ReturnWords α n) ≤ catalan n * (Fintype.card α)^n := by
  constructor
  · have h := Fintype.card_le_of_injective _ (fromDistinctTree_injective (α:=α) n)
    simpa only [Fintype.card_prod, card_shapes, Fintype.card_embedding_eq,
      Fintype.card_fin] using h
  · have h := Fintype.card_le_of_surjective _ (fromTree_surjective (α:=α) n)
    simpa only [Fintype.card_prod, card_shapes, Fintype.card_fun, Fintype.card_fin] using h

open Filter Topology Asymptotics in

theorem normalized_returnWord_count_tendsto (n : ℕ) :
    Tendsto (fun r : ℕ => (Fintype.card (ReturnWords (Fin r) n) : ℝ) / (r:ℝ)^n)
      atTop (𝓝 (catalan n : ℝ)) := by
  have hz : ∀ᶠ r : ℕ in atTop, (r:ℝ)^n ≠ 0 := by
    filter_upwards [eventually_ge_atTop 1] with r hr
    exact pow_ne_zero _ (by exact_mod_cast (show r≠0 by omega))
  have hd := (isEquivalent_iff_tendsto_one hz).mp (isEquivalent_descFactorial n)
  have hlo : Tendsto (fun r : ℕ => (catalan n : ℝ) * (r.descFactorial n : ℝ) / (r:ℝ)^n)
      atTop (𝓝 (catalan n : ℝ)) := by
    simpa only [Pi.div_apply, mul_one, mul_div_assoc] using hd.const_mul (catalan n : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds ?_ ?_
  · exact Filter.Eventually.of_forall fun r => by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast (by simpa only [Fintype.card_fin] using
        (returnWord_count_bounds (α:=Fin r) n).1 :
        catalan n * r.descFactorial n ≤ Fintype.card (ReturnWords (Fin r) n))
  · filter_upwards [hz] with r hr
    rw [div_le_iff₀ (lt_of_le_of_ne (by positivity) (Ne.symm hr))]
    exact_mod_cast (by simpa only [Fintype.card_fin] using
      (returnWord_count_bounds (α:=Fin r) n).2 :
      Fintype.card (ReturnWords (Fin r) n) ≤ catalan n * r^n)

end
end HochschildCatalanWords

namespace HochschildCatalanMoments
open HochschildCatalanWords Finset
noncomputable section
variable {α A : Type*} [Fintype α] [Ring A]
variable (u : FreeGroup α →* A)

def signedSum (b : Bool) (n : ℕ) : A :=
  ∑ f : Fin n → α, u (FreeGroup.mk (signed b (List.ofFn f)))

lemma signedSum_succ (b : Bool) (n : ℕ) :
    signedSum u b (n+1) = (∑ a : α, u (FreeGroup.mk [(a,b)])) * signedSum u (!b) n := by
  unfold signedSum
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => α)).sum_comp, Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, signed]
  change u (FreeGroup.mk ([(a,b)] ++ signed (!b) (List.ofFn f))) = _
  rw [← FreeGroup.mul_mk, map_mul]

@[simp] lemma signedSum_zero (b : Bool) : signedSum u b 0 = 1 := by
  simp [signedSum, signed, ← FreeGroup.one_eq_mk]

lemma signedSum_even (n : ℕ) :
    signedSum u false (2*n) =
      ((∑ a : α, u (FreeGroup.mk [(a,false)])) * (∑ a : α, u (FreeGroup.of a)))^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1) = (2*n+1)+1 by omega, signedSum_succ, signedSum_succ]
    simp only [Bool.not_false, Bool.not_true, ih, pow_succ']
    change (∑ a : α, u (FreeGroup.mk [(a,false)])) *
      ((∑ a : α, u (FreeGroup.of a)) *
        ((∑ a : α, u (FreeGroup.mk [(a,false)])) * (∑ a : α, u (FreeGroup.of a)))^n) = _
    exact (mul_assoc _ _ _).symm

variable [StarRing A] (hu : ∀ g, star (u g) = u g⁻¹)
include hu

lemma sum_star : (∑ a : α, u (FreeGroup.mk [(a,false)])) = star (∑ a : α, u (FreeGroup.of a)) := by
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [hu]
  rfl

lemma sum_pow_expansion (n : ℕ) :
    (star (∑ a : α, u (FreeGroup.of a)) * (∑ a : α, u (FreeGroup.of a)))^n =
      signedSum u false (2*n) := by
  rw [signedSum_even, sum_star u hu]

variable [DecidableEq α] [Algebra ℂ A] (τ : A →ₗ[ℂ] ℂ) (hτ : τ 1 = 1)
  (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)

omit hu [Fintype α] [StarRing A] in
include hτ hfree in
lemma trace_word (l : List (α × Bool)) :
    τ (u (FreeGroup.mk l)) = if FreeGroup.reduce l = [] then 1 else 0 := by
  have he : FreeGroup.reduce l = [] ↔ FreeGroup.mk l = 1 :=
    by simpa only [FreeGroup.toWord_mk] using
      (@FreeGroup.toWord_eq_nil_iff α _ (FreeGroup.mk l))
  by_cases h : FreeGroup.reduce l = []
  · simp [h, he.mp h, hτ]
  · rw [ite_eq_right h]
    exact hfree _ (fun hg => h (he.mpr hg))

include hτ hfree in
lemma trace_sum_pow (n : ℕ) :
    τ ((star (∑ a : α, u (FreeGroup.of a)) * (∑ a : α, u (FreeGroup.of a)))^n) =
      (Fintype.card (ReturnWords α n) : ℂ) := by
  rw [sum_pow_expansion u hu, signedSum, map_sum]
  simp only [trace_word u τ hτ hfree]
  simp [Fintype.card_subtype, ReturnWords]

def positiveSum : A := (Fintype.card α : ℂ)⁻¹ •
  (star (∑ a : α, u (FreeGroup.of a)) * (∑ a : α, u (FreeGroup.of a)))

include hτ hfree in
lemma trace_positiveSum_pow (n : ℕ) :
    τ ((positiveSum u)^n) =
      (Fintype.card (ReturnWords α n) : ℂ) / (Fintype.card α : ℂ)^n := by
  rw [positiveSum, smul_pow, map_smul, trace_sum_pow u hu τ hτ hfree]
  simp only [smul_eq_mul, inv_pow, div_eq_mul_inv, mul_comm]

include hτ hfree in
lemma re_trace_positiveSum_pow (n : ℕ) :
    (τ ((positiveSum u)^n)).re =
      (Fintype.card (ReturnWords α n) : ℝ) / (Fintype.card α : ℝ)^n := by
  rw [trace_positiveSum_pow u hu τ hτ hfree]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_div, Complex.ofReal_re]
end
end HochschildCatalanMoments
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMoments
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma norm_le_of_positive_moment_bound (τ : A →ₚ[ℂ] ℂ)
    (hfaithful : ∀ x : A, τ (star x * x) = 0 → x = 0)
    (a : A) (ha : 0 ≤ a) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ n : ℕ, (τ (a^n)).re ≤ R^n) : ‖a‖ ≤ R := by
  by_contra! hnot
  have : Nontrivial A := nontrivial_of_ne a 0 (by
    intro h; rw [h, norm_zero] at hnot; linarith)
  obtain ⟨c, hRc, hca⟩ := exists_between hnot
  have hc : 0 < c := hR.trans_lt hRc
  let f : ℝ → ℝ := fun t => max 0 (t-c)
  have hf : Continuous f := by fun_prop
  let x : A := cfc f a
  have hsa : IsSelfAdjoint a := .of_nonneg ha
  have hsx : IsSelfAdjoint x := cfc_predicate f a
  have hineq (n : ℕ) : c^n • (star x*x) ≤ ‖a‖^2 • a^n := by
    have hleft : cfc (fun t => c^n * (f t * f t)) a = c^n • (star x*x) := by
      rw [cfc_const_mul (c^n) (fun t => f t * f t) a (hf.mul hf).continuousOn,
        cfc_mul f f a hf.continuousOn hf.continuousOn, hsx.star_eq]
    have hright : cfc (fun t : ℝ => ‖a‖^2 * t^n) a = ‖a‖^2 • a^n := by
      rw [cfc_const_mul (‖a‖^2) (fun t : ℝ => t^n) a (continuous_id.pow n).continuousOn,
        cfc_pow_id a n hsa]
    rw [← hleft, ← hright]
    apply (cfc_le_iff _ _ a ((hf.mul hf).const_mul _).continuousOn
      ((continuous_id.pow n).const_mul _).continuousOn hsa).mpr
    intro t ht
    change c^n * (f t * f t) ≤ ‖a‖^2 * t^n
    have ht0 : 0 ≤ t := spectrum_nonneg_of_nonneg ha ht
    have htA : t ≤ ‖a‖ := (le_abs_self t).trans (spectrum.norm_le_norm_of_mem ht)
    by_cases htc : t ≤ c
    · simp only [f, max_eq_left (sub_nonpos.mpr htc), mul_zero]
      positivity
    · have hct : c ≤ t := le_of_lt (lt_of_not_ge htc)
      simp only [f, max_eq_right (sub_nonneg.mpr hct)]
      have hfA : (t-c)*(t-c) ≤ ‖a‖^2 := by nlinarith [norm_nonneg a]
      calc
        _ ≤ t^n * ‖a‖^2 := mul_le_mul (pow_le_pow_left₀ hc.le hct n) hfA
          (mul_self_nonneg _) (pow_nonneg ht0 _)
        _ = _ := by ring
  have hxtrace : 0 ≤ (τ (star x*x)).re := by
    exact (τ.map_nonneg (star_mul_self_nonneg x)).1
  have htrace (n : ℕ) : (τ (star x*x)).re ≤ ‖a‖^2 * (R/c)^n := by
    have hh := τ.monotone (hineq n)
    change τ (c^n • (star x*x)) ≤ τ (‖a‖^2 • a^n) at hh
    rw [τ.map_smul_of_tower, τ.map_smul_of_tower] at hh
    have hre : c^n * (τ (star x*x)).re ≤ ‖a‖^2 * (τ (a^n)).re := by simpa only [Complex.smul_re, smul_eq_mul] using hh.1
    apply (mul_le_mul_iff_right₀ (pow_pos hc n)).mp
    calc
      _ = c^n * (τ (star x*x)).re := by ring
      _ ≤ ‖a‖^2 * (τ (a^n)).re := hre
      _ ≤ ‖a‖^2 * R^n := mul_le_mul_of_nonneg_left (hbound n) (sq_nonneg _)
      _ = (‖a‖^2 * (R/c)^n) * c^n := by
        rw [div_pow, mul_assoc, div_mul_cancel₀ _ (ne_of_gt (pow_pos hc n))]
      _ = c^n * (‖a‖^2 * (R/c)^n) := by ring
  have hlim : Tendsto (fun n : ℕ => ‖a‖^2 * (R/c)^n) atTop (𝓝 0) := by
    convert (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR hc.le)
      ((div_lt_one hc).mpr hRc)).const_mul (‖a‖^2) using 1; simp
  have hzre : (τ (star x*x)).re = 0 := le_antisymm (ge_of_tendsto' hlim htrace) hxtrace
  have hz : τ (star x*x) = 0 := by
    have hp := τ.map_nonneg (star_mul_self_nonneg x)
    exact Complex.ext hzre hp.2.symm
  have hx : x = 0 := hfaithful x hz
  have heq : cfc f a = cfc (fun _ : ℝ => 0) a := by simpa only [cfc_const_zero] using hx
  have hxnorm := eqOn_of_cfc_eq_cfc heq hf.continuousOn continuousOn_const hsa
    (CStarAlgebra.norm_mem_spectrum_of_nonneg ha)
  dsimp [f] at hxnorm
  have : 0 < max 0 (‖a‖-c) := lt_max_of_lt_right (sub_pos.mpr hca)
  linarith

variable {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

end HochschildMoments
namespace HochschildFreeWords
open FreeGroup
variable {α : Type*}

theorem boundary_decomposition (v w : List (α × Bool))
    (hv : IsReduced v) (hw : IsReduced w) :
    ∃ u c h, v = u ++ c ∧ w = invRev c ++ h ∧ IsReduced (u ++ h) := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨[], [], w, rfl, rfl, hw⟩
  | @append_singleton v a ih =>
    cases w with
    | nil => exact ⟨v ++ [a], [], [], by simp, rfl, by simpa using hv⟩
    | cons b w =>
      by_cases hab : a.1 = b.1 ∧ a.2 = !b.2
      · have hv' : IsReduced v := hv.left_of_append
        have hw' : IsReduced w := hw.tail
        obtain ⟨u,c,h,hu,hc,hr⟩ := ih w hv' hw'
        refine ⟨u, c ++ [a], h, ?_, ?_, hr⟩
        · simp only [hu, List.append_assoc]
        · have hba : (a.1, !a.2) = b := by
            apply Prod.ext
            · exact hab.1
            · simp [hab.2]
          have hinv : invRev [a] = [b] := by
            simp [invRev, hba]
          rw [invRev_append, hinv]
          simpa using congrArg (fun l => b :: l) hc
      · refine ⟨v ++ [a], [], b::w, by simp, rfl, ?_⟩
        change List.IsChain _ _
        rw [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons]
        refine ⟨hv, ?_, hw⟩
        intro hfst
        have hh : a.2 ≠ !b.2 := fun h => hab ⟨hfst,h⟩
        cases ha : a.2 <;> cases hb : b.2 <;> simp_all

variable [DecidableEq α]

theorem boundary_reduction (v w : List (α × Bool))
    (hv : IsReduced v) (hw : IsReduced w) :
    ∃ u c h, v = u ++ c ∧ w = invRev c ++ h ∧
      reduce (v ++ w) = u ++ h ∧ IsReduced (u ++ h) := by
  obtain ⟨u,c,h,hu,hw,hr⟩ := boundary_decomposition v w hv hw
  refine ⟨u,c,h,hu,hw,?_,hr⟩
  have heq : FreeGroup.mk (v ++ w) = FreeGroup.mk (u ++ h) := by
    rw [hu,hw]
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    group
  have heq' := congr_arg FreeGroup.toWord heq
  simpa only [FreeGroup.toWord_mk, hr.reduce_eq] using heq'
end HochschildFreeWords

namespace HochschildLength
open Finset
noncomputable section

abbrev Vector (ι : Type*) := lp (fun _ : ι => ℂ) 2

lemma norm_sum_single_sq {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (out : ι → κ)
    (c : ι → ℂ) (hinj : Set.InjOn out s) :
    ‖∑ i ∈ s, (lp.single 2 (out i) (c i) : Vector κ)‖ ^ 2 = ∑ i ∈ s, ‖c i‖ ^ 2 := by
  classical
  have hi : inner ℂ (∑ i ∈ s, (lp.single 2 (out i) (c i) : Vector κ))
      (∑ i ∈ s, (lp.single 2 (out i) (c i) : Vector κ)) =
      ∑ i ∈ s, (‖c i‖ : ℂ) ^ 2 := by
    rw [sum_inner]
    apply sum_congr rfl
    intro i hi
    rw [inner_sum]
    rw [sum_eq_single i]
    · simp [inner_self_eq_norm_sq_to_K]
    · intro j hj hji
      rw [lp.inner_single_left, lp.single_apply_ne]
      · exact inner_zero_right _
      · exact fun h => hji (hinj hj hi h.symm)
    · exact fun h => (h hi).elim
  apply Complex.ofReal_injective
  simpa [inner_self_eq_norm_sq_to_K, Complex.ofReal_sum, Complex.ofReal_pow] using hi

lemma norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤
      (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have h := norm_sum_le s (fun i => a i * b i)
  simp only [norm_mul] at h
  exact (pow_le_pow_left₀ (norm_nonneg _) h 2).trans
    (sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

lemma block_matrix_bound {U V H : Type*} (su : Finset U) (sv : Finset V)
    (sh : Finset H) (a : U → V → ℂ) (b : V → H → ℂ) :
    ∑ h ∈ sh, ∑ u ∈ su, ‖∑ v ∈ sv, a u v * b v h‖ ^ 2 ≤
      (∑ u ∈ su, ∑ v ∈ sv, ‖a u v‖ ^ 2) *
        (∑ h ∈ sh, ∑ v ∈ sv, ‖b v h‖ ^ 2) := by
  calc
    _ ≤ ∑ h ∈ sh, ∑ u ∈ su,
        (∑ v ∈ sv, ‖a u v‖ ^ 2) * (∑ v ∈ sv, ‖b v h‖ ^ 2) := by
      gcongr with h hh u hu
      exact norm_sum_mul_sq_le sv _ _
    _ = _ := by simp_rw [← sum_mul, ← mul_sum]

lemma masked_block_matrix_bound {U V H W : Type*} [DecidableEq W]
    (su : Finset U) (sv : Finset V) (sh : Finset H)
    (a : U → V → ℂ) (b : V → H → ℂ) (P : U → H → Prop) [∀ u h, Decidable (P u h)]
    (out : U → H → W)
    (hinj : Set.InjOn (fun p : H × U => out p.2 p.1)
      {p | p.1 ∈ sh ∧ p.2 ∈ su ∧ P p.2 p.1}) :
    ‖∑ p ∈ (sh ×ˢ su).filter (fun p => P p.2 p.1),
        (lp.single 2 (out p.2 p.1) (∑ v ∈ sv, a p.2 v * b v p.1) : Vector W)‖ ^ 2 ≤
      (∑ u ∈ su, ∑ v ∈ sv, ‖a u v‖ ^ 2) *
        (∑ h ∈ sh, ∑ v ∈ sv, ‖b v h‖ ^ 2) := by
  classical
  rw [norm_sum_single_sq _ _ _ (by
    intro p hp q hq hpq
    apply hinj (by simpa only [mem_coe, mem_filter, mem_product, Set.mem_ofPred_eq, and_assoc] using hp)
      (by simpa only [mem_coe, mem_filter, mem_product, Set.mem_ofPred_eq, and_assoc] using hq) hpq)]
  calc
    _ ≤ ∑ p ∈ sh ×ˢ su, ‖∑ v ∈ sv, a p.2 v * b v p.1‖ ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intros; positivity
    _ = ∑ h ∈ sh, ∑ u ∈ su, ‖∑ v ∈ sv, a u v * b v h‖ ^ 2 := sum_product ..
    _ ≤ _ := block_matrix_bound su sv sh a b
end
end HochschildLength
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildLength
open Finset FreeGroup
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev Word (α : Type*) := List (α × Bool)
def words : ℕ → Finset (Word α)
  | 0 => {[]}
  | n+1 => ((univ : Finset (α × Bool)) ×ˢ words n).image (fun p => p.1 :: p.2)
@[simp] lemma mem_words {w : Word α} {n : ℕ} : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    cases w with
    | nil => simp [words]
    | cons a l => simp [words, ih]
def wordBall (N : ℕ) : Finset (Word α) := (range (N+1)).biUnion words
@[simp] lemma mem_wordBall {w : Word α} {N : ℕ} : w ∈ wordBall N ↔ w.length ≤ N := by
  simp only [wordBall, mem_biUnion, mem_range, mem_words]
  constructor
  · rintro ⟨n, hn, rfl⟩; omega
  · intro h; exact ⟨w.length, by omega, rfl⟩

omit [Fintype α] in
lemma reduced_boundary_product (u v h : Word α) (hr : IsReduced (u ++ h)) :
    reduce ((u ++ v) ++ (invRev v ++ h)) = u ++ h := by
  have heq : FreeGroup.mk ((u ++ v) ++ (invRev v ++ h)) = FreeGroup.mk (u ++ h) := by
    simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
    group
  have ht := congr_arg FreeGroup.toWord heq
  simpa only [FreeGroup.toWord_mk, hr.reduce_eq] using ht

omit [Fintype α] in

lemma boundary_unique {u v h u' v' h' : Word α}
    (hr : IsReduced (u ++ h)) (hr' : IsReduced (u' ++ h'))
    (hw : u ++ v = u' ++ v') (hx : invRev v ++ h = invRev v' ++ h') :
    u = u' ∧ v = v' ∧ h = h' := by
  have hout : u ++ h = u' ++ h' := by
    rw [← reduced_boundary_product u v h hr, hw, hx,
      reduced_boundary_product u' v' h' hr']
  have hwL := congrArg List.length hw
  have hxL := congrArg List.length hx
  have hyL := congrArg List.length hout
  simp only [List.length_append, invRev_length] at hwL hxL hyL
  have hvL : v.length = v'.length := by omega
  have hu : u = u' := List.append_inj_left' hw hvL
  subst u'
  have hv : v = v' := List.append_cancel_left hw
  subst v'
  exact ⟨rfl, rfl, List.append_cancel_left hx⟩

omit [Fintype α] [DecidableEq α] in
lemma append_injOn {su sv : Finset (Word α)} {l : ℕ}
    (hU : ∀ u ∈ su, u.length = l) :
    Set.InjOn (fun p : Word α × Word α => p.1 ++ p.2) (↑(su ×ˢ sv) : Set _) := by
  rintro ⟨u,v⟩ hp ⟨u',v'⟩ hp' h
  have hp₁ : u ∈ su ∧ v ∈ sv := by simpa only [mem_coe, mem_product] using hp
  have hp₂ : u' ∈ su ∧ v' ∈ sv := by simpa only [mem_coe, mem_product] using hp'
  have hu : u = u' := List.append_inj_left h
    ((hU u hp₁.1).trans (hU u' hp₂.1).symm)
  subst u'
  exact Prod.ext rfl (List.append_cancel_left h)

omit [Fintype α] [DecidableEq α] in
lemma invRev_append_injOn {sv sh : Finset (Word α)} {l : ℕ}
    (hV : ∀ v ∈ sv, v.length = l) :
    Set.InjOn (fun p : Word α × Word α => invRev p.1 ++ p.2) (↑(sv ×ˢ sh) : Set _) := by
  rintro ⟨v,h⟩ hp ⟨v',h'⟩ hp' hh
  have hp₁ : v ∈ sv ∧ h ∈ sh := by simpa only [mem_coe, mem_product] using hp
  have hp₂ : v' ∈ sv ∧ h' ∈ sh := by simpa only [mem_coe, mem_product] using hp'
  have hv : invRev v = invRev v' := List.append_inj_left hh (by
    simp only [invRev_length]
    exact (hV v hp₁.1).trans (hV v' hp₂.1).symm)
  have hv' : v = v' := by simpa using congrArg invRev hv
  subst v'
  exact Prod.ext rfl (List.append_cancel_left hh)

omit [Fintype α] [DecidableEq α] in
lemma sum_sq_comp_le {I J : Type*} [DecidableEq J]
    (si : Finset I) (sj : Finset J) (out : I → J) (c : J → ℂ)
    (hinj : Set.InjOn out si) (hzero : ∀ i ∈ si, out i ∉ sj → c (out i) = 0) :
    ∑ i ∈ si, ‖c (out i)‖ ^ 2 ≤ ∑ j ∈ sj, ‖c j‖ ^ 2 := by
  classical
  let ss := si.filter (fun i => out i ∈ sj)
  have heq : ∑ i ∈ si, ‖c (out i)‖ ^ 2 = ∑ i ∈ ss, ‖c (out i)‖ ^ 2 := by
    symm
    apply sum_subset (filter_subset _ _)
    intro i hi hnot
    have hz : c (out i) = 0 := hzero i hi (by
      intro hh; exact hnot (mem_filter.mpr ⟨hi,hh⟩))
    simp [hz]
  rw [heq, ← sum_image (f := fun j => ‖c j‖ ^ 2) (s := ss)
    (hinj.mono (by exact filter_subset _ _))]
  apply sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact (mem_filter.mp hi).2
  · intros; positivity

lemma coefficient_energy_le (q t : ℕ) (ht : t ≤ q) (c : Word α → ℂ) :
    ∑ u ∈ words (q-t), ∑ v ∈ words t, ‖c (u ++ v)‖ ^ 2 ≤
      ∑ w ∈ words q, ‖c w‖ ^ 2 := by
  have hb := sum_sq_comp_le (words (α := α) (q-t) ×ˢ words t) (words q)
    (fun p : Word α × Word α => p.1 ++ p.2) c (append_injOn (l := q-t) (by simp)) (by
      intro p hp hn
      have hh : p.1.length = q-t ∧ p.2.length = t := by simpa using hp
      exact (hn (by simp [hh, Nat.sub_add_cancel ht])).elim)
  simpa only [sum_product] using hb

lemma input_energy_le (N t : ℕ) (f : Word α → ℂ)
    (hf : ∀ w, N < w.length → f w = 0) :
    ∑ h ∈ wordBall N, ∑ v ∈ words t, ‖f (invRev v ++ h)‖ ^ 2 ≤
      ∑ x ∈ wordBall N, ‖f x‖ ^ 2 := by
  have hb := sum_sq_comp_le (words (α := α) t ×ˢ wordBall N) (wordBall N)
    (fun p : Word α × Word α => invRev p.1 ++ p.2) f
    (invRev_append_injOn (l := t) (by simp)) (by
      intro p _ hp
      exact hf _ (by simpa using hp))
  rw [sum_comm]
  simpa only [sum_product] using hb

def piece (q N t : ℕ) (c f : Word α → ℂ) : Vector (Word α) := by
  classical
  exact ∑ p ∈ ((wordBall N) ×ˢ words (q-t)).filter (fun p => IsReduced (p.2 ++ p.1)),
    lp.single 2 (p.2 ++ p.1) (∑ v ∈ words t, c (p.2 ++ v) * f (invRev v ++ p.1))

lemma piece_norm_sq_le (q N t : ℕ) (ht : t ≤ q) (c f : Word α → ℂ)
    (hf : ∀ w, N < w.length → f w = 0) :
    ‖piece q N t c f‖ ^ 2 ≤
      (∑ w ∈ words q, ‖c w‖ ^ 2) * ∑ x ∈ wordBall N, ‖f x‖ ^ 2 := by
  classical
  have hi : Set.InjOn (fun p : Word α × Word α => p.2 ++ p.1)
      {p | p.1 ∈ wordBall N ∧ p.2 ∈ words (q-t) ∧ IsReduced (p.2 ++ p.1)} := by
    rintro ⟨h,u⟩ hp ⟨h',u'⟩ hp' heq
    have hu : u = u' := List.append_inj_left heq
      ((mem_words.mp hp.2.1).trans (mem_words.mp hp'.2.1).symm)
    subst u'
    exact Prod.ext (List.append_cancel_left heq) rfl
  have hb := masked_block_matrix_bound (words (q-t)) (words t) (wordBall N)
    (fun u v => c (u ++ v)) (fun v h => f (invRev v ++ h))
    (fun u h => IsReduced (u ++ h)) (fun u h => u ++ h) hi
  exact hb.trans (mul_le_mul (coefficient_energy_le q t ht c)
    (input_energy_le N t f hf) (by positivity) (by positivity))

lemma piece_norm_le (q N t : ℕ) (ht : t ≤ q) (c f : Word α → ℂ)
    (hf : ∀ w, N < w.length → f w = 0) :
    ‖piece q N t c f‖ ≤
      Real.sqrt (∑ w ∈ words q, ‖c w‖ ^ 2) *
        Real.sqrt (∑ x ∈ wordBall N, ‖f x‖ ^ 2) := by
  have hc0 : 0 ≤ ∑ w ∈ words (α := α) q, ‖c w‖ ^ 2 := by positivity
  have hf0 : 0 ≤ ∑ x ∈ wordBall (α := α) N, ‖f x‖ ^ 2 := by positivity
  have hsq : (Real.sqrt (∑ w ∈ words (α := α) q, ‖c w‖ ^ 2) *
      Real.sqrt (∑ x ∈ wordBall (α := α) N, ‖f x‖ ^ 2)) ^ 2 =
      (∑ w ∈ words q, ‖c w‖ ^ 2) * ∑ x ∈ wordBall N, ‖f x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc0, Real.sq_sqrt hf0]
  have hb := piece_norm_sq_le q N t ht c f hf
  rw [← hsq] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hb

omit [Fintype α] [DecidableEq α] in
lemma single_sum {I J : Type*} [DecidableEq J] (s : Finset I) (j : J) (c : I → ℂ) :
    (lp.single 2 j (∑ i ∈ s, c i) : Vector J) = ∑ i ∈ s, lp.single 2 j (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [sum_insert ha, lp.single_add, ih]

def tripleBox (q N t : ℕ) : Finset ((Word α × Word α) × Word α) := by
  classical
  exact (((wordBall N) ×ˢ words (q-t)).filter
    (fun p => IsReduced (p.2 ++ p.1))) ×ˢ words t

def triples (q N : ℕ) : Finset (Σ _ : ℕ, (Word α × Word α) × Word α) :=
  (range (q+1)).sigma (tripleBox q N)

@[simp] lemma mem_triples (q N t : ℕ) (h u v : Word α) :
    Sigma.mk t ((h,u),v) ∈ triples q N ↔
      t ≤ q ∧ h.length ≤ N ∧ u.length = q-t ∧ IsReduced (u ++ h) ∧ v.length = t := by
  classical
  simp [triples, tripleBox, and_assoc]

def tripleValue (c f : Word α → ℂ) (p : Σ _ : ℕ, (Word α × Word α) × Word α) :
    Vector (Word α) :=
  lp.single 2 (p.2.1.2 ++ p.2.1.1) (c (p.2.1.2 ++ p.2.2) * f (invRev p.2.2 ++ p.2.1.1))

def triplePair (p : Σ _ : ℕ, (Word α × Word α) × Word α) : Word α × Word α :=
  (p.2.1.2 ++ p.2.2, invRev p.2.2 ++ p.2.1.1)

def convolution (q N : ℕ) (c f : Word α → ℂ) : Vector (Word α) :=
  ∑ p ∈ words q ×ˢ wordBall N,
    lp.single 2 (reduce (p.1 ++ p.2)) (c p.1 * f p.2)

lemma sum_pieces (q N : ℕ) (c f : Word α → ℂ) :
    ∑ t ∈ range (q+1), piece q N t c f =
      ∑ p ∈ triples q N, tripleValue c f p := by
  classical
  unfold triples
  rw [← sum_sigma' (range (q+1)) (tripleBox q N)
    (fun t p => tripleValue c f ⟨t,p⟩)]
  apply sum_congr rfl
  intro t _
  unfold piece tripleBox
  rw [sum_product]
  apply sum_congr rfl
  intro p _
  exact single_sum (words t) (p.2 ++ p.1) _

lemma convolution_eq_pieces (q N : ℕ) (c f : Word α → ℂ)
    (hc : ∀ w, c w ≠ 0 → IsReduced w)
    (hfr : ∀ w, f w ≠ 0 → IsReduced w)
    (hfN : ∀ w, N < w.length → f w = 0) :
    convolution q N c f = ∑ t ∈ range (q+1), piece q N t c f := by
  classical
  rw [sum_pieces]
  unfold convolution
  symm
  apply sum_bij_ne_zero (fun p _ _ => triplePair p)
  · rintro ⟨t,⟨⟨h,u⟩,v⟩⟩ hp hn
    obtain ⟨ht, hh, hu, hr, hv⟩ := (mem_triples q N t h u v).mp hp
    simp only [triplePair, mem_product, mem_words, mem_wordBall, List.length_append,
      invRev_length]
    refine ⟨by omega, ?_⟩
    by_contra! hgt
    have hz := hfN (invRev v ++ h) (by simpa using hgt)
    exact hn (by simp [tripleValue, hz])
  · rintro ⟨t,⟨⟨h,u⟩,v⟩⟩ hp _ ⟨t',⟨⟨h',u'⟩,v'⟩⟩ hp' _ heq
    obtain ⟨ht, hh, hu, hr, hv⟩ := (mem_triples q N t h u v).mp hp
    obtain ⟨ht', hh', hu', hr', hv'⟩ := (mem_triples q N t' h' u' v').mp hp'
    have hw : u ++ v = u' ++ v' := congrArg Prod.fst heq
    have hx : invRev v ++ h = invRev v' ++ h' := congrArg Prod.snd heq
    obtain ⟨rfl,rfl,rfl⟩ := boundary_unique hr hr' hw hx
    have htt : t = t' := hv.symm.trans hv'
    cases htt
    rfl
  · rintro ⟨w,x⟩ hp hn
    have hwL : w.length = q := mem_words.mp (mem_product.mp hp).1
    have hxL : x.length ≤ N := mem_wordBall.mp (mem_product.mp hp).2
    have hcw : c w ≠ 0 := by
      intro hz
      exact hn (by simp [hz])
    have hfx : f x ≠ 0 := by
      intro hz
      exact hn (by simp [hz])
    obtain ⟨u,v,h,hw,hx,hy,hr⟩ :=
      HochschildFreeWords.boundary_reduction w x (hc w hcw) (hfr x hfx)
    have hwLen : u.length + v.length = q := by simpa [hw] using hwL
    have hxLen : v.length + h.length ≤ N := by simpa [hx] using hxL
    let p : Σ _ : ℕ, (Word α × Word α) × Word α := ⟨v.length,((h,u),v)⟩
    have hpm : p ∈ triples q N := (mem_triples q N _ _ _ _).mpr
      ⟨by omega, by omega, by omega, hr, rfl⟩
    have hpvalue : tripleValue c f p =
        lp.single 2 (reduce (w ++ x)) (c w * f x) := by
      simp only [tripleValue, p, ← hw, ← hx, hy]
    refine ⟨p,hpm,?_,?_⟩
    · rwa [hpvalue]
    · exact Prod.ext hw.symm hx.symm
  · rintro ⟨t,⟨⟨h,u⟩,v⟩⟩ hp _
    obtain ⟨ht, hh, hu, hr, hv⟩ := (mem_triples q N t h u v).mp hp
    simp only [tripleValue, triplePair, reduced_boundary_product u v h hr]

theorem convolution_norm_le (q N : ℕ) (c f : Word α → ℂ)
    (hc : ∀ w, c w ≠ 0 → IsReduced w)
    (hfr : ∀ w, f w ≠ 0 → IsReduced w)
    (hfN : ∀ w, N < w.length → f w = 0) :
    ‖convolution q N c f‖ ≤ (q+1 : ℝ) *
      Real.sqrt (∑ w ∈ words q, ‖c w‖ ^ 2) *
        Real.sqrt (∑ x ∈ wordBall N, ‖f x‖ ^ 2) := by
  rw [convolution_eq_pieces q N c f hc hfr hfN]
  calc
    _ ≤ ∑ t ∈ range (q+1), ‖piece q N t c f‖ := norm_sum_le _ _
    _ ≤ ∑ _t ∈ range (q+1), Real.sqrt (∑ w ∈ words q, ‖c w‖ ^ 2) *
        Real.sqrt (∑ x ∈ wordBall N, ‖f x‖ ^ 2) := by
      apply sum_le_sum
      intro t ht
      exact piece_norm_le q N t (by simpa using ht) c f hfN
    _ = _ := by simp [mul_assoc]

end
end HochschildLength

namespace HochschildTransfer
open Finset FreeGroup
open HochschildLength
noncomputable section
variable {α : Type*} [DecidableEq α]
abbrev Polynomial (α : Type*) := MonoidAlgebra ℂ (FreeGroup α)

def vector : Polynomial α →ₗ[ℂ] Vector (Word α) :=
  (Finsupp.lsum ℂ (fun g : FreeGroup α => lp.lsingle (𝕜 := ℂ) (E := fun _ : Word α => ℂ) 2 g.toWord)).comp
    (MonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

lemma vector_def (p : Polynomial α) : vector p =
    ∑ g ∈ p.coeff.support, lp.single 2 g.toWord (p.coeff g) := by
  rfl

@[simp] lemma vector_single (g : FreeGroup α) (c : ℂ) :
    vector (MonoidAlgebra.single g c) = lp.single 2 g.toWord c := by
  simp [vector]

lemma vector_norm_sq (p : Polynomial α) :
    ‖vector p‖^2 = ∑ g ∈ p.coeff.support, ‖p.coeff g‖^2 := by
  rw [vector_def]
  exact norm_sum_single_sq _ _ _ (toWord_injective.injOn)

def wordCoeff (p : Polynomial α) (w : Word α) : ℂ := by
  classical
  exact if IsReduced w then p.coeff (mk w) else 0

@[simp] lemma wordCoeff_toWord (p : Polynomial α) (g : FreeGroup α) :
    wordCoeff p g.toWord = p.coeff g := by
  simp [wordCoeff, isReduced_toWord, mk_toWord]

omit [DecidableEq α] in
lemma reduced_of_wordCoeff_ne_zero (p : Polynomial α) (w : Word α)
    (h : wordCoeff p w ≠ 0) : IsReduced w := by
  classical
  by_contra hn
  simp [wordCoeff, hn] at h

omit [DecidableEq α] in
lemma wordCoeff_eq_zero (p : Polynomial α) (w : Word α)
    (h : p.coeff (mk w) = 0) : wordCoeff p w = 0 := by
  simp [wordCoeff, h]

lemma sum_wordCoeff (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s)
    {V : Type*} [AddCommMonoid V] (F : Word α → ℂ → V)
    (hzero : ∀ w, F w 0 = 0) :
    (∑ w ∈ s, F w (wordCoeff p w)) =
      ∑ g ∈ p.coeff.support, F g.toWord (p.coeff g) := by
  classical
  calc
    _ = ∑ w ∈ p.coeff.support.image toWord, F w (wordCoeff p w) := by
      symm
      apply sum_subset
      · intro w hw
        obtain ⟨g,hg,rfl⟩ := mem_image.mp hw
        exact hs g hg
      · intro w hw hnot
        by_cases hr : IsReduced w
        · have hm : mk w ∉ p.coeff.support := by
            intro hm
            apply hnot
            exact mem_image.mpr ⟨mk w, hm, by simpa [toWord_mk] using hr.reduce_eq⟩
          simp [wordCoeff, hr, Finsupp.notMem_support_iff.mp hm, hzero]
        · simp [wordCoeff, hr, hzero]
    _ = _ := by
      rw [sum_image toWord_injective.injOn]
      simp only [wordCoeff_toWord]

lemma polynomial_wordSum (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s) :
    (∑ w ∈ s, MonoidAlgebra.single (mk w) (wordCoeff p w)) = p := by
  rw [sum_wordCoeff p s hs _ (by simp)]
  simpa only [mk_toWord, Finsupp.sum] using p.sum_coeff_single

lemma vector_wordSum (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s) :
    (∑ w ∈ s, lp.single 2 w (wordCoeff p w)) = vector p := by
  rw [sum_wordCoeff p s hs _ (by simp), vector_def]

lemma vector_mul_wordSum (p d : Polynomial α) (S T : Finset (Word α))
    (hS : ∀ g ∈ p.coeff.support, g.toWord ∈ S)
    (hT : ∀ g ∈ d.coeff.support, g.toWord ∈ T) :
    vector (p*d) = ∑ v ∈ S, ∑ w ∈ T,
      lp.single 2 (reduce (v++w)) (wordCoeff p v * wordCoeff d w) := by
  conv_lhs => rw [← polynomial_wordSum p S hS, ← polynomial_wordSum d T hT]
  simp only [sum_mul, mul_sum, map_sum, MonoidAlgebra.single_mul_single, vector_single,
    FreeGroup.mul_mk, toWord_mk]
  rw [sum_comm]

lemma vector_norm_sq_wordSum (p : Polynomial α) (s : Finset (Word α))
    (hs : ∀ g ∈ p.coeff.support, g.toWord ∈ s) :
    ‖vector p‖^2 = ∑ w ∈ s, ‖wordCoeff p w‖^2 := by
  rw [← vector_wordSum p s hs]
  exact norm_sum_single_sq s id _ (Function.injective_id.injOn)

variable [Fintype α]
lemma vector_mul_norm_le (p d : Polynomial α) (q : ℕ)
    (hq : ∀ g ∈ p.coeff.support, g.toWord.length = q) :
    ‖vector (p*d)‖ ≤ (q+1:ℝ) * ‖vector p‖ * ‖vector d‖ := by
  let N := d.coeff.support.sup (fun g => g.toWord.length)
  have hq' : ∀ g ∈ p.coeff.support, g.toWord ∈ words q := by
    simpa only [mem_words] using hq
  have hN : ∀ g ∈ d.coeff.support, g.toWord ∈ wordBall N := by
    intro g hg
    rw [mem_wordBall]
    exact le_sup (f := fun g : FreeGroup α => g.toWord.length) hg
  have heq : vector (p*d) = convolution q N (wordCoeff p) (wordCoeff d) := by
    rw [vector_mul_wordSum p d _ _ hq' hN]
    unfold HochschildLength.convolution
    exact (sum_product (words q) (wordBall N)
      (fun z : Word α × Word α => (lp.single 2 (reduce (z.1++z.2))
        (wordCoeff p z.1 * wordCoeff d z.2) : Vector (Word α)))).symm
  rw [heq]
  have h := convolution_norm_le q N (wordCoeff p) (wordCoeff d)
    (reduced_of_wordCoeff_ne_zero p) (reduced_of_wordCoeff_ne_zero d) (by
      intro w hw
      classical
      by_cases hr : IsReduced w
      · apply wordCoeff_eq_zero
        by_contra hn
        have hmem := hN (mk w) (Finsupp.mem_support_iff.mpr hn)
        rw [mem_wordBall, toWord_mk, hr.reduce_eq] at hmem
        omega
      · simp [wordCoeff, hr])
  rw [← vector_norm_sq_wordSum p _ hq', ← vector_norm_sq_wordSum d _ hN,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h
  exact h

end
end HochschildTransfer

namespace HochschildTracePolynomial
open Finset
open scoped ComplexOrder
noncomputable section
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {G : Type*} [Group G] [DecidableEq G]
variable (τ : A →ₚ[ℂ] ℂ) (u : G →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : G, g ≠ 1 → τ (u g) = 0)

include hτ hu hfree

lemma inner_word (g h : G) :
    inner ℂ (τ.toPreGNS (u g)) (τ.toPreGNS (u h)) = if g = h then 1 else 0 := by
  classical
  rw [PositiveLinearMap.preGNS_inner_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, hu, ← map_mul]
  split_ifs with heq
  · subst h
    simp [hτ]
  · apply hfree
    exact fun h => heq (_root_.inv_mul_eq_one.mp h)

lemma norm_sum_word_sq (s : Finset G) (c : G → ℂ) :
    ‖τ.toPreGNS (∑ g ∈ s, c g • u g)‖^2 = ∑ g ∈ s, ‖c g‖^2 := by
  classical
  have hi : inner ℂ (τ.toPreGNS (∑ g ∈ s, c g • u g))
      (τ.toPreGNS (∑ g ∈ s, c g • u g)) = ∑ g ∈ s, (‖c g‖ : ℂ)^2 := by
    simp only [map_sum, map_smul]
    rw [sum_inner]
    apply sum_congr rfl
    intro g hg
    rw [inner_sum, sum_eq_single g]
    · rw [inner_smul_left, inner_smul_right, inner_word τ u hτ hu hfree]
      simp [Complex.conj_mul']
    · intro h hh hne
      rw [inner_smul_left, inner_smul_right, inner_word τ u hτ hu hfree]
      simp [Ne.symm hne]
    · exact fun h => (h hg).elim
  apply Complex.ofReal_injective
  simpa [inner_self_eq_norm_sq_to_K, Complex.ofReal_sum, Complex.ofReal_pow] using hi

lemma norm_eval_sq (p : MonoidAlgebra ℂ G) :
    ‖τ.toPreGNS (MonoidAlgebra.lift ℂ A G u p)‖^2 =
      ∑ g ∈ p.coeff.support, ‖p.coeff g‖^2 := by
  rw [MonoidAlgebra.lift_apply]
  exact norm_sum_word_sq τ u hτ hu hfree _ _

end
end HochschildTracePolynomial

namespace HochschildPolynomial
open Finset
noncomputable section
variable {G : Type*} [Group G]

def adjoint (p : MonoidAlgebra ℂ G) : MonoidAlgebra ℂ G :=
  .ofCoeff ((p.coeff.mapRange (starRingEnd ℂ) (map_zero _)).mapDomain Inv.inv)

@[simp] lemma coeff_adjoint (p : MonoidAlgebra ℂ G) (g : G) :
    (adjoint p).coeff g = star (p.coeff g⁻¹) := by
  have h := Finsupp.mapDomain_apply inv_injective
    (p.coeff.mapRange (starRingEnd ℂ) (map_zero _)) g⁻¹
  simpa [adjoint] using h

lemma adjoint_support (p : MonoidAlgebra ℂ G) (g : G) :
    g ∈ (adjoint p).coeff.support ↔ g⁻¹ ∈ p.coeff.support := by
  simp [Finsupp.mem_support_iff]

variable {A : Type*} [CStarAlgebra A]
lemma eval_adjoint (u : G →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (p : MonoidAlgebra ℂ G) :
    MonoidAlgebra.lift ℂ A G u (adjoint p) = star (MonoidAlgebra.lift ℂ A G u p) := by
  classical
  simp only [MonoidAlgebra.lift_apply, adjoint]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul])]
  rw [Finsupp.sum_mapRange_index (by simp)]
  simp only [Finsupp.sum, star_sum, star_smul, hu, Complex.star_def]

end
end HochschildPolynomial

open scoped ComplexOrder
open Filter Topology
namespace HochschildTransfer
open Finset
open scoped ComplexOrder
noncomputable section
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)
include hτ hu hfree
omit [Fintype α] in
lemma vector_norm_eq_preGNS (p : Polynomial α) :
    ‖vector p‖ = ‖τ.toPreGNS (MonoidAlgebra.lift ℂ A (FreeGroup α) u p)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [vector_norm_sq, HochschildTracePolynomial.norm_eval_sq τ u hτ hu hfree]

omit hτ hu hfree in
lemma norm_one_gns (h1 : τ 1 = 1) : ‖τ.toPreGNS 1‖ = 1 := by
  have h := congrArg Complex.re (τ.preGNS_norm_sq (τ.toPreGNS 1))
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, h1,
    ← Complex.ofReal_pow, Complex.ofReal_re, Complex.one_re] at h
  nlinarith [norm_nonneg (τ.toPreGNS 1)]

omit hτ hu hfree in
lemma norm_star_gns (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _

theorem norm_eval_homogeneous_le
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (p : Polynomial α) (q : ℕ)
    (hq : ∀ g ∈ p.coeff.support, g.toWord.length = q) :
    ‖MonoidAlgebra.lift ℂ A (FreeGroup α) u p‖ ≤
      (q+1:ℝ) * ‖τ.toPreGNS (MonoidAlgebra.lift ℂ A (FreeGroup α) u p)‖ := by
  let E := MonoidAlgebra.lift ℂ A (FreeGroup α) u
  let C : ℝ := (q+1:ℝ) * ‖τ.toPreGNS (E p)‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hp (d : Polynomial α) :
      ‖τ.toPreGNS (E (p*d))‖ ≤ C * ‖τ.toPreGNS (E d)‖ := by
    simpa only [vector_norm_eq_preGNS τ u hτ hu hfree] using
      vector_mul_norm_le p d q hq
  have hqa : ∀ g ∈ (HochschildPolynomial.adjoint p).coeff.support,
      g.toWord.length = q := by
    intro g hg
    have h := hq g⁻¹ ((HochschildPolynomial.adjoint_support p g).mp hg)
    simpa only [FreeGroup.toWord_inv, FreeGroup.invRev_length] using h
  have hpa (d : Polynomial α) :
      ‖τ.toPreGNS (E (HochschildPolynomial.adjoint p*d))‖ ≤
        C * ‖τ.toPreGNS (E d)‖ := by
    have h := vector_mul_norm_le (HochschildPolynomial.adjoint p) d q hqa
    simp only [vector_norm_eq_preGNS τ u hτ hu hfree,
      HochschildPolynomial.eval_adjoint u hu, norm_star_gns τ htr] at h
    exact h
  let a : Polynomial α := HochschildPolynomial.adjoint p * p
  have ha : E a = star (E p) * E p := by
    simp only [a, map_mul, E, HochschildPolynomial.eval_adjoint u hu]
  have hpow (n : ℕ) : ‖τ.toPreGNS (E (a^n))‖ ≤ (C^2)^n := by
    induction n with
    | zero => simp [norm_one_gns τ hτ]
    | succ n ih =>
      calc
        _ = ‖τ.toPreGNS (E (HochschildPolynomial.adjoint p*(p*a^n)))‖ := by
          rw [pow_succ']; simp only [a, mul_assoc]
        _ ≤ C * ‖τ.toPreGNS (E (p*a^n))‖ := hpa _
        _ ≤ C * (C * ‖τ.toPreGNS (E (a^n))‖) := mul_le_mul_of_nonneg_left (hp _) hC
        _ ≤ C * (C * (C^2)^n) := by gcongr
        _ = _ := by ring
  have hmoment (n : ℕ) : (τ ((star (E p)*E p)^n)).re ≤ (C^2)^n := by
    have hinner : inner ℂ (τ.toPreGNS 1) (τ.toPreGNS (E (a^n))) =
        τ ((star (E p)*E p)^n) := by
      simp only [PositiveLinearMap.preGNS_inner_def,
        PositiveLinearMap.ofPreGNS_toPreGNS, star_one, one_mul, map_pow, ha]
    calc
      _ ≤ ‖τ ((star (E p)*E p)^n)‖ := Complex.re_le_norm _
      _ = ‖inner ℂ (τ.toPreGNS 1) (τ.toPreGNS (E (a^n)))‖ := congrArg norm hinner.symm
      _ ≤ ‖τ.toPreGNS 1‖ * ‖τ.toPreGNS (E (a^n))‖ := norm_inner_le_norm _ _
      _ ≤ (C^2)^n := by rw [norm_one_gns τ hτ, one_mul]; exact hpow n
  have hn := HochschildMoments.norm_le_of_positive_moment_bound τ hfaith
    (star (E p)*E p) (star_mul_self_nonneg _) (C^2) (sq_nonneg _) hmoment
  rw [CStarRing.norm_star_mul_self] at hn
  change ‖E p‖ ≤ C
  nlinarith [norm_nonneg (E p)]
end
end HochschildTransfer
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildCollision
noncomputable section
open Finset
variable {α : Type*} [DecidableEq α]

def count (a : α) (l : List (α × Bool)) : ℕ := (l.map Prod.fst).count a

@[simp] lemma count_cons (a c : α) (b : Bool) (l : List (α × Bool)) :
    count a ((c,b)::l) = (if c=a then 1 else 0) + count a l := by
  by_cases h : c=a <;> simp [count, h, Nat.add_comm]

lemma count_parity (a : α) (l : List (α × Bool)) :
    Multiplicative.toAdd ((FreeGroup.lift
      (fun c : α => Multiplicative.ofAdd (if c=a then (1 : ZMod 2) else 0)))
        (FreeGroup.mk l)) = (count a l : ZMod 2) := by
  induction l with
  | nil => simp [count, ← FreeGroup.one_eq_mk]
  | cons p l ih =>
    rcases p with ⟨c,b⟩
    change Multiplicative.toAdd ((FreeGroup.lift _)
      (FreeGroup.mk ([(c,b)] ++ l))) = _
    rw [← FreeGroup.mul_mk, map_mul, toAdd_mul, ih, count_cons, Nat.cast_add]
    congr 1
    cases b
    · change Multiplicative.toAdd ((FreeGroup.lift _)
        (FreeGroup.of c)⁻¹) = _
      rw [map_inv, toAdd_inv, FreeGroup.lift_apply_of]
      by_cases h : c=a <;> simp [h]
    · change Multiplicative.toAdd ((FreeGroup.lift _) (FreeGroup.of c)) = _
      rw [FreeGroup.lift_apply_of]
      by_cases h : c=a <;> simp [h]

lemma combined_count_ne_one {l k : List (α × Bool)} (h : FreeGroup.mk l = FreeGroup.mk k)
    (a : α) : count a l + count a k ≠ 1 := by
  have hp : (count a l : ZMod 2) = (count a k : ZMod 2) := by
    simpa only [count_parity] using congrArg (fun g => Multiplicative.toAdd
      ((FreeGroup.lift (fun c : α => Multiplicative.ofAdd
        (if c=a then (1 : ZMod 2) else 0))) g)) h
  intro hc
  have hc' : count a l=1 ∧ count a k=0 ∨ count a l=0 ∧ count a k=1 := by omega
  rcases hc' with ⟨hl,hk⟩|⟨hl,hk⟩ <;> simp [hl,hk] at hp

lemma count_reduce_le (a : α) (l : List (α × Bool)) :
    count a (FreeGroup.reduce l) ≤ count a l := by
  exact (((FreeGroup.reduce.red (L:=l)).sublist).map Prod.fst).count_le a

lemma exists_repeat_of_not_nodup (l : List α) (h : ¬ l.Nodup) :
    ∃ a, 2 ≤ l.count a := by
  by_contra! hn
  apply h
  rw [List.nodup_iff_count_le_one]
  intro a
  exact Nat.le_of_lt_succ (hn a)

variable [Fintype α]

lemma sum_count (l : List (α × Bool)) : ∑ a : α, count a l = l.length := by
  induction l with
  | nil => simp [count]
  | cons p l ih =>
    rcases p with ⟨a,b⟩
    simp only [count_cons, sum_add_distrib, ih, List.length_cons]
    simp [Nat.add_comm]

theorem range_card_le_of_repeated_reduction {l k : List (α × Bool)} {L : ℕ}
    (hl : l.length=L) (hk : k.length=L)
    (he : FreeGroup.mk l = FreeGroup.mk k)
    (hbad : ¬ ((FreeGroup.reduce l).map Prod.fst).Nodup) :
    ((l.map Prod.fst ++ k.map Prod.fst).toFinset).card + 1 ≤ L := by
  obtain ⟨a, ha⟩ := exists_repeat_of_not_nodup _ hbad
  change 2 ≤ count a (FreeGroup.reduce l) at ha
  have hal : 2 ≤ count a l := ha.trans (count_reduce_le a l)
  have hred : FreeGroup.reduce l = FreeGroup.reduce k := congrArg FreeGroup.toWord he
  have hak : 2 ≤ count a k := by rw [hred] at ha; exact ha.trans (count_reduce_le a k)
  let s := (l.map Prod.fst ++ k.map Prod.fst).toFinset
  have has : a∈s := by
    simp only [s, List.mem_toFinset, List.mem_append]
    left
    exact List.count_pos_iff.mp (show 0 < count a l by omega)
  have hs (b : α) (hb : b∈s) : 2 ≤ count b l + count b k := by
    have hpos : 0 < count b l + count b k := by
      change 0 < (l.map Prod.fst).count b + (k.map Prod.fst).count b
      rw [← List.count_append]
      exact List.count_pos_iff.mpr (List.mem_toFinset.mp hb)
    have hne := combined_count_ne_one he b
    omega
  have hsum : ∑ b ∈ s, (count b l + count b k) = 2*L := by
    rw [sum_subset (subset_univ s)]
    · rw [sum_add_distrib, sum_count, sum_count, hl, hk]; omega
    · intro b _ hb
      have hb' : b ∉ l.map Prod.fst ∧ b ∉ k.map Prod.fst := by
        simpa only [s, List.mem_toFinset, List.mem_append, not_or] using hb
      simp [count, List.count_eq_zero.mpr hb'.1, List.count_eq_zero.mpr hb'.2]
  have hlower : 2*s.card + 2 ≤ ∑ b ∈ s, (count b l + count b k) := by
    calc
      2*s.card+2 = ∑ b ∈ s, (2 + if b=a then 2 else 0) := by
        simp [sum_add_distrib, has, Nat.mul_comm]
      _ ≤ _ := sum_le_sum fun b hb => by
        by_cases hba : b=a
        · subst b; simp; omega
        · simpa [hba] using hs b hb
  rw [hsum] at hlower
  change s.card + 1 ≤ L
  omega

end
end HochschildCollision

namespace HochschildBlockWords
noncomputable section
open List FreeGroup HochschildCatalanWords
variable {α : Type*}

@[simp] lemma length_signed (b : Bool) (l : List α) : (signed b l).length = l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp [signed, ih]

def Ends (b : Bool) (w : List (α × Bool)) : Prop :=
  (∃ a l, w = (a,b)::l) ∧ (∃ l a, w = l ++ [(a,b)])

lemma signed_odd_ends (l : List α) (hl : l.length % 2 = 1) (b : Bool) :
    Ends b (signed b l) := by
  induction l using List.twoStepInduction generalizing b with
  | nil => simp at hl
  | singleton a => exact ⟨⟨a, [], rfl⟩, ⟨[], a, rfl⟩⟩
  | cons_cons a c l ih _ =>
    have hl' : l.length % 2 = 1 := by simp only [List.length_cons] at hl; omega
    obtain ⟨_, ⟨k,d,hk⟩⟩ := ih hl' b
    exact ⟨⟨a, (c,!b) :: signed b l, by simp [signed]⟩,
      ⟨(a,b)::(c,!b)::k, d, by simp [signed, hk]⟩⟩

variable [DecidableEq α]

lemma reduce_signed_odd_ends (l : List α) (hl : l.length % 2 = 1) (b : Bool) :
    Ends b (reduce (signed b l)) := by
  have hr := (reduce.red (L:=signed b l)).length
  rw [reduce_signed, length_signed, length_signed] at hr
  obtain ⟨n,hn⟩ := hr
  have hp : (unorientedReduce l).length % 2 = 1 := by omega
  rw [reduce_signed]
  exact signed_odd_ends _ hp b

omit [DecidableEq α] in
lemma ends_append {l k : List (α × Bool)} {b : Bool} (hl : Ends b l) (hk : Ends b k) :
    Ends b (l++k) := by
  obtain ⟨⟨a,v,rfl⟩,_⟩ := hl
  obtain ⟨_,⟨w,c,rfl⟩⟩ := hk
  exact ⟨⟨a,v++(w++[(c,b)]),rfl⟩,
    ⟨((a,b)::v)++w,c, by simp [List.append_assoc]⟩⟩

omit [DecidableEq α] in
lemma reduced_append_of_ends {l k : List (α × Bool)} {b : Bool}
    (hl : IsReduced l) (hk : IsReduced k) (hel : Ends b l) (hek : Ends b k) :
    IsReduced (l++k) := by
  obtain ⟨_,⟨v,a,rfl⟩⟩ := hel
  obtain ⟨⟨c,w,rfl⟩,_⟩ := hek
  change List.IsChain _ _
  rw [List.append_assoc, List.singleton_append, List.isChain_append_cons_cons]
  exact ⟨hl,fun _ => rfl,hk⟩

theorem reduce_append_odd_blocks (l k : List (α × Bool)) {b : Bool}
    (hl : Ends b (reduce l)) (hk : Ends b (reduce k)) :
    reduce (l++k) = reduce l ++ reduce k ∧ Ends b (reduce (l++k)) := by
  have hr : IsReduced (reduce l ++ reduce k) := reduced_append_of_ends
    (IsReduced.of_reduce_eq (by simp)) (IsReduced.of_reduce_eq (by simp)) hl hk
  have he : reduce (l++k) = reduce l ++ reduce k := by
    rw [← reduce_append_reduce_reduce, hr.reduce_eq]
  exact ⟨he,he ▸ ends_append hl hk⟩

end
end HochschildBlockWords

namespace HochschildIndexedHaagerup
noncomputable section
open Finset
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable {G : Type*} [Group G] [DecidableEq G]
variable (τ : A →ₚ[ℂ] ℂ) (u : G →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : G, g ≠ 1 → τ (u g) = 0)
include hτ hu hfree

lemma norm_sum_sq {I : Type*} [Fintype I] (g : I → G) :
    ‖τ.toPreGNS (∑ i, u (g i))‖^2 =
      Fintype.card {p : I × I // g p.1 = g p.2} := by
  classical
  have hi : inner ℂ (τ.toPreGNS (∑ i, u (g i)))
      (τ.toPreGNS (∑ i, u (g i))) =
      (Fintype.card {p : I × I // g p.1 = g p.2} : ℂ) := by
    simp only [map_sum, sum_inner, inner_sum,
      HochschildTracePolynomial.inner_word τ u hτ hu hfree]
    simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum, apply_ite,
      Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type]
    exact Finset.sum_comm
  apply Complex.ofReal_injective
  simpa [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow] using hi

end
end HochschildIndexedHaagerup

namespace HochschildIndexedHaagerup
noncomputable section
open Finset HochschildTransfer
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)
include hτ hu hfree htr hfaith

lemma norm_sum_le {I : Type*} [Fintype I] (g : I → FreeGroup α) (q : ℕ)
    (hq : ∀ i, (g i).toWord.length = q) :
    ‖∑ i, u (g i)‖ ≤ (q+1:ℝ) *
      Real.sqrt (Fintype.card {p : I × I // g p.1 = g p.2}) := by
  classical
  let p : Polynomial α := ∑ i, MonoidAlgebra.single (g i) (1:ℂ)
  have hp : ∀ x ∈ p.coeff.support, x.toWord.length = q := by
    intro x hx
    have hx' : (∑ i : I, if g i = x then (1:ℂ) else 0) ≠ 0 := by
      simpa only [p, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        MonoidAlgebra.coeff_single, Finsupp.single_apply] using Finsupp.mem_support_iff.mp hx
    obtain ⟨i,_,hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx'
    have he : g i = x := by by_contra h; simp [h] at hi
    simpa only [← he] using hq i
  have he : MonoidAlgebra.lift ℂ A (FreeGroup α) u p = ∑ i, u (g i) := by
    simp only [p,map_sum,MonoidAlgebra.lift_single,one_smul]
  have h := norm_eval_homogeneous_le τ u hτ hu hfree htr hfaith p q hp
  rw [he] at h
  have hn := norm_sum_sq τ u hτ hu hfree g
  have he' : ‖τ.toPreGNS (∑ i, u (g i))‖ =
      Real.sqrt (Fintype.card {p : I × I // g p.1 = g p.2}) := by
    rw [← hn, Real.sqrt_sq (norm_nonneg _)]
  simpa only [he'] using h

end
end HochschildIndexedHaagerup

namespace HochschildRangeCount
noncomputable section
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev SmallRange (n k : ℕ) :=
  {f : Fin n → α // (Finset.univ.image f).card ≤ k}

def composeSmall {n k : ℕ} (p : (Fin k → α) × (Fin n → Fin k)) : SmallRange (α:=α) n k :=
  ⟨p.1 ∘ p.2, (card_le_card (by
    intro a ha
    obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    exact mem_image.mpr ⟨p.2 i, mem_univ _, rfl⟩ :
    univ.image (p.1 ∘ p.2) ⊆ univ.image p.1)).trans
      (card_image_le.trans (by simp))⟩

omit [Fintype α] in
lemma composeSmall_surjective [Nonempty α] (n k : ℕ) :
    Function.Surjective (composeSmall (α:=α) (n:=n) (k:=k)) := by
  classical
  let : Inhabited α := Classical.inhabited_of_nonempty ‹Nonempty α›
  intro h
  let s := Finset.univ.image h.val
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card ↥s ≤ Fintype.card (Fin k) by simpa only [Fintype.card_coe, Fintype.card_fin] using h.property)
  let f : Fin k → α := Function.extend e Subtype.val (fun _ => default)
  let g : Fin n → Fin k := fun i => e ⟨h.val i, by simp [s]⟩
  refine ⟨(f,g), Subtype.ext ?_⟩
  funext i
  exact e.injective.extend_apply Subtype.val (fun _ => default) ⟨h.val i, by simp [s]⟩

theorem card_smallRange_le [Nonempty α] (n k : ℕ) :
    Fintype.card (SmallRange (α:=α) n k) ≤ (Fintype.card α)^k * k^n := by
  have h := Fintype.card_le_of_surjective _ (composeSmall_surjective (α:=α) n k)
  simpa only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin] using h

end
end HochschildRangeCount

namespace HochschildCollision
noncomputable section
open Finset HochschildRangeCount
variable {α : Type*} [Fintype α] [DecidableEq α]

def tupleWord {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) : List (α × Bool) :=
  List.ofFn fun i => (f i, σ i)

omit [Fintype α] [DecidableEq α] in
@[simp] lemma tupleWord_length {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) :
    (tupleWord σ f).length = L := by simp [tupleWord]

omit [Fintype α] [DecidableEq α] in
@[simp] lemma tupleWord_map {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) :
    (tupleWord σ f).map Prod.fst = List.ofFn f := by simp [tupleWord, List.map_ofFn, Function.comp_def]

abbrev BadPairs {L : ℕ} (σ : Fin L → Bool) :=
  {p : (Fin L → α) × (Fin L → α) //
    FreeGroup.mk (tupleWord σ p.1) = FreeGroup.mk (tupleWord σ p.2) ∧
      ¬ ((FreeGroup.reduce (tupleWord σ p.1)).map Prod.fst).Nodup}

omit [Fintype α] in
lemma ofFn_toFinset {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).toFinset = univ.image f := by
  ext a
  simp

def pairToSmall {L : ℕ} (σ : Fin L → Bool) (p : BadPairs (α:=α) σ) :
    SmallRange (α:=α) (L+L) (L-1) := by
  refine ⟨Fin.append p.val.1 p.val.2, ?_⟩
  have h := range_card_le_of_repeated_reduction
    (tupleWord_length σ p.val.1) (tupleWord_length σ p.val.2) p.property.1 p.property.2
  rw [tupleWord_map,tupleWord_map, ← List.ofFn_fin_append, ofFn_toFinset] at h
  omega

lemma pairToSmall_injective {L : ℕ} (σ : Fin L → Bool) :
    Function.Injective (pairToSmall (α:=α) σ) := by
  intro p q hpq
  have h : Fin.append p.val.1 p.val.2 = Fin.append q.val.1 q.val.2 :=
    congrArg Subtype.val hpq
  apply Subtype.ext
  apply Prod.ext
  · funext i
    simpa only [Fin.append_left] using congrFun h (Fin.castAdd L i)
  · funext i
    simpa only [Fin.append_right] using congrFun h (Fin.natAdd L i)

theorem card_badPairs_le [Nonempty α] {L : ℕ} (σ : Fin L → Bool) :
    Fintype.card (BadPairs (α:=α) σ) ≤ (Fintype.card α)^(L-1) * (L-1)^(2*L) := by
  have h := Fintype.card_le_of_injective (pairToSmall (α:=α) σ) (pairToSmall_injective (α:=α) σ)
  exact h.trans (by simpa only [two_mul] using card_smallRange_le (α:=α) (L+L) (L-1))

end
end HochschildCollision

namespace HochschildBlockError
noncomputable section
open Finset HochschildCollision HochschildIndexedHaagerup
variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev BadTerms {L : ℕ} (σ : Fin L → Bool) (q : ℕ) :=
  {f : Fin L → α // (FreeGroup.mk (tupleWord σ f)).toWord.length = q ∧
    ¬ ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup}

def wordOf {L : ℕ} (σ : Fin L → Bool) (f : Fin L → α) : FreeGroup α :=
  FreeGroup.mk (tupleWord σ f)

def pairToBad {L : ℕ} (σ : Fin L → Bool) (q : ℕ)
    (p : {p : BadTerms (α:=α) σ q × BadTerms (α:=α) σ q //
      wordOf σ p.1.val = wordOf σ p.2.val}) : BadPairs (α:=α) σ :=
  ⟨(p.val.1.val,p.val.2.val),p.property,p.val.1.property.2⟩

omit [Fintype α] in
lemma pairToBad_injective {L : ℕ} (σ : Fin L → Bool) (q : ℕ) :
    Function.Injective (pairToBad (α:=α) σ q) := by
  intro p z hpz
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun p : BadPairs (α:=α) σ => p.val.1) hpz
  · apply Subtype.ext
    exact congrArg (fun p : BadPairs (α:=α) σ => p.val.2) hpz

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
variable (hτ : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
variable (hfree : ∀ g : FreeGroup α, g ≠ 1 → τ (u g) = 0)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)

def badSum {L : ℕ} (σ : Fin L → Bool) (q : ℕ) : A :=
  ∑ f : BadTerms (α:=α) σ q, u (wordOf σ f.val)

include hτ hu hfree htr hfaith in
lemma badSum_norm_le [Nonempty α] {L : ℕ} (σ : Fin L → Bool) (q : ℕ) :
    ‖badSum u σ q‖ ≤ (q+1:ℝ) *
      Real.sqrt ((Fintype.card α:ℝ)^(L-1) * (L-1:ℕ)^(2*L)) := by
  have hb := norm_sum_le τ u hτ hu hfree htr hfaith
    (fun f : BadTerms (α:=α) σ q => wordOf σ f.val) q (fun f => f.property.1)
  have hc := Fintype.card_le_of_injective (pairToBad (α:=α) σ q) (pairToBad_injective σ q)
  have hc' := hc.trans (card_badPairs_le (α:=α) σ)
  have hreal : (Fintype.card {p : BadTerms (α:=α) σ q × BadTerms (α:=α) σ q //
      wordOf σ p.1.val = wordOf σ p.2.val} : ℝ) ≤
      (Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L) := by exact_mod_cast hc'
  exact hb.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hreal) (by positivity))

def normalizer (r L : ℕ) : ℝ := (Real.sqrt r)⁻¹ ^ L

lemma normalizer_nonneg (r L : ℕ) : 0 ≤ normalizer r L := by unfold normalizer; positivity

lemma normalizer_sq (r L : ℕ) : normalizer r L ^ 2 = ((r:ℝ)^L)⁻¹ := by
  unfold normalizer
  rw [← pow_mul, Nat.mul_comm L 2, pow_mul, inv_pow,
    Real.sq_sqrt (by positivity), inv_pow]

lemma normalizer_cancel {r L : ℕ} (hr : 0 < r) (hL : 0 < L) :
    normalizer r L ^ 2 * (r:ℝ)^(L-1) = (r:ℝ)⁻¹ := by
  rw [normalizer_sq]
  have hr' : (r:ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have hp : (r:ℝ)^L = (r:ℝ)^(L-1) * r := by
    simpa only [pow_succ] using congrArg (fun n : ℕ => (r:ℝ)^n) (show L = (L-1)+1 by omega)
  rw [hp]
  field_simp

include hτ hu hfree htr hfaith in

theorem normalized_badSum_sq_le [Nonempty α] {L : ℕ} (hL : 0 < L)
    (σ : Fin L → Bool) (q : ℕ) :
    ‖normalizer (Fintype.card α) L • badSum u σ q‖^2 ≤
      ((q+1:ℝ)^2 * (L-1:ℕ)^(2*L)) / Fintype.card α := by
  have hn := badSum_norm_le τ u hτ hu hfree htr hfaith σ q
  have hc : 0 ≤ (Fintype.card α:ℝ)^(L-1) * (L-1:ℕ)^(2*L) := by positivity
  have hn' : ‖badSum u σ q‖^2 ≤
      (q+1:ℝ)^2 * ((Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L)) := by
    have h := sq_le_sq₀ (norm_nonneg (badSum u σ q)) (by positivity :
      0 ≤ (q+1:ℝ)*Real.sqrt ((Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L)))
    have h' := h.mpr hn
    simpa only [mul_pow, Real.sq_sqrt hc] using h'
  calc
    _ = normalizer (Fintype.card α) L ^ 2 * ‖badSum u σ q‖^2 := by
      rw [norm_smul, Real.norm_of_nonneg (normalizer_nonneg _ _),mul_pow]
    _ ≤ normalizer (Fintype.card α) L ^ 2 *
        ((q+1:ℝ)^2 * ((Fintype.card α:ℝ)^(L-1)*(L-1:ℕ)^(2*L))) :=
      mul_le_mul_of_nonneg_left hn' (sq_nonneg _)
    _ = (normalizer (Fintype.card α) L ^ 2 * (Fintype.card α:ℝ)^(L-1)) *
        ((q+1:ℝ)^2*(L-1:ℕ)^(2*L)) := by ring
    _ = _ := by rw [normalizer_cancel Fintype.card_pos hL]; ring

end

noncomputable section
open Filter
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ) (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
variable (hτ : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
variable (hfree : ∀ r (g : FreeGroup (Fin (r+1))), g ≠ 1 → τ (u r g) = 0)
variable (htr : ∀ a b : A, τ (a*b) = τ (b*a))
variable (hfaith : ∀ a : A, τ (star a*a) = 0 → a = 0)
include hτ hu hfree htr hfaith

theorem tendsto_normalized_badSum {L : ℕ} (hL : 0 < L) (σ : Fin L → Bool) (q : ℕ) :
    Tendsto (fun r => normalizer (r+1) L • badSum (u r) σ q) atTop (𝓝 0) := by
  have hsq : Tendsto (fun r => ‖normalizer (r+1) L • badSum (u r) σ q‖^2)
      atTop (𝓝 0) := by
    have hb (r : ℕ) : ‖normalizer (r+1) L • badSum (u r) σ q‖^2 ≤
        ((q+1:ℝ)^2 * (L-1:ℕ)^(2*L)) / ((r:ℝ)+1) := by
      simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
        normalized_badSum_sq_le τ (u r) hτ (hu r) (hfree r) htr hfaith hL σ q
    exact squeeze_zero (fun r => sq_nonneg _) hb
      (tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt

theorem tendsto_total_badSum {L : ℕ} (hL : 0 < L) (σ : Fin L → Bool) :
    Tendsto (fun r => ∑ q ∈ Finset.range (L+1),
      normalizer (r+1) L • badSum (u r) σ q) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    tendsto_finsetSum (Finset.range (L+1))
      (fun q _ => tendsto_normalized_badSum τ u hτ hu hfree htr hfaith hL σ q)
end
end HochschildBlockError
end
end OAI
end

section
namespace OAI

noncomputable section

namespace HochschildRigidity
open Finset

theorem norm_sum_smul_le_of_antitone
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℕ → ℝ) (z : ℕ → E) (B : ℝ) (hf : ∀ i, 0 ≤ f i)
    (hfmono : Antitone f) (hB : 0 ≤ B)
    (hz : ∀ k, ‖∑ i ∈ range k, z i‖ ≤ B) (n : ℕ) :
    ‖∑ i ∈ range n, f i • z i‖ ≤ f 0 * B := by
  cases n with
  | zero => simpa using mul_nonneg (hf 0) hB
  | succ n =>
    rw [sum_range_by_parts, Nat.succ_sub_one]
    have hd (i : ℕ) : 0 ≤ f i - f (i + 1) := sub_nonneg.mpr (hfmono (Nat.le_succ i))
    have heq : -(∑ i ∈ range n, (f (i + 1) - f i) • ∑ j ∈ range (i + 1), z j) =
        ∑ i ∈ range n, (f i - f (i + 1)) • ∑ j ∈ range (i + 1), z j := by
      simp only [← Finset.sum_neg_distrib, ← neg_smul, neg_sub]
    rw [sub_eq_add_neg, heq]
    calc
      _ ≤ ‖f n • ∑ i ∈ range (n + 1), z i‖ +
          ‖∑ i ∈ range n, (f i - f (i + 1)) • ∑ j ∈ range (i + 1), z j‖ := norm_add_le _ _
      _ ≤ f n * B + ∑ i ∈ range n, (f i - f (i + 1)) * B := by
        apply add_le_add
        · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf n)]
          exact mul_le_mul_of_nonneg_left (hz _) (hf n)
        · refine (norm_sum_le _ _).trans (sum_le_sum (fun i _ => ?_))
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hd i)]
          exact mul_le_mul_of_nonneg_left (hz _) (hd i)
      _ = f 0 * B := by
        rw [← sum_mul, sum_range_sub']
        ring

theorem abs_sum_sin_le (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi)
    (b : ℝ) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (t * i + b)| ≤ Real.pi / t := by
  have hspos : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hprod : Real.sin (t / 2) * |∑ i ∈ range n, Real.sin (t * i + b)| ≤ 1 := by
    have heq := congrArg abs (Real.sin_mul_sum_sin n t b)
    rw [abs_mul, abs_of_pos hspos, abs_mul] at heq
    rw [heq]
    calc
      _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)
      _ ≤ 1 := by simpa using Real.abs_sin_le_one _
  have hsin : t / Real.pi ≤ Real.sin (t / 2) := by
    simpa using Real.mul_le_sin (x := t / 2) (by positivity) (by linarith)
  calc
    _ ≤ 1 / Real.sin (t / 2) := (le_div_iff₀ hspos).mpr (by nlinarith [hprod])
    _ ≤ Real.pi / t := (div_le_div_iff₀ hspos ht).mpr (by
      have h := (div_le_iff₀ Real.pi_pos).mp hsin
      nlinarith)

theorem abs_harmonic_sin_tail_le (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi)
    (p : ℕ) (hp : 0 < p) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((p + i : ℕ) : ℝ) * t) / (p + i)| ≤
      Real.pi / (t * p) := by
  let f : ℕ → ℝ := fun i => 1 / (p + i : ℕ)
  let z : ℕ → ℝ := fun i => Real.sin (((p + i : ℕ) : ℝ) * t)
  have hf (i : ℕ) : 0 ≤ f i := by dsimp [f]; positivity
  have hfm : Antitone f := by
    intro i j hij
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast Nat.add_le_add_left hij p
  have hz (k : ℕ) : ‖∑ i ∈ range k, z i‖ ≤ Real.pi / t := by
    simpa [z, Real.norm_eq_abs, Nat.cast_add, add_mul, mul_add, mul_comm, add_comm] using
      abs_sum_sin_le t ht htpi (p * t) k
  have h := norm_sum_smul_le_of_antitone f z (Real.pi / t) hf hfm
    (by positivity) hz n
  simpa [f, z, Real.norm_eq_abs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h

theorem abs_harmonic_sin_prefix_le (t : ℝ) (ht : 0 ≤ t) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| ≤ n * t := by
  calc
    _ ≤ ∑ i ∈ range n, |Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range n, t := by
      apply sum_le_sum
      intro i _
      have hi : (0 : ℝ) < i + 1 := by positivity
      rw [abs_div, abs_of_pos hi]
      apply (div_le_iff₀ hi).mpr
      have h := Real.abs_sin_le_abs (x := ((i + 1 : ℕ) : ℝ) * t)
      rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ht)] at h
      simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
    _ = n * t := by simp

theorem abs_harmonic_sin_le_pos (t : ℝ) (ht : 0 < t) (htpi : t ≤ Real.pi)
    (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| ≤ 1 + Real.pi := by
  let K : ℕ := ⌊1 / t⌋₊
  have hK : (K : ℝ) * t ≤ 1 := by
    have h := Nat.floor_le (show 0 ≤ 1 / t by positivity)
    exact (le_div_iff₀ ht).mp h
  by_cases hn : n ≤ K
  · calc
      _ ≤ (n : ℝ) * t := abs_harmonic_sin_prefix_le t ht.le n
      _ ≤ (K : ℝ) * t := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) ht.le
      _ ≤ 1 := hK
      _ ≤ 1 + Real.pi := by linarith [Real.pi_pos]
  · have hKn : K ≤ n := by omega
    have hp : (0 : ℝ) < t * (K + 1) := by positivity
    have htK : 1 ≤ t * (K + 1) := by
      have h : 1 / t < (K : ℝ) + 1 := Nat.lt_floor_add_one (1 / t)
      have h' := (div_lt_iff₀ ht).mp h
      nlinarith
    have htail := abs_harmonic_sin_tail_le t ht htpi (K + 1) (by omega) (n - K)
    have htail' :
        |∑ i ∈ range (n - K), Real.sin (((K + i + 1 : ℕ) : ℝ) * t) / (K + i + 1)|
          ≤ Real.pi := by
      calc
        _ ≤ Real.pi / (t * (K + 1)) := by
          simpa [Nat.cast_add, Nat.cast_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            add_assoc, add_comm, add_left_comm] using htail
        _ ≤ Real.pi := (div_le_iff₀ hp).mpr (by nlinarith [Real.pi_pos])
    rw [show n = K + (n - K) by omega, sum_range_add]
    calc
      _ ≤ |∑ i ∈ range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| +
          |∑ i ∈ range (n - K), Real.sin (((K + i + 1 : ℕ) : ℝ) * t) / (K + i + 1)| :=
        by
          simpa only [Nat.cast_add] using
            (abs_add_le
              (∑ i ∈ range K, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1))
              (∑ i ∈ range (n - K),
                Real.sin (((K + i + 1 : ℕ) : ℝ) * t) / (K + i + 1)))
      _ ≤ (K : ℝ) * t + Real.pi := add_le_add
        (abs_harmonic_sin_prefix_le t ht.le K) htail'
      _ ≤ 1 + Real.pi := by linarith

theorem abs_harmonic_sin_le (t : ℝ) (ht : |t| ≤ Real.pi) (n : ℕ) :
    |∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * t) / (i + 1)| ≤ 1 + Real.pi := by
  rcases lt_trichotomy 0 t with hpos | rfl | hneg
  · exact abs_harmonic_sin_le_pos t hpos ((le_abs_self _).trans ht) n
  · simp only [mul_zero, Real.sin_zero, zero_div, sum_const_zero, abs_zero]
    positivity
  · have h := abs_harmonic_sin_le_pos (-t) (by linarith) (by
        simpa only [abs_of_neg hneg] using ht) n
    simpa only [mul_neg, Real.sin_neg, neg_div, sum_neg_distrib, abs_neg] using h

noncomputable def harmonicPolynomial {A : Type*} [Ring A] [Algebra ℂ A]
    (n : ℕ) (x : A) : A :=
  ∑ i ∈ range n, ((i + 1 : ℂ)⁻¹) • x ^ (i + 1)

theorem harmonicPolynomial_im (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    (harmonicPolynomial n z).im =
      ∑ i ∈ range n, Real.sin (((i + 1 : ℕ) : ℝ) * z.arg) / (i + 1) := by
  have hpower (k : ℕ) : (z ^ k).im = Real.sin ((k : ℝ) * z.arg) := by
    have hzrep := Complex.norm_mul_cos_add_sin_mul_I z
    rw [hz, Complex.ofReal_one, one_mul] at hzrep
    have h := congrArg Complex.im (Complex.cos_add_sin_mul_I_pow k (z.arg : ℂ))
    rw [hzrep] at h
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero,
      zero_add] using h
  simp only [harmonicPolynomial, Complex.im_sum, smul_eq_mul]
  apply sum_congr rfl
  intro i _
  rw [show (i + 1 : ℂ)⁻¹ = (((i + 1 : ℝ)⁻¹ : ℝ) : ℂ) by simp]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, hpower]
  ring

theorem norm_harmonicPolynomial_sub_star_le (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖harmonicPolynomial n z - star (harmonicPolynomial n z)‖ ≤
      2 * (1 + Real.pi) := by
  have h := abs_harmonic_sin_le z.arg (Complex.abs_arg_le_pi z) n
  rw [← harmonicPolynomial_im z hz n] at h
  change ‖harmonicPolynomial n z - (starRingEnd ℂ) (harmonicPolynomial n z)‖ ≤ _
  rw [Complex.sub_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

theorem norm_unitary_harmonicPolynomial_sub_star_le {A : Type*} [CStarAlgebra A]
    (u : unitary A) (n : ℕ) :
    ‖harmonicPolynomial n (u : A) - star (harmonicPolynomial n (u : A))‖ ≤
      2 * (1 + Real.pi) := by
  have hcfc : cfc (harmonicPolynomial n : ℂ → ℂ) (u : A) =
      harmonicPolynomial n (u : A) := by
    unfold harmonicPolynomial
    rw [show (fun x : ℂ => ∑ i ∈ range n, ((i + 1 : ℂ)⁻¹) • x ^ (i + 1)) =
        ∑ i ∈ range n, (fun x : ℂ => ((i + 1 : ℂ)⁻¹) • x ^ (i + 1)) by
      ext; simp only [Finset.sum_apply]]
    rw [cfc_sum (fun (i : ℕ) (x : ℂ) => ((i + 1 : ℂ)⁻¹) • x ^ (i + 1))
      (u : A) (range n) (by intro i _; fun_prop)]
    apply sum_congr rfl
    intro i _
    rw [cfc_smul ((i + 1 : ℂ)⁻¹) (fun x : ℂ => x ^ (i + 1)) (u : A) (by fun_prop),
      cfc_pow_id (R := ℂ) (u : A) (i + 1)]
  have hcont : Continuous (harmonicPolynomial n : ℂ → ℂ) := by
    unfold harmonicPolynomial
    fun_prop
  have h := norm_cfc_le (a := (u : A)) (f := fun z : ℂ =>
      harmonicPolynomial n z - star (harmonicPolynomial n z))
    (show 0 ≤ 2 * (1 + Real.pi) by positivity)
    (fun z hz => norm_harmonicPolynomial_sub_star_le z
      (spectrum.norm_eq_one_of_unitary u.property hz) n)
  rwa [cfc_sub _ _ _ hcont.continuousOn hcont.star.continuousOn, cfc_star, hcfc] at h

section FourierWindows
variable {L : ℕ} [NeZero L]

lemma sum_stdAddChar_mul (t : ZMod L) :
    ∑ j : ZMod L, ZMod.stdAddChar (t * j) = if t = 0 then (L : ℂ) else 0 := by
  split_ifs with ht
  · simp [ht]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar L ht)

theorem sum_dft_mul_star_dft {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (f g : ZMod L → A) :
    ∑ j : ZMod L, ZMod.dft f j * star (ZMod.dft g j) =
      (L : ℂ) • ∑ k : ZMod L, f k * star (g k) := by
  simp only [ZMod.dft_apply, star_sum, star_smul, sum_mul, mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_sum, smul_smul]
  simp only [Complex.star_def, ← AddChar.map_neg_eq_conj, neg_neg,
    ← AddChar.map_add_eq_mul, ← sub_eq_add_neg, ← sub_mul]
  rw [sum_comm]
  conv_lhs =>
    enter [2, k]
    rw [sum_comm]
  simp only [← sum_smul, sum_stdAddChar_mul, sub_eq_zero, ite_smul, zero_smul,
    sum_ite_eq, mem_univ, ite_true, ← smul_sum]

noncomputable def rootUnitary (j : ZMod L) : unitary ℂ :=
  ⟨ZMod.stdAddChar j, by
    rw [Unitary.mem_iff]
    simp only [Complex.star_def, ← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul,
      neg_add_cancel, add_neg_cancel, AddChar.map_zero_eq_one, and_self]⟩

@[simp] lemma rootUnitary_coe (j : ZMod L) :
    (rootUnitary j : ℂ) = ZMod.stdAddChar j := rfl

noncomputable def fourierWindow {A : Type*} [Ring A] [Algebra ℂ A]
    (u : A) (j : ZMod L) : A :=
  (L : ℂ)⁻¹ • ZMod.dft (fun k : ZMod L => u ^ k.val) j

lemma sum_fourierWindow_mul_star {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (u : unitary A) :
    ∑ j : ZMod L, fourierWindow (u : A) j * star (fourierWindow (u : A) j) = 1 := by
  have hpow (k : ZMod L) : (u : A) ^ k.val * star ((u : A) ^ k.val) = 1 := by
    simpa only [Unitary.coe_star, SubmonoidClass.coe_pow] using Unitary.coe_mul_star_self (u ^ k.val)
  simp only [fourierWindow, star_smul, smul_mul_smul_comm, star_inv₀, star_natCast,
    ← smul_sum, sum_dft_mul_star_dft, hpow, sum_const, card_univ, ZMod.card]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, smul_smul]
  have hL : (L : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  rw [show (L : ℂ)⁻¹ * (L : ℂ)⁻¹ * (L : ℂ) * (L : ℂ) = 1 by field_simp]
  exact one_smul _ _

lemma sum_zmod_val {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    ∑ k : ZMod L, f k.val = ∑ k ∈ range L, f k := by
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ L => exact Fin.sum_univ_eq_sum_range f (L + 1)

lemma fourierWindow_eq_geometric {A : Type*} [Ring A] [Algebra ℂ A]
    (u : A) (j : ZMod L) :
    fourierWindow u j = (L : ℂ)⁻¹ •
      ∑ k ∈ range L, (ZMod.stdAddChar (-j) • u) ^ k := by
  unfold fourierWindow
  rw [ZMod.dft_apply]
  congr 1
  calc
    _ = ∑ k : ZMod L, (ZMod.stdAddChar (-j) • u) ^ k.val := by
      apply sum_congr rfl
      intro k _
      rw [smul_pow, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
        ZMod.natCast_zmod_val, mul_neg]
    _ = _ := sum_zmod_val _

lemma norm_unitary_mul_fourierWindow_sub_le {A : Type*} [CStarAlgebra A]
    [Nontrivial A] (u : unitary A) (j : ZMod L) :
    ‖((rootUnitary (-j) • u : unitary A) : A) * fourierWindow (u : A) j -
      fourierWindow (u : A) j‖ ≤ 2 / (L : ℝ) := by
  let v : unitary A := rootUnitary (-j) • u
  have hq : fourierWindow (u : A) j =
      (L : ℂ)⁻¹ • ∑ k ∈ range L, (v : A) ^ k := fourierWindow_eq_geometric _ _
  have heq : (v : A) * fourierWindow (u : A) j - fourierWindow (u : A) j =
      (L : ℂ)⁻¹ • ((v : A) ^ L - 1) := by
    rw [← sub_one_mul, hq, mul_smul_comm, mul_geom_sum]
  change ‖(v : A) * fourierWindow (u : A) j - fourierWindow (u : A) j‖ ≤ _
  rw [heq, norm_smul, norm_inv, Complex.norm_natCast]
  have hpow : ‖(v : A) ^ L‖ = 1 := by
    simpa only [SubmonoidClass.coe_pow] using CStarRing.norm_coe_unitary (v ^ L)
  calc
    _ ≤ (L : ℝ)⁻¹ * (‖(v : A) ^ L‖ + ‖(1 : A)‖) := by gcongr; exact norm_sub_le _ _
    _ = _ := by rw [hpow, norm_one]; ring

lemma norm_unitary_pow_mul_sub_le {A : Type*} [CStarAlgebra A]
    (v : unitary A) (q : A) (k : ℕ) :
    ‖(v : A) ^ k * q - q‖ ≤ (k : ℝ) * ‖(v : A) * q - q‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have heq : (v : A) ^ (k + 1) * q - q =
          (v : A) * ((v : A) ^ k * q - q) + ((v : A) * q - q) := by
        rw [pow_succ', mul_sub, ← mul_assoc]; noncomm_ring
      rw [heq]
      calc
        _ ≤ ‖(v : A) * ((v : A) ^ k * q - q)‖ + ‖(v : A) * q - q‖ := norm_add_le _ _
        _ = ‖(v : A) ^ k * q - q‖ + ‖(v : A) * q - q‖ := by
          rw [CStarRing.norm_coe_unitary_mul]
        _ ≤ (k : ℝ) * ‖(v : A) * q - q‖ + ‖(v : A) * q - q‖ := by gcongr
        _ = _ := by push_cast; ring

lemma norm_star_unitary_mul_sub {A : Type*} [CStarAlgebra A]
    (v : unitary A) (q : A) :
    ‖(star v : A) * q - q‖ = ‖(v : A) * q - q‖ := by
  rw [← CStarRing.norm_coe_unitary_mul v ((star v : A) * q - q), mul_sub,
    ← mul_assoc, Unitary.mul_star_self_of_mem v.property, one_mul, norm_sub_rev]

lemma norm_harmonicPolynomial_mul_sub_le {A : Type*} [CStarAlgebra A]
    (v : unitary A) (q : A) (n : ℕ) :
    ‖harmonicPolynomial n (v : A) * q - (harmonic n : ℂ) • q‖ ≤
      (n : ℝ) * ‖(v : A) * q - q‖ := by
  have heq : harmonicPolynomial n (v : A) * q - (harmonic n : ℂ) • q =
      ∑ i ∈ range n, ((i + 1 : ℂ)⁻¹) • ((v : A) ^ (i + 1) * q - q) := by
    simp [harmonicPolynomial, harmonic, smul_sub, sum_mul,
      sum_smul, sum_sub_distrib]
  rw [heq]
  calc
    _ ≤ ∑ i ∈ range n, ‖((i + 1 : ℂ)⁻¹) • ((v : A) ^ (i + 1) * q - q)‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ range n, ‖(v : A) * q - q‖ := by
      apply sum_le_sum
      intro i _
      rw [norm_smul, norm_inv, ← Nat.cast_one (R := ℂ), ← Nat.cast_add,
        Complex.norm_natCast]
      calc
        _ ≤ ((i + 1 : ℕ) : ℝ)⁻¹ *
            (((i + 1 : ℕ) : ℝ) * ‖(v : A) * q - q‖) := by
          gcongr
          exact norm_unitary_pow_mul_sub_le v q (i + 1)
        _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    _ = _ := by simp

lemma star_harmonicPolynomial {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A]
    [StarModule ℂ A] (v : A) (n : ℕ) :
    star (harmonicPolynomial n v) = harmonicPolynomial n (star v) := by
  simp [harmonicPolynomial, star_sum, star_smul, star_pow]

end FourierWindows

section TraceHilbertSpace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

lemma preGNS_norm_star (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) :
    ‖τ.toPreGNS (star a)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_star]
  exact htr _ _
lemma preGNS_norm_mul_right_le (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A) :
    ‖τ.toPreGNS (a * b)‖ ≤ ‖b‖ * ‖τ.toPreGNS a‖ := by
  rw [← preGNS_norm_star τ htr, star_mul]
  exact (preGNS_norm_mul_le τ (star b) (star a)).trans_eq
    (by rw [norm_star, preGNS_norm_star τ htr])

open Finset
open scoped BigOperators
variable {ι : Type*} [Fintype ι]
lemma sum_preGNS_norm_mul_sq (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (q : ι → A) (hq : ∑ j, q j * star (q j) = 1) (a : A) :
    ∑ j, ‖τ.toPreGNS (a * q j)‖ ^ 2 = ‖τ.toPreGNS a‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [τ.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS, star_mul]
  calc
    _ = ∑ j, τ ((star a * a) * (q j * star (q j))) := by
      apply sum_congr rfl
      intro j _
      simpa only [mul_assoc] using htr (star (q j)) ((star a * a) * q j)
    _ = τ ((star a * a) * ∑ j, q j * star (q j)) := by rw [mul_sum, map_sum]
    _ = _ := by rw [hq, mul_one]

noncomputable def gnsFamily (f : ι → A) : PiLp 2 (fun _ : ι => τ.PreGNS) :=
  WithLp.toLp 2 (fun j => τ.toPreGNS (f j))

lemma norm_gnsFamily_sq (f : ι → A) :
    ‖gnsFamily τ f‖ ^ 2 = ∑ j, ‖τ.toPreGNS (f j)‖ ^ 2 :=
  PiLp.norm_sq_eq_of_L2 _ _

omit [StarOrderedRing A] [Fintype ι] in
lemma gnsFamily_add (f g : ι → A) :
    gnsFamily τ (fun j => f j + g j) = gnsFamily τ f + gnsFamily τ g := by
  ext j
  exact map_add τ.toPreGNS _ _

omit [StarOrderedRing A] [Fintype ι] in
lemma gnsFamily_sub (f g : ι → A) :
    gnsFamily τ (fun j => f j - g j) = gnsFamily τ f - gnsFamily τ g := by
  ext j
  exact map_sub τ.toPreGNS _ _

omit [StarOrderedRing A] [Fintype ι] in
lemma gnsFamily_smul (c : ℂ) (f : ι → A) :
    gnsFamily τ (fun j => c • f j) = c • gnsFamily τ f := by
  ext j
  exact map_smul τ.toPreGNS _ _

lemma norm_gnsFamily_mul (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (q : ι → A) (hq : ∑ j, q j * star (q j) = 1) (a : A) :
    ‖gnsFamily τ (fun j => a * q j)‖ = ‖τ.toPreGNS a‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_gnsFamily_sq, sum_preGNS_norm_mul_sq τ htr q hq]

lemma norm_gnsFamily_leftMul_le (a f : ι → A) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) :
    ‖gnsFamily τ (fun j => a j * f j)‖ ≤ C * ‖gnsFamily τ f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp
  rw [mul_pow, norm_gnsFamily_sq, norm_gnsFamily_sq, mul_sum]
  apply sum_le_sum
  intro j _
  rw [← mul_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (preGNS_norm_mul_le τ _ _).trans (by gcongr; exact ha j)

lemma norm_gnsFamily_sq_le (h1 : τ 1 = 1) (f : ι → A) (C : ℝ)
    (hf : ∀ j, ‖f j‖ ≤ C) :
    ‖gnsFamily τ f‖ ^ 2 ≤ (Fintype.card ι : ℝ) * C ^ 2 := by
  rw [norm_gnsFamily_sq]
  calc
    _ ≤ ∑ _ : ι, C ^ 2 := by
      apply sum_le_sum
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) ((preGNS_norm_le τ h1 _).trans (hf j)) _
    _ = _ := by simp

lemma norm_gnsFamily_square_card_le (h1 : τ 1 = 1) {K : ℕ} [NeZero K]
    (f : ZMod (K ^ 2) → A) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ j, ‖f j‖ ≤ C / (K : ℝ) ^ 2) :
    ‖gnsFamily τ f‖ ≤ C / (K : ℝ) := by
  apply (sq_le_sq₀ (norm_nonneg _) (div_nonneg hC (Nat.cast_nonneg _))).mp
  have hK : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  calc
    _ ≤ (Fintype.card (ZMod (K ^ 2)) : ℝ) * (C / (K : ℝ) ^ 2) ^ 2 :=
      norm_gnsFamily_sq_le τ h1 f _ hf
    _ = _ := by rw [ZMod.card, Nat.cast_pow]; field_simp

lemma norm_gnsFamily_harmonic_error_le (h1 : τ 1 = 1) {K : ℕ} [NeZero K]
    (q : ZMod (K ^ 2) → A) (v : ZMod (K ^ 2) → unitary A)
    (hv : ∀ j, ‖(v j : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2) (n : ℕ) :
    ‖gnsFamily τ (fun j => harmonicPolynomial n (v j : A) * q j -
        (harmonic n : ℂ) • q j)‖ ≤ (2 * n : ℝ) / (K : ℝ) := by
  apply norm_gnsFamily_square_card_le τ h1 _ _ (by positivity)
  intro j
  calc
    _ ≤ (n : ℝ) * ‖(v j : A) * q j - q j‖ := norm_harmonicPolynomial_mul_sub_le _ _ _
    _ ≤ (n : ℝ) * (2 / (K : ℝ) ^ 2) := by gcongr; exact hv j
    _ = _ := by ring
end TraceHilbertSpace
end HochschildRigidity
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildCatalan
open Polynomial
noncomputable section

lemma catalan_ratio (n : ℕ) :
    ((n:ℝ)+2) * catalan (n+1) = (4*n+2) * catalan n := by
  have h₁ := Nat.succ_mul_centralBinom_succ n
  rw [← succ_mul_catalan_eq_centralBinom (n+1),
    ← succ_mul_catalan_eq_centralBinom n] at h₁
  have h₂ : (n+1) * ((n+2)*catalan (n+1)) =
      (n+1) * ((4*n+2)*catalan n) := by nlinarith [h₁]
  have h₃ := Nat.eq_of_mul_eq_mul_left (by omega : 0 < n+1) h₂
  exact_mod_cast h₃

def catalanDifferential : ℝ[X] →ₗ[ℝ] ℝ[X] :=
  (LinearMap.mulLeft ℝ (X*(C 4-X))).comp derivative +
    LinearMap.mulLeft ℝ (C 2-C 2*X)

lemma catalanDifferential_apply (p : ℝ[X]) :
    catalanDifferential p = X*(C 4-X)*derivative p + (C 2-C 2*X)*p := rfl

lemma catalanDifferential_X_pow (n : ℕ) :
    catalanDifferential (X^n) = (4*(n:ℝ)+2) • X^n - ((n:ℝ)+2) • X^(n+1) := by
  cases n with
  | zero => simp [catalanDifferential_apply, smul_eq_C_mul]
  | succ n =>
    simp only [catalanDifferential_apply, derivative_X_pow, Nat.add_sub_cancel,
      smul_eq_C_mul, Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat]
    simp only [pow_succ]
    ring

lemma differential_moment_zero (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ n, L (X^n) = catalan n) (p : ℝ[X]) :
    L (catalanDifferential p) = 0 := by
  have h (n : ℕ) : L (catalanDifferential (X^n)) = 0 := by
    rw [catalanDifferential_X_pow, map_sub, map_smul, map_smul, hL, hL]
    simpa only [smul_eq_mul, sub_eq_zero] using (catalan_ratio n).symm
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, ← smul_eq_C_mul, map_smul, map_smul, h, smul_zero]

def cutoff : ℝ[X] := 1 - C (1/4) * X

lemma catalanDifferential_cutoff_pow (n : ℕ) :
    catalanDifferential (cutoff ^ n) =
      (4*(n:ℝ)+8) • cutoff^(n+1) - (4*(n:ℝ)+6) • cutoff^n := by
  have h : (4:ℝ[X]) * C (1/4:ℝ) = 1 := by
    rw [← map_ofNat C 4, ← map_mul]; norm_num
  cases n with
  | zero =>
    simp [catalanDifferential_apply, cutoff, smul_eq_C_mul]
    simp only [map_ofNat]
    simp only [one_div] at h
    linear_combination 2*X*h
  | succ n =>
    simp only [catalanDifferential_apply, derivative_pow, Nat.add_sub_cancel,
      smul_eq_C_mul, Nat.cast_add, Nat.cast_one, map_add, map_mul, map_ofNat]
    simp only [cutoff, derivative_sub, derivative_one, derivative_mul, derivative_C,
      derivative_X, zero_mul, mul_one, zero_add, zero_sub]
    simp only [pow_succ]
    norm_num
    linear_combination ((1-X*C (1/4:ℝ))^n *
      (2*X-X^2*((n:ℝ[X])+3)*C (1/4:ℝ)))*h

lemma cutoff_recurrence (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ n, L (X^n) = catalan n)
    (n : ℕ) :
    (2*(n:ℝ)+4)* L (cutoff^(n+1)) = (2*(n:ℝ)+3)* L (cutoff^n) := by
  have h := differential_moment_zero L hL (cutoff^n)
  rw [catalanDifferential_cutoff_pow, map_sub, map_smul, map_smul] at h
  simp only [smul_eq_mul] at h
  linarith

lemma cutoff_moment_sq_le (L : ℝ[X] →ₗ[ℝ] ℝ) (hL : ∀ n, L (X^n) = catalan n)
    (n : ℕ) : ((n:ℝ)+2) * (L (cutoff^n))^2 ≤ 2 := by
  induction n with
  | zero =>
    have h := hL 0
    simp only [pow_zero, catalan_zero, Nat.cast_one] at h
    simp [h]
  | succ n ih =>
    have hrec := cutoff_recurrence L hL n
    have hsq : (2*(n:ℝ)+4)^2 * (L (cutoff^(n+1)))^2 =
        (2*(n:ℝ)+3)^2 * (L (cutoff^n))^2 := by
      exact (_root_.mul_pow _ _ 2).symm.trans
        ((congrArg (fun x : ℝ => x^2) hrec).trans (_root_.mul_pow _ _ 2))
    have hc : ((n:ℝ)+3)*(2*(n:ℝ)+3)^2 ≤ ((n:ℝ)+2)*(2*(n:ℝ)+4)^2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hp : 0 < (2*(n:ℝ)+4)^2 := by positivity
    simp only [Nat.cast_add, Nat.cast_one]
    apply (mul_le_mul_iff_right₀ hp).mp
    calc
      _ = ((n:ℝ)+3)*((2*(n:ℝ)+4)^2 * (L (cutoff^(n+1)))^2) := by ring
      _ = ((n:ℝ)+3)*((2*(n:ℝ)+3)^2 * (L (cutoff^n))^2) := by rw [hsq]
      _ ≤ (((n:ℝ)+2)*(2*(n:ℝ)+4)^2) * (L (cutoff^n))^2 := by
        nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (L (cutoff^n)))]
      _ = (2*(n:ℝ)+4)^2 * (((n:ℝ)+2) * (L (cutoff^n))^2) := by ring
      _ ≤ (2*(n:ℝ)+4)^2 * 2 := mul_le_mul_of_nonneg_left ih hp.le

open Filter Topology in

theorem cutoff_moment_tendsto_zero (L : ℝ[X] →ₗ[ℝ] ℝ)
    (hL : ∀ n, L (X^n) = catalan n) :
    Tendsto (fun n => L (cutoff^n)) atTop (𝓝 0) := by
  have hb (n : ℕ) : (L (cutoff^n))^2 ≤ 2/((n:ℝ)+2) := by
    exact (le_div_iff₀ (by positivity : 0 < (n:ℝ)+2)).mpr
      (by simpa only [mul_comm] using cutoff_moment_sq_le L hL n)
  have hsq : Tendsto (fun n => L (cutoff^n)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg _) hb
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right atTop 2 (tendsto_natCast_atTop_atTop (R := ℝ)))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hsq.sqrt

section Trace
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)
open HochschildRigidity

def momentFunctional (a : A) : ℝ[X] →ₗ[ℝ] ℝ :=
  Complex.reLm.comp ((τ.toLinearMap.restrictScalars ℝ).comp (aeval a).toLinearMap)

omit [StarOrderedRing A] in
lemma momentFunctional_apply (a : A) (p : ℝ[X]) :
    momentFunctional τ a p = (τ (aeval a p)).re := rfl

omit [StarOrderedRing A] in
lemma momentFunctional_X_pow (a : A) (n : ℕ) :
    momentFunctional τ a (X^n) = (τ (a^n)).re := by
  rw [momentFunctional_apply, aeval_X_pow]
end Trace
end
end HochschildCatalan
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildNewtonPolar
noncomputable section
open Polynomial

def polarPoly : ℕ → ℝ[X]
  | 0 => C (1/2)
  | n+1 => C (1/2) * polarPoly n * (C 3-X*(polarPoly n)^2)

def defectPoly (n : ℕ) : ℝ[X] := 1-X*(polarPoly n)^2

lemma defect_succ (n : ℕ) :
    defectPoly (n+1) = C (1/4)*(defectPoly n)^2*(C 3+defectPoly n) := by
  apply Polynomial.funext
  intro t
  simp only [defectPoly,polarPoly,eval_sub,eval_one,eval_mul,eval_X,eval_pow,eval_C,eval_add]
  ring

lemma eval_defect_bounds (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) :
    0 ≤ (defectPoly n).eval t ∧ (defectPoly n).eval t ≤ (1-t/4)^(n+1) := by
  have hc : 0 ≤ 1-t/4 := by linarith
  have hc1 : 1-t/4 ≤ 1 := by linarith
  induction n with
  | zero => simp only [defectPoly,polarPoly,eval_sub,eval_one,eval_mul,eval_X,eval_pow,eval_C]
            constructor <;> nlinarith
  | succ n ih =>
    have hpow : (1-t/4)^(n+1) ≤ 1-t/4 := by
      rw [pow_succ]
      exact mul_le_of_le_one_left hc (pow_le_one₀ hc hc1)
    have he1 : (defectPoly n).eval t ≤ 1 := (ih.2.trans hpow).trans hc1
    rw [defect_succ]
    simp only [eval_mul,eval_C,eval_pow,eval_add]
    constructor
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by linarith [ih.1])
    · calc
        (1/4:ℝ)*(defectPoly n).eval t^2*(3+(defectPoly n).eval t) ≤
            (defectPoly n).eval t^2 := by nlinarith [sq_nonneg ((defectPoly n).eval t)]
        _ ≤ (1-t/4)^(n+1)*(1-t/4) := by
          rw [pow_two]
          exact mul_le_mul ih.2 (ih.2.trans hpow) ih.1 (pow_nonneg hc _)
        _ = _ := by rw [← pow_succ]

section Algebra
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

def polarApprox (s : A) (n : ℕ) : A := s * aeval (star s*s) (polarPoly n)

omit [PartialOrder A] [StarOrderedRing A] in
lemma aeval_selfAdjoint (a : A) (ha : IsSelfAdjoint a) (p : ℝ[X]) :
    IsSelfAdjoint (aeval a p) := by
  rw [← cfc_polynomial p a ha]
  exact cfc_predicate _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma polarApprox_defect (s : A) (n : ℕ) :
    1-star (polarApprox s n)*polarApprox s n = aeval (star s*s) (defectPoly n) := by
  let a := star s*s
  let p := aeval a (polarPoly n)
  have hp : star p = p := (aeval_selfAdjoint a (IsSelfAdjoint.star_mul_self s) _).star_eq
  have hcomm : Commute a p := by
    simpa only [aeval_X] using (Commute.all (X:ℝ[X]) (polarPoly n)).map (aeval a)
  simp only [polarApprox,star_mul]
  rw [mul_assoc (star (aeval (star s*s) (polarPoly n))), ← mul_assoc (star s)]
  change 1-star p*(a*p) = _
  rw [← mul_assoc,hp]
  simp only [defectPoly,map_sub,map_one,map_mul,aeval_X,map_pow]
  change 1-p*a*p = 1-a*p^2
  rw [hcomm.eq.symm,pow_two,mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
lemma spectrum_star_mul_bound [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) {t : ℝ}
    (ht : t ∈ spectrum ℝ (star s*s)) : 0 ≤ t ∧ t ≤ 4 := by
  constructor
  · exact spectrum_star_mul_self_nonneg t ht
  · calc
      t ≤ |t| := le_abs_self t
      _ = ‖t‖ := (Real.norm_eq_abs t).symm
      _ ≤ ‖star s*s‖ := spectrum.norm_le_norm_of_mem ht
      _ ≤ 4 := by rw [CStarRing.norm_star_mul_self]; nlinarith [norm_nonneg s]

lemma defect_nonneg [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) (n : ℕ) :
    0 ≤ 1-star (polarApprox s n)*polarApprox s n := by
  rw [polarApprox_defect,← cfc_polynomial _ _ (IsSelfAdjoint.star_mul_self s)]
  apply cfc_nonneg
  intro t ht
  obtain ⟨ht0,ht4⟩ := spectrum_star_mul_bound s hs ht
  exact (eval_defect_bounds n t ht0 ht4).1

lemma polarApprox_norm_le_one [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) (n : ℕ) :
    ‖polarApprox s n‖ ≤ 1 := by
  have hd := defect_nonneg s hs n
  rw [sub_nonneg,← CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg _),
    CStarRing.norm_star_mul_self] at hd
  nlinarith [norm_nonneg (polarApprox s n)]

lemma defect_le_cutoff [Nontrivial A] (s : A) (hs : ‖s‖ ≤ 2) (n : ℕ) :
    1-star (polarApprox s n)*polarApprox s n ≤ (1-(1/4:ℝ) • (star s*s))^(n+1) := by
  have he : (1-(1/4:ℝ) • (star s*s))^(n+1) =
      aeval (star s*s) (((1:ℝ[X])-C (1/4)*X)^(n+1)) := by simp [Algebra.smul_def]
  rw [polarApprox_defect,he,← cfc_polynomial _ _ (IsSelfAdjoint.star_mul_self s),
    ← cfc_polynomial _ _ (IsSelfAdjoint.star_mul_self s)]
  apply (cfc_le_iff _ _ _).mpr
  intro t ht
  obtain ⟨ht0,ht4⟩ := spectrum_star_mul_bound s hs ht
  simpa only [eval_pow,eval_sub,eval_one,eval_mul,eval_C,eval_X,div_eq_mul_inv,mul_comm,one_mul]
    using (eval_defect_bounds n t ht0 ht4).2

end Algebra
end
end HochschildNewtonPolar

namespace HochschildFreeSums
noncomputable section
open Finset Polynomial Filter Topology
open scoped ComplexOrder
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in

def freeSum {α : Type*} [Fintype α] (u : FreeGroup α →* A) : A :=
  (Real.sqrt (Fintype.card α))⁻¹ • ∑ i, u (FreeGroup.of i)

lemma collisionCard_of_injective {I G : Type*} [Fintype I] [DecidableEq G]
    (g : I → G) (hg : Function.Injective g) :
    Fintype.card {p : I × I // g p.1 = g p.2} = Fintype.card I := by
  classical
  apply Fintype.card_congr
  exact {
    toFun := fun p => p.val.1
    invFun := fun i => ⟨(i,i),rfl⟩
    left_inv := fun p => Subtype.ext (Prod.ext rfl (hg p.property))
    right_inv := fun _ => rfl }

lemma norm_freeSum_le_two {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup α →* A)
    (h1 : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
    (hfree : ∀ g, g ≠ 1 → τ (u g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) : ‖freeSum u‖ ≤ 2 := by
  have hn := HochschildIndexedHaagerup.norm_sum_le τ u h1 hu hfree htr hf
    FreeGroup.of 1 (fun i => by simp)
  rw [collisionCard_of_injective _ FreeGroup.of_injective] at hn
  have hc : 0 < Real.sqrt (Fintype.card α) := Real.sqrt_pos.mpr (by exact_mod_cast Fintype.card_pos)
  rw [freeSum,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hc.le)]
  calc
    _ ≤ (Real.sqrt (Fintype.card α))⁻¹ * ((1+1:ℝ)*Real.sqrt (Fintype.card α)) :=
      mul_le_mul_of_nonneg_left (by simpa only [Nat.cast_one] using hn) (inv_nonneg.mpr hc.le)
    _ = 2 := by field_simp; ring

omit [PartialOrder A] [StarOrderedRing A] in
lemma star_mul_freeSum {α : Type*} [Fintype α] (u : FreeGroup α →* A) :
    star (freeSum u)*freeSum u = HochschildCatalanMoments.positiveSum u := by
  rw [freeSum,star_smul,star_trivial,smul_mul_smul]
  have hscalar : (Real.sqrt (Fintype.card α))⁻¹ * (Real.sqrt (Fintype.card α))⁻¹ =
      (Fintype.card α:ℝ)⁻¹ := by
    rw [← pow_two,inv_pow,Real.sq_sqrt (by positivity)]
  rw [hscalar]
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  change (Complex.ofReal ((Fintype.card α:ℝ)⁻¹)) • _ = _
  simp only [Complex.ofReal_inv,Complex.ofReal_natCast,HochschildCatalanMoments.positiveSum]

def catalanFunctional : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum (fun n => LinearMap.mulRight ℝ (catalan n : ℝ))

@[simp] lemma catalanFunctional_X_pow (n : ℕ) : catalanFunctional (X^n) = catalan n := by
  change (X^n:ℝ[X]).sum (fun n c => c*(catalan n:ℝ)) = _
  rw [← one_mul (X^n),← map_one C, C_mul_X_pow_eq_monomial, sum_monomial_index]
  · simp
  · simp

omit [StarOrderedRing A] in
lemma polynomial_moments_tendsto (τ : A →ₚ[ℂ] ℂ) (s : ℕ → A)
    (hm : ∀ n, Tendsto (fun r => (τ ((star (s r)*s r)^n)).re) atTop (nhds (catalan n:ℝ)))
    (p : ℝ[X]) : Tendsto (fun r => (τ (aeval (star (s r)*s r) p)).re)
      atTop (nhds (catalanFunctional p)) := by
  change Tendsto (fun r => HochschildCatalan.momentFunctional τ (star (s r)*s r) p) _ _
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial,← smul_eq_C_mul,map_smul]
    simp only [map_smul,HochschildCatalan.momentFunctional_X_pow,catalanFunctional_X_pow]
    exact (hm n).const_smul c

omit [StarOrderedRing A] in
lemma freeSum_moments_tendsto (τ : A →ₚ[ℂ] ℂ) (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0) (n : ℕ) :
    Tendsto (fun r => (τ ((star (freeSum (u r))*freeSum (u r))^n)).re)
      atTop (nhds (catalan n:ℝ)) := by
  have he (r : ℕ) : (τ ((star (freeSum (u r))*freeSum (u r))^n)).re =
      (Fintype.card (HochschildCatalanWords.ReturnWords (Fin (r+1)) n):ℝ) / ((r+1:ℕ):ℝ)^n := by
    rw [star_mul_freeSum]
    simpa only [PositiveLinearMap.coe_toLinearMap, Fintype.card_fin] using HochschildCatalanMoments.re_trace_positiveSum_pow (u r) (hu r) τ.toLinearMap h1 (hfree r) n
  simp_rw [he]
  exact (HochschildCatalanWords.normalized_returnWord_count_tendsto n).comp (tendsto_add_atTop_nat 1)

lemma cutoff_catalan_tendsto_zero : Tendsto
    (fun n => catalanFunctional (HochschildCatalan.cutoff^(n+1))) atTop (nhds 0) := by
  exact (HochschildCatalan.cutoff_moment_tendsto_zero catalanFunctional
    catalanFunctional_X_pow).comp (tendsto_add_atTop_nat 1)
end
end HochschildFreeSums
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildBlockAssembly
noncomputable section
open Finset Filter Topology HochschildCollision HochschildBlockError HochschildBlockWords
variable {A : Type*} [CStarAlgebra A]
variable {α : Type*} [Fintype α] [DecidableEq α]

def allSum (u : FreeGroup α →* A) {L : ℕ} (σ : Fin L → Bool) : A :=
  ∑ f : Fin L → α, u (wordOf σ f)

lemma sum_badSum (u : FreeGroup α →* A) {L : ℕ} (σ : Fin L → Bool) :
    (∑ q ∈ range (L+1), badSum u σ q) =
      ∑ f : Fin L → α with ¬ ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup,
        u (wordOf σ f) := by
  classical
  let s : Finset (Fin L → α) := univ.filter fun f =>
    ¬ ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup
  have hlen (f : Fin L → α) (_hf : f ∈ s) : (wordOf σ f).toWord.length ∈ range (L+1) := by
    have h := @FreeGroup.norm_mk_le α (tupleWord σ f)
    rw [tupleWord_length] at h
    exact mem_range.mpr (by exact Nat.lt_succ_of_le h)
  rw [← sum_fiberwise_of_maps_to hlen (fun f => u (wordOf σ f))]
  apply sum_congr rfl
  intro q _
  unfold badSum
  symm
  apply sum_subtype
  intro f
  constructor
  · intro h
    exact ⟨(Finset.mem_filter.mp h).2, (Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2⟩
  · intro h
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2⟩,h.1⟩

lemma map_allSum_eq_badSum (u : FreeGroup α →* A) (T : A →L[ℝ] A)
    {L : ℕ} (σ : Fin L → Bool)
    (hT : ∀ f : Fin L → α,
      ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup → T (u (wordOf σ f)) = 0) :
    T (allSum u σ) = T (∑ q ∈ range (L+1), badSum u σ q) := by
  classical
  rw [sum_badSum,allSum,map_sum,map_sum]
  rw [sum_filter]
  apply sum_congr rfl
  intro f _
  split_ifs with h
  · exact hT f h
  · rfl

variable [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

lemma tendsto_map_allSum (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (T : A →L[ℝ] A) {L : ℕ} (hL : 0 < L) (σ : Fin L → Bool)
    (hT : ∀ r (f : Fin L → Fin (r+1)),
      ((FreeGroup.reduce (tupleWord σ f)).map Prod.fst).Nodup → T (u r (wordOf σ f)) = 0) :
    Tendsto (fun r => T (normalizer (r+1) L • allSum (u r) σ)) atTop (nhds 0) := by
  have he (r : ℕ) : T (normalizer (r+1) L • allSum (u r) σ) =
      T (∑ q ∈ range (L+1),normalizer (r+1) L • badSum (u r) σ q) := by
    rw [map_smul,map_allSum_eq_badSum (u r) T σ (hT r),← map_smul,smul_sum]
  simp_rw [he]
  simpa only [map_zero,Function.comp_def] using T.continuous.tendsto 0 |>.comp
    (tendsto_total_badSum τ u h1 hu hfree htr hf hL σ)

end
end HochschildBlockAssembly

namespace HochschildWordEval
noncomputable section
open Finset HochschildCollision HochschildBlockError HochschildBlockAssembly HochschildFreeSums
variable {A : Type*} [CStarAlgebra A]

def letter (s : A) (b : Bool) : A := if b then s else star s

def eval (s : A) (σ : List Bool) : A := (σ.map (letter s)).prod

@[simp] lemma eval_nil (s : A) : eval s [] = 1 := rfl
@[simp] lemma eval_cons (s : A) (b : Bool) (σ : List Bool) :
    eval s (b::σ) = letter s b * eval s σ := rfl
@[simp] lemma eval_append (s : A) (σ ρ : List Bool) :
    eval s (σ++ρ) = eval s σ * eval s ρ := by simp [eval,List.prod_append]

lemma letter_smul (c : ℝ) (s : A) (b : Bool) : letter (c • s) b = c • letter s b := by
  cases b <;> simp [letter,star_smul]

lemma eval_smul (c : ℝ) (s : A) (σ : List Bool) :
    eval (c • s) σ = c^σ.length • eval s σ := by
  induction σ with
  | nil => simp
  | cons b σ ih => simp only [eval_cons,letter_smul,ih,List.length_cons,smul_mul_smul,pow_succ']

variable {α : Type*} [Fintype α]

lemma letter_sum (s : α → A) (b : Bool) : letter (∑ i, s i) b = ∑ i, letter (s i) b := by
  cases b <;> simp [letter,star_sum]

omit [Fintype α] in
lemma wordOf_cons (b : Bool) (σ : List Bool) (f : Fin (σ.length+1) → α) :
    wordOf (fun i => (b::σ)[i]) f = FreeGroup.mk [(f 0,b)] *
      wordOf (fun i => σ[i]) (fun i => f i.succ) := by
  simp only [wordOf,tupleWord,List.ofFn_succ,FreeGroup.mul_mk]
  rfl

omit [Fintype α] in
lemma map_singleton (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (i : α) (b : Bool) : u (FreeGroup.mk [(i,b)]) = letter (u (FreeGroup.of i)) b := by
  cases b
  · simpa only [letter,Bool.false_eq_true,↓reduceIte,FreeGroup.of,FreeGroup.inv_mk,FreeGroup.invRev,List.map_cons,List.map_nil,List.reverse_cons,List.reverse_nil,List.nil_append,Bool.not_true] using (hu (FreeGroup.of i)).symm
  · rfl

lemma allSum_cons (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (b : Bool) (σ : List Bool) :
    allSum u (fun i => (b::σ)[i]) =
      (∑ i, letter (u (FreeGroup.of i)) b) * allSum u (fun i => σ[i]) := by
  classical
  unfold allSum
  calc
    _ = ∑ p : α × (Fin σ.length → α),
        u (wordOf (fun i => (b::σ)[i]) (Fin.cons p.1 p.2)) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (σ.length+1) => α)) _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type,sum_mul]
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      apply sum_congr rfl
      intro f _
      rw [wordOf_cons,map_mul,map_singleton u hu]
      rfl

lemma eval_sum_eq (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (σ : List Bool) : eval (∑ i, u (FreeGroup.of i)) σ = allSum u (fun i => σ[i]) := by
  classical
  induction σ with
  | nil => simp [allSum,wordOf,tupleWord,← FreeGroup.one_eq_mk]
  | cons b σ ih => rw [eval_cons,letter_sum,ih,allSum_cons u hu]

lemma eval_freeSum (u : FreeGroup α →* A) (hu : ∀ g, star (u g) = u g⁻¹)
    (σ : List Bool) :
    eval (freeSum u) σ = normalizer (Fintype.card α) σ.length • allSum u (fun i => σ[i]) := by
  rw [freeSum,eval_smul,eval_sum_eq u hu]
  rfl

end
end HochschildWordEval

namespace HochschildGoodPatterns
noncomputable section
open HochschildCatalanWords HochschildBlockWords HochschildWordEval

def Good (b : Bool) (σ : List Bool) : Prop :=
  ∀ (α : Type) [DecidableEq α] (w : List (α × Bool)),
    w.map Prod.snd = σ → Ends b (FreeGroup.reduce w)

def alt (b : Bool) : ℕ → List Bool
  | 0 => []
  | n+1 => b :: alt (!b) n

@[simp] lemma length_alt (b : Bool) (n : ℕ) : (alt b n).length = n := by
  induction n generalizing b with
  | zero => rfl
  | succ n ih => simp [alt,ih]

lemma signed_fst {α : Type*} (b : Bool) (l : List α) : (signed b l).map Prod.fst = l := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp [signed,ih]

lemma signed_snd {α : Type*} (b : Bool) (l : List α) :
    (signed b l).map Prod.snd = alt b l.length := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => simp [signed,alt,ih]

lemma good_alt (b : Bool) (d : ℕ) : Good b (alt b (2*d+1)) := by
  intro α _ w hw
  have hlen : w.length = 2*d+1 := by
    simpa only [List.length_map,length_alt] using congrArg List.length hw
  have he : signed b (w.map Prod.fst) = w := by
    apply (List.zip_of_prod (signed_fst b _) ?_).trans
    · exact (List.zip_of_prod rfl rfl).symm
    · rw [signed_snd,List.length_map,hlen,← hw]
  rw [← he]
  exact reduce_signed_odd_ends _ (by simp only [List.length_map,hlen]; omega) b

lemma good_append {b : Bool} {σ ρ : List Bool} (hσ : Good b σ) (hρ : Good b ρ) :
    Good b (σ++ρ) := by
  intro α _ w hw
  obtain ⟨l,k,rfl,hl,hk⟩ := List.map_eq_append_iff.mp hw
  exact (reduce_append_odd_blocks l k (hσ α l hl) (hρ α k hk)).2

lemma good_length_pos {b : Bool} {σ : List Bool} (hσ : Good b σ) : 0 < σ.length := by
  by_contra h
  have he : σ = [] := List.length_eq_zero_iff.mp (by omega)
  obtain ⟨⟨a,l,ha⟩,_⟩ := hσ Unit [] he.symm
  simp at ha

def invPattern (σ : List Bool) : List Bool := (σ.map Bool.not).reverse

@[simp] lemma invPattern_invPattern (σ : List Bool) : invPattern (invPattern σ) = σ := by
  simp [invPattern,List.map_reverse,List.map_map,Function.comp_def]

lemma invRev_snd {α : Type*} (w : List (α × Bool)) :
    (FreeGroup.invRev w).map Prod.snd = invPattern (w.map Prod.snd) := by
  simp [FreeGroup.invRev,invPattern,List.map_reverse,List.map_map,Function.comp_def]

lemma ends_invRev {α : Type*} {b : Bool} {w : List (α × Bool)} (hw : Ends b w) :
    Ends (!b) (FreeGroup.invRev w) := by
  rcases hw with ⟨⟨a,l,ha⟩,⟨k,c,hc⟩⟩
  constructor
  · refine ⟨c,FreeGroup.invRev k,?_⟩
    rw [hc,FreeGroup.invRev_append]
    simp [FreeGroup.invRev]
  · refine ⟨FreeGroup.invRev l,a,?_⟩
    rw [ha,FreeGroup.invRev_cons]
    rfl

lemma good_inv {b : Bool} {σ : List Bool} (hσ : Good b σ) : Good (!b) (invPattern σ) := by
  intro α _ w hw
  have hg := hσ α (FreeGroup.invRev w) (by rw [invRev_snd,hw,invPattern_invPattern])
  have hh := ends_invRev hg
  simpa only [FreeGroup.reduce_invRev,FreeGroup.invRev_invRev] using hh

variable {A : Type*} [CStarAlgebra A]

lemma letter_not (s : A) (b : Bool) : letter s (!b) = star (letter s b) := by
  cases b <;> simp [letter]

lemma eval_inv (s : A) (σ : List Bool) : eval s (invPattern σ) = star (eval s σ) := by
  induction σ with
  | nil => simp [invPattern]
  | cons b σ ih =>
    simp only [invPattern,List.map_cons,List.reverse_cons]
    rw [eval_append]
    change eval s (invPattern σ) * eval s [!b] = _
    rw [ih,eval_cons,eval_nil,mul_one,letter_not,eval_cons,star_mul]

lemma eval_alt (s : A) (b : Bool) (d : ℕ) :
    eval s (alt b (2*d+1)) = letter s b * (letter s (!b) * letter s b)^d := by
  induction d with
  | zero => simp [alt]
  | succ d ih =>
    have he : 2*(d+1)+1 = (2*d+1)+1+1 := by omega
    rw [he,alt,alt,Bool.not_not,eval_cons,eval_cons,ih,pow_succ']
    simp only [mul_assoc]

end
end HochschildGoodPatterns

namespace HochschildBlockSpan
noncomputable section
open Filter Topology HochschildWordEval HochschildGoodPatterns
open scoped Polynomial
variable {A : Type*} [CStarAlgebra A]

def span (s : ℕ → A) (b : Bool) : Submodule ℝ (ℕ → A) :=
  Submodule.span ℝ {f | ∃ σ, Good b σ ∧ f = fun r => eval (s r) σ}

lemma generator_mem (s : ℕ → A) {b : Bool} {σ : List Bool} (hσ : Good b σ) :
    (fun r => eval (s r) σ) ∈ span s b := Submodule.subset_span ⟨σ,hσ,rfl⟩

lemma mul_mem (s : ℕ → A) (b : Bool) {x y : ℕ → A} (hx : x ∈ span s b) (hy : y ∈ span s b) :
    x*y ∈ span s b := by
  refine Submodule.span_induction₂ (p := fun x y _ _ => x*y ∈ span s b) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · rintro x y ⟨σ,hσ,rfl⟩ ⟨ρ,hρ,rfl⟩
    apply Submodule.subset_span
    refine ⟨σ++ρ,good_append hσ hρ,?_⟩
    funext r
    exact (eval_append (s r) σ ρ).symm
  · intro y _
    simpa only [zero_mul] using (span s b).zero_mem
  · intro x _
    simpa only [mul_zero] using (span s b).zero_mem
  · intro x y z _ _ _ ihx ihy
    rw [add_mul]
    exact (span s b).add_mem ihx ihy
  · intro x y z _ _ _ ihy ihz
    rw [mul_add]
    exact (span s b).add_mem ihy ihz
  · intro c x y _ _ ih
    rw [smul_mul_assoc]
    exact (span s b).smul_mem c ih
  · intro c x y _ _ ih
    rw [mul_smul_comm]
    exact (span s b).smul_mem c ih

lemma pow_mem (s : ℕ → A) (b : Bool) {x : ℕ → A} (hx : x ∈ span s b)
    (k : ℕ) (hk : 0 < k) : x^k ∈ span s b := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  induction n with
  | zero => simpa using hx
  | succ n ih => simpa only [pow_succ] using mul_mem s b (ih (Nat.succ_pos _)) hx

lemma star_mem (s : ℕ → A) (b : Bool) {x : ℕ → A} (hx : x ∈ span s b) :
    star x ∈ span s (!b) := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨σ,hσ,rfl⟩ := hf
    apply Submodule.subset_span
    refine ⟨invPattern σ,good_inv hσ,?_⟩
    funext r
    exact (eval_inv (s r) σ).symm
  | zero => simp
  | add x y hx hy ihx ihy =>
    rw [star_add]
    exact (span s (!b)).add_mem ihx ihy
  | smul c x hx ih =>
    rw [star_smul,star_trivial]
    exact (span s (!b)).smul_mem c ih

lemma polynomial_block_mem (s : ℕ → A) (p : ℝ[X]) :
    (fun r => s r * Polynomial.aeval (star (s r)*s r) p) ∈ span s true := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simpa only [map_add,mul_add,Pi.add_def] using (span s true).add_mem hp hq
  | monomial n c =>
    have hg := (span s true).smul_mem c (generator_mem s (good_alt true n))
    simpa only [Pi.smul_def,eval_alt,letter,Bool.not_true,↓reduceIte,
      Bool.false_eq_true,Polynomial.aeval_monomial,← Algebra.smul_def,mul_smul_comm] using hg

lemma polarApprox_mem (s : ℕ → A) (n : ℕ) :
    (fun r => HochschildNewtonPolar.polarApprox (s r) n) ∈ span s true :=
  polynomial_block_mem s (HochschildNewtonPolar.polarPoly n)

variable [PartialOrder A] [StarOrderedRing A]
open scoped ComplexOrder

lemma tendsto_eval_of_good (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (T : A →L[ℝ] A) (b : Bool)
    (hT : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → T (u r g) = 0)
    (σ : List Bool) (hσ : Good b σ) :
    Tendsto (fun r => T (eval (HochschildFreeSums.freeSum (u r)) σ)) atTop (nhds 0) := by
  simp_rw [eval_freeSum _ (hu _), Fintype.card_fin]
  apply HochschildBlockAssembly.tendsto_map_allSum τ u h1 hu hfree htr hf T (good_length_pos hσ)
  intro r f hnodup
  apply hT r _
  · simpa only [HochschildBlockError.wordOf,FreeGroup.toWord_mk] using hnodup
  · rw [HochschildBlockError.wordOf,FreeGroup.toWord_mk]
    apply hσ (Fin (r+1))
    simp only [HochschildCollision.tupleWord,List.map_ofFn,Function.comp_def]
    exact List.ofFn_get σ

lemma tendsto_of_mem (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (T : A →L[ℝ] A) (b : Bool)
    (hT : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → T (u r g) = 0)
    {x : ℕ → A} (hx : x ∈ span (fun r => HochschildFreeSums.freeSum (u r)) b) :
    Tendsto (fun r => T (x r)) atTop (nhds 0) := by
  induction hx using Submodule.span_induction with
  | mem f hf' =>
    obtain ⟨σ,hσ,rfl⟩ := hf'
    exact tendsto_eval_of_good τ u h1 hu hfree htr hf T b hT σ hσ
  | zero => simp only [Pi.zero_apply,map_zero]; exact tendsto_const_nhds
  | add x y hx hy ihx ihy => simpa only [Pi.add_apply,map_add,add_zero] using ihx.add ihy
  | smul c x hx ih => simpa only [Pi.smul_apply,map_smul,smul_zero] using ih.const_smul c
end
end HochschildBlockSpan
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildMatrixDilation
noncomputable section
open scoped Matrix ComplexOrder
open Complex
variable {A : Type*} [CStarAlgebra A]

abbrev Mat (A : Type*) := CStarMatrix (Fin 2) (Fin 2) A

def diag (a b : A) : Mat A := CStarMatrix.ofMatrix !![a,0;0,b]

def offdiag (a b : A) : Mat A := CStarMatrix.ofMatrix !![0,a;b,0]

@[simp] lemma diag_zero_zero : diag (0:A) 0 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_one_one : diag (1:A) 1 = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl
@[simp] lemma diag_add (a b c d : A) : diag (a+c) (b+d) = diag a b + diag c d := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_smul (z : ℂ) (a b : A) : diag (z • a) (z • b) = z • diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
@[simp] lemma diag_mul (a b c d : A) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.mul_apply, Fin.sum_univ_two]
@[simp] lemma star_diag (a b : A) : star (diag a b) = diag (star a) (star b) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma star_offdiag (a b : A) : star (offdiag a b) = offdiag (star b) (star a) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [offdiag, CStarMatrix.star_eq_conjTranspose]
@[simp] lemma offdiag_mul (a b c d : A) :
    offdiag a b * offdiag c d = diag (a*d) (b*c) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [diag, offdiag, CStarMatrix.mul_apply, Fin.sum_univ_two]

def diagHom : A × A →⋆ₐ[ℂ] Mat A where
  toFun a := diag a.1 a.2
  map_one' := diag_one_one
  map_mul' a b := (diag_mul _ _ _ _).symm
  map_zero' := diag_zero_zero
  map_add' a b := diag_add _ _ _ _
  commutes' z := by
    ext i j; fin_cases i <;> fin_cases j <;>
      rfl
  map_star' a := (star_diag _ _).symm

variable [PartialOrder A] [StarOrderedRing A]

lemma norm_diag_le (a b : A) : ‖diag a b‖ ≤ max ‖a‖ ‖b‖ := by
  exact NonUnitalStarAlgHom.norm_apply_le diagHom (a,b)

omit [PartialOrder A] [StarOrderedRing A] in
lemma offdiag_selfAdjoint (a : A) : IsSelfAdjoint (offdiag a (star a)) := by
  change star (offdiag a (star a)) = _
  simp

lemma offdiag_norm_le_one (a : A) (ha : ‖a‖ ≤ 1) : ‖offdiag a (star a)‖ ≤ 1 := by
  have hsq : ‖offdiag a (star a)‖^2 ≤ 1 := by
    rw [← (offdiag_selfAdjoint a).norm_mul_self, offdiag_mul]
    refine (norm_diag_le _ _).trans (max_le ?_ ?_)
    · calc
        ‖a * star a‖ ≤ ‖a‖ * ‖star a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
    · calc
        ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ := norm_mul_le _ _
        _ ≤ 1 := by rw [norm_star]; nlinarith [norm_nonneg a]
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp hsq

def flipUnitary : unitary (Mat A) :=
  ⟨offdiag 1 1, by rw [Unitary.mem_iff]; simp⟩

def dilation (a : A) (ha : ‖a‖ ≤ 1) : unitary (Mat A) :=
  (selfAdjoint.unitarySelfAddISMul
    ⟨offdiag a (star a), offdiag_selfAdjoint a⟩ (offdiag_norm_le_one a ha)) * flipUnitary

local instance : NonUnitalContinuousFunctionalCalculus ℝ (Mat A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance : NonnegSpectrumClass ℝ (Mat A) :=
  CStarAlgebra.instNonnegSpectrumClass

lemma dilation_sub_diag (a : A) (ha : ‖a‖ ≤ 1) :
    (dilation a ha : Mat A) - diag a (star a) =
    Complex.I • (CFC.sqrt (1 - offdiag a (star a) ^ 2) * offdiag 1 1) := by
  change (offdiag a (star a) + Complex.I • CFC.sqrt (1 - offdiag a (star a)^2)) *
    offdiag 1 1 - diag a (star a) = _
  rw [add_mul, smul_mul_assoc, offdiag_mul, mul_one, mul_one]
  abel

lemma diagEntry_nonneg (M : Mat A) (hM : 0 ≤ M) (i : Fin 2) : 0 ≤ M i i := by
  have hs := CFC.sqrt_nonneg M
  have he : M = star (CFC.sqrt M) * CFC.sqrt M := by
    rw [hs.isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self M hM]
  rw [he, CStarMatrix.mul_apply]
  simp only [CStarMatrix.star_apply]
  exact Finset.sum_nonneg fun j _ => star_mul_self_nonneg _

def matrixTraceLinear (τ : A →ₚ[ℂ] ℂ) : Mat A →ₗ[ℂ] ℂ where
  toFun M := (τ (M 0 0) + τ (M 1 1)) / 2
  map_add' M N := by simp only [CStarMatrix.add_apply, map_add]; ring
  map_smul' z M := by
    simp only [CStarMatrix.smul_apply, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

def matrixTrace (τ : A →ₚ[ℂ] ℂ) : Mat A →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀ (matrixTraceLinear τ) (fun M hM =>
    div_nonneg (add_nonneg (τ.map_nonneg (diagEntry_nonneg M hM 0))
      (τ.map_nonneg (diagEntry_nonneg M hM 1))) (by norm_num))

lemma matrixTrace_apply (τ : A →ₚ[ℂ] ℂ) (M : Mat A) :
    matrixTrace τ M = (τ (M 0 0) + τ (M 1 1)) / 2 := rfl

@[simp] lemma matrixTrace_diag (τ : A →ₚ[ℂ] ℂ) (a b : A) :
    matrixTrace τ (diag a b) = (τ a + τ b)/2 := rfl

lemma matrixTrace_one (τ : A →ₚ[ℂ] ℂ) (hτ : τ 1 = 1) : matrixTrace τ 1 = 1 := by
  rw [← diag_one_one, matrixTrace_diag, hτ]
  ring

lemma matrixTrace_tracial (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (M N : Mat A) :
    matrixTrace τ (M*N) = matrixTrace τ (N*M) := by
  simp only [matrixTrace_apply, CStarMatrix.mul_apply, Fin.sum_univ_two, map_add]
  rw [htr (M 0 0), htr (M 0 1), htr (M 1 0), htr (M 1 1)]
  ring

lemma matrixTrace_norm_sq (τ : A →ₚ[ℂ] ℂ) (M : Mat A) :
    ‖(matrixTrace τ).toPreGNS M‖^2 =
    (‖τ.toPreGNS (M 0 0)‖^2 + ‖τ.toPreGNS (M 1 0)‖^2 +
      ‖τ.toPreGNS (M 0 1)‖^2 + ‖τ.toPreGNS (M 1 1)‖^2) / 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS,
    matrixTrace_apply, CStarMatrix.mul_apply, Fin.sum_univ_two, CStarMatrix.star_apply,
    map_add]
  ring

lemma matrixTrace_faithful (τ : A →ₚ[ℂ] ℂ)
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0) (M : Mat A)
    (hM : matrixTrace τ (star M*M) = 0) : M = 0 := by
  have hm : ‖(matrixTrace τ).toPreGNS M‖^2 = 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_pow, Complex.ofReal_zero,
      PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS] using hM
  rw [matrixTrace_norm_sq] at hm
  have hn (a : A) (h : ‖τ.toPreGNS a‖^2 = 0) : a = 0 := by
    apply hf
    simpa only [Complex.ofReal_pow, Complex.ofReal_zero,
      PositiveLinearMap.preGNS_norm_sq, PositiveLinearMap.ofPreGNS_toPreGNS] using
      congrArg (fun r : ℝ => (r:ℂ)) h
  have h00 := sq_nonneg ‖τ.toPreGNS (M 0 0)‖
  have h10 := sq_nonneg ‖τ.toPreGNS (M 1 0)‖
  have h01 := sq_nonneg ‖τ.toPreGNS (M 0 1)‖
  have h11 := sq_nonneg ‖τ.toPreGNS (M 1 1)‖
  have hz00 : M 0 0 = 0 := hn _ (by linarith)
  have hz10 : M 1 0 = 0 := hn _ (by linarith)
  have hz01 : M 0 1 = 0 := hn _ (by linarith)
  have hz11 : M 1 1 = 0 := hn _ (by linarith)
  ext i j
  fin_cases i <;> fin_cases j
  · exact hz00
  · exact hz01
  · exact hz10
  · exact hz11

open scoped Matrix.Norms.Elementwise in

def matrixMap (R : A →L[ℂ] A) : Mat A →L[ℂ] Mat A where
  toLinearMap := CStarMatrix.mapₗ R.toLinearMap
  cont := by
    let e := CStarMatrix.ofMatrixL (m:=Fin 2) (n:=Fin 2) (A:=A)
    have hc : Continuous (fun M : Mat A => fun i j => R (e.symm M i j)) := by
      apply continuous_pi; intro i
      apply continuous_pi; intro j
      exact R.continuous.comp ((continuous_apply j).comp ((continuous_apply i).comp e.symm.continuous))
    exact e.continuous.comp hc

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixMap_apply (R : A →L[ℂ] A) (M : Mat A) (i j : Fin 2) :
    matrixMap R M i j = R (M i j) := rfl

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma matrixMap_diag (R : A →L[ℂ] A) (a b : A) :
    matrixMap R (diag a b) = diag (R a) (R b) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag]

lemma dilation_defect_nonneg (a : A) (ha : ‖a‖ ≤ 1) :
    0 ≤ (1 - offdiag a (star a)^2 : Mat A) := by
  have hself := offdiag_selfAdjoint a
  have hnon : 0 ≤ (offdiag a (star a) : Mat A)^2 := by
    simpa only [hself.star_eq, pow_two] using (star_mul_self_nonneg (offdiag a (star a)))
  rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg _ hnon,
    pow_two, hself.norm_mul_self]
  exact (sq_le_one_iff₀ (norm_nonneg _)).mpr (offdiag_norm_le_one a ha)

lemma dilation_error_sq (τ : A →ₚ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a : A) (ha : ‖a‖ ≤ 1) :
    ‖(matrixTrace τ).toPreGNS ((dilation a ha : Mat A) - diag a (star a))‖^2 =
      (τ (1-star a*a)).re := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_pow, PositiveLinearMap.preGNS_norm_sq]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, dilation_sub_diag,
    star_smul, star_mul, smul_mul_smul, Complex.star_def, Complex.conj_I, neg_mul,
    Complex.I_mul_I, neg_neg, one_smul]
  let d : Mat A := CFC.sqrt (1 - offdiag a (star a)^2)
  have hd : star d = d := (CFC.sqrt_nonneg _).isSelfAdjoint.star_eq
  change matrixTrace τ ((star (offdiag 1 1) * star d) * (d * offdiag 1 1)) = _
  rw [mul_assoc, ← mul_assoc (star d), hd, CFC.sqrt_mul_sqrt_self _ (dilation_defect_nonneg a ha)]
  rw [← mul_assoc, matrixTrace_tracial τ htr, ← mul_assoc, star_offdiag,
    star_one, offdiag_mul, one_mul, diag_one_one, one_mul]
  rw [pow_two, offdiag_mul]
  have he : (1 : Mat A) - diag (a*star a) (star a*a) =
      diag (1-a*star a) (1-star a*a) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag]
  rw [he, matrixTrace_diag]
  have ht : τ (1-a*star a) = τ (1-star a*a) := by simp only [map_sub, htr a (star a)]
  rw [ht]
  have hnon : 0 ≤ 1-star a*a := by
    rw [sub_nonneg, ← CStarAlgebra.norm_le_one_iff_of_nonneg _ (star_mul_self_nonneg a),
      CStarRing.norm_star_mul_self]
    nlinarith [norm_nonneg a]
  have hre : (τ (1-star a*a)).im = 0 := (Complex.nonneg_iff.mp (τ.map_nonneg hnon)).2.symm

  rw [← Complex.re_add_im (τ (1-star a*a)), hre]
  simp
end
end HochschildMatrixDilation
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildRigidity
noncomputable section
open scoped ComplexOrder BigOperators
open Finset
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

def unitaryHarmonicError {K : ℕ} [NeZero K] (S : A →L[ℂ] A)
    (u : unitary A) (a b : A) (n : ℕ) (j : ZMod (K^2)) : A :=
  let v : unitary A := rootUnitary (-j) • u
  S (harmonicPolynomial n (v:A) - star (harmonicPolynomial n (v:A))) -
    (a * harmonicPolynomial n (v:A) - b * star (harmonicPolynomial n (v:A)))

theorem unitary_power_approx_multiplier_bound [Nontrivial A]
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (S : A →L[ℂ] A) (u : unitary A) (a b : A)
    (n : ℕ) {K : ℕ} [NeZero K] :
    (harmonic n : ℝ) * ‖τ.toPreGNS (a - b)‖ ≤
      (2 * (1 + Real.pi)) * ‖S‖ + (‖a‖ + ‖b‖) * ((2 * n : ℝ) / K) +
      ‖gnsFamily τ (fun j : ZMod (K^2) => unitaryHarmonicError S u a b n j *
        fourierWindow (u:A) j)‖ := by
  let q : ZMod (K ^ 2) → A := fun j => fourierWindow (u : A) j
  let v : ZMod (K ^ 2) → unitary A := fun j => rootUnitary (-j) • u
  have hq : ∑ j, q j * star (q j) = 1 := sum_fourierWindow_mul_star u
  have hv (j) : ‖(v j : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2 := by
    simpa only [q, v, Nat.cast_pow] using norm_unitary_mul_fourierWindow_sub_le u j
  have hvneg (j) : ‖(star (v j) : A) * q j - q j‖ ≤ 2 / (K : ℝ) ^ 2 := by
    rw [norm_star_unitary_mul_sub]
    exact hv j
  let ep := fun j => harmonicPolynomial n (v j : A) * q j - (harmonic n : ℂ) • q j
  let em := fun j => star (harmonicPolynomial n (v j : A)) * q j - (harmonic n : ℂ) • q j
  let F := fun j => S (harmonicPolynomial n (v j : A) - star (harmonicPolynomial n (v j : A)))
  have hep : ‖gnsFamily τ ep‖ ≤ (2 * n : ℝ) / K :=
    norm_gnsFamily_harmonic_error_le τ h1 q v hv n
  have hem : ‖gnsFamily τ em‖ ≤ (2 * n : ℝ) / K := by
    simpa only [em, star_harmonicPolynomial, Unitary.coe_star] using
      norm_gnsFamily_harmonic_error_le τ h1 q (fun j => star (v j)) hvneg n
  let E := fun j : ZMod (K^2) => unitaryHarmonicError S u a b n j
  have hFbound (j) : ‖F j‖ ≤ (2 * (1 + Real.pi)) * ‖S‖ := by
    calc
      _ ≤ ‖S‖ * ‖harmonicPolynomial n (v j : A) - star (harmonicPolynomial n (v j : A))‖ := S.le_opNorm _
      _ ≤ ‖S‖ * (2 * (1 + Real.pi)) := by
        gcongr
        exact norm_unitary_harmonicPolynomial_sub_star_le (v j) n
      _ = _ := mul_comm _ _
  have hqn : ‖gnsFamily τ q‖ = 1 := by
    simpa only [one_mul, preGNS_norm_one τ h1] using norm_gnsFamily_mul τ htr q hq 1
  have hFn : ‖gnsFamily τ (fun j => F j * q j)‖ ≤ (2 * (1 + Real.pi)) * ‖S‖ := by
    simpa only [hqn, mul_one] using
      norm_gnsFamily_leftMul_le τ F q _ (by positivity) hFbound
  have hepn : ‖gnsFamily τ (fun j => a * ep j)‖ ≤ ‖a‖ * ((2 * n : ℝ) / K) :=
    (norm_gnsFamily_leftMul_le τ (fun _ => a) ep ‖a‖ (norm_nonneg _) (fun _ => le_rfl)).trans
      (by gcongr)
  have hemn : ‖gnsFamily τ (fun j => b * em j)‖ ≤ ‖b‖ * ((2 * n : ℝ) / K) :=
    (norm_gnsFamily_leftMul_le τ (fun _ => b) em ‖b‖ (norm_nonneg _) (fun _ => le_rfl)).trans
      (by gcongr)
  have hid (j) : (harmonic n : ℂ) • ((a - b) * q j) =
      F j * q j - a * ep j + b * em j - E j * q j := by
    change (harmonic n : ℂ) • ((a - b) * q j) =
      F j * q j - a * ep j + b * em j -
      (F j - (a * harmonicPolynomial n (v j:A) - b * star (harmonicPolynomial n (v j:A)))) * q j
    simp only [ep, em, sub_mul, mul_sub, smul_sub, mul_smul_comm]
    noncomm_ring
  have hh : 0 ≤ (harmonic n : ℝ) := by unfold harmonic; positivity
  have hhnorm : ‖(harmonic n : ℂ)‖ = (harmonic n : ℝ) := by
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_of_nonneg hh]
  calc
    _ = ‖gnsFamily τ (fun j => (harmonic n : ℂ) • ((a - b) * q j))‖ := by
      rw [gnsFamily_smul, norm_smul, hhnorm, norm_gnsFamily_mul τ htr q hq]
    _ = ‖gnsFamily τ (fun j => F j * q j) - gnsFamily τ (fun j => a * ep j) +
        gnsFamily τ (fun j => b * em j) - gnsFamily τ (fun j => E j * q j)‖ := by
      simp only [hid, gnsFamily_add, gnsFamily_sub]
    _ ≤ (‖gnsFamily τ (fun j => F j * q j)‖ + ‖gnsFamily τ (fun j => a * ep j)‖) +
        ‖gnsFamily τ (fun j => b * em j)‖ + ‖gnsFamily τ (fun j => E j * q j)‖ :=
      (norm_sub_le _ _).trans (by
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _))
    _ ≤ _ := by nlinarith [hFn, hepn, hemn]

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_fourierWindow_le_one [Nontrivial A] {L : ℕ} [NeZero L]
    (u : unitary A) (j : ZMod L) : ‖fourierWindow (u:A) j‖ ≤ 1 := by
  let v : unitary A := rootUnitary (-j) • u
  change ‖fourierWindow (u:A) j‖ ≤ 1
  rw [fourierWindow_eq_geometric, norm_smul, norm_inv, Complex.norm_natCast]
  have hn (k : ℕ) : ‖(ZMod.stdAddChar (-j) • (u:A))^k‖ = 1 := by
    change ‖(v:A)^k‖ = 1
    simpa only [SubmonoidClass.coe_pow] using CStarRing.norm_coe_unitary (v^k)
  calc
    _ ≤ (L:ℝ)⁻¹ * ∑ k ∈ range L, ‖(ZMod.stdAddChar (-j) • (u:A))^k‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = 1 := by simp only [hn, sum_const, card_range, nsmul_eq_mul, mul_one]
                exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L))

lemma tendsto_smul_power_error (S : A →L[ℂ] A) (u : ℕ → A) (a : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (u r ^ k) - a * u r ^ k)) Filter.atTop (nhds 0))
    (c : ℂ) (k : ℕ) (hk : 0 < k) : Filter.Tendsto
      (fun r => τ.toPreGNS (S ((c • u r)^k) - a * (c • u r)^k))
      Filter.atTop (nhds 0) := by
  have he (r) : τ.toPreGNS (S ((c • u r)^k) - a * (c • u r)^k) =
      c^k • τ.toPreGNS (S (u r^k) - a*u r^k) := by
    simp only [smul_pow, map_smul, mul_smul_comm, ← smul_sub]
  simpa only [he, smul_zero] using (hp k hk).const_smul (c^k)

lemma tendsto_harmonic_power_error (S : A →L[ℂ] A) (u : ℕ → A) (a : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (u r ^ k) - a * u r ^ k)) Filter.atTop (nhds 0))
    (n : ℕ) : Filter.Tendsto
      (fun r => τ.toPreGNS (S (harmonicPolynomial n (u r)) -
        a * harmonicPolynomial n (u r))) Filter.atTop (nhds 0) := by
  have he (r) : τ.toPreGNS (S (harmonicPolynomial n (u r)) -
        a * harmonicPolynomial n (u r)) =
      ∑ i ∈ range n, ((i+1:ℂ)⁻¹) • τ.toPreGNS (S (u r^(i+1))-a*u r^(i+1)) := by
    simp only [harmonicPolynomial, map_sum, map_smul, mul_sum, mul_smul_comm,
      ← sum_sub_distrib, ← smul_sub]
  simp_rw [he]
  simpa only [smul_zero, sum_const_zero] using
    tendsto_finsetSum (range n) (fun i _ => (hp (i+1) (Nat.succ_pos i)).const_smul ((i+1:ℂ)⁻¹))

lemma tendsto_unitaryHarmonicError (S : A →L[ℂ] A) (u : ℕ → unitary A) (a b : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S ((u r:A)^k)-a*(u r:A)^k)) Filter.atTop (nhds 0))
    (hm : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (star (u r:A)^k)-b*star (u r:A)^k)) Filter.atTop (nhds 0))
    (n : ℕ) {K : ℕ} [NeZero K] (j : ZMod (K^2)) : Filter.Tendsto
      (fun r => τ.toPreGNS (unitaryHarmonicError S (u r) a b n j)) Filter.atTop (nhds 0) := by
  let c := ZMod.stdAddChar (-j)
  have hp' := tendsto_harmonic_power_error τ S (fun r => c • (u r:A)) a
    (fun k hk => tendsto_smul_power_error τ S (fun r => (u r:A)) a hp c k hk) n
  have hm' := tendsto_harmonic_power_error τ S (fun r => star c • star (u r:A)) b
    (fun k hk => tendsto_smul_power_error τ S (fun r => star (u r:A)) b hm (star c) k hk) n
  have he (r) : τ.toPreGNS (unitaryHarmonicError S (u r) a b n j) =
      τ.toPreGNS (S (harmonicPolynomial n (c • (u r:A))) - a*harmonicPolynomial n (c • (u r:A))) -
      τ.toPreGNS (S (harmonicPolynomial n (star c • star (u r:A))) -
        b*harmonicPolynomial n (star c • star (u r:A))) := by
    change τ.toPreGNS (S (harmonicPolynomial n (c • (u r:A)) -
      star (harmonicPolynomial n (c • (u r:A)))) -
      (a * harmonicPolynomial n (c • (u r:A)) - b * star (harmonicPolynomial n (c • (u r:A))))) = _
    simp only [star_harmonicPolynomial, star_smul, map_sub]
    abel
  simpa only [he, sub_self] using hp'.sub hm'

lemma tendsto_preGNS_mul_zero_of_contraction
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (f g : ℕ → A)
    (hf : Filter.Tendsto (fun r => τ.toPreGNS (f r)) Filter.atTop (nhds 0))
    (hg : ∀ r, ‖g r‖ ≤ 1) :
    Filter.Tendsto (fun r => τ.toPreGNS (f r * g r)) Filter.atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun r =>
    (preGNS_norm_mul_right_le τ htr _ _).trans ((mul_le_mul_of_nonneg_right (hg r)
      (norm_nonneg _)).trans_eq (one_mul _)))
  simpa only [norm_zero] using hf.norm

lemma tendsto_harmonic_errorFamily [Nontrivial A]
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (S : A →L[ℂ] A) (u : ℕ → unitary A) (a b : A)
    (hp : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S ((u r:A)^k)-a*(u r:A)^k)) Filter.atTop (nhds 0))
    (hm : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (star (u r:A)^k)-b*star (u r:A)^k)) Filter.atTop (nhds 0))
    (n : ℕ) {K : ℕ} [NeZero K] : Filter.Tendsto
      (fun r => ‖gnsFamily τ (fun j : ZMod (K^2) =>
        unitaryHarmonicError S (u r) a b n j * fourierWindow (u r:A) j)‖)
      Filter.atTop (nhds 0) := by
  have he (j : ZMod (K^2)) := tendsto_preGNS_mul_zero_of_contraction τ htr
    (fun r => unitaryHarmonicError S (u r) a b n j)
    (fun r => fourierWindow (u r:A) j)
    (tendsto_unitaryHarmonicError τ S u a b hp hm n j)
    (fun r => norm_fourierWindow_le_one (u r) j)
  have hf := (PiLp.continuous_toLp (p:=2) (β:=fun _ : ZMod (K^2) => τ.PreGNS)).continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr he)
  have hf' : Filter.Tendsto
      (fun r => gnsFamily τ (fun j : ZMod (K^2) =>
        unitaryHarmonicError S (u r) a b n j * fourierWindow (u r:A) j))
      Filter.atTop (nhds 0) := hf
  simpa only [norm_zero] using hf'.norm

theorem unitary_power_rigidity_of_tendsto
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a * b) = τ (b * a))
    (hfaithful : ∀ x : A, τ (star x * x) = 0 → x = 0)
    (S : A →L[ℂ] A) (u : ℕ → unitary A) (a b : A)
    (hpos : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S ((u r:A)^k)-a*(u r:A)^k)) Filter.atTop (nhds 0))
    (hneg : ∀ k : ℕ, 0 < k → Filter.Tendsto
      (fun r => τ.toPreGNS (S (star (u r:A)^k)-b*star (u r:A)^k)) Filter.atTop (nhds 0)) :
    a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let C : ℝ := (2 * (1 + Real.pi)) * ‖S‖
  have happrox (n : ℕ) (K : ℕ) [NeZero K] :
      (harmonic n : ℝ) * ‖τ.toPreGNS (a-b)‖ ≤
      C + (‖a‖+‖b‖)*((2*n:ℝ)/K) := by
    have he := tendsto_harmonic_errorFamily τ htr S u a b hpos hneg n (K:=K)
    have ht := (tendsto_const_nhds (x := C + (‖a‖+‖b‖)*((2*n:ℝ)/K))).add he
    have ht' : Filter.Tendsto
        (fun r => C + (‖a‖+‖b‖)*((2*n:ℝ)/K) +
          ‖gnsFamily τ (fun j : ZMod (K^2) => unitaryHarmonicError S (u r) a b n j *
            fourierWindow (u r:A) j)‖) Filter.atTop
        (nhds (C + (‖a‖+‖b‖)*((2*n:ℝ)/K))) := by simpa only [add_zero] using ht
    apply ge_of_tendsto ht'
    exact Filter.Eventually.of_forall fun r =>
      unitary_power_approx_multiplier_bound τ h1 htr S (u r) a b n (K:=K)
  have hbound (n : ℕ) : (harmonic n : ℝ) * ‖τ.toPreGNS (a - b)‖ ≤ C := by
    have hl : Filter.Tendsto (fun m : ℕ =>
        C + (‖a‖ + ‖b‖) * ((2 * n : ℝ) / ((m : ℝ) + 1)))
        Filter.atTop (nhds C) := by
      simpa only [mul_zero, add_zero, mul_one_div] using
        tendsto_const_nhds.add
          ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * (n : ℝ)) |>.const_mul (‖a‖ + ‖b‖))
    apply ge_of_tendsto hl
    apply Filter.Eventually.of_forall
    intro m
    simpa only [Nat.cast_add, Nat.cast_one] using
      happrox n (m+1)
  have hdiv : Filter.Tendsto (fun n : ℕ => (harmonic n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono log_add_one_le_harmonic
      (Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop : Filter.Tendsto (fun n : ℕ => (n : ℝ))
          Filter.atTop Filter.atTop).comp (Filter.tendsto_add_atTop_nat 1)))
  have hz : ‖τ.toPreGNS (a - b)‖ = 0 := by
    by_contra hne
    have hp : 0 < ‖τ.toPreGNS (a - b)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    obtain ⟨n, hn⟩ := ((hdiv.atTop_mul_const hp).eventually_gt_atTop C).exists
    exact (not_lt_of_ge (hbound n)) hn
  exact sub_eq_zero.mp ((preGNS_norm_eq_zero_iff τ hfaithful (a - b)).mp hz)

end
end HochschildRigidity

namespace HochschildMatrixDilation
noncomputable section
open scoped ComplexOrder
open Filter HochschildRigidity
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (τ : A →ₚ[ℂ] ℂ)

lemma matrixTrace_entry_le (M : Mat A) (i j : Fin 2) :
    ‖τ.toPreGNS (M i j)‖ ≤ 2 * ‖(matrixTrace τ).toPreGNS M‖ := by
  have he := matrixTrace_norm_sq τ M
  have h00 := sq_nonneg ‖τ.toPreGNS (M 0 0)‖
  have h10 := sq_nonneg ‖τ.toPreGNS (M 1 0)‖
  have h01 := sq_nonneg ‖τ.toPreGNS (M 0 1)‖
  have h11 := sq_nonneg ‖τ.toPreGNS (M 1 1)‖
  have hM := sq_nonneg ‖(matrixTrace τ).toPreGNS M‖
  have hn00 : ‖τ.toPreGNS (M 0 0)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  have hn10 : ‖τ.toPreGNS (M 1 0)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  have hn01 : ‖τ.toPreGNS (M 0 1)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  have hn11 : ‖τ.toPreGNS (M 1 1)‖^2 ≤ (2*‖(matrixTrace τ).toPreGNS M‖)^2 := by nlinarith
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  fin_cases i <;> fin_cases j
  · exact hn00
  · exact hn01
  · exact hn10
  · exact hn11

lemma tendsto_matrixTrace_of_entries (M : ℕ → Mat A)
    (hM : ∀ i j, Tendsto (fun r => ‖τ.toPreGNS (M r i j)‖) atTop (nhds 0)) :
    Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (M r)‖) atTop (nhds 0) := by
  have he : Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (M r)‖^2) atTop (nhds 0) := by
    simp_rw [matrixTrace_norm_sq]
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add, zero_div] using
      ((((hM 0 0).pow 2).add ((hM 1 0).pow 2)).add ((hM 0 1).pow 2) |>.add ((hM 1 1).pow 2) |>.div_const 2)
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using he.sqrt

lemma matrixMap_sequential (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (M : ℕ → Mat A) (hM : ∃ C : ℝ, ∀ r, ‖M r‖ ≤ C)
    (ht : Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (M r)‖) atTop (nhds 0)) :
    Tendsto (fun r => ‖(matrixTrace τ).toPreGNS (matrixMap R (M r))‖) atTop (nhds 0) := by
  apply tendsto_matrixTrace_of_entries
  intro i j
  apply hR (fun r => M r i j)
  · obtain ⟨C,hC⟩ := hM
    exact ⟨C,fun r => CStarMatrix.norm_entry_le_norm.trans (hC r)⟩
  · exact squeeze_zero (fun _ => norm_nonneg _) (fun r => matrixTrace_entry_le τ (M r) i j)
      (by simpa only [mul_zero] using ht.const_mul 2)

lemma preGNS_norm_pow_sub_le [Nontrivial A]
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (a b : A)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (k : ℕ) :
    ‖τ.toPreGNS (a^k-b^k)‖ ≤ (k:ℝ)*‖τ.toPreGNS (a-b)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he : a^(k+1)-b^(k+1) = a*(a^k-b^k)+(a-b)*b^k := by
      rw [pow_succ' a, pow_succ' b]
      noncomm_ring
    rw [he, map_add]
    have hbk : ‖b^k‖ ≤ 1 := (norm_pow_le b k).trans (by simpa using pow_le_pow_left₀ (norm_nonneg b) hb k)
    calc
      _ ≤ ‖τ.toPreGNS (a*(a^k-b^k))‖+‖τ.toPreGNS ((a-b)*b^k)‖ := norm_add_le _ _
      _ ≤ ‖a‖*‖τ.toPreGNS (a^k-b^k)‖+‖b^k‖*‖τ.toPreGNS (a-b)‖ :=
        add_le_add (preGNS_norm_mul_le τ _ _) (preGNS_norm_mul_right_le τ htr _ _)
      _ ≤ 1*((k:ℝ)*‖τ.toPreGNS (a-b)‖)+1*‖τ.toPreGNS (a-b)‖ := by gcongr
      _ = _ := by push_cast; ring

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma diag_pow (a b : A) (k : ℕ) : (diag a b)^k = diag (a^k) (b^k) := by
  induction k with
  | zero => simp
  | succ k ih => simp only [pow_succ, ih, diag_mul]

lemma tendsto_multiplier_error_transfer (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (x y : ℕ → A) (c : A)
    (hb : ∃ C : ℝ, ∀ r, ‖x r-y r‖ ≤ C)
    (hd : Tendsto (fun r => ‖τ.toPreGNS (x r-y r)‖) atTop (nhds 0))
    (hy : Tendsto (fun r => ‖τ.toPreGNS (R (y r)-c*y r)‖) atTop (nhds 0)) :
    Tendsto (fun r => ‖τ.toPreGNS (R (x r)-c*x r)‖) atTop (nhds 0) := by
  have hr := hR (fun r => x r-y r) hb hd
  have hmajor := (hr.add (hd.const_mul ‖c‖)).add hy
  simp only [mul_zero, zero_add] at hmajor
  apply squeeze_zero (fun _ => norm_nonneg _) _ hmajor
  intro r
  have he : R (x r)-c*x r = (R (x r-y r)-c*(x r-y r))+(R (y r)-c*y r) := by
    rw [map_sub, mul_sub]; abel
  rw [he]
  simp only [map_add, map_sub]
  have hn := preGNS_norm_mul_le τ c (x r-y r)
  rw [map_sub] at hn
  calc
    _ ≤ ‖τ.toPreGNS (R (x r-y r)) - τ.toPreGNS (c*(x r-y r))‖ +
        ‖τ.toPreGNS (R (y r)-c*y r)‖ := by
      simpa only [map_sub] using (norm_add_le
        (τ.toPreGNS (R (x r-y r)) - τ.toPreGNS (c*(x r-y r)))
        (τ.toPreGNS (R (y r)-c*y r)))
    _ ≤ _ := by
      have h := norm_sub_le (τ.toPreGNS (R (x r-y r))) (τ.toPreGNS (c*(x r-y r)))
      simp only [map_sub] at h ⊢
      linarith

lemma tendsto_preGNS_pow_sub [Nontrivial A]
    (htr : ∀ a b : A, τ (a*b) = τ (b*a)) (x y : ℕ → A)
    (hx : ∀ r, ‖x r‖ ≤ 1) (hy : ∀ r, ‖y r‖ ≤ 1)
    (hd : Tendsto (fun r => ‖τ.toPreGNS (x r-y r)‖) atTop (nhds 0)) (k : ℕ) :
    Tendsto (fun r => ‖τ.toPreGNS ((x r)^k-(y r)^k)‖) atTop (nhds 0) := by
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun r => preGNS_norm_pow_sub_le τ htr (x r) (y r) (hx r) (hy r) k)
  simpa only [mul_zero] using hd.const_mul (k:ℝ)

theorem contraction_power_rigidity
    (h1 : τ 1 = 1) (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ x : A, τ (star x*x) = 0 → x = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (q : ℕ → A) (hq : ∀ r, ‖q r‖ ≤ 1)
    (hdef : Tendsto (fun r => (τ (1-star (q r)*q r)).re) atTop (nhds 0))
    (a b : A)
    (hp : ∀ k : ℕ, 0 < k → Tendsto
      (fun r => ‖τ.toPreGNS (R ((q r)^k)-a*(q r)^k)‖) atTop (nhds 0))
    (hm : ∀ k : ℕ, 0 < k → Tendsto
      (fun r => ‖τ.toPreGNS (R (star (q r)^k)-b*star (q r)^k)‖) atTop (nhds 0)) :
    a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let U : ℕ → unitary (Mat A) := fun r => dilation (q r) (hq r)
  let D : ℕ → Mat A := fun r => diag (q r) (star (q r))
  let T := matrixTrace τ
  have hTtr := matrixTrace_tracial τ htr
  have hD (r : ℕ) : ‖D r‖ ≤ 1 := by
    exact (norm_diag_le _ _).trans (max_le (hq r) (by simpa only [norm_star] using hq r))
  have hU (r : ℕ) : ‖(U r:Mat A)‖ ≤ 1 := by simp
  have hd : Tendsto (fun r => ‖T.toPreGNS ((U r:Mat A)-D r)‖) atTop (nhds 0) := by
    have hs : Tendsto (fun r => ‖T.toPreGNS ((U r:Mat A)-D r)‖^2) atTop (nhds 0) := by
      simpa only [U,D,T,dilation_error_sq τ htr] using hdef
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt
  have hmd : Tendsto (fun r => ‖T.toPreGNS (star (U r:Mat A)-star (D r))‖)
      atTop (nhds 0) := by
    simpa only [← star_sub, preGNS_norm_star T hTtr] using hd
  have hdpos (k : ℕ) := tendsto_preGNS_pow_sub T hTtr (fun r => (U r:Mat A)) D hU hD hd k
  have hdneg (k : ℕ) := tendsto_preGNS_pow_sub T hTtr (fun r => star (U r:Mat A))
    (fun r => star (D r)) (by simpa only [norm_star] using hU)
    (by simpa only [norm_star] using hD) hmd k
  have hbound (x y : ℕ → Mat A) (hx : ∀ r, ‖x r‖ ≤ 1) (hy : ∀ r, ‖y r‖ ≤ 1)
      (k : ℕ) : ∃ C : ℝ, ∀ r, ‖(x r)^k-(y r)^k‖ ≤ C := by
    refine ⟨2,fun r => (norm_sub_le _ _).trans ?_⟩
    have hxk : ‖(x r)^k‖ ≤ 1 := (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg (x r)) (hx r) k)
    have hyk : ‖(y r)^k‖ ≤ 1 := (norm_pow_le _ _).trans (by simpa using pow_le_pow_left₀ (norm_nonneg (y r)) (hy r) k)
    linarith
  have hdp (k : ℕ) (hk : 0 < k) : Tendsto
      (fun r => ‖T.toPreGNS (matrixMap R ((D r)^k)-diag a b*(D r)^k)‖) atTop (nhds 0) := by
    apply tendsto_matrixTrace_of_entries
    intro i j
    simp only [D,diag_pow,matrixMap_diag,diag_mul]
    fin_cases i <;> fin_cases j
    · simpa [diag] using hp k hk
    · simp [diag]
    · simp [diag]
    · simpa [diag] using hm k hk
  have hdm (k : ℕ) (hk : 0 < k) : Tendsto
      (fun r => ‖T.toPreGNS (matrixMap R (star (D r)^k)-diag b a*star (D r)^k)‖) atTop (nhds 0) := by
    apply tendsto_matrixTrace_of_entries
    intro i j
    simp only [D,star_diag,star_star,diag_pow,matrixMap_diag,diag_mul]
    fin_cases i <;> fin_cases j
    · simpa [diag] using hm k hk
    · simp [diag]
    · simp [diag]
    · simpa [diag] using hp k hk
  have he : diag a b = diag b a := unitary_power_rigidity_of_tendsto T
    (matrixTrace_one τ h1) hTtr (matrixTrace_faithful τ hf) (matrixMap R) U (diag a b) (diag b a)
    (fun k hk => tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_multiplier_error_transfer T (matrixMap R) (matrixMap_sequential τ R hR)
        (fun r => (U r:Mat A)^k) (fun r => (D r)^k) (diag a b)
        (hbound _ _ hU hD k) (hdpos k) (hdp k hk)))
    (fun k hk => tendsto_zero_iff_norm_tendsto_zero.mpr
      (tendsto_multiplier_error_transfer T (matrixMap R) (matrixMap_sequential τ R hR)
        (fun r => star (U r:Mat A)^k) (fun r => star (D r)^k) (diag b a)
        (hbound _ _ (by simpa only [norm_star] using hU)
          (by simpa only [norm_star] using hD) k) (hdneg k) (hdm k hk)))
  exact congrArg (fun M : Mat A => M 0 0) he
end
end HochschildMatrixDilation
end
end OAI
end

section
namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
namespace HochschildFirstLetter
noncomputable section
open Filter Topology
open scoped Polynomial ComplexOrder
open HochschildFreeSums HochschildNewtonPolar HochschildBlockSpan
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma tendsto_norm_of_span (τ : A →ₚ[ℂ] ℂ)
    (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A) (a : A) (b : Bool)
    (hR : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → R (u r g) = a*u r g)
    {x : ℕ → A} (hx : x ∈ span (fun r => freeSum (u r)) b) :
    Tendsto (fun r => ‖R (x r)-a*x r‖) atTop (nhds 0) := by
  let T : A →L[ℝ] A := (R-ContinuousLinearMap.mul ℂ A a).restrictScalars ℝ
  have hT : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends b g.toWord → T (u r g) = 0 := by
    intro r g hnodup hends
    change R (u r g)-a*u r g = 0
    rw [hR r g hnodup hends,sub_self]
  have ht := (tendsto_of_mem τ u h1 hu hfree htr hf T b hT hx).norm
  change Tendsto (fun r => ‖R (x r)-a*x r‖) atTop (nhds ‖(0:A)‖) at ht
  simpa only [norm_zero] using ht

lemma choose_diagonal (E : Bool → ℕ → ℕ → ℕ → ℝ) (c : ℕ → ℕ → ℝ) (C : ℕ → ℝ)
    (hE : ∀ b n k, 0 < k → Tendsto (E b n k) atTop (nhds 0))
    (hc : ∀ n, Tendsto (c n) atTop (nhds (C n))) :
    ∃ r : ℕ → ℕ, (∀ n, |c n (r n)-C n| < 1/(n+1:ℝ)) ∧
      (∀ b n k, 0 < k → k ≤ n → E b n k (r n) < 1/(n+1:ℝ)) := by
  have hex (n : ℕ) : ∃ r, |c n r-C n| < 1/(n+1:ℝ) ∧
      ∀ b k, 0 < k → k ≤ n → E b n k r < 1/(n+1:ℝ) := by
    have heps : 0 < 1/(n+1:ℝ) := by positivity
    have he : ∀ᶠ r in atTop, ∀ b k, 0 < k → k ≤ n → E b n k r < 1/(n+1:ℝ) := by
      apply eventually_all.mpr
      intro b
      have hb : ∀ᶠ r in atTop, ∀ k ∈ Finset.Icc 1 n, E b n k r < 1/(n+1:ℝ) := by
        apply (eventually_all_finset _).mpr
        intro k hk
        exact (hE b n k (Finset.mem_Icc.mp hk).1).eventually (gt_mem_nhds heps)
      filter_upwards [hb] with r hr
      intro k hk hkn
      exact hr k (Finset.mem_Icc.mpr ⟨hk,hkn⟩)
    have hd : ∀ᶠ r in atTop, |c n r-C n| < 1/(n+1:ℝ) := by
      simpa only [Real.dist_eq] using (hc n).eventually (Metric.ball_mem_nhds _ heps)
    exact (hd.and he).exists
  choose r hr using hex
  exact ⟨r,fun n => (hr n).1,fun b n k hk hkn => (hr n).2 b k hk hkn⟩

lemma diagonal_error_tendsto (E : Bool → ℕ → ℕ → ℕ → ℝ) (r : ℕ → ℕ)
    (h0 : ∀ b n k j, 0 ≤ E b n k j)
    (he : ∀ b n k, 0 < k → k ≤ n → E b n k (r n) < 1/(n+1:ℝ))
    (b : Bool) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n => E b n k (r n)) atTop (nhds 0) := by
  have hinv : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (nhds 0) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (nhds 0))
  apply squeeze_zero' (Filter.Eventually.of_forall fun n => h0 b n k (r n)) _ hinv
  filter_upwards [eventually_ge_atTop k] with n hn
  exact (he b n k hk hn).le

theorem finite_config_rigidity
    (τ : A →ₚ[ℂ] ℂ) (u : (r : ℕ) → FreeGroup (Fin (r+1)) →* A)
    (h1 : τ 1 = 1) (hu : ∀ r g, star (u r g) = u r g⁻¹)
    (hfree : ∀ r g, g ≠ 1 → τ (u r g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (a b : A)
    (hp : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends true g.toWord → R (u r g) = a*u r g)
    (hm : ∀ r (g : FreeGroup (Fin (r+1))), (g.toWord.map Prod.fst).Nodup →
      HochschildBlockWords.Ends false g.toWord → R (u r g) = b*u r g) : a = b := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact Subsingleton.elim _ _
  let s : ℕ → A := fun r => freeSum (u r)
  let q : ℕ → ℕ → A := fun n r => polarApprox (s r) n
  let E : Bool → ℕ → ℕ → ℕ → ℝ := fun t n k r =>
    if t then ‖R ((q n r)^k)-a*(q n r)^k‖ else
      ‖R (star (q n r)^k)-b*star (q n r)^k‖
  let c : ℕ → ℕ → ℝ := fun n r => (τ ((1-(1/4:ℝ) • (star (s r)*s r))^(n+1))).re
  let C : ℕ → ℝ := fun n => catalanFunctional (HochschildCatalan.cutoff^(n+1))
  have hE : ∀ t n k, 0 < k → Tendsto (E t n k) atTop (nhds 0) := by
    intro t n k hk
    cases t
    · change Tendsto (fun r => ‖R (star (q n r)^k)-b*star (q n r)^k‖) _ _
      apply tendsto_norm_of_span τ u h1 hu hfree htr hf R b false hm
      exact pow_mem s false (star_mem s true (polarApprox_mem s n)) k hk
    · change Tendsto (fun r => ‖R ((q n r)^k)-a*(q n r)^k‖) _ _
      apply tendsto_norm_of_span τ u h1 hu hfree htr hf R a true hp
      exact pow_mem s true (polarApprox_mem s n) k hk
  have hc (n : ℕ) : Tendsto (c n) atTop (nhds (C n)) := by
    have h := polynomial_moments_tendsto τ s (freeSum_moments_tendsto τ u h1 hu hfree)
      (HochschildCatalan.cutoff^(n+1))
    simpa only [c,C,HochschildCatalan.cutoff,map_pow,map_sub,map_one,map_mul,
      Polynomial.aeval_C,Polynomial.aeval_X,← Algebra.smul_def] using h
  obtain ⟨r,hc',he⟩ := choose_diagonal E c C hE hc
  have hs (r : ℕ) : ‖s r‖ ≤ 2 := norm_freeSum_le_two τ (u r) h1 (hu r) (hfree r) htr hf
  have hq (n r : ℕ) : ‖q n r‖ ≤ 1 := polarApprox_norm_le_one (s r) (hs r) n
  have hE0 (t : Bool) (n k j : ℕ) : 0 ≤ E t n k j := by cases t <;> exact norm_nonneg _
  have htE (t : Bool) (k : ℕ) (hk : 0 < k) := diagonal_error_tendsto E r hE0 he t k hk
  have hinv : Tendsto (fun n : ℕ => 1/(n+1:ℝ)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hdef : Tendsto (fun n => (τ (1-star (q n (r n))*q n (r n))).re) atTop (nhds 0) := by
    apply squeeze_zero (fun n => (τ.map_nonneg (defect_nonneg (s (r n)) (hs (r n)) n)).1)
      (fun n => ?_) (by simpa only [add_zero] using cutoff_catalan_tendsto_zero.add hinv)
    have hle := (τ.monotone (defect_le_cutoff (s (r n)) (hs (r n)) n)).1
    have hcupper := (abs_lt.mp (hc' n)).2
    change (τ (1-star (q n (r n))*q n (r n))).re ≤ c n (r n) at hle
    change (τ (1-star (q n (r n))*q n (r n))).re ≤ C n+1/(n+1:ℝ)
    linarith
  apply HochschildMatrixDilation.contraction_power_rigidity τ h1 htr hf R hR
    (fun n => q n (r n)) (fun n => hq n (r n)) hdef a b
  · intro k hk
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => HochschildRigidity.preGNS_norm_le τ h1 _)
    exact htE true k hk
  · intro k hk
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => HochschildRigidity.preGNS_norm_le τ h1 _)
    exact htE false k hk

lemma toWord_map_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (g : FreeGroup α) :
    (FreeGroup.map f g).toWord = g.toWord.map (fun z => (f z.1,z.2)) := by
  have hm : FreeGroup.IsReduced (g.toWord.map (fun z => (f z.1,z.2))) := by
    rw [FreeGroup.IsReduced,List.isChain_map]
    exact FreeGroup.isReduced_toWord.imp (fun a b h he => h (hf he))
  conv_lhs => rw [← (FreeGroup.mk_toWord (x:=g)),FreeGroup.map.mk,FreeGroup.toWord_mk]
  exact hm.reduce_eq

theorem countable_first_letter_rigidity
    (τ : A →ₚ[ℂ] ℂ) (u : FreeGroup ℕ →* A)
    (h1 : τ 1 = 1) (hu : ∀ g, star (u g) = u g⁻¹)
    (hfree : ∀ g, g ≠ 1 → τ (u g) = 0)
    (htr : ∀ a b : A, τ (a*b) = τ (b*a))
    (hf : ∀ a : A, τ (star a*a) = 0 → a = 0)
    (R : A →L[ℂ] A)
    (hR : ∀ x : ℕ → A, (∃ C : ℝ, ∀ r, ‖x r‖ ≤ C) →
      Tendsto (fun r => ‖τ.toPreGNS (x r)‖) atTop (nhds 0) →
      Tendsto (fun r => ‖τ.toPreGNS (R (x r))‖) atTop (nhds 0))
    (a b : A)
    (hw : ∀ (g : FreeGroup ℕ) i t l, g.toWord = (i,t)::l →
      (g.toWord.map Prod.fst).Nodup → R (u g) = (if t then a else b)*u g) :
    a = b := by
  let v (r : ℕ) := u.comp (FreeGroup.map (Fin.val : Fin (r+1) → ℕ))
  have hv (r : ℕ) (g : FreeGroup (Fin (r+1))) : star (v r g) = v r g⁻¹ := by
    simp only [v,MonoidHom.comp_apply,hu,map_inv]
  have hvfree (r : ℕ) (g : FreeGroup (Fin (r+1))) (hg : g ≠ 1) : τ (v r g) = 0 := by
    apply hfree
    exact fun he => hg ((FreeGroup.map_injective Fin.val_injective) (he.trans (map_one _).symm))
  have hvword (r : ℕ) (g : FreeGroup (Fin (r+1))) (t : Bool)
      (hn : (g.toWord.map Prod.fst).Nodup) (he : HochschildBlockWords.Ends t g.toWord) :
      R (v r g) = (if t then a else b)*v r g := by
    obtain ⟨⟨i,l,hl⟩,_⟩ := he
    let h : FreeGroup ℕ := FreeGroup.map Fin.val g
    have hh := toWord_map_injective Fin.val Fin.val_injective g
    apply hw h i.val t (l.map (fun z => (z.1.val,z.2)))
    · rw [hh,hl,List.map_cons]
    · rw [hh,List.map_map]
      simpa only [List.map_map,Function.comp_def] using (hn.map Fin.val_injective)
  apply finite_config_rigidity τ v h1 hv hvfree htr hf R hR a b
  · intro r g hn he
    exact hvword r g true hn he
  · intro r g hn he
    exact hvword r g false hn he
end
end HochschildFirstLetter
end
end OAI
end

theorem solution.{u_1} : type_of% @OAI.HochschildFirstLetter.countable_first_letter_rigidity.{u_1} := @OAI.HochschildFirstLetter.countable_first_letter_rigidity.{u_1}
