-- Prove2me | solution 1 for OAI.PlanarUnitDistances.IncidenceSequence.diagonal_sequence
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T03:03:30.869359+00:00
-- url     : https://prove2.me/submissions/8525e5b2-b8c0-4e2a-ad5d-a82a9fb85167

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    dite p a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Cutting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.CircleCutting
open Set Polynomial

lemma plane_dist_sq (p q : Plane) :
    dist p q ^ 2 = (p 0-q 0)^2+(p 1-q 1)^2 := by
  rw [dist_eq_norm,EuclideanSpace.norm_sq_eq,Fin.sum_univ_two]
  simp only [WithLp.ofLp_sub,Pi.sub_apply,Real.norm_eq_abs,sq_abs]

lemma mem_circleIntersections {Q : Finset Plane} {c d p : Plane}
    (hc : c ∈ Q) (hd : d ∈ Q) (hcd : c ≠ d)
    (hpc : dist p c = 1) (hpd : dist p d = 1) : p ∈ circleIntersections Q := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨(c,d),Finset.mem_product.mpr ⟨hc,hd⟩,?_⟩
  simp only [dite_eq_right hcd,Set.Finite.mem_toFinset,mem_ofPred_eq]
  exact ⟨hpc,hpd⟩

lemma direction_unit (t : ℝ) : (direction t 0)^2+(direction t 1)^2 = 1 := by
  have ht : 1+t^2 ≠ 0 := by nlinarith [sq_nonneg t]
  simp only [direction,WithLp.ofLp_toLp,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  field_simp
  ring

lemma directionPolynomial_ne_zero {a b c : ℝ} (h : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) :
    directionPolynomial a b c ≠ 0 := by
  intro hz
  have h0 := congrArg (fun p : Polynomial ℝ => p.coeff 0) hz
  have h1 := congrArg (fun p : Polynomial ℝ => p.coeff 1) hz
  have h2 := congrArg (fun p : Polynomial ℝ => p.coeff 2) hz
  norm_num [directionPolynomial, coeff_one, coeff_X] at h0 h1 h2
  rcases h with h | h | h <;> apply h <;> linarith

lemma directionPolynomial_eval (a b c t : ℝ) :
    (directionPolynomial a b c).eval t =
      (direction t 0*a+direction t 1*b-c)*(1+t^2) := by
  have ht : 1+t^2 ≠ 0 := by nlinarith [sq_nonneg t]
  simp only [directionPolynomial,eval_sub,eval_add,eval_mul,eval_C,eval_one,eval_pow,
    eval_X,Polynomial.eval_ofNat,direction,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  field_simp

lemma avoids_finite_polynomials {ι : Type*} [Finite ι]
    (f : ι → Polynomial ℝ) (hf : ∀ i, f i ≠ 0) :
    ∃ t : ℝ, ∀ i, (f i).eval t ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  let F := ∏ i, f i
  have hF : F ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hf i)
  have he : ∃ t, F.eval t ≠ 0 := by
    by_contra h
    push Not at h
    exact hF (Polynomial.zero_of_eval_zero F h)
  obtain ⟨t,ht⟩ := he
  refine ⟨t,fun i hi => ht ?_⟩
  simp only [F,eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

theorem exists_good_direction (A P Q : Finset Plane) :
    ∃ e : Plane, (e 0)^2+(e 1)^2 = 1 ∧
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → projection e a ≠ projection e b) ∧
      (∀ p ∈ P, ∀ c ∈ Q, projection e (p-c) ≠ 1 ∧ projection e (p-c) ≠ -1) := by
  classical
  let I := {ab : A × A // ab.1 ≠ ab.2}
  let J := P × Q × Bool
  let f : I ⊕ J → Polynomial ℝ := fun k => match k with
    | .inl ab => directionPolynomial ((ab.val.1 : Plane) 0-(ab.val.2 : Plane) 0)
        ((ab.val.1 : Plane) 1-(ab.val.2 : Plane) 1) 0
    | .inr pc => directionPolynomial ((pc.1 : Plane) 0-(pc.2.1 : Plane) 0)
        ((pc.1 : Plane) 1-(pc.2.1 : Plane) 1) (if pc.2.2 then 1 else -1)
  have hf : ∀ k, f k ≠ 0 := by
    intro k
    cases k with
    | inl ab =>
      apply directionPolynomial_ne_zero
      by_contra h
      push Not at h
      apply ab.property
      apply Subtype.ext
      ext i
      fin_cases i
      · exact sub_eq_zero.mp h.1
      · exact sub_eq_zero.mp h.2.1
    | inr pc =>
      apply directionPolynomial_ne_zero
      right; right
      split <;> norm_num
  obtain ⟨t,ht⟩ := avoids_finite_polynomials f hf
  refine ⟨direction t,direction_unit t,?_,?_⟩
  · intro a ha b hb hab heq
    have hne := ht (.inl ⟨(⟨a,ha⟩,⟨b,hb⟩),by intro h; exact hab (congrArg Subtype.val h)⟩)
    apply hne
    rw [show f (.inl ⟨(⟨a,ha⟩,⟨b,hb⟩),_⟩) = directionPolynomial (a 0-b 0) (a 1-b 1) 0 from rfl,
      directionPolynomial_eval]
    unfold projection at heq
    have hz : direction t 0*(a 0-b 0)+direction t 1*(a 1-b 1)-0 = 0 := by linarith
    rw [hz,zero_mul]
  · intro p hp c hc
    constructor
    · intro heq
      have hne := ht (.inr (⟨p,hp⟩,⟨c,hc⟩,true))
      apply hne
      change (directionPolynomial (p 0-c 0) (p 1-c 1) 1).eval t = 0
      rw [directionPolynomial_eval]
      change direction t 0*(p 0-c 0)+direction t 1*(p 1-c 1) = 1 at heq
      rw [heq,sub_self,zero_mul]
    · intro heq
      have hne := ht (.inr (⟨p,hp⟩,⟨c,hc⟩,false))
      apply hne
      change (directionPolynomial (p 0-c 0) (p 1-c 1) (-1)).eval t = 0
      rw [directionPolynomial_eval]
      change direction t 0*(p 0-c 0)+direction t 1*(p 1-c 1) = -1 at heq
      rw [heq,sub_self,zero_mul]

lemma rotate_dist (e : Plane) (he : (e 0)^2+(e 1)^2=1) (p q : Plane) :
    dist (rotate e p) (rotate e q) = dist p q := by
  apply (sq_eq_sq₀ (dist_nonneg) (dist_nonneg)).mp
  rw [plane_dist_sq,plane_dist_sq]
  simp only [rotate,projection,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one]
  nlinarith [sq_nonneg (p 0-q 0),sq_nonneg (p 1-q 1)]

lemma rotate_injective (e : Plane) (he : (e 0)^2+(e 1)^2=1) :
    Function.Injective (rotate e) := by
  intro p q h
  apply dist_eq_zero.mp
  rw [← rotate_dist e he,h,dist_self]

lemma circle_intersection_card (c d : Plane) (hcd : c ≠ d) (S : Finset Plane)
    (hS : ∀ p ∈ S, dist p c=1 ∧ dist p d=1) : S.card ≤ 2 := by
  classical
  by_cases hs : (S : Set Plane).Subsingleton
  · exact (Finset.card_le_one.mpr (fun a ha b hb => hs ha hb)).trans (by decide)
  obtain ⟨a,ha,b,hb,hab⟩ := Set.not_subsingleton_iff.mp hs
  apply (Finset.card_le_card (show S ⊆ {a,b} from ?_)).trans Finset.card_le_two
  intro p hp
  have h := EuclideanGeometry.eq_of_dist_eq_of_dist_eq_of_finrank_eq_two
    (by simp : Module.finrank ℝ Plane = 2) hcd hab
    (hS a ha).1 (hS b hb).1 (hS p hp).1
    (hS a ha).2 (hS b hb).2 (hS p hp).2
  simpa only [Finset.mem_insert,Finset.mem_singleton] using h

lemma circleIntersections_card (Q : Finset Plane) :
    (circleIntersections Q).card ≤ 2*Q.card^2 := by
  classical
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun cd _ => show
      (if h : cd.1=cd.2 then ∅ else (finite_circle_intersection cd.1 cd.2 h).toFinset).card ≤ 2 from ?_)).trans
  · simp [Finset.card_product,pow_two,mul_comm]
  · split
    · simp
    · apply circle_intersection_card
      · assumption
      · intro p hp
        simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq] using hp

lemma active_radicand {c : Plane} {x : ℝ} (h : active c x) :
    0 < 1-(x-c 0)^2 := by
  unfold active at h
  nlinarith

lemma closed_radicand {c : Plane} {x : ℝ} (h : c 0-1 ≤ x ∧ x ≤ c 0+1) :
    0 ≤ 1-(x-c 0)^2 := by
  nlinarith

lemma continuous_branch (c : Plane) (b : Bool) : Continuous (branch c b) := by
  cases b <;> unfold branch <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> fun_prop

lemma branch_order {c : Plane} {x : ℝ} (h : active c x) :
    branch c false x < branch c true x := by
  have hs := Real.sqrt_pos.mpr (active_radicand h)
  simp only [branch,Bool.false_eq_true,ite_false,ite_true]
  linarith

lemma graphPoint_unit {c : Plane} {x : ℝ} (b : Bool)
    (h : c 0-1 ≤ x ∧ x ≤ c 0+1) : dist (graphPoint c b x) c = 1 := by
  have hs := Real.sq_sqrt (closed_radicand h)
  have hd := plane_dist_sq (graphPoint c b x) c
  apply (sq_eq_sq₀ dist_nonneg (by positivity : (0:ℝ) ≤ 1)).mp
  rw [hd]
  cases b <;> simp only [graphPoint,branch,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_fin_one,Bool.false_eq_true,ite_false,ite_true]
  all_goals nlinarith

lemma unit_iff_graph {c p : Plane} (h : active c (p 0)) :
    dist p c = 1 ↔ ∃ b : Bool, p 1=branch c b (p 0) := by
  constructor
  · intro hp
    have hd := plane_dist_sq p c
    have hs := Real.sq_sqrt (le_of_lt (active_radicand h))
    rw [hp] at hd
    have he : (p 1-c 1)^2 = (Real.sqrt (1-(p 0-c 0)^2))^2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with hg | hg
    · refine ⟨true,?_⟩
      simp only [branch,ite_true]; linarith
    · refine ⟨false,?_⟩
      simp only [branch,Bool.false_eq_true,ite_false]; linarith
  · rintro ⟨b,hb⟩
    have hp : p = graphPoint c b (p 0) := by
      ext i
      fin_cases i
      · rfl
      · exact hb
    rw [hp]
    exact graphPoint_unit b ⟨le_of_lt h.1,le_of_lt h.2⟩

lemma unit_projection_closed {c p : Plane} (h : dist p c=1) :
    c 0-1 ≤ p 0 ∧ p 0 ≤ c 0+1 := by
  have hd := plane_dist_sq p c
  rw [h] at hd
  constructor <;> nlinarith [sq_nonneg (p 1-c 1)]

lemma active_of_unit_nonextreme {c p : Plane} (h : dist p c=1)
    (hlo : p 0 ≠ c 0-1) (hhi : p 0 ≠ c 0+1) : active c (p 0) :=
  ⟨lt_of_le_of_ne (unit_projection_closed h).1 (Ne.symm hlo),
    lt_of_le_of_ne (unit_projection_closed h).2 hhi⟩

lemma extrema_mem_events {Q : Finset Plane} {c : Plane} (hc : c ∈ Q) :
    c 0-1 ∈ eventAbscissas Q ∧ c 0+1 ∈ eventAbscissas Q := by
  classical
  constructor <;> apply Finset.mem_union_left <;>
    apply Finset.mem_biUnion.mpr <;> refine ⟨c,hc,?_⟩ <;> simp

lemma branch_collision_event {Q : Finset Plane} {c d : Plane}
    (hc : c ∈ Q) (hd : d ∈ Q) {b b' : Bool} {x : ℝ}
    (hx : active c x) (hx' : active d x)
    (hne : (c,b) ≠ (d,b')) (he : branch c b x=branch d b' x) :
    x ∈ eventAbscissas Q := by
  classical
  have hcd : c ≠ d := by
    rintro rfl
    have hbb : b ≠ b' := fun h => hne (by rw [h])
    cases b <;> cases b' <;> simp only [ne_eq,not_true_eq_false] at hbb
    · exact (ne_of_lt (branch_order hx)) he
    · exact (ne_of_gt (branch_order hx)) he
  have hp : graphPoint c b x=graphPoint d b' x := by
    ext i
    fin_cases i
    · rfl
    · exact he
  apply Finset.mem_union_right
  apply Finset.mem_image.mpr
  refine ⟨graphPoint c b x,?_,rfl⟩
  apply mem_circleIntersections hc hd hcd (graphPoint_unit b ⟨hx.1.le,hx.2.le⟩)
  rw [hp]
  exact graphPoint_unit b' ⟨hx'.1.le,hx'.2.le⟩

lemma same_side_of_not_mem {S : Set ℝ} (hS : S.OrdConnected)
    {a x y : ℝ} (ha : a ∉ S) (hx : x ∈ S) (hy : y ∈ S) :
    (a < x ↔ a < y) ∧ (x < a ↔ y < a) := by
  constructor <;> constructor <;> intro h
  · by_contra hn
    exact ha (hS.out hy hx ⟨le_of_not_gt hn,h.le⟩)
  · by_contra hn
    exact ha (hS.out hx hy ⟨le_of_not_gt hn,h.le⟩)
  · by_contra hn
    exact ha (hS.out hx hy ⟨h.le,le_of_not_gt hn⟩)
  · by_contra hn
    exact ha (hS.out hy hx ⟨h.le,le_of_not_gt hn⟩)

lemma active_constant {Q : Finset Plane} {S : Set ℝ} (hS : S.OrdConnected)
    (hE : ∀ x ∈ S, x ∉ eventAbscissas Q) {c : Plane} (hc : c ∈ Q)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : active c x ↔ active c y := by
  have hlo : c 0-1 ∉ S := fun h => hE _ h (extrema_mem_events hc).1
  have hhi : c 0+1 ∉ S := fun h => hE _ h (extrema_mem_events hc).2
  exact and_congr (same_side_of_not_mem hS hlo hx hy).1
    (same_side_of_not_mem hS hhi hx hy).2

lemma order_constant {S : Set ℝ} (hS : S.OrdConnected) {f g : ℝ → ℝ}
    (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hne : ∀ x ∈ S, f x ≠ g x) {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    (hxy : f x < g x) : f y < g y := by
  by_contra hn
  obtain ⟨z,hz,he⟩ := hS.isPreconnected.intermediate_value hx hy (hf.sub hg)
    (show (0:ℝ) ∈ Set.Icc (f x-g x) (f y-g y) from ⟨sub_nonpos.mpr hxy.le,
      sub_nonneg.mpr (le_of_not_gt hn)⟩)
  exact hne z hz (sub_eq_zero.mp he)

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.Sweep
open Finset Classical

variable {α : Type*} [DecidableEq α]

lemma sdiff_triangle (A B C : Finset α) :
    (A \ C).card ≤ (A \ B).card + (B \ C).card := by
  apply (card_le_card (show A \ C ⊆ (A \ B) ∪ (B \ C) from ?_)).trans
    (card_union_le _ _)
  intro a ha
  simp only [mem_sdiff,mem_union] at *
  by_cases h : a ∈ B
  · exact Or.inr ⟨h,ha.2⟩
  · exact Or.inl ⟨ha.1,h⟩

lemma sdiff_insert_same (a : α) (A B : Finset α) :
    (insert a A \ insert a B).card ≤ (A \ B).card := by
  apply card_le_card
  intro x hx
  simp only [mem_sdiff,mem_insert] at *
  exact ⟨hx.1.resolve_left (fun h => hx.2 (Or.inl h)),fun h => hx.2 (Or.inr h)⟩

lemma sdiff_insert_left (a : α) (A B : Finset α) :
    (insert a A \ B).card ≤ 1 + (A \ B).card := by
  apply (card_le_card (show insert a A \ B ⊆ insert a (A \ B) from ?_)).trans
  · exact (card_insert_le _ _).trans_eq (Nat.add_comm _ _)
  · intro x hx
    simp only [mem_sdiff,mem_insert] at *
    exact hx.1.elim Or.inl (fun h => Or.inr ⟨h,hx.2⟩)

lemma sdiff_insert_right (a : α) (A B : Finset α) :
    (A \ insert a B).card ≤ (A \ B).card :=
  card_le_card (sdiff_subset_sdiff (Subset.refl _) (subset_insert _ _))

lemma links_card_le (x : Option α) (L : List α) :
    (links x L).card ≤ L.length+1 := by
  induction L generalizing x with
  | nil => simp [links]
  | cons a L ih =>
    apply (card_insert_le _ _).trans
    simpa only [List.length_cons] using Nat.add_le_add_right (ih (some a)) 1

lemma links_change_start (x y : Option α) (L : List α) :
    (links x L \ links y L).card ≤ 1 := by
  cases L with
  | nil => exact (card_le_card sdiff_subset).trans (by simp [links])
  | cons a L =>
    apply (sdiff_insert_left _ _ _).trans
    have h : links (some a) L \ insert (y,some a) (links (some a) L) = ∅ :=
      sdiff_eq_empty_iff_subset.mpr (subset_insert _ _)
    simp only [links,h,card_empty,add_zero,le_refl]

lemma links_delete_head (x : Option α) (a : α) (L : List α) :
    (links x (a::L) \ links x L).card ≤ 2 ∧
      (links x L \ links x (a::L)).card ≤ 1 := by
  constructor
  · exact (sdiff_insert_left _ _ _).trans (by
      have h := links_change_start (some a) x L
      omega)
  · exact (sdiff_insert_right _ _ _).trans (links_change_start x (some a) L)

theorem links_filter_sdiff (C : Finset α) (x : Option α) (L : List α) :
    (links x L \ links x (L.filter (· ∉ C))).card ≤ 2*(L.filter (· ∈ C)).length ∧
    (links x (L.filter (· ∉ C)) \ links x L).card ≤ (L.filter (· ∈ C)).length := by
  induction L generalizing x with
  | nil => simp [links]
  | cons a L ih =>
    by_cases ha : a ∈ C
    · simp only [List.filter_cons]
      simp only [ha,not_true_eq_false,decide_true,decide_false,
        Bool.false_eq_true,ite_true,ite_false,List.length_cons]
      have h := ih x
      have hd := links_delete_head x a L
      constructor
      · have ht := sdiff_triangle (links x (a::L)) (links x L)
          (links x (L.filter (· ∉ C)))
        omega
      · have ht := sdiff_triangle (links x (L.filter (· ∉ C))) (links x L)
          (links x (a::L))
        omega
    · simp only [List.filter_cons]
      simp only [ha,not_false_eq_true,decide_true,decide_false,
        Bool.false_eq_true,ite_true,ite_false]
      constructor
      · exact (sdiff_insert_same _ _ _).trans (ih (some a)).1
      · exact (sdiff_insert_same _ _ _).trans (ih (some a)).2

lemma links_touch_card (C : Finset α) (x : Option α) (L : List α) :
    ((links x L).filter (touches C)).card ≤
      2*(L.filter (· ∈ C)).length + if ∃ a ∈ C, x = some a then 1 else 0 := by
  classical
  induction L generalizing x with
  | nil =>
    have ht : touches C (x,none) ↔ ∃ a ∈ C, x = some a := by simp [touches]
    by_cases hx : ∃ a ∈ C, x = some a
    · simpa only [links,List.filter_nil,List.length_nil,mul_zero,zero_add,ite_eq_left hx]
        using (card_filter_le (s := ({(x,none)} : Finset (Option α × Option α)))
          (p := touches C)).trans_eq (card_singleton _)
    · have hno : ¬touches C (x,none) := mt ht.mp hx
      simp [links,hx,hno]
  | cons a L ih =>
    have ht : touches C (x,some a) ↔ (∃ b ∈ C, x = some b) ∨ a ∈ C := by
      simp [touches]
    have htail := ih (some a)
    by_cases ha : a ∈ C
    · have hhead : touches C (x,some a) := ht.mpr (Or.inr ha)
      rw [links,filter_insert,ite_eq_left hhead]
      apply (card_insert_le _ _).trans
      simp [ha] at htail ⊢
      split <;> omega
    · simp [ha] at htail
      by_cases hx : ∃ b ∈ C, x = some b
      · rw [links,filter_insert,ite_eq_left (ht.mpr (Or.inl hx))]
        apply (card_insert_le _ _).trans
        simp [ha,hx]
        omega
      · rw [links,filter_insert,ite_eq_right (by simp only [ht,hx,ha,or_self,not_false_eq_true])]
        simpa [ha,hx] using htail

theorem event_starts_card (C : Finset α) (L R : List α)
    (hL : L.Nodup) (hR : R.Nodup)
    (hskel : L.filter (· ∉ C) = R.filter (· ∉ C)) :
    ((gaps R).filter (fun g => g ∉ gaps L ∨ touches C g)).card ≤ 5*C.card := by
  classical
  have hleft : (L.filter (· ∈ C)).length ≤ C.card := by
    rw [← List.toFinset_card_of_nodup (hL.filter _)]
    exact card_le_card (by intro a ha; exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp ha)).2)
  have hright : (R.filter (· ∈ C)).length ≤ C.card := by
    rw [← List.toFinset_card_of_nodup (hR.filter _)]
    exact card_le_card (by intro a ha; exact of_decide_eq_true (List.mem_filter.mp (List.mem_toFinset.mp ha)).2)
  have hd : (gaps R \ gaps L).card ≤ 3*C.card := by
    have ht := sdiff_triangle (gaps R) (gaps (L.filter (· ∉ C))) (gaps L)
    have h1 := (links_filter_sdiff C none R).1
    have h2 := (links_filter_sdiff C none L).2
    change (gaps (L.filter (· ∉ C)) \ gaps L).card ≤ _ at h2
    change (gaps R \ gaps (R.filter (· ∉ C))).card ≤ _ at h1
    rw [← hskel] at h1
    omega
  have hb : ((gaps R).filter (touches C)).card ≤ 2*C.card := by
    have h := links_touch_card C none R
    simp at h
    exact h.trans (Nat.mul_le_mul_left _ hright)
  apply (card_le_card (show (gaps R).filter (fun g => g ∉ gaps L ∨ touches C g) ⊆
      (gaps R \ gaps L) ∪ (gaps R).filter (touches C) from ?_)).trans
      (card_union_le _ _) |>.trans (by omega)
  intro g hg
  simp only [mem_filter,mem_sdiff,mem_union] at *
  exact hg.2.elim (fun h => Or.inl ⟨hg.1,h⟩) (fun h => Or.inr ⟨hg.1,h⟩)

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.SweepIntervals
open Finset Set Classical

lemma between_finsets (A B : Finset ℝ) (h : ∀ a ∈ A, ∀ b ∈ B, a < b) :
    ∃ x : ℝ, (∀ a ∈ A, a < x) ∧ (∀ b ∈ B, x < b) := by
  by_cases hA : A.Nonempty
  · by_cases hB : B.Nonempty
    · obtain ⟨x,hx1,hx2⟩ := exists_between (h _ (A.max'_mem hA) _ (B.min'_mem hB))
      exact ⟨x,fun a ha => (A.le_max' a ha).trans_lt hx1,
        fun b hb => hx2.trans_le (B.min'_le b hb)⟩
    · refine ⟨A.max' hA+1,fun a ha => (A.le_max' a ha).trans_lt (by linarith),?_⟩
      exact fun b hb => False.elim (hB ⟨b,hb⟩)
  · by_cases hB : B.Nonempty
    · refine ⟨B.min' hB-1,?_,fun b hb => (show B.min' hB-1 < B.min' hB by linarith).trans_le (B.min'_le b hb)⟩
      exact fun a ha => False.elim (hA ⟨a,ha⟩)
    · exact ⟨0,fun a ha => False.elim (hA ⟨a,ha⟩),
        fun b hb => False.elim (hB ⟨b,hb⟩)⟩

lemma span_ordConnected {n : ℕ} (a : Fin n → ℝ) (lo hi : ℕ) :
    (span a lo hi).OrdConnected := by
  constructor
  intro x hx y hy z hz
  exact ⟨fun i hi => (hx.1 i hi).trans_le hz.1,
    fun i hi => hz.2.trans_lt (hy.2 i hi)⟩

lemma span_open {n : ℕ} (a : Fin n → ℝ) (lo hi : ℕ) : IsOpen (span a lo hi) := by
  change IsOpen ({x | ∀ i : Fin n, i.val < lo → a i < x} ∩
    {x | ∀ i : Fin n, hi ≤ i.val → x < a i})
  apply IsOpen.inter
  · simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_Ioi
  · simp only [ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro _
    exact isOpen_Iio

lemma slab_nonempty {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a) (k : ℕ) :
    (slab a k).Nonempty := by
  let A := (univ.filter fun i : Fin n => i.val < k).image a
  let B := (univ.filter fun i : Fin n => k ≤ i.val).image a
  obtain ⟨x,hA,hB⟩ := between_finsets A B (by
    intro v hv w hw
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
    apply ha
    change i.val<j.val
    exact lt_of_lt_of_le (mem_filter.mp hi).2 (mem_filter.mp hj).2)
  refine ⟨x,fun i hi => hA _ ?_,fun i hi => hB _ ?_⟩
  · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩
  · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_univ _,hi⟩,rfl⟩

lemma slab_no_event {n : ℕ} {a : Fin n → ℝ} {k : ℕ} {x : ℝ}
    (hx : x ∈ slab a k) (i : Fin n) : x ≠ a i := by
  by_cases h : i.val < k
  · exact ne_of_gt (hx.1 i h)
  · exact ne_of_lt (hx.2 i (le_of_not_gt h))

lemma count_lt_iff {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a) (x : ℝ) (i : Fin n) :
    i.val < (univ.filter fun j => a j < x).card ↔ a i < x := by
  constructor
  · intro hi
    by_contra hn
    have hs : (univ.filter fun j => a j < x) ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      apply ha.lt_iff_lt.mp
      exact (mem_filter.mp hj).2.trans_le (le_of_not_gt hn)
    have hh := Finset.card_le_card hs
    simp only [Fin.card_Iio] at hh
    omega
  · intro hi
    have hs : Finset.Iic i ⊆ (univ.filter fun j => a j < x) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ j,(ha.monotone (Finset.mem_Iic.mp hj)).trans_lt hi⟩
    have hh := Finset.card_le_card hs
    simp only [Fin.card_Iic] at hh
    omega

lemma cover_slabs {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a) {x : ℝ}
    (hx : ∀ i, x ≠ a i) : ∃ k ≤ n, x ∈ slab a k := by
  let k := (univ.filter fun j => a j < x).card
  refine ⟨k,(card_filter_le _ _).trans (by simp),?_,?_⟩
  · intro i hi
    exact (count_lt_iff ha x i).mp hi
  · intro i hi
    have hn : ¬a i < x := fun h => (not_lt_of_ge hi) ((count_lt_iff ha x i).mpr h)
    exact lt_of_le_of_ne (le_of_not_gt hn) (hx i)

lemma slab_subset_span {n : ℕ} {a : Fin n → ℝ} {lo hi k : ℕ}
    (hl : lo ≤ k) (hh : k ≤ hi) : slab a k ⊆ span a lo hi := by
  intro x hx
  exact ⟨fun i hi => hx.1 i (hi.trans_le hl),fun i hi => hx.2 i (hh.trans hi)⟩

lemma span_decomposition {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {lo hi : ℕ} (hlo : lo ≤ hi) (hhi : hi ≤ n) {x : ℝ} (hx : x ∈ span a lo hi) :
    (∃ j : Fin n, lo ≤ j.val ∧ j.val < hi ∧ x=a j) ∨
      ∃ k, lo ≤ k ∧ k ≤ hi ∧ x ∈ slab a k := by
  by_cases he : ∃ j, x=a j
  · obtain ⟨j,rfl⟩ := he
    left
    refine ⟨j,?_,?_,rfl⟩
    · by_contra hn
      exact lt_irrefl _ (hx.1 j (lt_of_not_ge hn))
    · by_contra hn
      exact lt_irrefl _ (hx.2 j (le_of_not_gt hn))
  · push Not at he
    obtain ⟨k,hk,hxk⟩ := cover_slabs ha he
    right
    refine ⟨k,?_,?_,hxk⟩
    · by_contra hn
      have hkl : k<lo := lt_of_not_ge hn
      by_cases hkn : k<n
      · exact lt_asymm (hxk.2 ⟨k,hkn⟩ le_rfl) (hx.1 ⟨k,hkn⟩ hkl)
      · omega
    · by_contra hn
      have hh : hi<k := lt_of_not_ge hn
      have hin : hi<n := hh.trans_le hk
      exact lt_asymm (hx.2 ⟨hi,hin⟩ le_rfl) (hxk.1 ⟨hi,hin⟩ hh)

end PlanarUnitDistances.SweepIntervals

namespace PlanarUnitDistances.Sweep
open Finset Classical

lemma sorted_heights {α : Type*} (S : Finset α) (f : α → ℝ)
    (hf : Set.InjOn f S) :
    ∃ L : List α, L.Nodup ∧ (∀ a, a ∈ L ↔ a ∈ S) ∧
      L.Pairwise (fun a b => f a < f b) := by
  classical
  let : LinearOrder S := LinearOrder.lift' (fun a => f a) (by
    intro a b h
    exact Subtype.ext (hf a.property b.property h))
  let L := (Finset.univ : Finset S).sort
  refine ⟨L.map Subtype.val,?_,?_,?_⟩
  · exact List.Nodup.map Subtype.val_injective (Finset.sort_nodup _ _)
  · intro a
    simp only [List.mem_map,L,Finset.mem_sort,Finset.mem_univ,true_and]
    exact ⟨fun ⟨b,hb⟩ => hb ▸ b.property,fun ha => ⟨⟨a,ha⟩,rfl⟩⟩
  · exact List.pairwise_map.mpr (Finset.sortedLT_sort _).pairwise

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

lemma mem_labels {Q : Finset Plane} {b : Label} : b ∈ labels Q ↔ b.1 ∈ Q := by
  simp [labels]

lemma mem_activeLabels {Q : Finset Plane} {b : Label} {x : ℝ} :
    b ∈ activeLabels Q x ↔ b.1 ∈ Q ∧ active b.1 x := by
  simp [activeLabels,mem_labels]

lemma height_injOn {Q : Finset Plane} {x : ℝ} (hx : x ∉ eventAbscissas Q) :
    Set.InjOn (fun b => height b x) (activeLabels Q x) := by
  intro b hb d hd he
  by_contra hne
  exact hx (branch_collision_event (mem_activeLabels.mp hb).1
    (mem_activeLabels.mp hd).1 (mem_activeLabels.mp hb).2
    (mem_activeLabels.mp hd).2 hne he)

lemma exists_ordered_branches {Q : Finset Plane} {x : ℝ} (hx : x ∉ eventAbscissas Q) :
    ∃ L : List Label, L.Nodup ∧ (∀ b, b ∈ L ↔ b ∈ activeLabels Q x) ∧
      L.Pairwise (fun b d => height b x < height d x) :=
  Sweep.sorted_heights _ _ (height_injOn hx)

lemma circleEvents_subset {Q : Finset Plane} {c : Plane} (hc : c ∈ Q) :
    circleEvents Q c ⊆ eventAbscissas Q := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (extrema_mem_events hc).1
    · rw [Finset.mem_singleton] at hx
      rw [hx]; exact (extrema_mem_events hc).2
  · obtain ⟨d,hd,hxd⟩ := Finset.mem_biUnion.mp hx
    by_cases hcd : c=d
    · simp [hcd] at hxd
    · simp only [dite_eq_right hcd,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hxd
      obtain ⟨p,hp,rfl⟩ := hxd
      exact Finset.mem_union_right _ (Finset.mem_image.mpr
        ⟨p,mem_circleIntersections hc hd hcd hp.1 hp.2,rfl⟩)

lemma circleEvents_card (Q : Finset Plane) (c : Plane) :
    (circleEvents Q c).card ≤ 2+2*Q.card := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add Finset.card_le_two
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun d _ => show
    (if h : c=d then ∅ else (finite_circle_intersection c d h).toFinset.image (· 0)).card ≤ 2 from ?_)).trans
  · simp [mul_comm]
  · split
    · simp
    · apply Finset.card_image_le.trans
      apply circle_intersection_card
      · assumption
      · intro p hp
        simpa only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] using hp

lemma extrema_mem_circleEvents (Q : Finset Plane) (c : Plane) :
    c 0-1 ∈ circleEvents Q c ∧ c 0+1 ∈ circleEvents Q c := by
  constructor <;> apply Finset.mem_union_left <;> simp

lemma collision_mem_circleEvents {Q : Finset Plane} {c d : Plane}
    (hd : d ∈ Q) (hcd : c ≠ d) {p : Plane} (hc : dist p c=1) (hp : dist p d=1) :
    p 0 ∈ circleEvents Q c := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨d,hd,?_⟩
  simp only [dite_eq_right hcd,Finset.mem_image,Set.Finite.mem_toFinset,Set.mem_ofPred_eq]
  exact ⟨p,⟨hc,hp⟩,rfl⟩

lemma critical_card_sum (Q : Finset Plane) (E : Finset ℝ) :
    ∑ x ∈ E, (critical Q x).card ≤ 4*Q.card+4*Q.card^2 := by
  classical
  have he : ∑ x ∈ E, (critical Q x).card =
      ∑ b ∈ labels Q, (E ∩ circleEvents Q b.1).card := by
    simp only [critical,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.filter_mem_eq_inter,Finset.sum_filter]
  rw [he]
  apply (Finset.sum_le_sum (fun b _ =>
    (Finset.card_le_card Finset.inter_subset_right).trans (circleEvents_card Q b.1))).trans
  simp only [Finset.sum_const,Finset.card_product,labels,Finset.card_univ,Fintype.card_bool,smul_eq_mul]
  nlinarith

lemma active_constant_without_events {Q : Finset Plane} {c : Plane} {S : Set ℝ}
    (hS : S.OrdConnected) (hE : ∀ z ∈ S, z ∉ circleEvents Q c)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S) : active c x ↔ active c y := by
  have hlo : c 0-1 ∉ S := fun h => hE _ h (extrema_mem_circleEvents Q c).1
  have hhi : c 0+1 ∉ S := fun h => hE _ h (extrema_mem_circleEvents Q c).2
  exact and_congr (same_side_of_not_mem hS hlo hx hy).1
    (same_side_of_not_mem hS hhi hx hy).2

lemma height_ne_without_events {Q : Finset Plane} {b d : Label} {x : ℝ}
    (hbd : b ≠ d) (hd : d.1 ∈ Q) (hb : active b.1 x) (hdx : active d.1 x)
    (hx : x ∉ circleEvents Q b.1) : height b x ≠ height d x := by
  intro he
  by_cases hcd : b.1=d.1
  · have hsign : b.2 ≠ d.2 := fun h => hbd (Prod.ext hcd h)
    have hlt := branch_order hb
    change branch b.1 b.2 x=branch d.1 d.2 x at he
    rw [← hcd] at he
    cases hb2 : b.2 <;> cases hd2 : d.2
    all_goals simp only [hb2,hd2,ne_eq,not_true_eq_false] at hsign
    · rw [hb2,hd2] at he; exact hlt.ne he
    · rw [hb2,hd2] at he; exact hlt.ne' he
  · have hp : graphPoint b.1 b.2 x=graphPoint d.1 d.2 x := by
      ext i
      fin_cases i
      · rfl
      · exact he
    have hdx' : dist (graphPoint b.1 b.2 x) d.1=1 := by
      rw [hp]; exact graphPoint_unit d.2 ⟨hdx.1.le,hdx.2.le⟩
    exact hx (collision_mem_circleEvents hd hcd (graphPoint_unit b.2 ⟨hb.1.le,hb.2.le⟩) hdx')

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

lemma skeleton_constant {Q : Finset Plane} {S : Set ℝ} (hS : S.OrdConnected)
    (C : Finset Label) (hC : ∀ b ∈ labels Q, b ∉ C → ∀ z ∈ S, z ∉ circleEvents Q b.1)
    {x y : ℝ} (hx : x ∈ S) (hy : y ∈ S)
    {L R : List Label} (hLn : L.Nodup) (hRn : R.Nodup)
    (hLm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q x)
    (hRm : ∀ b, b ∈ R ↔ b ∈ activeLabels Q y)
    (hLo : L.Pairwise (fun b d => height b x < height d x))
    (hRo : R.Pairwise (fun b d => height b y < height d y)) :
    L.filter (· ∉ C) = R.filter (· ∉ C) := by
  have hm : ∀ b, b ∈ L.filter (· ∉ C) ↔ b ∈ R.filter (· ∉ C) := by
    intro b
    simp only [List.mem_filter,decide_eq_true_eq,hLm,hRm,mem_activeLabels]
    constructor
    · rintro ⟨⟨hb,hbx⟩,hbc⟩
      exact ⟨⟨hb,(active_constant_without_events hS
        (hC b (mem_labels.mpr hb) hbc) hx hy).mp hbx⟩,hbc⟩
    · rintro ⟨⟨hb,hby⟩,hbc⟩
      exact ⟨⟨hb,(active_constant_without_events hS
        (hC b (mem_labels.mpr hb) hbc) hx hy).mpr hby⟩,hbc⟩
  have hp : (L.filter (· ∉ C)).Pairwise (fun b d => height b y < height d y) := by
    apply (hLo.filter _).imp_of_mem
    intro b d hb hd hbd
    have hb' := List.mem_filter.mp hb
    have hd' := List.mem_filter.mp hd
    have hbx := mem_activeLabels.mp ((hLm b).mp hb'.1)
    have hdx := mem_activeLabels.mp ((hLm d).mp hd'.1)
    have he := hC b (mem_labels.mpr hbx.1) (of_decide_eq_true hb'.2)
    have he' := hC d (mem_labels.mpr hdx.1) (of_decide_eq_true hd'.2)
    apply order_constant hS (continuous_branch _ _).continuousOn
      (continuous_branch _ _).continuousOn (fun z hz => ?_) hx hy hbd
    exact height_ne_without_events (fun heq => by rw [heq] at hbd; exact lt_irrefl _ hbd)
      hdx.1 ((active_constant_without_events hS he hx hz).mp hbx.2)
      ((active_constant_without_events hS he' hx hz).mp hdx.2) (he z hz)
  exact List.Perm.eq_of_pairwise (fun _ _ _ _ h h' => False.elim (lt_asymm h h'))
    hp (hRo.filter _) ((List.perm_ext_iff_of_nodup (hLn.filter _) (hRn.filter _)).mpr hm)

lemma event_span_no_other {n : ℕ} {a : Fin n → ℝ} {k i : Fin n} {x : ℝ}
    (hx : x ∈ SweepIntervals.span a k.val (k.val+1)) (he : x=a i) : i=k := by
  apply Fin.ext
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · exact (ne_of_gt (hx.1 i h)) he
  · exact (ne_of_lt (hx.2 i (by omega))) he

lemma event_span_noncritical {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ x, x ∈ eventAbscissas Q ↔ ∃ i, a i=x) (k : Fin n)
    {b : Label} (hb : b ∈ labels Q) (hbc : b ∉ critical Q (a k))
    {z : ℝ} (hz : z ∈ SweepIntervals.span a k.val (k.val+1)) :
    z ∉ circleEvents Q b.1 := by
  intro he
  have hbq := mem_labels.mp hb
  obtain ⟨i,hi⟩ := (ha z).mp (circleEvents_subset hbq he)
  have hik := event_span_no_other hz hi.symm
  rw [hik] at hi
  apply hbc
  exact Finset.mem_filter.mpr ⟨hb,hi ▸ he⟩

theorem event_skeleton {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ x, x ∈ eventAbscissas Q ↔ ∃ i, a i=x) (k : Fin n)
    {x y : ℝ} (hx : x ∈ SweepIntervals.slab a k.val)
    (hy : y ∈ SweepIntervals.slab a (k.val+1))
    {L R : List Label} (hLn : L.Nodup) (hRn : R.Nodup)
    (hLm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q x)
    (hRm : ∀ b, b ∈ R ↔ b ∈ activeLabels Q y)
    (hLo : L.Pairwise (fun b d => height b x < height d x))
    (hRo : R.Pairwise (fun b d => height b y < height d y)) :
    L.filter (· ∉ critical Q (a k)) = R.filter (· ∉ critical Q (a k)) := by
  apply skeleton_constant (SweepIntervals.span_ordConnected _ _ _) _
    (fun b hb hbc z hz => event_span_noncritical ha k hb hbc hz)
    (SweepIntervals.slab_subset_span le_rfl (Nat.le_succ _) hx)
    (SweepIntervals.slab_subset_span (Nat.le_succ _) le_rfl hy)
    hLn hRn hLm hRm hLo hRo

end PlanarUnitDistances.CircleCutting

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sweep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.Sweep
open Finset Classical
variable {α : Type*} [DecidableEq α]

lemma links_cover (f : α → ℝ) (x : Option α) (L : List α) (y : ℝ)
    (hx : Lower f x y) (hy : ∀ a ∈ L, y ≠ f a) :
    ∃ g ∈ links x L, GapBand f g y := by
  induction L generalizing x with
  | nil =>
    exact ⟨(x,none),by simp [links],hx,fun _ h => by cases h⟩
  | cons a L ih =>
    by_cases ha : y<f a
    · refine ⟨(x,some a),Finset.mem_insert_self _ _,hx,?_⟩
      intro b hb
      exact Option.some.inj hb ▸ ha
    · have hay : f a<y := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm (hy a List.mem_cons_self))
      obtain ⟨g,hg,hgy⟩ := ih (some a) (by
        intro b hb
        exact Option.some.inj hb ▸ hay) (fun b hb => hy b (List.mem_cons_of_mem a hb))
      exact ⟨g,Finset.mem_insert_of_mem hg,hgy⟩

lemma links_sound (f : α → ℝ) (x : Option α) (L : List α)
    (hL : L.Pairwise (fun a b => f a<f b))
    (hx : ∀ a, x=some a → ∀ b ∈ L, f a<f b)
    {g : Option α × Option α} (hg : g ∈ links x L) {y : ℝ}
    (hy : GapBand f g y) : Lower f x y ∧ ∀ a ∈ L, y≠f a := by
  induction L generalizing x with
  | nil =>
    have he := Finset.mem_singleton.mp hg
    subst g
    exact ⟨hy.1,by simp⟩
  | cons a L ih =>
    have hL' := List.pairwise_cons.mp hL
    rcases Finset.mem_insert.mp hg with he | hg
    · subst g
      refine ⟨hy.1,?_⟩
      intro b hb
      have hya := hy.2 a rfl
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hya.ne
      · exact (hya.trans (hL'.1 b hb)).ne
    · have hr := ih (some a) hL'.2 (by
        intro b hb c hc
        exact Option.some.inj hb ▸ hL'.1 c hc) hg
      have hay := hr.1 a rfl
      refine ⟨?_,?_⟩
      · intro b hb
        exact (hx b hb a List.mem_cons_self).trans hay
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact hay.ne'
        · exact hr.2 b hb

lemma gaps_cover (f : α → ℝ) (L : List α) (y : ℝ) (hy : ∀ a ∈ L, y≠f a) :
    ∃ g ∈ gaps L, GapBand f g y :=
  links_cover f none L y (fun _ h => by cases h) hy

lemma gaps_avoid (f : α → ℝ) (L : List α)
    (hL : L.Pairwise (fun a b => f a<f b)) {g : Option α × Option α}
    (hg : g ∈ gaps L) {y : ℝ} (hy : GapBand f g y) : ∀ a ∈ L, y≠f a :=
  (links_sound f none L hL (fun _ h => by cases h) hg hy).2

lemma links_endpoints (x : Option α) (L : List α) {g : Option α × Option α}
    (hg : g ∈ links x L) {a : α} (ha : g.1=some a ∨ g.2=some a) :
    x=some a ∨ a ∈ L := by
  induction L generalizing x with
  | nil =>
    have he := Finset.mem_singleton.mp hg
    subst g
    rcases ha with h | h
    · exact Or.inl h
    · exact by cases h
  | cons b L ih =>
    rcases Finset.mem_insert.mp hg with he | hg
    · subst g
      rcases ha with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj h).symm))
    · rcases ih (some b) hg with h | h
      · exact Or.inr (List.mem_cons.mpr (Or.inl (Option.some.inj h).symm))
      · exact Or.inr (List.mem_cons_of_mem b h)

lemma gaps_endpoints (L : List α) {g : Option α × Option α}
    (hg : g ∈ gaps L) {a : α} (ha : g.1=some a ∨ g.2=some a) : a ∈ L := by
  rcases links_endpoints none L hg ha with h | h
  · exact by cases h
  · exact h

end PlanarUnitDistances.Sweep

namespace PlanarUnitDistances.SweepRuns
open Finset Classical
variable {α : Type*}

lemma reach_self {G : ℕ → Finset α} {bad : ℕ → α → Prop} {g : α} {k : ℕ}
    (h : g ∈ G k) : Reach G bad g k k :=
  ⟨le_rfl,fun _ h1 h2 => by simpa only [le_antisymm h2 h1] using h,
    fun _ h1 h2 => False.elim (not_lt_of_ge h1 h2)⟩

lemma reach_extend_left {G : ℕ → Finset α} {bad : ℕ → α → Prop} {g : α}
    {lo hi : ℕ} (hr : Reach G bad g (lo+1) hi) (hmem : g ∈ G lo)
    (hbad : ¬bad lo g) : Reach G bad g lo hi := by
  refine ⟨(Nat.le_succ lo).trans hr.1,?_,?_⟩
  · intro k hk hk'
    by_cases h : k=lo
    · simpa [h] using hmem
    · exact hr.2.1 k (by omega) hk'
  · intro k hk hk'
    by_cases h : k=lo
    · simpa [h] using hbad
    · exact hr.2.2 k (by omega) hk'

lemma mem_starts {G : ℕ → Finset α} {bad : ℕ → α → Prop} {g : α} {k : ℕ} :
    g ∈ starts G bad k ↔ g ∈ G k ∧ (k=0 ∨ g ∉ G (k-1) ∨ bad (k-1) g) :=
  Finset.mem_filter

lemma starts_zero (G : ℕ → Finset α) (bad : ℕ → α → Prop) : starts G bad 0=G 0 := by
  ext g
  simp only [mem_starts,true_or,and_true]

lemma starts_succ (G : ℕ → Finset α) (bad : ℕ → α → Prop) (k : ℕ) :
    starts G bad (k+1) = (G (k+1)).filter (fun g => g ∉ G k ∨ bad k g) := by
  ext g
  simp only [mem_starts,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,false_or,
    Nat.add_sub_cancel,Finset.mem_filter]

lemma mem_runs {G : ℕ → Finset α} {bad : ℕ → α → Prop} {n : ℕ}
    {r : α × ℕ × ℕ} (h : r ∈ runs G bad n) :
    r.2.1 ≤ r.2.2 ∧ r.2.2 ≤ n ∧ Reach G bad r.1 r.2.1 r.2.2 := by
  obtain ⟨lo,hlo,hg⟩ := Finset.mem_biUnion.mp h
  obtain ⟨g,hstart,rfl⟩ := Finset.mem_image.mp hg
  have hn : lo ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hlo)
  have hr : Reach G bad g lo (last G bad n g lo) :=
    Nat.findGreatest_spec hn (reach_self (mem_starts.mp hstart).1)
  exact ⟨hr.1,Nat.findGreatest_le _,hr⟩

lemma runs_cover {G : ℕ → Finset α} {bad : ℕ → α → Prop} {n k : ℕ}
    {g : α} (hk : k ≤ n) (hg : g ∈ G k) :
    ∃ r ∈ runs G bad n, r.1=g ∧ r.2.1 ≤ k ∧ k ≤ r.2.2 := by
  let H : ∃ lo, Reach G bad g lo k := ⟨k,reach_self hg⟩
  let lo := Nat.find H
  have hlo : Reach G bad g lo k := Nat.find_spec H
  have hs : g ∈ starts G bad lo := by
    refine mem_starts.mpr ⟨hlo.2.1 lo le_rfl hlo.1,?_⟩
    by_cases hzero : lo=0
    · exact Or.inl hzero
    · right
      by_contra h
      push Not at h
      have he : lo-1+1=lo := by omega
      have hlo' : Reach G bad g (lo-1+1) k := by rw [he]; exact hlo
      have hr := reach_extend_left hlo' h.1 h.2
      exact Nat.find_min H (show lo-1 < lo by omega) hr
  refine ⟨(g,lo,last G bad n g lo),?_,rfl,hlo.1,?_⟩
  · exact Finset.mem_biUnion.mpr ⟨lo,Finset.mem_range.mpr (Nat.lt_succ_of_le (hlo.1.trans hk)),
      Finset.mem_image.mpr ⟨g,hs,rfl⟩⟩
  · exact Nat.le_findGreatest hk hlo

lemma runs_card (G : ℕ → Finset α) (bad : ℕ → α → Prop) (n : ℕ) :
    (runs G bad n).card ≤ (G 0).card +
      ∑ k ∈ range n, ((G (k+1)).filter (fun g => g ∉ G k ∨ bad k g)).card := by
  apply Finset.card_biUnion_le.trans
  apply (Finset.sum_le_sum (fun lo _ => Finset.card_image_le)).trans
  rw [Finset.sum_range_succ']
  simp only [starts_zero,starts_succ,Nat.add_comm,le_refl]

end PlanarUnitDistances.SweepRuns

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma continuous_graphPoint (c : Plane) (b : Bool) : Continuous (graphPoint c b) := by
  unfold graphPoint
  have := continuous_branch c b
  fun_prop

lemma unit_graph_closed {c p : Plane} (hp : dist p c=1) :
    ∃ b : Bool, p=graphPoint c b (p 0) := by
  have h := unit_projection_closed hp
  have hd := plane_dist_sq p c
  have hs := Real.sq_sqrt (closed_radicand h)
  rw [hp] at hd
  have he : (p 1-c 1)^2=(Real.sqrt (1-(p 0-c 0)^2))^2 := by nlinarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · refine ⟨true,?_⟩
    ext i
    fin_cases i
    · rfl
    · change p 1=c 1+Real.sqrt (1-(p 0-c 0)^2)
      linarith
  · refine ⟨false,?_⟩
    ext i
    fin_cases i
    · rfl
    · change p 1=c 1+-Real.sqrt (1-(p 0-c 0)^2)
      linarith

lemma circle_open_avoids_abscissas {U : Set Plane} (hU : IsOpen U) {c p : Plane}
    (hp : p ∈ U) (hc : dist p c=1) (E : Finset ℝ) :
    ∃ q ∈ U, dist q c=1 ∧ q 0 ∉ E := by
  obtain ⟨b,hb⟩ := unit_graph_closed hc
  let V := graphPoint c b ⁻¹' U
  have hVo : IsOpen V := (continuous_graphPoint c b).isOpen_preimage U hU
  have hVp : p 0 ∈ V := by change graphPoint c b (p 0) ∈ U; rw [← hb]; exact hp
  have hmem : p 0 ∈ closure (Set.Ioo (c 0-1) (c 0+1)) := by
    rw [closure_Ioo (by linarith : c 0-1 ≠ c 0+1)]
    exact unit_projection_closed hc
  have hn : (V ∩ Set.Ioo (c 0-1) (c 0+1)).Nonempty :=
    mem_closure_iff.mp hmem V hVo hVp
  have ho : IsOpen (V ∩ Set.Ioo (c 0-1) (c 0+1)) := hVo.inter isOpen_Ioo
  obtain ⟨x,hx,hxE⟩ := ((E.finite_toSet.countable).dense_compl ℝ).inter_open_nonempty _ ho hn
  exact ⟨graphPoint c b x,hx.1,graphPoint_unit b ⟨hx.2.1.le,hx.2.2.le⟩,hxE⟩

lemma region_open {n : ℕ} (a : Fin n → ℝ) (g : Gap) (lo hi : ℕ) :
    IsOpen (region a g lo hi) := by
  have h0 : Continuous (fun p : Plane => p 0) := by fun_prop
  have h1 : Continuous (fun p : Plane => p 1) := by fun_prop
  have hs := (SweepIntervals.span_open a lo hi).preimage h0
  have hb (b : Label) : Continuous (fun p : Plane => height b (p 0)) :=
    (continuous_branch _ _).comp h0
  rcases g with ⟨l,u⟩
  cases l with
  | none =>
    cases u with
    | none => convert hs using 1; ext p; simp [region,Sweep.GapBand,Sweep.Lower]
    | some u => convert hs.inter (isOpen_lt h1 (hb u)) using 1; ext p; simp [region,Sweep.GapBand,Sweep.Lower]
  | some l =>
    cases u with
    | none => convert hs.inter (isOpen_lt (hb l) h1) using 1; ext p; simp [region,Sweep.GapBand,Sweep.Lower]
    | some u =>
      convert hs.inter ((isOpen_lt (hb l) h1).inter (isOpen_lt h1 (hb u))) using 1
      ext p
      simp [region,Sweep.GapBand,Sweep.Lower]

lemma slab_list_transport {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z) {k : ℕ}
    {x y : ℝ} (hx : x ∈ SweepIntervals.slab a k) (hy : y ∈ SweepIntervals.slab a k)
    {L : List Label} (hm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q x)
    (ho : L.Pairwise (fun b d => height b x<height d x)) :
    (∀ b, b ∈ L ↔ b ∈ activeLabels Q y) ∧
      L.Pairwise (fun b d => height b y<height d y) := by
  have hE : ∀ z ∈ SweepIntervals.slab a k, z ∉ eventAbscissas Q := by
    intro z hz he
    obtain ⟨i,hi⟩ := (ha z).mp he
    exact SweepIntervals.slab_no_event hz i hi.symm
  have hS := SweepIntervals.span_ordConnected a k k
  have hm' : ∀ b, b ∈ L ↔ b ∈ activeLabels Q y := by
    intro b
    rw [hm,mem_activeLabels,mem_activeLabels]
    constructor
    · rintro ⟨hb,hbx⟩
      exact ⟨hb,(active_constant hS hE hb hx hy).mp hbx⟩
    · rintro ⟨hb,hby⟩
      exact ⟨hb,(active_constant hS hE hb hx hy).mpr hby⟩
  refine ⟨hm',ho.imp_of_mem ?_⟩
  intro b d hb hd hbd
  have hbx := mem_activeLabels.mp ((hm b).mp hb)
  have hdx := mem_activeLabels.mp ((hm d).mp hd)
  apply order_constant hS (continuous_branch _ _).continuousOn (continuous_branch _ _).continuousOn
    (fun z hz he => ?_) hx hy hbd
  exact hE z hz (branch_collision_event hbx.1 hdx.1
    ((active_constant hS hE hbx.1 hx hz).mp hbx.2)
    ((active_constant hS hE hdx.1 hx hz).mp hdx.2)
    (fun heq => by change b=d at heq; rw [heq] at hbd; exact lt_irrefl _ hbd) he)

lemma slab_gap_avoids {Q : Finset Plane} {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z) {k : ℕ} {p : Plane}
    (hp : p 0 ∈ SweepIntervals.slab a k) {L : List Label}
    (hm : ∀ b, b ∈ L ↔ b ∈ activeLabels Q (p 0))
    (ho : L.Pairwise (fun b d => height b (p 0)<height d (p 0)))
    {g : Gap} (hg : g ∈ Sweep.gaps L)
    (hpg : Sweep.GapBand (fun b => height b (p 0)) g (p 1)) :
    ∀ c ∈ Q, dist p c≠1 := by
  intro c hc hpc
  have hn : p 0 ∉ eventAbscissas Q := by
    intro he
    obtain ⟨i,hi⟩ := (ha _).mp he
    exact SweepIntervals.slab_no_event hp i hi.symm
  have hx := active_of_unit_nonextreme hpc
    (fun h => hn (h ▸ (extrema_mem_events hc).1))
    (fun h => hn (h ▸ (extrema_mem_events hc).2))
  obtain ⟨b,hb⟩ := (unit_iff_graph hx).mp hpc
  exact Sweep.gaps_avoid _ L ho hg hpg (c,b) ((hm _).mpr (mem_activeLabels.mpr ⟨hc,hx⟩)) hb

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma arrangement_exists (Q : Finset Plane) : Nonempty (Arrangement Q) := by
  let E := eventAbscissas Q
  let a := E.orderEmbOfFin rfl
  have ha : StrictMono a := a.strictMono
  have he : ∀ z, z ∈ eventAbscissas Q ↔ ∃ i, a i=z := by
    intro z
    change z ∈ (E : Set ℝ) ↔ ∃ i, a i=z
    rw [← Finset.range_orderEmbOfFin E rfl]
    rfl
  have hL : ∀ k, ∃ L : List Label, L.Nodup ∧
      (∀ x ∈ SweepIntervals.slab a k, ∀ b, b ∈ L ↔ b ∈ activeLabels Q x) ∧
      (∀ x ∈ SweepIntervals.slab a k, L.Pairwise (fun b d => height b x<height d x)) := by
    intro k
    obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty ha k
    have hxE : x ∉ eventAbscissas Q := by
      intro hxE
      obtain ⟨i,hi⟩ := (he x).mp hxE
      exact SweepIntervals.slab_no_event hx i hi.symm
    obtain ⟨L,hLn,hLm,hLo⟩ := exists_ordered_branches hxE
    exact ⟨L,hLn,fun y hy => (slab_list_transport he hx hy hLm hLo).1,
      fun y hy => (slab_list_transport he hx hy hLm hLo).2⟩
  choose L hLn hLm hLo using hL
  exact ⟨⟨E.card,a,ha,he,L,hLn,hLm,hLo⟩⟩

namespace Arrangement
variable {Q : Finset Plane} (d : Arrangement Q)

lemma list_card_le (k : ℕ) : (d.L k).length ≤ 2*Q.card := by
  obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty d.strict k
  rw [← List.toFinset_card_of_nodup (d.nodup k)]
  have hsub : (d.L k).toFinset ⊆ labels Q := by
    intro b hb
    exact (Finset.mem_filter.mp ((d.mem k x hx b).mp (List.mem_toFinset.mp hb))).1
  exact (Finset.card_le_card hsub).trans_eq (by simp [labels,Finset.card_product,mul_comm])

lemma G_card_le (k : ℕ) : (d.G k).card ≤ 2*Q.card+1 :=
  (Sweep.links_card_le none (d.L k)).trans (Nat.add_le_add_right (d.list_card_le k) 1)

lemma skeleton (k : Fin d.n) :
    (d.L k.val).filter (· ∉ d.criticalAt k.val) =
      (d.L (k.val+1)).filter (· ∉ d.criticalAt k.val) := by
  unfold criticalAt
  rw [dite_eq_left k.is_lt]
  obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty d.strict k.val
  obtain ⟨y,hy⟩ := SweepIntervals.slab_nonempty d.strict (k.val+1)
  exact event_skeleton d.events k hx hy (d.nodup _) (d.nodup _)
    (d.mem _ x hx) (d.mem _ y hy) (d.order _ x hx) (d.order _ y hy)

lemma critical_sum : ∑ k ∈ range d.n, (d.criticalAt k).card ≤ 4*Q.card+4*Q.card^2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => (d.criticalAt k).card)]
  simp only [criticalAt,dite_eq_left (Fin.is_lt _)]
  have he : ∑ k : Fin d.n, (critical Q (d.a k)).card =
      ∑ x ∈ eventAbscissas Q, (critical Q x).card := by
    apply Finset.sum_bij (fun k _ => d.a k)
    · intro k _
      exact (d.events _).mpr ⟨k,rfl⟩
    · intro k _ j _ h
      exact d.strict.injective h
    · intro x hx
      obtain ⟨k,hk⟩ := (d.events _).mp hx
      exact ⟨k,Finset.mem_univ _,hk⟩
    · intro _ _; rfl
  rw [he]
  exact critical_card_sum Q _

lemma pieces_card : d.pieces.card ≤ 43*(1+Q.card^2) := by
  have hs : ∑ k ∈ range d.n,
      ((d.G (k+1)).filter (fun g => g ∉ d.G k ∨ Sweep.touches (d.criticalAt k) g)).card ≤
      5 * ∑ k ∈ range d.n, (d.criticalAt k).card := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have h := Sweep.event_starts_card (d.criticalAt k) (d.L k) (d.L (k+1))
      (d.nodup k) (d.nodup (k+1)) (d.skeleton ⟨k,Finset.mem_range.mp hk⟩)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg Finset.card
    ext g
    simp only [G,Finset.mem_filter]
    exact Finset.mem_filter
  have hR := SweepRuns.runs_card d.G (fun k g => Sweep.touches (d.criticalAt k) g) d.n
  have h0 := d.G_card_le 0
  have hcrit := d.critical_sum
  have hq : Q.card ≤ Q.card^2 := by
    by_cases h : Q.card=0
    · simp [h]
    · have h1 : 1≤Q.card := Nat.one_le_iff_ne_zero.mpr h
      simpa [pow_two] using Nat.mul_le_mul_left Q.card h1
  change (d.pieces).card ≤ _ at hR
  nlinarith

lemma piece_avoids {r : Gap × ℕ × ℕ} (hr : r ∈ d.pieces) :
    ∀ p ∈ region d.a r.1 r.2.1 r.2.2, ∀ c ∈ Q, dist p c≠1 := by
  intro p hp c hc hpc
  obtain ⟨q,hq,hqc,hqE⟩ := circle_open_avoids_abscissas
    (region_open _ _ _ _) hp hpc (eventAbscissas Q)
  have hr' := SweepRuns.mem_runs hr
  have hq' : q 0 ∈ SweepIntervals.span d.a r.2.1 r.2.2 := hq.1
  rcases SweepIntervals.span_decomposition d.strict hr'.1 hr'.2.1 hq' with hj | hk
  · obtain ⟨j,_,_,hj⟩ := hj
    exact hqE ((d.events _).mpr ⟨j,hj.symm⟩)
  · obtain ⟨k,hk1,hk2,hqk⟩ := hk
    exact slab_gap_avoids d.events hqk (d.mem k (q 0) hqk) (d.order k (q 0) hqk)
      (hr'.2.2.2.1 k hk1 hk2) hq.2 c hc hqc

lemma pieces_cover {p : Plane} (hp : p 0 ∉ eventAbscissas Q)
    (hpc : ∀ c ∈ Q, dist p c≠1) :
    ∃ r ∈ d.pieces, p ∈ region d.a r.1 r.2.1 r.2.2 := by
  have hn : ∀ i, p 0 ≠ d.a i := by
    intro i hi
    exact hp ((d.events _).mpr ⟨i,hi.symm⟩)
  obtain ⟨k,hkn,hpk⟩ := SweepIntervals.cover_slabs d.strict hn
  have hh : ∀ b ∈ d.L k, p 1≠height b (p 0) := by
    intro b hb he
    have hb' := mem_activeLabels.mp ((d.mem k (p 0) hpk b).mp hb)
    have hdist := (unit_iff_graph hb'.2).mpr ⟨b.2,he⟩
    exact hpc b.1 hb'.1 hdist
  obtain ⟨g,hg,hpg⟩ := Sweep.gaps_cover (fun b => height b (p 0)) (d.L k) (p 1) hh
  obtain ⟨r,hr,hrg,hrk,hrk'⟩ := SweepRuns.runs_cover (G := d.G)
    (bad := fun k g => Sweep.touches (d.criticalAt k) g) hkn hg
  refine ⟨r,hr,SweepIntervals.slab_subset_span hrk hrk' hpk,?_⟩
  rw [hrg]
  exact hpg

end Arrangement
end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma circleIntersections_mono {Q T : Finset Plane} (h : Q ⊆ T) :
    circleIntersections Q ⊆ circleIntersections T := by
  intro p hp
  obtain ⟨⟨c,d⟩,hcd,hp⟩ := Finset.mem_biUnion.mp hp
  have hc := Finset.mem_product.mp hcd
  split at hp
  · simp_all
  · simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hp
    exact mem_circleIntersections (h hc.1) (h hc.2) (by assumption) hp.1 hp.2

lemma eventAbscissas_mono {Q T : Finset Plane} (h : Q ⊆ T) :
    eventAbscissas Q ⊆ eventAbscissas T := by
  apply Finset.union_subset_union
  · intro x hx
    obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨c,h hc,hx⟩
  · exact Finset.image_subset_image (circleIntersections_mono h)

lemma eventAbscissas_card (Q : Finset Plane) :
    (eventAbscissas Q).card ≤ 2*Q.card+2*Q.card^2 := by
  apply (Finset.card_union_le _ _).trans
  apply Nat.add_le_add
  · apply Finset.card_biUnion_le.trans
    apply (Finset.sum_le_sum (fun c _ => Finset.card_le_two (a := c 0-1) (b := c 0+1))).trans
    simp [mul_comm]
  · exact Finset.card_image_le.trans (circleIntersections_card Q)

lemma candidateCodes_card (Q : Finset Plane) :
    (candidateCodes Q).card ≤ 81*(1+Q.card)^6 := by
  have he : (endpoints Q).card ≤ 3*(1+Q.card)^2 := by
    have h := (Finset.card_insert_le none ((eventAbscissas Q).image some)).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
    have hE := eventAbscissas_card Q
    change (endpoints Q).card ≤ _ at h
    nlinarith
  have hb : (boundaries Q).card ≤ 3*(1+Q.card) := by
    have h := (Finset.card_insert_le none ((labels Q).image some)).trans
      (Nat.add_le_add_right Finset.card_image_le 1)
    have hL : (labels Q).card=2*Q.card := by simp [labels,mul_comm]
    change (boundaries Q).card ≤ _ at h
    omega
  simp only [candidateCodes,Finset.card_product]
  calc
    _ ≤ (3*(1+Q.card)^2)*(3*(1+Q.card)^2)*((3*(1+Q.card))*(3*(1+Q.card))) :=
      Nat.mul_le_mul (Nat.mul_le_mul he he) (Nat.mul_le_mul hb hb)
    _ = _ := by ring

lemma span_description {n : ℕ} {a : Fin n → ℝ} (ha : StrictMono a)
    {Q : Finset Plane} (he : ∀ i, a i ∈ eventAbscissas Q)
    {lo hi : ℕ} (hl : lo ≤ n) (hh : hi ≤ n) :
    ∃ e₁ ∈ endpoints Q, ∃ e₂ ∈ endpoints Q,
      SweepIntervals.span a lo hi = {x | Sweep.GapBand id (e₁,e₂) x} := by
  have hleft : ∃ e ∈ endpoints Q,
      ∀ x, (∀ i, i.val<lo → a i<x) ↔ Sweep.Lower id e x := by
    by_cases hz : lo=0
    · refine ⟨none,Finset.mem_insert_self _ _,?_⟩
      intro x
      simp [hz,Sweep.Lower]
    · let i : Fin n := ⟨lo-1,by omega⟩
      refine ⟨some (a i),Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a i,he i,rfl⟩),?_⟩
      intro x
      simp only [Sweep.Lower,Option.some.injEq,forall_eq',id_eq]
      constructor
      · exact fun h => h i (by dsimp [i]; omega)
      · intro h j hj
        apply (ha.monotone (show j ≤ i by change j.val ≤ lo-1; omega)).trans_lt h
  have hright : ∃ e ∈ endpoints Q,
      ∀ x, (∀ i, hi ≤ i.val → x<a i) ↔ (∀ z, e=some z → x<z) := by
    by_cases hh' : hi<n
    · let i : Fin n := ⟨hi,hh'⟩
      refine ⟨some (a i),Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a i,he i,rfl⟩),?_⟩
      intro x
      simp only [Option.some.injEq,forall_eq']
      constructor
      · exact fun h => h i le_rfl
      · intro h j hj
        exact h.trans_le (ha.monotone hj)
    · refine ⟨none,Finset.mem_insert_self _ _,?_⟩
      intro x
      constructor
      · intro _ z hz
        cases hz
      · intro _ i hi
        have hn := i.is_lt
        omega
  obtain ⟨e₁,he₁,h₁⟩ := hleft
  obtain ⟨e₂,he₂,h₂⟩ := hright
  refine ⟨e₁,he₁,e₂,he₂,?_⟩
  ext x
  exact and_congr (h₁ x) (h₂ x)

namespace Arrangement
variable {T Q : Finset Plane} (d : Arrangement T)

lemma piece_description (hT : T ⊆ Q) {r : Gap × ℕ × ℕ} (hr : r ∈ d.pieces) :
    ∃ c ∈ candidateCodes Q, region d.a r.1 r.2.1 r.2.2 = codeRegion c := by
  have hr' := SweepRuns.mem_runs hr
  obtain ⟨e₁,he₁,e₂,he₂,he⟩ := span_description d.strict
    (fun i => eventAbscissas_mono hT ((d.events _).mpr ⟨i,rfl⟩))
    (hr'.1.trans hr'.2.1) hr'.2.1
  have hb : ∀ b, b ∈ r.1.1 ∨ b ∈ r.1.2 → b ∈ labels Q := by
    intro b hb
    have hg := hr'.2.2.2.1 r.2.1 le_rfl hr'.1
    have hbL := Sweep.gaps_endpoints (d.L r.2.1) hg (hb.imp Option.mem_def.mp Option.mem_def.mp)
    obtain ⟨x,hx⟩ := SweepIntervals.slab_nonempty d.strict r.2.1
    exact mem_labels.mpr (hT (mem_activeLabels.mp ((d.mem _ x hx b).mp hbL)).1)
  have hb' (t : Option Label) (ht : t=r.1.1 ∨ t=r.1.2) : t ∈ boundaries Q := by
    cases t with
    | none => exact Finset.mem_insert_self _ _
    | some b =>
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨b,hb b ?_,rfl⟩
      rcases ht with ht | ht
      · exact Or.inl (ht.symm ▸ Option.mem_def.mpr rfl)
      · exact Or.inr (ht.symm ▸ Option.mem_def.mpr rfl)
  refine ⟨((e₁,e₂),r.1),Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨he₁,he₂⟩,
    Finset.mem_product.mpr ⟨hb' _ (Or.inl rfl),hb' _ (Or.inr rfl)⟩⟩,?_⟩
  ext p
  change (p 0 ∈ SweepIntervals.span d.a r.2.1 r.2.2 ∧ _) ↔ _
  rw [he]
  rfl

end Arrangement
end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleCutting
open Finset Classical Set

lemma rotate_surjective (e : Plane) (he : (e 0)^2+(e 1)^2=1) :
    Function.Surjective (rotate e) := by
  intro p
  refine ⟨WithLp.toLp 2 ![e 0*p 0-e 1*p 1,e 1*p 0+e 0*p 1],?_⟩
  ext i
  fin_cases i
  · change e 0*(e 0*p 0-e 1*p 1)+e 1*(e 1*p 0+e 0*p 1)=p 0
    nlinarith [congrArg (fun z : ℝ => z*p 0) he]
  · change -e 1*(e 0*p 0-e 1*p 1)+e 0*(e 1*p 0+e 0*p 1)=p 1
    nlinarith [congrArg (fun z : ℝ => z*p 1) he]

lemma mem_circleIntersections_iff {Q : Finset Plane} {p : Plane} :
    p ∈ circleIntersections Q ↔ ∃ c ∈ Q, ∃ d ∈ Q, c≠d ∧ dist p c=1 ∧ dist p d=1 := by
  constructor
  · intro hp
    obtain ⟨⟨c,d⟩,hcd,hp⟩ := Finset.mem_biUnion.mp hp
    have hc := Finset.mem_product.mp hcd
    split at hp
    · simp_all
    · simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq] at hp
      exact ⟨c,hc.1,d,hc.2,by assumption,hp⟩
  · rintro ⟨c,hc,d,hd,hcd,hp,hp'⟩
    exact mem_circleIntersections hc hd hcd hp hp'

lemma good_rotated_position (P Q : Finset Plane) :
    ∃ e : Plane, (e 0)^2+(e 1)^2=1 ∧
      ∀ T ⊆ Q.image (rotate e), ∀ p ∈ P.image (rotate e),
        (∀ c ∈ T, dist p c≠1) → p 0 ∉ eventAbscissas T := by
  obtain ⟨e,he,hsep,hex⟩ := exists_good_direction (P ∪ circleIntersections Q) P Q
  refine ⟨e,he,?_⟩
  intro T hT p hp havoid hbad
  obtain ⟨p,hpP,rfl⟩ := Finset.mem_image.mp hp
  rcases Finset.mem_union.mp hbad with hextr | hint
  · obtain ⟨c,hc,hx⟩ := Finset.mem_biUnion.mp hextr
    obtain ⟨c,hcQ,rfl⟩ := Finset.mem_image.mp (hT hc)
    have hne := hex p hpP c hcQ
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with hx | hx
    · apply hne.2
      change projection e p=projection e c-1 at hx
      unfold projection at *
      simp only [WithLp.ofLp_sub,Pi.sub_apply]
      linarith
    · apply hne.1
      change projection e p=projection e c+1 at hx
      unfold projection at *
      simp only [WithLp.ofLp_sub,Pi.sub_apply]
      linarith
  · obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hint
    obtain ⟨c,hc,d,hd,hcd,hyc,hyd⟩ := mem_circleIntersections_iff.mp hy
    obtain ⟨c,hcQ,rfl⟩ := Finset.mem_image.mp (hT hc)
    obtain ⟨d,hdQ,rfl⟩ := Finset.mem_image.mp (hT hd)
    obtain ⟨y,rfl⟩ := rotate_surjective e he y
    rw [rotate_dist e he] at hyc hyd
    have hyQ : y ∈ circleIntersections Q := mem_circleIntersections hcQ hdQ
      (fun h => hcd (congrArg (rotate e) h)) hyc hyd
    have hyp : y=p := by
      by_contra hne
      exact hsep y (Finset.mem_union_right _ hyQ) p (Finset.mem_union_left _ hpP) hne hyx
    subst y
    exact havoid (rotate e c) hc (by rw [rotate_dist e he]; exact hyc)

end PlanarUnitDistances.CircleCutting

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteSampling
open Finset Classical

lemma avoiding_count {A : Type*} [Fintype A] (C : Finset A) (s : ℕ) :
    ((univ : Finset (Fin s → A)).filter (fun f => ∀ i, f i ∉ C)).card =
      (Fintype.card A-C.card)^s := by
  rw [← Fintype.card_subtype]
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := fun (_ : Fin s) a => a ∉ C))]
  rw [Fintype.card_fun,Fintype.card_subtype_compl]
  simp only [Fintype.card_fin,Fintype.card_coe]

lemma sampleSize_error {R : ℝ} (hR : 0<R) (N : ℕ) :
    (N : ℝ)*Real.exp (-(sampleSize R N : ℝ)/R)<1/10 := by
  have hN : (0 : ℝ)<10*((N : ℝ)+1) := by positivity
  have hs : R*Real.log (10*((N : ℝ)+1)) ≤ (sampleSize R N : ℝ) := Nat.le_ceil _
  have hd : Real.log (10*((N : ℝ)+1)) ≤ (sampleSize R N : ℝ)/R := by
    apply (le_div_iff₀ hR).mpr
    simpa only [mul_comm] using hs
  have he : Real.exp (-(sampleSize R N : ℝ)/R) ≤ (10*((N : ℝ)+1))⁻¹ := by
    calc
      _ ≤ Real.exp (-Real.log (10*((N : ℝ)+1))) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div]
        exact neg_le_neg hd
      _ = _ := by rw [Real.exp_neg,Real.exp_log hN]
  apply (mul_le_mul_of_nonneg_left he (Nat.cast_nonneg N)).trans_lt
  rw [← div_eq_mul_inv]
  apply (div_lt_iff₀ hN).mpr
  linarith

lemma sampleSize_le {R : ℝ} (hR : 0<R) {N M : ℕ} (hNM : N≤M) :
    (sampleSize R N : ℝ) ≤ R*Real.log (10*((M : ℝ)+1))+1 := by
  apply le_of_lt
  have hN : (1 : ℝ) ≤ 10*((N : ℝ)+1) := by have hh : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  apply (Nat.ceil_lt_add_one (mul_nonneg hR.le (Real.log_nonneg hN))).trans_le
  apply add_le_add_left
  apply mul_le_mul_of_nonneg_left _ hR.le
  exact Real.log_le_log (by positivity) (by exact_mod_cast (Nat.mul_le_mul_left 10 (Nat.add_le_add_right hNM 1)))

lemma sum_sample_coordinate {A J : Type*} [Fintype A] [Fintype J] [DecidableEq J]
    (hA : 0<Fintype.card A) (w : A → ℝ) (j : J) :
    ∑ f : J → A, w (f j) = (Fintype.card (J → A) : ℝ)*((∑ a, w a)/Fintype.card A) := by
  let e := Equiv.piSplitAt j (fun _ : J => A)
  have he : ∑ f : J → A, w (f j) = ∑ z : A × ({i : J // i≠j} → A), w z.1 :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [he,Fintype.sum_prod_type]
  simp only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum]
  have hc := Fintype.card_congr e
  rw [Fintype.card_prod] at hc
  have hc' : (Fintype.card (J → A) : ℝ) =
      (Fintype.card A : ℝ)*(Fintype.card ({i : J // i≠j} → A) : ℝ) := by exact_mod_cast hc
  rw [hc']
  have ha : (Fintype.card A : ℝ)≠0 := ne_of_gt (Nat.cast_pos.mpr hA)
  field_simp
  simp [mul_comm]

lemma sum_sample_cost {A : Type*} [Fintype A] (hA : 0<Fintype.card A)
    (w : A → ℝ) (s : ℕ) :
    ∑ f : Fin s → A, ∑ j, w (f j) =
      (Fintype.card A : ℝ)^s*((s : ℝ)*((∑ a, w a)/Fintype.card A)) := by
  calc
    _ = ∑ j : Fin s, ∑ f : Fin s → A, w (f j) := by exact Finset.sum_comm
    _ = ∑ _j : Fin s, (Fintype.card (Fin s → A) : ℝ)*((∑ a, w a)/Fintype.card A) := by
      apply Finset.sum_congr rfl
      intro j _
      exact sum_sample_coordinate hA w j
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Fintype.card_fun,Nat.cast_pow]
      ring

lemma exists_low_cost_in_large_set {B : Type*} [Fintype B]
    (hB : 0<Fintype.card B) (S : Finset B) (w : B → ℝ) (a : ℝ)
    (hw : ∀ b, 0≤w b) (hs : (Fintype.card B : ℝ)/2 < S.card)
    (hmean : ∑ b, w b ≤ (Fintype.card B : ℝ)*a) :
    ∃ b ∈ S, w b≤2*a := by
  have hn : S.Nonempty := Finset.card_pos.mp (by
    have hh : (0 : ℝ)<S.card := (half_pos (Nat.cast_pos.mpr hB)).trans hs
    exact_mod_cast hh)
  have ha : 0≤a := by
    have hh := (Finset.sum_nonneg (fun b _ => hw b)).trans hmean
    exact nonneg_of_mul_nonneg_right hh (Nat.cast_pos.mpr hB)
  by_contra! hbad
  have hlt : (S.card : ℝ)*(2*a) < ∑ b ∈ S, w b := by
    simpa only [Finset.sum_const,nsmul_eq_mul] using
      (Finset.sum_lt_sum_of_nonempty hn (fun b hb => hbad b hb))
  have hsum : ∑ b ∈ S, w b ≤ ∑ b, w b :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun b _ _ => hw b)
  have hc : (Fintype.card B : ℝ)*a ≤ (S.card : ℝ)*(2*a) := by nlinarith
  exact (not_lt_of_ge (hmean.trans hc)) (hlt.trans_le hsum)

lemma avoiding_count_le {A : Type*} [Fintype A] (hA : 0<Fintype.card A)
    (C : Finset A) (s : ℕ) {q : ℝ} (hC : q ≤ (C.card : ℝ)/Fintype.card A) :
    ((((univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C)).card) : ℝ) ≤
      (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)*q) := by
  rw [avoiding_count,Nat.cast_pow]
  have hl : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
  have hcard : C.card ≤ Fintype.card A := Finset.card_le_univ _
  have he : ((Fintype.card A-C.card : ℕ) : ℝ)/(Fintype.card A : ℝ) ≤ Real.exp (-q) := by
    rw [Nat.cast_sub hcard,sub_div,div_self hl.ne']
    exact (sub_le_sub_left hC 1).trans (Real.one_sub_le_exp_neg q)
  have he' := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hl.le) he s
  rw [div_pow,← Real.exp_nat_mul] at he'
  have hid : (s : ℝ)*(-q)= -(s : ℝ)*q := by ring
  rw [hid] at he'
  exact (div_le_iff₀ (pow_pos hl s)).mp he' |>.trans_eq (mul_comm _ _)

lemma exists_hit_large_conflicts_with_cost {A I : Type*} [Fintype A]
    (hA : 0<Fintype.card A) (K : Finset I) (C : I → Finset A)
    (w : A → ℝ) (hw : ∀ a, 0≤w a) {R : ℝ} (hR : 0<R) :
    ∃ f : Fin (sampleSize R K.card) → A,
      (∀ i ∈ K, (Fintype.card A : ℝ)/R < (C i).card → ∃ j, f j ∈ C i) ∧
      ∑ j, w (f j) ≤ 2*(sampleSize R K.card : ℝ)*((∑ a, w a)/Fintype.card A) := by
  let s := sampleSize R K.card
  let B := K.filter (fun i => (Fintype.card A : ℝ)/R < (C i).card)
  let bad : Finset (Fin s → A) := B.biUnion
    (fun i => univ.filter (fun f => ∀ j, f j ∉ C i))
  have hl : (0 : ℝ)<Fintype.card A := Nat.cast_pos.mpr hA
  have hprob : (bad.card : ℝ) < (Fintype.card A : ℝ)^s/10 := by
    have hc (i : I) (hi : i ∈ B) :
        ((((univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C i)).card) : ℝ) ≤
          (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)/R) := by
      have hq : 1/R ≤ ((C i).card : ℝ)/Fintype.card A := by
        apply le_of_lt
        apply (div_lt_div_iff₀ hR hl).mpr
        simpa only [one_mul] using (div_lt_iff₀ hR).mp (Finset.mem_filter.mp hi).2
      simpa only [mul_one_div] using avoiding_count_le hA (C i) s hq
    calc
      _ ≤ ∑ i ∈ B, ((((univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C i)).card) : ℝ) := by
        exact_mod_cast (Finset.card_biUnion_le (s := B) (t := fun i => (univ : Finset (Fin s → A)).filter (fun f => ∀ j, f j ∉ C i)))
      _ ≤ ∑ _i ∈ B, (Fintype.card A : ℝ)^s*Real.exp (-(s : ℝ)/R) := Finset.sum_le_sum hc
      _ = (Fintype.card A : ℝ)^s*((B.card : ℝ)*Real.exp (-(s : ℝ)/R)) := by
        simp only [Finset.sum_const,nsmul_eq_mul]; ring
      _ ≤ (Fintype.card A : ℝ)^s*((K.card : ℝ)*Real.exp (-(s : ℝ)/R)) := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hl.le s)
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact_mod_cast Finset.card_filter_le K _
      _ < _ := by
        have hh := mul_lt_mul_of_pos_left (sampleSize_error hR K.card) (pow_pos hl s)
        simpa only [mul_one_div] using hh
  have htotal : Fintype.card (Fin s → A)=(Fintype.card A)^s := by simp
  have hS : (Fintype.card (Fin s → A) : ℝ)/2 < ((univ \ bad).card : ℝ) := by
    have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ bad)
    have hc' : ((univ \ bad).card : ℝ)+(bad.card : ℝ)=(Fintype.card A : ℝ)^s := by
      have hh : (univ \ bad).card+bad.card=(Fintype.card A)^s := by simpa using hc
      exact_mod_cast hh
    rw [htotal,Nat.cast_pow]
    linarith [pow_pos hl s]
  obtain ⟨f,hf,hcost⟩ := exists_low_cost_in_large_set
    (by rw [htotal]; exact pow_pos hA s) (univ \ bad) (fun f => ∑ j, w (f j))
    ((s : ℝ)*((∑ a, w a)/Fintype.card A))
    (fun f => Finset.sum_nonneg (fun j _ => hw (f j))) hS
    (by rw [sum_sample_cost hA w,htotal,Nat.cast_pow])
  refine ⟨f,?_,by simpa only [mul_assoc] using hcost⟩
  intro i hi hci
  by_contra! hn
  exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_biUnion.mpr
    ⟨i,Finset.mem_filter.mpr ⟨hi,hci⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩)

end PlanarUnitDistances.FiniteSampling

namespace PlanarUnitDistances.CircleCutting
open Finset Classical

lemma conflicts_subtype_card (Q : Finset Plane) (U : Set Plane) :
    ((univ : Finset Q).filter (fun (c : Q) => ∃ p ∈ U, dist p (c : Plane)=1)).card=(conflicts Q U).card := by
  apply Finset.card_bij (fun (c : Q) _ => (c : Plane))
  · intro c hc
    exact Finset.mem_filter.mpr ⟨c.property,(Finset.mem_filter.mp hc).2⟩
  · intro c _ d _ h
    exact Subtype.ext h
  · intro c hc
    exact ⟨⟨c,(Finset.mem_filter.mp hc).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc).2⟩,rfl⟩

theorem cutting_good_position (P Q : Finset Plane) (hQ : Q.Nonempty)
    (hpos : ∀ T ⊆ Q, ∀ p ∈ P, (∀ c ∈ T, dist p c≠1) → p 0 ∉ eventAbscissas T)
    (w : Plane → ℝ) (hw : ∀ c ∈ Q, 0≤w c) {R : ℝ} (hR : 0<R) :
    ∃ (f : Fin (FiniteSampling.sampleSize R (candidateCodes Q).card) → Plane)
      (D : Finset (Set Plane)),
      (∀ j, f j ∈ Q) ∧
      (∑ j, w (f j) ≤ 2*(FiniteSampling.sampleSize R (candidateCodes Q).card : ℝ)*
        ((∑ c ∈ Q, w c)/Q.card)) ∧
      D.card ≤ 43*(1+(FiniteSampling.sampleSize R (candidateCodes Q).card)^2) ∧
      (∀ U ∈ D, IsOpen U ∧ ((conflicts Q U).card : ℝ)≤(Q.card : ℝ)/R) ∧
      (∀ p ∈ P, (∀ j, dist p (f j)≠1) → ∃ U ∈ D, p ∈ U) := by
  let C (r : RegionCode) : Finset Q := univ.filter (fun (c : Q) => ∃ p ∈ codeRegion r, dist p (c : Plane)=1)
  have hl : 0<Fintype.card Q := by simpa using hQ.card_pos
  obtain ⟨f,hf,hcost⟩ := FiniteSampling.exists_hit_large_conflicts_with_cost hl (candidateCodes Q)
    C (fun c => w c) (fun c => hw c c.property) hR
  let T := univ.image (fun j => (f j : Plane))
  have hT : T ⊆ Q := by
    intro c hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    exact (f j).property
  obtain ⟨d⟩ := arrangement_exists T
  let D := d.pieces.image (fun r => region d.a r.1 r.2.1 r.2.2)
  refine ⟨fun j => f j,D,fun j => (f j).property,?_,?_,?_,?_⟩
  · have hs : ∑ c ∈ Q, w c=∑ c : Q, w c := Finset.sum_subtype Q (fun _ => Iff.rfl) w
    simpa only [hs,Fintype.card_coe] using hcost
  · apply Finset.card_image_le.trans (d.pieces_card.trans ?_)
    have ht : T.card ≤ FiniteSampling.sampleSize R (candidateCodes Q).card := by
      exact Finset.card_image_le.trans_eq (by simp)
    gcongr
  · intro U hU
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hU
    refine ⟨region_open _ _ _ _,?_⟩
    obtain ⟨c,hc,he⟩ := d.piece_description hT hr
    by_contra! hbad
    have hbig : (Fintype.card Q : ℝ)/R < ((C c).card : ℝ) := by
      simpa only [C,conflicts_subtype_card,Fintype.card_coe,← he] using hbad
    obtain ⟨j,hj⟩ := hf c hc hbig
    obtain ⟨p,hp,hpf⟩ := (Finset.mem_filter.mp hj).2
    rw [← he] at hp
    exact d.piece_avoids hr p hp (f j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) hpf
  · intro p hp havoid
    have hpT : ∀ c ∈ T, dist p c≠1 := by
      intro c hc
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
      exact havoid j
    obtain ⟨r,hr,hpr⟩ := d.pieces_cover (hpos T hT p hp hpT) hpT
    exact ⟨_,Finset.mem_image.mpr ⟨r,hr,rfl⟩,hpr⟩

lemma rotate_continuous (e : Plane) : Continuous (rotate e) := by
  unfold rotate projection
  fun_prop

lemma conflicts_rotate (Q : Finset Plane) (e : Plane) (he : (e 0)^2+(e 1)^2=1)
    (U : Set Plane) :
    conflicts (Q.image (rotate e)) U=(conflicts Q ((rotate e) ⁻¹' U)).image (rotate e) := by
  ext c
  simp only [conflicts,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨c,hc,rfl⟩,p,hp,hpc⟩
    obtain ⟨p,rfl⟩ := rotate_surjective e he p
    exact ⟨c,⟨hc,p,hp,by simpa only [rotate_dist e he] using hpc⟩,rfl⟩
  · rintro ⟨c,⟨hc,p,hp,hpc⟩,rfl⟩
    exact ⟨⟨c,hc,rfl⟩,rotate e p,hp,by simpa only [rotate_dist e he] using hpc⟩

theorem cutting_with_cost (P Q : Finset Plane) (hQ : Q.Nonempty)
    (w : Plane → ℝ) (hw : ∀ c ∈ Q, 0≤w c) {R : ℝ} (hR : 0<R) :
    ∃ (s : ℕ) (T : Finset Plane) (D : Finset (Set Plane)),
      (s : ℝ) ≤ R*cuttingLog Q.card+1 ∧ T ⊆ Q ∧ T.card ≤ s ∧
      (∑ c ∈ T, w c ≤ 2*(s : ℝ)*((∑ c ∈ Q, w c)/Q.card)) ∧
      D.card ≤ 43*(1+s^2) ∧
      (∀ U ∈ D, IsOpen U ∧ ((conflicts Q U).card : ℝ)≤(Q.card : ℝ)/R) ∧
      (∀ p ∈ P, (∀ c ∈ T, dist p c≠1) → ∃ U ∈ D, p ∈ U) := by
  obtain ⟨e,he,hpos⟩ := good_rotated_position P Q
  let v : Plane ≃ Plane := Equiv.ofBijective (rotate e) ⟨rotate_injective e he,rotate_surjective e he⟩
  have hv (p : Plane) : v p=rotate e p := rfl
  let Q' := Q.image (rotate e)
  obtain ⟨f,D,hf,hcost,hD,hconf,hcover⟩ := cutting_good_position
    (P.image (rotate e)) Q' (Finset.Nonempty.image hQ _) hpos (fun c => w (v.symm c))
    (by intro c hc; change c ∈ Q.image (rotate e) at hc
        obtain ⟨c₀,hc₀,heq⟩ := Finset.mem_image.mp hc
        rw [← heq,← hv,Equiv.symm_apply_apply]
        exact hw c₀ hc₀) hR
  let s := FiniteSampling.sampleSize R (candidateCodes Q').card
  let g : Fin s → Plane := fun j => v.symm (f j)
  let T := univ.image g
  let D' := D.image (fun U => (rotate e) ⁻¹' U)
  have hcQ : Q'.card=Q.card := Finset.card_image_of_injective Q (rotate_injective e he)
  have hsum : ∑ c ∈ Q', (fun c => w (v.symm c)) c=∑ c ∈ Q, w c := by
    rw [Finset.sum_image (rotate_injective e he).injOn]
    simp only [← hv,Equiv.symm_apply_apply]
  have hg (j : Fin s) : g j ∈ Q := by
    obtain ⟨c,hc,hcf⟩ := Finset.mem_image.mp (hf j)
    have hh : g j=c := by change v.symm (f j)=c; rw [← hcf,← hv,v.symm_apply_apply]
    rwa [hh]
  refine ⟨s,T,D',?_,?_,?_,?_,?_,?_,?_⟩
  · have hh := FiniteSampling.sampleSize_le hR (candidateCodes_card Q')
    simpa only [hcQ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_pow,cuttingLog,Nat.cast_ofNat] using hh
  · intro c hc
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
    exact hg j
  · exact Finset.card_image_le.trans_eq (by simp)
  · have hh : ∑ c ∈ T, w c ≤ ∑ j, w (g j) :=
      Finset.sum_image_le_of_nonneg (fun c hc => by
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hc
        exact hw _ (hg j))
    exact hh.trans (by simpa only [hsum,hcQ,Function.comp_apply] using hcost)
  · exact Finset.card_image_le.trans hD
  · intro U hU
    obtain ⟨V,hV,rfl⟩ := Finset.mem_image.mp hU
    refine ⟨(hconf V hV).1.preimage (rotate_continuous e),?_⟩
    have hh := (hconf V hV).2
    rw [conflicts_rotate Q e he,Finset.card_image_of_injective _ (rotate_injective e he),hcQ] at hh
    exact hh
  · intro p hp havoid
    have ha : ∀ j, dist (rotate e p) (f j)≠1 := by
      intro j hj
      have hh : f j=rotate e (g j) := (v.apply_symm_apply (f j)).symm
      rw [hh,rotate_dist e he] at hj
      exact havoid (g j) (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩) hj
    obtain ⟨U,hU,hpU⟩ := hcover (rotate e p) (Finset.mem_image.mpr ⟨p,hp,rfl⟩) ha
    exact ⟨_,Finset.mem_image.mpr ⟨U,hU,rfl⟩,hpU⟩

end PlanarUnitDistances.CircleCutting

namespace PlanarUnitDistances.CircleIncidence
open Real

lemma cutting_small_parameter {m l R : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hR : 0 ≤ R) (hR1 : R ≤ 1) (he : R^3*l=m^2) : m*sqrt l ≤ l := by
  have hR3 : R^3 ≤ 1 := by simpa using pow_le_one₀ hR hR1 (n := 3)
  have hsq : m^2 ≤ l := by nlinarith
  have hp := mul_le_mul_of_nonneg_right hsq hl
  have hs := Real.sq_sqrt hl
  have he' : (m*sqrt l)^2=m^2*l := by rw [mul_pow,hs]
  have hmn : 0 ≤ m*sqrt l := mul_nonneg hm (sqrt_nonneg l)
  nlinarith

lemma cutting_large_parameter {m l R L : ℝ} (hm : 0 ≤ m) (hl : 0 < l)
    (hml : m ≤ l) (_hR : 0 ≤ R) (hL : 1 ≤ L) (he : R^3*l=m^2)
    (hlarge : l < 4*(R*L+1)) : l ≤ 32*L^2 := by
  have hLn : 0 ≤ L := by linarith
  have hL2 : 1 ≤ L^2 := by nlinarith
  by_cases hl8 : l ≤ 8
  · nlinarith
  have hlarge' : l ≤ 8*R*L := by linarith
  have hR3 : R^3 ≤ l := by
    have hs : m^2 ≤ l^2 := (sq_le_sq₀ hm hl.le).mpr hml
    nlinarith
  have hc := pow_le_pow_left₀ hl.le hlarge' 3
  have hc' : l^3 ≤ 512*l*L^3 := by
    have hh := mul_le_mul_of_nonneg_right hR3 (show 0 ≤ 512*L^3 by positivity)
    nlinarith only [hc,hh]
  have hc'' : l^2 ≤ 512*L^3 := by nlinarith only [hc',hl]
  have hLpow : L^3 ≤ L^4 := by
    exact pow_le_pow_right₀ hL (by norm_num)
  have hh : l^2 ≤ (32*L^2)^2 := by nlinarith only [hc'',hLpow,sq_nonneg (L^2)]
  exact (sq_le_sq₀ hl.le (by positivity)).mp hh

lemma cutting_sqrt_identity {m l R : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l) (hR : 0 < R)
    (he : R^3*l=m^2) : m*sqrt (l/R)=R*l := by
  have hs := Real.sq_sqrt (div_nonneg hl hR.le)
  have heq : (m*sqrt (l/R))^2=(R*l)^2 := by
    rw [mul_pow,hs,← he]
    field_simp
  exact (sq_eq_sq₀ (by positivity) (by positivity)).mp heq

lemma cutting_absorbed_numeric {m l R L : ℝ} (hm : 0 ≤ m) (hl : 0 ≤ l)
    (hR : 1 ≤ R) (hL : 1 ≤ L) (he : R^3*l=m^2) :
    4*(R*L+1)*l+4*m*sqrt (l/R)+172*(1+(R*L+1)^2)*(l/R) ≤
      1000*L^2*(R*l+m+l) := by
  have hRp : 0 < R := by linarith
  have hLn : 0 ≤ L := by linarith
  have hR2 : 1 ≤ R*L := by nlinarith
  have hL2 : L ≤ L^2 := by nlinarith
  have hRLn : 0 ≤ R*L := by positivity
  have ha : R*L+1 ≤ 2*(R*L) := by linarith
  have hb := (sq_le_sq₀ (show 0 ≤ R*L+1 by positivity) (show 0 ≤ 2*(R*L) by positivity)).mpr ha
  have hc : 1+(R*L+1)^2 ≤ 5*R^2*L^2 := by nlinarith [sq_nonneg (R*L-1)]
  have hd := mul_le_mul_of_nonneg_right hc (div_nonneg hl hRp.le)
  have hd' : (5*R^2*L^2)*(l/R)=5*R*L^2*l := by field_simp
  rw [hd'] at hd
  have ha' := mul_le_mul_of_nonneg_right ha hl
  have hLL := mul_le_mul_of_nonneg_left hL2 (show 0 ≤ R*l by positivity)
  have hsq := cutting_sqrt_identity hm hl hRp he
  have hlo : R*l ≤ R*L^2*l := by
    have hLsq : 1 ≤ L^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hLsq (show 0 ≤ R*l by positivity)
    nlinarith
  have hmn : 0 ≤ L^2*m := by positivity
  have hln : 0 ≤ L^2*l := by positivity
  nlinarith only [hd,ha',hLL,hsq,hlo,hmn,hln]

lemma cutting_parameter_exists {m l : ℝ} (hm : 0 < m) (hl : 0 < l) :
    ∃ R : ℝ, 0 < R ∧ R^3*l=m^2 ∧ R*l=(m*l)^((2:ℝ)/3) := by
  let R : ℝ := (m^2/l)^((1:ℝ)/3)
  have hb : 0 < m^2/l := div_pos (sq_pos_of_pos hm) hl
  have hR : 0 < R := Real.rpow_pos_of_pos hb _
  have he : R^3*l=m^2 := by
    have hh : R^3=m^2/l := by
      change ((m^2/l)^((1:ℝ)/3))^3=m^2/l
      rw [← Real.rpow_mul_natCast hb.le]
      norm_num
    rw [hh,div_mul_cancel₀ _ hl.ne']
  refine ⟨R,hR,he,?_⟩
  have hn := Real.rpow_nonneg (mul_pos hm hl).le ((2:ℝ)/3)
  have hs : ((m*l)^((2:ℝ)/3))^3=(m*l)^2 := by
    rw [← Real.rpow_mul_natCast (mul_pos hm hl).le]
    norm_num
  have hh : (R*l)^3=((m*l)^((2:ℝ)/3))^3 := by
    rw [hs]
    calc
      (R*l)^3 = (R^3*l)*l^2 := by ring
      _ = m^2*l^2 := by rw [he]
      _ = (m*l)^2 := by ring
  exact (pow_left_inj₀ (mul_pos hR hl).le hn (by norm_num : 3≠0)).mp hh

end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.CircleIncidence
open Finset Classical
open CircleCutting

lemma degree_nonneg (P : Finset Plane) (q : Plane) : 0 ≤ degree P q := Nat.cast_nonneg _

lemma incidences_nonneg (P Q : Finset Plane) : 0  ≤  incidences P Q :=
  Finset.sum_nonneg (fun q _ => degree_nonneg P q)

lemma incidences_comm (P Q : Finset Plane) : incidences P Q=incidences Q P := by
  unfold incidences
  simp_rw [degree_sum]
  rw [Finset.sum_comm]
  simp only [dist_comm]

lemma common_sum (Q : Finset Plane) (p r : Plane) :
    common Q p r = ∑ q ∈ Q, (if dist p q=1 then (1 : ℝ) else 0)*(if dist r q=1 then 1 else 0) := by
  simp only [common,← Finset.sum_boole]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> simp_all

lemma common_le_two (Q : Finset Plane) (p r : Plane) (hpr : p≠r) : common Q p r ≤ 2 := by
  apply Nat.cast_le.mpr
  apply circle_intersection_card p r hpr
  intro q hq
  simpa only [dist_comm] using (Finset.mem_filter.mp hq).2

lemma common_self (Q : Finset Plane) (p : Plane) : common Q p p=degree Q p := by
  simp only [common,degree,and_self,dist_comm]

lemma degree_sq_sum (P Q : Finset Plane) :
    ∑ q ∈ Q, (degree P q)^2 = ∑ p ∈ P, ∑ r ∈ P, common Q p r := by
  simp_rw [degree_sum,pow_two,Finset.sum_mul,Finset.mul_sum,common_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p _
  rw [Finset.sum_comm]

lemma degree_sq_bound (P Q : Finset Plane) :
    ∑ q ∈ Q, (degree P q)^2  ≤  incidences P Q+2*(P.card : ℝ)^2 := by
  rw [degree_sq_sum]
  have h (p : Plane) (hp : p ∈ P) : ∑ r ∈ P, common Q p r  ≤  degree Q p+2*(P.card : ℝ) := by
    rw [← Finset.sum_erase_add _ _ hp,common_self]
    have hh : ∑ r ∈ P.erase p, common Q p r  ≤  2*(P.card : ℝ) := by
      apply (Finset.sum_le_sum (fun r hr => common_le_two Q p r (Finset.ne_of_mem_erase hr).symm)).trans
      simp only [Finset.sum_const,nsmul_eq_mul]
      have hc : ((P.erase p).card : ℝ) ≤ (P.card : ℝ) := Nat.cast_le.mpr (Finset.card_erase_le)
      linarith
    linarith
  apply (Finset.sum_le_sum h).trans_eq
  rw [Finset.sum_add_distrib]
  change incidences Q P + _ = _
  rw [incidences_comm Q P]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

lemma incidences_pair_bound (P Q : Finset Plane) :
    incidences P Q  ≤  2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ)+2*Q.card := by
  have hcs : (incidences P Q)^2  ≤  (Q.card : ℝ)*(∑ q ∈ Q, (degree P q)^2) := sq_sum_le_card_mul_sum_sq
  have hsq := degree_sq_bound P Q
  have hn := incidences_nonneg P Q
  have hm : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  have hl : (0 : ℝ) ≤ Q.card := Nat.cast_nonneg _
  have hr := Real.sqrt_nonneg (Q.card : ℝ)
  have he := Real.sq_sqrt hl
  have hh : (incidences P Q)^2  ≤  (Q.card : ℝ)*(incidences P Q+2*(P.card : ℝ)^2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hsq hl)
  by_contra! hbad
  have ht : 0 ≤ 2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ)+2*Q.card := by positivity
  have hmul : (2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ)+2*Q.card)^2 < (incidences P Q)^2 := by nlinarith
  have hh' : (incidences P Q-2*(Q.card : ℝ))^2 ≤ 2*(P.card : ℝ)^2*(Q.card : ℝ) := by
    have hi : (2 : ℝ)*Q.card < incidences P Q := by nlinarith
    nlinarith
  have hz : 0 ≤ 2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ) := by positivity
  have hi : 2*(P.card : ℝ)*Real.sqrt (Q.card : ℝ) < incidences P Q-2*(Q.card : ℝ) := by linarith
  have hs := (sq_lt_sq₀ hz (hz.trans hi.le)).mpr hi
  have hid : ((P.card : ℝ)*Real.sqrt (Q.card : ℝ))^2=(P.card : ℝ)^2*(Q.card : ℝ) := by rw [mul_pow,he]
  nlinarith [sq_nonneg ((P.card : ℝ)*Real.sqrt (Q.card : ℝ))]

lemma degree_mono {P P' : Finset Plane} (h : P ⊆ P') (q : Plane) : degree P q ≤ degree P' q := by
  apply Nat.cast_le.mpr
  exact Finset.card_le_card (Finset.filter_subset_filter _ h)

lemma incidences_mono_left {P P' : Finset Plane} (h : P ⊆ P') (Q : Finset Plane) :
    incidences P Q  ≤  incidences P' Q :=
  Finset.sum_le_sum (fun q _ => degree_mono h q)

lemma incidences_mono_right (P : Finset Plane) {Q Q' : Finset Plane} (h : Q ⊆ Q') :
    incidences P Q  ≤  incidences P Q' :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun q _ _ => degree_nonneg P q)

lemma incidences_filter_split (P Q : Finset Plane) (A : Plane → Prop) :
    incidences P Q=incidences (P.filter A) Q+incidences (P.filter (fun p => ¬ A p)) Q := by
  rw [incidences_comm P Q,incidences_comm (P.filter A) Q,
    incidences_comm (P.filter (fun p => ¬ A p)) Q]
  exact (Finset.sum_filter_add_sum_filter_not P A (degree Q)).symm

lemma incidence_deletion_split (P Q T : Finset Plane) :
    incidences P Q=incidences (retained P T) Q+incidences (deleted P T) Q := by
  rw [incidences_filter_split P Q (fun p => ∀ c ∈ T, dist p c≠1)]
  congr 1
  · apply congrArg (fun S => incidences S Q)
    ext p
    simp only [Finset.mem_filter,retained]
  · apply congrArg (fun S => incidences S Q)
    ext p
    simp only [Finset.mem_filter,deleted,not_forall,not_not,exists_prop]

lemma deleted_degree_le (P T : Finset Plane) (q : Plane) (hq : q ∉ T) :
    degree (deleted P T) q  ≤  2*T.card := by
  let B (c : Plane) := P.filter (fun p => dist p c=1 ∧ dist p q=1)
  have hsub : (deleted P T).filter (fun p => dist p q=1) ⊆ T.biUnion B := by
    intro p hp
    obtain ⟨hp,hpq⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp,c,hc,hpc⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨hp,hpc,hpq⟩⟩
  have hc (c : Plane) (hmem : c ∈ T) : (B c).card ≤ 2 :=
    circle_intersection_card c q (fun he => hq (he ▸ hmem)) (B c)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hh : ((deleted P T).filter (fun p => dist p q=1)).card  ≤  ∑ _c ∈ T, (2 : ℕ) :=
    (Finset.card_le_card hsub).trans (Finset.card_biUnion_le.trans (Finset.sum_le_sum hc))
  have hsum : (∑ _c ∈ T, (2 : ℕ))=2*T.card := by simp [mul_comm]
  rw [hsum] at hh
  unfold degree
  exact_mod_cast hh

lemma deleted_incidence_le (P Q T : Finset Plane) (hT : T ⊆ Q) :
    incidences (deleted P T) Q  ≤  incidences P T+2*(T.card : ℝ)*Q.card := by
  have he : incidences (deleted P T) Q = incidences (deleted P T) T+
      incidences (deleted P T) (Q \ T) := by
    unfold incidences
    have hh := Finset.sum_sdiff (f := degree (deleted P T)) hT
    linarith
  rw [he]
  have hT' : incidences (deleted P T) T  ≤  incidences P T :=
    incidences_mono_left (Finset.filter_subset _ _) T
  have hrest : incidences (deleted P T) (Q \ T)  ≤  2*(T.card : ℝ)*Q.card := by
    apply (Finset.sum_le_sum (fun q hq => deleted_degree_le P T q (Finset.mem_sdiff.mp hq).2)).trans
    simp only [Finset.sum_const,nsmul_eq_mul]
    have hh : ((Q \ T).card : ℝ) ≤ (Q.card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)
    have hn : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
    nlinarith
  exact add_le_add hT' hrest

lemma incidence_in_region (P Q : Finset Plane) (U : Set Plane) (hP : ∀ p ∈ P, p ∈ U) :
    incidences P Q=incidences P (conflicts Q U) := by
  apply (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro q hq hnot
  unfold degree
  have he : P.filter (fun p => dist p q=1)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro p hp
    obtain ⟨hp,hpq⟩ := Finset.mem_filter.mp hp
    exact hnot (Finset.mem_filter.mpr ⟨hq,p,hP p hp,hpq⟩)
  rw [he,Finset.card_empty,Nat.cast_zero]

lemma incidence_partition {P Q : Finset Plane} {D : Finset (Set Plane)} (a : Plane → Set Plane)
    (ha : ∀ p ∈ P, a p ∈ D) :
    (∑ U ∈ D, incidences (P.filter (fun p => a p=U)) Q)=incidences P Q := by
  rw [incidences_comm P Q]
  have h (U : Set Plane) : incidences (P.filter (fun p => a p=U)) Q =
      ∑ p ∈ P.filter (fun p => a p=U), degree Q p := incidences_comm _ _
  simp_rw [h]
  exact Finset.sum_fiberwise_of_maps_to ha (degree Q)

lemma incidence_cutting_regions (P Q : Finset Plane) (D : Finset (Set Plane))
    {b : ℝ} (hconf : ∀ U ∈ D, ((conflicts Q U).card : ℝ) ≤ b)
    (hcover : ∀ p ∈ P, ∃ U ∈ D, p ∈ U) :
    incidences P Q  ≤  2*(P.card : ℝ)*Real.sqrt b+2*(D.card : ℝ)*b := by
  choose a ham hamem using hcover
  let f (p : Plane) : Set Plane := if hp : p ∈ P then a p hp else ∅
  have hf (p : Plane) (hp : p ∈ P) : f p ∈ D ∧ p ∈ f p := by
    simpa only [f,dite_eq_left hp] using And.intro (ham p hp) (hamem p hp)
  let B (U : Set Plane) := P.filter (fun p => f p=U)
  have hB (U : Set Plane) : ∀ p ∈ B U, p ∈ U := by
    intro p hp
    obtain ⟨hp,hpU⟩ := Finset.mem_filter.mp hp
    exact hpU ▸ (hf p hp).2
  have hc (U : Set Plane) (hU : U ∈ D) :
      incidences (B U) Q  ≤  2*((B U).card : ℝ)*Real.sqrt b+2*b := by
    rw [incidence_in_region (B U) Q U (hB U)]
    apply (incidences_pair_bound _ _).trans
    have hs := Real.sqrt_le_sqrt (hconf U hU)
    have hn : (0 : ℝ) ≤ (B U).card := Nat.cast_nonneg _
    nlinarith [hconf U hU]
  have hsum : ∑ U ∈ D, ((B U).card : ℝ)=(P.card : ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (fun p hp => (hf p hp).1) (fun _ : Plane => (1 : ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  rw [← incidence_partition f (fun p hp => (hf p hp).1)]
  apply (Finset.sum_le_sum hc).trans_eq
  rw [Finset.sum_add_distrib]
  rw [← Finset.sum_mul,← Finset.mul_sum,hsum]
  simp only [Finset.sum_const,nsmul_eq_mul]
  ring

theorem incidence_cutting_recurrence (P Q : Finset Plane) (hQ : Q.Nonempty)
    {R : ℝ} (hR : 0 < R) :
    ∃ s : ℕ, (s : ℝ) ≤ R*cuttingLog Q.card+1 ∧
      incidences P Q  ≤  2*(s : ℝ)*(incidences P Q/Q.card)+2*(s : ℝ)*Q.card+
        2*(P.card : ℝ)*Real.sqrt ((Q.card : ℝ)/R)+86*(1+(s : ℝ)^2)*((Q.card : ℝ)/R) := by
  obtain ⟨s,T,D,hs,hT,hTs,hcost,hD,hconf,hcover⟩ :=
    cutting_with_cost P Q hQ (degree P) (fun q _ => degree_nonneg P q) hR
  refine ⟨s,hs,?_⟩
  have hp : incidences (retained P T) Q  ≤
      2*(P.card : ℝ)*Real.sqrt ((Q.card : ℝ)/R)+86*(1+(s : ℝ)^2)*((Q.card : ℝ)/R) := by
    have hh := incidence_cutting_regions (retained P T) Q D
      (fun U hU => (hconf U hU).2)
      (fun p hp => hcover p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
    apply hh.trans
    have hpc : ((retained P T).card : ℝ) ≤ (P.card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hdc : (D.card : ℝ) ≤ 43*(1+(s : ℝ)^2) := by exact_mod_cast hD
    have hn : 0 ≤ (Q.card : ℝ)/R := div_nonneg (Nat.cast_nonneg _) hR.le
    have h1 := mul_le_mul_of_nonneg_right hpc (Real.sqrt_nonneg ((Q.card : ℝ)/R))
    have h2 := mul_le_mul_of_nonneg_right hdc hn
    linarith
  have hd := deleted_incidence_le P Q T hT
  have ht : (T.card : ℝ) ≤ s := Nat.cast_le.mpr hTs
  change incidences P T ≤ 2*(s : ℝ)*(incidences P Q/Q.card) at hcost
  have hmul := mul_le_mul_of_nonneg_right ht (Nat.cast_nonneg Q.card : (0 : ℝ) ≤ Q.card)
  have hsplit := incidence_deletion_split P Q T
  linarith

lemma incidence_cutting_absorbed (P Q : Finset Plane) (hQ : Q.Nonempty)
    {R L : ℝ} (hR : 0 < R) (hL : cuttingLog Q.card ≤ L)
    (hsmall : 4*(R*L+1) ≤ (Q.card : ℝ)) :
    incidences P Q  ≤  4*(R*L+1)*(Q.card : ℝ)+4*(P.card : ℝ)*Real.sqrt ((Q.card : ℝ)/R)+
      172*(1+(R*L+1)^2)*((Q.card : ℝ)/R) := by
  obtain ⟨s,hs,hi⟩ := incidence_cutting_recurrence P Q hQ hR
  have hs' : (s : ℝ) ≤ R*L+1 := hs.trans (by nlinarith)
  have hsn : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hrl : 0 ≤ R*L+1 := hsn.trans hs'
  have hsq : (s : ℝ)^2 ≤ (R*L+1)^2 := sq_le_sq₀ hsn hrl |>.mpr hs'
  have hl : (0 : ℝ)<Q.card := Nat.cast_pos.mpr hQ.card_pos
  have hn := incidences_nonneg P Q
  have hcost : 2*(s : ℝ)*(incidences P Q/Q.card) ≤ incidences P Q/2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hl).mpr
    have hh : 4*(s : ℝ) ≤ (Q.card : ℝ) := by linarith
    have hh' := mul_le_mul_of_nonneg_right hh hn
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hs' hl.le
  have h2 := mul_le_mul_of_nonneg_right hsq (div_nonneg hl.le hR.le)
  linarith

lemma cuttingLog_one_le (l : ℕ) : 1 ≤ cuttingLog l := by
  have hn : (0 : ℝ) ≤ l := Nat.cast_nonneg _
  have hp : (1 : ℝ) ≤ (1+(l : ℝ))^6 := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1+l) 6
  apply (Real.le_log_iff_exp_le (by positivity : 0 < 10*(81*(1+(l : ℝ))^6+1))).mpr
  exact Real.exp_one_lt_three.le.trans (by nlinarith)

lemma cuttingLog_mono : Monotone cuttingLog := by
  intro a b hab
  have hh : (a : ℝ) ≤ b := Nat.cast_le.mpr hab
  apply Real.log_le_log (by positivity)
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1+a by positivity) (show (1 : ℝ)+a ≤ 1+b by linarith) 6
  nlinarith only [hp]

lemma incidence_bound_oriented (P Q : Finset Plane) (hPQ : P.card ≤ Q.card)
    {L : ℝ} (hL : 1 ≤ L) (hLog : cuttingLog Q.card ≤ L) :
    incidences P Q ≤ 1000*L^2*(((P.card : ℝ)*Q.card)^((2:ℝ)/3)+P.card+Q.card) := by
  by_cases hp : P.Nonempty
  · have hm : (0 : ℝ)<P.card := Nat.cast_pos.mpr hp.card_pos
    have hml : (P.card : ℝ) ≤ Q.card := Nat.cast_le.mpr hPQ
    have hl : (0 : ℝ)<Q.card := hm.trans_le hml
    have hq : Q.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp hl)
    obtain ⟨R,hR,he,ha⟩ := cutting_parameter_exists hm hl
    rw [← ha]
    have hLsq : 1 ≤ L^2 := by nlinarith
    have hLn : 0 ≤ L := by linarith
    have hpos : 0 ≤ L^2*(R*(Q.card : ℝ)+P.card) := by positivity
    by_cases hR1 : R ≤ 1
    · have hs := cutting_small_parameter hm.le hl.le hR.le hR1 he
      have hi := incidences_pair_bound P Q
      have hh := mul_le_mul_of_nonneg_right hLsq hl.le
      nlinarith only [hs,hi,hh,hpos]
    · have hR1' : 1 ≤ R := (le_of_not_ge hR1)
      by_cases hsmall : 4*(R*L+1) ≤ (Q.card : ℝ)
      · exact (incidence_cutting_absorbed P Q hq hR hLog hsmall).trans
          (cutting_absorbed_numeric hm.le hl.le hR1' hL he)
      · have hs := cutting_large_parameter hm.le hl hml hR.le hL he (lt_of_not_ge hsmall)
        have hp := mul_le_mul_of_nonneg_left hs hm.le
        have hi := incidences_le P Q
        have hn : 0 ≤ L^2*(R*(Q.card : ℝ)+Q.card) := by positivity
        have hn' : 0 ≤ L^2*(P.card : ℝ) := by positivity
        nlinarith only [hp,hi,hn,hn']
  · have he : P=∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    subst P
    simp only [incidences,degree,Finset.filter_empty,Finset.card_empty,Nat.cast_zero,
      Finset.sum_const_zero,zero_mul,Real.zero_rpow (by norm_num : (2:ℝ)/3≠0),zero_add]
    positivity

end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.FiniteTruncation
open Finset Classical

theorem weighted_subset {α : Type*} (s : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) {B : ℕ} (hB : 0<B) :
    ∃ t ⊆ s, t.card ≤ B ∧
      (∑ a ∈ s, w a) ≤ (1+(s.card : ℝ)/B)*(∑ a ∈ t, w a) := by
  classical
  revert hw
  refine Finset.strongInductionOn s ?_
  intro s ih hw
  have hBn : (0 : ℝ)<B := Nat.cast_pos.mpr hB
  by_cases hs : s.card ≤ B
  · refine ⟨s,Finset.Subset.refl _,hs,?_⟩
    have hn : 0 ≤ ∑ a ∈ s, w a := Finset.sum_nonneg hw
    have hc : 0 ≤ (s.card : ℝ)/B := by positivity
    nlinarith
  · obtain ⟨t,ht,htB⟩ := Finset.exists_subset_card_eq (le_of_not_ge hs)
    have htpos : t.Nonempty := Finset.card_pos.mp (by omega)
    have hss : s \ t ⊂ s := Finset.sdiff_ssubset ht htpos
    obtain ⟨u,hu,huB,huW⟩ := ih (s \ t) hss (fun a ha => hw a (Finset.mem_sdiff.mp ha).1)
    have hc : ((s \ t).card : ℝ)+(t.card : ℝ)=(s.card : ℝ) := by
      exact_mod_cast Finset.card_sdiff_add_card_eq_card ht
    have hsum : (∑ a ∈ s \ t, w a)+(∑ a ∈ t, w a)=∑ a ∈ s, w a :=
      Finset.sum_sdiff ht
    have htW : 0 ≤ ∑ a ∈ t, w a := Finset.sum_nonneg (fun a ha => hw a (ht ha))
    have huWn : 0 ≤ ∑ a ∈ u, w a :=
      Finset.sum_nonneg (fun a ha => hw a (Finset.mem_sdiff.mp (hu ha)).1)
    have hco : 0 ≤ 1+((s \ t).card : ℝ)/B := by positivity
    have he : 2+((s \ t).card : ℝ)/B=1+(s.card : ℝ)/B := by
      rw [htB] at hc
      field_simp
      linarith
    rcases le_total (∑ a ∈ u, w a) (∑ a ∈ t, w a) with h|h
    · refine ⟨t,ht,htB.le,?_⟩
      have hz := huW.trans (mul_le_mul_of_nonneg_left h hco)
      rw [← he]
      nlinarith
    · refine ⟨u,hu.trans Finset.sdiff_subset,huB,?_⟩
      rw [← he]
      nlinarith

end PlanarUnitDistances.FiniteTruncation

namespace PlanarUnitDistances.CircleIncidence
open Finset Classical CircleCutting

lemma dense_region_subset (P Q : Finset Plane) (hP : P.Nonempty)
    (D : Finset (Set Plane)) {b : ℝ} {B : ℕ} (hB : 0<B)
    (hconf : ∀ U ∈ D, ((conflicts Q U).card : ℝ) ≤ b)
    (hcover : ∀ p ∈ P, ∃ U ∈ D, p ∈ U) :
    ∃ F ⊆ P, ∃ G ⊆ Q, F.card ≤ B ∧ (G.card : ℝ) ≤ b ∧
      incidences P Q ≤ ((D.card : ℝ)+(P.card : ℝ)/B)*incidences F G := by
  choose a ham hamem using hcover
  let f (p : Plane) : Set Plane := if hp : p ∈ P then a p hp else ∅
  have hf (p : Plane) (hp : p ∈ P) : f p ∈ D ∧ p ∈ f p := by
    simpa only [f,dite_eq_left hp] using And.intro (ham p hp) (hamem p hp)
  let A (U : Set Plane) := P.filter (fun p => f p=U)
  have hA (U : Set Plane) : ∀ p ∈ A U, p ∈ U := by
    intro p hp
    obtain ⟨hp,hpU⟩ := Finset.mem_filter.mp hp
    exact hpU ▸ (hf p hp).2
  have hs (U : Set Plane) : ∃ t ⊆ A U, t.card ≤ B ∧
      incidences (A U) Q ≤ (1+((A U).card : ℝ)/B)*incidences t Q := by
    obtain ⟨t,ht,htB,htW⟩ := FiniteTruncation.weighted_subset (A U) (degree Q)
      (fun p _ => degree_nonneg Q p) hB
    refine ⟨t,ht,htB,?_⟩
    rw [incidences_comm (A U) Q,incidences_comm t Q]
    exact htW
  choose t ht htB htW using hs
  have hD : D.Nonempty := by
    obtain ⟨p,hp⟩ := hP
    exact ⟨f p,(hf p hp).1⟩
  obtain ⟨U,hU,hmax⟩ := Finset.exists_max_image D (fun U => incidences (t U) Q) hD
  refine ⟨t U,(ht U).trans (Finset.filter_subset _ _),conflicts Q U,
    Finset.filter_subset _ _,htB U,hconf U hU,?_⟩
  rw [← incidence_in_region (t U) Q U (fun p hp => hA U p (ht U hp))]
  have hsum : ∑ V ∈ D, ((A V).card : ℝ)=(P.card : ℝ) := by
    have hh := Finset.sum_fiberwise_of_maps_to (fun p hp => (hf p hp).1) (fun _ : Plane => (1 : ℝ))
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_one] using hh
  have hh (V : Set Plane) (hV : V ∈ D) : incidences (A V) Q ≤
      (1+((A V).card : ℝ)/B)*incidences (t U) Q :=
    (htW V).trans (mul_le_mul_of_nonneg_left (hmax V hV) (by positivity))
  rw [← incidence_partition f (fun p hp => (hf p hp).1)]
  apply (Finset.sum_le_sum hh).trans_eq
  rw [← Finset.sum_mul,Finset.sum_add_distrib,← Finset.sum_div,hsum]
  simp

lemma deleted_incidence_trivial (P Q T : Finset Plane) (hT : T ⊆ Q) :
    incidences (deleted P T) Q ≤ (T.card : ℝ)*((P.card : ℝ)+2*Q.card) := by
  have hd := deleted_incidence_le P Q T hT
  have ht := incidences_le P T
  nlinarith

theorem exists_incidence_piece (P Q : Finset Plane) (hQ : Q.Nonempty)
    {R : ℝ} (hR : 0<R) {B : ℕ} (hB : 0<B) :
    ∃ F ⊆ P, ∃ G ⊆ Q, F.card ≤ B ∧ (G.card : ℝ) ≤ (Q.card : ℝ)/R ∧
      incidences P Q ≤ (R*cuttingLog Q.card+1)*((P.card : ℝ)+2*Q.card)+
        (43*(1+(R*cuttingLog Q.card+1)^2)+(P.card : ℝ)/B)*incidences F G := by
  obtain ⟨s,T,D,hs,hT,hTs,_,hD,hconf,hcover⟩ :=
    cutting_with_cost P Q hQ (degree P) (fun q _ => degree_nonneg P q) hR
  have hsn : (0 : ℝ) ≤ s := Nat.cast_nonneg _
  have hTl : (T.card : ℝ) ≤ R*cuttingLog Q.card+1 := (Nat.cast_le.mpr hTs).trans hs
  have hrl : 0 ≤ R*cuttingLog Q.card+1 := hsn.trans hs
  have hdel : incidences (deleted P T) Q ≤
      (R*cuttingLog Q.card+1)*((P.card : ℝ)+2*Q.card) :=
    (deleted_incidence_trivial P Q T hT).trans
      (mul_le_mul_of_nonneg_right hTl (by positivity))
  have hrP : ((retained P T).card : ℝ) ≤ (P.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_filter_le _ _)
  have hDc : (D.card : ℝ) ≤ 43*(1+(R*cuttingLog Q.card+1)^2) := by
    have hh : (D.card : ℝ) ≤ 43*(1+(s : ℝ)^2) := by exact_mod_cast hD
    have hh' := (sq_le_sq₀ hsn hrl).mpr hs
    linarith
  by_cases hp : (retained P T).Nonempty
  · obtain ⟨F,hF,G,hG,hFB,hGR,hFG⟩ := dense_region_subset (retained P T) Q hp D hB
      (fun U hU => (hconf U hU).2)
      (fun p hp => hcover p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)
    refine ⟨F,hF.trans (Finset.filter_subset _ _),G,hG,hFB,hGR,?_⟩
    have hcoef : (D.card : ℝ)+((retained P T).card : ℝ)/B ≤
        43*(1+(R*cuttingLog Q.card+1)^2)+(P.card : ℝ)/B :=
      add_le_add hDc (div_le_div_of_nonneg_right hrP (Nat.cast_nonneg _))
    have hm := mul_le_mul_of_nonneg_right hcoef (incidences_nonneg F G)
    have hsplit := incidence_deletion_split P Q T
    linarith
  · refine ⟨∅,Finset.empty_subset _,∅,Finset.empty_subset _,by simp,by simp; positivity,?_⟩
    have he : retained P T=∅ := Finset.not_nonempty_iff_eq_empty.mp hp
    have hz : incidences (retained P T) Q=0 := by simp [he,incidences,degree]
    have hz' : incidences ∅ ∅=0 := by simp [incidences]
    rw [hz',mul_zero,add_zero]
    have hsplit := incidence_deletion_split P Q T
    linarith

end PlanarUnitDistances.CircleIncidence

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PowerGrowth
open Filter

variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Lower.mono (hf : Lower F t f a) (h : f ≤ᶠ[F] g) : Lower F t g a := by
  intro ε hε
  filter_upwards [hf ε hε,h] with i hi hfg
  exact hi.trans hfg

lemma Upper.mono (hg : Upper F t g a) (h : f ≤ᶠ[F] g) : Upper F t f a := by
  intro ε hε
  filter_upwards [hg ε hε,h] with i hi hfg
  exact hfg.trans hi

lemma Lower.congr (hf : Lower F t f a) (h : f =ᶠ[F] g) : Lower F t g a :=
  hf.mono h.le

lemma Upper.congr (hf : Upper F t f a) (h : f =ᶠ[F] g) : Upper F t g a :=
  hf.mono h.symm.le

lemma eventually_one_le (ht : Tendsto t F atTop) : ∀ᶠ i in F,1 ≤ t i :=
  ht.eventually_ge_atTop 1

lemma eventually_base_pos (ht : Tendsto t F atTop) : ∀ᶠ i in F,0 < t i :=
  (eventually_one_le ht).mono fun _ hi => lt_of_lt_of_le zero_lt_one hi

lemma Lower.exponent_mono (hf : Lower F t f a) (h : b ≤ a)
    (ht : Tendsto t F atTop) : Lower F t f b := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_one_le ht] with i hi hti
  exact (Real.rpow_le_rpow_of_exponent_le hti (sub_le_sub_right h ε)).trans hi

lemma Upper.exponent_mono (hf : Upper F t f a) (h : a ≤ b)
    (ht : Tendsto t F atTop) : Upper F t f b := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_one_le ht] with i hi hti
  exact hi.trans (Real.rpow_le_rpow_of_exponent_le hti (by linarith))

lemma Lower.eventually_pos (hf : Lower F t f a) (ht : Tendsto t F atTop) :
    ∀ᶠ i in F,0 < f i := by
  filter_upwards [hf 1 zero_lt_one,eventually_base_pos ht] with i hi hti
  exact (Real.rpow_pos_of_pos hti _).trans_le hi

lemma Lower.mul (hf : Lower F t f a) (hg : Lower F t g b)
    (ht : Tendsto t F atTop) : Lower F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),eventually_base_pos ht]
    with i hi hj hti
  have he : a+b-ε=(a-ε/2)+(b-ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj (Real.rpow_nonneg hti.le _) ((Real.rpow_nonneg hti.le _).trans hi)

lemma Upper.mul (hf : Upper F t f a) (hg : Upper F t g b)
    (hnf : ∀ᶠ i in F,0 ≤ f i) (hng : ∀ᶠ i in F,0 ≤ g i)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hnf,hng,eventually_base_pos ht]
    with i hi hj _ hj0 hti
  have he : a+b+ε=(a+ε/2)+(b+ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj hj0 (Real.rpow_nonneg hti.le _)

lemma eventually_constant_le_rpow (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ i in F,C ≤ t i ^ ε := by
  exact (_root_.tendsto_rpow_atTop hε |>.comp ht).eventually_ge_atTop C

lemma Lower.const_mul (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 < C) : Lower F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C⁻¹,eventually_base_pos ht] with i hi hc hti
  have hc' : 1 ≤ C*(t i)^(ε/2) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hC).mp hc
  have he : a-ε/2=(a-ε)+ε/2 := by ring
  have hpos := Real.rpow_nonneg hti.le (a-ε)
  calc
    (t i)^(a-ε) ≤ (t i)^(a-ε)*(C*(t i)^(ε/2)) := le_mul_of_one_le_right hpos hc'
    _ = C*(t i)^(a-ε/2) := by
      conv_rhs => rw [he,Real.rpow_add hti]
      ring
    _ ≤ C*f i := mul_le_mul_of_nonneg_left hi hC.le

lemma Upper.const_mul (hf : Upper F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 ≤ C) : Upper F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C,eventually_base_pos ht] with i hi hc hti
  have he : a+ε=ε/2+(a+ε/2) := by ring
  calc
    C*f i ≤ C*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ (t i)^(ε/2)*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hti.le _)
    _ = (t i)^(a+ε) := by rw [he]; exact (Real.rpow_add hti _ _).symm

lemma Upper.add (hf : Upper F t f a) (hg : Upper F t g a)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i+g i) a := by
  have hmax : Upper F t (fun i => max (f i) (g i)) a := by
    intro ε hε
    filter_upwards [hf ε hε,hg ε hε] with i hi hj
    exact max_le hi hj
  exact (hmax.const_mul ht (show (0:ℝ)≤2 by norm_num)).mono
    (Eventually.of_forall fun i => by dsimp; linarith [le_max_left (f i) (g i),le_max_right (f i) (g i)])

lemma Lower.div (hf : Lower F t f a) (hg : Upper F t g b)
    (hng : ∀ᶠ i in F,0 < g i) (ht : Tendsto t F atTop) :
    Lower F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b-ε=(a-ε/2)-(b+ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ ((Real.rpow_nonneg hti.le _).trans hi) hi hj0 hj

end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma upper_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Upper F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
lemma lower_rpow (ht : Tendsto t F atTop) (a : ℝ) :
    Lower F t (fun i => t i^a) a := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  exact Real.rpow_le_rpow_of_exponent_le hi (by linarith)
lemma upper_const (ht : Tendsto t F atTop) (c : ℝ) : Upper F t (fun _ => c) 0 := by
  intro ε hε
  simpa only [zero_add] using eventually_constant_le_rpow ht hε c
lemma lower_const (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) : Lower F t (fun _ => c) 0 := by
  have h := (lower_rpow ht 0).const_mul ht hc
  simpa only [Real.rpow_zero,mul_one] using h

lemma Upper.div (hf : Upper F t f a) (hg : Lower F t g b)
    (hng : ∀ᶠi in F,0<g i) (ht : Tendsto t F atTop) :
    Upper F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b+ε=(a+ε/2)-(b-ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ (Real.rpow_nonneg hti.le _) hi (Real.rpow_pos_of_pos hti _) hj

lemma Upper.rpow (hf : Upper F t f a) (hnf : ∀ᶠi in F,0≤f i)
    (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) :
    Upper F t (fun i => f i^c) (a*c) := by
  intro ε hε
  filter_upwards [hf (ε/c) (div_pos hε hc),hnf,eventually_base_pos ht] with i hi hi0 hti
  have hh := Real.rpow_le_rpow hi0 hi hc.le
  rw [←Real.rpow_mul hti.le] at hh
  convert hh using 1
  congr 1
  field_simp

lemma Lower.rpow (hf : Lower F t f a) (ht : Tendsto t F atTop) {c : ℝ} (hc : 0<c) :
    Lower F t (fun i => f i^c) (a*c) := by
  intro ε hε
  filter_upwards [hf (ε/c) (div_pos hε hc),eventually_base_pos ht] with i hi hti
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hti.le _) hi hc.le
  rw [←Real.rpow_mul hti.le] at hh
  convert hh using 1
  congr 1
  field_simp

lemma Upper.tendsto_zero (hf : Upper F t f a) (hnf : ∀ᶠi in F,0≤f i)
    (ht : Tendsto t F atTop) (ha : a<0) : Tendsto f F (nhds 0) := by
  have hb := hf (-a/2) (by linarith)
  have he : a+ -a/2=a/2 := by ring
  rw [he] at hb
  have hz : Tendsto (fun x : ℝ => x^(a/2)) atTop (nhds 0) := by
    have he' : -(-a/2)=a/2 := by ring
    simpa only [he'] using (_root_.tendsto_rpow_neg_atTop (by linarith : 0 < -a/2))
  exact squeeze_zero' hnf hb (hz.comp ht)

lemma Upper.ratio_zero (hf : Upper F t f a) (hg : Lower F t g b)
    (hnf : ∀ᶠi in F,0≤f i) (ht : Tendsto t F atTop) (hab : a<b) :
    Tendsto (fun i => f i/g i) F (nhds 0) := by
  have hg0 := hg.eventually_pos ht
  exact (hf.div hg hg0 ht).tendsto_zero
    (by filter_upwards [hnf,hg0] with i hi hj; exact div_nonneg hi hj.le) ht (sub_neg.mpr hab)

lemma upper_log (ht : Tendsto t F atTop) : Upper F t (fun i => Real.log (t i)) 0 := by
  intro ε hε
  have hh := (_root_.isLittleO_log_rpow_atTop hε).bound (by norm_num : (0:ℝ)<1)
  filter_upwards [ht.eventually hh,eventually_base_pos ht] with i hi hti
  apply (le_abs_self (Real.log (t i))).trans
  simpa only [Real.norm_eq_abs,one_mul,abs_of_nonneg (Real.rpow_nonneg hti.le ε),zero_add] using hi

lemma Upper.log (hf : Upper F t f a) (hfp : ∀ᶠi in F,0<f i)
    (ht : Tendsto t F atTop) (ha : 0≤a) : Upper F t (fun i => Real.log (f i)) 0 := by
  apply ((upper_log ht).const_mul ht (show 0≤a+1 by linarith)).mono
  filter_upwards [hf 1 zero_lt_one,hfp,eventually_base_pos ht] with i hi hfi hti
  have hh := Real.log_le_log hfi hi
  simpa only [Real.log_rpow hti] using hh

lemma Lower.of_loss (hg : Lower F t g a) {h : ι → ℝ} (hh : Upper F t h b)
    (hh0 : ∀ᶠi in F,0≤h i) (ht : Tendsto t F atTop) (hab : b<a)
    (hle : ∀ᶠi in F,g i≤f i+h i) : Lower F t f a := by
  have hlim := hh.ratio_zero hg hh0 ht hab
  have hsmall : ∀ᶠi in F,h i/g i≤1/2 := hlim.eventually_le_const (by norm_num)
  apply (hg.const_mul ht (by norm_num : (0:ℝ)<1/2)).mono
  filter_upwards [hsmall,hg.eventually_pos ht,hle] with i hi hgi hle
  have hh' := (div_le_iff₀ hgi).mp hi
  linarith

lemma diagonal {R : ℕ → ℕ → Prop} (hR : ∀k,∀ᶠn in atTop,R k n) :
    ∃f : ℕ → ℕ,Tendsto f atTop atTop ∧ ∀n,R n (f n) := by
  have h : ∀k,∃N,∀n≥N,R k n := fun k => eventually_atTop.mp (hR k)
  choose N hN using h
  refine ⟨fun n => max n (N n),tendsto_atTop_mono (fun n => le_max_left n (N n)) tendsto_id,?_⟩
  intro n
  exact hN n _ (le_max_right _ _)
end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.CuttingAsymptotics
open Filter PowerGrowth CircleIncidence CircleCutting
open scoped Classical
noncomputable section

lemma cuttingLog_upper {t : ℕ → ℝ} {X : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3) :
    Upper atTop t (fun i => cuttingLog (X i).card) 0 := by
  have h1 := (upper_const ht 1).exponent_mono (by norm_num : (0:ℝ)≤3) ht
  have hs := h1.add hX ht
  have hp := hs.rpow (Eventually.of_forall fun i => by positivity) ht (by norm_num : (0:ℝ)<6)
  have hp' : Upper atTop t (fun i => 81*(1+((X i).card:ℝ))^6) 18 := by
    convert hp.const_mul ht (by norm_num : (0:ℝ)≤81) using 1
    · ext i; exact congrArg (81*·) (Real.rpow_natCast (1+((X i).card:ℝ)) 6).symm
    · norm_num
  have ho := hp'.add ((upper_const ht 1).exponent_mono (by norm_num : (0:ℝ)≤18) ht) ht
  have hq := ho.const_mul ht (by norm_num : (0:ℝ)≤10)
  exact hq.log (Eventually.of_forall fun i => by positivity) ht (by norm_num)

theorem exists_cut_sequence {t : ℕ → ℝ} (X : ℕ → Finset Plane)
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1≤t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hE : Lower atTop t (fun i => incidences (X i) (X i)) 4)
    {a : ℝ} (ha : 0<a) (ha1 : a<1) :
    ∃P Q : ℕ → Finset Plane,(∀i,P i⊆X i ∧ Q i⊆X i) ∧
      Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a) ∧
      Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a) ∧
      Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a) := by
  let R : ℕ → ℝ := fun i => (t i)^(1-a)
  let B : ℕ → ℕ := fun i => Nat.ceil ((t i)^(1+2*a))+1
  have ht0 (i : ℕ) : 0<t i := zero_lt_one.trans_le (ht1 i)
  have hRp (i : ℕ) : 0<R i := Real.rpow_pos_of_pos (ht0 i) _
  have hBp (i : ℕ) : 0<B i := Nat.succ_pos _
  choose P hP Q hQ hcP hcQ hc using fun i =>
    exists_incidence_piece (X i) (X i) (hX0 i) (hRp i) (hBp i)
  have hR : Upper atTop t R (1-a) := upper_rpow ht _
  have hRl : Lower atTop t R (1-a) := lower_rpow ht _
  have hBu : Upper atTop t (fun i => (B i:ℝ)) (1+2*a) := by
    apply ((upper_rpow ht (1+2*a)).add
      ((upper_const ht 2).exponent_mono (by linarith : 0≤1+2*a) ht) ht).mono
    exact Eventually.of_forall fun i => by
      have hh := Nat.ceil_lt_add_one (Real.rpow_nonneg (ht0 i).le (1+2*a))
      dsimp [B]
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
  have hBl : Lower atTop t (fun i => (B i:ℝ)) (1+2*a) := by
    apply (lower_rpow ht (1+2*a)).mono
    exact Eventually.of_forall fun i => by
      have hh := Nat.le_ceil ((t i)^(1+2*a))
      dsimp [B]
      simp only [Nat.cast_add,Nat.cast_one]
      linarith
  have hPu : Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a) :=
    hBu.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (hcP i))
  have hQu : Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a) := by
    have hh := (hX.div hRl (Eventually.of_forall hRp) ht).mono (Eventually.of_forall hcQ)
    convert hh using 1 <;> first | rfl | ring
  let S : ℕ → ℝ := fun i => R i*cuttingLog (X i).card+1
  have hln := cuttingLog_upper ht hX
  have hSu : Upper atTop t S (1-a) := by
    have hh := hR.mul hln (Eventually.of_forall fun i => (hRp i).le)
      (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
    simp only [add_zero] at hh
    exact hh.add ((upper_const ht 1).exponent_mono (by linarith : 0≤1-a) ht) ht
  have hS0 (i : ℕ) : 0≤S i := by
    dsimp [S]
    exact add_nonneg (mul_nonneg (hRp i).le (zero_le_one.trans (cuttingLog_one_le _))) zero_le_one
  let K : ℕ → ℝ := fun i => 43*(1+(S i)^2)+((X i).card:ℝ)/(B i:ℝ)
  have hKp (i : ℕ) : 0<K i := by dsimp [K]; positivity
  have hKu : Upper atTop t K (2-2*a) := by
    have hs2 := hSu.mul hSu (Eventually.of_forall hS0) (Eventually.of_forall hS0) ht
    have hs2' : Upper atTop t (fun i => (S i)^2) (2-2*a) := by
      convert hs2 using 1 <;> ring_nf
    have hu := ((upper_const ht 1).exponent_mono (by linarith : 0≤2-2*a) ht).add hs2' ht
    have hv := hX.div hBl (Eventually.of_forall fun i => Nat.cast_pos.mpr (hBp i)) ht
    have hv' : Upper atTop t (fun i => ((X i).card:ℝ)/(B i:ℝ)) (2-2*a) := by
      convert hv using 1 <;> first | rfl | ring
    exact (hu.const_mul ht (by norm_num : (0:ℝ)≤43)).add hv' ht
  let loss : ℕ → ℝ := fun i => S i*(((X i).card:ℝ)+2*(X i).card)
  have hlu : Upper atTop t loss (4-a) := by
    have hn := hX.add (hX.const_mul ht (by norm_num : (0:ℝ)≤2)) ht
    have hh := hSu.mul hn (Eventually.of_forall hS0)
      (Eventually.of_forall fun i => by positivity) ht
    convert hh using 1 <;> first | rfl | ring
  have hkeep : Lower atTop t (fun i => K i*incidences (P i) (Q i)) 4 :=
    hE.of_loss hlu (Eventually.of_forall fun i => mul_nonneg (hS0 i) (by positivity)) ht
      (by linarith) (Eventually.of_forall fun i => by
        have hh := hc i
        change incidences (X i) (X i) ≤ loss i+K i*incidences (P i) (Q i) at hh
        linarith)
  have hfinal := hkeep.div hKu (Eventually.of_forall hKp) ht
  have hfinal' : Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a) := by
    have he : (fun i => K i*incidences (P i) (Q i)/K i) =
        (fun i => incidences (P i) (Q i)) := by
      funext i
      exact mul_div_cancel_left₀ _ (hKp i).ne'
    rw [he] at hfinal
    convert hfinal using 1 <;> first | rfl | ring
  exact ⟨P,Q,fun i => ⟨hP i,hQ i⟩,hPu,hQu,hfinal'⟩
end
end PlanarUnitDistances.CuttingAsymptotics

namespace PlanarUnitDistances.CircleIncidence
open Finset CircleCutting
open scoped Classical
noncomputable section

lemma high_degree_card (P Q : Finset Plane) {a : ℝ} (ha : 0 < a) :
    ((Q.filter (fun q => a < degree P q)).card : ℝ) ≤ incidences P Q/a := by
  apply (le_div_iff₀ ha).mpr
  have hh : ((Q.filter (fun q => a < degree P q)).card : ℝ)*a ≤ ∑q ∈ Q.filter (fun q => a < degree P q),degree P q := by
    calc
      _ = ∑q ∈ Q.filter (fun q => a < degree P q),a := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (Finset.mem_filter.mp hq).2.le)
  exact hh.trans (incidences_mono_right P (Finset.filter_subset _ _))

lemma incidence_bound_enlarged (P Q : Finset Plane) {L m n : ℝ}
    (hL : 1 ≤ L) (hlP : cuttingLog P.card ≤ L) (hlQ : cuttingLog Q.card ≤ L)
    (hm : (P.card : ℝ) ≤ m) (hn : (Q.card : ℝ) ≤ n) :
    incidences P Q ≤ 1000*L^2*((m*n)^((2:ℝ)/3)+m+n) := by
  have h0 := (Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)
  have h1 := (Nat.cast_nonneg Q.card : (0:ℝ) ≤ Q.card)
  have hi : incidences P Q ≤ 1000*L^2*(((P.card:ℝ)*Q.card)^((2:ℝ)/3)+P.card+Q.card) := by
    rcases le_total P.card Q.card with h | h
    · exact incidence_bound_oriented P Q h hL hlQ
    · have he := incidence_bound_oriented Q P h hL hlP
      rw [incidences_comm Q P] at he
      convert he using 1; ring_nf
  apply hi.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hp := Real.rpow_le_rpow (mul_nonneg h0 h1)
    (mul_le_mul hm hn h1 (h0.trans hm)) (by norm_num : (0:ℝ) ≤ 2/3)
  linarith

theorem exists_trimmed (P Q : Finset Plane) {a b L : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hL : 1 ≤ L)
    (hlP : cuttingLog P.card ≤ L) (hlQ : cuttingLog Q.card ≤ L) :
    ∃F ⊆ P,∃G ⊆ Q,
      (∀p∈F,degree G p ≤ a) ∧ (∀q∈G,degree F q ≤ b) ∧
      incidences P Q ≤ incidences F G+
        1000*L^2*((incidences P Q/a*(Q.card:ℝ))^((2:ℝ)/3)+incidences P Q/a+Q.card)+
        1000*L^2*(((P.card:ℝ)*(incidences P Q/b))^((2:ℝ)/3)+P.card+incidences P Q/b) := by
  let F := P.filter (fun p => degree Q p ≤ a)
  let G := Q.filter (fun q => degree P q ≤ b)
  let H := P.filter (fun p => a < degree Q p)
  let J := Q.filter (fun q => b < degree P q)
  have hF : F⊆P := Finset.filter_subset _ _
  have hG : G⊆Q := Finset.filter_subset _ _
  have hH : H⊆P := Finset.filter_subset _ _
  have hJ : J⊆Q := Finset.filter_subset _ _
  have hcH : (H.card:ℝ) ≤ incidences P Q/a := by
    simpa only [incidences_comm Q P] using high_degree_card Q P ha
  have hcJ : (J.card:ℝ) ≤ incidences P Q/b := high_degree_card P Q hb
  have hHP : cuttingLog H.card ≤ L := (cuttingLog_mono (Finset.card_le_card hH)).trans hlP
  have hJQ : cuttingLog J.card ≤ L := (cuttingLog_mono (Finset.card_le_card hJ)).trans hlQ
  have heH := incidence_bound_enlarged H Q hL hHP hlQ hcH (le_refl (Q.card:ℝ))
  have heJ := incidence_bound_enlarged P J hL hlP hJQ (le_refl (P.card:ℝ)) hcJ
  have hs1 : incidences P Q=incidences F Q+incidences H Q := by
    simpa only [not_le] using incidences_filter_split P Q (fun p => degree Q p ≤ a)
  have hs2 : incidences F Q=incidences F G+incidences F J := by
    have hh := incidences_filter_split Q F (fun q => degree P q ≤ b)
    have hh' : incidences Q F=incidences G F+incidences J F := by
      simpa only [not_le] using hh
    simpa only [incidences_comm Q F,incidences_comm G F,incidences_comm J F] using hh'
  have hfj := incidences_mono_left hF J
  refine ⟨F,hF,G,hG,?_,?_,?_⟩
  · intro p hp
    exact (degree_mono hG p).trans (Finset.mem_filter.mp hp).2
  · intro q hq
    exact (degree_mono hF q).trans (Finset.mem_filter.mp hq).2
  · linarith
end
end PlanarUnitDistances.CircleIncidence

namespace PlanarUnitDistances.CuttingAsymptotics
open Filter PowerGrowth CircleIncidence CircleCutting
open scoped Classical
noncomputable section

lemma incidence_upper {t : ℕ → ℝ} {X P Q : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i⊆X i) (hQX : ∀i,Q i⊆X i)
    {m n e : ℝ} (hP : Upper atTop t (fun i => ((P i).card:ℝ)) m)
    (hQ : Upper atTop t (fun i => ((Q i).card:ℝ)) n)
    (hm : m≤e) (hn : n≤e) (hmn : (m+n)*(2/3:ℝ)≤e) :
    Upper atTop t (fun i => incidences (P i) (Q i)) e := by
  have hlog := cuttingLog_upper ht hX
  have hLp := hlog.mul hlog
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
  have hL : Upper atTop t (fun i => 1000*(cuttingLog (X i).card)^2) 0 := by
    have hh := hLp.const_mul ht (by norm_num : (0:ℝ)≤1000)
    convert hh using 1 <;> ring_nf
  have hprod := hP.mul hQ (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hmixed := (hprod.rpow (Eventually.of_forall fun i => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ht (by norm_num : (0:ℝ)<2/3)).exponent_mono hmn ht
  have hsum := (hmixed.add (hP.exponent_mono hm ht) ht).add (hQ.exponent_mono hn ht) ht
  have htot := hL.mul hsum (Eventually.of_forall fun i => by positivity)
    (Eventually.of_forall fun i => by positivity) ht
  simp only [zero_add] at htot
  apply htot.mono
  exact Eventually.of_forall fun i => incidence_bound_enlarged (P i) (Q i)
    (cuttingLog_one_le _) (cuttingLog_mono (Finset.card_le_card (hPX i)))
      (cuttingLog_mono (Finset.card_le_card (hQX i))) le_rfl le_rfl

theorem trim_sequence {t : ℕ → ℝ} {X P Q : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1≤t i)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i⊆X i) (hQX : ∀i,Q i⊆X i)
    {a b : ℝ} (_ha : 0<a) (ha1 : a<1) (hb : 0<b) (hba : b<a)
    (hP : Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a))
    (hQ : Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a))
    (hE : Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a)) :
    ∃F G : ℕ → Finset Plane,(∀i,F i⊆P i ∧ G i⊆Q i) ∧
      (∀i,∀p∈F i,degree (G i) p≤(t i)^(1+b)) ∧
      (∀i,∀q∈G i,degree (F i) q≤(t i)^(a+b)) ∧
      Upper atTop t (fun i => ((F i).card:ℝ)) (1+2*a) ∧
      Upper atTop t (fun i => ((G i).card:ℝ)) (2+a) ∧
      Lower atTop t (fun i => incidences (F i) (G i)) (2+2*a) := by
  have ht0 (i : ℕ) : 0<t i := zero_lt_one.trans_le (ht1 i)
  let L : ℕ → ℝ := fun i => cuttingLog (X i).card
  let A : ℕ → ℝ := fun i => (t i)^(1+b)
  let B : ℕ → ℝ := fun i => (t i)^(a+b)
  have hAp (i : ℕ) : 0<A i := Real.rpow_pos_of_pos (ht0 i) _
  have hBp (i : ℕ) : 0<B i := Real.rpow_pos_of_pos (ht0 i) _
  choose F hF G hG hdF hdG he using fun i => exists_trimmed (P i) (Q i)
    (hAp i) (hBp i) (cuttingLog_one_le (X i).card)
    (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
  have hEu : Upper atTop t (fun i => incidences (P i) (Q i)) (2+2*a) :=
    incidence_upper ht hX hPX hQX hP hQ (by linarith) (by linarith) (by ring_nf; rfl)
  have hlog := cuttingLog_upper ht hX
  have hLp := hlog.mul hlog
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _)) ht
  have hLu : Upper atTop t (fun i => 1000*(L i)^2) 0 := by
    dsimp only [L]
    have hh := hLp.const_mul ht (by norm_num : (0:ℝ)≤1000)
    convert hh using 1 <;> ring_nf
  have hEA := hEu.div (lower_rpow ht (1+b)) (Eventually.of_forall hAp) ht
  have hEB := hEu.div (lower_rpow ht (a+b)) (Eventually.of_forall hBp) ht
  have hEA0 : ∀ᶠi in atTop,0≤ incidences (P i) (Q i)/A i :=
    Eventually.of_forall fun i => div_nonneg (incidences_nonneg _ _) (hAp i).le
  have hEB0 : ∀ᶠi in atTop,0≤ incidences (P i) (Q i)/B i :=
    Eventually.of_forall fun i => div_nonneg (incidences_nonneg _ _) (hBp i).le
  have hPA := hEA.mul hQ hEA0 (Eventually.of_forall fun i => Nat.cast_nonneg _) ht
  have hPB := hP.mul hEB (Eventually.of_forall fun i => Nat.cast_nonneg _) hEB0 ht
  have hPA0 : ∀ᶠi in atTop,0≤ incidences (P i) (Q i)/A i*((Q i).card:ℝ) :=
    hEA0.mono fun i hi => mul_nonneg hi (Nat.cast_nonneg _)
  have hPB0 : ∀ᶠi in atTop,0≤((P i).card:ℝ)*(incidences (P i) (Q i)/B i) :=
    hEB0.mono fun i hi => mul_nonneg (Nat.cast_nonneg _) hi
  have hMA := (hPA.rpow hPA0 ht (by norm_num : (0:ℝ)<2/3)).exponent_mono
    (show ((2+2*a-(1+b))+(2+a))*(2/3:ℝ)≤2+2*a-b/2 by linarith) ht
  have hMB := (hPB.rpow hPB0 ht (by norm_num : (0:ℝ)<2/3)).exponent_mono
    (show ((1+2*a)+(2+2*a-(a+b)))*(2/3:ℝ)≤2+2*a-b/2 by linarith) ht
  have hSA := (hMA.add (hEA.exponent_mono (by linarith : 2+2*a-(1+b)≤2+2*a-b/2) ht) ht).add
    (hQ.exponent_mono (by linarith : 2+a≤2+2*a-b/2) ht) ht
  have hSB := (hMB.add (hP.exponent_mono (by linarith : 1+2*a≤2+2*a-b/2) ht) ht).add
    (hEB.exponent_mono (by linarith : 2+2*a-(a+b)≤2+2*a-b/2) ht) ht
  have hA0 : ∀ᶠi in atTop,0≤(incidences (P i) (Q i)/A i*((Q i).card:ℝ))^(2/3:ℝ)+incidences (P i) (Q i)/A i+(Q i).card := by
    filter_upwards [hEA0] with i hi
    positivity
  have hB0 : ∀ᶠi in atTop,0≤(((P i).card:ℝ)*(incidences (P i) (Q i)/B i))^(2/3:ℝ)+(P i).card+incidences (P i) (Q i)/B i := by
    filter_upwards [hEB0] with i hi
    positivity
  have hLA := hLu.mul hSA (Eventually.of_forall fun i => by positivity) hA0 ht
  have hLB := hLu.mul hSB (Eventually.of_forall fun i => by positivity) hB0 ht
  simp only [zero_add] at hLA hLB
  have hloss := hLA.add hLB ht
  have hnon : ∀ᶠi in atTop,0≤1000*(L i)^2*((incidences (P i) (Q i)/A i*((Q i).card:ℝ))^(2/3:ℝ)+incidences (P i) (Q i)/A i+(Q i).card)+
      1000*(L i)^2*((((P i).card:ℝ)*(incidences (P i) (Q i)/B i))^(2/3:ℝ)+(P i).card+incidences (P i) (Q i)/B i) := by
    filter_upwards [hA0,hB0] with i hi hj
    positivity
  refine ⟨F,G,fun i => ⟨hF i,hG i⟩,hdF,hdG,
    hP.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hF i))),
    hQ.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hG i))),?_⟩
  apply hE.of_loss hloss hnon ht (by linarith)
  exact Eventually.of_forall fun i => by simpa only [add_assoc] using he i
end
end PlanarUnitDistances.CuttingAsymptotics

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Regularization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceRegularization
open Finset Real

lemma mass_nonneg {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (s : Finset A) :
    0 ≤ mass μ s := sum_nonneg (fun a _ => hμ a)
lemma mass_mono {A : Type*} (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    {s t : Finset A} (hst : s ⊆ t) : mass μ s ≤ mass μ t :=
  sum_le_sum_of_subset_of_nonneg hst (fun a _ _ => hμ a)

section Optimizer
variable {P Q : Type*} [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q]
variable (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)

omit [DecidableEq P] [DecidableEq Q] in

theorem exists_maximizing {τ γ : ℝ} (hτ : τ ≤ 1)
    (hμ : ∑ p, μ p = 1) (hν : ∑ q, ν q = 1)
    (hw : ∑ p, ∑ q, w p q = 1) :
    ∃ F G, IsMaximizing μ ν w τ γ F G ∧ 1 ≤ objective μ ν w γ F G := by
  classical
  let S : Finset (Finset P × Finset Q) := univ.filter fun x =>
    τ ≤ mass μ x.1 ∧ τ ≤ mass ν x.2
  have hfull : ((univ : Finset P), (univ : Finset Q)) ∈ S := by
    apply mem_filter.mpr
    exact ⟨mem_univ _, by simpa [mass,hμ,hν] using And.intro hτ hτ⟩
  obtain ⟨⟨F,G⟩,hFG,hmax⟩ := S.exists_max_image
    (fun x => objective μ ν w γ x.1 x.2) ⟨_,hfull⟩
  have hfeas := (mem_filter.mp hFG).2
  refine ⟨F,G,⟨hfeas.1,hfeas.2,?_⟩,?_⟩
  · intro A B hA hB
    exact hmax (A,B) (by simp [S,hA,hB])
  · have hh := hmax (univ,univ) hfull
    simpa [objective, mass, rect, hμ, hν, hw] using hh

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in
lemma winner_positive {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hτ : 0 < τ) (hmax : IsMaximizing μ ν w τ γ F G)
    (hwin : 1 ≤ objective μ ν w γ F G) :
    0 < mass μ F ∧ 0 < mass ν G ∧ 0 < rect w F G ∧
      (mass μ F * mass ν G)^γ ≤ rect w F G := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hpow := rpow_pos_of_pos (mul_pos hU hV) γ
  have hW : (mass μ F * mass ν G)^γ ≤ rect w F G := by
    simpa using (le_div_iff₀ hpow).mp hwin
  exact ⟨hU,hV,hpow.trans_le hW,hW⟩

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in

theorem feasible_expansion {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hτ : 0 < τ) (hmax : IsMaximizing μ ν w τ γ F G)
    (hW : 0 < rect w F G) (A : Finset P) (B : Finset Q)
    (hA : τ ≤ mass μ A) (hB : τ ≤ mass ν B) :
    rect w A B / rect w F G ≤
      (mass μ A / mass μ F * (mass ν B / mass ν G))^γ := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hα := hτ.trans_le hA
  have hβ := hτ.trans_le hB
  have hUV := rpow_pos_of_pos (mul_pos hU hV) γ
  have hαβ := rpow_pos_of_pos (mul_pos hα hβ) γ
  have ho := hmax.2.2 A B hA hB
  unfold objective at ho
  have ho' := (div_le_div_iff₀ hαβ hUV).mp ho
  have hid : mass μ A / mass μ F * (mass ν B / mass ν G) =
      (mass μ A * mass ν B)/(mass μ F * mass ν G) := by ring
  rw [hid, div_rpow (mul_pos hα hβ).le (mul_pos hU hV).le]
  exact (div_le_div_iff₀ hW hUV).mpr (by nlinarith)

omit [Fintype P] [Fintype Q] [DecidableEq Q] in

theorem left_atom_bound {τ γ : ℝ} (_hμ : ∀ p, 0 ≤ μ p)
    {F : Finset P} {G : Finset Q} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hmax : IsMaximizing μ ν w τ γ F G) (hW : 0 < rect w F G)
    {p : P} (hp : p ∈ F) (herase : τ ≤ mass μ (F.erase p)) :
    γ * (μ p / mass μ F) ≤ (∑ q ∈ G, w p q) / rect w F G := by
  have hU := hτ.trans_le hmax.1
  have hV := hτ.trans_le hmax.2.1
  have hsum : mass μ (F.erase p) + μ p = mass μ F := by
    exact sum_erase_add _ _ hp
  have hrect : rect w (F.erase p) G + (∑ q ∈ G, w p q) = rect w F G := by
    exact sum_erase_add _ _ hp
  have he := feasible_expansion μ ν w hτ hmax hW (F.erase p) G herase hmax.2.1
  have hratio : mass μ (F.erase p) / mass μ F = 1 - μ p / mass μ F := by
    apply (div_eq_iff hU.ne').mpr
    field_simp
    linarith
  rw [div_self hV.ne', mul_one, hratio] at he
  have hple : μ p ≤ mass μ F := by linarith [mass_nonneg μ _hμ (F.erase p)]
  have hratio1 : μ p / mass μ F ≤ 1 := (div_le_one hU).mpr hple
  have hBern := rpow_one_add_le_one_add_mul_self
    (by linarith : -1 ≤ -(μ p / mass μ F)) hγ hγ1
  have hBern' : (1 - μ p / mass μ F)^γ ≤ 1-γ*(μ p / mass μ F) := by
    convert hBern using 1 <;> first | rfl | ring
  have he' := he.trans hBern'
  have hd : rect w (F.erase p) G / rect w F G +
      (∑ q ∈ G, w p q) / rect w F G = 1 := by
    rw [← add_div, hrect, div_self hW.ne']
  linarith

omit [DecidableEq P] in
lemma mass_le_one (hμ : ∀ p, 0 ≤ μ p) (hs : ∑ p, μ p = 1) (F : Finset P) :
    mass μ F ≤ 1 := by
  simpa [mass,hs] using mass_mono μ hμ (subset_univ F)

omit [Fintype P] [Fintype Q] [DecidableEq P] [DecidableEq Q] in
lemma transpose_maximizing {τ γ : ℝ} {F : Finset P} {G : Finset Q}
    (hm : IsMaximizing μ ν w τ γ F G) :
    IsMaximizing ν μ (fun q p => w p q) τ γ G F := by
  refine ⟨hm.2.1,hm.1,?_⟩
  intro B A hB hA
  have hh := hm.2.2 A B hA hB
  have hrect (A : Finset P) (B : Finset Q) :
      rect (fun q p => w p q) B A = rect w A B := sum_comm
  simpa only [objective, hrect, mul_comm] using hh

omit [Fintype P] [Fintype Q] [DecidableEq P] in
theorem right_atom_bound {τ γ : ℝ} (hν : ∀ q, 0 ≤ ν q)
    {F : Finset P} {G : Finset Q} (hτ : 0 < τ)
    (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hmax : IsMaximizing μ ν w τ γ F G) (hW : 0 < rect w F G)
    {q : Q} (hq : q ∈ G) (herase : τ ≤ mass ν (G.erase q)) :
    γ * (ν q / mass ν G) ≤ (∑ p ∈ F, w p q) / rect w F G := by
  have ht : rect (fun q p => w p q) G F = rect w F G := sum_comm
  have he := left_atom_bound ν μ (fun q p => w p q) hν hτ hγ hγ1
    (transpose_maximizing μ ν w hmax) (by rw [ht]; exact hW) hq herase
  simpa only [ht] using he

end Optimizer

lemma min_le_geometric {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y ≤ sqrt (x*y) := by
  have hh : (min x y)^2 ≤ x*y := by
    rcases le_total x y with h|h
    · rw [min_eq_left h]
      nlinarith [mul_nonneg hx (sub_nonneg.mpr h)]
    · rw [min_eq_right h]
      nlinarith [mul_nonneg hy (sub_nonneg.mpr h)]
  have hs := sq_sqrt (mul_nonneg hx hy)
  have hn := sqrt_nonneg (x*y)
  nlinarith [min_le_left x y, min_le_right x y]

theorem preliminary_square_root {u v a b T w : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (hi : w ≤ T*((u*v)^((2:ℝ)/3)+a*v+b*u))
    (hdP : w ≤ T*u) (hdQ : w ≤ T*v) :
    w ≤ T*sqrt (u*v)*((u*v)^((1:ℝ)/6)+sqrt a+sqrt b) := by
  have hA := rpow_nonneg (mul_nonneg hu hv) ((2:ℝ)/3)
  have hc : w ≤ T*((u*v)^((2:ℝ)/3)+min (a*v) u+min (b*u) v) := by
    by_cases h1 : a*v ≤ u
    · rw [min_eq_left h1]
      by_cases h2 : b*u ≤ v
      · simpa only [min_eq_left h2] using hi
      · rw [min_eq_right (le_of_not_ge h2)]
        exact hdQ.trans (mul_le_mul_of_nonneg_left (by nlinarith) hT)
    · rw [min_eq_right (le_of_not_ge h1)]
      exact hdP.trans (mul_le_mul_of_nonneg_left
        (by linarith [le_min (mul_nonneg hb hu) hv]) hT)
  have hz1 : min (a*v) u ≤ sqrt a * sqrt (u*v) := by
    have := min_le_geometric (mul_nonneg ha hv) hu
    convert this using 1
    rw [← sqrt_mul ha]
    congr 1
    ring
  have hz2 : min (b*u) v ≤ sqrt b * sqrt (u*v) := by
    have := min_le_geometric (mul_nonneg hb hu) hv
    convert this using 1
    rw [← sqrt_mul hb]
    congr 1
    ring
  have hpow : (u*v)^((2:ℝ)/3) = sqrt (u*v)*(u*v)^((1:ℝ)/6) := by
    by_cases hzero : u*v = 0
    · simp [hzero, zero_rpow (by norm_num : (2:ℝ)/3 ≠ 0)]
    · rw [sqrt_eq_rpow, ← rpow_add (lt_of_le_of_ne (mul_nonneg hu hv) (Ne.symm hzero))]
      norm_num
  calc
    w ≤ T*((u*v)^((2:ℝ)/3)+min (a*v) u+min (b*u) v) := hc
    _ ≤ T*((u*v)^((2:ℝ)/3)+sqrt a*sqrt (u*v)+sqrt b*sqrt (u*v)) :=
      mul_le_mul_of_nonneg_left (by linarith) hT
    _ = T*sqrt (u*v)*((u*v)^((1:ℝ)/6)+sqrt a+sqrt b) := by rw [hpow]; ring

lemma renormalized_preliminary {α β U V W T ρ e x : ℝ}
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hU : 0 < U) (hV : 0 < V)
    (hU1 : U ≤ 1) (hV1 : V ≤ 1) (hW : 0 < W)
    (hT : 0 ≤ T) (hρ : 0 ≤ ρ)
    (hp : x ≤ T*sqrt (α*β)*((α*β)^ρ+e)) :
    x/W ≤ (T*sqrt (U*V)/W)*sqrt (α/U*(β/V))*
      ((α/U*(β/V))^ρ+e) := by
  have hUV : 0 < U*V := mul_pos hU hV
  have huv : 0 ≤ α/U*(β/V) := mul_nonneg (div_nonneg hα hU.le) (div_nonneg hβ hV.le)
  have hid : α*β = (U*V)*(α/U*(β/V)) := by field_simp
  have hUV1 : U*V ≤ 1 := by nlinarith [mul_nonneg (sub_nonneg.mpr hU1) (sub_nonneg.mpr hV1)]
  have hle : α*β ≤ α/U*(β/V) := by rw [hid]; nlinarith
  have hr := rpow_le_rpow (mul_nonneg hα hβ) hle hρ
  have hrt : 0 ≤ T*sqrt (α*β) := mul_nonneg hT (sqrt_nonneg _)
  have hb := hp.trans (mul_le_mul_of_nonneg_left (show (α*β)^ρ+e ≤ (α/U*(β/V))^ρ+e by linarith) hrt)
  have hs : sqrt (α*β) = sqrt (U*V)*sqrt (α/U*(β/V)) := by
    rw [hid, sqrt_mul hUV.le]
  apply (div_le_iff₀ hW).mpr
  have heq : (T*sqrt (U*V)/W)*sqrt (α/U*(β/V))*
      ((α/U*(β/V))^ρ+e)*W = T*(sqrt (U*V)*sqrt (α/U*(β/V)))*
      ((α/U*(β/V))^ρ+e) := by field_simp
  rw [heq]
  simpa [hs] using hb

theorem maximizing_expansion {P Q : Type*} [Fintype P] [Fintype Q]
    [DecidableEq P] [DecidableEq Q]
    (μ : P → ℝ) (ν : Q → ℝ) (w : P → Q → ℝ)
    (hμ : ∀ p, 0 ≤ μ p) (hν : ∀ q, 0 ≤ ν q)
    (hμs : ∑ p, μ p = 1) (hνs : ∑ q, ν q = 1)
    {τ η ρ T e : ℝ} (hτ : 0 < τ) (hη : 0 ≤ η) (hρ : 0 ≤ ρ)
    (hT : 0 ≤ T) (he : 0 ≤ e)
    {F : Finset P} {G : Finset Q}
    (hm : IsMaximizing μ ν w τ ((1:ℝ)/2+η) F G)
    (hW : 0 < rect w F G)
    (hpre : ∀ A B, rect w A B ≤
      T*sqrt (mass μ A * mass ν B)*((mass μ A * mass ν B)^ρ+e)) :
    let ξ := (T*sqrt (mass μ F * mass ν G)/rect w F G)*
      ((τ/min (mass μ F) (mass ν G))^ρ+e)
    ∀ A ⊆ F, ∀ B ⊆ G,
      rect w A B/rect w F G ≤
        sqrt (mass μ A/mass μ F*(mass ν B/mass ν G))*
          ((mass μ A/mass μ F*(mass ν B/mass ν G))^η+ξ) := by
  dsimp only
  intro A hAF B hBG
  let U := mass μ F
  let V := mass ν G
  let α := mass μ A
  let β := mass ν B
  let W := rect w F G
  let u := α/U
  let v := β/V
  let C := T*sqrt (U*V)/W
  let ξ := C*((τ/min U V)^ρ+e)
  have hU : 0 < U := hτ.trans_le hm.1
  have hV : 0 < V := hτ.trans_le hm.2.1
  have hU1 : U ≤ 1 := mass_le_one μ hμ hμs F
  have hV1 : V ≤ 1 := mass_le_one ν hν hνs G
  have hα : 0 ≤ α := mass_nonneg μ hμ A
  have hβ : 0 ≤ β := mass_nonneg ν hν B
  have hαU : α ≤ U := mass_mono μ hμ hAF
  have hβV : β ≤ V := mass_mono ν hν hBG
  have hu : 0 ≤ u := div_nonneg hα hU.le
  have hv : 0 ≤ v := div_nonneg hβ hV.le
  have hu1 : u ≤ 1 := (div_le_one hU).mpr hαU
  have hv1 : v ≤ 1 := (div_le_one hV).mpr hβV
  have hC : 0 ≤ C := div_nonneg (mul_nonneg hT (sqrt_nonneg _)) hW.le
  have hmin : 0 < min U V := lt_min hU hV
  have hξ : 0 ≤ ξ := mul_nonneg hC (add_nonneg (rpow_nonneg
    (div_nonneg hτ.le hmin.le) ρ) he)
  have hsplit : (u*v)^((1:ℝ)/2+η) = sqrt (u*v)*(u*v)^η := by
    rw [sqrt_eq_rpow, ← rpow_add' (mul_nonneg hu hv) (by linarith : (1:ℝ)/2+η ≠ 0)]
  change rect w A B/W ≤ sqrt (u*v)*((u*v)^η+ξ)
  by_cases hfeas : τ ≤ α ∧ τ ≤ β
  · have hh := feasible_expansion μ ν w hτ hm hW A B hfeas.1 hfeas.2
    change rect w A B/W ≤ (u*v)^((1:ℝ)/2+η) at hh
    rw [hsplit] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (by linarith) (sqrt_nonneg _))
  · have hsmall : u*v ≤ τ/min U V := by
      by_cases ha : τ ≤ α
      · have hb : β < τ := lt_of_not_ge (fun hb => hfeas ⟨ha,hb⟩)
        have hvτ : v ≤ τ/V := (div_le_div_iff_of_pos_right hV).mpr hb.le
        have hτm : τ/V ≤ τ/min U V := div_le_div_of_nonneg_left hτ.le hmin (min_le_right _ _)
        have huv : u*v ≤ v := by nlinarith
        exact huv.trans (hvτ.trans hτm)
      · have hατ : α < τ := lt_of_not_ge ha
        have huτ : u ≤ τ/U := (div_le_div_iff_of_pos_right hU).mpr hατ.le
        have hτm : τ/U ≤ τ/min U V := div_le_div_of_nonneg_left hτ.le hmin (min_le_left _ _)
        have huv : u*v ≤ u := by nlinarith
        exact huv.trans (huτ.trans hτm)
    have hp := renormalized_preliminary hα hβ hU hV hU1 hV1 hW hT hρ (hpre A B)
    change rect w A B/W ≤ C*sqrt (u*v)*((u*v)^ρ+e) at hp
    have hr := rpow_le_rpow (mul_nonneg hu hv) hsmall hρ
    calc
      rect w A B/W ≤ C*sqrt (u*v)*((u*v)^ρ+e) := hp
      _ ≤ C*sqrt (u*v)*((τ/min U V)^ρ+e) :=
        mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hC (sqrt_nonneg _))
      _ = sqrt (u*v)*ξ := by dsimp [ξ]; ring
      _ ≤ sqrt (u*v)*((u*v)^η+ξ) :=
        mul_le_mul_of_nonneg_left (by linarith [rpow_nonneg (mul_nonneg hu hv) η]) (sqrt_nonneg _)

end PlanarUnitDistances.IncidenceRegularization

namespace PlanarUnitDistances.GeometricExpansion
open CircleIncidence CircleCutting IncidenceRegularization
open scoped Classical
noncomputable section

lemma factor_bounds {m n e L dP dQ t a : ℝ}
    (hm : 0≤ m) (hn : 0≤ n) (he : 0< e) (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t) :
    1≤ factor m n e L dP dQ t a ∧
    1000*L^2*(m*n)^(2/3:ℝ)/e≤ factor m n e L dP dQ t a ∧
    1000*L^2*n*t^a/e≤ factor m n e L dP dQ t a ∧
    1000*L^2*m*t/e≤ factor m n e L dP dQ t a ∧
    dP*m/e≤ factor m n e L dP dQ t a ∧
    dQ*n/e≤ factor m n e L dP dQ t a := by
  have h1 : 0≤ 1000*L^2*(m*n)^(2/3:ℝ)/e := by positivity
  have h2 : 0≤ 1000*L^2*n*t^a/e := by positivity
  have h3 : 0≤ 1000*L^2*m*t/e := by positivity
  have h4 : 0≤ dP*m/e := by positivity
  have h5 : 0≤ dQ*n/e := by positivity
  unfold factor
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

lemma incidence_degree_le (P Q : Finset Plane) {D : ℝ} (hD : ∀p∈P,degree Q p≤ D) :
    incidences P Q≤(P.card:ℝ)*D := by
  rw [incidences_comm]
  unfold incidences
  exact (Finset.sum_le_sum hD).trans_eq (by simp)

theorem preliminary (P Q : Finset Plane) {L dP dQ t a : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ) :
    ∀F⊆P,∀G⊆Q,
      let u := (F.card:ℝ)/(P.card:ℝ)
      let v := (G.card:ℝ)/(Q.card:ℝ)
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      incidences F G/incidences P Q ≤
        T*Real.sqrt (u*v)*((u*v)^(1/6:ℝ)+Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))) := by
  intro F hF G hG
  dsimp only
  let m : ℝ := P.card
  let n : ℝ := Q.card
  let e := incidences P Q
  let u : ℝ := (F.card:ℝ)/m
  let v : ℝ := (G.card:ℝ)/n
  let T := factor m n e L dP dQ t a
  have hm0 : 0≤ m := Nat.cast_nonneg _
  have hn0 : 0≤ n := Nat.cast_nonneg _
  have hmn : 0< m*n := hE.trans_le (incidences_le P Q)
  have hm : 0< m := pos_of_mul_pos_left hmn hn0
  have hn : 0< n := pos_of_mul_pos_right hmn hm0
  have hu : 0≤ u := div_nonneg (Nat.cast_nonneg _) hm0
  have hv : 0≤ v := div_nonneg (Nat.cast_nonneg _) hn0
  have hT := factor_bounds hm0 hn0 hE hdP hdQ ht (a:=a) (L:=L)
  have hcF : (F.card:ℝ)=m*u := by
    dsimp only [u]
    calc
      _ = (F.card:ℝ)*(m/m) := by rw [div_self hm.ne',mul_one]
      _ = m*((F.card:ℝ)/m) := by ring
  have hcG : (G.card:ℝ)=n*v := by
    dsimp only [v]
    calc
      _ = (G.card:ℝ)*(n/n) := by rw [div_self hn.ne',mul_one]
      _ = n*((G.card:ℝ)/n) := by ring
  have hraw := incidence_bound_enlarged F G hL
    ((cuttingLog_mono (Finset.card_le_card hF)).trans hlP)
    ((cuttingLog_mono (Finset.card_le_card hG)).trans hlQ) le_rfl le_rfl
  have hmul : ((F.card:ℝ)*G.card)^(2/3:ℝ)=(m*n)^(2/3:ℝ)*(u*v)^(2/3:ℝ) := by
    rw [hcF,hcG]
    have heq : m*u*(n*v)=(m*n)*(u*v) := by ring
    rw [heq,Real.mul_rpow (mul_nonneg hm0 hn0) (mul_nonneg hu hv)]
  have htcan : t^a*t^(-a)=1 := by rw [←Real.rpow_add ht]; simp
  have htcan1 : t*t^(-1:ℝ)=1 := by rw [Real.rpow_neg_one]; exact mul_inv_cancel₀ ht.ne'
  have hlinQ : 1000*L^2*n/e ≤ T*t^(-a) := by
    have hh := mul_le_mul_of_nonneg_right hT.2.2.1 (Real.rpow_nonneg ht.le (-a))
    have heq : (1000*L^2*n*t^a/e)*t^(-a)=1000*L^2*n/e := by
      calc
        _ = (1000*L^2*n/e)*(t^a*t^(-a)) := by ring
        _ = _ := by rw [htcan,mul_one]
    change _ ≤ T*_ at hh
    rw [show (1000*L^2*n*t^a/incidences P Q)*t^(-a)=1000*L^2*n/e from heq] at hh
    exact hh
  have hlinP : 1000*L^2*m/e ≤ T*t^(-1:ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hT.2.2.2.1 (Real.rpow_nonneg ht.le (-1))
    have heq : (1000*L^2*m*t/e)*t^(-1:ℝ)=1000*L^2*m/e := by
      calc
        _ = (1000*L^2*m/e)*(t*t^(-1:ℝ)) := by ring
        _ = _ := by rw [htcan1,mul_one]
    change _ ≤ T*_ at hh
    rw [show (1000*L^2*m*t/incidences P Q)*t^(-1:ℝ)=1000*L^2*m/e from heq] at hh
    exact hh
  have hinc : incidences F G/e≤ T*((u*v)^(2/3:ℝ)+t^(-a)*v+t^(-1:ℝ)*u) := by
    have hh := div_le_div_of_nonneg_right hraw hE.le
    rw [hmul,hcF,hcG] at hh
    have h0 := mul_le_mul_of_nonneg_right hT.2.1 (Real.rpow_nonneg (mul_nonneg hu hv) (2/3:ℝ))
    have h1 := mul_le_mul_of_nonneg_right hlinQ hv
    have h2 := mul_le_mul_of_nonneg_right hlinP hu
    calc
      _ ≤ 1000*L^2*((m*n)^(2/3:ℝ)*(u*v)^(2/3:ℝ)+m*u+n*v)/e := hh
      _ = (1000*L^2*(m*n)^(2/3:ℝ)/e)*(u*v)^(2/3:ℝ)+
          (1000*L^2*m/e)*u+(1000*L^2*n/e)*v := by ring
      _ ≤ _ := by nlinarith only [h0,h1,h2]
  have heP := incidence_degree_le F G (fun p hp =>
    (degree_mono hG p).trans (hP p (hF hp)))
  have heQ := incidence_degree_le G F (fun q hq =>
    (degree_mono hF q).trans (hQ q (hG hq)))
  have hp : incidences F G/e≤ T*u := by
    have hh := div_le_div_of_nonneg_right heP hE.le
    rw [hcF] at hh
    calc
      _ ≤ m*u*dP/e := hh
      _ = (dP*m/e)*u := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT.2.2.2.2.1 hu
  have hq : incidences F G/e≤ T*v := by
    rw [incidences_comm G F] at heQ
    have hh := div_le_div_of_nonneg_right heQ hE.le
    rw [hcG] at hh
    calc
      _ ≤ n*v*dQ/e := hh
      _ = (dQ*n/e)*v := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hT.2.2.2.2.2 hv
  exact preliminary_square_root hu hv (Real.rpow_nonneg ht.le _) (Real.rpow_nonneg ht.le _)
    (zero_le_one.trans hT.1) hinc hp hq
end
end PlanarUnitDistances.GeometricExpansion

namespace PlanarUnitDistances.GeometricOptimizer
open CircleIncidence CircleCutting IncidenceRegularization GeometricExpansion
open scoped Classical
noncomputable section

lemma lift_subset (P : Finset Plane) (A : Finset P) : lift P A⊆P := by
  intro p hp
  obtain ⟨q,_,rfl⟩ := Finset.mem_map.mp hp
  exact q.property
lemma lift_univ (P : Finset Plane) : lift P Finset.univ=P := by
  ext p
  simp [lift]
lemma lift_subtype (P A : Finset Plane) (hA : A⊆P) : lift P (A.subtype (·∈P))=A := by
  rw [lift,Finset.subtype_map]
  exact Finset.filter_eq_self.mpr (fun p hp => hA hp)
lemma subtype_subset {P A : Finset Plane} {F : Finset P} (h : A⊆lift P F) :
    A.subtype (·∈P)⊆F := by
  intro p hp
  have hh := h (Finset.mem_subtype.mp hp)
  obtain ⟨q,hq,heq⟩ := Finset.mem_map.mp hh
  have hpq : q=p := Subtype.ext heq
  simpa only [hpq] using hq

lemma counting_mass (P : Finset Plane) (A : Finset P) :
    mass (counting P) A=((lift P A).card:ℝ)/(P.card:ℝ) := by
  simp [mass,counting,lift,div_eq_mul_inv]
lemma weight_rect (P Q : Finset Plane) (A : Finset P) (B : Finset Q) :
    rect (weight P Q) A B=incidences (lift P A) (lift Q B)/incidences P Q := by
  unfold rect weight
  simp only [←Finset.sum_div]
  congr 1
  simp only [incidences,degree_sum,lift,Finset.sum_map,Function.Embedding.coe_subtype]
  exact Finset.sum_comm
lemma weight_row (P Q : Finset Plane) (p : P) (B : Finset Q) :
    (∑q∈B,weight P Q p q)=degree (lift Q B) p/incidences P Q := by
  simp only [weight,←Finset.sum_div,degree_sum,lift,Finset.sum_map,Function.Embedding.coe_subtype,dist_comm]

theorem exists_rectangle (P Q : Finset Plane) {L dP dQ t a τ : ℝ}
    (hE : 0< incidences P Q) (hL : 1≤ L)
    (hlP : cuttingLog P.card≤ L) (hlQ : cuttingLog Q.card≤ L)
    (hdP : 0≤ dP) (hdQ : 0≤ dQ) (ht : 0< t)
    (hP : ∀p∈P,degree Q p≤ dP) (hQ : ∀q∈Q,degree P q≤ dQ)
    (hτ : 0< τ) (hτ1 : τ≤ 1) :
    ∃F⊆P,∃G⊆Q,
      let U := (F.card:ℝ)/(P.card:ℝ)
      let V := (G.card:ℝ)/(Q.card:ℝ)
      let W := incidences F G/incidences P Q
      let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
      let e := Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))
      let ξ := (T*Real.sqrt (U*V)/W)*((τ/min U V)^(1/6:ℝ)+e)
      τ≤ U ∧ τ≤ V ∧ 0< W ∧ (U*V)^(27/50:ℝ)≤ W ∧
      (∀A⊆F,∀B⊆G,incidences A B/incidences F G≤
        Real.sqrt ((A.card:ℝ)/F.card*((B.card:ℝ)/G.card))*
          (((A.card:ℝ)/F.card*((B.card:ℝ)/G.card))^(1/25:ℝ)+ξ)) ∧
      (τ≤ U-1/(P.card:ℝ) → ∀p∈F,(27/50:ℝ)/(F.card:ℝ)≤ degree G p/incidences F G) ∧
      (τ≤ V-1/(Q.card:ℝ) → ∀q∈G,(27/50:ℝ)/(G.card:ℝ)≤ degree F q/incidences F G) := by
  have hmn : 0<(P.card:ℝ)*(Q.card:ℝ) := hE.trans_le (incidences_le P Q)
  have hm : 0<(P.card:ℝ) := pos_of_mul_pos_left hmn (Nat.cast_nonneg _)
  have hn : 0<(Q.card:ℝ) := pos_of_mul_pos_right hmn (Nat.cast_nonneg _)
  have hμ : ∀p,0≤ counting P p := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hν : ∀q,0≤ counting Q q := fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hμs : ∑p,counting P p=1 := by
    change mass (counting P) Finset.univ=1
    rw [counting_mass,lift_univ,div_self hm.ne']
  have hνs : ∑q,counting Q q=1 := by
    change mass (counting Q) Finset.univ=1
    rw [counting_mass,lift_univ,div_self hn.ne']
  have hws : ∑p,∑q,weight P Q p q=1 := by
    change rect (weight P Q) Finset.univ Finset.univ=1
    rw [weight_rect,lift_univ,lift_univ,div_self hE.ne']
  obtain ⟨F,G,hmax,hwin⟩ := exists_maximizing (counting P) (counting Q) (weight P Q)
    (γ:=(1/2:ℝ)+1/25) hτ1 hμs hνs hws
  obtain ⟨hU,hV,hW,hpow⟩ := winner_positive (counting P) (counting Q) (weight P Q) hτ hmax hwin
  let T := factor (P.card:ℝ) (Q.card:ℝ) (incidences P Q) L dP dQ t a
  let err := Real.sqrt (t^(-a))+Real.sqrt (t^(-1:ℝ))
  have hT0 : 0≤ T := zero_le_one.trans (factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hE hdP hdQ ht (a:=a) (L:=L)).1
  have hpre (A : Finset P) (B : Finset Q) : rect (weight P Q) A B≤
      T*Real.sqrt (mass (counting P) A*mass (counting Q) B)*
        ((mass (counting P) A*mass (counting Q) B)^(1/6:ℝ)+err) := by
    rw [weight_rect,counting_mass,counting_mass]
    simpa only [T,err,add_assoc] using preliminary (a:=a) P Q hE hL hlP hlQ hdP hdQ ht hP hQ (lift P A) (lift_subset P A)
      (lift Q B) (lift_subset Q B)
  have hexp := maximizing_expansion (counting P) (counting Q) (weight P Q)
    hμ hν hμs hνs hτ (by norm_num : (0:ℝ)≤ 1/25) (by norm_num : (0:ℝ)≤ 1/6)
    hT0 (show 0≤ err by dsimp [err]; positivity) hmax hW hpre
  let FP := lift P F
  let GQ := lift Q G
  have hFP : 0<(FP.card:ℝ) := by
    have hh := hU
    rw [counting_mass] at hh
    exact (div_pos_iff_of_pos_right hm).mp hh
  have hGQ : 0<(GQ.card:ℝ) := by
    have hh := hV
    rw [counting_mass] at hh
    exact (div_pos_iff_of_pos_right hn).mp hh
  have hFG : 0< incidences FP GQ := by
    rw [weight_rect] at hW
    exact (div_pos_iff_of_pos_right hE).mp hW
  refine ⟨FP,lift_subset P F,GQ,lift_subset Q G,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [counting_mass] using hmax.1
  · simpa only [counting_mass] using hmax.2.1
  · simpa only [weight_rect] using hW
  · norm_num only at hpow
    simpa only [counting_mass,weight_rect] using hpow
  · intro A hA B hB
    let As := A.subtype (·∈P)
    let Bs := B.subtype (·∈Q)
    have hAP : A⊆P := hA.trans (lift_subset P F)
    have hBQ : B⊆Q := hB.trans (lift_subset Q G)
    have hAs : lift P As=A := lift_subtype P A hAP
    have hBs : lift Q Bs=B := lift_subtype Q B hBQ
    have hh := hexp As (subtype_subset hA) Bs (subtype_subset hB)
    simp only [counting_mass,weight_rect,hAs,hBs] at hh
    have hnormA : ((A.card:ℝ)/P.card)/((FP.card:ℝ)/P.card)=(A.card:ℝ)/FP.card := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    have hnormB : ((B.card:ℝ)/Q.card)/((GQ.card:ℝ)/Q.card)=(B.card:ℝ)/GQ.card := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    have hnormE : (incidences A B/incidences P Q)/(incidences FP GQ/incidences P Q)=
        incidences A B/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    dsimp only [FP,GQ] at hnormA hnormB hnormE
    simpa only [hnormA,hnormB,hnormE,FP,GQ,T,err] using hh
  · intro he p hp
    obtain ⟨ps,hps,hpseq⟩ := Finset.mem_map.mp hp
    have her : τ≤ mass (counting P) (F.erase ps) := by
      have hh : mass (counting P) (F.erase ps)+counting P ps=mass (counting P) F :=
        Finset.sum_erase_add _ _ hps
      simp only [counting_mass,counting] at hh ⊢
      dsimp only [FP,GQ] at he
      linarith
    have hh := left_atom_bound (counting P) (counting Q) (weight P Q) hμ hτ
      (by norm_num : (0:ℝ)≤ 1/2+1/25) (by norm_num : (1/2:ℝ)+1/25≤ 1) hmax hW hps her
    rw [counting_mass,weight_row,weight_rect] at hh
    norm_num only at hh
    have hca : counting P ps/((FP.card:ℝ)/P.card)=1/(FP.card:ℝ) := by dsimp [counting]; field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne']
    have hce : (degree GQ ps/incidences P Q)/(incidences FP GQ/incidences P Q)=degree GQ ps/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    rw [hca,hce] at hh
    change (ps:Plane)=p at hpseq
    simpa only [hpseq,mul_one_div] using hh
  · intro he q hq
    obtain ⟨qs,hqs,hqseq⟩ := Finset.mem_map.mp hq
    have her : τ≤ mass (counting Q) (G.erase qs) := by
      have hh : mass (counting Q) (G.erase qs)+counting Q qs=mass (counting Q) G :=
        Finset.sum_erase_add _ _ hqs
      simp only [counting_mass,counting] at hh ⊢
      dsimp only [FP,GQ] at he
      linarith
    have hh := right_atom_bound (counting P) (counting Q) (weight P Q) hν hτ
      (by norm_num : (0:ℝ)≤ 1/2+1/25) (by norm_num : (1/2:ℝ)+1/25≤ 1) hmax hW hqs her
    have hcol : (∑p∈F,weight P Q p qs)=degree FP qs/incidences P Q := by
      simp only [weight,←Finset.sum_div,degree_sum,FP,lift,Finset.sum_map,Function.Embedding.coe_subtype]
      congr 1

    rw [counting_mass,hcol,weight_rect] at hh
    norm_num only at hh
    have hca : counting Q qs/((GQ.card:ℝ)/Q.card)=1/(GQ.card:ℝ) := by dsimp [counting]; field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne']
    have hce : (degree FP qs/incidences P Q)/(incidences FP GQ/incidences P Q)=degree FP qs/incidences FP GQ := by field_simp [hm.ne',hn.ne',hFP.ne',hGQ.ne',hE.ne',hFG.ne']
    rw [hca,hce] at hh
    change (qs:Plane)=q at hqseq
    simpa only [hqseq,mul_one_div] using hh
end
end PlanarUnitDistances.GeometricOptimizer

namespace PlanarUnitDistances.IncidenceRegularization
open Real

lemma winning_product {U V W T τ η ρ e : ℝ}
    (hτ : 0 < τ) (hU : τ ≤ U) (hV : τ ≤ V)
    (hT : 0 < T) (hη : 0 ≤ η) (he : 0 ≤ e)
    (hwin : (U*V)^((1:ℝ)/2+η) ≤ W)
    (hpre : W ≤ T*sqrt (U*V)*((U*V)^ρ+e))
    (herr : T*e*(τ^2)^(-η) ≤ 1/2) :
    1/2 ≤ T*(U*V)^(ρ-η) := by
  have hUp := hτ.trans_le hU
  have hVp := hτ.trans_le hV
  have hUV := mul_pos hUp hVp
  have heq : (U*V)^((1:ℝ)/2+η)=sqrt (U*V)*(U*V)^η := by
    rw [Real.rpow_add hUV,Real.sqrt_eq_rpow]
  have hw : (U*V)^η ≤ T*((U*V)^ρ+e) := by
    apply (mul_le_mul_iff_right₀ (Real.sqrt_pos.mpr hUV)).mp
    calc
      _ = (U*V)^((1:ℝ)/2+η) := by simpa only [mul_comm] using heq.symm
      _ ≤ W := hwin
      _ ≤ _ := hpre
      _ = _ := by ring
  have hw' := mul_le_mul_of_nonneg_right hw (Real.rpow_pos_of_pos hUV (-η)).le
  have hone : (U*V)^η*(U*V)^(-η)=1 := by rw [←Real.rpow_add hUV]; simp
  have hp : (U*V)^ρ*(U*V)^(-η)=(U*V)^(ρ-η) := by rw [←Real.rpow_add hUV]; rfl
  rw [hone] at hw'
  have hfeas : τ^2 ≤ U*V := by nlinarith [mul_le_mul hU hV hτ.le hUp.le]
  have hpow : (U*V)^(-η) ≤ (τ^2)^(-η) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hτ) hfeas (by linarith)
  have herr' := (mul_le_mul_of_nonneg_left hpow (mul_nonneg hT.le he)).trans herr
  have hh : T*((U*V)^ρ+e)*(U*V)^(-η)=T*(U*V)^(ρ-η)+T*e*(U*V)^(-η) := by
    rw [mul_add,add_mul,mul_assoc,hp]
  rw [hh] at hw'
  linarith

lemma winning_product_lower {U V W T τ η ρ e : ℝ}
    (hτ : 0 < τ) (hU : τ ≤ U) (hV : τ ≤ V)
    (hT : 0 < T) (hη : 0 ≤ η) (he : 0 ≤ e) (hρη : η < ρ)
    (hwin : (U*V)^((1:ℝ)/2+η) ≤ W)
    (hpre : W ≤ T*sqrt (U*V)*((U*V)^ρ+e))
    (herr : T*e*(τ^2)^(-η) ≤ 1/2) :
    (1/(2*T))^(1/(ρ-η)) ≤ U*V := by
  have hh := winning_product hτ hU hV hT hη he hwin hpre herr
  have hp : 1/(2*T) ≤ (U*V)^(ρ-η) := by
    apply (div_le_iff₀ (by positivity : 0 < 2*T)).mpr
    linarith
  have hUp := hτ.trans_le hU
  have hVp := hτ.trans_le hV
  have hpos : 0 < ρ-η := sub_pos.mpr hρη
  have hr := Real.rpow_le_rpow (by positivity : 0 ≤ 1/(2*T)) hp
    (by positivity : 0 ≤ 1/(ρ-η))
  simpa only [one_div,Real.rpow_rpow_inv (mul_pos hUp hVp).le hpos.ne'] using hr
end PlanarUnitDistances.IncidenceRegularization

namespace PlanarUnitDistances.OptimizerPowers
open Filter PowerGrowth IncidenceRegularization GeometricExpansion
open scoped Classical
noncomputable section

lemma factor_upper {t m n e L : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop) (_ha : 0 < a) (_ha1 : a < 1) (hb : 0 < b)
    (hm : Upper atTop t m (1+2*a)) (hn : Upper atTop t n (2+a))
    (he : Lower atTop t e (2+2*a)) (hL : Upper atTop t L 0)
    (hm0 : ∀ᶠi in atTop,0 ≤ m i) (hn0 : ∀ᶠi in atTop,0 ≤ n i)
    (hL0 : ∀ᶠi in atTop,0 ≤ L i) :
    Upper atTop t (fun i => factor (m i) (n i) (e i) (L i)
      ((t i)^(1+b)) ((t i)^(a+b)) (t i) a) b := by
  have he0 := he.eventually_pos ht
  have ht0 := eventually_base_pos ht
  have hC : Upper atTop t (fun i => 1000*(L i)^2) 0 := by
    have h := (hL.mul hL hL0 hL0 ht).const_mul ht (by norm_num : (0:ℝ) ≤ 1000)
    convert h using 1 <;> ring_nf
  have hC0 : ∀ᶠi in atTop,0 ≤ 1000*(L i)^2 := Eventually.of_forall fun i => by positivity
  have hmn := (hm.mul hn hm0 hn0 ht).rpow (by filter_upwards [hm0,hn0] with i hi hj; positivity)
    ht (by norm_num : (0:ℝ) < 2/3)
  have hmix := (hC.mul hmn hC0 (by filter_upwards [hm0,hn0] with i hi hj; exact Real.rpow_nonneg (mul_nonneg hi hj) _) ht).div he he0 ht
  have h1 : Upper atTop t (fun i => 1000*(L i)^2*(m i*n i)^(2/3:ℝ)/e i) b :=
    hmix.exponent_mono (by linarith) ht
  have hna := hn.mul (upper_rpow ht a) hn0
    (by filter_upwards [ht0] with i hi; positivity) ht
  have h2' := (hC.mul hna hC0 (by filter_upwards [hn0,ht0] with i hi hj; positivity) ht).div he he0 ht
  have h2 : Upper atTop t (fun i => 1000*(L i)^2*n i*(t i)^a/e i) b := by
    have hh := h2'.exponent_mono (show 0+(2+a+a)-(2+2*a) ≤ b by linarith) ht
    convert hh using 1; ring_nf
  have hmt := hm.mul (upper_rpow ht 1) hm0 (by filter_upwards [ht0] with i hi; positivity) ht
  have h3' := (hC.mul hmt hC0 (by filter_upwards [hm0,ht0] with i hi hj; positivity) ht).div he he0 ht
  have h3 : Upper atTop t (fun i => 1000*(L i)^2*m i*t i/e i) b := by
    have hh := h3'.exponent_mono (show 0+(1+2*a+1)-(2+2*a) ≤ b by linarith) ht
    simpa only [Real.rpow_one,mul_assoc] using hh
  have h4' := ((upper_rpow ht (1+b)).mul hm (by filter_upwards [ht0] with i hi; positivity) hm0 ht).div he he0 ht
  have h4 : Upper atTop t (fun i => (t i)^(1+b)*m i/e i) b := by
    convert h4' using 1 <;> first | rfl | ring
  have h5' := ((upper_rpow ht (a+b)).mul hn (by filter_upwards [ht0] with i hi; positivity) hn0 ht).div he he0 ht
  have h5 : Upper atTop t (fun i => (t i)^(a+b)*n i/e i) b := by
    convert h5' using 1 <;> first | rfl | ring
  exact (((((upper_const ht 1).exponent_mono hb.le ht).add h1 ht).add h2 ht).add h3 ht).add h4 ht |>.add h5 ht

theorem winning_powers {t U V W T : ℕ → ℝ} {a b : ℝ}
    (ht : Tendsto t atTop atTop) (_ha : 0 < a) (ha1 : a < 1)
    (hb : 0 < b) (hba : b < a/1000)
    (hT : Upper atTop t T b)
    (hdata : ∀ᶠi in atTop,
      1 ≤ T i ∧ (t i)^(-a/8) ≤ U i ∧ (t i)^(-a/8) ≤ V i ∧
      U i ≤ 1 ∧ V i ≤ 1 ∧ 0 < W i ∧
      (U i*V i)^(27/50:ℝ) ≤ W i ∧
      W i ≤ T i*Real.sqrt (U i*V i)*((U i*V i)^(1/6:ℝ)+
        (Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))))) :
    Lower atTop t (fun i => U i*V i) (-9*b) ∧
    Lower atTop t U (-9*b) ∧ Lower atTop t V (-9*b) ∧
    Lower atTop t W (-5*b) ∧
    Tendsto (fun i => (T i*Real.sqrt (U i*V i)/W i)*
      ((((t i)^(-a/8))/min (U i) (V i))^(1/6:ℝ)+
        (Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))))) atTop (nhds 0) := by
  let err := fun i => Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))
  have ht0 := eventually_base_pos ht
  have herr1 : Upper atTop t (fun i => Real.sqrt ((t i)^(-a))) (-a/2) := by
    have hh := (upper_rpow ht (-a)).rpow (by filter_upwards [ht0] with i hi; positivity) ht
      (by norm_num : (0:ℝ) < 1/2)
    simpa only [Real.sqrt_eq_rpow,div_eq_mul_inv,one_mul] using hh
  have herr2 : Upper atTop t (fun i => Real.sqrt ((t i)^(-1:ℝ))) (-a/2) := by
    have hh := (upper_rpow ht (-1)).rpow (by filter_upwards [ht0] with i hi; positivity) ht
      (by norm_num : (0:ℝ) < 1/2)
    have hh' := hh.exponent_mono (show (-1:ℝ)*(1/2) ≤ -a/2 by linarith) ht
    simpa only [Real.sqrt_eq_rpow] using hh'
  have herr := herr1.add herr2 ht
  have hT0 : ∀ᶠi in atTop,0 ≤ T i := hdata.mono fun i hi => zero_le_one.trans hi.1
  have hTpos : ∀ᶠi in atTop,0 < T i := hdata.mono fun i hi => zero_lt_one.trans_le hi.1
  have herr0 : ∀ᶠi in atTop,0 ≤ err i := Eventually.of_forall fun i => by dsimp [err]; positivity
  have hfloor : Upper atTop t (fun i => (((t i)^(-a/8))^2)^(-(1/25:ℝ))) (a/100) := by
    apply (upper_rpow ht (a/100)).congr
    filter_upwards [ht0] with i hi
    rw [←Real.rpow_natCast,←Real.rpow_mul hi.le,←Real.rpow_mul hi.le]
    congr 1
    ring
  have hfloor0 : ∀ᶠi in atTop,0 ≤ (((t i)^(-a/8))^2)^(-(1/25:ℝ)) :=
    Eventually.of_forall fun i => Real.rpow_nonneg (sq_nonneg _) _
  have hsmall := ((hT.mul herr hT0 herr0 ht).mul hfloor
    (by filter_upwards [hT0,herr0] with i hi hj; positivity) hfloor0 ht).tendsto_zero
      (by filter_upwards [hT0,herr0,hfloor0] with i hi hj hk; positivity) ht
      (show b+(-a/2)+a/100 < 0 by linarith)
  have hevent := hsmall.eventually_le_const (by norm_num : (0:ℝ) < 1/2)
  have hLB := (((lower_const ht (by norm_num : (0:ℝ) < 1/2)).div hT hTpos ht).rpow ht
    (by norm_num : (0:ℝ) < 150/19))
  have hUV : Lower atTop t (fun i => U i*V i) (-9*b) := by
    apply (hLB.exponent_mono (show -9*b ≤ (0-b)*(150/19) by linarith) ht).mono
    filter_upwards [hdata,ht0,hevent] with i hi hti he
    have hh := winning_product_lower (Real.rpow_pos_of_pos hti (-a/8)) hi.2.1 hi.2.2.1
      (zero_lt_one.trans_le hi.1) (by norm_num : (0:ℝ) ≤ 1/25)
      (show 0 ≤ err i by dsimp [err]; positivity) (by norm_num : (1/25:ℝ) < 1/6)
      (by norm_num; exact hi.2.2.2.2.2.2.1) hi.2.2.2.2.2.2.2 he
    norm_num only at hh
    convert hh using 1; ring_nf
  have huv0 : ∀ᶠi in atTop,0 < U i ∧ 0 < V i := by
    filter_upwards [hdata,ht0] with i hi hti
    exact ⟨(Real.rpow_pos_of_pos hti _).trans_le hi.2.1,(Real.rpow_pos_of_pos hti _).trans_le hi.2.2.1⟩
  have hU : Lower atTop t U (-9*b) := hUV.mono (by
    filter_upwards [hdata,huv0] with i hi hj
    exact mul_le_of_le_one_right hj.1.le hi.2.2.2.2.1)
  have hV : Lower atTop t V (-9*b) := hUV.mono (by
    filter_upwards [hdata,huv0] with i hi hj
    exact mul_le_of_le_one_left hj.2.le hi.2.2.2.1)
  have hW : Lower atTop t W (-5*b) := by
    apply ((hUV.rpow ht (by norm_num : (0:ℝ) < 27/50)).exponent_mono
      (show -5*b ≤ -9*b*(27/50) by linarith) ht).mono
    exact hdata.mono fun i hi => hi.2.2.2.2.2.2.1
  have hmin : Lower atTop t (fun i => min (U i) (V i)) (-9*b) := by
    intro ε hε
    filter_upwards [hU ε hε,hV ε hε] with i hi hj
    exact le_min hi hj
  have hmin0 := hmin.eventually_pos ht
  have hquot := (upper_rpow ht (-a/8)).div hmin hmin0 ht
  have hqpow := hquot.rpow (by filter_upwards [ht0,hmin0] with i hi hj; positivity) ht
    (by norm_num : (0:ℝ) < 1/6)
  have hinside : Upper atTop t (fun i => (((t i)^(-a/8))/min (U i) (V i))^(1/6:ℝ)+err i)
      (-a/48+3*b/2) := by
    have hh : Upper atTop t (fun i => (((t i)^(-a/8))/min (U i) (V i))^(1/6:ℝ)) (-a/48+3*b/2) := by
      convert hqpow using 1 <;> first | rfl | ring
    exact hh.add (herr.exponent_mono (by linarith) ht) ht
  have hsqrt : Upper atTop t (fun i => Real.sqrt (U i*V i)) 0 := by
    apply (upper_const ht 1).mono
    filter_upwards [hdata,huv0] with i hi hj
    apply (Real.sqrt_le_one).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hi.2.2.2.1) (sub_nonneg.mpr hi.2.2.2.2.1)]
  have hpref := (hT.mul hsqrt hT0 (Eventually.of_forall fun i => Real.sqrt_nonneg _) ht).div hW (hW.eventually_pos ht) ht
  have hfin := hpref.mul hinside (by filter_upwards [hT0,hW.eventually_pos ht] with i hi hj; positivity)
    (by filter_upwards [ht0,hmin0] with i hi hj; dsimp [err]; positivity) ht
  refine ⟨hUV,hU,hV,hW,?_⟩
  exact hfin.tendsto_zero (by filter_upwards [hT0,hW.eventually_pos ht,ht0,hmin0] with i hi hj hk hl; dsimp [err]; positivity)
    ht (by linarith)
end
end PlanarUnitDistances.OptimizerPowers

namespace PlanarUnitDistances.RegularizedPiece
open Filter PowerGrowth CircleIncidence CircleCutting GeometricExpansion GeometricOptimizer OptimizerPowers
open scoped Classical
noncomputable section

lemma eventually_choose {ι A : Type*} [Nonempty A] {F : Filter ι} {R : ι → A → Prop}
    (h : ∀ᶠi in F,∃x,R i x) : ∃f : ι → A,∀ᶠi in F,R i (f i) := by
  let f : ι → A := fun i => if hi : ∃x,R i x then Classical.choose hi else Classical.choice inferInstance
  refine ⟨f,h.mono ?_⟩
  intro i hi
  simp only [f,dite_eq_left hi]
  exact Classical.choose_spec hi

theorem regularize {t : ℕ → ℝ} {X P Q : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1 ≤ t i)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hPX : ∀i,P i ⊆ X i) (hQX : ∀i,Q i ⊆ X i)
    {a b : ℝ} (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) (hba : b < a/1000)
    (hP : Upper atTop t (fun i => ((P i).card:ℝ)) (1+2*a))
    (hQ : Upper atTop t (fun i => ((Q i).card:ℝ)) (2+a))
    (hE : Lower atTop t (fun i => incidences (P i) (Q i)) (2+2*a))
    (hdP : ∀i,∀p∈P i,degree (Q i) p ≤ (t i)^(1+b))
    (hdQ : ∀i,∀q∈Q i,degree (P i) q ≤ (t i)^(a+b)) :
    ∃F G : ℕ → Finset Plane,∃ξ : ℕ → ℝ,
      Tendsto ξ atTop (nhds 0) ∧
      Upper atTop t (fun i => ((F i).card:ℝ)) (1+2*a) ∧
      Upper atTop t (fun i => ((G i).card:ℝ)) (2+a) ∧
      Lower atTop t (fun i => ((F i).card:ℝ)) (1+2*a-10*b) ∧
      Lower atTop t (fun i => ((G i).card:ℝ)) (2+a-10*b) ∧
      Lower atTop t (fun i => incidences (F i) (G i)) (2+2*a-5*b) ∧
      (∀ᶠi in atTop,F i ⊆ P i ∧ G i ⊆ Q i ∧ 0 ≤ ξ i ∧
        0 < incidences (F i) (G i) ∧
        (∀A⊆F i,∀B⊆G i,incidences A B/incidences (F i) (G i) ≤
          Real.sqrt ((A.card:ℝ)/(F i).card*((B.card:ℝ)/(G i).card))*
            (((A.card:ℝ)/(F i).card*((B.card:ℝ)/(G i).card))^(1/25:ℝ)+ξ i)) ∧
        (∀p∈F i,(27/50:ℝ)/((F i).card:ℝ) ≤ degree (G i) p/incidences (F i) (G i)) ∧
        (∀q∈G i,(27/50:ℝ)/((G i).card:ℝ) ≤ degree (F i) q/incidences (F i) (G i))) := by
  let m : ℕ → ℝ := fun i => (P i).card
  let n : ℕ → ℝ := fun i => (Q i).card
  let e : ℕ → ℝ := fun i => incidences (P i) (Q i)
  let L : ℕ → ℝ := fun i => cuttingLog (X i).card
  let T : ℕ → ℝ := fun i => factor (m i) (n i) (e i) (L i) ((t i)^(1+b)) ((t i)^(a+b)) (t i) a
  let τ : ℕ → ℝ := fun i => (t i)^(-a/8)
  let err : ℕ → ℝ := fun i => Real.sqrt ((t i)^(-a))+Real.sqrt ((t i)^(-1:ℝ))
  have ht0 (i : ℕ) : 0 < t i := zero_lt_one.trans_le (ht1 i)
  have he0 := hE.eventually_pos ht
  have hmp : ∀ᶠi in atTop,0 < m i := by
    filter_upwards [he0] with i hi
    exact pos_of_mul_pos_left (hi.trans_le (incidences_le (P i) (Q i))) (Nat.cast_nonneg _)
  have hnp : ∀ᶠi in atTop,0 < n i := by
    filter_upwards [he0] with i hi
    exact pos_of_mul_pos_right (hi.trans_le (incidences_le (P i) (Q i))) (Nat.cast_nonneg _)
  have hmL : Lower atTop t m (1+2*a-b) := by
    have hh := hE.div (upper_rpow ht (1+b)) (Eventually.of_forall fun i => Real.rpow_pos_of_pos (ht0 i) _) ht
    have hh' := hh.mono (Eventually.of_forall fun i => (div_le_iff₀ (Real.rpow_pos_of_pos (ht0 i) _)).mpr (incidence_degree_le (P i) (Q i) (hdP i)))
    convert hh' using 1 <;> first | rfl | ring
  have hnL : Lower atTop t n (2+a-b) := by
    have hh := hE.div (upper_rpow ht (a+b)) (Eventually.of_forall fun i => Real.rpow_pos_of_pos (ht0 i) _) ht
    have hh' := hh.mono (Eventually.of_forall fun i => (div_le_iff₀ (Real.rpow_pos_of_pos (ht0 i) _)).mpr (by simpa only [incidences_comm] using incidence_degree_le (Q i) (P i) (hdQ i)))
    convert hh' using 1 <;> first | rfl | ring
  have hlog := CuttingAsymptotics.cuttingLog_upper ht hX
  have hTu : Upper atTop t T b := factor_upper ht ha ha1 hb hP hQ hE hlog
    (Eventually.of_forall fun i => Nat.cast_nonneg _) (Eventually.of_forall fun i => Nat.cast_nonneg _)
    (Eventually.of_forall fun i => zero_le_one.trans (cuttingLog_one_le _))
  let R := fun i (fg : Finset Plane×Finset Plane) =>
    fg.1 ⊆ P i ∧ fg.2 ⊆ Q i ∧
    let U := (fg.1.card:ℝ)/m i
    let V := (fg.2.card:ℝ)/n i
    let W := incidences fg.1 fg.2/e i
    let ξ := (T i*Real.sqrt (U*V)/W)*((τ i/min U V)^(1/6:ℝ)+err i)
    τ i ≤ U ∧ τ i ≤ V ∧ 0 < W ∧ (U*V)^(27/50:ℝ) ≤ W ∧
      (∀A⊆fg.1,∀B⊆fg.2,incidences A B/incidences fg.1 fg.2 ≤
        Real.sqrt ((A.card:ℝ)/fg.1.card*((B.card:ℝ)/fg.2.card))*
          (((A.card:ℝ)/fg.1.card*((B.card:ℝ)/fg.2.card))^(1/25:ℝ)+ξ)) ∧
      (τ i ≤ U-1/m i → ∀p∈fg.1,(27/50:ℝ)/(fg.1.card:ℝ) ≤ degree fg.2 p/incidences fg.1 fg.2) ∧
      (τ i ≤ V-1/n i → ∀q∈fg.2,(27/50:ℝ)/(fg.2.card:ℝ) ≤ degree fg.1 q/incidences fg.1 fg.2)
  have hr : ∀ᶠi in atTop,∃fg,R i fg := by
    filter_upwards [he0] with i hi
    obtain ⟨F,hF,G,hG,h⟩ := exists_rectangle (P i) (Q i) hi (cuttingLog_one_le _)
      (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
      (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i) (hdP i) (hdQ i)
      (Real.rpow_pos_of_pos (ht0 i) (-a/8)) (Real.rpow_le_one_of_one_le_of_nonpos (ht1 i) (by linarith : -a/8 ≤ 0))
    exact ⟨(F,G),hF,hG,h⟩
  obtain ⟨fg,hfg⟩ := eventually_choose hr
  let F := fun i => (fg i).1
  let G := fun i => (fg i).2
  let U := fun i => ((F i).card:ℝ)/m i
  let V := fun i => ((G i).card:ℝ)/n i
  let W := fun i => incidences (F i) (G i)/e i
  let ξ := fun i => (T i*Real.sqrt (U i*V i)/W i)*((τ i/min (U i) (V i))^(1/6:ℝ)+err i)
  have hdata : ∀ᶠi in atTop,1 ≤ T i ∧ τ i ≤ U i ∧ τ i ≤ V i ∧ U i ≤ 1 ∧ V i ≤ 1 ∧
      0 < W i ∧ (U i*V i)^(27/50:ℝ) ≤ W i ∧
      W i ≤ T i*Real.sqrt (U i*V i)*((U i*V i)^(1/6:ℝ)+err i) := by
    filter_upwards [hfg,he0,hmp,hnp] with i hi hei hmi hni
    obtain ⟨hF,hG,hU,hV,hW,hpow,_,_,_⟩ := hi
    refine ⟨(factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _) hei
      (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i)).1,hU,hV,?_,?_,hW,hpow,?_⟩
    · exact (div_le_one hmi).mpr (Nat.cast_le.mpr (Finset.card_le_card hF))
    · exact (div_le_one hni).mpr (Nat.cast_le.mpr (Finset.card_le_card hG))
    · simpa only [T,U,V,W,err,m,n,e,L,add_assoc] using preliminary (P i) (Q i) hei (cuttingLog_one_le _)
        (cuttingLog_mono (Finset.card_le_card (hPX i))) (cuttingLog_mono (Finset.card_le_card (hQX i)))
        (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i) (hdP i) (hdQ i) (F i) hF (G i) hG
  obtain ⟨_,hUL,hVL,hWL,hξ⟩ := winning_powers ht ha ha1 hb hba hTu hdata
  have hFL : Lower atTop t (fun i => ((F i).card:ℝ)) (1+2*a-10*b) := by
    have hh := hmL.mul hUL ht
    have heq : (fun i => m i*U i) =ᶠ[atTop] (fun i => ((F i).card:ℝ)) := by
      filter_upwards [hmp] with i hi
      dsimp only [U]
      exact mul_div_cancel₀ _ hi.ne'
    convert hh.congr heq using 1 <;> first | rfl | ring
  have hGL : Lower atTop t (fun i => ((G i).card:ℝ)) (2+a-10*b) := by
    have hh := hnL.mul hVL ht
    have heq : (fun i => n i*V i) =ᶠ[atTop] (fun i => ((G i).card:ℝ)) := by
      filter_upwards [hnp] with i hi
      dsimp only [V]
      exact mul_div_cancel₀ _ hi.ne'
    convert hh.congr heq using 1 <;> first | rfl | ring
  have hEL : Lower atTop t (fun i => incidences (F i) (G i)) (2+2*a-5*b) := by
    have hh := hE.mul hWL ht
    have heq : (fun i => e i*W i) =ᶠ[atTop] (fun i => incidences (F i) (G i)) := by
      filter_upwards [he0] with i hi
      dsimp only [W]
      exact mul_div_cancel₀ _ hi.ne'
    convert hh.congr heq using 1 <;> first | rfl | ring
  have hτU := (upper_rpow ht (-a/8)).ratio_zero hUL (Eventually.of_forall fun i => (Real.rpow_pos_of_pos (ht0 i) _).le) ht (by linarith : -a/8 < -9*b)
  have hτV := (upper_rpow ht (-a/8)).ratio_zero hVL (Eventually.of_forall fun i => (Real.rpow_pos_of_pos (ht0 i) _).le) ht (by linarith : -a/8 < -9*b)
  have hmU := (upper_const ht 1).ratio_zero (hmL.mul hUL ht) (Eventually.of_forall fun _ => zero_le_one) ht (by linarith : 0 < 1+2*a-b+ -9*b)
  have hnV := (upper_const ht 1).ratio_zero (hnL.mul hVL ht) (Eventually.of_forall fun _ => zero_le_one) ht (by linarith : 0 < 2+a-b+ -9*b)
  refine ⟨F,G,ξ,hξ,hP.mono (hfg.mono fun i hi => Nat.cast_le.mpr (Finset.card_le_card hi.1)),
    hQ.mono (hfg.mono fun i hi => Nat.cast_le.mpr (Finset.card_le_card hi.2.1)),hFL,hGL,hEL,?_⟩
  filter_upwards [hfg,he0,hmp,hnp,hUL.eventually_pos ht,hVL.eventually_pos ht,hWL.eventually_pos ht,
    hτU.eventually_le_const (by norm_num : (0:ℝ) < 1/2),hτV.eventually_le_const (by norm_num : (0:ℝ) < 1/2),
    hmU.eventually_le_const (by norm_num : (0:ℝ) < 1/2),hnV.eventually_le_const (by norm_num : (0:ℝ) < 1/2),
    hEL.eventually_pos ht] with i hi hei hmi hni hui hvi hwi htu htv hmu hnv heli
  obtain ⟨hF,hG,_,_,_,_,hexp,hp,hq⟩ := hi
  have hfeasP : τ i ≤ U i-1/m i := by
    have h1 := (div_le_iff₀ hui).mp htu
    have h2 := (div_le_iff₀ (mul_pos hmi hui)).mp hmu
    have h3 : 1/m i ≤ U i/2 := (div_le_iff₀ hmi).mpr (by nlinarith)
    linarith
  have hfeasQ : τ i ≤ V i-1/n i := by
    have h1 := (div_le_iff₀ hvi).mp htv
    have h2 := (div_le_iff₀ (mul_pos hni hvi)).mp hnv
    have h3 : 1/n i ≤ V i/2 := (div_le_iff₀ hni).mpr (by nlinarith)
    linarith
  refine ⟨hF,hG,?_,heli,hexp,hp hfeasP,hq hfeasQ⟩
  dsimp only [ξ,err,τ]
  have hTi : 0 ≤ T i := zero_le_one.trans (factor_bounds (Nat.cast_nonneg _) (Nat.cast_nonneg _) hei
    (Real.rpow_pos_of_pos (ht0 i) _).le (Real.rpow_pos_of_pos (ht0 i) _).le (ht0 i)).1
  have hmin : 0 < min (U i) (V i) := lt_min hui hvi
  exact mul_nonneg (div_nonneg (mul_nonneg hTi (Real.sqrt_nonneg _)) hwi.le)
    (add_nonneg (Real.rpow_nonneg (div_nonneg (Real.rpow_nonneg (ht0 i).le _) hmin.le) _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
end
end PlanarUnitDistances.RegularizedPiece

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Information
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.FiniteInformation
open scoped InnerProductSpace
open Finset Real

lemma hellinger_pointwise {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hac : p ≠ 0 → q ≠ 0) :
    (sqrt p - sqrt q)^2 ≤ p * log (p/q) - p + q := by
  by_cases hpz : p = 0
  · simp [hpz, sq_sqrt hq]
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hpz)
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm (hac hpz))
  have hspp := sqrt_pos.mpr hpp
  have hsqp := sqrt_pos.mpr hqp
  have hsp := sq_sqrt hp
  have hsq := sq_sqrt hq
  have hl := log_le_sub_one_of_pos (div_pos hsqp hspp)
  rw [log_div (ne_of_gt hsqp) (ne_of_gt hspp), log_sqrt hq, log_sqrt hp] at hl
  have hm : p * (sqrt q / sqrt p) = sqrt p * sqrt q := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt hspp)).mpr
    nlinarith
  have hh := mul_le_mul_of_nonneg_left hl (show 0 ≤ 2*p by positivity)
  rw [log_div hpz (hac hpz)]
  nlinarith

theorem hellinger_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) :
    (∑ a, (sqrt (p a) - sqrt (q a))^2) ≤ KL p q := by
  have hh := sum_le_sum (s := univ) (fun a _ => hellinger_pointwise (hp a) (hq a) (hac a))
  simpa only [sum_add_distrib, sum_sub_distrib, hpsum, hqsum, sub_add_cancel, KL] using hh

theorem TV_sq_le_KL {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : (TV p q)^2 ≤ KL p q := by
  have hH := hellinger_le_KL p q hp hq hpsum hqsum hac
  have hs : (∑ a, (sqrt (p a) + sqrt (q a))^2) ≤ 4 := by
    calc
      _ ≤ ∑ a, (2*p a + 2*q a) := by
        apply sum_le_sum
        intro a _
        nlinarith [sq_nonneg (sqrt (p a) - sqrt (q a)), sq_sqrt (hp a), sq_sqrt (hq a)]
      _ = 4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum, hpsum, hqsum]; norm_num
  have hid (a : α) : |p a-q a| =
      |sqrt (p a)-sqrt (q a)| * (sqrt (p a)+sqrt (q a)) := by
    rw [← abs_of_nonneg (show 0 ≤ sqrt (p a)+sqrt (q a) by positivity), ← abs_mul]
    congr 1
    nlinarith [sq_sqrt (hp a), sq_sqrt (hq a)]
  have hcs := sum_mul_sq_le_sq_mul_sq univ
    (fun a => |sqrt (p a)-sqrt (q a)|) (fun a => sqrt (p a)+sqrt (q a))
  simp only [← hid, sq_abs] at hcs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ ∑ a, (sqrt (p a)-sqrt (q a))^2 by positivity)
  unfold TV
  nlinarith

theorem KL_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ a, 0 ≤ q a)
    (hpsum : ∑ a, p a = 1) (hqsum : ∑ a, q a = 1)
    (hac : ∀ a, p a ≠ 0 → q a ≠ 0) : 0 ≤ KL p q :=
  (sq_nonneg _).trans (TV_sq_le_KL p q hp hq hpsum hqsum hac)

universe u

end PlanarUnitDistances.FiniteInformation

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceEntropy
open Finset Real FiniteInformation
variable {P Q : Type*} [Fintype P] [Fintype Q]

lemma atom_le_one {α : Type*} [Fintype α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) (a : α) : p a ≤ 1 := by
  rw [← hs]
  exact single_le_sum (fun x _ => hp x) (mem_univ a)

lemma entropy_le_log_card {α : Type*} [Fintype α] [Nonempty α] (p : α → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hs : ∑ a, p a = 1) :
    entropy p ≤ log (Fintype.card α) := by
  have hc : (0:ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  let q : α → ℝ := fun _ => (Fintype.card α : ℝ)⁻¹
  have hq : ∀ a, 0 ≤ q a := fun _ => inv_nonneg.mpr hc.le
  have hqs : ∑ a, q a = 1 := by simp [q, hc.ne']
  have hqz : ∀ a, q a ≠ 0 := fun _ => inv_ne_zero hc.ne'
  have hh := KL_nonneg p q hp hq hs hqs (fun a _ => hqz a)
  have hid : KL p q = -entropy p + log (Fintype.card α) := by
    unfold KL entropy
    have he (a : α) : p a * log (p a / q a) =
        p a * log (p a) + p a * log (Fintype.card α) := by
      by_cases hz : p a = 0
      · simp [hz]
      · rw [log_div hz (hqz a)]
        simp only [q, log_inv]
        ring
    simp_rw [he]
    rw [sum_add_distrib, ← sum_mul, hs]
    ring
  rw [hid] at hh
  linarith

lemma entropy_off_diagonal_bound [DecidableEq P] (w : P × P → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) {M : ℝ} (_hM : 0 < M)
    (hbound : ∀ p r, p ≠ r → w (p,r) ≤ M) :
    (1 - ∑ p, w (p,p)) * log (1/M) ≤ entropy w := by
  have he (x : P × P) : (if x.1 ≠ x.2 then w x else 0) * log (1/M) ≤
      -(w x * log (w x)) := by
    by_cases hd : x.1 = x.2
    · simp only [hd, ne_eq, not_true_eq_false, ite_false, zero_mul]
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (hw x)
        (log_nonpos (hw x) (atom_le_one w hw hs x)))
    · simp only [hd, ne_eq, not_false_eq_true, ite_true]
      by_cases hz : w x = 0
      · simp [hz]
      have hwp : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hz)
      have hl := log_le_log hwp (hbound x.1 x.2 hd)
      rw [one_div, log_inv]
      nlinarith [mul_le_mul_of_nonneg_left hl (hw x)]
  have hh := sum_le_sum (s := univ) (fun x _ => he x)
  rw [← sum_mul, sum_neg_distrib] at hh
  change (∑ x, if x.1 ≠ x.2 then w x else 0) * log (1/M) ≤ entropy w at hh
  have hsplit : (∑ x, if x.1 ≠ x.2 then w x else 0) = 1 - ∑ p, w (p,p) := by
    have he' (x : P × P) : (if x.1 ≠ x.2 then w x else 0) =
        w x - if x.1 = x.2 then w x else 0 := by split_ifs <;> simp_all
    simp_rw [he']
    rw [sum_sub_distrib, hs, Fintype.sum_prod_type]
    simp
  rwa [hsplit] at hh

lemma joint_KL_entropy (w : P × Q → ℝ) (hw : ∀ x, 0 ≤ w x) :
    KL w (fun x => (∑ q, w (x.1,q)) * (∑ p, w (p,x.2))) =
      entropy (fun p => ∑ q, w (p,q)) + entropy (fun q => ∑ p, w (p,q))
        - entropy w := by
  let a : P → ℝ := fun p => ∑ q, w (p,q)
  let b : Q → ℝ := fun q => ∑ p, w (p,q)
  have ha (x : P × Q) (hx : w x ≠ 0) : a x.1 ≠ 0 := by
    have hh := single_le_sum (s := univ) (f := fun q => w (x.1,q))
      (fun q _ => hw _) (mem_univ x.2)
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hw x) (Ne.symm hx)) hh)
  have hb (x : P × Q) (hx : w x ≠ 0) : b x.2 ≠ 0 := by
    have hh := single_le_sum (s := univ) (f := fun p => w (p,x.2))
      (fun p _ => hw _) (mem_univ x.1)
    exact ne_of_gt (lt_of_lt_of_le (lt_of_le_of_ne (hw x) (Ne.symm hx)) hh)
  have he (x : P × Q) : w x * log (w x / (a x.1*b x.2)) =
      w x * log (w x) - w x * log (a x.1) - w x * log (b x.2) := by
    by_cases hz : w x = 0
    · simp [hz]
    · rw [log_div hz (mul_ne_zero (ha x hz) (hb x hz)), log_mul (ha x hz) (hb x hz)]
      ring
  change (∑ x, w x * log (w x / (a x.1*b x.2))) = _
  simp_rw [he]
  rw [sum_sub_distrib, sum_sub_distrib]
  have h₁ : (∑ x : P × Q, w x * log (a x.1)) = ∑ p, a p * log (a p) := by
    rw [Fintype.sum_prod_type]
    simp_rw [← sum_mul]
    rfl
  have h₂ : (∑ x : P × Q, w x * log (b x.2)) = ∑ q, b q * log (b q) := by
    rw [Fintype.sum_prod_type, sum_comm]
    simp_rw [← sum_mul]
    rfl
  rw [h₁,h₂]
  dsimp [entropy, a, b]
  ring

theorem mutual_information_bound [DecidableEq P] [Nonempty P]
    (w : P × P → ℝ) (μ : P → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (hμ : ∀ p, 0 ≤ μ p) (hμs : ∑ p, μ p = 1)
    (hfst : ∀ p, ∑ r, w (p,r) = μ p) (hsnd : ∀ r, ∑ p, w (p,r) = μ r)
    {M : ℝ} (hM : 0 < M) (hbound : ∀ p r, p ≠ r → w (p,r) ≤ M) :
    KL w (fun x => μ x.1*μ x.2) ≤
      2*log (Fintype.card P) - (1-∑ p, w (p,p))*log (1/M) := by
  have h₁ := entropy_le_log_card μ hμ hμs
  have h₂ := entropy_off_diagonal_bound w hw hs hM hbound
  have hid := joint_KL_entropy w hw
  simp only [hfst, hsnd] at hid
  rw [hid]
  linarith

omit [Fintype Q] in
lemma degree_nonneg (E : P → Q → Prop) (q : Q) : 0 ≤ degree E q :=
  sum_nonneg fun p _ => indicator_nonneg E p q

lemma edgeCount_nonneg (E : P → Q → Prop) : 0 ≤ edgeCount E :=
  sum_nonneg fun q _ => degree_nonneg E q

lemma wedge_nonneg (E : P → Q → Prop) (x : P × P) : 0 ≤ wedge E x := by
  unfold wedge
  exact sum_nonneg fun q _ => div_nonneg
    (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
    (mul_nonneg (edgeCount_nonneg E) (degree_nonneg E _))

lemma wedge_symm (E : P → Q → Prop) (p r : P) : wedge E (p,r) = wedge E (r,p) := by
  unfold wedge
  apply sum_congr rfl
  intro q _
  exact congrArg (fun a => a / (edgeCount E * degree E q)) (mul_comm _ _)

lemma pointLaw_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) : ∑ p, pointLaw E p = 1 := by
  unfold pointLaw
  rw [← sum_div, sum_comm]
  exact div_self hE

lemma wedge_fst (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (p : P) :
    ∑ r, wedge E (p,r) = pointLaw E p := by
  unfold wedge pointLaw
  rw [sum_comm, sum_div]
  apply sum_congr rfl
  intro q _
  dsimp only
  rw [← sum_div, ← mul_sum]
  change indicator E p q * degree E q / (edgeCount E * degree E q) = _
  exact mul_div_mul_right _ _ (hd q)

lemma wedge_snd (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) (r : P) :
    ∑ p, wedge E (p,r) = pointLaw E r := by
  simp_rw [wedge_symm E _ r]
  exact wedge_fst E hd r

lemma wedge_sum (E : P → Q → Prop) (hE : edgeCount E ≠ 0) (hd : ∀ q, degree E q ≠ 0) :
    ∑ x, wedge E x = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [wedge_fst E hd]
  exact pointLaw_sum E hE

theorem wedge_diagonal (E : P → Q → Prop) (hd : ∀ q, degree E q ≠ 0) :
    ∑ p, wedge E (p,p) = Fintype.card Q / edgeCount E := by
  classical
  unfold wedge
  rw [sum_comm]
  have he (q : Q) : (∑ p, indicator E p q * indicator E p q / (edgeCount E * degree E q)) =
      1 / edgeCount E := by
    have hi (p : P) : indicator E p q * indicator E p q = indicator E p q := by
      unfold indicator
      split_ifs <;> norm_num
    simp_rw [hi]
    rw [← sum_div]
    change degree E q / (edgeCount E * degree E q) = _
    simpa using mul_div_mul_right (1:ℝ) (edgeCount E) (hd q)
  simp_rw [he]
  simp [div_eq_mul_inv]

theorem wedge_atom (E : P → Q → Prop) {dmin : ℝ}
    (hE : 0 < edgeCount E) (hd : 0 < dmin) (hdeg : ∀ q, dmin ≤ degree E q)
    (hcodeg : ∀ p r, p ≠ r → (∑ q, indicator E p q * indicator E r q) ≤ 2)
    (p r : P) (hpr : p ≠ r) : wedge E (p,r) ≤ 2/(edgeCount E*dmin) := by
  unfold wedge
  calc
    _ ≤ ∑ q, indicator E p q * indicator E r q / (edgeCount E*dmin) := by
      apply sum_le_sum
      intro q _
      exact div_le_div_of_nonneg_left
        (mul_nonneg (indicator_nonneg E _ _) (indicator_nonneg E _ _))
        (mul_pos hE hd) (mul_le_mul_of_nonneg_left (hdeg q) hE.le)
    _ = (∑ q, indicator E p q * indicator E r q) / (edgeCount E*dmin) := by rw [sum_div]
    _ ≤ 2/(edgeCount E*dmin) := div_le_div_of_nonneg_right (hcodeg p r hpr) (by positivity)

theorem wedge_information [DecidableEq P] [Nonempty P]
    (E : P → Q → Prop) {dmin : ℝ} (hE : 0 < edgeCount E)
    (hd : 0 < dmin) (hdeg : ∀ q, dmin ≤ degree E q)
    (hcodeg : ∀ p r, p ≠ r → (∑ q, indicator E p q * indicator E r q) ≤ 2) :
    KL (wedge E) (fun x => pointLaw E x.1 * pointLaw E x.2) ≤
      2*log (Fintype.card P) - (1-Fintype.card Q/edgeCount E)*log (edgeCount E*dmin/2) := by
  have hdn : ∀ q, degree E q ≠ 0 := fun q => (lt_of_lt_of_le hd (hdeg q)).ne'
  have hh := mutual_information_bound (wedge E) (pointLaw E)
    (wedge_nonneg E) (wedge_sum E hE.ne' hdn)
    (fun p => div_nonneg (sum_nonneg fun q _ => indicator_nonneg E p q) hE.le)
    (pointLaw_sum E hE.ne') (wedge_fst E hdn) (wedge_snd E hdn)
    (show 0 < 2/(edgeCount E*dmin) by positivity) (wedge_atom E hE hd hdeg hcodeg)
  rw [wedge_diagonal E hdn] at hh
  convert hh using 1
  congr 2
  field_simp

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.UnitCodegree
open Polynomial Complex
open scoped ComplexConjugate

lemma center_linear (p r q : ℂ)
    (hp : (q-p)*(conj q-conj p) = 1)
    (hr : (q-r)*(conj q-conj r) = 1) :
    (p-r)*conj q + (conj p-conj r)*q = p*conj p-r*conj r := by
  linear_combination hr-hp

lemma centerPolynomial_eval (p r q : ℂ)
    (hp : (q-p)*(conj q-conj p) = 1)
    (hr : (q-r)*(conj q-conj r) = 1) :
    (centerPolynomial p r).eval q = 0 := by
  have hl := center_linear p r q hp hr
  simp only [centerPolynomial, eval_sub, eval_mul, eval_X, eval_C]
  linear_combination -(q-p)*hl+(p-r)*hp

lemma centerPolynomial_expansion (p r : ℂ) :
    centerPolynomial p r = C (-(conj p-conj r))*X^2+
      C (p*conj p-r*conj r-(p-r)*conj p+p*(conj p-conj r))*X+
      C (-(p*(p*conj p-r*conj r-(p-r)*conj p))-(p-r)) := by
  simp only [centerPolynomial, map_add, map_sub, map_neg, map_mul]
  ring

lemma centerPolynomial_ne_zero (p r : ℂ) (hpr : p ≠ r) : centerPolynomial p r ≠ 0 := by
  intro hz
  have hh := congrArg (fun f : ℂ[X] => f.coeff 2) hz
  rw [centerPolynomial_expansion] at hh
  norm_num only [coeff_add, coeff_C_mul_X_pow, coeff_mul_X, coeff_C] at hh
  simp only [ite_true, ite_false, add_zero, coeff_zero] at hh
  exact hpr (star_injective (sub_eq_zero.mp (neg_eq_zero.mp hh)))

lemma centerPolynomial_degree (p r : ℂ) : (centerPolynomial p r).natDegree ≤ 2 := by
  rw [centerPolynomial_expansion]
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply (natDegree_add_le _ _).trans
    apply max_le
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X_pow]; norm_num)
    · exact natDegree_mul_le.trans (by simp only [natDegree_C, natDegree_X]; norm_num)
  · simp only [natDegree_C]; norm_num

theorem common_centers_card (p r : ℂ) (hpr : p ≠ r) (S : Finset ℂ)
    (hS : ∀ q ∈ S, (q-p)*(conj q-conj p) = 1 ∧ (q-r)*(conj q-conj r) = 1) :
    S.card ≤ 2 := by
  have hh : S.card ≤ (centerPolynomial p r).natDegree :=
    Polynomial.card_le_degree_of_subset_roots ?_
  · exact hh.trans (centerPolynomial_degree p r)
  · intro q hq
    exact (Polynomial.mem_roots (centerPolynomial_ne_zero p r hpr)).mpr
      (centerPolynomial_eval p r q (hS q hq).1 (hS q hq).2)

lemma unit_distance_equation (p q : ℂ) (h : dist p q = 1) :
    (q-p)*(conj q-conj p) = 1 := by
  rw [← map_sub, mul_conj, normSq_eq_norm_sq, ← dist_eq_norm, dist_comm q p, h]
  norm_num

theorem unit_centers_card (p r : ℂ) (hpr : p ≠ r) (S : Finset ℂ)
    (hS : ∀ q ∈ S, dist p q = 1 ∧ dist r q = 1) : S.card ≤ 2 :=
  common_centers_card p r hpr S fun q hq =>
    ⟨unit_distance_equation p q (hS q hq).1, unit_distance_equation r q (hS q hq).2⟩

end PlanarUnitDistances.UnitCodegree

namespace PlanarUnitDistances.IncidenceEntropy
open Finset UnitCodegree
variable {P Q : Type*} [Fintype P] [Fintype Q]

omit [Fintype P] in

theorem unit_incidence_codegree (E : P → Q → Prop) (x : P → ℂ) (y : Q → ℂ)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hE : ∀ p q, E p q → dist (x p) (y q) = 1)
    (p r : P) (hpr : p ≠ r) : (∑ q, indicator E p q * indicator E r q) ≤ 2 := by
  classical
  let T : Finset Q := univ.filter fun q => E p q ∧ E r q
  have hs : (∑ q, indicator E p q * indicator E r q) = (T.card : ℝ) := by
    have hh (q : Q) : indicator E p q * indicator E r q =
        if E p q ∧ E r q then (1:ℝ) else 0 := by
      unfold indicator
      split_ifs <;> simp_all
    simp_rw [hh]
    simp [T]
  rw [hs]
  have hc := unit_centers_card (x p) (x r) (fun hh => hpr (hx hh)) (T.image y) ?_
  · rw [Finset.card_image_of_injective _ hy] at hc
    exact_mod_cast hc
  · intro q hq
    obtain ⟨s,hs,hsy⟩ := mem_image.mp hq
    have hss := (mem_filter.mp hs).2
    subst q
    exact ⟨hE p s hss.1,hE r s hss.2⟩

theorem planar_wedge_information [DecidableEq P] [Nonempty P]
    (E : P → Q → Prop) (x : P → EuclideanSpace ℝ (Fin 2))
    (y : Q → EuclideanSpace ℝ (Fin 2))
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hunit : ∀ p q, E p q → dist (x p) (y q) = 1)
    {dmin : ℝ} (hE : 0 < edgeCount E) (hd : 0 < dmin)
    (hdeg : ∀ q, dmin ≤ degree E q) :
    FiniteInformation.KL (wedge E) (fun t => pointLaw E t.1 * pointLaw E t.2) ≤
      2*Real.log (Fintype.card P) -
        (1-Fintype.card Q/edgeCount E)*Real.log (edgeCount E*dmin/2) := by
  apply wedge_information E hE hd hdeg
  apply unit_incidence_codegree E (fun p => zCoordinate (x p)) (fun q => zCoordinate (y q))
    (zCoordinate.injective.comp hx) (zCoordinate.injective.comp hy)
  intro p q hpq
  rw [LinearIsometryEquiv.dist_map]
  exact hunit p q hpq

end PlanarUnitDistances.IncidenceEntropy

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f : ι → ℝ} {a : ℝ}
lemma Upper.log_ratio (hf : Upper F t f a) (hfp : ∀ᶠi in F,0<f i)
    (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠi in F,Real.log (f i)/Real.log (t i)≤a+ε := by
  filter_upwards [hf ε hε,hfp,ht.eventually_gt_atTop 1] with i hi hfi hti
  apply (div_le_iff₀ (Real.log_pos hti)).mpr
  have hh := Real.log_le_log hfi hi
  simpa only [Real.log_rpow (zero_lt_one.trans hti)] using hh
lemma Lower.log_ratio (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {ε : ℝ} (hε : 0<ε) : ∀ᶠi in F,a-ε≤Real.log (f i)/Real.log (t i) := by
  filter_upwards [hf ε hε,ht.eventually_gt_atTop 1] with i hi hti
  apply (le_div_iff₀ (Real.log_pos hti)).mpr
  have hh := Real.log_le_log (Real.rpow_pos_of_pos (zero_lt_one.trans hti) _) hi
  simpa only [Real.log_rpow (zero_lt_one.trans hti)] using hh
end PlanarUnitDistances.PowerGrowth

namespace PlanarUnitDistances.InformationPowers
open Filter PowerGrowth

theorem information_rate {t m n e D : ℕ → ℝ} {M N E γ : ℝ}
    (ht : Tendsto t atTop atTop) (hγ : 0<γ)
    (hm : Upper atTop t m M) (hn : Upper atTop t n N) (he : Lower atTop t e E)
    (hm0 : ∀ᶠi : ℕ in atTop,(0:ℝ) < m i) (hn0 : ∀ᶠi : ℕ in atTop,(0:ℝ) < n i)
    (hNE : N<E) (hV : 0<2*E-N)
    (hD : ∀ᶠi in atTop,D i≤2*Real.log (m i)-
      (1-n i/e i)*Real.log (e i*(γ*e i/n i)/2)) :
    ∀ε : ℝ,0<ε → ∀ᶠi in atTop,D i/Real.log (t i)≤2*M-2*E+N+ε := by
  let V := 2*E-N
  have he0 := he.eventually_pos ht
  have hr := hn.ratio_zero he (hn0.mono fun _ hi => hi.le) ht hNE
  have hprod : Lower atTop t (fun i => e i*(γ*e i/n i)/2) V := by
    have hh := (he.mul (he.div hn hn0 ht) ht).const_mul ht (show 0<γ/2 by positivity)
    change Lower atTop t _ (2*E-N)
    convert hh using 1
    · ext i; ring
    · ring
  intro ε hε
  let δ := min (ε/4) (V/2)
  have hδ : 0<δ := lt_min (by positivity) (by dsimp [V]; positivity)
  have hδV : δ≤V/2 := min_le_right _ _
  have hδε : δ≤ε/4 := min_le_left _ _
  have hrv : 0<ε/(4*V) := by dsimp [V]; positivity
  filter_upwards [hD,hm.log_ratio hm0 ht (show 0<ε/8 by positivity),hprod.log_ratio ht hδ,
    hr.eventually_le_const (by norm_num : (0:ℝ)<1/2),hr.eventually_le_const hrv,hn0,he0,
    ht.eventually_gt_atTop 1] with i hDi hMi hVi hr1 hrε hni hei hti
  have hl : 0<Real.log (t i) := Real.log_pos hti
  have hr0 : 0≤n i/e i := div_nonneg hni.le hei.le
  have hrV : n i/e i*V≤ε/4 := by
    have hh := (le_div_iff₀ (show 0<4*V by positivity)).mp hrε
    nlinarith
  have hmult := mul_le_mul_of_nonneg_left hVi (show 0≤1-n i/e i by linarith)
  have hdivide := (div_le_div_of_nonneg_right hDi hl.le)
  rw [sub_div,mul_div_assoc,mul_div_assoc] at hdivide
  have hout : D i/Real.log (t i)≤2*M-V+ε := by
    nlinarith [mul_nonneg hr0 hδ.le]
  dsimp only [V] at hout
  convert hout using 1 <;> first | rfl | ring
end PlanarUnitDistances.InformationPowers

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f : ι → ℝ} {a b : ℝ}
lemma Upper.power_bound (hf : Upper F t f a) (hab : a < b) :
    ∀ᶠi in F,f i ≤ t i^b := by
  convert hf (b-a) (sub_pos.mpr hab) using 1; ring_nf
lemma Lower.power_bound (hf : Lower F t f a) (hab : b < a) :
    ∀ᶠi in F,t i^b ≤ f i := by
  simpa only [sub_sub_cancel] using hf (a-b) (sub_pos.mpr hab)
lemma Lower.tends_to_infinity (hf : Lower F t f a) (ht : Tendsto t F atTop) (ha : 0 < a) :
    Tendsto f F atTop := by
  exact tendsto_atTop_mono' F (hf.power_bound (by linarith : a/2 < a))
    ((_root_.tendsto_rpow_atTop (by positivity : 0 < a/2)).comp ht)
end PlanarUnitDistances.PowerGrowth

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Sequence
attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceSequence
open Filter PowerGrowth CircleIncidence
open scoped Classical
noncomputable section

lemma information_bound (P Q : Finset Plane) (he : 0 < incidences P Q)
    {d : ℝ} (hd : 0 < d) (hdeg : ∀q∈Q,d ≤ degree P q) :
    information P Q  ≤  2*Real.log (P.card:ℝ)-(1-(Q.card:ℝ)/incidences P Q)*
      Real.log (incidences P Q*d/2) := by
  have : Nonempty P := (Finset.card_pos.mp (GeometricLaw.card_pos P Q he).1).to_subtype
  have hge : 0 < IncidenceEntropy.edgeCount (GeometricLaw.E P Q) := by
    rw [GeometricLaw.edgeCount_eq]; exact he
  have hh := IncidenceEntropy.planar_wedge_information (GeometricLaw.E P Q)
    (fun p => (p:Plane)) (fun q => (q:Plane)) Subtype.val_injective Subtype.val_injective
    (fun _ _ h => h) hge hd (fun q => by rw [GeometricLaw.degree_eq]; exact hdeg q q.property)
  simpa only [information,Fintype.card_coe,GeometricLaw.edgeCount_eq] using hh

theorem fixed_accuracy {t : ℕ → ℝ} {X : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1 ≤ t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hE : Lower atTop t (fun i => incidences (X i) (X i)) 4)
    (hAlg : ∀i,∀p∈X i,∀k,IsAlgebraic ℚ (p k))
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (R : ℝ) :
    ∃P Q : ℕ → Finset Plane,∃ξ : ℕ → ℝ,
      ∀ᶠi in atTop,Good (t i) δ R (P i) (Q i) (ξ i) := by
  let a := δ/100
  let b := a/2000
  have ha : 0 < a := by dsimp [a]; positivity
  have ha1 : a < 1 := by dsimp [a]; linarith
  have hb : 0 < b := by dsimp [b]; positivity
  have hba : b < a/1000 := by dsimp [b]; linarith
  obtain ⟨P,Q,hPQ,hP,hQ,hE'⟩ := CuttingAsymptotics.exists_cut_sequence X ht ht1 hX0 hX hE ha ha1
  obtain ⟨F,G,hFG,hdF,hdG,hF,hG,hFG'⟩ := CuttingAsymptotics.trim_sequence ht ht1 hX
    (fun i => (hPQ i).1) (fun i => (hPQ i).2) ha ha1 hb (by linarith) hP hQ hE'
  obtain ⟨A,B,ξ,hξ,hA,hB,_,_,hAB,hd⟩ := RegularizedPiece.regularize ht ht1 hX
    (fun i => ((hFG i).1).trans (hPQ i).1) (fun i => ((hFG i).2).trans (hPQ i).2)
    ha ha1 hb hba hF hG hFG' hdF hdG
  let e := fun i => incidences (A i) (B i)
  let m := fun i => ((A i).card:ℝ)
  let n := fun i => ((B i).card:ℝ)
  have he0 := hAB.eventually_pos ht
  have hm0 : ∀ᶠi in atTop,(0:ℝ)  <  m i := by
    filter_upwards [he0] with i hi
    change (0:ℝ) < ((A i).card:ℝ)
    exact_mod_cast (GeometricLaw.card_pos (A i) (B i) hi).1
  have hn0 : ∀ᶠi in atTop,(0:ℝ)  <  n i := by
    filter_upwards [he0] with i hi
    change (0:ℝ) < ((B i).card:ℝ)
    exact_mod_cast (GeometricLaw.card_pos (A i) (B i) hi).2
  have hdp : Lower atTop t (fun i => (27/50:ℝ)*e i/m i) (1-5*b) := by
    have h := (hAB.div hA hm0 ht).const_mul ht (by norm_num : (0:ℝ) < 27/50)
    convert h using 1
    · ext i; dsimp only [e,m]; ring
    · ring
  have hdq : Lower atTop t (fun i => (27/50:ℝ)*e i/n i) (a-5*b) := by
    have h := (hAB.div hB hn0 ht).const_mul ht (by norm_num : (0:ℝ) < 27/50)
    convert h using 1
    · ext i; dsimp only [e,n]; ring
    · ring
  have hpup : Upper atTop t (fun i => (t i)^(1+b)/e i) (-1-2*a+6*b) := by
    have h := (upper_rpow ht (1+b)).div hAB he0 ht
    convert h using 1 <;> first | rfl | ring
  have hprod : Lower atTop t (fun i => e i*((27/50:ℝ)*e i/n i)/2) (2+3*a-10*b) := by
    have h := (hAB.mul hdq ht).const_mul ht (by norm_num : (0:ℝ) < 1/2)
    convert h using 1
    · ext i; dsimp only [e]; ring
    · ring
  have hinfo := InformationPowers.information_rate (D := fun i => information (A i) (B i)) ht (by norm_num : (0:ℝ) < 27/50)
    hA hB hAB hm0 hn0 (by dsimp [b] at *; linarith : 2+a < 2+2*a-5*b)
    (by dsimp [b] at *; linarith : 0 < 2*(2+2*a-5*b)-(2+a))
  have hinfo' : ∀ᶠi in atTop,information (A i) (B i)/Real.log (t i) ≤ δ := by
    have hbound : ∀ᶠi in atTop,information (A i) (B i) ≤ 2*Real.log (m i)-
        (1-n i/e i)*Real.log (e i*((27/50:ℝ)*e i/n i)/2) := by
      filter_upwards [hd,he0,hn0] with i hi hei hni
      apply information_bound (A i) (B i) hei (by dsimp [e,n]; positivity)
      intro q hq
      have hh := hi.2.2.2.2.2.2 q hq
      have h := (le_div_iff₀ hei).mp hh
      simpa only [div_mul_eq_mul_div] using h
    have hh := hinfo hbound (δ-(a+10*b)) (by dsimp [a,b]; linarith)
    filter_upwards [hh] with i hi
    convert hi using 1 <;> first | rfl | ring
  have had : 1+2*a < 1+δ := by dsimp [a]; linarith
  have hpd : (1/2:ℝ) < 1-5*b := by dsimp [b,a]; linarith
  have hqd : 0 < a-5*b := by dsimp [b]; linarith
  have hpud : -1-2*a+6*b < (-1/2:ℝ) := by dsimp [b]; linarith
  have hw : 2-δ < 2+3*a-10*b := by dsimp [b]; linarith
  refine ⟨A,B,ξ,?_⟩
  filter_upwards [hd,hξ.eventually_le_const hδ,hA.power_bound had,hdp.power_bound hpd,
    (hdq.tends_to_infinity ht hqd).eventually_ge_atTop R,hpup.power_bound hpud,
    hprod.power_bound hw,hinfo'] with i hi hξi hAi hdpi hdqi hpui hwi hIi
  rcases hi with ⟨hAi',hBi',hξ0,hei,hexp,hatP,hatQ⟩
  refine ⟨fun p hp => hAlg i p ((hPQ i).1 ((hFG i).1 (hAi' hp))),
    fun q hq => hAlg i q ((hPQ i).2 ((hFG i).2 (hBi' hq))),hei,hξ0,hξi,hexp,
    hatP,hatQ,hAi,?_,hdpi,hdqi,hwi,hIi⟩
  intro p hp
  apply (div_le_div_of_nonneg_right ?_ hei.le).trans hpui
  exact (CircleIncidence.degree_mono hBi' p).trans (hdF i p (hAi' hp))

theorem diagonal_sequence_oai {t : ℕ → ℝ} {X : ℕ → Finset Plane}
    (ht : Tendsto t atTop atTop) (ht1 : ∀i,1 ≤ t i) (hX0 : ∀i,(X i).Nonempty)
    (hX : Upper atTop t (fun i => ((X i).card:ℝ)) 3)
    (hE : Lower atTop t (fun i => incidences (X i) (X i)) 4)
    (hAlg : ∀i,∀p∈X i,∀k,IsAlgebraic ℚ (p k)) : Nonempty Sequence := by
  have hg (k : ℕ) := fixed_accuracy ht ht1 hX0 hX hE hAlg
    (δ := 1/((k:ℝ)+1)) (by positivity) (by
      apply (div_le_one (by positivity : (0:ℝ) < (k:ℝ)+1)).mpr
      linarith [Nat.cast_nonneg (α:=ℝ) k]) ((k:ℝ)+1)
  choose P Q ξ hg using hg
  have hh (k : ℕ) : ∀ᶠi in atTop,Good (t i) (1/((k:ℝ)+1)) ((k:ℝ)+1)
      (P k i) (Q k i) (ξ k i) ∧ (k:ℝ)+2 ≤ t i :=
    (hg k).and (ht.eventually_ge_atTop ((k:ℝ)+2))
  obtain ⟨f,_,hf⟩ := PowerGrowth.diagonal hh
  exact ⟨⟨fun i => t (f i),fun i => P i (f i),fun i => Q i (f i),fun i => ξ i (f i),
    fun i => (hf i).2,fun i => (hf i).1⟩⟩

end
end PlanarUnitDistances.IncidenceSequence

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.IncidenceSequence.diagonal_sequence_oai := @OAI.PlanarUnitDistances.IncidenceSequence.diagonal_sequence_oai
