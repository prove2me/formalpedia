-- Prove2me | solution 1 for OAI.OneWayLiveness.rankLoss_all
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:04:10.053548+00:00
-- url     : https://prove2.me/submissions/09e4f32e-d053-42a2-b4e5-d3abc354ebd9

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/RankLoss.lean:L274-L351
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.rankLoss_all. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_OneWayLiveness
import Definitions.Def_OAI_Combinatorics_Automata_Model
import Definitions.Def_OAI_Combinatorics_Automata_Wiring
import Definitions.Def_OAI_Combinatorics_Automata_Cells
import Definitions.Def_OAI_Combinatorics_Automata_Tours
import Definitions.Def_OAI_Combinatorics_Automata_Normalization
import Definitions.Def_OAI_Combinatorics_Automata_Network
import Definitions.Def_OAI_Combinatorics_Automata_Rank
import Definitions.Def_OAI_Combinatorics_Automata_Diagram
import Definitions.Def_OAI_Combinatorics_Automata_Diagrams
import Definitions.Def_OAI_Combinatorics_Automata_Corners
import Definitions.Def_OAI_Combinatorics_Automata_Relations
import Definitions.Def_OAI_Combinatorics_Automata_RankLoss
import Theorems.Thm_OAI_OneWayLiveness_Pairing_full_rank_isUnit
import Theorems.Thm_OAI_OneWayLiveness_Pairing_support_sandwich_subset_marked
import Theorems.Thm_OAI_OneWayLiveness_conjugate_lift
import Theorems.Thm_OAI_OneWayLiveness_rectangle_chain

-- ---- from OAI.Combinatorics.Automata.Rank ----
namespace OAI

namespace OneWayLiveness

namespace Pairing
open scoped Classical
variable {A B C : Type*}

variable [Fintype A] [Fintype B] [Fintype C]

lemma rank_eq_rights (a : Pairing (A ⊕ B)) : rank a = (rights a).card := by
  simpa only [Fintype.card_coe, rank] using Fintype.card_congr (transversalEquiv a)

lemma lefts_compose_subset (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    lefts (compose a b) ⊆ lefts a := by
  intro i hi
  obtain ⟨k, hik⟩ := (mem_lefts _ _).mp hi
  obtain ⟨j, hij, _⟩ := a.unique (.inl i)
  rcases j with j | j
  · have hh := compose_left_cap a b hij
    have he := ((compose a b).eq_mate hh).trans ((compose a b).eq_mate hik).symm
    cases he
  · exact (mem_lefts _ _).mpr ⟨j, hij⟩

lemma rights_compose_subset (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rights (compose a b) ⊆ rights b := by
  intro k hk
  obtain ⟨i, hik⟩ := (mem_rights _ _).mp hk
  obtain ⟨j, hkj, _⟩ := b.unique (.inr k)
  rcases j with j | j
  · exact (mem_rights _ _).mpr ⟨j, b.symm hkj⟩
  · have hh := compose_right_cap a b hkj
    have he := ((compose a b).eq_mate hh).trans
      ((compose a b).eq_mate ((compose a b).symm hik)).symm
    cases he

lemma rank_compose_le_left (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank a := Finset.card_le_card (lefts_compose_subset a b)
lemma rank_compose_le_right (a : Pairing (A ⊕ B)) (b : Pairing (B ⊕ C)) :
    rank (compose a b) ≤ rank b := by
  rw [rank_eq_rights, rank_eq_rights]
  exact Finset.card_le_card (rights_compose_subset a b)
lemma rank_le_card (a : Pairing (A ⊕ B)) : rank a ≤ Fintype.card A :=
  Finset.card_le_univ _

lemma defect_le_support (a : Pairing (A ⊕ A)) :
    Fintype.card A - rank a ≤ (support a).card := by
  have hs : Finset.univ \ support a ⊆ lefts a := by
    intro i hi
    simp only [Finset.mem_sdiff, Finset.mem_univ, mem_support, not_not, true_and] at hi
    exact (mem_lefts a i).mpr ⟨i, hi⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ] at hc
  unfold rank
  omega

lemma support_compose_subset (a b : Pairing (A ⊕ A)) :
    support (compose a b) ⊆ support a ∪ support b := by
  intro i hi
  by_contra hn
  have ha : a.link (.inl i) (.inr i) := by
    simpa using (Finset.notMem_union.mp hn).1
  have hb : b.link (.inl i) (.inr i) := by
    simpa using (Finset.notMem_union.mp hn).2
  exact (mem_support _ _).mp hi (compose_transversal a b ha hb)

lemma support_idempotent_subset (e : Pairing (A ⊕ A)) (he : compose e e = e) :
    support e ⊆ (Finset.univ \ lefts e) ∪ (Finset.univ \ rights e) := by
  intro i hi
  by_contra hn
  have hl : i ∈ lefts e := by simpa using (Finset.notMem_union.mp hn).1
  have hr : i ∈ rights e := by simpa using (Finset.notMem_union.mp hn).2
  obtain ⟨j, hij⟩ := (mem_lefts _ _).mp hl
  obtain ⟨k, hki⟩ := (mem_rights _ _).mp hr
  have hkj := compose_transversal e e hki hij
  rw [he] at hkj
  have hji : j = i := Sum.inr.inj ((e.eq_mate hkj).trans (e.eq_mate hki).symm)
  subst j
  exact (mem_support _ _).mp hi hij

lemma support_idempotent_bound (e : Pairing (A ⊕ A)) (he : compose e e = e) :
    (support e).card ≤ 2 * (Fintype.card A - rank e) := by
  calc
    _ ≤ ((Finset.univ \ lefts e) ∪ (Finset.univ \ rights e)).card :=
      Finset.card_le_card (support_idempotent_subset e he)
    _ ≤ (Finset.univ \ lefts e).card + (Finset.univ \ rights e).card := Finset.card_union_le _ _
    _ = _ := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
        ← rank_eq_rights]
      simp only [rank, two_mul]

end Pairing

namespace Pairing
open scoped Classical
variable {P : Type*} {A B C D : Type*}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D]

end Pairing

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Diagram ----
namespace OAI

namespace OneWayLiveness

namespace FiniteWiring
variable {V C : Type*} (G : SimpleGraph V)

end FiniteWiring

namespace Pairing
open scoped Classical
variable {A B : Type*} [Fintype A] [Fintype B]

lemma left_reachable_eq (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) {x y : A}
    (h : (glueGraph v u).Reachable (outer (.inl x)) (outer (.inl y))) : x = y := by
  by_contra hne
  have hl : (compose v u).link (.inl x) (.inl y) :=
    ⟨fun he => hne (Sum.inl.inj he), h⟩
  rw [huv, identity_link] at hl
  cases hl

lemma marked_card_le (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) : (marked v u J).card ≤ J.card := by
  let f : {x // x ∈ marked v u J} → {i // i ∈ J} := fun x =>
    ⟨((mem_marked v u J x).mp x.property).choose,
     ((mem_marked v u J x).mp x.property).choose_spec.1⟩
  have hf (x : {x // x ∈ marked v u J}) :
      (glueGraph v u).Reachable (outer (.inl x.val)) (.inl (.inr (f x).val)) :=
    ((mem_marked v u J x).mp x.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply left_reachable_eq v u huv
    have hx := hf x
    rw [hxy] at hx
    exact hx.trans (hf y).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

/-- The simultaneous support estimate: a single small set works for every
middle diagram supported in the original set, including products and powers. -/
lemma common_support (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) :
    ∃ K : Finset A, K.card ≤ J.card ∧ ∀ a : Pairing (B ⊕ B), support a ⊆ J →
      support (compose (compose v a) u) ⊆ K :=
  ⟨marked v u J, marked_card_le v u huv J, support_sandwich_subset_marked v u huv J⟩

end Pairing

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
lemma support_mul_subset (a b : Pairing (A ⊕ A)) :
    support (a * b) ⊆ support a ∪ support b := support_compose_subset a b

lemma expand_reduce (e z : Pairing (A ⊕ A)) : expand e (reduce e z) = e * z * e := by
  simp only [expand, reduce, mul_eq_compose, compose_assoc, ← splitLeft_splitRight e]

lemma splitLeft_absorb (e : Pairing (A ⊕ A)) (he : e * e = e) :
    compose e (splitLeft e) = splitLeft e := by
  calc
    _ = compose (compose (splitLeft e) (splitRight e)) (splitLeft e) :=
      congrArg (fun t => compose t (splitLeft e)) (splitLeft_splitRight e).symm
    _ = _ := by rw [compose_assoc, splitRight_splitLeft e he, compose_identity]

lemma reduce_sandwich (e a : Pairing (A ⊕ A)) (he : e * e = e) :
    reduce e (e * a * e) = reduce e a := by
  unfold reduce
  simp only [mul_eq_compose, compose_assoc]
  rw [← compose_assoc (splitRight e) e]
  rw [splitRight_absorb e he, splitLeft_absorb e he]

lemma rank_reduce (e z : Pairing (A ⊕ A)) (hzl : e * z = z) (hzr : z * e = z) :
    rank (reduce e z) = rank z := by
  apply le_antisymm
  · exact (rank_compose_le_left _ _).trans (rank_compose_le_right _ _)
  · have heq : expand e (reduce e z) = z := by rw [expand_reduce, hzl, hzr]
    calc
      rank z = rank (expand e (reduce e z)) := congrArg rank heq.symm
      _ ≤ rank (compose (splitLeft e) (reduce e z)) := rank_compose_le_left _ _
      _ ≤ rank (reduce e z) := rank_compose_le_right _ _

lemma reduce_common_support (e : Pairing (A ⊕ A)) (he : e * e = e) (J : Finset A) :
    ∃ K : Finset {i // i ∈ lefts e}, K.card ≤ J.card ∧
      ∀ a : Pairing (A ⊕ A), support a ⊆ J → support (reduce e (e * a * e)) ⊆ K := by
  obtain ⟨K, hK, hall⟩ := common_support (splitRight e) (splitLeft e)
    (splitRight_splitLeft e he) J
  refine ⟨K, hK, fun a ha => ?_⟩
  rw [reduce_sandwich e a he]
  exact hall a ha

lemma card_reduced (e : Pairing (A ⊕ A)) : Fintype.card {i // i ∈ lefts e} = rank e :=
  Fintype.card_coe _
end Pairing

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Corners ----
namespace OAI

namespace OneWayLiveness

/-- Positive powers in any finite monoid contain an idempotent. -/
lemma exists_idempotent_power {M : Type*} [Monoid M] [Finite M] (a : M) :
    ∃ n : ℕ, 0 < n ∧ a ^ n * a ^ n = a ^ n := by
  let : TopologicalSpace M := ⊥
  have : DiscreteTopology M := ⟨rfl⟩
  let S : Set M := {x | ∃ n : ℕ, 0 < n ∧ a ^ n = x}
  have hS : S.Nonempty := ⟨a, 1, by omega, pow_one a⟩
  have hmul : ∀ᵉ (x ∈ S) (y ∈ S), x * y ∈ S := by
    rintro x ⟨n, hn, rfl⟩ y ⟨m, hm, rfl⟩
    exact ⟨n + m, by omega, pow_add a n m⟩
  obtain ⟨b, ⟨n, hn, rfl⟩, hb⟩ := exists_idempotent_in_compact_subsemigroup
    (fun _ => continuous_of_discreteTopology) S hS (Set.toFinite S).isCompact hmul
  exact ⟨n, hn, hb⟩

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}
end Corner

lemma isUnit_of_injective_map_finite {M N : Type*} [Monoid M] [Monoid N] [Finite M]
    (f : M →* N) (hf : Function.Injective f) (a : M) (ha : IsUnit (f a)) : IsUnit a := by
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power a
  have hp : f (a ^ n) = 1 := by
    have hu : IsUnit (f (a ^ n)) := by rw [map_pow]; exact ha.pow n
    apply (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp
    change f (a ^ n) * f (a ^ n) = f (a ^ n)
    rw [← map_mul, hi]
  have he : a ^ n = 1 := hf (by simpa using hp)
  apply (isUnit_pow_iff (Nat.ne_of_gt hn)).mp
  rw [he]
  exact isUnit_one

namespace Corner
variable {M N : Type*} [Monoid M] [Monoid N] {e : M} {he : e * e = e}
    {q : N} {hq : q * q = q}

end Corner

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
    {M : Type*} [Monoid M] (ρ : M →* Pairing (A ⊕ A))
    (e : M) (he : e * e = e)

lemma reduceHom_rank (x : Corner e he) : rank (reduceHom ρ e he x) = rank (ρ x.val) :=
  rank_reduce _ _ (by rw [← map_mul, x.left]) (by rw [← map_mul, x.right])

lemma reduceHom_common_support (J : Finset A) :
    ∃ K : Finset {i // i ∈ lefts (ρ e)}, K.card ≤ J.card ∧
      ∀ a : M, support (ρ a) ⊆ J → support (reduceHom ρ e he (Corner.sandwich a)) ⊆ K := by
  obtain ⟨K, hK, hall⟩ := reduce_common_support (ρ e) (image_idempotent ρ e he) J
  refine ⟨K, hK, fun a ha => ?_⟩
  change support (reduce (ρ e) (ρ (e * a * e))) ⊆ K
  rw [map_mul, map_mul]
  exact hall (ρ a) ha

end Pairing

/-- A lift of an idempotent can always be made idempotent without changing its image. -/
lemma exists_idempotent_lift {M N : Type*} [Monoid M] [Monoid N] [Finite M]
    (f : M →* N) (hf : Function.Surjective f) (q : N) (hq : q * q = q) :
    ∃ e : M, e * e = e ∧ f e = q := by
  obtain ⟨a, ha⟩ := hf q
  obtain ⟨n, hn, hi⟩ := exists_idempotent_power a
  refine ⟨a ^ n, hi, ?_⟩
  rw [map_pow, ha]
  exact IsIdempotentElem.pow_eq hq (Nat.ne_of_gt hn)

namespace Corner
variable {M : Type*} [Monoid M] {e f : M} {he : e * e = e} {hf : f * f = f}

end Corner

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.Relations ----
namespace OAI

namespace OneWayLiveness

namespace BRel
variable {H : Type*}

end BRel

namespace BRel
variable {H : Type*}
lemma addEdge_ne_one {x y : H} (hxy : x ≠ y) : addEdge x y ≠ 1 := by
  intro he
  have hh : (addEdge x y).holds x y := Or.inr ⟨rfl, rfl⟩
  rw [he] at hh
  exact hxy hh

end BRel

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
lemma generator_image (i : I) (j : J) :
    F.base * BRel.addEdge (F.left i) F.hub * BRel.addEdge F.hub (F.right j) * F.base =
      F.rel {(i,j)} := by
  have hl := F.left_ne_hub i
  have hr := F.right_ne_hub j
  have he : F.base * BRel.addEdge (F.left i) F.hub * BRel.addEdge F.hub (F.right j) * F.base =
      F.base * (BRel.addEdge (F.left i) F.hub * BRel.addEdge F.hub (F.right j)) * F.base := by
    simp only [mul_assoc]
  rw [he]
  ext x y
  simp only [base, BRel.mul_holds, BRel.addEdge_holds, rel_holds,
    Set.mem_singleton_iff, exists_eq_left]
  aesop

end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

end Corner

namespace BRel
variable {H : Type*}
end BRel

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.RankLoss ----
namespace OAI

namespace OneWayLiveness

namespace RectangleFrame
open scoped Classical
variable {H I J : Type} [Fintype I] [Fintype J]
    (F : RectangleFrame H I J)

lemma deleted_card (i : I) (j : J) :
    (F.deleted i j).card = (Fintype.card I - 1) + (Fintype.card J - 1) + 1 := by
  have hLR : Disjoint ((Finset.univ.erase i).image F.left) ((Finset.univ.erase j).image F.right) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    exact F.disjoint a b hb.symm
  have hh : Disjoint ((Finset.univ.erase i).image F.left ∪ (Finset.univ.erase j).image F.right)
      {F.hub} := by
    rw [Finset.disjoint_singleton_right]
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists, not_and]
    exact ⟨fun a _ => F.left_ne_hub a, fun b _ => F.right_ne_hub b⟩
  simp only [deleted, Finset.card_union_of_disjoint hh, Finset.card_union_of_disjoint hLR,
    Finset.card_singleton, Finset.card_image_of_injective _ F.left_injective,
    Finset.card_image_of_injective _ F.right_injective, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

lemma retained_card [Fintype H] (i : I) (j : J) :
    Fintype.card (F.retained i j) = Fintype.card H -
      ((Fintype.card I - 1) + (Fintype.card J - 1) + 1) := by
  rw [Fintype.card_of_subtype (F.deleted i j)ᶜ (by intro x; simp [retained]),
    Finset.card_compl, F.deleted_card]

lemma exists_frame [Fintype H] (h : 33 ≤ Fintype.card H) : Nonempty (RectangleFrame H (Fin 16) (Fin 16)) := by
  obtain ⟨f⟩ : Nonempty (((Fin 16 ⊕ Fin 16) ⊕ Unit) ↪ H) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using h
  refine ⟨⟨fun i => f (Sum.inl (Sum.inl i)), fun j => f (Sum.inl (Sum.inr j)),
    f (Sum.inr ()), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i j hij
    simpa using f.injective hij
  · intro i j hij
    simpa using f.injective hij
  · intro i j hij
    simpa using f.injective hij
  · intro i hij
    simpa using f.injective hij
  · intro j hij
    simpa using f.injective hij
end RectangleFrame

open scoped Classical

lemma rankLoss_recurrence {h : ℕ} (hh : 33 ≤ h) : rankLoss h = 2 * rankLoss (h - 31) := by
  have he : (h - 2) / 31 = (h - 31 - 2) / 31 + 1 := by omega
  simp only [rankLoss, he, pow_succ]
  omega

/-- Exponential rank loss by 256-addition amplification, simultaneously in the
relation alphabet and the ambient diagram degree. -/
theorem rankLoss_all (h : ℕ) : RankLossAt h := by
  induction h using Nat.strong_induction_on with
  | h h IH =>
    intro H A M _ _ _ _ hH ρ hρ φ hφ hl a ha x y hxy hφa
    classical
    have hcpos : 1 ≤ Fintype.card A - Pairing.rank (ρ a) := by
      have hr := Pairing.rank_le_card (ρ a)
      have hne : Pairing.rank (ρ a) ≠ Fintype.card A := by
        intro heq
        have hu := isUnit_of_injective_map_finite ρ hρ a (Pairing.full_rank_isUnit (ρ a) heq)
        have haone : a = 1 := (IsIdempotentElem.iff_eq_one_of_isUnit hu).mp ha
        have hh : BRel.addEdge x y = 1 := by rw [← hφa, haone, map_one]
        exact BRel.addEdge_ne_one hxy hh
      omega
    by_cases hh : h < 33
    · have he : (h - 2) / 31 = 0 := by omega
      simpa only [rankLoss, he, pow_zero] using hcpos
    have hh : 33 ≤ h := by omega
    obtain ⟨F⟩ := RectangleFrame.exists_frame (H := H) (by omega)
    let c := Fintype.card A - Pairing.rank (ρ a)
    let src : Fin 16 ⊕ Fin 16 → H := Sum.elim F.left (fun _ => F.hub)
    let dst : Fin 16 ⊕ Fin 16 → H := Sum.elim (fun _ => F.hub) F.right
    have hdist (p : Fin 16 ⊕ Fin 16) : src p ≠ dst p := by
      cases p with
      | inl i => exact F.left_ne_hub i
      | inr j => exact (F.right_ne_hub j).symm
    choose s hs hφs hrs using fun p => conjugate_lift ρ φ hl a ha x y hxy hφa (src p) (dst p) (hdist p)
    let J : Finset A := Finset.univ.biUnion (fun p => Pairing.support (ρ (s p)))
    have hsJ (p : Fin 16 ⊕ Fin 16) : Pairing.support (ρ (s p)) ⊆ J := by
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hi⟩
    have hJ : J.card ≤ 64 * c := by
      have hb (p : Fin 16 ⊕ Fin 16) : (Pairing.support (ρ (s p))).card ≤ 2 * c := by
        have hi : ρ (s p) * ρ (s p) = ρ (s p) := by rw [← map_mul, hs]
        simpa only [hrs, c] using Pairing.support_idempotent_bound (ρ (s p)) hi
      have hh := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin 16 ⊕ Fin 16))
        (fun p => Pairing.support (ρ (s p))) (2 * c) (fun p _ => hb p)
      simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_fin] at hh
      dsimp [J]
      omega
    have hbase : F.base * F.base = F.base := BRel.restrictedId_idem _
    obtain ⟨e, he, heφ⟩ := exists_idempotent_lift φ hφ F.base hbase
    let ρ₀ := Pairing.reduceHom ρ e he
    obtain ⟨K, hK, hall⟩ := Pairing.reduceHom_common_support ρ e he J
    let g : Fin 16 × Fin 16 → Corner e he := fun p =>
      Corner.sandwich (s (Sum.inl p.1) * s (Sum.inr p.2))
    have hg (p : Fin 16 × Fin 16) : φ (g p).val = F.rel {p} := by
      change φ (e * (s (Sum.inl p.1) * s (Sum.inr p.2)) * e) = _
      rw [map_mul, map_mul, map_mul, heφ, hφs, hφs]
      dsimp [src, dst]
      rw [← mul_assoc]
      exact F.generator_image p.1 p.2
    have hgK (p : Fin 16 × Fin 16) : Pairing.support (ρ₀ (g p)) ⊆ K := by
      apply hall
      rw [map_mul]
      intro i hi
      rcases Finset.mem_union.mp (Pairing.support_mul_subset _ _ hi) with hi | hi
      · exact hsJ _ hi
      · exact hsJ _ hi
    have hcard (i j : Fin 16) : Fintype.card (F.retained i j) = h - 31 := by
      rw [F.retained_card, hH]
      rfl
    have hi (i j : Fin 16) : RankLossAt (Fintype.card (F.retained i j)) := by
      rw [hcard]
      exact IH (h - 31) (by omega)
    obtain ⟨b, _hb, _hbφ, hbK, hcost⟩ := rectangle_chain ρ hρ φ hφ F (rankLoss (h - 31))
      (fun i j => congrArg rankLoss (hcard i j)) hi e he heφ g hg K hgK Finset.univ
    have hbudget : Pairing.rank (ρ e) - Pairing.rank (ρ b.val) ≤ 64 * c := by
      have hd := Pairing.defect_le_support (ρ₀ b)
      have hbc := Finset.card_le_card hbK
      simp only [ρ₀, Pairing.card_reduced, Pairing.reduceHom_rank] at hd
      omega
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hcost
    rw [rankLoss_recurrence hh]
    change 2 * rankLoss (h - 31) ≤ c
    omega

namespace Corner
variable {M : Type*} [Monoid M]
end Corner

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness
open scoped Classical


theorem solution : type_of% @_root_.OAI.OneWayLiveness.rankLoss_all := @_root_.OAI.OneWayLiveness.rankLoss_all
