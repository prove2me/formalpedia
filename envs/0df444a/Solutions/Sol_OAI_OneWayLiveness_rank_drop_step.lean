-- Prove2me | solution 1 for OAI.OneWayLiveness.rank_drop_step
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:00:12.29222+00:00
-- url     : https://prove2.me/submissions/fa3950fb-db53-4e1b-af6c-7920d5437f5b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/RankLoss.lean:L18-L84
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.rank_drop_step. The node keeps its source
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
import Theorems.Thm_OAI_OneWayLiveness_BRel_relation_corner
import Theorems.Thm_OAI_OneWayLiveness_Pairing_support_sandwich_subset_marked
import Theorems.Thm_OAI_OneWayLiveness_min_rank_corner_isUnit

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
lemma support_one : support (1 : Pairing (A ⊕ A)) = ∅ := by
  ext i
  simp [mem_support, identity_link]

lemma support_mul_subset (a b : Pairing (A ⊕ A)) :
    support (a * b) ⊆ support a ∪ support b := support_compose_subset a b

lemma support_pow_subset (a : Pairing (A ⊕ A)) (n : ℕ) : support (a ^ n) ⊆ support a := by
  induction n with
  | zero => simp only [pow_zero, support_one, Finset.empty_subset]
  | succ n ih =>
    rw [pow_succ]
    exact (support_mul_subset _ _).trans (Finset.union_subset ih (Finset.Subset.refl _))

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

lemma reduce_injective (e : Pairing (A ⊕ A)) {x y : Pairing (A ⊕ A)}
    (hxl : e * x = x) (hxr : x * e = x) (hyl : e * y = y) (hyr : y * e = y)
    (h : reduce e x = reduce e y) : x = y := by
  have hh := congrArg (expand e) h
  simpa only [expand_reduce, hxl, hxr, hyl, hyr] using hh

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

namespace Corner
variable {M N : Type*} [Monoid M] [Monoid N] {e : M} {he : e * e = e}
    {q : N} {hq : q * q = q}

lemma mapTo_surjective (f : M →* N) (hf : f e = q) (hs : Function.Surjective f) :
    Function.Surjective (mapTo (he := he) (hq := hq) f hf) := by
  intro y
  obtain ⟨x, hx⟩ := hs y.val
  refine ⟨sandwich x, Corner.ext ?_⟩
  change f (e * x * e) = y.val
  rw [map_mul, map_mul, hf, hx, y.left, y.right]

end Corner

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
    {M : Type*} [Monoid M] (ρ : M →* Pairing (A ⊕ A))
    (e : M) (he : e * e = e)

lemma reduceHom_injective (hρ : Function.Injective ρ) : Function.Injective (reduceHom ρ e he) := by
  intro x y hxy
  apply Corner.ext
  apply hρ
  apply reduce_injective (ρ e) (by rw [← map_mul, x.left]) (by rw [← map_mul, x.right])
    (by rw [← map_mul, y.left]) (by rw [← map_mul, y.right]) hxy

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

lemma exists_min_rank_lift {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (f : M →* N) (hf : Function.Surjective f)
    (q : N) (hq : q * q = q) :
    ∃ e : M, e * e = e ∧ f e = q ∧
      ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z) := by
  let S : Set M := {e | e * e = e ∧ f e = q}
  have hS : S.Nonempty := exists_idempotent_lift f hf q hq
  obtain ⟨e, he, hmin⟩ := Set.exists_min_image S (fun z => Pairing.rank (ρ z)) (Set.toFinite _) hS
  exact ⟨e, he.1, he.2, fun z hz hq => hmin z ⟨hz, hq⟩⟩

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
lemma addEdge_idem (x y : H) : addEdge x y * addEdge x y = addEdge x y := by
  ext u v
  simp only [mul_holds, addEdge_holds]
  aesop
end BRel

namespace RectangleFrame
variable {H I J : Type*} (F : RectangleFrame H I J)
end RectangleFrame

namespace Corner
variable {M : Type*} [Monoid M] {e : M} {he : e * e = e}

end Corner

lemma HasUnitLifts.comp_equiv {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]
    {f : M →* N} (hf : HasUnitLifts f) (e : N ≃* P) : HasUnitLifts (e.toMonoidHom.comp f) := by
  intro u
  obtain ⟨v, hv⟩ := hf (Units.map e.symm.toMonoidHom u)
  refine ⟨v, ?_⟩
  change e (f (↑v)) = (↑u)
  rw [hv]
  exact e.apply_symm_apply _

lemma min_rank_corner_unitLifts {M N A : Type*} [Monoid M] [Monoid N] [Finite M] [Fintype A]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (f : M →* N) (hs : Function.Surjective f)
    (e : M) (he : e * e = e) (q : N) (hq : q * q = q) (hf : f e = q)
    (hmin : ∀ z : M, z * z = z → f z = q → Pairing.rank (ρ e) ≤ Pairing.rank (ρ z)) :
    HasUnitLifts (Corner.mapTo (he := he) (hq := hq) f hf) := by
  intro u
  obtain ⟨y, hy⟩ := Corner.mapTo_surjective (he := he) (hq := hq) f hf hs (↑u)
  have hunit : IsUnit y := min_rank_corner_isUnit ρ hρ f e he q hq hf hmin y (hy ▸ u.isUnit)
  obtain ⟨v, rfl⟩ := hunit
  exact ⟨v, hy⟩

namespace BRel
variable {H : Type*}
lemma restricted_sandwich {P N : BRel H} (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N) :
    let Q := P * restrictedId F * P
    restrictedId F * (Q * N * Q) * restrictedId F = restrictedId F * N * restrictedId F := by
  let E := restrictedId F
  have hl : E * (P * E * P) = E * P := by rw [← mul_assoc, ← mul_assoc, hF]
  have hr : (P * E * P) * E = P * E := by rw [mul_assoc P E P, mul_assoc, hF]
  change E * ((P * E * P) * N * (P * E * P)) * E = E * N * E
  calc
    _ = (E * (P * E * P)) * N * ((P * E * P) * E) := by simp only [mul_assoc]
    _ = (E * P) * N * (P * E) := by rw [hl, hr]
    _ = E * (P * N * P) * E := by simp only [mul_assoc]
    _ = E * N * E := by rw [hPN, hNP]

lemma sandwich_holds_on {P N : BRel H} (F : Set H)
    (hF : restrictedId F * P * restrictedId F = restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N) (x y : F) :
    ((P * restrictedId F * P) * N * (P * restrictedId F * P)).holds x.val y.val ↔
      N.holds x.val y.val := by
  have hh := congrArg (fun a : BRel H => a.holds x.val y.val) (restricted_sandwich F hF hPN hNP)
  simpa only [mul_restrictedId, restrictedId_mul, x.property, y.property,
    true_and, and_true, eq_iff_iff] using hh
end BRel

end OneWayLiveness

end OAI

-- ---- from OAI.Combinatorics.Automata.RankLoss ----
namespace OAI

namespace OneWayLiveness

/-- One new relation pair forces the inductive rank loss, after two genuine
corner reductions. The support budget loses only the factor two. -/
lemma rank_drop_step {H A M : Type} [Fintype H] [Fintype A] [Monoid M] [Finite M]
    (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ)
    (e : M) (he : e * e = e) (b : Corner e he) (hb : b * b = b)
    (P N : BRel H) (heP : φ e = P) (hbN : φ b.val = N)
    (F : Set H) [Fintype F]
    (hF : BRel.restrictedId F * P * BRel.restrictedId F = BRel.restrictedId F)
    (hPN : P * N = N) (hNP : N * P = N)
    (x y : F) (hxy : x ≠ y)
    (hN : ∀ i j : F, N.holds i.val j.val ↔ (BRel.addEdge x y).holds i j)
    (hIH : RankLossAt (Fintype.card F)) :
    rankLoss (Fintype.card F) ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by
  classical
  let ρ₁ := Pairing.reduceHom ρ e he
  have hρ₁ : Function.Injective ρ₁ := Pairing.reduceHom_injective ρ e he hρ
  have hP : P * P = P := by rw [← heP, ← map_mul, he]
  let φ₁ := Corner.mapTo (he := he) (hq := hP) φ heP
  have hs₁ : Function.Surjective φ₁ := Corner.mapTo_surjective φ heP hφ
  obtain ⟨hQ, θ, hθ, hPQ, hQP⟩ := BRel.relation_corner hP F hF
  let Q := P * BRel.restrictedId F * P
  let q : Corner P hP := ⟨Q, hPQ, hQP⟩
  have hq : q * q = q := Corner.ext hQ
  obtain ⟨d, hd, hφd, hmin⟩ := exists_min_rank_lift ρ₁ φ₁ hs₁ q hq
  let ρ₂ := Pairing.reduceHom ρ₁ d hd
  have hρ₂ : Function.Injective ρ₂ := Pairing.reduceHom_injective ρ₁ d hd hρ₁
  let φ₂ := Corner.mapTo (he := hd) (hq := hq) φ₁ hφd
  let E := (Corner.flattenEquiv q hq).trans θ
  let ψ := E.toMonoidHom.comp φ₂
  have hsψ : Function.Surjective ψ :=
    E.surjective.comp (Corner.mapTo_surjective φ₁ hφd hs₁)
  have hlψ : HasUnitLifts ψ :=
    (min_rank_corner_unitLifts ρ₁ hρ₁ φ₁ hs₁ d hd q hq hφd hmin).comp_equiv E
  let w : Corner d hd := Corner.sandwich b
  have hw : ψ w = BRel.addEdge x y := by
    ext i j
    change (θ ((Corner.flattenEquiv q hq) (φ₂ w))).holds i j ↔ _
    rw [hθ]
    change (φ₁ (d * b * d)).val.holds i.val j.val ↔ _
    rw [map_mul, map_mul, hφd]
    change (Q * φ b.val * Q).holds i.val j.val ↔ _
    rw [hbN]
    exact (BRel.sandwich_holds_on F hF hPN hNP i j).trans (hN i j)
  obtain ⟨n, hn, hnidem⟩ := exists_idempotent_power w
  have him : ψ (w ^ n) = BRel.addEdge x y := by
    rw [map_pow, hw]
    exact IsIdempotentElem.pow_eq (BRel.addEdge_idem x y) (Nat.ne_of_gt hn)
  have hlow := hIH F {i // i ∈ Pairing.lefts (ρ₁ d)} (Corner d hd) rfl
    ρ₂ hρ₂ ψ hsψ hlψ (w ^ n) hnidem x y hxy him
  let J := Pairing.support (ρ₁ b)
  obtain ⟨K, hK, hall⟩ := Pairing.reduceHom_common_support ρ₁ d hd J
  have hwK : Pairing.support (ρ₂ w) ⊆ K := hall b (Finset.Subset.refl _)
  have hvK : Pairing.support (ρ₂ (w ^ n)) ⊆ K := by
    rw [map_pow]
    exact (Pairing.support_pow_subset _ _).trans hwK
  have hJ : J.card ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := by
    have hi : ρ₁ b * ρ₁ b = ρ₁ b := by rw [← map_mul, hb]
    have hh := Pairing.support_idempotent_bound (ρ₁ b) hi
    simpa only [ρ₁, Pairing.card_reduced, Pairing.reduceHom_rank] using hh
  calc
    rankLoss (Fintype.card F) ≤ Fintype.card {i // i ∈ Pairing.lefts (ρ₁ d)} -
        Pairing.rank (ρ₂ (w ^ n)) := hlow
    _ ≤ (Pairing.support (ρ₂ (w ^ n))).card := Pairing.defect_le_support _
    _ ≤ K.card := Finset.card_le_card hvK
    _ ≤ J.card := hK
    _ ≤ 2 * (Pairing.rank (ρ e) - Pairing.rank (ρ b.val)) := hJ

namespace RectangleFrame
open scoped Classical
variable {H I J : Type} [Fintype I] [Fintype J]
    (F : RectangleFrame H I J)

end RectangleFrame

open scoped Classical

namespace Corner
variable {M : Type*} [Monoid M]
end Corner

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness


theorem solution : type_of% @_root_.OAI.OneWayLiveness.rank_drop_step := @_root_.OAI.OneWayLiveness.rank_drop_step
