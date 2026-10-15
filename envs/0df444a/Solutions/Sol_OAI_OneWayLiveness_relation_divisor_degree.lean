-- Prove2me | solution 1 for OAI.OneWayLiveness.relation_divisor_degree
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T05:07:30.169974+00:00
-- url     : https://prove2.me/submissions/36859b93-3b00-4ec2-b9ac-2bb20450382f

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Automata/RankLoss.lean:L364-L382
-- (upload_full_project.md Phase 4): solution for node OAI.OneWayLiveness.relation_divisor_degree. The node keeps its source
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
import Theorems.Thm_OAI_OneWayLiveness_min_rank_corner_isUnit
import Theorems.Thm_OAI_OneWayLiveness_rankLoss_all

-- ---- from OAI.Combinatorics.Automata.Rank ----
namespace OAI

namespace OneWayLiveness

namespace Pairing
open scoped Classical
variable {A B C : Type*}

variable [Fintype A] [Fintype B] [Fintype C]

lemma rank_le_card (a : Pairing (A ⊕ B)) : rank a ≤ Fintype.card A :=
  Finset.card_le_univ _

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

end Pairing

namespace Pairing
open scoped Classical
variable {A : Type*} [Fintype A]
lemma expand_reduce (e z : Pairing (A ⊕ A)) : expand e (reduce e z) = e * z * e := by
  simp only [expand, reduce, mul_eq_compose, compose_assoc, ← splitLeft_splitRight e]

lemma reduce_injective (e : Pairing (A ⊕ A)) {x y : Pairing (A ⊕ A)}
    (hxl : e * x = x) (hxr : x * e = x) (hyl : e * y = y) (hyr : y * e = y)
    (h : reduce e x = reduce e y) : x = y := by
  have hh := congrArg (expand e) h
  simpa only [expand_reduce, hxl, hxr, hyl, hyr] using hh

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

end RectangleFrame

open scoped Classical

namespace Corner
variable {M : Type*} [Monoid M]
end Corner

/-- No permutation-lift hypothesis remains in the divisor degree bound. -/
theorem relation_divisor_degree {H A M : Type} [Fintype H] [Fintype A]
    [Monoid M] [Finite M] (ρ : M →* Pairing (A ⊕ A)) (hρ : Function.Injective ρ)
    (φ : M →* BRel H) (hφ : Function.Surjective φ) (x y : H) (hxy : x ≠ y) :
    rankLoss (Fintype.card H) ≤ Fintype.card A := by
  classical
  obtain ⟨e, he, heφ, hmin⟩ := exists_min_rank_lift ρ φ hφ 1 (one_mul 1)
  let ρ₀ := Pairing.reduceHom ρ e he
  let φ₀ := Corner.mapTo (he := he) (hq := one_mul 1) φ heφ
  let ψ := Corner.oneEquiv.toMonoidHom.comp φ₀
  have hψ : Function.Surjective ψ := Corner.oneEquiv.surjective.comp
    (Corner.mapTo_surjective φ heφ hφ)
  have hlψ : HasUnitLifts ψ :=
    (min_rank_corner_unitLifts ρ hρ φ hφ e he 1 (one_mul 1) heφ hmin).comp_equiv Corner.oneEquiv
  obtain ⟨a, ha, haψ⟩ := exists_idempotent_lift ψ hψ (BRel.addEdge x y) (BRel.addEdge_idem x y)
  have hb := rankLoss_all (Fintype.card H) H {i // i ∈ Pairing.lefts (ρ e)} (Corner e he)
    rfl ρ₀ (Pairing.reduceHom_injective ρ e he hρ) ψ hψ hlψ a ha x y hxy haψ
  rw [Pairing.card_reduced] at hb
  exact hb.trans ((Nat.sub_le _ _).trans (Pairing.rank_le_card _))

end OneWayLiveness

end OAI

-- ---- platform node ----
open OAI OAI.OneWayLiveness
open scoped Classical


theorem solution : type_of% @_root_.OAI.OneWayLiveness.relation_divisor_degree := @_root_.OAI.OneWayLiveness.relation_divisor_degree
