-- Prove2me | solution 1 for OAI.TwoWayComplementation.single_edge_cost
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:10:05.257048+00:00
-- url     : https://prove2.me/submissions/b75909ee-72e2-44e4-b7ad-467909af35c4

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean:L14-L180
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.single_edge_cost. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Amplification
import Theorems.Thm_OAI_TwoWayComplementation_bipartite_relation_comp
import Theorems.Thm_OAI_TwoWayComplementation_common_pair_budget
import Theorems.Thm_OAI_TwoWayComplementation_exists_hub_families
import Theorems.Thm_OAI_TwoWayComplementation_exists_nested_chain
import Theorems.Thm_OAI_TwoWayComplementation_minimal_idempotent_lift
import Theorems.Thm_OAI_TwoWayComplementation_pair_conjugate
import Theorems.Thm_OAI_TwoWayComplementation_retained_pair_set
import Theorems.Thm_OAI_TwoWayComplementation_single_edge_base
import Theorems.Thm_OAI_TwoWayComplementation_smaller_relation_instance

-- ---- from OAI.Combinatorics.TwoWayAutomata.Amplification ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Removing the hub leaves exactly the desired pair between its two neighbours. -/
theorem hub_pair_relation {H : Type*} (u v z : H) (huz : u ≠ z) (hvz : v ≠ z) :
    restrictedIdentity {x | x ≠ z} ○ (SetRel.id ∪ {(u, z)}) ○
      (SetRel.id ∪ {(z, v)}) ○ restrictedIdentity {x | x ≠ z} =
        restrictedIdentity {x | x ≠ z} ∪ {(u, v)} := by
  ext ⟨a, b⟩
  simp only [SetRel.comp, Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff,
    SetRel.id, restrictedIdentity, Prod.mk.injEq]
  aesop

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.Retained ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Identity sandwiches restrict exactly the two endpoints. -/
theorem mem_restricted_sandwich {H : Type*} (F : Set H) (R : SetRel H H) (a b : H) :
    (a, b) ∈ restrictedIdentity F ○ R ○ restrictedIdentity F ↔
      a ∈ F ∧ b ∈ F ∧ (a, b) ∈ R := by
  simp only [SetRel.comp, restrictedIdentity, Set.mem_ofPred_eq]
  aesop

/-- Before its turn, the selected pair is absent from the retained restriction. -/
theorem retained_relation_identity {H : Type*} (U V F : Set H) (z x y : H)
    (hz : z ∉ F) (hx : ∀ a ∈ U, a ∈ F → a = x) (hy : ∀ b ∈ V, b ∈ F → b = y)
    (E : SetRel H H) (hE : E ⊆ U ×ˢ V) (hnew : (x, y) ∉ E) :
    restrictedIdentity F ○ (restrictedIdentity {a | a ≠ z} ∪ E) ○ restrictedIdentity F =
      restrictedIdentity F := by
  ext ⟨a, b⟩
  rw [mem_restricted_sandwich]
  constructor
  · rintro ⟨ha, hb, hid | hedge⟩
    · exact ⟨hid.1, ha⟩
    · exact (hnew (by simpa only [hx a (hE hedge).1 ha, hy b (hE hedge).2 hb] using hedge)).elim
  · rintro ⟨rfl, ha⟩
    exact ⟨ha, ha, Or.inl ⟨rfl, fun h => hz (h ▸ ha)⟩⟩

/-- At its turn, restriction adds precisely the selected pair to the retained identity. -/
theorem retained_relation_pair {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : restrictedIdentity F ○ P ○ restrictedIdentity F = restrictedIdentity F)
    (x y : H) (hx : x ∈ F) (hy : y ∈ F) :
    restrictedIdentity F ○ (P ∪ {(x, y)}) ○ restrictedIdentity F =
      restrictedIdentity F ∪ {(x, y)} := by
  rw [relComp_union, union_relComp, hP]
  congr 1
  ext ⟨a, b⟩
  rw [mem_restricted_sandwich]
  simp only [Set.mem_singleton_iff, Prod.mk.injEq]
  aesop

/-- The target doubles whenever the induction removes 127 points. -/
theorem lossBound_step {h : ℕ} (hh : 129 ≤ h) : lossBound h = 2 * lossBound (h - 127) := by
  have hexp : (h - 2) / 127 = (h - 127 - 2) / 127 + 1 := by omega
  simp only [lossBound, hexp, pow_succ, Nat.mul_comm]

/-- The numerical conclusion of summing the 4096 inductive lower bounds. -/
theorem amplification_arithmetic {h c : ℕ} (hh : 129 ≤ h) (δ : Fin 4096 → ℕ)
    (htotal : ∑ j, δ j ≤ 1024 * c)
    (hstep : ∀ j, lossBound (h - 127) ≤ 2 * δ j) : lossBound h ≤ c := by
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 4096))) => hstep j)
  have hbound : 4096 * lossBound (h - 127) ≤ 2 * ∑ j, δ j := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← Finset.mul_sum] using hsum
  rw [lossBound_step hh]
  omega

/-- Every positive power of a sandwich is absorbed by its idempotent outer factor. -/
theorem sandwich_power_absorption {A : Type*} [Monoid A] (b a : A)
    (hb : IsIdempotentElem b) (k : ℕ) :
    b * (b * a * b) ^ (k + 1) = (b * a * b) ^ (k + 1) ∧
      (b * a * b) ^ (k + 1) * b = (b * a * b) ^ (k + 1) := by
  have hl : b * (b * a * b) = b * a * b := by rw [← mul_assoc, ← mul_assoc, hb.eq]
  have hr : b * a * b * b = b * a * b := by rw [mul_assoc, hb.eq]
  induction k with
  | zero => simpa using And.intro hl hr
  | succ k ih =>
    constructor
    · rw [pow_succ, ← mul_assoc, ih.1]
    · rw [pow_succ, mul_assoc, hr]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.ImageBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace TwoWayComplementation

universe u v

open scoped SetRel

/-- Exponential cost of a single edge for every finite source monoid and label type. -/
theorem single_edge_cost (h : ℕ) :
    ∀ {A : Type u} {H : Type v} [Monoid A] [Finite A] [Finite H] {m : ℕ},
      Nat.card H = h → 2 ≤ h →
      ∀ (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H), Function.Surjective φ →
      (∀ a b, (ι a, ι b) ∈ Diagram.inclusion m → (φ b).toRel ⊆ (φ a).toRel) →
      (∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val) →
      ∀ a, IsIdempotentElem a → ∀ x y : H, x ≠ y →
      (φ a).toRel = SetRel.id ∪ {(x, y)} →
      lossBound h ≤ ((ι 1).missing (ι a)).ncard := by
  classical
  induction h using Nat.strong_induction_on with
  | h h ih =>
    intro A H _ _ _ m hH hh ι φ hφ hreverse hlift a ha x y hxy himage
    by_cases hsmall : h ≤ 128
    · simpa only [hH] using single_edge_base ι φ hreverse a x y hxy himage (by omega)
    have hlarge : 129 ≤ h := by omega
    obtain ⟨u, v, z, huv, huz, hvz⟩ := exists_hub_families (H := H) (by omega)
    choose s hs hsimage hscost using fun i =>
      pair_conjugate ι φ hlift a ha x y hxy himage (u i) z (huz i)
    choose s' hs' hsimage' hscost' using fun j =>
      pair_conjugate ι φ hlift a ha x y hxy himage z (v j) (hvz j).symm
    let f : Bool × Fin 64 → A := fun p => if p.1 then s' p.2 else s p.2
    let c := ((ι 1).missing (ι a)).ncard
    have hcost (p : Bool × Fin 64) : ((ι 1).missing (ι (f p))).ncard ≤ 2 * c := by
      obtain ⟨b, i⟩ := p
      cases b
      · exact hscost i
      · exact hscost' i
    let T : Set H := {w | w ≠ z}
    let P0 := restrictedIdentity T
    have hP0 : IsIdempotentElem (RelationMonoid.ofRel P0) :=
      RelationMonoid.ext (restrictedIdentity_comp_self T)
    obtain ⟨b0, hb0, hb0image, _⟩ := minimal_idempotent_lift φ.toMulHom hφ
      (RelationMonoid.ofRel P0) hP0
    have hφb0 : (φ b0).toRel = P0 := congrArg RelationMonoid.toRel hb0image
    obtain ⟨J0, _, hJcard, hJ⟩ := common_pair_budget ι f b0 hb0 hcost
    let index : Fin 4096 ≃ Fin 64 × Fin 64 := (finProdFinEquiv (m := 64) (n := 64)).symm
    let edge : Fin 4096 → H × H := fun r => (u (index r).1, v (index r).2)
    have hedgeinj : Function.Injective edge := by
      intro r s h
      apply index.injective
      exact Prod.ext (u.injective (congrArg Prod.fst h)) (v.injective (congrArg Prod.snd h))
    let E (j : ℕ) : SetRel H H := edge '' {r : Fin 4096 | r.val < j}
    let P (j : ℕ) := P0 ∪ E j
    let U := Set.range u
    let V := Set.range v
    have hUV : Disjoint U V := by
      apply Set.disjoint_left.mpr
      rintro w ⟨i, rfl⟩ ⟨j, heq⟩
      exact huv i j heq.symm
    have hUT : U ⊆ T := by rintro w ⟨i, rfl⟩; exact huz i
    have hVT : V ⊆ T := by rintro w ⟨j, rfl⟩; exact hvz j
    have hE (j : ℕ) : E j ⊆ U ×ˢ V := by
      rintro _ ⟨r, _, rfl⟩
      exact ⟨⟨(index r).1, rfl⟩, ⟨(index r).2, rfl⟩⟩
    have he (r : Fin 4096) : {edge r} ⊆ U ×ˢ V := by
      rintro w rfl
      exact ⟨⟨(index r).1, rfl⟩, ⟨(index r).2, rfl⟩⟩
    have hnew (r : Fin 4096) : edge r ∉ E r.val := by
      rintro ⟨s, hs, heq⟩
      change s.val < r.val at hs
      exact (hedgeinj heq ▸ hs).false
    have hEsucc (r : Fin 4096) : E (r.val + 1) = E r.val ∪ {edge r} := by
      have hidx : {s : Fin 4096 | s.val < r.val + 1} =
          {s : Fin 4096 | s.val < r.val} ∪ {r} := by
        ext s
        simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
        constructor
        · intro hs
          by_cases hlt : s.val < r.val
          · exact Or.inl hlt
          · exact Or.inr (Fin.ext (by omega))
        · rintro (hlt | rfl) <;> omega
      change edge '' _ = _
      rw [hidx, Set.image_union, Set.image_singleton]
    have hPidemp (j : ℕ) : P j ○ P j = P j := by
      simpa only [P, Set.union_self] using
        bipartite_relation_comp T U V hUT hVT hUV (E j) (E j) (hE j) (hE j)
    let g (j : ℕ) : A := if hj : j < 4096 then
      b0 * s (index ⟨j, hj⟩).1 * s' (index ⟨j, hj⟩).2 * b0 else b0
    have hgimage (r : Fin 4096) : (φ (g r.val)).toRel = P0 ∪ {edge r} := by
      simp only [g, dite_eq_left r.isLt, map_mul, RelationMonoid.toRel_mul,
        hφb0, hsimage, hsimage']
      exact hub_pair_relation _ _ z (huz _) (hvz _)
    have hgbudget : ∀ j < 4096,
        ι (g j) ∈ (ι b0).corner ∧ (ι b0).missing (ι (g j)) ⊆ J0 := by
      intro j hj
      simp only [g, dite_eq_left hj]
      constructor
      · constructor
        · change ι b0 * ι _ = _
          rw [← map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, hb0.eq]
        · change ι _ * ι b0 = _
          rw [← map_mul, mul_assoc, hb0.eq]
      · exact hJ _ _
    obtain ⟨b, hbzero, hbidemp, hbpower, _, _, htotal⟩ :=
      exists_nested_chain ι b0 hb0 g J0 hgbudget
    have hbimage : ∀ j ≤ 4096, (φ (b j)).toRel = P j := by
      intro j
      induction j with
      | zero => intro _; simp [hbzero, hφb0, P, E]
      | succ j hj =>
        intro hjle
        let r : Fin 4096 := ⟨j, by omega⟩
        have hprev := hj (by omega)
        have hnext : φ (b j * g j * b j) = RelationMonoid.ofRel (P (j + 1)) := by
          apply RelationMonoid.ext
          rw [map_mul, map_mul, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul,
            hprev, hgimage r, RelationMonoid.toRel_ofRel]
          change (P0 ∪ E j) ○ (P0 ∪ {edge r}) ○ (P0 ∪ E j) = P0 ∪ E (j + 1)
          rw [bipartite_relation_comp T U V hUT hVT hUV _ _ (hE j) (he r)]
          rw [bipartite_relation_comp T U V hUT hVT hUV _ _
            (Set.union_subset (hE j) (he r)) (hE j)]
          rw [show E (j + 1) = E j ∪ {edge r} from hEsucc r]
          rw [Set.union_right_comm (E j) {edge r} (E j), Set.union_self]
        obtain ⟨n, hn⟩ := hbpower j
        rw [hn, map_pow, hnext]
        have hi : IsIdempotentElem (RelationMonoid.ofRel (P (j + 1))) :=
          RelationMonoid.ext (hPidemp (j + 1))
        rw [hi.pow_succ_eq, RelationMonoid.toRel_ofRel]
    let δ (r : Fin 4096) := ((ι (b r.val)).missing (ι (b (r.val + 1)))).ncard
    have hsum : ∑ r, δ r ≤ 1024 * c := by
      have heq : ∑ r, δ r =
          ∑ j ∈ Finset.range 4096, ((ι (b j)).missing (ι (b (j + 1)))).ncard := by
        exact Fin.sum_univ_eq_sum_range
          (fun j => ((ι (b j)).missing (ι (b (j + 1)))).ncard) 4096
      rw [heq]
      omega
    apply amplification_arithmetic hlarge δ hsum
    intro r
    obtain ⟨F, hFcard, hxF, hyF, hzF, hUF, hVF⟩ := retained_pair_set U V
      (by simpa [U] using Set.ncard_range_of_injective u.injective)
      (by simpa [V] using Set.ncard_range_of_injective v.injective) hUV z
      (edge r).1 (edge r).2
      (by rintro ⟨i, hi⟩; exact huz i hi)
      (by rintro ⟨j, hj⟩; exact hvz j hj)
      ⟨(index r).1, rfl⟩ ⟨(index r).2, rfl⟩
    have hrestrict : restrictedIdentity F ○ (φ (b r.val)).toRel ○ restrictedIdentity F =
        restrictedIdentity F := by
      rw [hbimage _ r.isLt.le]
      exact retained_relation_identity U V F z _ _ hzF hUF hVF (E r.val) (hE r.val) (hnew r)
    have hrestrict' : restrictedIdentity F ○ (φ (b (r.val + 1))).toRel ○
        restrictedIdentity F = restrictedIdentity F ∪ {edge r} := by
      rw [hbimage _ r.isLt, show P (r.val + 1) = P r.val ∪ {edge r} from
        (congrArg (P0 ∪ ·) (hEsucc r)).trans (Set.union_assoc _ _ _).symm]
      have hp : restrictedIdentity F ○ P r.val ○ restrictedIdentity F = restrictedIdentity F := by
        rwa [hbimage _ r.isLt.le] at hrestrict
      exact retained_relation_pair (P r.val) F hp _ _ hxF hyF
    obtain ⟨n, hn⟩ := hbpower r.val
    have habsorb := sandwich_power_absorption (b r.val) (g r.val) (hbidemp r.val) n
    rw [← hn] at habsorb
    obtain ⟨d, hd, ψ, hψ, hliftψ, hψrel, w, hw, hwimage, hwcost⟩ :=
      smaller_relation_instance ι φ hφ (b r.val) (b (r.val + 1)) (hbidemp r.val)
        habsorb.1 habsorb.2 F hrestrict ⟨(edge r).1, hxF⟩ ⟨(edge r).2, hyF⟩ hrestrict'
    let ιb : (hbidemp r.val).Corner →ₙ* Diagram m := ι.comp (MulMemClass.subtype _)
    let ιd : hd.Corner →ₙ* Diagram m := ιb.comp (MulMemClass.subtype _)
    have hreverseψ : ∀ s t, (ιd s, ιd t) ∈ Diagram.inclusion m →
        (ψ t).toRel ⊆ (ψ s).toRel := by
      intro s t hst
      rw [hψrel, hψrel]
      exact fun _ hp => hreverse s.val.val t.val.val hst hp
    have hlow := ih (h - 127) (by omega) (A := hd.Corner) (H := F)
      (by omega) (by omega) ιd ψ hψ hreverseψ hliftψ w hw
      ⟨(edge r).1, hxF⟩ ⟨(edge r).2, hyF⟩
      (fun heq => huv (index r).1 (index r).2 (congrArg Subtype.val heq)) hwimage
    exact hlow.trans hwcost

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution.{u,v} : type_of% @_root_.OAI.TwoWayComplementation.single_edge_cost.{u,v} := @_root_.OAI.TwoWayComplementation.single_edge_cost.{u,v}
