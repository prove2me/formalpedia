-- Prove2me | solution 1 for OAI.TwoWayComplementation.relation_corner_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:53:14.408356+00:00
-- url     : https://prove2.me/submissions/109f5cff-4191-4c93-8a7b-85ef8ae43aa7

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/RelationMonoid.lean:L157-L226
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.relation_corner_equiv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_RelationMonoid
import Theorems.Thm_OAI_TwoWayComplementation_relation_corner_inverse
import Theorems.Thm_OAI_TwoWayComplementation_relation_extend_comp

-- ---- from OAI.Combinatorics.TwoWayAutomata.RelationMonoid ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Restriction-corner identities.
    The supporting relation `i` can be any idempotent with `iPi = i`. -/
theorem relation_corner_identities {α : Type*} (P i : SetRel α α)
    (hP : P ○ P = P) (hiPi : i ○ P ○ i = i) :
    let Q := P ○ i ○ P
    Q ○ Q = Q ∧ P ○ Q = Q ∧ Q ○ P = Q ∧
    Q ○ i = P ○ i ∧ i ○ Q = i ○ P ∧ i ○ Q ○ i = i := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  dsimp
  simp [SetRel.comp_assoc, hPP, hiPiR, hP, hiPi]

/-- Extension preserves products on the supported relation corner. -/
theorem relation_corner_comp {α : Type*} (P i A B : SetRel α α)
    (hP : P ○ P = P) (hi : i ○ i = i) (hiPi : i ○ P ○ i = i)
    (hA : i ○ A ○ i = A) (hB : i ○ B ○ i = B) :
    (P ○ A ○ P) ○ (P ○ B ○ P) = P ○ (A ○ B) ○ P := by
  have hPP (R : SetRel α α) : P ○ (P ○ R) = P ○ R := by
    rw [← SetRel.comp_assoc, hP]
  have hiPiR (R : SetRel α α) : i ○ (P ○ (i ○ R)) = i ○ R := by
    rw [← SetRel.comp_assoc i P, ← SetRel.comp_assoc, hiPi]
  have hii (R : SetRel α α) : i ○ (i ○ R) = i ○ R := by
    rw [← SetRel.comp_assoc, hi]
  conv_lhs => rw [← hA, ← hB]
  simpa only [SetRel.comp_assoc, hPP, hiPiR, hii] using
    congrArg (fun R => P ○ R ○ P) (congrArg₂ SetRel.comp hA hB)

namespace RelationMonoid

end RelationMonoid

/-- Extending a relation on a subset and restricting it again loses no pairs. -/
theorem relation_extend_restrict {H : Type*} (F : Set H) (R : SetRel F F) :
    {xy : F × F | (xy.1.val, xy.2.val) ∈ (Prod.map Subtype.val Subtype.val) '' R} = R := by
  ext ⟨x, y⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.map_apply, Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, hab, hax, hby⟩
    exact (Subtype.ext hax ▸ Subtype.ext hby ▸ hab)
  · intro hxy
    exact ⟨x, y, hxy, rfl, rfl⟩

/-- Extension of restriction is precisely the identity sandwich on the subset. -/
theorem relation_restrict_extend {H : Type*} (F : Set H) (R : SetRel H H) :
    (Prod.map Subtype.val Subtype.val) '' {xy : F × F | (xy.1.val, xy.2.val) ∈ R} =
      restrictedIdentity F ○ R ○ restrictedIdentity F := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, Prod.exists, Set.mem_ofPred_eq, Prod.map_apply, Prod.mk.injEq,
    SetRel.comp, restrictedIdentity]
  constructor
  · rintro ⟨a, b, hab, rfl, rfl⟩
    exact ⟨b.val, ⟨a.val, ⟨rfl, a.property⟩, hab⟩, rfl, b.property⟩
  · rintro ⟨b, ⟨a, ⟨rfl, hx⟩, hab⟩, rfl, hy⟩
    exact ⟨⟨x, hx⟩, ⟨b, hy⟩, hab, rfl, rfl⟩

/-- The full relation monoid on a subset is the compressed relation corner. -/
theorem relation_corner_equiv {H : Type*} (P : SetRel H H) (F : Set H)
    (hP : P ○ P = P) (hiPi : restrictedIdentity F ○ P ○ restrictedIdentity F =
      restrictedIdentity F) :
    ∃ hQ : IsIdempotentElem (RelationMonoid.ofRel (P ○ restrictedIdentity F ○ P)),
      ∃ ρ : hQ.Corner ≃* RelationMonoid F,
        ∀ Z, (ρ Z).toRel = {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel} := by
  let i := restrictedIdentity F
  let Q := P ○ i ○ P
  have hQ : IsIdempotentElem (RelationMonoid.ofRel Q) :=
    RelationMonoid.ext (relation_corner_identities P i hP hiPi).1
  have hZ (Z : hQ.Corner) : Q ○ Z.val.toRel ○ Q = Z.val.toRel := by
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp Z.property
    exact congrArg RelationMonoid.toRel ((congrArg (· * RelationMonoid.ofRel Q) hl).trans hr)
  let extend (A : RelationMonoid F) : SetRel H H :=
    (Prod.map Subtype.val Subtype.val) '' A.toRel
  have hsupp (A : RelationMonoid F) : i ○ extend A ○ i = extend A := by
    rw [← relation_restrict_extend F, relation_extend_restrict]
  let f (Z : hQ.Corner) : RelationMonoid F :=
    .ofRel {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel}
  let g (A : RelationMonoid F) : hQ.Corner :=
    ⟨.ofRel (P ○ extend A ○ P), (Subsemigroup.mem_corner_iff hQ).mpr (by
      have hs := (relation_corner_inverse P i hP hiPi).2 (extend A) (hsupp A) |>.1
      change Q ○ (P ○ extend A ○ P) ○ Q = P ○ extend A ○ P at hs
      have hQQ : Q ○ Q = Q := (relation_corner_identities P i hP hiPi).1
      constructor <;> apply RelationMonoid.ext
      · change Q ○ (P ○ extend A ○ P) = P ○ extend A ○ P
        conv_lhs => rw [← hs]
        simpa only [← SetRel.comp_assoc, hQQ] using hs
      · change (P ○ extend A ○ P) ○ Q = P ○ extend A ○ P
        conv_lhs => rw [← hs]
        simpa only [SetRel.comp_assoc, hQQ] using hs)⟩
  have hleft (Z : hQ.Corner) : g (f Z) = Z := by
    apply Subtype.ext
    apply RelationMonoid.ext
    change P ○ ((Prod.map Subtype.val Subtype.val) ''
      {xy : F × F | (xy.1.val, xy.2.val) ∈ Z.val.toRel}) ○ P = Z.val.toRel
    rw [relation_restrict_extend]
    exact (relation_corner_inverse P i hP hiPi).1 _ (hZ Z)
  have hright (A : RelationMonoid F) : f (g A) = A := by
    apply RelationMonoid.ext
    have hext : extend (f (g A)) = extend A := by
      change (Prod.map Subtype.val Subtype.val) '' {xy : F × F |
        (xy.1.val, xy.2.val) ∈ P ○ extend A ○ P} = extend A
      rw [relation_restrict_extend]
      exact (relation_corner_inverse P i hP hiPi).2 (extend A) (hsupp A) |>.2
    have hinj : Function.Injective
        (Prod.map (Subtype.val : F → H) (Subtype.val : F → H)) :=
      fun _ _ h => Prod.ext (Subtype.ext (congrArg Prod.fst h))
        (Subtype.ext (congrArg Prod.snd h))
    exact Set.image_injective.mpr hinj hext
  have hgmul (A B : RelationMonoid F) : g (A * B) = g A * g B := by
    apply Subtype.ext
    apply RelationMonoid.ext
    change P ○ extend (A * B) ○ P = (P ○ extend A ○ P) ○ (P ○ extend B ○ P)
    have hext : extend (A * B) = extend A ○ extend B := relation_extend_comp F _ _
    rw [hext]
    exact (relation_corner_comp P i _ _ hP (restrictedIdentity_comp_self F)
      hiPi (hsupp A) (hsupp B)).symm
  let ρ : hQ.Corner ≃* RelationMonoid F :=
    { toFun := f
      invFun := g
      left_inv := hleft
      right_inv := hright
      map_mul' := by
        intro Z W
        apply_fun g
        · rw [hgmul, hleft, hleft, hleft]
        · exact Function.LeftInverse.injective hright }
  exact ⟨hQ, ρ, fun _ => rfl⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.relation_corner_equiv := @_root_.OAI.TwoWayComplementation.relation_corner_equiv
