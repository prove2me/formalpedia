-- Prove2me | solution 1 for OAI.TwoWayComplementation.pair_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T09:59:37.536062+00:00
-- url     : https://prove2.me/submissions/b185f503-5625-4e11-b602-4589cc4efa97

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Amplification.lean:L149-L176
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.pair_conjugate. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_conjugate_missing_bound

-- ---- from OAI.Combinatorics.TwoWayAutomata.Amplification ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Permutation conjugation relabels both endpoints of every relation edge. -/
theorem permutation_conjugate_relation {H : Type*} (σ : Equiv.Perm H) (R : SetRel H H) :
    Function.graph σ ○ R ○ Function.graph σ.symm = {xy | (σ xy.1, σ xy.2) ∈ R} := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨c, ⟨d, had, hdc⟩, hcb⟩
    change σ a = d at had
    change σ.symm c = b at hcb
    have hc : c = σ b := by rw [← hcb, σ.apply_symm_apply]
    rwa [← had, hc] at hdc
  · intro hab
    exact ⟨σ b, ⟨σ a, rfl, hab⟩, σ.symm_apply_apply b⟩

/-- Unit lifts move the initial added pair to any other ordered pair of distinct points. -/
theorem pair_conjugate {A H : Type*} [Monoid A] {m : ℕ}
    (ι : A →ₙ* Diagram m) (φ : A →* RelationMonoid H)
    (hlift : ∀ σ : Equiv.Perm H, ∃ p : Aˣ, φ p = (permutationUnit σ).val)
    (a : A) (ha : IsIdempotentElem a) (x y : H) (hxy : x ≠ y)
    (himage : (φ a).toRel = SetRel.id ∪ {(x, y)}) (u v : H) (huv : u ≠ v) :
    ∃ s : A, IsIdempotentElem s ∧ (φ s).toRel = SetRel.id ∪ {(u, v)} ∧
      ((ι 1).missing (ι s)).ncard ≤ 2 * ((ι 1).missing (ι a)).ncard := by
  have hinj {r s : H} (hrs : r ≠ s) : Function.Injective (fun b : Bool => if b then s else r) := by
    intro b c h
    cases b <;> cases c <;> simp_all
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun b : Bool => if b then v else u) (fun b : Bool => if b then y else x)
    (hinj huv) (hinj hxy)
  have hσu : σ u = x := by simpa using hσ false
  have hσv : σ v = y := by simpa using hσ true
  obtain ⟨p, hp⟩ := hlift σ
  have hunit : Units.map φ p = permutationUnit σ := Units.ext hp
  have hinv : φ (↑p⁻¹ : A) = (↑(permutationUnit σ)⁻¹ : RelationMonoid H) :=
    congrArg (fun q : (RelationMonoid H)ˣ => (↑q⁻¹ : RelationMonoid H)) hunit
  refine ⟨p * a * (↑p⁻¹ : A), ?_, ?_, conjugate_missing_bound ι p a⟩
  · change (↑p * a * ↑p⁻¹) * (↑p * a * ↑p⁻¹) = ↑p * a * ↑p⁻¹
    simp only [mul_assoc, Units.inv_mul_cancel_left, ← mul_assoc a a, ha.eq]
  · rw [map_mul, map_mul, hp, hinv, RelationMonoid.toRel_mul, RelationMonoid.toRel_mul, himage]
    change Function.graph σ ○ (SetRel.id ∪ {(x, y)}) ○ Function.graph σ.symm = _
    rw [permutation_conjugate_relation, ← hσu, ← hσv]
    ext ⟨r, s⟩
    simp [SetRel.id, σ.injective.eq_iff]

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.pair_conjugate := @_root_.OAI.TwoWayComplementation.pair_conjugate
