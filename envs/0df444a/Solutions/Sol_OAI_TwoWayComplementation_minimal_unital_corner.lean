-- Prove2me | solution 1 for OAI.TwoWayComplementation.minimal_unital_corner
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:11:42.831593+00:00
-- url     : https://prove2.me/submissions/39db9317-c3ce-4434-b3c3-160fa809d726

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/ImageBound.lean:L182-L209
-- (upload_full_project.md Phase 4): solution for node OAI.TwoWayComplementation.minimal_unital_corner. The node keeps its source
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
import Theorems.Thm_OAI_TwoWayComplementation_minimal_corner_reflects_units
import Theorems.Thm_OAI_TwoWayComplementation_minimal_idempotent_lift

-- ---- from OAI.Combinatorics.TwoWayAutomata.Corners ----
namespace OAI

namespace TwoWayComplementation

open scoped SetRel

theorem cornerMap_surjective {A M : Type*} [Semigroup A] [Semigroup M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) {d : A} {q : M}
    (hd : IsIdempotentElem d) (hq : IsIdempotentElem q) (hθd : θ d = q) :
    Function.Surjective (cornerMap θ hd hq hθd) := by
  intro y
  obtain ⟨x, hx⟩ := hθ y.val
  refine ⟨⟨d * x * d, x, rfl⟩, ?_⟩
  apply Subtype.ext
  change θ (d * x * d) = y.val
  obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hq).mp y.property
  rw [map_mul, map_mul, hθd, hx, hl, hr]

end TwoWayComplementation

end OAI

-- ---- from OAI.Combinatorics.TwoWayAutomata.ImageBound ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace TwoWayComplementation

universe u v

open scoped SetRel

/-- A surjection has a unital identity corner with unit lifts for every target unit. -/
theorem minimal_unital_corner {A M : Type*} [Semigroup A] [Finite A] [Monoid M]
    (θ : A →ₙ* M) (hθ : Function.Surjective θ) :
    ∃ d : A, ∃ hd : IsIdempotentElem d, ∃ ψ : hd.Corner →* M,
      Function.Surjective ψ ∧ (∀ w, ψ w = θ w.val) ∧
      ∀ u : Mˣ, ∃ p : hd.Cornerˣ, ψ p = u.val := by
  have h1 : IsIdempotentElem (1 : M) := by simp [IsIdempotentElem]
  obtain ⟨d, hd, hθd, hminimal⟩ := minimal_idempotent_lift θ hθ 1 h1
  let ε : h1.Corner ≃* M :=
    { toFun := Subtype.val
      invFun := fun x => ⟨x, (Subsemigroup.mem_corner_iff h1).mpr ⟨one_mul x, mul_one x⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  let γ := cornerMap θ hd h1 hθd
  let ψ := ε.toMonoidHom.comp γ
  have hψ : Function.Surjective ψ :=
    ε.surjective.comp (cornerMap_surjective θ hθ hd h1 hθd)
  refine ⟨d, hd, ψ, hψ, fun _ => rfl, ?_⟩
  intro u
  obtain ⟨w, hw⟩ := hψ u.val
  have hu : IsUnit (ψ w) := hw.symm ▸ u.isUnit
  have hγ : IsUnit (γ w) := by
    have hu' := hu.map ε.symm.toMonoidHom
    simpa only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply] using hu'
  obtain ⟨p, hp⟩ := minimal_corner_reflects_units θ hd h1 hθd hminimal w hγ
  exact ⟨p, hp ▸ hw⟩

end TwoWayComplementation

end OAI

-- ---- platform node ----
open OAI OAI.TwoWayComplementation
open scoped SetRel


theorem solution : type_of% @_root_.OAI.TwoWayComplementation.minimal_unital_corner := @_root_.OAI.TwoWayComplementation.minimal_unital_corner
