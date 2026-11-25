-- Prove2me | solution 1 for GroundTheory.ProfCoh.subsingleton_cohomology_of_primary_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:43:00.338822+00:00
-- url     : https://prove2.me/submissions/820b263a-65d7-4a41-a664-74304094f6d5

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_ColimitUnion
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_SubsingletonCohomologyOfPrimaryOfFinite
import Theorems.Thm_GroundTheory_ProfCoh_finite_sup_of_finite
import Theorems.Thm_GroundTheory_ProfCoh_exists_finite_stable_submodule
import Theorems.Thm_GroundTheory_ProfCoh_exists_cohomologyMap_subtype_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory Limits
universe u
attribute [local instance 2000] Rep.hV2
attribute [-instance] ULift.module
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GroundTheory.ProfCoh
theorem _root_.solution [CompactSpace G] {p : ℕ} (hp : 0 < p) {m : ℕ}
    (h : ∀ (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] [Finite A],
      (∀ a : A, ∃ k : ℕ, p ^ k • a = 0) → Subsingleton (cohomology A m))
    (A : Rep.{u} (ULift.{u} ℤ) G) [IsDiscreteRep A] (hA : ∀ a : A, ∃ k : ℕ, p ^ k • a = 0) :
    Subsingleton (cohomology A m) := by
  let ι := {W : Submodule (ULift.{u} ℤ) A // (∀ g, W ≤ W.comap (A.ρ g)) ∧ Finite W}
  let Wf : ι → Submodule (ULift.{u} ℤ) A := Subtype.val
  have hW : Monotone Wf := fun i j hij => hij
  have hstable : ∀ i g, Wf i ≤ (Wf i).comap (A.ρ g) := fun i => i.2.1
  have : Nonempty ι := ⟨⟨⊥, fun g => bot_le, inferInstance⟩⟩
  have : IsDirectedOrder ι := ⟨fun i j => by
    have := i.2.2
    have := j.2.2
    exact ⟨⟨i.1 ⊔ j.1, fun g => sup_le ((i.2.1 g).trans (Submodule.comap_mono le_sup_left))
      ((j.2.1 g).trans (Submodule.comap_mono le_sup_right)), finite_sup_of_finite _ _⟩,
      (le_sup_left : i.1 ≤ i.1 ⊔ j.1), (le_sup_right : j.1 ≤ i.1 ⊔ j.1)⟩⟩
  have hunion : ∀ a : A, ∃ i, a ∈ Wf i := fun a => by
    obtain ⟨W, h1, h2, h3⟩ := exists_finite_stable_submodule A hp hA a
    exact ⟨⟨W, h1, h2⟩, h3⟩
  suffices hz : ∀ x : cohomology A m, x = 0 from ⟨fun x y => by rw [hz x, hz y]⟩
  intro x
  obtain ⟨i, z, rfl⟩ := exists_cohomologyMap_subtype_eq A Wf hW hstable hunion m x
  have : Finite (A.subrepresentation (Wf i) (hstable i)) := i.2.2
  have hs := h (A.subrepresentation (Wf i) (hstable i)) (by
    rintro ⟨b, hb⟩
    obtain ⟨k, hk⟩ := hA b
    exact ⟨k, Subtype.ext hk⟩)
  rw [@Subsingleton.elim _ hs z 0, map_zero]
end GroundTheory.ProfCoh
