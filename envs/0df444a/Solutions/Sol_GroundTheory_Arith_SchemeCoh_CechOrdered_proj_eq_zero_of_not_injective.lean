-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechOrdered.proj_eq_zero_of_not_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:37.439852+00:00
-- url     : https://prove2.me/submissions/9c4164f9-3ce0-425a-a5e5-ebe69bce811c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechOrdered

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u
open GroundTheory.Arith.SchemeCoh.CechOrdered
variable (ι : Type w)
variable {ι}
variable [LinearOrder ι]
namespace GroundTheory.Arith.SchemeCoh.CechOrdered
theorem _root_.solution (q : ℕ) (i : Fin (q + 1) → ι)
    (hi : ¬ Function.Injective i) : proj q i = 0 := by
  classical
  ext t
  by_contra h
  obtain ⟨hts, htr⟩ := proj_supp q i t h
  have h1 : (Finset.univ.image t).card ≤ (Finset.univ.image i).card :=
    Finset.card_le_card fun x hx => by
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b, hb⟩ := htr a
      exact Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩
  rw [Finset.card_image_of_injective _ hts.injective, Finset.card_univ, Fintype.card_fin] at h1
  have h2 : (Finset.univ.image i).card = (Finset.univ : Finset (Fin (q + 1))).card :=
    le_antisymm Finset.card_image_le (by rw [Finset.card_univ, Fintype.card_fin]; exact h1)
  exact hi fun a b hab => Finset.card_image_iff.mp h2 (by simp) (by simp) hab
end GroundTheory.Arith.SchemeCoh.CechOrdered
