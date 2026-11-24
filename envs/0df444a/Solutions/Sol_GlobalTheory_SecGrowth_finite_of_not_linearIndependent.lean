-- Prove2me | solution 1 for GlobalTheory.SecGrowth.finite_of_not_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:37:26.944432+00:00
-- url     : https://prove2.me/submissions/93d1ce99-28b7-4d22-9325-4bc3f82b22dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
namespace GlobalTheory.SecGrowth
theorem _root_.solution {R V : Type} [CommRing R] (hR : IsField R) [AddCommGroup V] [Module R V]
    (n : ℕ) (h : ∀ b : Fin n → V, ¬ LinearIndependent R b) : Module.Finite R V := by
  letI := hR.toField
  haveI : Module.Free R V := Module.Free.of_divisionRing R V
  by_contra hV
  obtain ⟨b, hb⟩ := exists_linearIndependent_of_le_rank (R := R) (M := V) (n := n)
    ((Cardinal.natCast_lt_aleph0 (n := n)).le.trans (not_lt.1 fun hlt => hV (Module.rank_lt_aleph0_iff.1 hlt)))
  exact h b hb
end GlobalTheory.SecGrowth
