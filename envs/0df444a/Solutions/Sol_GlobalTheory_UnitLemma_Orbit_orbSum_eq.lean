-- Prove2me | solution 1 for GlobalTheory.UnitLemma.Orbit.orbSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:58.103126+00:00
-- url     : https://prove2.me/submissions/d4fdbf17-3187-4e6f-8c55-07dc41d8ec8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit
open GlobalTheory.UnitLemma Polynomial IsLocalRing ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion
variable {K : UQ}
variable {O : Type} [CommRing O] {A A' : Type} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']
namespace GlobalTheory.UnitLemma.Orbit
theorem _root_.solution (G : Subgroup Aˣ) (X : Set (Submodule O A)) :
    orbSum O G X (fun _ => 1) = ∑ᶠ o, orbWt G X o := by
  unfold orbSum
  refine finsum_congr fun o => ?_
  conv_rhs => rw [← Quot.out_eq o]
  rw [one_mul]
  rfl
end GlobalTheory.UnitLemma.Orbit
