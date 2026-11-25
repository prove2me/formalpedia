-- Prove2me | solution 1 for GlobalTheory.Spread.fg_iSup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:30:02.715802+00:00
-- url     : https://prove2.me/submissions/91bacaeb-f762-445f-b6eb-04441b875db8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Spread
variable {k : Type} [CommRing k] {B Z : Scheme.{0}} (pB : B ⟶ Sp k)
variable (A : Type) [CommRing A] [Algebra k A]
variable {A} (pZ : Z ⟶ Sp k)
namespace GlobalTheory.Spread
theorem _root_.solution {ι : Type*} [Finite ι] {R : ι → Subalgebra k A} (hR : ∀ i, (R i).FG) :
    (⨆ i, R i).FG := by
  classical
  have := Fintype.ofFinite ι
  choose s hs using hR
  refine ⟨Finset.univ.biUnion s, ?_⟩
  simp only [Finset.coe_biUnion, Finset.mem_coe, Finset.mem_univ, Set.iUnion_true,
    Algebra.adjoin_iUnion, hs]
end GlobalTheory.Spread
