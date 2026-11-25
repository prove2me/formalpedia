-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.constFn_eps_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:01:30.813358+00:00
-- url     : https://prove2.me/submissions/5171f5d0-a998-4d8e-9e4f-101b84e88503

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SurjectiveSpMapFst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
noncomputable section
open GlobalTheory GlobalTheory.InvFieldRing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.InvFieldRing
theorem _root_.solution {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Sp (DualNumber R)) (O : Y.Opens) :
    constFn p O DualNumber.eps * constFn p O DualNumber.eps = 0 := by
  simp only [constFn, ← map_mul, DualNumber.eps_mul_eps, map_zero]
end GlobalTheory.InvFieldRing
