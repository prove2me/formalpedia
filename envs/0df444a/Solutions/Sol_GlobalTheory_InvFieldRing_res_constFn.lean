-- Prove2me | solution 1 for GlobalTheory.InvFieldRing.res_constFn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:59:10.412751+00:00
-- url     : https://prove2.me/submissions/8a9336f0-e29b-4e3d-8f8b-59356eaafe09

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
theorem _root_.solution {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Sp R) {V W : Y.Opens} (h : W ≤ V) (a : R) :
    resG Y h (constFn f V a) = constFn f W a :=
  congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)
end GlobalTheory.InvFieldRing
