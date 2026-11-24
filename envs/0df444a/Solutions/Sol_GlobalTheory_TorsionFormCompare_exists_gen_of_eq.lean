-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.exists_gen_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:32:57.879942+00:00
-- url     : https://prove2.me/submissions/5e80fcba-7feb-4148-a0d9-fb69c3582268

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIdentityPullbackDegeneration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
namespace GlobalTheory.TorsionFormCompare
theorem _root_.solution {X Y : Scheme.{0}} (L : LB X) {p q : Y ⟶ X} (h : q = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => q) (fun _ => n)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι),
        gm r z (LB.wchart L (fun _ => q) j) (b.s j) = gm r z (LB.wchart L (fun _ => p) j) (a.s j)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  subst h
  exact ⟨a, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
end GlobalTheory.TorsionFormCompare
