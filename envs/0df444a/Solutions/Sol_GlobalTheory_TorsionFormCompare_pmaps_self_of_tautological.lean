-- Prove2me | solution 1 for GlobalTheory.TorsionFormCompare.pmaps_self_of_tautological
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:33:00.264527+00:00
-- url     : https://prove2.me/submissions/6f1daab2-b5fa-4514-b681-87d81f34bc50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PullPointIdentityDegeneration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]
end GlobalTheory.TorsionFormCompare
