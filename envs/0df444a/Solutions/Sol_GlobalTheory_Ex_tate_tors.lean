-- Prove2me | solution 1 for GlobalTheory.Ex.tate_tors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:49.542002+00:00
-- url     : https://prove2.me/submissions/2cc7d4b3-1799-43c5-8805-07308e134123

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
namespace GlobalTheory.Ex
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (n : ℕ) : (tate q).toNumB.Tors n 0 where
  div x := ⟨x, rfl⟩
  str j := by
    haveI : Unique (tate q).A := inferInstanceAs (Unique PUnit)
    haveI : Unique (powMonoidHom (n ^ j) : (tate q).A →* (tate q).A).ker := ⟨⟨1⟩, fun _ => Subsingleton.elim _ _⟩
    haveI : IsEmpty (Fin (2 * 0)) := inferInstanceAs (IsEmpty (Fin 0))
    exact ⟨MulEquiv.ofUnique⟩
  nondeg _ _ _ _ := rfl
  good a := ⟨a, rfl, norm_one⟩
  sep _ _ _ _ _ _ _ := rfl
end GlobalTheory.Ex
