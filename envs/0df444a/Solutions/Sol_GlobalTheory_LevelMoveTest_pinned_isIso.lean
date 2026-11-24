-- Prove2me | solution 1 for GlobalTheory.LevelMoveTest.pinned_isIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:22.384118+00:00
-- url     : https://prove2.me/submissions/fb9882cc-52fb-41bc-83cf-f2c938ffc629

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_CarriedGeneratorUnique

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevelMoveTest
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group
namespace GlobalTheory.LevelMoveTest
theorem _root_.solution {S : Type} [CommRing S] {ρ : Xo.X ⟶ Xo.X} (ν : SABMap Xo.univ.t Xo.univ.t ρ)
    (x : Sp S ⟶ Xo.X) (pm : Gx x ⟶ Gx (x ≫ ρ))
    (hf : pm ≫ (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left)
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ) :
    IsIso pm := by
  have p1 : IsPullback (snd (Over.mk x) Xo.univ.t.G).left (fst (Over.mk x) Xo.univ.t.G).left Xo.univ.t.G.hom x :=
    (IsPullback.of_hasPullback x Xo.univ.t.G.hom).flip
  have p2 : IsPullback (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (x ≫ ρ)) Xo.univ.t.G).left
      Xo.univ.t.G.hom (x ≫ ρ) := (IsPullback.of_hasPullback (x ≫ ρ) Xo.univ.t.G.hom).flip
  have p3 := p1.paste_horiz ν.cart.1
  have : pm = (p3.isoIsPullback _ _ p2).hom := by
    apply p2.hom_ext
    · rw [hs]; simp
    · rw [hf]; simp
  rw [this]; infer_instance
end GlobalTheory.LevelMoveTest
