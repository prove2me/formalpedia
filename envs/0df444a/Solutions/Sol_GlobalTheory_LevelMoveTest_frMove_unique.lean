-- Prove2me | solution 1 for GlobalTheory.LevelMoveTest.frMove_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:01:18.463778+00:00
-- url     : https://prove2.me/submissions/f887985a-eb23-4031-9389-d825b6b1cbfd

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_CarriedGeneratorUnique
import Theorems.Thm_GlobalTheory_LevelMoveTest_carried_generator_unique
import Theorems.Thm_GlobalTheory_LevActCompare_levelAction_overlap_le_source_chart


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
theorem _root_.solution {S : Type} [CommRing S] [Algebra c.F S] {ρ : Xo.X ⟶ Xo.X}
    (ν : SABMap Xo.univ.t Xo.univ.t ρ) (hw : ∀ w w', CubIso ν w → CubIso ν w' → w = w')
    (y y' y'' : FrPt Xo c S) (h' : FrMove ρ ν y y') (h'' : FrMove ρ ν y y'') : y' = y'' := by
  obtain ⟨x', o', u', t', e', b', s', g'⟩ := y'
  obtain ⟨x'', o'', u'', t'', e'', b'', s'', g''⟩ := y''
  obtain ⟨hx, hu, pm, w, hf, hs, hc, h⟩ := h'
  obtain ⟨hx2, hu2, pm2, w2, hf2, hs2, hc2, h2⟩ := h''
  dsimp only at hx hu hf hs h hx2 hu2 hf2 hs2 h2 pm pm2
  subst hx hx2
  obtain rfl := hw w w2 hc hc2
  have p2 : IsPullback (snd (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left (fst (Over.mk (y.x ≫ ρ)) Xo.univ.t.G).left
      Xo.univ.t.G.hom (y.x ≫ ρ) := (IsPullback.of_hasPullback (y.x ≫ ρ) Xo.univ.t.G.hom).flip
  obtain rfl : pm = pm2 := p2.hom_ext (hs.trans hs2.symm) (hf.trans hf2.symm)
  obtain rfl : u' = u'' := by funext τ i; rw [hu, hu2]
  have hs' : s' = s'' := by
    have key := carried_generator_unique ν y.x pm hf hs s' s'' (fun i j W hW h₁ => by
      subst hW
      exact (h i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).trans
        (h2 i j _ rfl le_rfl h₁ (GlobalTheory.LevActCompare.levelAction_overlap_le_source_chart ν.cm.F y.x i j)).symm)
    obtain ⟨f', c'⟩ := s'
    obtain ⟨f'', c''⟩ := s''
    obtain rfl : f' = f'' := by
      funext i
      have : i = fun _ => i 0 := funext fun k => congrArg i (Subsingleton.elim _ _)
      rw [this]
      exact key (i 0)
    rfl
  subst hs'
  rfl
end GlobalTheory.LevelMoveTest
