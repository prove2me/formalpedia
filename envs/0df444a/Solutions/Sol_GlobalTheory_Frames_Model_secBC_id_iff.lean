-- Prove2me | solution 1 for GlobalTheory.Frames.Model.secBC_id_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:55:23.455553+00:00
-- url     : https://prove2.me/submissions/2db6420e-de3f-422d-95f9-5898d3995995

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing
import Theorems.Thm_GlobalTheory_Frames_Model_spMap_id
import Theorems.Thm_GlobalTheory_Frames_Model_appLE_id_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.Frames.Model
theorem _root_.solution {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (a : S) (s s' : LB.Sec (PPx x)) :
    SecBC (RingHom.id S) a x x s s' ↔ ∀ i, s'.f i = scal x a i * s.f i := by
  have hid : (fst (Over.mk x) Xo.univ.t.G).left ≫ spMap (RingHom.id S) = (fst (Over.mk x) Xo.univ.t.G).left := by
    rw [spMap_id]
    exact Category.comp_id _

  have hpm : ∀ pm : Gx x ⟶ Gx x, pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left →
      pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left ≫ spMap (RingHom.id S) →
      pm = 𝟙 _ := by
    intro pm h₁ h₂
    rw [hid] at h₂
    exact pullback.hom_ext (h₂.trans (Category.id_comp _).symm) (h₁.trans (Category.id_comp _).symm)
  constructor
  · rintro ⟨pm, h₁, h₂, h₃⟩ i
    obtain rfl := hpm pm h₁ h₂
    exact ((appLE_id_apply _ _ _ _).symm.trans (h₃ i le_rfl)).symm
  · intro hs
    refine ⟨𝟙 _, Category.id_comp _, (Category.id_comp _).trans hid.symm, fun i h => ?_⟩
    exact (appLE_id_apply _ _ _ _).trans (hs i).symm
end GlobalTheory.Frames.Model
