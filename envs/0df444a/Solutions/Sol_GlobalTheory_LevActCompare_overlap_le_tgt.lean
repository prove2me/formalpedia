-- Prove2me | solution 1 for GlobalTheory.LevActCompare.overlap_le_tgt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:42:44.58867+00:00
-- url     : https://prove2.me/submissions/7e184eae-ccce-4272-8f7e-5f3bf5da3692

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelPairAction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevActCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelPairAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}
namespace GlobalTheory.LevActCompare
theorem _root_.solution {S : Type} [CommRing S] (φ : Xo.univ.t.G.left ⟶ Xo.univ.t.G.left) {x x' : Sp S ⟶ Xo.X}
    (pm : Gx x ⟶ Gx x')
    (hp : pm ≫ (snd (Over.mk x') Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ φ)
    (i j : Xo.univ.t.PP.L.ι) :
    (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ ((LB.div (Xo.univ.t.PP.L.pull φ) Xo.univ.t.PP.L).U ((fun _ => i), j)) ≤
      pm ⁻¹ᵁ (PPx x').U (fun _ => i) := by
  intro z hz
  have h1 : ((snd (Over.mk x) Xo.univ.t.G).left ≫ φ).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
    Set.mem_iInter.1 hz.1 PUnit.unit
  rw [← hp] at h1
  exact Set.mem_iInter.2 fun _ => h1
end GlobalTheory.LevActCompare
