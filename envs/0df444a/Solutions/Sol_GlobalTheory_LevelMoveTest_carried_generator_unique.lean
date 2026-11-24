-- Prove2me | solution 1 for GlobalTheory.LevelMoveTest.carried_generator_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:59:26.328856+00:00
-- url     : https://prove2.me/submissions/131629fb-eb2c-4780-8e61-5eca1afc92e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_LevelGroupEqTopOfCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LevelActionOverlapLeSourceChart
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_CarriedGeneratorUnique
import Theorems.Thm_GlobalTheory_LevelMoveTest_pinned_isIso
import Theorems.Thm_GlobalTheory_LevActCompare_overlap_le_tgt


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
    (hs : pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left = (snd (Over.mk x) Xo.univ.t.G).left ≫ ν.φ)
    (s' s'' : LB.Sec (PPx (x ≫ ρ)))
    (h : ∀ (i j : Xo.univ.t.PP.L.ι) (W : (Gx x).Opens),
        W = (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j)) →
        ∀ (h₁ : W ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i)),
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s'.f (fun _ => i)) =
        (pm.appLE ((PPx (x ≫ ρ)).U (fun _ => i)) W h₁).hom (s''.f (fun _ => i)))
    (i : Xo.univ.t.PP.L.ι) : s'.f (fun _ => i) = s''.f (fun _ => i) := by
  haveI := pinned_isIso ν x pm hf hs
  have inj : Function.Injective (pm.app ((PPx (x ≫ ρ)).U (fun _ => i))).hom :=
    (ConcreteCategory.bijective_of_isIso (pm.app ((PPx (x ≫ ρ)).U (fun _ => i)))).1
  apply inj
  let W : Xo.univ.t.PP.L.ι → (Gx x).Opens := fun j => (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ
          ((LB.div (Xo.univ.t.PP.L.pull ν.cm.F) Xo.univ.t.PP.L).U ((fun _ => i), j))
  have hW : ∀ j, W j ≤ pm ⁻¹ᵁ (PPx (x ≫ ρ)).U (fun _ => i) := fun j =>
    GlobalTheory.LevActCompare.overlap_le_tgt ν.cm.F pm hs i j
  refine (Gx x).sheaf.eq_of_locally_eq' W _ (fun j => homOfLE (hW j)) ?_ _ _ ?_
  · intro z hz
    have hc : (snd (Over.mk x) Xo.univ.t.G).left.base z ∈ (⨆ j, Xo.univ.t.PP.L.U j) := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hc
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_, hj⟩
    refine Set.mem_iInter.2 fun _ => ?_
    have h1 : (pm ≫ (snd (Over.mk (x ≫ ρ)) Xo.univ.t.G).left).base z ∈ (Xo.univ.t.PP.L.U i : Set _) :=
      Set.mem_iInter.1 hz 0
    rw [hs] at h1
    exact h1
  · intro j
    exact h i j _ rfl (hW j)
end GlobalTheory.LevelMoveTest
