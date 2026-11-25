-- Prove2me | solution 1 for GlobalTheory.WeilPullNoncomm.tval_manyChart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:11:59.815505+00:00
-- url     : https://prove2.me/submissions/3c271886-ef02-48ae-aca5-915cd14d495d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NotWeilIsGrpPullback
import Theorems.Thm_GlobalTheory_WeilPullNoncomm_gm_manyChart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilPullNoncomm
open GlobalTheory.CommPairing
variable {S : Scheme.{0}} {G : Over S} [GrpObj G]
namespace GlobalTheory.WeilPullNoncomm
theorem _root_.solution {κ : Type} (v : κ → Γ(G.left, ⊤)ˣ) {k : ℤ} {T : Over S} (θ : ThetaGrp G (manyChart v) k T)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ G).left) (z : Z) (J J' : (Z ⟶ G.left) → κ) :
    tval θ r z J = ((gm (r ≫ (snd T G).left) z ⊤ (v (J (r ≫ (snd T G).left))) *
        (gm (r ≫ (snd T G).left) z ⊤ (v (J' (r ≫ (snd T G).left))))⁻¹) ^ k *
      (gm (r ≫ (translPt G θ.pt).left) z ⊤ (v (J (r ≫ (translPt G θ.pt).left))) *
        (gm (r ≫ (translPt G θ.pt).left) z ⊤ (v (J' (r ≫ (translPt G θ.pt).left))))⁻¹) ^ (-k)) * tval θ r z J' := by
  have hJ : ∀ J, Good (manyChart v) z J := fun _ _ => trivial
  refine (gen_trans (φ := ![(snd T G).left, (translPt G θ.pt).left]) (ε := ![k, -k]) θ.isGen r z
    ((hJ J).mem _ r) ((hJ J').mem _ r)).trans ?_
  congr 1
  refine (Finset.prod_congr rfl fun i _ => congrArg (· ^ _) (gm_manyChart v _ z _ _)).trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
end GlobalTheory.WeilPullNoncomm
