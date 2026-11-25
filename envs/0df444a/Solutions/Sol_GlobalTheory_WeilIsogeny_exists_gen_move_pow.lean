-- Prove2me | solution 1 for GlobalTheory.WeilIsogeny.exists_gen_move_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:01:34.844385+00:00
-- url     : https://prove2.me/submissions/748de4e6-4fdf-40e2-a3d6-48218a1a8762

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_GenMove
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenMovePow
import Theorems.Thm_GlobalTheory_WeilIsogeny_exists_gen_of_lbPow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linComb_isLB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_exists_gen_move


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilIsogeny
open CommutatorPairing
variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
namespace GlobalTheory.WeilIsogeny
theorem _root_.solution {X₀ Y₀ : Scheme.{0}} {M : LB X₀} {F : X ⟶ X₀} (hL : L.IsLB) (hM : M.IsLB) {d : ℕ}
    (w : LB.Iso (lbPow L d) (M.pull F)) (hw : w.IsGen) (hε : ∀ k, ε' k = ε k * d) {φ₀ : K → (Y₀ ⟶ X₀)} (h : Y ⟶ Y₀)
    (hc : ∀ k, φ k ≫ F = h ≫ φ₀ k) (t : LB.Gen (LB.LinComb M φ₀ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L φ ε'), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J₀),
      Good L z J → Good M z J₀ → val t (r ≫ h) z J₀ =
        (∏ k, (fun χ : Z ⟶ X => gw w χ z (J₀ (χ ≫ F)) (fun _ => J χ)) (r ≫ φ k) ^ ε k) * val u r z J := by
  obtain ⟨b, hb, hm⟩ := H1.exists_gen_move hM (DVR.linComb_isLB L hL _ _) w ((isGen_iff w).1 hw) φ₀ φ ε h hc t ht
  obtain ⟨u, hu, hv⟩ := exists_gen_of_lbPow d hε b hb
  refine ⟨u, hu, fun Z r z J J₀ hJ hJ₀ => ?_⟩
  have m := hm _ r z (fun i => J₀ ((r ≫ φ i) ≫ F)) (fun i _ => J (r ≫ φ i))
    (fun i => hJ₀ ((r ≫ φ i) ≫ F)) (fun i => Set.mem_iInter.2 fun _ => hJ (r ≫ φ i))
  exact (val_of t _ z J₀ _ (fun i => congrArg J₀ (by rw [Category.assoc, Category.assoc, hc]))).trans
    (m.trans (congrArg (_ * ·) (hv _ r z _ (hJ.mem φ r)).symm))
end GlobalTheory.WeilIsogeny
