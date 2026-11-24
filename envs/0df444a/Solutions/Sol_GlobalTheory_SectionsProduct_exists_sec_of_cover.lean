-- Prove2me | solution 1 for GlobalTheory.SectionsProduct.exists_sec_of_cover
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:39:04.206186+00:00
-- url     : https://prove2.me/submissions/6409996b-4fbc-4593-a58b-6fcd0bcb237c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MemRangeRTensorOfForallDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SectionLinCombFiberProductSeparated
import Theorems.Thm_GlobalTheory_SectionsProduct_gs_g
import Theorems.Thm_GlobalTheory_KuennethOne_glue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.SectionsProduct
open GlobalTheory.KuennethOne
variable {B Y T S X₁ X₂ W : Scheme.{0}} {L : LB B} {K : Type} [Fintype K]
namespace GlobalTheory.SectionsProduct
theorem _root_.solution (hL : L.IsLB) (φ : K → (Y ⟶ B)) (ε : K → ℤ) {P : Type} (U : P → Y.Opens)
    (j : P → K → L.ι) (hU : ∀ p, U p ≤ LB.wchart L φ (j p)) (hc : ∀ y, ∃ p, y ∈ U p) (a : ∀ p, Γ(Y, U p))
    (ha : ∀ p p' y, y ∈ U p → y ∈ U p' → gs (𝟙 Y) y (U p) (a p) =
      (trF φ ε (𝟙 Y) y (j p) (j p')).val * gs (𝟙 Y) y (U p') (a p')) :
    ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (T : Scheme.{0}) (r : T ⟶ Y) (z : T) (p : P) (k : K → L.ι), r z ∈ U p →
      r z ∈ LB.wchart L φ k →
      gs r z (LB.wchart L φ k) (s.f k) = (trF φ ε r z k (j p)).val * gs r z (U p) (a p) := by
  have gl : ∀ k : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ k), ∀ (T : Scheme.{0}) (r : T ⟶ Y) (z : T) (p : P), r z ∈ U p →
      r z ∈ LB.wchart L φ k → gs r z (LB.wchart L φ k) b = (trF φ ε r z k (j p)).val * gs r z (U p) (a p) := by
    intro k
    obtain ⟨u, hu⟩ : ∃ u : ∀ p, Γ(Y, LB.wchart L φ k ⊓ U p), ∀ (T : Scheme.{0}) (r : T ⟶ Y) (z : T) p,
        r z ∈ LB.wchart L φ k ⊓ U p →
        gs r z _ (u p) = (trF φ ε r z k (j p)).val * gs r z (U p) (a p) :=
      ⟨fun p => rs (inf_le_inf le_rfl (hU p) : LB.wchart L φ k ⊓ U p ≤ LB.wchart L φ k ⊓ LB.wchart L φ (j p))
          ((LB.LinComb L φ ε).g k (j p)).val * rs inf_le_right (a p),
        fun T r z p hz => (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
          ((gs_res r z _ hz _).trans (gs_g φ ε r z hz.1 (hU p hz.2))) (gs_res r z _ hz _))⟩
    obtain ⟨b, hb⟩ := glue (LB.wchart L φ k) (fun p => LB.wchart L φ k ⊓ U p) (fun p => inf_le_left)
      (fun y hy => by
        obtain ⟨p, hp⟩ := hc y
        exact Opens.mem_iSup.2 ⟨p, hy, hp⟩) u
      (fun p p' => fn_ext fun y hy => by
        refine (gs_res (𝟙 Y) y inf_le_left hy _).trans (Eq.trans ?_ (gs_res (𝟙 Y) y inf_le_right hy _).symm)
        rw [hu _ _ y p hy.1, hu _ _ y p' hy.2, ha p p' y hy.1.2 hy.2.2, ← _root_.mul_assoc, ← Units.val_mul,
          trF_trans hL φ ε (𝟙 Y) y hy.1.1 (hU p hy.1.2) (hU p' hy.2.2)])
    refine ⟨b, fun T r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L φ k ⊓ U p := ⟨h₂, h₁⟩
    exact (gs_res r z inf_le_left hz b).symm.trans ((congrArg (gs r z _) (hb p)).trans (hu T r z p hz))
  choose b hb using gl
  refine ⟨⟨b, fun k k' => fn_ext fun y hy => ?_⟩, fun T r z p k => hb k T r z p⟩
  obtain ⟨p, hp⟩ := hc y
  refine (gs_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·)
    (gs_g φ ε (𝟙 Y) y hy.1 hy.2) (gs_res (𝟙 Y) y _ hy _))).symm)
  refine (hb k _ (𝟙 Y) y p hp hy.1).trans (Eq.trans ?_ (congrArg _ (hb k' _ (𝟙 Y) y p hp hy.2)).symm)
  rw [← trF_trans hL φ ε (𝟙 Y) y hy.1 hy.2 (hU p hp), Units.val_mul, _root_.mul_assoc]
end GlobalTheory.SectionsProduct
