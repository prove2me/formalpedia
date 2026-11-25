-- Prove2me | solution 1 for GlobalTheory.ExpUniq.sval_eq_zero_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:29.915796+00:00
-- url     : https://prove2.me/submissions/8f529011-03ff-45b2-831f-5a590e50474b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_CancelSecAct
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_WeightedChartPullback_TorusInj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SecEqZeroAndHomEqOfThickenings
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalEqZeroOfWeightSum
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_of
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_TorusInj_eq_zero_of_sum


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ExpUniq
namespace GlobalTheory.ExpUniq
theorem _root_.solution {S B : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {L : LB B} (hL : L.IsLB)
    {K : Type} [Fintype K] (φ : X → K → (Y.left ⟶ B)) (ε : K → ℤ) (s : ∀ χ, LB.Sec (LB.LinComb L (φ χ) ε))
    (F : Finset X) (H : ∀ (w : (splitTorus S X ⊗ Y).left) J, Good L w J →
      ∑ χ ∈ F, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * sval (s χ) (snd (splitTorus S X) Y).left w J = 0)
    (α : X) (hα : α ∈ F) (y : Y.left) (J) (hJ : Good L y J) : sval (s α) (𝟙 _) y J = 0 := by
  classical
  let j : X → K → L.ι := fun β k => J (𝟙 _ ≫ φ β k)
  let V : Y.left.Opens := F.inf fun β => LB.wchart L (φ β) (j β)
  have hV : ∀ β ∈ F, V ≤ LB.wchart L (φ β) (j β) := fun β hβ => Finset.inf_le hβ
  have hy : y ∈ V := by
    have : ∀ (F' : Finset X), y ∈ F'.inf fun β => LB.wchart L (φ β) (j β) := fun F' => by
      induction F' using Finset.induction_on with
      | empty => trivial
      | insert a F' _ ih => rw [Finset.inf_insert]; exact ⟨hJ.mem (φ a) (𝟙 _), ih⟩
    exact this F
  have ex : ∀ β ∈ F, ∃ c : Γ(Y.left, V), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ Y.left) (z : Z),
      ρ z ∈ V → gs ρ z V c = gs ρ z (LB.wchart L (φ β) (j β)) ((s β).f (j β)) := fun β hβ =>
    ⟨_, fun Z ρ z hz => gs_res ρ z (hV β hβ) hz _⟩
  choose! c hc using ex
  let σ : Y ⟶ splitTorus S X ⊗ Y := lift 1 (𝟙 _)
  have hσ : σ.left ≫ (snd (splitTorus S X) Y).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h0 := TorusInj.eq_zero_of_sum X Y F c (fn_ext fun w hw => by
    obtain ⟨J', hJ', e⟩ := exists_good L hL w (K := F × K)
      (fun a => (snd (splitTorus S X) Y).left ≫ φ a.1.1 a.2) (fun a => j a.1.1 a.2)
      (fun a b e => by
        have := congrArg (σ.left ≫ ·) e
        simp only [← Category.assoc, hσ] at this
        exact congrArg J this)
      (fun a => Set.mem_iInter.1 (hV _ a.1.2 hw) a.2)
    have E := H w J' hJ'
    have hw' : (𝟙 (splitTorus S X ⊗ Y).left : _ ⟶ _) w ∈ (snd (splitTorus S X) Y).left ⁻¹ᵁ V := hw
    rw [gs_eq _ w _ hw', gs_eq _ w _ hw', map_zero, map_zero, map_sum, map_sum, ← E]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [← gs_eq _ w _ hw', gs_mul _ w _ hw', gs_res _ w _ hw', gs_pull (𝟙 _) (snd (splitTorus S X) Y).left w V hw, Category.id_comp,
      hc β hβ _ _ w hw, sval_of (s β) _ w J' (j β) (fun k => e (⟨β, hβ⟩, k))]) α hα
  have := hc α hα _ (𝟙 _) y hy
  rw [h0, gs_eq _ y V hy, map_zero, map_zero] at this
  exact this.symm
end GlobalTheory.ExpUniq
