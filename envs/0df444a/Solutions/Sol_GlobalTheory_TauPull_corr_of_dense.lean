-- Prove2me | solution 1 for GlobalTheory.TauPull.corr_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:49:48.557543+00:00
-- url     : https://prove2.me/submissions/3e9f4e66-61dc-4744-9b00-af3f3786c007

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Theorems.Thm_GlobalTheory_TauPull_gm_injective_of_dense
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_good
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TauPull
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
namespace GlobalTheory.TauPull
theorem _root_.solution {X Y Z : Scheme.{0}} [IsReduced Y] [X.IsSeparated] {L : LB X} (hL : L.IsLB)
    {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')} (h : Z ⟶ Y) (z : Z)
    (hd : ∀ V : Y.Opens, (V : Set Y).Nonempty → h z ∈ V)
    (H : ∀ J, Good L z J → val t h z J = val t' h z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  have dom : IsDominant h := ⟨dense_iff_inter_open.2 fun U hU hne => ⟨h z, hd ⟨U, hU⟩ hne, z, rfl⟩⟩
  refine unit_ext fun y hy => congrArg (gm (𝟙 Y) y _) ?_
  have hz : h z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hd _ ⟨y, hy⟩
  apply gm_injective_of_dense h z hd _ hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (Sum.elim (fun k => h ≫ φ k) (fun k => h ≫ φ' k)) (Sum.elim j j') (by
    rintro (a | a) (b | b) e
    exacts [c₁ a b (ext_of_isDominant h e), c₃ a b (ext_of_isDominant h e),
      (c₃ b a (ext_of_isDominant h e.symm)).symm, c₂ a b (ext_of_isDominant h e)]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz.1 a, Set.mem_iInter.1 hz.2 a])
  have := H J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  exact (gm_res _ z _ hz _).trans (this.trans (gm_res _ z _ hz _).symm)
end GlobalTheory.TauPull
