-- Prove2me | solution 1 for GlobalTheory.PsiSpread.exists_extends
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:28:58.549202+00:00
-- url     : https://prove2.me/submissions/73d3d2d5-9ee4-4ba3-a721-588498ce5b65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsFiniteCubeInduction
import Theorems.Thm_GlobalTheory_PsiSpread_exists_gen_of_chart
import Theorems.Thm_GlobalTheory_PsiSpread_exists_unit_near
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


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
open GlobalTheory.PsiSpread
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace GlobalTheory.PsiSpread
theorem _root_.solution (χ : D.X) (z : (TK R).left) : ∃ V : (Spec (CommRingCat.of R)).Opens, jK R z ∈ V ∧
    ∀ W : (Spec (CommRingCat.of R)).Opens, W ≤ V → ∀ κ : TK R ⟶ TW W, Extends D κ χ := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R) (S := FractionRing R)
  have sub : Subsingleton (TK R).left := inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  obtain ⟨j, hj⟩ := exists_chart D.P.isLB (D.xK χ z)
  obtain ⟨U, u, hU, e⟩ := exists_unit_near (jK R) z
    (gm (𝟙 (TK R).left) z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j)) ((D.psi χ).s (fun _ => j)))
  refine ⟨U ⊓ (D.c χ).left ⁻¹ᵁ D.P.L.U j, ⟨hU, hj⟩, fun W hW κ => ?_⟩
  have hκ : κ.left ≫ W.ι = jK R := Over.w κ
  obtain ⟨t, ht, vt⟩ := exists_gen_of_chart D.P.isLB (K := PUnit) (fun _ => (cP D (TW W) χ).left) (fun _ => -1)
    (fun _ => j) (fun y => Set.mem_iInter.2 fun _ => (hW y.2).2) (W.ι ⁻¹ᵁ U) (fun y => (hW y.2).1) (pullU W.ι U u)
  refine ⟨t, ht, fun z' J hJ => ?_⟩
  obtain rfl : z = z' := Subsingleton.elim _ _
  have q : κ.left ≫ (cP D (TW W) χ).left = 𝟙 _ ≫ D.xK χ :=
    (congrArg (fun q => q.left) (comp_cP D κ χ)).trans (Category.id_comp _).symm
  refine (vt _ κ.left z _ (hJ.mem _ _)).trans (Eq.trans ?_
    (gen_trans (D.psi_gen χ) (𝟙 _) z (j' := fun _ => j) (hJ.mem _ _) (Set.mem_iInter.2 fun _ => hj)).symm)
  refine congrArg₂ (· * ·) ?_ ((gm_pull κ.left W.ι z U (hW (κ.left z).2).1 u).trans (by rw [hκ]; exact e))
  exact congrArg (fun ψ => ∏ _k : PUnit.{1}, gm ψ z (D.P.L.U (J ψ) ⊓ D.P.L.U j) (D.P.L.g (J ψ) j) ^ (-1 : ℤ)) q
end GlobalTheory.PsiSpread
