-- Prove2me | solution 1 for GlobalTheory.FamIntAt.exists_psi_of_psiIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:12:02.74545+00:00
-- url     : https://prove2.me/submissions/d1aaa84d-bc3b-4d27-95ec-63b45dc58af5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsFamRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PsiInOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IntegralFamilyPrescribedTermUnitAtPrime
import Theorems.Thm_GlobalTheory_FamIntAt_exists_extend
import Theorems.Thm_GlobalTheory_FamIntAt_eq_genPt
import Theorems.Thm_GlobalTheory_PsiInPull_jK_mem
import Theorems.Thm_GlobalTheory_PsiInPull_mem_wchart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_genSec


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FamIntAt
variable {R : Type} [CommRing R] [IsDomain R]
namespace GlobalTheory.FamIntAt
theorem _root_.solution {D : DegPre R} {χ : D.X} {I : Ideal R} (h : D.PsiIn χ I) :
    ∃ Ψ : LB.Sec (LB.LinComb D.P.L (Y := Spec (CommRingCat.of R)) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)),
      ∀ (T : Scheme.{0}) (r : T ⟶ (TK R).left) (z : T) (J), Good D.P.L z J →
        sval Ψ (r ≫ jK R) z J = (val (D.psi χ) r z J).val := by
  obtain ⟨s, hs⟩ := exists_extend D.P.isLB (jK R) (genPt R) eq_genPt (PsiInPull.jK_mem _) (K := PUnit)
    (fun _ => (D.c χ).left) (fun _ => -1) (Geo.Tor.genSec (D.psi χ) (D.psi_gen χ)) (fun q => by
      obtain ⟨p, hp⟩ := exists_chart D.P.isLB ((D.c χ).left q)
      obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
        (show q ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U p : (Spec (CommRingCat.of R)).Opens) from hp)
        ((D.c χ).left ⁻¹ᵁ D.P.L.U p).isOpen
      have h' : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U (fun _ => p) :=
        fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp hy)
      obtain ⟨a, -, ha⟩ := h (fun _ => p) V hV hVp h'
      have hm : jK R (genPt R) ∈ V := PsiInPull.jK_mem _ V fun h0 => (h0.le hvV : q ∈ (⊥ : (Spec (CommRingCat.of R)).Opens))
      refine ⟨fun _ => p, V, a, hvV, fun y hy => PsiInPull.mem_wchart _ _ _ _ (hVp hy), ?_⟩
      have e := gs_pull (𝟙 _) (jK R) (genPt R) V hm a
      rw [Category.id_comp] at e
      rw [← e, ha]
      exact gs_res (𝟙 _) (genPt R) h' hm _)
  exact ⟨s, fun T r z J hJ => (hs T r z J hJ).trans (sval_genSec (D.psi χ) (D.psi_gen χ) r z hJ)⟩
end GlobalTheory.FamIntAt
