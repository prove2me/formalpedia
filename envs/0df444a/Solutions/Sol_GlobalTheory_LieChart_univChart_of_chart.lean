-- Prove2me | solution 1 for GlobalTheory.LieChart.univChart_of_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:47:28.553859+00:00
-- url     : https://prove2.me/submissions/14a48f74-bb96-443f-a794-d5f8d697830f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsLieBasisBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsAffineLieBasisBaseChange
import Theorems.Thm_GlobalTheory_LieChart_algChart_of_isStandardSmooth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_aug_surj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_elt_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_exists_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_le_preimage_of_nil
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_nil_of_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_pt_injective
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_pt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_spMap_comp


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
open GlobalTheory GlobalTheory.LieChart
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Chart
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj
namespace GlobalTheory.LieChart
theorem _root_.solution {R : Type} [CommRing R] (G : Over (Spec (CommRingCat.of R))) [GrpObj G] (C : Chart G)
    (hC : (alg0 C).IsStandardSmooth) :
    ∃ (d : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G), IsUnivChart G d x := by
  obtain ⟨n, π, htr, hze, huniv⟩ := algChart_of_isStandardSmooth Γ(G.left, C.U) hC (eps C)
  refine ⟨n, fun m => pt C (π m), fun m => ?_, fun m => ?_, ?_⟩
  · rw [spMap_pt, htr]
  · rw [spMap_pt, hze, pt_eps]
  · intro A _ _ aug m hJ y hy
    have hJn := nil_of_pow _ hJ
    have hy' : spMap aug ≫ y = pt C ((Algebra.ofId R R).comp (eps C)) := by rw [pt_eps]; exact hy
    obtain ⟨φ, rfl⟩ := exists_pt C y (le_preimage_of_nil C aug (aug_surj aug) (elt_nil _ hJn) y _ hy')
    have hφ : aug.comp φ = eps C := by
      have := pt_injective C ((spMap_pt C aug φ).symm.trans hy')
      rw [this]
      ext b
      rfl
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := huniv A aug m hJ φ hφ
    refine ⟨ψ, ⟨hψ1, by rw [spMap_pt, hψ2]⟩, ?_⟩
    rintro ψ₂ ⟨h1, h2⟩
    rw [spMap_pt] at h2
    exact hψu ψ₂ ⟨h1, (pt_injective C h2).symm⟩
end GlobalTheory.LieChart
