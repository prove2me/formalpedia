-- Prove2me | solution 1 for GlobalTheory.exists_sec_generates_specialFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:38:10.552479+00:00
-- url     : https://prove2.me/submissions/789253a0-90a6-43b8-8e89-3aa837d32458

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecGeneratesSpecialFibre
import Theorems.Thm_GlobalTheory_SpecialFibreGenerator_mem_nonzeroLocus_secAlong
import Theorems.Thm_GlobalTheory_SpecialFibreGenerator_mem_basicOpen_of_isClosed
import Theorems.Thm_GlobalTheory_DvrModel_existsUnique_zpow_mul_sec
import Theorems.Thm_GlobalTheory_DvrModel_isIntegral
import Theorems.Thm_GlobalTheory_DvrModel_isOpenImmersion_generic
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff
import Theorems.Thm_GlobalTheory_DvrModel_notMem_basicOpen_iff_specializes
import Theorems.Thm_GlobalTheory_DvrModel_opensRange_generic
import Theorems.Thm_GlobalTheory_DvrModel_prime_res_generic
import Theorems.Thm_GlobalTheory_grpObj_geometricallyIntegral_of_smooth
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_mem_of_cover


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
set_option backward.isDefEq.respectTransparency false
open GlobalTheory
open SpecialFibreGenerator TopologicalSpace
namespace GlobalTheory
theorem _root_.solution : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : LB G.left), N.IsLB → ∀ s : LB.Sec (N.pull (pullback.fst G.hom (jK V))), (∃ a, a ∈ nonzeroLocus s) → IsClosed ((pullback.fst G.hom (jK V)) '' {a | a ∉ nonzeroLocus s}) → ∃ θ : H0 N 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint V → x ∈ nonzeroLocus θ := by
  intro V _ _ _ G _ _ hG N hN s ⟨a₀, ha₀⟩ hZ
  have := hG.smooth
  have := hG.geomConnected
  have := grpObj_geometricallyIntegral_of_smooth _ G
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hK := IsPullback.of_hasPullback G.hom (jK V)
  have hs := IsPullback.of_hasPullback G.hom (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  have := DvrModel.isOpenImmersion_generic hK
  have := DvrModel.isIntegral hK
  obtain ⟨n, ⟨σ, hσ, b, x₀, hx₀, hb⟩, -⟩ := DvrModel.existsUnique_zpow_mul_sec hK hs hϖ hN s (by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 ha₀
    exact ⟨k, fun h ↦ by rw [h, Scheme.basicOpen_zero] at hk; exact hk⟩)
  have hξ := DvrModel.notMem_basicOpen_iff_specializes hϖ hs
  have hr := DvrModel.opensRange_generic hϖ hK
  refine ⟨secAlong σ (𝟙 _), fun x hx ↦ ?_⟩
  obtain ⟨a, ha⟩ := LB.mem_of_cover hN x
  refine mem_nonzeroLocus_secAlong σ (𝟙 _) (a := a) ?_
  refine mem_basicOpen_of_isClosed hξ (DvrModel.prime_res_generic hϖ hs) σ (b := b)
    (((hξ x₀).1 ((DvrModel.notMem_basicOpen_iff _ hϖ x₀).2 hx₀)).mem_open
      (Scheme.basicOpen _ _).isOpen hb) hZ ?_ (fun y hy hyZ ↦ ?_)
    ((DvrModel.notMem_basicOpen_iff _ hϖ x).2 hx) ha
  · rintro _ ⟨y, -, rfl⟩
    exact hr.le ⟨y, rfl⟩
  · obtain ⟨z, rfl⟩ := hr.ge hy
    have hz : z ∈ nonzeroLocus s := by_contra fun h ↦ hyZ ⟨z, h, rfl⟩
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
    refine ⟨k ⟨⟩, ?_⟩
    have h0 : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
      zpow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V _)).2 hϖ.ne_zero)
    have h := congrArg (Scheme.basicOpen _) (hσ k)
    rw [Scheme.basicOpen_mul, Scheme.basicOpen_appLE,
      Scheme.basicOpen_of_isUnit _ (((h0.isUnit.map _).map _).map _)] at h
    exact (h.ge ⟨Scheme.basicOpen_le _ _ hk, hk⟩).2
end GlobalTheory
