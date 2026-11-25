-- Prove2me | solution 1 for GlobalTheory.PowGerm.univConv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:37:46.88907+00:00
-- url     : https://prove2.me/submissions/be4a0827-8a58-4544-9478-c29ddcaf6867

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalJetsReindexFin
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_toAt_ofAt
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_ofAt_toAt
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_spMap_toAt
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_ofAt_spMap
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_ren_zR
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_aug_ren
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_aug_symm
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_trunc_symm
import Theorems.Thm_GlobalTheory_PowGerm_UnivConv_zero_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_spMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PowGerm
open UnivConv
namespace GlobalTheory.PowGerm
theorem _root_.solution : UnivConvSt := by
  intro V _ G _ κ z hz N β
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun m => Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, trunc_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetTrunc), spMap_toAt, Category.assoc, h1]
  · intro m
    rw [← Category.assoc, Chart.spMap_comp, zero_eq, AlgHom.comp_assoc, aug_symm, ← Chart.spMap_comp, Category.assoc,
      ← Category.assoc (Chart.spMap jetAug), spMap_toAt, Category.assoc, h2, ← Category.assoc]
    exact MonObj.comp_one _
  · intro A _ _ aug m hm y hy
    obtain ⟨φ, ⟨hφ1, hφ2⟩, hu⟩ := h3 A aug m hm (ofAt A ≫ y) (by
      rw [← Category.assoc, ← ofAt_spMap, Category.assoc, hy]
      exact MonObj.comp_one _)
    refine ⟨φ.comp (ren (V := V) β m).toAlgHom, ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hφ1, aug_ren]
    · have e : (φ.comp (ren (V := V) β m).toAlgHom).comp (ren (V := V) β m).symm.toAlgHom = φ :=
        AlgHom.ext fun a => by simp
      rw [← Category.assoc, Chart.spMap_comp, e, ← Category.assoc, spMap_toAt, Category.assoc, ← hφ2,
        ← Category.assoc, toAt_ofAt, Category.id_comp]
    · rintro ψ ⟨hψ1, hψ2⟩
      have e := hu (ψ.comp (ren (V := V) β m).symm.toAlgHom) ⟨by rw [← AlgHom.comp_assoc, hψ1, aug_symm], by
        rw [hψ2, ← Category.assoc (Chart.spMap ψ), Chart.spMap_comp, ← Category.assoc, ofAt_spMap, Category.assoc,
          ← Category.assoc (ofAt _), ofAt_toAt, Category.id_comp]⟩
      rw [← e]
      exact AlgHom.ext fun a => by simp
  · intro m
    refine ⟨ren β m, ren_zR β m, ?_⟩
    have e : Chart.spMap (ren (V := V) β m).toAlgHom ≫
        Chart.spMap (ren (V := V) β m).symm.toAlgHom ≫ toAt _ ≫ z m = toAt _ ≫ z m := by
      have e' : (ren (V := V) β m).toAlgHom.comp (ren (V := V) β m).symm.toAlgHom = AlgHom.id V _ :=
        AlgHom.ext fun a => by simp
      have e'' : Chart.spMap (AlgHom.id V (Jet V κ m)) = 𝟙 _ :=
        Over.OverMorphism.ext (Spec.map_id _)
      rw [← Category.assoc, Chart.spMap_comp, e', e'', Category.id_comp]
    exact (Category.id_comp _).symm.trans (congrArg CommaMorphism.left e).symm
end GlobalTheory.PowGerm
