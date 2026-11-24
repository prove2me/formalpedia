-- Prove2me | solution 1 for GlobalTheory.PowGerm.nabJet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:07.138809+00:00
-- url     : https://prove2.me/submissions/6f8f7dc2-79bd-44da-810c-1408a6244265

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonNCongr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_coeff_mul_congr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_constantCoeff_DmonN_congr
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_isLinearMap_DmonN
import Theorems.Thm_GlobalTheory_PowGerm_NabJet_constantCoeff_DpolyN_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.PowGerm
open MvPowerSeries
namespace GlobalTheory.PowGerm
theorem _root_.solution : NabJetSt := by
  intro R _ d O _ _ B k _ _ _ h w0 q n Ix _ cp u
  classical
  refine ⟨fun P f g hfg => ?_, fun P J _ c f => ?_, fun f J _ c P => ?_⟩
  · unfold nabValN
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl]
    refine Finset.sum_congr rfl fun m hm => ?_
    congr 1
    refine NabJet.constantCoeff_DmonN_congr _ cp u m _ _ fun mo hmo => ?_
    refine NabJet.coeff_mul_congr P.totalDegree f g _ hfg mo (hmo.trans ?_)
    have := MvPolynomial.le_totalDegree hm
    rwa [Finsupp.degree_apply]
  · unfold nabValN
    simp only [NabJet.constantCoeff_DpolyN_eq _ cp u P _ _ subset_rfl, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hl := NabJet.isLinearMap_DmonN (B.FK k) cp u m
    rw [Finset.sum_mul, ← IsLinearMap.mk'_apply hl, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, IsLinearMap.mk'_apply, smul_eq_C_mul, map_mul, constantCoeff_C]
    ring
  · unfold nabValN
    set S : Finset (Ix →₀ ℕ) := (∑ j, c j • P j).support ∪ Finset.univ.biUnion fun j => (P j).support with hS
    rw [NabJet.constantCoeff_DpolyN_eq _ cp u _ _ S Finset.subset_union_left]
    have hj : ∀ j, (P j).support ⊆ S := fun j =>
      (Finset.subset_biUnion_of_mem (fun j => (P j).support) (Finset.mem_univ j)).trans Finset.subset_union_right
    simp only [fun j => NabJet.constantCoeff_DpolyN_eq (B.FK k) cp u (P j)
      (f * FB.expS k ((q : k) • ∑ b, ev ![pt k d b] (B.hL k h w0))) S (hj j), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.coeff_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul, _root_.mul_assoc]
end GlobalTheory.PowGerm
