-- Prove2me | solution 1 for GlobalTheory.BesselPeriodCompare.besselPeriod_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:20:13.844855+00:00
-- url     : https://prove2.me/submissions/e841c139-01e7-4856-a082-cae2ae4e5dc3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_BesselPeriodGGP
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NodeGapNoncompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SymmetricMeasureL2NormEqResolutionL2
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_haar_of_compact
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_exists_haar
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_isHaarOn_iff
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_closedS
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_haar_prod
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_period_eq
import Theorems.Thm_GlobalTheory_BesselPeriodCompare_isHCParam_of_interlaces
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x2_closedN
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_closedW
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_interlace_iff
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_lam_eq
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_parity_iff
import Theorems.Thm_GlobalTheory_Proof_NodeGapNoncompact_sign_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.BesselPeriodCompare
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open Formalism.FourierDecayAlt.B2 (IsClosedSubgroup mulM invM)
open Formalism.FourierDecayAlt.P.B2x1
open GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient (Mat leviW IsClosedMatGroup)
variable {k r : ℕ}
namespace GlobalTheory.BesselPeriodCompare
theorem _root_.solution :
    PI.BesselPeriodGGP.BesselPeriodGGP ↔ GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.BesselPeriodNeZero := by
  constructor
  · intro hA k r hk he v b u hl hi hp H _ _ σ hσ z hz hT Wp _ _ π hπ c hc μS hS x hx
    have hk1 : 1 ≤ k := by omega
    have hu := isHCParam_of_interlaces hl hi hp
    rw [← GlobalTheory.Proof.NodeGapNoncompact.interlace_iff k r hk1] at hi
    rw [← GlobalTheory.Proof.NodeGapNoncompact.parity_iff k r hk1] at hp
    rw [← GlobalTheory.Proof.NodeGapNoncompact.lam_eq k r hk1] at hl hσ hx
    rw [← GlobalTheory.Proof.NodeGapNoncompact.sign_eq k r hk1] at hσ hx
    have : CompleteSpace H := hσ.choose_spec.2.1
    have : FiniteDimensional ℂ Wp := hπ.choose_spec.2.2.1
    obtain ⟨μW, hW⟩ := exists_haar (Formalism.FourierDecayAlt.P.B2x3.closedW k r z)
    obtain ⟨μN, hN⟩ := exists_haar (Formalism.FourierDecayAlt.P.B2x2.closedN k r)
    have hW' := haar_of_compact (Formalism.FourierDecayAlt.P.B2x3.closedW k r z).closed hW
    have hN' := haar_of_compact (Formalism.FourierDecayAlt.P.B2x2.closedN k r).closed hN
    obtain ⟨g, y, hg, hy, h⟩ :=
      hA k r z c u v b hk he hz hT hc hu hl hi hp H σ hσ Wp π hπ x hx μW μN hW' hN'
    obtain ⟨t, ht, e⟩ := period_eq hz hW' hN' hS
    have hne : GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.period k r z c σ π μS (σ g x) (σ y x) ≠ 0 := by
      rw [e]
      exact smul_ne_zero ht.ne' h
    exact ⟨g, hg, y, hy, Integrable.of_integral_ne_zero hne, hne⟩
  · intro hB k r z c u v b hk he hz hT hc _ hl hi hp H _ _ _ σ hσ Wp _ _ _ π hπ x hx μW μN hW hN
    have hk1 : 1 ≤ k := by omega
    rw [GlobalTheory.Proof.NodeGapNoncompact.interlace_iff k r hk1] at hi
    rw [GlobalTheory.Proof.NodeGapNoncompact.parity_iff k r hk1] at hp
    rw [GlobalTheory.Proof.NodeGapNoncompact.lam_eq k r hk1] at hl hσ hx
    rw [GlobalTheory.Proof.NodeGapNoncompact.sign_eq k r hk1] at hσ hx
    have hS := (isHaarOn_iff (closedS hz) _).mp (haar_prod hz hW hN)
    obtain ⟨g, hg, y, hy, -, h⟩ :=
      hB k r hk he v b u hl hi hp H σ hσ z hz hT Wp π hπ c hc _ hS x hx
    obtain ⟨t, -, e⟩ := period_eq hz hW hN hS
    refine ⟨g, y, hg, hy, fun h0 => h ?_⟩
    rw [e, h0, smul_zero]
end GlobalTheory.BesselPeriodCompare
