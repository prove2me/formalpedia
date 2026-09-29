-- Prove2me | solution 1 for GeneralCK.Certificates.E8TAxisProd0001Certified.centerBoxes_contains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-25T03:56:05.740877+00:00
-- url     : https://prove2.me/submissions/59358d62-fa9e-436a-ae77-43619add3ca1

import Definitions.Def_GeneralCK_E8_Prod0001_graph_mixed_data
import Definitions.Def_GeneralCK_E8_Prod0001_inputs
import Definitions.Def_GeneralCK_E8_Prod0001_leaf_data
import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_first_cell_Taylor_interface
import Definitions.Def_GeneralCK_E8_first_cell_inputs
import Definitions.Def_GeneralCK_E8_first_cell_jet_graphs
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_reusable_cell_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Definitions.Def_GeneralCK_MixedBounds
import Definitions.Def_GeneralCK_RB2_checker_semantics_v2
import Definitions.Def_GeneralCK_RB2_program_data
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_correction_entries
import Definitions.Def_GeneralCK_statement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerA_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerB_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerC_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001EndpointWitnesses_centerD_covers
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001GraphCenterA_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001GraphCenterB_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001GraphCenterC_qJetBox_contains
import Theorems.Thm_GeneralCK_Certificates_E8TAxisProd0001GraphCenterD_qJetBox_contains

section
namespace GeneralCK.Certificates.E8TAxisProd0001Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0001Geometry E8TAxisProd0001CertifiedArithmetic












end GeneralCK.Certificates.E8TAxisProd0001Certified
end

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisProd0001Certified
open GeneralCK Set E8TAxisDeltaDirectionalJet E8TAxisMixedCoefficients
open E8TAxisGeneralCenteredTaylor E8TAxisPartitionKernel
open E8TAxisProd0001Geometry E8TAxisProd0001CertifiedArithmetic
theorem solution : centerBoxes.ContainsAt centerS centerT := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0001EndpointWitnesses.centerA_covers
    have hh := E8TAxisProd0001GraphCenterA.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0001EndpointWitnesses.centerB_covers
    have hh := E8TAxisProd0001GraphCenterB.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0001EndpointWitnesses.centerC_covers
    have hh := E8TAxisProd0001GraphCenterC.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
  · obtain ⟨a, ha, hpos, hy⟩ := E8TAxisProd0001EndpointWitnesses.centerD_covers
    have hh := E8TAxisProd0001GraphCenterD.qJetBox_contains ha hpos
    rw [hy] at hh
    exact hh
