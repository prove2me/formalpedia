-- Prove2me | solution 1 for GlobalTheory.GodementJacquet.TestNearE.nhds_zero_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:36:35.700976+00:00
-- url     : https://prove2.me/submissions/3dd37f81-a3c2-4a5d-b284-e3f41f3e6eeb

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_LeviRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ExistsSchwartzBumpNearIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
open GlobalTheory GlobalTheory.GodementJacquet GlobalTheory.GodementJacquet.TestNearE
open ValuativeRel Filter Topology
namespace GlobalTheory.GodementJacquet.TestNearE
theorem _root_.solution (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n m : ℕ) : (𝓝 (0 : Matrix (Fin n) (Fin m) k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by
  have h0 := IsValuativeTopology.hasBasis_nhds_zero k
  have h1 : (𝓝 (0 : Fin m → k)).HasBasis (fun Ik : Set (Fin m) × (ValueGroupWithZero k)ˣ => Ik.1.Finite ∧ True)
      (fun Ik => Ik.1.pi fun _ => {x : k | valuation k x < Ik.2}) := by
    rw [nhds_pi]; exact h0.pi_self
  have h2 : (𝓝 (0 : Fin n → Fin m → k)).HasBasis
      (fun IJ : Set (Fin n) × (Set (Fin m) × (ValueGroupWithZero k)ˣ) => IJ.1.Finite ∧ (IJ.2.1.Finite ∧ True))
      (fun IJ => IJ.1.pi fun _ => IJ.2.1.pi fun _ => {x : k | valuation k x < IJ.2.2}) := by
    rw [nhds_pi]; exact h1.pi_self
  exact h2
end GlobalTheory.GodementJacquet.TestNearE
