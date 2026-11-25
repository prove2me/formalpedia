-- Prove2me | solution 1 for GlobalTheory.DualCokernel.exists_smul_eq_zero_of_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:51.113952+00:00
-- url     : https://prove2.me/submissions/3e574c9e-7882-4e10-aff1-1f57f2116f71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution (p : Ideal R) [hp : p.IsPrime] (N : Type) [AddCommGroup N]
    [Module R N] [Module.Finite R N] (h : Subsingleton (p.ResidueField ⊗[R] N)) :
    ∃ s, s ∉ p ∧ ∀ x : N, s • x = 0 := by
  have h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∉ Module.support R N := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr h
  rw [Module.mem_support_iff_of_finite] at h1
  obtain ⟨s, hs, hs'⟩ := Set.not_subset.mp h1
  exact ⟨s, hs', Module.mem_annihilator.mp hs⟩
end GlobalTheory.DualCokernel
