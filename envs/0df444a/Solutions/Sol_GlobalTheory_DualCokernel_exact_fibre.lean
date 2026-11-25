-- Prove2me | solution 1 for GlobalTheory.DualCokernel.exact_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:25.583628+00:00
-- url     : https://prove2.me/submissions/e6a1acd1-f5d2-4b33-8e64-76d45118adb2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres
import Theorems.Thm_GlobalTheory_exact_lTensor_iff_residueField
import Theorems.Thm_GlobalTheory_isZero_homology_extendScalars_iff


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
variable (C : CochainComplex (ModuleCat.{0} R) ℕ)
namespace GlobalTheory.DualCokernel
theorem _root_.solution (p : Ideal R) [p.IsPrime] {K : Type} [Field K] (φ : R →+* K)
    (hφ : RingHom.ker φ = p) (i : ℕ)
    (h : (((ModuleCat.extendScalars φ).mapHomologicalComplex _).obj C).ExactAt i) :
    Exact ((C.d (i - 1) i).hom.lTensor p.ResidueField)
      ((C.d i (i + 1)).hom.lTensor p.ResidueField) := by
  let := φ.toAlgebra
  rw [← exact_lTensor_iff_residueField p K hφ,
    ← isZero_homology_extendScalars_iff K C (by cases i <;> simp) (by simp),
    ← HomologicalComplex.exactAt_iff_isZero_homology]
  exact h
end GlobalTheory.DualCokernel
