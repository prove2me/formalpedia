-- Prove2me | solution 1 for NewtonianLipschitz.newtonianJacobianMatrix_normalized_allRows_le_candidateMaximum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T03:54:00.879468+00:00
-- url     : https://prove2.me/submissions/cc981c1b-de01-4b77-838c-462d1b5c68bb

module
public import Definitions.Def_NewtonianLipschitz_JacobianMatrix
public import Definitions.Def_NewtonianLipschitz_ScalarMaximum
public import Definitions.Def_NewtonianLipschitz_NormalizedSharpBound
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_firstRow_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_secondRow_le_candidateMaximum
public import Theorems.Thm_NewtonianLipschitz_newtonianJacobianMatrix_normalized_thirdRow_le_candidateMaximum

set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz
namespace NewtonianLipschitz
theorem _root_.solution
    (μ u v : ℝ) (hμ : 0 ≤ μ)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (i : Fin 3) :
    (∑ j : Fin 3,
      |newtonianJacobianMatrix μ (normalizedVector u v) i j|) ≤
      μ * candidateMaximum := by
  fin_cases i
  · exact newtonianJacobianMatrix_normalized_firstRow_le_candidateMaximum
      μ u v hμ hu0 hu1 hv0 hv1
  · exact newtonianJacobianMatrix_normalized_secondRow_le_candidateMaximum
      μ u v hμ hu0 hu1 hv0 hv1
  · exact newtonianJacobianMatrix_normalized_thirdRow_le_candidateMaximum
      μ u v hμ hu0 hu1 hv0 hv1
end NewtonianLipschitz
