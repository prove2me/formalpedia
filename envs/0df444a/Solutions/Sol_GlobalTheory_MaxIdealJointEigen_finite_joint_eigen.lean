-- Prove2me | solution 1 for GlobalTheory.MaxIdealJointEigen.finite_joint_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:34:09.484535+00:00
-- url     : https://prove2.me/submissions/0ec1e6b2-749d-4b49-ab1d-afab27de0d6f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen
import Theorems.Thm_GlobalTheory_MaxIdealJointEigen_iSupIndep_of_joint_eigen

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
open GlobalTheory GlobalTheory.MaxIdealJointEigen
namespace GlobalTheory.MaxIdealJointEigen
theorem _root_.solution {K I : Type} [Field K] {n : ℕ} (T : I → Matrix (Fin n) (Fin n) K) :
    {θ : I → K | ∃ c : Fin n → K, c ≠ 0 ∧ ∀ i, (T i).mulVec c = θ i • c}.Finite := by
  classical
  let V : (I → K) → Submodule K (Fin n → K) := fun θ =>
    ⨅ i, Module.End.eigenspace (Matrix.toLin' (T i)) (θ i)
  have hV : ∀ x, ∀ v ∈ V x, ∀ i, Matrix.toLin' (T i) v = x i • v := by
    intro x v hv i
    have := (Submodule.mem_iInf _).mp hv i
    exact Module.End.mem_eigenspace_iff.mp this
  have hind := iSupIndep_of_joint_eigen (fun i => Matrix.toLin' (T i)) V hV
  have hfin : Finite {θ // V θ ≠ ⊥} := by
    haveI := hind.fintypeNeBotOfFiniteDimensional
    infer_instance
  refine (Set.finite_coe_iff.mp hfin).subset ?_
  rintro θ ⟨c, hc0, hc⟩
  show V θ ≠ ⊥
  rw [Submodule.ne_bot_iff]
  refine ⟨c, (Submodule.mem_iInf _).mpr fun i => ?_, hc0⟩
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]
  exact hc i
end GlobalTheory.MaxIdealJointEigen
