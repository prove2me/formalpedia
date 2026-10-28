-- Prove2me | solution 1 for OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:14:02.047228+00:00
-- url     : https://prove2.me/submissions/fce28d5c-e1dd-447f-8af5-5069c4376989

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C007
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C031

section
-- module Solutions.OAIQ039_CM.Commutator_CommutatorPerturbation
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma commutatorSeminorm_le (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H) (C : ℝ)
    (hC : ∀ a : H →L[ℂ] H,a∈P → ‖a‖≤1 → ‖Y*a-a*Y‖≤C) :
    commutatorSeminorm P Y≤C := by
  apply csSup_le
  · exact ⟨0,0,P.zero_mem,by simp,by simp⟩
  · rintro r ⟨a,ha,hna,rfl⟩
    exact hC a ha hna

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryMainTransport
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable (U : H ≃ₗᵢ[ℂ] K)

lemma conj_norm (a : H →L[ℂ] H) : ‖U.conjStarAlgEquiv a‖=‖a‖ := by
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map]
      using a.le_opNorm (U.symm x)
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.norm_map,
      U.symm_apply_apply] using (U.conjStarAlgEquiv a).le_opNorm (U x)

lemma seminorm (M : VonNeumannAlgebra H) (Y : H →L[ℂ] H) :
    commutatorSeminorm (algebra U M) (U.conjStarAlgEquiv Y)=commutatorSeminorm M Y := by
  apply le_antisymm
  · apply commutatorSeminorm_le
    rintro a ⟨b,hb,rfl⟩ hna
    change ‖U.conjStarAlgEquiv Y * U.conjStarAlgEquiv b -
      U.conjStarAlgEquiv b * U.conjStarAlgEquiv Y‖ ≤ _
    rw [←map_mul,←map_mul,←map_sub,conj_norm]
    change ‖U.conjStarAlgEquiv b‖ ≤ 1 at hna
    exact commutator_bound_unitball M Y hb (by simpa only [conj_norm] using hna)
  · apply commutatorSeminorm_le
    intro a ha hna
    have hh := commutator_bound_unitball (algebra U M) (U.conjStarAlgEquiv Y)
      ((mem_algebra U M a).mpr ha) (by
        rw [conj_norm]
        exact hna)
    simpa only [←map_mul U.conjStarAlgEquiv,←map_sub U.conjStarAlgEquiv,
      conj_norm] using hh

lemma diagonal (h : ℕ) (Y : H →L[ℂ] H) :
    (copies U h).conjStarAlgEquiv (diagonalAmplification h Y)=
      diagonalAmplification h (U.conjStarAlgEquiv Y) := by
  ext x i
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,copies_apply,copies_symm_apply,
    diagonalAmplification_apply]

lemma matrix (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    (copies U h).conjStarAlgEquiv (matrixOperator h X)=
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j)) := by
  ext x i
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,copies_apply,copies_symm_apply,
    matrixOperator_apply,map_sum]
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using
    (matrixOperator_apply h (fun i j => U.conjStarAlgEquiv (X i j)) x i).symm

lemma matrix_norm (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    ‖matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))‖=‖matrixOperator h X‖ := by
  rw [←matrix,conj_norm]

lemma matrix_commutator_norm (h : ℕ) (Y : H →L[ℂ] H)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) :
    ‖diagonalAmplification h (U.conjStarAlgEquiv Y)*
        matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))-
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))*
        diagonalAmplification h (U.conjStarAlgEquiv Y)‖=
      ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ := by
  rw [←diagonal,←matrix,←map_mul,←map_mul,←map_sub,conj_norm]

end Kadison.UnitaryTransport

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UnitaryBoundTransfer
attribute [-instance] _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.UnitaryTransport

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem bound_of_conjugate_bound_oai (U : H ≃ₗᵢ[ℂ] K) (M : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (c : ℝ)
    (hb : ‖diagonalAmplification h (U.conjStarAlgEquiv Y)*
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))-
      matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))*
      diagonalAmplification h (U.conjStarAlgEquiv Y)‖≤
      c*commutatorSeminorm (algebra U M) (U.conjStarAlgEquiv Y)*
      ‖matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))‖) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm M Y*‖matrixOperator h X‖ := by
  simpa only [matrix_commutator_norm,seminorm,matrix_norm] using hb

end Kadison.UnitaryTransport

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound_oai.{u_1, u_2} := @OAI.Kadison.UnitaryTransport.bound_of_conjugate_bound_oai.{u_1, u_2}
