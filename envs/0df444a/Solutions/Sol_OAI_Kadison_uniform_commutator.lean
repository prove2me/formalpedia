-- Prove2me | solution 1 for OAI.Kadison.uniform_commutator
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:17:03.097225+00:00
-- url     : https://prove2.me/submissions/87263f1e-85a4-4520-a109-36753b0775eb

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C019
import Definitions.Def_OAIQ039C030
import Definitions.Def_OAIQ039C031
import Theorems.Thm_OAI_Kadison_CentralSpectral_separable_uniform_bound
import Theorems.Thm_OAI_Kadison_SeparableTest_bound_of_separable_bound

section
-- module Solutions.OAIQ039_CM.Commutator_CommutatorPerturbation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
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
-- module Solutions.OAIQ039_CM.Commutator_SeparableUniverseTransfer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace BigOperators

universe u

namespace Kadison.SeparableTest

theorem SeparableBound.lift {c : ℝ} (hsmall : SeparableBound.{0} c) :
    SeparableBound.{u} c := by
  intro H _ _ _ _ P Y h hh X hX
  let U := (SeparableSmall.unitary H).symm
  let Q := UnitaryTransport.algebra U P
  have hb := hsmall (SeparableSmall.Model H) Q (U.conjStarAlgEquiv Y) h hh
    (fun i j => U.conjStarAlgEquiv (X i j))
    (fun i j => (UnitaryTransport.mem_algebra U P (X i j)).mpr (hX i j))
  change ‖diagonalAmplification h (U.conjStarAlgEquiv Y)*
    matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))-
    matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))*
    diagonalAmplification h (U.conjStarAlgEquiv Y)‖≤
    c*commutatorSeminorm (UnitaryTransport.algebra U P) (U.conjStarAlgEquiv Y)*
    ‖matrixOperator h (fun i j => U.conjStarAlgEquiv (X i j))‖ at hb
  simpa only [UnitaryTransport.matrix_commutator_norm,UnitaryTransport.seminorm,
    UnitaryTransport.matrix_norm] using hb

theorem bound_of_small_separable_bound {H : Type u} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (P : VonNeumannAlgebra H)
    (Y : H →L[ℂ] H) (h : ℕ) (hh : 1≤h)
    (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H)) (hX : ∀ i j,X i j∈P)
    {c : ℝ} (hc : 0 ≤ c) (hsmall : SeparableBound.{0} c) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      c*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
  bound_of_separable_bound P Y h X hX hc hsmall.lift hh

end Kadison.SeparableTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StableUniversalAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open MeasureTheory Filter

open scoped Topology InnerProductSpace ComplexOrder

namespace Kadison.CentralSpectral

open CyclicSpectral Decomposable

theorem universal_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) (Y : H →L[ℂ] H)
    (h : ℕ) (hh : 1≤h) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (hX : ∀ i j,X i j∈P) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*‖matrixOperator h X‖ :=
  SeparableTest.bound_of_small_separable_bound P Y h hh X hX (by norm_num) separable_uniform_bound

end Kadison.CentralSpectral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_UniversalMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

universe u

namespace Kadison

theorem uniform_commutator_oai :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : Type u) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
      [CompleteSpace K] (P : VonNeumannAlgebra K) (Y : K →L[ℂ] K)
      (h : ℕ), 1 ≤ h → ∀ (X : Matrix (Fin h) (Fin h) (K →L[ℂ] K)),
      (∀ i j, X i j ∈ P) →
      ‖diagonalAmplification h Y * matrixOperator h X -
        matrixOperator h X * diagonalAmplification h Y‖ ≤
        C * commutatorSeminorm P Y * ‖matrixOperator h X‖ := by
  refine ⟨9368,by norm_num,?_⟩
  intro K _ _ _ P Y h hh X hX
  exact CentralSpectral.universal_bound P Y h hh X hX

end Kadison

end

end
end

end OAI
end

theorem solution.{u} : type_of% @OAI.Kadison.uniform_commutator_oai.{u} := @OAI.Kadison.uniform_commutator_oai.{u}
