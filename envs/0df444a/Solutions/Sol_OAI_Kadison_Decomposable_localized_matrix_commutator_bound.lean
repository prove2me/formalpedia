-- Prove2me | solution 1 for OAI.Kadison.Decomposable.localized_matrix_commutator_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:19:20.081959+00:00
-- url     : https://prove2.me/submissions/b7152869-8754-48ea-9037-f61b55b97057

import Mathlib
import Definitions.Def_UniformCommutator
import Definitions.Def_OAIQ039C018
import Definitions.Def_OAIQ039C043
import Theorems.Thm_OAI_Kadison_CentralAverage_exists_center_average
import Theorems.Thm_OAI_Kadison_Decomposable_matrix_commutator_bound_of_countable_factor_fields

section
-- module Solutions.OAIQ039_CM.Commutator_MainCommutantDistance
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

open ContinuousLinearMap

universe u

namespace Kadison

variable {K : Type u} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [CompleteSpace K] in
lemma operator_commutator_norm_le (Y Z : K →L[ℂ] K) : ‖Y*Z-Z*Y‖≤2*‖Y‖*‖Z‖ := by
  calc
    _ ≤ ‖Y*Z‖+‖Z*Y‖ := norm_sub_le _ _
    _ ≤ ‖Y‖*‖Z‖+‖Z‖*‖Y‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ = _ := by ring

end Kadison

end

end
end

end OAI
end

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

lemma commutatorSeminorm_perturb (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H) :
    commutatorSeminorm P Z ≤ commutatorSeminorm P Y+2*‖Z-Y‖ := by
  apply commutatorSeminorm_le
  intro a ha hna
  have he : Z*a-a*Z=(Y*a-a*Y)+((Z-Y)*a-a*(Z-Y)) := by
    simp only [sub_mul,mul_sub]; abel
  rw [he]
  calc
    _ ≤ ‖Y*a-a*Y‖+‖(Z-Y)*a-a*(Z-Y)‖ := norm_add_le _ _
    _ ≤ commutatorSeminorm P Y+2*‖Z-Y‖*‖a‖ :=
      add_le_add (commutator_bound_unitball P Y ha hna) (operator_commutator_norm_le _ _)
    _ ≤ commutatorSeminorm P Y+2*‖Z-Y‖ := by nlinarith [norm_nonneg (Z-Y)]

lemma commutatorSeminorm_three (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H)
    (hZ : ‖Z-Y‖ ≤ commutatorSeminorm P Y) : commutatorSeminorm P Z≤3*commutatorSeminorm P Y := by
  have hh := commutatorSeminorm_perturb P Y Z
  linarith

lemma matrix_commutator_perturb (P : VonNeumannAlgebra H) (Y Z : H →L[ℂ] H)
    (hZ : ‖Z-Y‖ ≤ commutatorSeminorm P Y) (c : ℝ) (hc : 0 ≤ c)
    (h : ℕ) (X : Matrix (Fin h) (Fin h) (H →L[ℂ] H))
    (hb : ‖diagonalAmplification h Z*matrixOperator h X-matrixOperator h X*diagonalAmplification h Z‖ ≤
      c*commutatorSeminorm P Z*‖matrixOperator h X‖) :
    ‖diagonalAmplification h Y*matrixOperator h X-matrixOperator h X*diagonalAmplification h Y‖ ≤
      (3*c+2)*commutatorSeminorm P Y*‖matrixOperator h X‖ := by
  let A := matrixOperator h X
  have he : diagonalAmplification h Y*A-A*diagonalAmplification h Y=
      (diagonalAmplification h Z*A-A*diagonalAmplification h Z)+
      (diagonalAmplification h (Y-Z)*A-A*diagonalAmplification h (Y-Z)) := by
    rw [diagonalAmplification_sub,sub_mul,mul_sub]
    abel
  have hdelta : ‖Y-Z‖ ≤ commutatorSeminorm P Y := by rwa [norm_sub_rev]
  have herr := (operator_commutator_norm_le (diagonalAmplification h (Y-Z)) A).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left ((diagonalAmplification_norm_le h (Y-Z)).trans hdelta) (by norm_num))
      (norm_nonneg A))
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (commutatorSeminorm_three P Y Z hZ) hc) (norm_nonneg A)
  change ‖diagonalAmplification h Y*A-A*diagonalAmplification h Y‖≤_
  rw [he]
  calc
    _ ≤ ‖diagonalAmplification h Z*A-A*diagonalAmplification h Z‖+
      ‖diagonalAmplification h (Y-Z)*A-A*diagonalAmplification h (Y-Z)‖ := norm_add_le _ _
    _ ≤ c*(3*commutatorSeminorm P Y)*‖A‖+2*commutatorSeminorm P Y*‖A‖ :=
      add_le_add (hb.trans hh) herr
    _ = _ := by dsimp [A]; ring

end Kadison

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FactorFieldLocalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω : Type*} {H : Type} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

theorem localized_matrix_commutator_bound_oai
    (P : VonNeumannAlgebra (Lp H 2 μ)) (Q : Ω → VonNeumannAlgebra H)
    (hfac : ∀ᵐ a ∂μ,FactorCorner.IsFactor (Q a))
    (hdiag : ∀ (s : Set Ω) (hs : MeasurableSet s),
      indicatorOperator (H:=H) μ s hs∈P ∧
      indicatorOperator (H:=H) μ s hs∈Set.centralizer (P : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)))
    (test : ℕ → Ω → H →L[ℂ] H)
    (ht : ∀ n ξ,AEStronglyMeasurable (fun a => test n a ξ) μ)
    (htb : ∀ n,∀ᵐ a ∂μ,‖test n a‖≤1)
    (htmem : ∀ n,operator μ (test n) (ht n) (htb n)∈P)
    (htdense : ∀ᵐ a ∂μ,∀ A : H →L[ℂ] H,A∈Q a → ‖A‖≤1 →
      ∃ k : ℕ → ℕ,∀ ξ,Tendsto (fun n => test (k n) a ξ) atTop (𝓝 (A ξ)))
    (Y : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (h : ℕ) (hh : 1≤h) (X : Fin h → Fin h → Ω → H →L[ℂ] H)
    (hX : ∀ i j ξ,AEStronglyMeasurable (fun a => X i j a ξ) μ)
    {c : Fin h → Fin h → ℝ} (hc0 : ∀ i j,0 ≤ c i j)
    (hc : ∀ i j,∀ᵐ a ∂μ,‖X i j a‖ ≤ c i j)
    (hmem : ∀ᵐ a ∂μ,∀ i j,X i j a∈Q a) :
    ‖diagonalAmplification h Y*
        matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))-
      matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))*
        diagonalAmplification h Y‖≤
      9368*commutatorSeminorm P Y*
        ‖matrixOperator h (fun i j => operator μ (X i j) (hX i j) (hc i j))‖ := by
  obtain ⟨Z,hz,hd,_⟩ := CentralAverage.exists_center_average P Y
  have hcomm (s : Set Ω) (hs : MeasurableSet s) : Commute Z (indicatorOperator μ s hs) :=
    hz _ (hdiag s hs).1 (hdiag s hs).2
  obtain ⟨T,hT,hb,he⟩ := exists_field_of_commutes_indicator μ Z hcomm
  have hbnd := matrix_commutator_bound_of_countable_factor_fields μ P Q hfac T hT
    (norm_nonneg Z) hb test ht htb htmem htdense h hh X hX hc0 hc hmem
  rw [←he] at hbnd
  convert matrix_commutator_perturb P Y Z hd 3122 (by norm_num) h
    (fun i j => operator μ (X i j) (hX i j) (hc i j)) hbnd using 1
  all_goals try with_reducible_and_instances rfl
  norm_num

end Kadison.Decomposable

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.Decomposable.localized_matrix_commutator_bound_oai.{u_1} := @OAI.Kadison.Decomposable.localized_matrix_commutator_bound_oai.{u_1}
