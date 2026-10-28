-- Prove2me | solution 1 for OAI.Kadison.OperatorAmplification.matrixTrace_normal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:06:01.765992+00:00
-- url     : https://prove2.me/submissions/6e5df50f-877f-424b-8625-77a6c4a2c367

import Mathlib
import Definitions.Def_OAIQ039C068
import Theorems.Thm_OAI_Kadison_OperatorAmplification_matrixTrace_apply

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixEntryWOT
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

omit [CompleteSpace H] in
lemma norm_single_eq (i : ι) (x : H) : ‖single ι i x‖=‖x‖ := by
  have he : single ι i x=PiLp.single 2 i x := by
    ext j
    simp [PiLp.single_apply]
  rw [he,PiLp.norm_single]

omit [CompleteSpace H] in
lemma norm_entry_le (T : SumSpace (H:=H) ι →L[ℂ] SumSpace (H:=H) ι) (i j : ι) :
    ‖entry ι T i j‖≤‖T‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (entry ι T i j) (norm_nonneg T)
  intro x
  change ‖T (single ι j x) i‖≤‖T‖*‖x‖
  calc
    _ ≤ ‖T (single ι j x)‖ := PiLp.norm_apply_le _ _
    _ ≤ ‖T‖*‖single ι j x‖ := T.le_opNorm _
    _ = ‖T‖*‖x‖ := by rw [norm_single_eq]

omit [CompleteSpace H] in
lemma continuous_entryWOT (i j : ι) :
    Continuous (fun T : SumSpace (H:=H) ι →WOT[ℂ] SumSpace (H:=H) ι =>
      ofCLM (entry ι T.toCLM i j)) := by
  change Continuous (fun T : SumSpace (H:=H) ι →WOT[ℂ] SumSpace (H:=H) ι =>
    (ofCLM (PiLp.proj 2 (fun _ : ι => H) i)).comp ((T).comp (ofCLM (single ι j))))
  exact (continuous_postcomp _).comp (continuous_precomp _)

end Kadison.OperatorAmplification

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixNormalTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

attribute [-instance] NonUnitalStarSubalgebra.nonUnitalCStarAlgebra

open scoped BigOperators InnerProductSpace ComplexOrder Topology

open ContinuousLinearMapWOT

namespace Kadison.OperatorAmplification

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (ι : Type*) [Fintype ι] (i₀ : ι) (M : VonNeumannAlgebra H)

attribute [local instance] OAI.Kadison.OperatorAmplification.instDecidableEq_solutions_1
variable (τ : M →ₚ[ℂ] ℂ)

lemma matrixTrace_normal_oai (hnormal : NormalGNS.BoundedWOTContinuous M τ) :
    NormalGNS.BoundedWOTContinuous (matrixVonNeumann ι i₀ M) (matrixTrace ι i₀ M τ) := by
  intro C
  let F := {T : SumSpace (H:=H) ι →WOT[ℂ] SumSpace (H:=H) ι //
    T.toCLM∈matrixVonNeumann ι i₀ M ∧ ‖T.toCLM‖≤C}
  let f (i : ι) : F → {T : H →WOT[ℂ] H // T.toCLM∈M ∧ ‖T.toCLM‖≤C} :=
    fun a => ⟨ofCLM (entry ι a.val.toCLM i i),
      (mem_matrixVonNeumann ι i₀ M a.val.toCLM).mp a.property.1 i i,
      (norm_entry_le ι a.val.toCLM i i).trans a.property.2⟩
  have hf (i : ι) : Continuous (f i) :=
    ((continuous_entryWOT ι i i).comp continuous_subtype_val).subtype_mk _
  have ht (i : ι) : Continuous (fun a : F => τ ⟨(f i a).val.toCLM,(f i a).property.1⟩) :=
    (hnormal C).comp (hf i)
  convert continuous_const.mul (continuous_finsetSum Finset.univ (fun i _ => ht i)) using 1
  all_goals try with_reducible_and_instances rfl
  ext a
  exact matrixTrace_apply ι i₀ M τ _

end Kadison.OperatorAmplification

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.OperatorAmplification.matrixTrace_normal_oai.{u_1, u_2} := @OAI.Kadison.OperatorAmplification.matrixTrace_normal_oai.{u_1, u_2}
