-- Prove2me | solution 1 for OAI.CurrentProjection.actualRowSourceRefinement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-24T23:53:14.773366+00:00
-- url     : https://prove2.me/submissions/d7f81ad7-5873-4aa7-8587-3b988a5224cf

import Mathlib
import Definitions.Def_GaussianReplacement
import Definitions.Def_OAIQWCP000
import Theorems.Thm_OAI_CurrentProjection_actualRowRefinement

section
-- module Solutions.OAIQW_CurrentProjection.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.Entropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory

open InformationTheory



lemma klDiv_map_equiv {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P Q : Measure A) [IsFiniteMeasure P] [IsFiniteMeasure Q] (e : A ≃ᵐ B) :
    klDiv (P.map e) (Q.map e) = klDiv P Q := by
  apply le_antisymm (klDiv_map_le P Q e.measurable)
  have h := klDiv_map_le (P.map e) (Q.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h



end CurrentProjection

end

end OAI
end

section
-- module Solutions.OAIQW_CurrentProjection.ConditionalInfo
attribute [-instance] _root_.OAI.CurrentProjection.blockLaw_probability _root_.OAI.CurrentProjection.criticalSignal_probability _root_.OAI.CurrentProjection.endingSignalLaw_probability _root_.OAI.CurrentProjection.fiberObservationLaw_finite _root_.OAI.CurrentProjection.sphericalFiberKernel_markov _root_.OAI.CurrentProjection.uniformSphere_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace CurrentProjection
open InnerProductSpace
open InformationTheory




lemma kernel_prod_eq_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (κ : Kernel Z A) (η : Kernel Z B) [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    κ ×ₖ η = κ ⊗ₖ η.comap Prod.fst measurable_fst := by
  ext z s hs
  rw [Kernel.prod_apply' _ _ _ hs, Kernel.compProd_apply hs]
  rfl

lemma compProd_prod_assoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z A) (η : Kernel Z B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ (κ ×ₖ η)).map MeasurableEquiv.prodAssoc.symm =
      (μ ⊗ₘ κ) ⊗ₘ η.comap Prod.fst measurable_fst := by
  rw [kernel_prod_eq_compProd, Measure.compProd_assoc]

lemma compProd_prod_swapAssoc {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z A) (η : Kernel Z B)
    [IsSFiniteKernel κ] [IsSFiniteKernel η] :
    (μ ⊗ₘ (κ ×ₖ η)).map swapAssoc = (μ ⊗ₘ η) ⊗ₘ κ.comap Prod.fst measurable_fst := by
  change (μ ⊗ₘ (κ ×ₖ η)).map (MeasurableEquiv.prodAssoc.symm ∘ Prod.map id Prod.swap) = _
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap), ← Measure.compProd_map measurable_swap,
    Kernel.map_prod_swap, compProd_prod_assoc]

lemma fst_map_swapAssoc_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z (A×B)) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map swapAssoc).fst = μ ⊗ₘ κ.snd := by
  rw [Kernel.snd_eq]
  rw [Measure.compProd_map measurable_snd]
  rw [Measure.fst, Measure.map_map measurable_fst swapAssoc.measurable]
  rfl



lemma conditionalKL_chain {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [Nonempty A]
    (μ : Measure Z) [IsProbabilityMeasure μ] (κ : Kernel Z (A×B)) [IsMarkovKernel κ]
    (π : Measure B) [IsProbabilityMeasure π] :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z π)) =
      klDiv (μ ⊗ₘ κ.snd) (μ.prod π) +
      klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  let R := (μ ⊗ₘ κ).map swapAssoc
  have hR : R.fst = μ ⊗ₘ κ.snd := fst_map_swapAssoc_compProd μ κ
  have hchain := klDiv_compProd_eq_add R.fst (μ.prod π) R.condKernel
    (κ.fst.comap Prod.fst measurable_fst)
  rw [R.disintegrate R.condKernel, hR] at hchain
  have hleft := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z π)) swapAssoc
  rw [compProd_prod_swapAssoc, Measure.compProd_const] at hleft
  have hright := klDiv_map_equiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) swapAssoc
  rw [compProd_prod_swapAssoc] at hright
  exact hleft.symm.trans (hchain.trans (congrArg (klDiv (μ ⊗ₘ κ.snd) (μ.prod π) + ·) hright))


lemma fst_map_assoc_compProd {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] (μ : Measure Z) [SFinite μ] (κ : Kernel Z (A×B)) [IsSFiniteKernel κ] :
    ((μ ⊗ₘ κ).map MeasurableEquiv.prodAssoc.symm).fst = μ ⊗ₘ κ.fst := by
  rw [Kernel.fst_eq, Measure.compProd_map measurable_fst, Measure.fst,
    Measure.map_map measurable_fst MeasurableEquiv.prodAssoc.symm.measurable]
  rfl

lemma mutualInformation_chain {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (P : Measure (Z×(A×B))) [IsProbabilityMeasure P] :
    mutualInformation (P.map MeasurableEquiv.prodAssoc.symm) =
      mutualInformation (P.map (Prod.map id Prod.snd)) + conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let Q := P.map MeasurableEquiv.prodAssoc.symm
  let R := P.map (Prod.map id Prod.snd)
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  let : IsProbabilityMeasure R := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  have hQ : Q.fst = μ ⊗ₘ κ.fst := by
    change (P.map MeasurableEquiv.prodAssoc.symm).fst = _
    rw [← hP]
    exact fst_map_assoc_compProd μ κ
  have hR : R = μ ⊗ₘ κ.snd := by
    rw [Kernel.snd_eq,Measure.compProd_map measurable_snd,hP]
  have hRf : R.fst = μ := by rw [hR,Measure.fst_compProd]
  have hRs : R.snd = Q.snd := by
    dsimp only [R,Q,Measure.snd]
    rw [Measure.map_map measurable_snd (measurable_id.prodMap measurable_snd),
      Measure.map_map measurable_snd MeasurableEquiv.prodAssoc.symm.measurable]
    rfl
  have hleft := klDiv_map_equiv P (μ ⊗ₘ (κ.fst ×ₖ Kernel.const Z Q.snd)) MeasurableEquiv.prodAssoc.symm
  rw [compProd_prod_assoc] at hleft
  have hconst : (Kernel.const Z Q.snd).comap (Prod.fst : Z×A → Z) measurable_fst =
      Kernel.const (Z×A) Q.snd := by ext x t ht; rfl
  rw [hconst,Measure.compProd_const,← hQ] at hleft
  have hc := conditionalKL_chain μ κ Q.snd
  have hSmall : klDiv (μ ⊗ₘ κ.snd) (μ.prod Q.snd) = mutualInformation R := by
    rw [← hR,← hRf,← hRs]
    rfl
  rw [hP,hSmall] at hc
  have hCM : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simp only [conditionalMutualInformation,dite_eq_left (inferInstance : Nonempty (A×B))]
    rfl
  rw [hCM]
  exact hleft.trans hc

lemma conditionalMutualInformation_compProd {Z A B : Type*} [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] [StandardBorelSpace A] [StandardBorelSpace B]
    [Nonempty A] [Nonempty B] (μ : Measure Z) [IsFiniteMeasure μ]
    (κ : Kernel Z (A×B)) [IsMarkovKernel κ] :
    conditionalMutualInformation (μ ⊗ₘ κ) = klDiv (μ ⊗ₘ κ) (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
  simp only [conditionalMutualInformation,dite_eq_left (inferInstance : Nonempty (A×B)),Measure.fst_compProd]
  congr 1
  apply Measure.compProd_congr
  filter_upwards [condKernel_compProd μ κ] with z hz
  simp only [Kernel.prod_apply,Kernel.fst_apply,Kernel.snd_apply,hz]




lemma rowInformation_eq_conditionalMutualInformation {S W X : Type*}
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace X]
    [StandardBorelSpace W] [StandardBorelSpace X] [Nonempty W] [Nonempty X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    rowInformation P γ = conditionalMutualInformation (P.map MeasurableEquiv.prodAssoc) := by
  let Q := P.map (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X))
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hX : P.snd = γ := by
    have h := congrArg Measure.snd hInd
    rw [Measure.snd_prod] at h
    convert h using 1
    simp only [Measure.snd, Measure.fst, Measure.map_map measurable_fst swapLast.measurable,
      Measure.map_map measurable_snd (measurable_fst.comp swapLast.measurable)]
    rfl
  have hQ : Q.map MeasurableEquiv.prodAssoc.symm = P :=
    MeasurableEquiv.prodAssoc.map_symm_map
  have hR : Q.map (Prod.map id Prod.snd) = ν.prod γ := by
    trans (P.map swapLast).fst
    · dsimp only [Q,Measure.fst]
      rw [Measure.map_map (measurable_id.prodMap measurable_snd)
        MeasurableEquiv.prodAssoc.measurable,
        Measure.map_map measurable_fst swapLast.measurable]
      rfl
    · exact hInd
  have hc := mutualInformation_chain Q
  rw [hQ,hR] at hc
  have hzero : mutualInformation (ν.prod γ) = 0 := by
    simp [mutualInformation, klDiv_self]
  rw [hzero,zero_add] at hc
  simpa only [rowInformation,mutualInformation,hX] using hc

lemma conditionalMutualInformation_swap {S A B : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B]
    [StandardBorelSpace A] [StandardBorelSpace B] [Nonempty A] [Nonempty B]
    (P : Measure (S×(A×B))) [IsProbabilityMeasure P] :
    conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      conditionalMutualInformation P := by
  let μ := P.fst
  let κ := P.condKernel
  let e : S×(A×B) ≃ᵐ S×(B×A) :=
    (MeasurableEquiv.refl S).prodCongr MeasurableEquiv.prodComm
  have hP : μ ⊗ₘ κ = P := P.disintegrate P.condKernel
  let : IsMarkovKernel (κ.map Prod.swap) := Kernel.IsMarkovKernel.map κ measurable_swap
  have hf : (κ.map Prod.swap).fst = κ.snd := by
    rw [Kernel.fst_eq, ← Kernel.map_comp_right _ measurable_swap measurable_fst, Kernel.snd_eq]
    rfl
  have hs : (κ.map Prod.swap).snd = κ.fst := by
    rw [Kernel.snd_eq, ← Kernel.map_comp_right _ measurable_swap measurable_snd, Kernel.fst_eq]
    rfl
  have href : μ ⊗ₘ ((κ.map Prod.swap).fst ×ₖ (κ.map Prod.swap).snd) =
      (μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map e := by
    rw [hf,hs, ← Kernel.map_prod_swap, Measure.compProd_map measurable_swap]
    rfl
  have hQ : μ ⊗ₘ κ.map Prod.swap = P.map (Prod.map id Prod.swap) := by
    rw [Measure.compProd_map measurable_swap,hP]
  have hcm : conditionalMutualInformation (P.map (Prod.map id Prod.swap)) =
      klDiv (P.map (Prod.map id Prod.swap)) ((μ ⊗ₘ (κ.fst ×ₖ κ.snd)).map e) := by
    simpa only [hQ,href] using conditionalMutualInformation_compProd μ (κ.map Prod.swap)
  have hcm0 : conditionalMutualInformation P = klDiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) := by
    simpa only [hP] using conditionalMutualInformation_compProd μ κ
  rw [hcm,hcm0]
  exact klDiv_map_equiv P (μ ⊗ₘ (κ.fst ×ₖ κ.snd)) e


lemma rowInformation_eq_sourceConditionalInformation {S W X : Type*}
    [MeasurableSpace S] [MeasurableSpace W] [MeasurableSpace X]
    [StandardBorelSpace W] [StandardBorelSpace X]
    (P : Measure ((S×W)×X)) [IsProbabilityMeasure P]
    (ν : Measure S) (γ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure γ]
    (hInd : (P.map swapLast).fst = ν.prod γ) :
    rowInformation P γ = conditionalMutualInformation
      (P.map (fun p => (p.1.1,(p.2,p.1.2)))) := by
  let := nonempty_of_isProbabilityMeasure P
  let : Nonempty W := ⟨(Classical.choice (inferInstance : Nonempty ((S×W)×X))).1.2⟩
  let : Nonempty X := ⟨(Classical.choice (inferInstance : Nonempty ((S×W)×X))).2⟩
  let : IsProbabilityMeasure (P.map (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X))) :=
    Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  rw [rowInformation_eq_conditionalMutualInformation P ν γ hInd]
  have he := conditionalMutualInformation_swap
    (P.map (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X)))
  have hfun : (Prod.map id Prod.swap ∘
      (MeasurableEquiv.prodAssoc : (S×W)×X ≃ᵐ S×(W×X))) =
      (fun p : (S×W)×X => (p.1.1,(p.2,p.1.2))) := rfl
  simpa only [Measure.map_map (measurable_id.prodMap measurable_swap)
    MeasurableEquiv.prodAssoc.measurable, hfun] using he.symm




theorem actualRowSourceRefinement_oai {d m : ℕ} {W E : Type*} [MeasurableSpace W]
    [MeasurableSpace E] [Countable W] [MeasurableSingletonClass W]
    [Countable E] [MeasurableSingletonClass E]
    (P : Measure ((Sphere d×W)×Rows m d)) [IsProbabilityMeasure P]
    (ν : Measure (Sphere d)) [IsProbabilityMeasure ν]
    (hInd : (P.map swapLast).fst = ν.prod (gaussianRows m d))
    (e : Sphere d×W → E) (he : Measurable e)
    (hEntropy : shannonEntropy
      ((P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))).map swapLast).snd ≠ ∞) :
    actualConditionalRowInformation (P.map (fun p => ((p.1.1,(p.1.2,e p.1)),p.2))) =
      actualConditionalRowInformation P := by
  let F : (Sphere d×W)×Rows m d → (Sphere d×(W×E))×Rows m d :=
    fun p => ((p.1.1,(p.1.2,e p.1)),p.2)
  have hF : Measurable F :=
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk (he.comp measurable_fst))).prodMk measurable_snd
  let Q := P.map F
  let : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map (by first | fun_prop | exact (measurable_of_countable _).aemeasurable | exact measurable_exposedJointMap.aemeasurable | exact measurable_observedMessageMap.aemeasurable | exact (measurable_fst.prodMk measurable_own_label).aemeasurable)
  have hIndQ : (Q.map swapLast).fst = ν.prod (gaussianRows m d) := by
    trans (P.map swapLast).fst
    · dsimp only [Q,Measure.fst]
      rw [Measure.map_map swapLast.measurable hF,
        Measure.map_map measurable_fst (swapLast.measurable.comp hF),
        Measure.map_map measurable_fst swapLast.measurable]
      rfl
    · exact hInd
  have hiQ := rowInformation_eq_sourceConditionalInformation Q ν (gaussianRows m d) hIndQ
  have hi := rowInformation_eq_sourceConditionalInformation P ν (gaussianRows m d) hInd
  change actualConditionalRowInformation Q = actualConditionalRowInformation P
  calc
    _ = rowInformation Q (gaussianRows m d) := hiQ.symm
    _ = rowInformation P (gaussianRows m d) := actualRowRefinement P e he hEntropy
    _ = _ := hi





end CurrentProjection

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CurrentProjection.actualRowSourceRefinement_oai.{u_1, u_2} := @OAI.CurrentProjection.actualRowSourceRefinement_oai.{u_1, u_2}
