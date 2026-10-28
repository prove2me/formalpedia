-- Prove2me | solution 1 for OAI.Kadison.SchurWeyl.centered_expansion_contractions
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:24:59.620359+00:00
-- url     : https://prove2.me/submissions/56e8e49d-c7f7-4710-84ad-acac74feb1cf

import Mathlib
import Definitions.Def_OAIQ039C052
import Theorems.Thm_OAI_Kadison_SchurWeyl_centered_expansion_pairings

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.SchurWeyl

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma rawCycleTrace_eq_sum (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ A = ∑ a : J → I, ∏ j, A j (a (σ j)) (a j) := by
  classical
  simp only [rawCycleTrace, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    permutationMatrix, tensorMatrices]
  apply Finset.sum_congr rfl
  intro a _
  have he (b : J → I) : a = b ∘ σ.symm ↔ b = a ∘ σ := by
    constructor
    · intro h; ext j; simpa using (congrFun h (σ j)).symm
    · rintro rfl; simp [Function.comp_def]
  simp only [he, ite_mul, one_mul, zero_mul]
  simp

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_PairTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.Pairing

variable {J : Type*} [LinearOrder J]

theorem prod_pairs [Fintype J] {R : Type*} [CommMonoid R]
    (σ : Pairing J) (f : J → R) :
    (∏ j, f j) = ∏ r : Representatives σ, f r * f (σ r) := by
  classical
  rw [← (pairEquiv σ).prod_comp f, Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro r _
  rw [Fintype.prod_bool]
  simp only [pairEquiv_true, pairEquiv_false, mul_comm]

theorem sum_prod_pairs [Fintype J] {I R : Type*} [Fintype I] [CommSemiring R]
    (σ : Pairing J) (A : J → I → I → R) :
    (∑ b : J → I, ∏ j, A j (b (σ j)) (b j)) =
      ∏ r : Representatives σ, ∑ i : I, ∑ j : I, A r j i * A (σ r) i j := by
  classical
  calc
    _ = ∑ b : J → I, ∏ r : Representatives σ,
        A r (b (σ r)) (b r) * A (σ r) (b r) (b (σ r)) := by
      apply Finset.sum_congr rfl
      intro b _
      simpa only [apply_apply] using prod_pairs σ (fun j => A j (b (σ j)) (b j))
    _ = ∑ b : Representatives σ → Bool → I, ∏ r : Representatives σ,
        A r (b r true) (b r false) * A (σ r) (b r false) (b r true) := by
      apply Fintype.sum_equiv (pairFunctionEquiv σ I)
      intro b
      simp only [pairFunctionEquiv_apply, pairEquiv_true, pairEquiv_false]
    _ = ∏ r : Representatives σ, ∑ b : Bool → I,
        A r (b true) (b false) * A (σ r) (b false) (b true) := by
      exact (Fintype.prod_sum (fun (r : Representatives σ) (b : Bool → I) =>
        A r (b true) (b false) * A (σ r) (b false) (b true))).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro r _
      have he := Fintype.sum_equiv (Equiv.boolArrowEquivProd I)
        (fun b : Bool → I => A r (b true) (b false) * A (σ r) (b false) (b true))
        (fun b : I × I => A r b.2 b.1 * A (σ r) b.1 b.2) (fun b => rfl)
      rw [Fintype.sum_prod_type] at he
      exact he

end Kadison.Pairing
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J I : Type*} [Fintype J] [LinearOrder J] [Fintype I] [DecidableEq I]

theorem rawCycleTrace_pairing {𝕜 : Type*} [CommRing 𝕜]
    (σ : Pairing J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ.val A =
      ∏ r : Pairing.Representatives σ, Matrix.trace (A r * A (σ r)) := by
  rw [rawCycleTrace_eq_sum]
  rw [Pairing.sum_prod_pairs σ A]
  apply Finset.prod_congr rfl
  intro r _
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J I : Type*} [Fintype J] [LinearOrder J] [Fintype I] [DecidableEq I]

lemma cycleCount_endpointPairing (σ : Pairing J) :
    cycleCount (endpointPairingPerm σ) = Fintype.card (Pairing.Representatives σ) + 1 := by
  have hh := Fintype.card_congr (endpointPairingCycleEquiv σ)
  simpa only [cycleCount, Fintype.card_option] using hh

theorem rawCycleTrace_option {𝕜 : Type*} [CommRing 𝕜]
    (σ : Equiv.Perm J) (A : Option J → Matrix I I 𝕜) :
    rawCycleTrace (Equiv.optionCongr σ) A =
      Matrix.trace (A none) * rawCycleTrace σ (fun j => A (some j)) := by
  classical
  rw [rawCycleTrace_eq_sum, rawCycleTrace_eq_sum]
  simp only [Fintype.prod_option, Equiv.optionCongr_apply, Option.map_none, Option.map_some]
  calc
    _ = ∑ b : I × (J → I), A none b.1 b.1 * ∏ j, A (some j) (b.2 (σ j)) (b.2 j) := by
      exact Fintype.sum_equiv Equiv.piOptionEquivProd _ _ (fun _ => rfl)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
      rfl

theorem cycleTrace_endpointPairing (σ : Pairing J) (A : Option J → Matrix I I ℂ) :
    cycleTrace (endpointPairingPerm σ) A =
      (Fintype.card I : ℂ)⁻¹ * Matrix.trace (A none) *
        Pairing.contraction σ (fun X Y => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
          (fun j => A (some j)) := by
  classical
  rw [cycleTrace, cycleCount_endpointPairing]
  change (Fintype.card I : ℂ)⁻¹ ^ (Fintype.card (Pairing.Representatives σ) + 1) *
    rawCycleTrace (Equiv.optionCongr σ.val) A = _
  rw [rawCycleTrace_option, rawCycleTrace_pairing, pow_succ]
  have hc : Pairing.contraction σ
      (fun (X Y : Matrix I I ℂ) => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
        (fun j => A (some j)) =
      (Fintype.card I : ℂ)⁻¹ ^ Fintype.card (Pairing.Representatives σ) *
        ∏ r : Pairing.Representatives σ, Matrix.trace (A (some r.1) * A (some (σ r))) := by
    unfold Pairing.contraction
    rw [Finset.prod_subtype (p := fun j => j < σ j) (F := inferInstance) _ (by simp)]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
  rw [hc]
  ring

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CyclePairTrace3
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace Kadison.SchurWeyl

variable {J : Type*}

variable [Fintype J] [LinearOrder J]

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem centered_expansion_contractions_oai (d : Equiv.Perm (Option J) → ℂ)
    (hd : ∀ σ, 2 * cycleCount σ < Fintype.card (Option J) + 1 → d σ = 0)
    (A : Option J → Matrix I I ℂ) (hA : ∀ j, Matrix.trace (A (some j)) = 0) :
    (∑ σ, d σ * cycleTrace σ A) =
      ((Fintype.card I : ℂ)⁻¹ * Matrix.trace (A none)) *
        ∑ τ : Pairing J, d (endpointPairingPerm τ) *
          Pairing.contraction τ
            (fun X Y => (Fintype.card I : ℂ)⁻¹ * Matrix.trace (X * Y))
            (fun j => A (some j)) := by
  classical
  rw [centered_expansion_pairings none d hd A (by
    intro j hj
    cases j with
    | none => exact (hj rfl).elim
    | some j => exact hA j)]
  have hfilter : (Finset.univ.filter (fun σ : Equiv.Perm (Option J) =>
      σ none = none ∧ (∀ j, σ (σ j) = j) ∧ ∀ j, σ j = j → j = none)) =
      Finset.univ.filter IsEndpointPairing := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsEndpointPairing]
  rw [hfilter]
  rw [Finset.sum_subtype (p := IsEndpointPairing) (F := inferInstance) _ (by simp)]
  rw [← endpointPairingEquiv.sum_comp (fun σ => d σ.1 * cycleTrace σ.1 A)]
  change (∑ τ : Pairing J, d (endpointPairingPerm τ) *
    cycleTrace (endpointPairingPerm τ) A) = _
  simp_rw [cycleTrace_endpointPairing]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  ring

end Kadison.SchurWeyl
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.SchurWeyl.centered_expansion_contractions_oai.{u_1, u_2} := @OAI.Kadison.SchurWeyl.centered_expansion_contractions_oai.{u_1, u_2}
