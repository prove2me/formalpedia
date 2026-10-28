-- Prove2me | solution 1 for OAI.Kadison.TracialGNS.stageWord_inner_classification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:49:50.928139+00:00
-- url     : https://prove2.me/submissions/84507479-fde7-492b-b9f7-988cccebdcf3

import Mathlib
import Definitions.Def_OAIQ039C058
import Theorems.Thm_OAI_Kadison_TracialGNS_stageCoefficient_crossing

section
-- module Solutions.OAIQ039_CM.Commutator_CenteredSpace
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

namespace Kadison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

lemma coe_center (Ω : E) (hΩ : ‖Ω‖ = 1) (x : E) :
    (center Ω x : E) = x - inner ℂ Ω x • Ω := by
  change (ℂ ∙ Ω)ᗮ.starProjection x = _
  rw [Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℂ hΩ]

end Kadison
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry5
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

namespace Kadison.HilbertTensor

open UniformSpace

open scoped TensorProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

lemma inner_map_left_adjoint (a b : E →L[ℂ] E)
    (hab : ∀ x y, inner ℂ (a x) y = inner ℂ x (b y))
    (x y : Completion (E ⊗[ℂ] F)) :
    inner ℂ (map a (1 : F →L[ℂ] F) x) y =
      inner ℂ x (map b (1 : F →L[ℂ] F) y) := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y =>
    induction x using OAI.tensorInductionOn with
    | add x x' hx hx' =>
      simp only [Completion.coe_add, map_add, inner_add_left, hx, hx']
    | tmul x v =>
      induction y using OAI.tensorInductionOn with
      | add y y' hy hy' =>
        simp only [Completion.coe_add, map_add, inner_add_right, hy, hy']
      | tmul y w =>
        simp only [map_coe_tmul, one_apply_eq_self, Completion.inner_coe,
          TensorProduct.inner_tmul, hab]

end Kadison.HilbertTensor
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixTrace
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

namespace Kadison.MatrixTrace

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

variable (φ : Matrix I I ℂ →ₗ[ℂ] ℂ)

variable (htr : ∀ x y, φ (x * y) = φ (y * x)) (hunit : φ 1 = 1)

include htr

lemma off_diagonal (i j : I) (hij : i ≠ j) : φ (single i j 1) = 0 := by
  have h := htr (single i i 1) (single i j 1)
  have hz : (single i j (1 : ℂ)) * single i i 1 = 0 :=
    Matrix.single_mul_single_of_ne 1 i j i hij.symm 1
  simpa [hz] using h

lemma diagonal_eq (i j : I) : φ (single i i 1) = φ (single j j 1) := by
  simpa using htr (single i j 1) (single j i 1)

variable [Nonempty I]

include hunit

lemma diagonal (i : I) : φ (single i i 1) = (Fintype.card I : ℂ)⁻¹ := by
  have hcard : (Fintype.card I : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h : (Fintype.card I : ℂ) * φ (single i i 1) = 1 := by
    calc
      _ = ∑ j : I, φ (single j j 1) := by
        simp only [← diagonal_eq φ htr i, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
      _ = φ 1 := by rw [← map_sum, Matrix.sum_single_one]
      _ = 1 := hunit
  apply (mul_left_cancel₀ hcard)
  rw [h, mul_inv_cancel₀ hcard]

lemma unique (a : Matrix I I ℂ) : φ a = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  have hsingle (i j : I) : φ (single i j (a i j)) =
      if i = j then (Fintype.card I : ℂ)⁻¹ * a i j else 0 := by
    have hs : single i j (a i j) = a i j • (single i j (1 : ℂ)) := by
      ext k l
      simp [Matrix.single]
    rw [hs, map_smul]
    by_cases hij : i = j
    · subst j
      rw [diagonal φ htr hunit, ite_eq_left rfl]
      exact mul_comm _ _
    · rw [off_diagonal φ htr i j hij, ite_eq_right hij, smul_zero]
  calc
    φ a = ∑ i : I, ∑ j : I, φ (single i j (a i j)) := by
      nth_rw 1 [Matrix.matrix_eq_sum_single a]
      simp only [map_sum]
    _ = (Fintype.card I : ℂ)⁻¹ * a.trace := by
      simp [hsingle, Matrix.trace, ← Finset.mul_sum]

end Kadison.MatrixTrace
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixGNS
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

namespace Kadison.TracialGNS

open Matrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

variable (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)

omit [StarOrderedRing A] in
include hτ h1 in
lemma stage_trace (a : Matrix I I ℂ) :
    τ (φ a) = (Fintype.card I : ℂ)⁻¹ * a.trace := by
  apply MatrixTrace.unique (τ.toLinearMap.comp φ.toLinearMap)
  · intro x y
    change τ (φ (x*y)) = τ (φ (y*x))
    simpa only [map_mul] using hτ (φ x) (φ y)
  · change τ (φ 1) = 1
    simpa using h1

include hτ h1 in
lemma stage_inner (a b : Matrix I I ℂ) :
    inner ℂ (stageVector τ φ a) (stageVector τ φ b) =
      (Fintype.card I : ℂ)⁻¹ * (star a * b).trace := by
  change inner ℂ (algebraVector τ (φ a)) (algebraVector τ (φ b)) = _
  rw [inner_algebraVector, ← map_star, ← map_mul, stage_trace τ hτ h1 φ]

include hτ h1 in
lemma stage_centered (a : Matrix I I ℂ) :
    (centeredStageVector τ φ a : τ.GNS) =
      stageVector τ φ a - ((Fintype.card I : ℂ)⁻¹ * a.trace) • vacuum τ := by
  change (center (vacuum τ) (algebraVector τ (φ a)) : τ.GNS) = _
  rw [coe_center _ (vacuum_norm τ h1), inner_vacuum_algebraVector,
    stage_trace τ hτ h1 φ]
  rfl

end Kadison.TracialGNS
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry6
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

namespace Kadison.TracialGNS

open PreHilbert UniformSpace

open scoped TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a * b) = τ (b * a)) (h1 : τ 1 = 1)

lemma wordLeft_inner (a : A) (n : ℕ)
    (x y : wordSpace (fullSpace τ) (zeroSpace τ) n) :
    inner ℂ (wordLeft τ a n x) y = inner ℂ x (wordLeft τ (star a) n y) := by
  apply HilbertTensor.inner_map_left_adjoint
  intro x y
  rw [map_star, ContinuousLinearMap.star_eq_adjoint]
  exact (ContinuousLinearMap.adjoint_inner_right (τ.gnsStarAlgHom a) x y).symm

lemma wordLeft_word (a d : A) (n : ℕ) (x : Fin n → zeroSpace τ) :
    wordLeft τ a n (word (fullSpace τ) (zeroSpace τ) n (algebraVector τ d) x) =
      word (fullSpace τ) (zeroSpace τ) n (algebraVector τ (a*d)) x := by
  simp only [wordLeft, word, HilbertTensor.map_coe_tmul, one_apply_eq_self,
    algebraVector_apply, left_coe]

variable {k l : ℕ}

variable (Y : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
  wordSpace (fullSpace τ) (zeroSpace τ) l)

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

lemma word_inner_move_endpoint
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (d c : A) (x : Fin k → zeroSpace τ) (y : Fin l → zeroSpace τ) :
    inner ℂ (word (fullSpace τ) (zeroSpace τ) l (algebraVector τ c) y)
      (Y (word (fullSpace τ) (zeroSpace τ) k (algebraVector τ d) x)) =
      inner ℂ (word (fullSpace τ) (zeroSpace τ) l (algebraVector τ (star d * c)) y)
        (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) := by
  have hd : word (fullSpace τ) (zeroSpace τ) k (algebraVector τ d) x =
      wordLeft τ d k (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x) := by
    have hv : algebraVector τ (1 : A) = vacuum τ := rfl
    simpa only [mul_one, hv] using (wordLeft_word τ d 1 k x).symm
  have hy : Y (wordLeft τ d k (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) =
      wordLeft τ d l (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) :=
    congrArg (fun T : wordSpace (fullSpace τ) (zeroSpace τ) k →L[ℂ]
      wordSpace (fullSpace τ) (zeroSpace τ) l =>
        T (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x)) (hleft d)
  have hm := wordLeft_inner τ (star d) l
    (word (fullSpace τ) (zeroSpace τ) l (algebraVector τ c) y)
    (Y (word (fullSpace τ) (zeroSpace τ) k (vacuum τ) x))
  rw [wordLeft_word, star_star] at hm
  rw [hd, hy]
  exact hm.symm

omit [Nonempty I] in
lemma word_inner_stageCoefficient (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y)
    (d c : Matrix I I ℂ) (x : Fin k → Matrix I I ℂ) (y : Fin l → Matrix I I ℂ) :
    inner ℂ (word (fullSpace τ) (zeroSpace τ) l (stageVector τ φ c)
      (fun j => centeredStageVector τ φ (y j)))
      (Y (word (fullSpace τ) (zeroSpace τ) k (stageVector τ φ d)
        (fun i => centeredStageVector τ φ (x i)))) =
      stageCoefficient τ Y φ (fun o : Option (Fin k ⊕ Fin l) =>
        o.elim (star c * d) (Sum.elim x (fun j => star (y j)))) := by
  have h := word_inner_move_endpoint τ Y hleft (φ d) (φ c)
    (fun i => centeredStageVector τ φ (x i)) (fun j => centeredStageVector τ φ (y j))
  simp only [stageCoefficient, coefficientMultilinear, MultilinearMap.coe_mk]
  simp only [coefficient, Option.elim_none, Option.elim_some, Sum.elim_inl,
    Sum.elim_inr, star_mul, star_star]
  have ha : stageVector τ φ (star d * c) = algebraVector τ (star (φ d) * φ c) := by
    change algebraVector τ (φ (star d * c)) = _
    rw [map_mul, map_star]
  rw [ha]
  exact h

include hτ h1 in
lemma centeredStageVector_of_trace_zero (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (a : Matrix I I ℂ) (ha : a.trace = 0) :
    (centeredStageVector τ φ a : τ.GNS) = stageVector τ φ a := by
  rw [stage_centered τ hτ h1, ha, mul_zero, zero_smul, sub_zero]

include hτ h1 in
lemma centeredStageVector_inner (φ : Matrix I I ℂ →⋆ₐ[ℂ] A)
    (a b : Matrix I I ℂ) (ha : a.trace = 0) (hb : b.trace = 0) :
    inner ℂ (centeredStageVector τ φ a) (centeredStageVector τ φ b) =
      (Fintype.card I : ℂ)⁻¹ * Matrix.trace (b * star a) := by
  change inner ℂ (centeredStageVector τ φ a : τ.GNS)
    (centeredStageVector τ φ b : τ.GNS) = _
  rw [centeredStageVector_of_trace_zero τ hτ h1 φ a ha,
    centeredStageVector_of_trace_zero τ hτ h1 φ b hb, stage_inner τ hτ h1]
  rw [Matrix.trace_mul_comm]

include hτ h1 in
theorem stageWord_inner_classification_oai (I : ℕ → Type*)
    [∀ n, Fintype (I n)] [∀ n, DecidableEq (I n)] [∀ n, Nonempty (I n)]
    (φ : ∀ n, Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] A)
    (e : ∀ {n m : ℕ}, n ≤ m → Matrix (I n) (I n) ℂ →⋆ₐ[ℂ] Matrix (I m) (I m) ℂ)
    (he : ∀ n m (h : n ≤ m) a, φ m (e h a) = φ n a)
    (hsize : ∀ n q : ℕ, ∃ m, n ≤ m ∧ q ≤ Fintype.card (I m))
    (hY : ∀ n (u : unitary (Matrix (I n) (I n) ℂ)),
      Y.comp (wordConjugation τ hτ (stageUnitary (φ n) u) k).toContinuousLinearMap =
        (wordConjugation τ hτ (stageUnitary (φ n) u) l).toContinuousLinearMap.comp Y)
    (hleft : ∀ a : A, Y.comp (wordLeft τ a k) = (wordLeft τ a l).comp Y) :
    ∃ c₀ : (Fin k ≃ Fin l) → ℂ, ∀ n (d c : Matrix (I n) (I n) ℂ)
      (x : Fin k → Matrix (I n) (I n) ℂ) (y : Fin l → Matrix (I n) (I n) ℂ),
      (∀ i, Matrix.trace (x i) = 0) → (∀ j, Matrix.trace (y j) = 0) →
      inner ℂ (word (fullSpace τ) (zeroSpace τ) l (stageVector τ (φ n) c)
        (fun j => centeredStageVector τ (φ n) (y j)))
        (Y (word (fullSpace τ) (zeroSpace τ) k (stageVector τ (φ n) d)
          (fun i => centeredStageVector τ (φ n) (x i)))) =
      inner ℂ (stageVector τ (φ n) c) (stageVector τ (φ n) d) *
        ∑ b : Fin k ≃ Fin l, c₀ b * ∏ i,
          inner ℂ (centeredStageVector τ (φ n) (y (b i)))
            (centeredStageVector τ (φ n) (x i)) := by
  classical
  obtain ⟨c₀, hc₀⟩ := stageCoefficient_crossing τ hτ h1 Y I φ e he hsize hY hleft
  refine ⟨c₀, ?_⟩
  intro n d c x y hx hy
  rw [word_inner_stageCoefficient τ Y (φ n) hleft]
  let v : TailSlots k l → Matrix (I n) (I n) ℂ := Sum.elim x (fun j => star (y j))
  have hv (j : TailSlots k l) : (v j).trace = 0 := by
    cases j with
    | inl i => exact hx i
    | inr j => simp only [v, Sum.elim_inr, Matrix.star_eq_conjTranspose,
        Matrix.trace_conjTranspose, hy j, star_zero]
  have h := hc₀ n (star c * d) v hv
  change stageCoefficient τ Y (φ n)
    (fun o : Option (TailSlots k l) => o.elim (star c * d) v) = _
  refine h.trans ?_
  rw [stage_inner τ hτ h1]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (centeredStageVector_inner τ hτ h1 (φ n) (y (b i)) (x i) (hy _) (hx _)).symm

end Kadison.TracialGNS
end

end OAI
end

theorem solution.{u_2} : type_of% @OAI.Kadison.TracialGNS.stageWord_inner_classification_oai.{u_2} := @OAI.Kadison.TracialGNS.stageWord_inner_classification_oai.{u_2}
