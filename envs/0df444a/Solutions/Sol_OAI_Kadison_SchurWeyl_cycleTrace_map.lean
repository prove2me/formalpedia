-- Prove2me | solution 1 for OAI.Kadison.SchurWeyl.cycleTrace_map
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:25:44.619599+00:00
-- url     : https://prove2.me/submissions/14f54fdd-bc00-4e16-aa89-2043073379d5

import Mathlib
import Definitions.Def_OAIQ039C049

section
-- module Solutions.OAIQ039_CM.Commutator_CycleInvariants
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.SchurWeyl.instDecidableEqCycleSet _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
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

lemma fixedLabel_card (R : Type*) [Fintype R] [DecidableEq R] (σ : Equiv.Perm J) :
    Fintype.card {f : J → R // ∀ j, f (σ j) = f j} =
      Fintype.card R ^ cycleCount σ := by
  classical
  rw [Fintype.card_congr (fixedLabelEquiv R σ), Fintype.card_fun, cycleCount]

omit [Fintype I] [DecidableEq I] [DecidableEq J] in
lemma prod_inflateMatrix {R : Type*} [DecidableEq R]
    (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) (a : J → I) (r : J → R) :
    (∏ j, inflateMatrix (A j) (a (σ j), r (σ j)) (a j, r j)) =
      if ∀ j, r (σ j) = r j then ∏ j, A j (a (σ j)) (a j) else 0 := by
  classical
  by_cases h : ∀ j, r (σ j) = r j
  · simp [inflateMatrix, h]
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

omit [Fintype I] [DecidableEq I] in
lemma fixedLabel_indicator_sum (R : Type*) [Fintype R] [DecidableEq R]
    (σ : Equiv.Perm J) :
    (∑ r : J → R, if ∀ j, r (σ j) = r j then (1 : 𝕜) else 0) =
      (Fintype.card R : 𝕜) ^ cycleCount σ := by
  classical
  calc
    _ = (Fintype.card {r : J → R // ∀ j, r (σ j) = r j} : 𝕜) := by
      rw [Fintype.card_subtype]
      exact Finset.sum_boole _ _
    _ = _ := by rw [fixedLabel_card, Nat.cast_pow]

lemma rawCycleTrace_inflate (R : Type*) [Fintype R] [DecidableEq R]
    (σ : Equiv.Perm J) (A : J → Matrix I I 𝕜) :
    rawCycleTrace σ (fun j => inflateMatrix (R := R) (A j)) =
      (Fintype.card R : 𝕜) ^ cycleCount σ * rawCycleTrace σ A := by
  classical
  rw [rawCycleTrace_eq_sum, rawCycleTrace_eq_sum]
  calc
    _ = ∑ ar : (J → I) × (J → R),
        ∏ j, inflateMatrix (A j) (ar.1 (σ j), ar.2 (σ j)) (ar.1 j, ar.2 j) := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow J (fun _ => I) (fun _ => R))
      intro x
      rfl
    _ = ∑ a : J → I, ∑ r : J → R,
        ∏ j, inflateMatrix (A j) (a (σ j), r (σ j)) (a j, r j) :=
      Fintype.sum_prod_type _
    _ = ∑ a : J → I, ∑ r : J → R,
        (if ∀ j, r (σ j) = r j then (1 : 𝕜) else 0) *
          ∏ j, A j (a (σ j)) (a j) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro r _
      rw [prod_inflateMatrix]
      split_ifs <;> simp
    _ = _ := by
      simp_rw [← Finset.sum_mul, fixedLabel_indicator_sum]
      rw [Finset.mul_sum]

lemma cycleTrace_inflate (R : Type*) [Fintype R] [DecidableEq R] [Nonempty R]
    (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) :
    cycleTrace σ (fun j => inflateMatrix (R := R) (A j)) = cycleTrace σ A := by
  classical
  have hr : (Fintype.card R : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [cycleTrace, Fintype.card_prod, Nat.cast_mul, _root_.mul_inv_rev, mul_pow,
    rawCycleTrace_inflate]
  have hc : ((Fintype.card R : ℂ)⁻¹ ^ cycleCount σ) *
      (Fintype.card R : ℂ) ^ cycleCount σ = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hr, one_pow]
  calc
    _ = (((Fintype.card R : ℂ)⁻¹ ^ cycleCount σ) *
        (Fintype.card R : ℂ) ^ cycleCount σ) *
          ((Fintype.card I : ℂ)⁻¹ ^ cycleCount σ * rawCycleTrace σ A) := by ring
    _ = _ := by rw [hc, one_mul]

end Kadison.SchurWeyl
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixModules
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

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I E : Type*} [Field 𝕜] [Fintype I] [DecidableEq I]
  [AddCommGroup E] [Module 𝕜 E]

variable (ρ : Matrix I I 𝕜 →ₐ[𝕜] Module.End 𝕜 E) (o : I)

lemma moduleEquiv_intertwines (a : Matrix I I 𝕜) (x : I → corner ρ o) :
    ρ a (moduleEquiv ρ o x) = moduleEquiv ρ o (fun i => ∑ j, a i j • x j) := by
  change ρ a (recombine ρ o x) = recombine ρ o _
  simp only [recombine_apply, Submodule.coe_sum, Submodule.coe_smul, map_sum,
    map_smul]
  have hm (j : I) : a * single j o 1 = ∑ i, a i j • single i o 1 := by
    ext i k
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.single, Matrix.of_apply]
    by_cases h : o = k <;> simp [h]
  calc
    (∑ j, ρ a (ρ (single j o 1) (x j : E))) =
        ∑ j, ∑ i, a i j • ρ (single i o 1) (x j : E) := by
      apply Finset.sum_congr rfl
      intro j _
      change (ρ a * ρ (single j o 1)) (x j : E) = _
      rw [← map_mul, hm, map_sum, LinearMap.sum_apply]
      simp only [map_smul, LinearMap.smul_apply]
    _ = _ := Finset.sum_comm

section Coordinates

variable {R : Type*} [Fintype R]

omit [DecidableEq I] in
lemma inflate_mulVec [DecidableEq R] (a : Matrix I I 𝕜) (v : I × R → 𝕜)
    (i : I) (r : R) : (inflate (R := R) a *ᵥ v) (i, r) = ∑ j, a i j * v (j, r) := by
  classical
  simp [Matrix.mulVec, dotProduct, inflate, Fintype.sum_prod_type]

lemma basisCopies_intertwines [DecidableEq R] (b : Module.Basis R 𝕜 (corner ρ o))
    (a : Matrix I I 𝕜) (v : I × R → 𝕜) :
    basisCopies ρ o b (inflate a *ᵥ v) =
      fun i => ∑ j, a i j • basisCopies ρ o b v j := by
  funext i
  simp only [basisCopies_apply, inflate_mulVec]
  apply b.equivFun.injective
  rw [LinearEquiv.apply_symm_apply, map_sum]
  simp only [map_smul, LinearEquiv.apply_symm_apply]
  ext r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

lemma representationEquiv_intertwines [DecidableEq R]
    (b : Module.Basis R 𝕜 (corner ρ o)) (a : Matrix I I 𝕜) (v : I × R → 𝕜) :
    ρ a (representationEquiv ρ o b v) = representationEquiv ρ o b (inflate a *ᵥ v) := by
  change ρ a (moduleEquiv ρ o (basisCopies ρ o b v)) =
    moduleEquiv ρ o (basisCopies ρ o b (inflate a *ᵥ v))
  rw [moduleEquiv_intertwines, basisCopies_intertwines]

end Coordinates

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_MatrixClassification
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

namespace Kadison.MatrixModules

open Matrix

variable {𝕜 I K R : Type*} [Field 𝕜]
  [Fintype I] [DecidableEq I] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R]

variable (φ : Matrix I I 𝕜 →ₐ[𝕜] Matrix K K 𝕜) (o : I)

lemma backward_forward
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    backwardMatrix φ o b * forwardMatrix φ o b = 1 := by
  unfold backwardMatrix forwardMatrix
  rw [← LinearMap.toMatrix'_comp]
  have h : (coordinateEquiv φ o b).symm.toLinearMap.comp
      (coordinateEquiv φ o b).toLinearMap = LinearMap.id := by ext x; simp
  rw [h, LinearMap.toMatrix'_id]

lemma classification
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) (a : Matrix I I 𝕜) :
    φ a = (HMul.hMul (self := Matrix.instHMulOfFintypeOfMulOfAddCommMonoid)
      (forwardMatrix φ o b) (inflate (R := R) a) : Matrix K (I × R) 𝕜) * backwardMatrix φ o b := by
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul]
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, forwardMatrix, backwardMatrix,
    Matrix.toLin'_toMatrix', LinearEquiv.coe_coe]
  change (matrixRepresentation φ a) x = _
  have h := representationEquiv_intertwines (matrixRepresentation φ) o b a
    ((coordinateEquiv φ o b).symm x)
  simpa only [coordinateEquiv, LinearEquiv.apply_symm_apply, Matrix.toLin'_apply] using h

omit [DecidableEq R] in
lemma dimensions
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) :
    Fintype.card I * Fintype.card R = Fintype.card K := by
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod] using
    (coordinateEquiv φ o b).finrank_eq

omit [DecidableEq R] in
lemma multiplicity_nonempty [Nonempty K]
    (b : Module.Basis R 𝕜 (corner (matrixRepresentation φ) o)) : Nonempty R := by
  apply Fintype.card_pos_iff.mp
  have h := dimensions φ o b
  have hK := Fintype.card_pos (α := K)
  nlinarith

end Kadison.MatrixModules
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RectangularTensors
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

namespace Kadison.RectangularTensors

open Matrix

variable {𝕜 : Type*} [CommRing 𝕜]

variable {I K L J : Type*} [Fintype I] [Fintype K] [Fintype L] [Fintype J] [DecidableEq J]

omit [Fintype I] [Fintype L] in
lemma tensor_mul (A : J → Matrix I K 𝕜) (B : J → Matrix K L 𝕜) :
    tensor (fun j => A j * B j) = tensor A * tensor B := by
  classical
  ext a b
  simp only [tensor, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  simp only [← Finset.prod_mul_distrib]

omit [Fintype I] [DecidableEq J] in
lemma tensor_one [DecidableEq I] : tensor (fun _ : J => (1 : Matrix I I 𝕜)) = 1 := by
  classical
  ext a b
  simp only [tensor, Matrix.one_apply]
  by_cases h : a = b
  · subst b; simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

lemma tensor_constant_natural [DecidableEq I] [DecidableEq K]
    (X : Matrix I K 𝕜) (σ : Equiv.Perm J) :
    tensor (fun _ : J => X) * perm (𝕜 := 𝕜) (I := K) σ = perm (𝕜 := 𝕜) (I := I) σ * tensor (fun _ : J => X) := by
  classical
  ext a b
  simp only [Matrix.mul_apply, perm, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (b ∘ σ.symm)]
  · rw [ite_eq_left rfl]
    rw [Finset.sum_eq_single (a ∘ σ)]
    · have ha : a = (a ∘ σ) ∘ σ.symm := by ext j; simp
      rw [ite_eq_left ha, one_mul]
      simp only [tensor, Function.comp_apply]
      simpa using (Equiv.prod_comp σ.symm (fun j => X (a (σ j)) (b j)))
    · intro c _ hc
      rw [ite_eq_right (by intro h; apply hc; ext j; simpa using (congrFun h (σ j)).symm),
        zero_mul]
    · simp
  · intro c _ hc
    exact ite_eq_right hc
  · simp

lemma trace_transport [DecidableEq I] [DecidableEq K]
    (X : Matrix I K 𝕜) (Y : Matrix K I 𝕜) (hYX : Y * X = 1)
    (A : J → Matrix K K 𝕜) (σ : Equiv.Perm J) :
    Matrix.trace (perm (𝕜 := 𝕜) (I := I) σ * tensor (fun j => X * A j * Y)) =
      Matrix.trace (perm (𝕜 := 𝕜) (I := K) σ * tensor A) := by
  rw [tensor_mul, tensor_mul]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [← Matrix.mul_assoc (tensor (fun _ : J => Y))
    (perm (𝕜 := 𝕜) (I := I) σ * tensor (fun _ : J => X)) (tensor A)]
  rw [← Matrix.mul_assoc (tensor (fun _ : J => Y)) (perm (𝕜 := 𝕜) (I := I) σ)
    (tensor (fun _ : J => X)), tensor_constant_natural Y σ]
  rw [Matrix.mul_assoc (perm (𝕜 := 𝕜) (I := K) σ), ← tensor_mul]
  simp only [hYX, tensor_one, Matrix.mul_one]

end Kadison.RectangularTensors
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CycleEmbeddings
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

variable {I K J : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype K] [DecidableEq K] [Nonempty K] [Fintype J] [DecidableEq J]

theorem cycleTrace_map_oai (φ : Matrix I I ℂ →ₐ[ℂ] Matrix K K ℂ)
    (σ : Equiv.Perm J) (A : J → Matrix I I ℂ) :
    cycleTrace σ (fun j => φ (A j)) = cycleTrace σ A := by
  classical
  let o : I := Classical.choice ‹Nonempty I›
  let E := MatrixModules.corner (MatrixModules.matrixRepresentation φ) o
  let R := Fin (Module.finrank ℂ E)
  let b : Module.Basis R ℂ E := Module.finBasis ℂ E
  let : Nonempty R := MatrixModules.multiplicity_nonempty φ o b
  let X := MatrixModules.forwardMatrix φ o b
  let Y := MatrixModules.backwardMatrix φ o b
  have hYX : Y * X = 1 := MatrixModules.backward_forward φ o b
  have hA : (fun j => φ (A j)) = fun j => X * inflateMatrix (R := R) (A j) * Y := by
    funext j
    exact MatrixModules.classification φ o b (A j)
  have hr : rawCycleTrace σ (fun j => φ (A j)) =
      rawCycleTrace σ (fun j => inflateMatrix (R := R) (A j)) := by
    rw [hA]
    exact RectangularTensors.trace_transport X Y hYX _ σ
  have hc : Fintype.card K = Fintype.card (I × R) := by
    simpa only [Fintype.card_prod] using (MatrixModules.dimensions φ o b).symm
  calc
    _ = cycleTrace σ (fun j => inflateMatrix (R := R) (A j)) := by
      simp only [cycleTrace, hr, hc]
    _ = _ := cycleTrace_inflate R σ A

end Kadison.SchurWeyl
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.SchurWeyl.cycleTrace_map_oai.{u_1, u_2, u_3} := @OAI.Kadison.SchurWeyl.cycleTrace_map_oai.{u_1, u_2, u_3}
