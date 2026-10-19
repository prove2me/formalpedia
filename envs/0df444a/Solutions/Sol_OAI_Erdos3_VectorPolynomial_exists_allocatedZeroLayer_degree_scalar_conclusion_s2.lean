-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_degree_scalar_conclusion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:02:02.143218+00:00
-- url     : https://prove2.me/submissions/664736bf-31b7-4e7b-9d71-4bdca483cd1d

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B266
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedZeroLayer_scalar_passage_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped BigOperators Classical

variable {σ R : Type*} [CommRing R] [Fintype σ]

theorem polynomialShearBasis_coordinate_eval (w : σ → ℕ)
    [Fintype (PolynomialShearIndex w)] (D : PolynomialShearLieAlgebra w R) (i : σ) :
    D.val (X i) = ∑ a : PolynomialShearIndex w,
      if a.1 = i then C ((polynomialShearBasis (R := R) w).repr D a) * monomial a.2.val 1
      else 0 := by
  classical
  let ev : PolynomialShearLieAlgebra w R →ₗ[R] MvPolynomial σ R :=
    { toFun := fun E => E.val (X i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  calc
    D.val (X i) = ev (∑ a, (polynomialShearBasis (R := R) w).repr D a •
        polynomialShearBasis (R := R) w a) :=
      congrArg ev ((polynomialShearBasis (R := R) w).sum_repr D).symm
    _ = ∑ a, (polynomialShearBasis (R := R) w).repr D a •
        (polynomialShearBasis (R := R) w a).val (X i) := by
      rw [map_sum]
      simp only [map_smul]
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      rw [polynomialShearBasis_eq_monomial, polynomialShearMonomial_X]
      by_cases h : a.1 = i
      · simp [h, smul_eq_C_mul]
      · simp [h, Ne.symm h]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialSymbolicShearWeightedDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R] [Algebra ℚ R]
variable {w₀ w₁ : σ → ℕ} {v₀ : τ → ℕ}

omit [Algebra ℚ R] in

theorem polynomialShear_pow_intertwine
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : PolynomialShearLieAlgebra w₀ R) (E : PolynomialShearLieAlgebra v₀ R)
    (hφ : ∀ P, φ (D.val P) = E.val (φ P)) (k : ℕ) (P : MvPolynomial σ R) :
    φ ((D.val.toLinearMap ^ k) P) = (E.val.toLinearMap ^ k) (φ P) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply]
      change φ (D.val ((D.val.toLinearMap ^ k) P)) =
        E.val ((E.val.toLinearMap ^ k) (φ P))
      rw [hφ, ih]

theorem polynomialShearExp_intertwine_of_degree
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : PolynomialShearLieAlgebra w₀ R) (E : PolynomialShearLieAlgebra v₀ R)
    (hφ : ∀ P, φ (D.val P) = E.val (φ P))
    {P : MvPolynomial σ R} {n : ℕ}
    (hP : P ∈ weightedSupportLE w₀ n) (hφP : φ P ∈ weightedSupportLE v₀ n) :
    φ (polynomialShearExp D P) = polynomialShearExp E (φ P) := by
  rw [polynomialShearExp_eq_sum D hP, polynomialShearExp_eq_sum E hφP, map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_rat_smul, polynomialShear_pow_intertwine φ D E hφ]

theorem polynomialShearExp_intertwine
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : PolynomialShearLieAlgebra w₀ R) (E : PolynomialShearLieAlgebra v₀ R)
    (hφ : ∀ P, φ (D.val P) = E.val (φ P)) (P : MvPolynomial σ R) :
    φ (polynomialShearExp D P) = polynomialShearExp E (φ P) := by
  let n := max (P.weightedTotalDegree w₀) ((φ P).weightedTotalDegree v₀)
  have hP : P ∈ weightedSupportLE w₀ n :=
    (mem_weightedSupportLE_iff w₀ n P).mpr (le_max_left _ _)
  have hφP : φ P ∈ weightedSupportLE v₀ n :=
    (mem_weightedSupportLE_iff v₀ n (φ P)).mpr (le_max_right _ _)
  exact polynomialShearExp_intertwine_of_degree φ D E hφ hP hφP

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDerivationIntertwine
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem polynomialDerivation_intertwine_of_X
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (E : Derivation R (MvPolynomial τ R) (MvPolynomial τ R))
    (hX : ∀ i, φ (D (X i)) = E (φ (X i))) (P : MvPolynomial σ R) :
    φ (D P) = E (φ P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hC : φ (C c) = C c := φ.commutes c
      simp only [hC, MvPolynomial.derivation_C, map_zero]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, hX, hP]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearWeightedOrbitCoordinates
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s)

theorem polynomialShearOrbitParameterCoordinates_eval
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
    (t : σ → ℝ) (a : PolynomialShearIndex w) :
    MvPolynomial.eval t (polynomialShearOrbitParameterCoordinates s hw g a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          (fun _ : σ => 1) t g).coord a := by
  exact (VectorPolynomial.coordinate_eval₂
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a) t g.log).symm

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped BigOperators TensorProduct

variable {σ : Type*} {d : ℕ}

theorem patchParameterSpecialization_rename_parameter (t : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    patchParameterSpecialization (d := d) t (rename Sum.inl P) = C (MvPolynomial.eval t P) := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [patchParameterSpecialization]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
    simp only [map_mul, rename_X, hP, eval_X]
    simp [patchParameterSpecialization]

theorem patchParameterSpecialization_rename_slot (t : σ → ℝ)
    (P : MvPolynomial (Fin d) ℝ) :
    patchParameterSpecialization t (rename Sum.inr P) = P := by
  induction P using MvPolynomial.induction_on with
  | C r => simp [patchParameterSpecialization]
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, rename_X, hP, patchParameterSpecialization_X_slot]

variable (w : Fin d → ℕ) [Fintype (PolynomialShearIndex w)]

omit [Fintype (PolynomialShearIndex w)] in

theorem polynomialSymbolicShearTerm_specialization
    (c : PolynomialShearIndex w → MvPolynomial σ ℝ) (t : σ → ℝ)
    (a : PolynomialShearIndex w) :
    patchParameterSpecialization t (polynomialSymbolicShearTerm w c a) =
      C (MvPolynomial.eval t (c a)) * monomial a.2.val 1 := by
  rw [polynomialSymbolicShearTerm, map_mul, patchParameterSpecialization_rename_parameter,
    patchParameterSpecialization_rename_slot]

theorem polynomialSymbolicShearSlot_specialization
    (c : PolynomialShearIndex w → MvPolynomial σ ℝ) (t : σ → ℝ) (i : Fin d) :
    patchParameterSpecialization t (polynomialSymbolicShearSlot w c i) =
      ∑ a : PolynomialShearIndex w,
        if a.1 = i then C (MvPolynomial.eval t (c a)) * monomial a.2.val 1 else 0 := by
  classical
  simp only [polynomialSymbolicShearSlot, map_sum, apply_ite,
    polynomialSymbolicShearTerm_specialization, map_zero]

variable (s : ℕ) (hw : ∀ i, w i ≤ s)
variable (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1))
variable (t : σ → ℝ)

local notation "orbitD" => polynomialShearRealificationEquiv w
  (NilpotentLieBCHGroup.coord
    (NilpotentLieFiltration.polynomialOrbitRealEval
      (NilpotentLieFiltration.realification (polynomialShearFiltration w s hw))
      (fun _ : σ => 1) t g))
local notation "symbolicD" => polynomialSymbolicShearDerivation w
  (polynomialShearOrbitParameterCoordinates s hw g)

theorem polynomialShearOrbitSymbolicDerivation_X_slot_specialization (i : Fin d) :
    patchParameterSpecialization t ((symbolicD).val (X (Sum.inr i))) = (orbitD).val (X i) := by
  rw [polynomialSymbolicShearDerivation_X_slot, polynomialSymbolicShearSlot_specialization,
    polynomialShearBasis_coordinate_eval]
  apply Finset.sum_congr rfl
  intro a ha
  rw [polynomialShearOrbitParameterCoordinates_eval, polynomialShearRealificationEquiv_repr]
  split_ifs <;> rfl

theorem polynomialShearOrbitSymbolicDerivation_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t ((symbolicD).val P) =
      (orbitD).val (patchParameterSpecialization t P) := by
  apply polynomialDerivation_intertwine_of_X (patchParameterSpecialization t) (symbolicD).val (orbitD).val
  intro i
  cases i with
  | inl i =>
    rw [polynomialSymbolicShearDerivation_X_parameter, map_zero]
    simp only [patchParameterSpecialization, aeval_X, Sum.elim_inl, MvPolynomial.derivation_C]
  | inr i =>
    rw [patchParameterSpecialization_X_slot]
    exact polynomialShearOrbitSymbolicDerivation_X_slot_specialization w s hw g t i

theorem polynomialShearOrbitSymbolicExp_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialShearExp symbolicD P) =
      polynomialShearExp orbitD (patchParameterSpecialization t P) :=
  polynomialShearExp_intertwine (patchParameterSpecialization t) symbolicD orbitD
    (polynomialShearOrbitSymbolicDerivation_specialization w s hw g t) P

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

namespace PolynomialPatch

variable (A : PolynomialPatch σ s d)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim (fun _ : τ => 1) A.weight) n)

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

include hspecialize in
theorem symbolicShearFullCenter_eval (t : τ → ℝ) (x : Fin d → ℝ) (i : Fin d) :
    aeval (Sum.elim t x) (A.symbolicShearFullCenter f i) =
      (A.form.shearTransformedSlots A.weight_mono (e t)).center x i := by
  rw [symbolicShearFullCenter, map_sub, aeval_X]
  change x i - _ = x i - _
  congr 1
  rw [← patchParameterSpecialization_eval, hspecialize]
  have hsp : patchParameterSpecialization t
      (rename Sum.inr (A.form.topResidualEquiv (X i))) = A.form.topResidualEquiv (X i) := by
    rw [patchParameterSpecialization, MvPolynomial.aeval_rename]
    exact MvPolynomial.aeval_X_left_apply _
  rw [hsp]
  exact (polynomialSubstitutionPoint_aeval (e t).val.toAlgHom x
    (A.form.topResidualEquiv (X i))).symm

include hspecialize in
theorem symbolicShearForm_slots (t : τ → ℝ) :
    (A.symbolicShearForm f hdegree).slots t =
      A.form.shearTransformedSlots A.weight_mono (e t) := by
  classical
  apply TriangularSlots.ext
  intro x i
  let y : Fin d → ℝ := fun j => if j.val < i.val then x j else 0
  have hy : ∀ j : Fin d, j < i → y j = x j := by
    intro j hj
    exact if_pos hj
  have heval :
      (fun v => aeval (Sum.elim t (fun j => x (earlierSlot i j)))
        (symbolicShearPrefixSubstitution i v)) = Sum.elim t y := by
    funext v
    cases v with
    | inl a => simp [symbolicShearPrefixSubstitution]
    | inr j =>
        dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr, y]
        split_ifs with h
        · exact aeval_X _ _
        · exact map_zero _
  change aeval (Sum.elim t (fun j => x (earlierSlot i j)))
    (aeval (symbolicShearPrefixSubstitution i) (A.symbolicShearFullCenter f i)) = _
  rw [MvPolynomial.comp_aeval_apply, heval,
    A.symbolicShearFullCenter_eval f e hspecialize]
  exact (A.form.shearTransformedSlots A.weight_mono (e t)).lower i y x hy

include hspecialize in
theorem symbolicShearPatch_value (t : τ → ℝ) :
    (A.symbolicShearPatch f hdegree).value t =
      ∑' b : Fin d → ℤ, A.kernel.value
        (fun i => aeval (polynomialSubstitutionPoint (e t).val.toAlgHom
          (fun j => (b j : ℝ))) (A.form.topResidualEquiv (X i))) := by
  change ((A.symbolicShearForm f hdegree).slots t).patchValue A.kernel = _
  rw [A.symbolicShearForm_slots f hdegree e hspecialize]
  simp only [TriangularSlots.patchValue, PolynomialSlots.shearTransformedSlots_residual]

include hspecialize in
theorem symbolicShearPatch_value_eq_observable
    (g : (τ → ℝ) → (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (he : ∀ t, e t = (polynomialShearRealAutEquiv A.weight s A.weight_le (g t))⁻¹)
    (t : τ → ℝ) :
    (A.symbolicShearPatch f hdegree).value t =
      A.shearObservable (QuotientGroup.mk (g t)) := by
  rw [A.symbolicShearPatch_value f hdegree e hspecialize]
  unfold shearObservable polynomialShearQuotientSum
  change _ = polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel (g t)
  rw [he t]
  rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial

variable {τ : Type*} {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShearOrbitSymbolicHom_specialization (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : τ => 1))
    (t : τ → ℝ) (P : MvPolynomial (τ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialShearOrbitSymbolicHom hw g P) =
      (polynomialShearRealAutEquiv w s hw
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          (fun _ : τ => 1) t g)).val (patchParameterSpecialization t P) :=
  polynomialShearOrbitSymbolicExp_specialization w s hw g t P

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

theorem ofShearOrbit_value_real
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℝ) :
    (A.ofShearOrbit g).value t = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : τ => 1) t g)) := by
  let _ := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.symbolicShearPatch_value_eq_observable
    (polynomialShearOrbitSymbolicHom A.weight_le g⁻¹)
    (polynomialShearOrbitSymbolicHom_degree A.weight_le g⁻¹)
    (fun t => polynomialShearRealAutEquiv A.weight s A.weight_le
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : τ => 1) t g⁻¹))
    (polynomialShearOrbitSymbolicHom_specialization A.weight_le g⁻¹)
    (fun t => (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
      (fun _ : τ => 1) t g)
    (fun t => by rw [map_inv, map_inv]) t

theorem ofShearOrbit_value_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : τ => 1)) (t : τ → ℤ) :
    (A.ofShearOrbit g).value (fun i => (t i : ℝ)) = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
        (fun _ : τ => 1) t g)) := by
  rw [ofShearOrbit_value_real, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialPatchWeightedChartNiltest
namespace OAI

section

namespace Erdos3.PolynomialPatch

open scoped NNReal TensorProduct

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
    [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem exists_ordinary_niltest_of_weighted_chart
    (M : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    {p : ℝ} (hcomplex : (A.shearNiltest M hA).ComplexityLE p)
    (w : ξ → ℕ) (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w) :
    ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : τ => 1),
      T.observable = (A.shearNiltest M hA).observable ∧
      T.normBound = (A.shearNiltest M hA).normBound ∧
      T.lipBound = (A.shearNiltest M hA).lipBound ∧
      T.UnitIntervalValued ∧ T.ComplexityLE p ∧
      ∀ x : τ → ℤ, T.eval x =
        ((A.ofWeightedChartShearOrbit w β hβ g).value (fun i => (x i : ℝ)) : ℂ) := by
  let orbit := (polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
    w (fun _ : τ => 1) β hβ g
  let T := (A.shearNiltest M hA).withOrbit orbit
  refine ⟨T, rfl, rfl, rfl, A.shearNiltest_unitInterval M hA, hcomplex, ?_⟩
  intro x
  have heval := A.ofShearOrbit_value_integer orbit x
  exact ((A.shearNiltest M hA).withOrbit_eval orbit x).trans
    (congrArg (fun r : ℝ => (r : ℂ)) heval.symm)

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

variable {X : Type*} {J : Fin 0 → Type*}

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (A : PolynomialPatch V s d)

variable [Fintype (PolynomialShearIndex A.weight)]
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
    [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem exists_zeroLayer_physical_niltest
    (M : ℝ≥0) (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M)
    {p : ℝ} (hcomplex : (A.shearNiltest M hA).ComplexityLE p)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : X => 1),
      T.observable = (A.shearNiltest M hA).observable ∧
      T.UnitIntervalValued ∧ T.ComplexityLE p ∧
      ∀ x : X → ℤ, T.eval x = ((A.ofZeroLayerShearOrbit g).value
        (fun i => (x i : ℝ)) : ℂ) := by
  obtain ⟨T, hobs, _, _, hunit, hcomp, hval⟩ := A.exists_ordinary_niltest_of_weighted_chart
    M hA hcomplex (fullTaggedVariableWeight J) zeroLayerSpatialChart
    zeroLayerSpatialChart_support g
  exact ⟨T, hobs, hunit, hcomp, hval⟩

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.ZeroLayerPhysicalNiltestBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

theorem relativePatchComplexity_le_of_rank_lip
    {X : Type*} {s d : ℕ} (A : PolynomialPatch X s d) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hLip : (A.kernel.lip : ℝ) ≤ Real.exp p) :
    relativePatchComplexity A ≤ 2 * p + 1 := by
  have he : 1 ≤ Real.exp p := Real.one_le_exp hp
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ p + 1 := by
    apply (Real.log_le_iff_le_exp (by positivity : 0 < 1 + (A.kernel.lip : ℝ))).mpr
    calc
      1 + (A.kernel.lip : ℝ) ≤ 1 + Real.exp p := by linarith
      _ ≤ 2 * Real.exp p := by linarith
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right he1 (Real.exp_nonneg p)
      _ = Real.exp (p + 1) := by rw [← Real.exp_add]; congr 1; ring
  unfold relativePatchComplexity
  linarith

theorem exists_zeroLayer_physical_niltest_of_mass_bounds (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {V X : Type*} {J : Fin 0 → Type*} {d : ℕ}
      (A : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex A.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p →
      (∀ j, realPolynomialMass (A.form.center j) ≤ p) →
      (A.kernel.lip : ℝ) ≤ Real.exp p →
      ∀ g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
        (fullTaggedVariableWeight (X := X) J),
      relativePatchComplexity (A.ofZeroLayerShearOrbit g) ≤ (p + 2) ^ C ∧
      ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : X => 1),
        T.UnitIntervalValued ∧ T.ComplexityLE ((p + 2) ^ C) ∧
        ∀ x, T.eval x = ((A.ofZeroLayerShearOrbit g).value (fun i => (x i : ℝ)) : ℂ) := by
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_patch_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro V X J d A _ _ _ _ _ p hp hd hform hLip g
  let M : ℝ≥0 := ⟨p, hp⟩
  have hM : ∀ j, realPolynomialMass (A.form.center j) ≤ M := hform
  have hnative := hbudget A M hM p hp hd le_rfl hLip
  obtain ⟨T, _, hunit, hcomplex, heval⟩ :=
    A.exists_zeroLayer_physical_niltest M hM hnative g
  refine ⟨?_, T, hunit, hcomplex, heval⟩
  rw [PolynomialPatch.ofZeroLayerShearOrbit_complexity]
  calc
    relativePatchComplexity A ≤ 2 * p + 1 := relativePatchComplexity_le_of_rank_lip A hp hd hLip
    _ ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    _ ≤ (p + 2) ^ C := pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hC

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AllocatedZeroLayerDegreeScalarConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

theorem exists_allocatedZeroLayer_degree_scalar_conclusion_s2_oai (s n₀ ratio : ℕ)
    (hn₀ : 2 ≤ n₀) (hratio : 2 ≤ ratio)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ observableC nativeC scalarE scalarC scalarF : ℕ,
      2 ≤ observableC ∧ 2 ≤ nativeC ∧
      2 ≤ scalarE ∧ 2 ≤ scalarC ∧ 2 ≤ scalarF ∧
    ∀ {G X : Type} [Fintype G] [Fintype X]
      {I Ecol J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U basis R σ}
      {hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {σsurplus : ℝ}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      (A : AllocatedExternalCandidateSampler B U basis S hb o hR hσ N poly hm
        (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
        (fun _ : X => 1) {0} center)
      (_hK : Fintype.card (LayerSamplerVariables G I n B) = n₀)
      {V : Type} {d : ℕ} (patch : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex patch.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra patch.weight ℚ)]
      {f : (X → ℤ) → ℝ} {lam cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := Ecol) A
        (polynomialShearNilmanifold patch.weight s patch.weight_le)
        (RationalTorus.trivialFiltration s) 0 1
        (fun _ y => (patch.shearObservable y : ℂ))
        (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold)
      (_hkeep : ∀ z : P.productive, (P.chart z).keep = (fun _ => True))
      (pPatch pGlobal outputCost b : ℝ) (netExponent : ℕ),
      0 ≤ pPatch → (d : ℝ) ≤ pPatch →
      (∀ i, realPolynomialMass (patch.form.center i) ≤ pPatch) →
      (patch.kernel.lip : ℝ) ≤ Real.exp pPatch →
      (pPatch + 2) ^ observableC ≤ pGlobal →
      (pPatch + 2) ^ nativeC ≤ b →
      0 ≤ pGlobal → cost ≤ pGlobal →
      Real.exp (-pGlobal) ≤ massThreshold → Real.exp (-pGlobal) ≤ scoreThreshold →
      2 ≤ b → (Fintype.card X : ℝ) ≤ b →
      0 < σsurplus → σsurplus ≤ 1 → σsurplus⁻¹ ≤ Real.exp b →
      lam ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ lam →
      0 ≤ outputCost → outputCost ≤ b →
      (∀ x, f x ∈ Set.Icc (0 : ℝ) 1) →
      A.DegreeGlobalizationAt (E := Ecol) (fun x => ((f x - lam : ℝ) : ℂ))
        s netExponent pGlobal outputCost →
      let p := (b + 2) ^ scalarE
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (p + 1)
      let budget := (target + 2) ^ scalarC
      (∀ i, Real.exp budget ≤ (A.sides i : ℝ)) →
      (∀ i, (A.sides i : ℝ) ≤ (ratio : ℝ) * Real.exp budget) →
      (∀ i, Real.exp ((p + scalarF) ^ scalarF) ≤ (N i : ℝ)) →
      RelativePatchSliceConclusion s N f ((1 - discount) * lam) d
        ((p + scalarF) ^ scalarF) := by
  obtain ⟨observableC, hObservableC, hregularity⟩ :=
    exists_polynomialPatch_external_observable_budget s
  obtain ⟨nativeC, hNativeC, hnative⟩ :=
    exists_zeroLayer_physical_niltest_of_mass_bounds s
  obtain ⟨scalarE, scalarC, scalarF, hE, hC, hF, hpassage⟩ :=
    exists_allocatedZeroLayer_scalar_passage_s2 s n₀ ratio hn₀ hratio hdiscount hdiscountHalf
  refine ⟨observableC, nativeC, scalarE, scalarC, scalarF,
    hObservableC, hNativeC, hE, hC, hF, ?_⟩
  intro G X _ _ I Ecol J _ _ n B _ U basis R σ S hb o hR hσ N poly hm
    σsurplus center _ A hK V d patch _ _ _ _ _ f lam cost massThreshold scoreThreshold
    P hkeep pPatch pGlobal outputCost b netExponent
    hpPatch hd hcenter hLip hObservableBudget hNativeBudget
    hpGlobal hcost hmass hscore hb2 hX hsurplus hsurplus1 hsurplusInv
    hlam hlamLower houtputCost houtputCostB hf rule p target budget hlo hhi hN
  have regularity := PolynomialPatch.ExternalObservableRegularity.mono patch
    (hregularity patch pPatch hpPatch hd hcenter hLip) hObservableBudget
  obtain ⟨out⟩ := P.conclusion_of_shearDegreeGlobalization patch regularity
    hpGlobal hcost hmass hscore hf hlam rule
  obtain ⟨hphysicalComplexity, g, _hunit, hg, heval⟩ :=
    hnative patch pPatch hpPatch hd hcenter hLip out.ambient
  have hpatch : relativePatchComplexity patch ≤ b :=
    hphysicalComplexity.trans hNativeBudget
  have houtputThreshold : Real.exp (-b) ≤ Real.exp (-outputCost) :=
    Real.exp_le_exp.mpr (neg_le_neg houtputCostB)
  exact hpassage A hK patch P hkeep out b hb2 hX hsurplus hsurplus1 hsurplusInv
    hlam hlamLower houtputCost houtputCostB houtputThreshold houtputThreshold hpatch
    g (hg.mono hNativeBudget) heval hlo hhi hN (fun x _ => hf x)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_degree_scalar_conclusion_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_degree_scalar_conclusion_s2_oai
