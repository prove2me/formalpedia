-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:22:47.773112+00:00
-- url     : https://prove2.me/submissions/93a60d9f-7feb-454a-992d-74545f8d5ed0

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B271
import Theorems.Thm_OAI_Erdos3_exists_indexed_comparable_scalar_retained_slice_patch_s2

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

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueMeshExponentialBudget
namespace OAI

section

namespace Erdos3

theorem exists_denseResidueMesh_exponential_budget (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ (b δ ε : ℝ), 0 ≤ b →
      Real.exp (-b) ≤ δ → δ ≤ 1 → Real.exp (-b) ≤ ε → ε ≤ 1 →
      let Q := ⌈2 / δ⌉₊
      let K := denseResidueMeshCap n δ ε C
      ((Q + 1 : ℕ) : ℝ) ≤ Real.exp ((A : ℝ) + 2 * b) ∧
      ((K + 1 : ℕ) : ℝ) ≤ Real.exp ((A : ℝ) + 2 * b) ∧
      16 * ((n : ℝ) + 1) / (ε * δ) ≤ Real.exp ((A : ℝ) + 2 * b) := by
  let D : ℝ := 16 * ((n : ℝ) + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC0 : 0 ≤ C := by linarith
  have hDC : 0 ≤ D * C := mul_nonneg hD hC0
  obtain ⟨A, hA⟩ := exists_nat_ge (D * C + D + 8)
  have hAtwo : 2 ≤ A := by
    have : (2 : ℝ) ≤ A := by linarith
    exact_mod_cast this
  have hAexp : (A : ℝ) ≤ Real.exp A := by linarith [Real.add_one_le_exp (A : ℝ)]
  have hAfour : (4 : ℝ) ≤ Real.exp A := by linarith
  have hADC : D * C + 3 ≤ Real.exp A := by linarith
  have hAD : D ≤ Real.exp A := by linarith
  refine ⟨A, hAtwo, ?_⟩
  intro b δ ε hb hδ _hδ₁ hε _hε₁
  have hδ0 : 0 < δ := (Real.exp_pos _).trans_le hδ
  have hε0 : 0 < ε := (Real.exp_pos _).trans_le hε
  have hδinv : δ⁻¹ ≤ Real.exp b := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-b)) hδ
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have hεinv : ε⁻¹ ≤ Real.exp b := by
    have h := one_div_le_one_div_of_le (Real.exp_pos (-b)) hε
    simpa only [one_div, Real.exp_neg, inv_inv] using h
  have hinv : (ε * δ)⁻¹ ≤ Real.exp (2 * b) := by
    calc
      _ = ε⁻¹ * δ⁻¹ := by simp only [mul_inv_rev, mul_comm]
      _ ≤ Real.exp b * Real.exp b :=
        mul_le_mul hεinv hδinv (inv_nonneg.mpr hδ0.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have heone : 1 ≤ Real.exp (2 * b) := Real.one_le_exp_iff.mpr (by positivity)
  have hδinv2 : δ⁻¹ ≤ Real.exp (2 * b) :=
    hδinv.trans (Real.exp_le_exp.mpr (by linarith))
  have hQceil : (⌈2 / δ⌉₊ : ℝ) ≤ 2 / δ + 1 :=
    (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 / δ)).le
  have hKceil : (⌈D * C / (ε * δ)⌉₊ : ℝ) ≤ D * C / (ε * δ) + 1 :=
    (Nat.ceil_lt_add_one (by positivity : 0 ≤ D * C / (ε * δ))).le
  have hquot : 2 / δ ≤ 2 * Real.exp (2 * b) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hδinv2 (by norm_num)
  have hmesh : D * C / (ε * δ) ≤ D * C * Real.exp (2 * b) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hinv hDC
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((⌈2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ 4 * Real.exp (2 * b) := by
        push_cast
        linarith
      _ ≤ Real.exp A * Real.exp (2 * b) :=
        mul_le_mul_of_nonneg_right hAfour (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  · calc
      ((denseResidueMeshCap n δ ε C + 1 : ℕ) : ℝ) ≤
          (D * C + 3) * Real.exp (2 * b) := by
        unfold denseResidueMeshCap
        change (((⌈D * C / (ε * δ)⌉₊ + 1) + 1 : ℕ) : ℝ) ≤ _
        push_cast
        nlinarith
      _ ≤ Real.exp A * Real.exp (2 * b) :=
        mul_le_mul_of_nonneg_right hADC (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  · calc
      16 * ((n : ℝ) + 1) / (ε * δ) = D * (ε * δ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ D * Real.exp (2 * b) := mul_le_mul_of_nonneg_left hinv hD
      _ ≤ Real.exp A * Real.exp (2 * b) :=
        mul_le_mul_of_nonneg_right hAD (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchMarkedChartRestoration
namespace OAI

section

namespace Erdos3.PolynomialPatch

variable {σ τ ξ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

theorem ofWeightedChartShearOrbit_value (w : ξ → ℕ)
    (β : ξ → MvPolynomial τ ℝ)
    (hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i))
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit w)
    (x : τ → ℝ) :
    (A.ofWeightedChartShearOrbit w β hβ g).value x =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
          w (fun i => MvPolynomial.eval x (β i)) g)) := by
  rw [ofWeightedChartShearOrbit, ofShearOrbit_value_real,
    NilpotentLieFiltration.polynomialOrbitRealChart_realEval]

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RelativeSliceAffineThreeFactorLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators

variable {X : Type*} [Fintype X] [DecidableEq X]
variable {keep : X → Prop} [DecidablePred keep] {N : X → ℕ} {q : ℕ}

theorem fiberSliceLaw_complexMean
    (S : ResidueBoxSlice (fun k : {x // keep x} => N k.val) q)
    (hlen : ∀ k, 0 < S.length k) (fixed : {x // ¬keep x} → ℤ)
    (hfixed : ∀ k, 0 ≤ fixed k ∧ fixed k < (N k.val : ℤ))
    (test : integerBox N → ℂ) :
    (S.fiberSliceLaw hlen fixed hfixed).complexMean test =
      𝔼 u, test (S.fiberPointInBox fixed hfixed u) := by
  let : ∀ k, Nonempty (Fin (S.length k)) := fun k => ⟨⟨0, hlen k⟩⟩
  exact FiniteProbabilityWeights.uniform_finitePushforward_complexMean _ _

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {G X : Type*} {I J : Fin 0 → Type*} {n : Fin 0 → ℕ}
    (B : LayerSamplerAxis I n → Type*)

variable [Fintype G] [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ}

variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateRootBudget_zero_layers :
    allocatedExternalCandidateRootBudget B U b S =
      (Fintype.card G : ℝ) * S.value := by
  unfold allocatedExternalCandidateRootBudget
  rw [zeroLayerVariables_card]

theorem allocatedExternalCandidateWidths_zero_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N := by
  funext z
  rw [allocatedExternalCandidateWidths, allocatedExternalCandidateRootBudget_zero_layers]
  rcases z with ⟨_ | k, x⟩
  · rfl
  · cases k with
    | inl g => rfl
    | inr a => exact Fin.elim0 a.1.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule
open scoped BigOperators Classical

variable {G X : Type*} [Fintype G]
    {I J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin 0 → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedExternalCandidateSides_sum_zero_layers :
    unconditionedResidueSiteBound (allocatedExternalCandidateSides B U b S) =
      (Fintype.card (LayerSamplerVariables G I n B) : ℝ) * S.value := by
  simp only [unconditionedResidueSiteBound, allocatedExternalCandidateSides_zero_layers,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem allocatedExternalCandidateWidths_eq_scalar_zero_layers
    (N : X → ℕ) (τ ξ : ℝ) :
    allocatedExternalCandidateWidths B U b S N τ ξ =
      trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        (unconditionedResidueSiteBound (allocatedExternalCandidateSides B U b S)) τ N := by
  rw [allocatedExternalCandidateSides_sum_zero_layers, zeroLayerVariables_card,
    allocatedExternalCandidateWidths_zero_layers]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseResidueScalarScoreNet
namespace OAI

section

namespace Erdos3

private theorem denseResidueCode_card_exp_bound (n Q K : ℕ) (T : ℝ)
    (hQ : ((Q + 1 : ℕ) : ℝ) ≤ Real.exp T)
    (hK : ((K + 1 : ℕ) : ℝ) ≤ Real.exp T) :
    (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤
      Real.exp (((1 + 3 * n : ℕ) : ℝ) * T) := by
  rw [DenseResidueSliceNetCode.card, Fintype.card_fin]
  push_cast
  calc
    (Q + 1 : ℝ) * ((Q + 1 : ℝ) * (K + 1 : ℝ) ^ 2) ^ n ≤
        Real.exp T * (Real.exp T * (Real.exp T) ^ 2) ^ n := by
      push_cast at hQ hK
      gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      push_cast
      ring

theorem exists_denseResidueScalarNet_power_budget (n : ℕ) {C : ℝ} (hC : 1 ≤ C) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (b δ ε : ℝ), 0 ≤ b →
      Real.exp (-b) ≤ δ → δ ≤ 1 → Real.exp (-b) ≤ ε → ε ≤ 1 →
      let Q := ⌈2 / δ⌉₊
      let K := denseResidueMeshCap n δ ε C
      Real.log (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤ (b + 2) ^ E ∧
      (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤ Real.exp ((b + 2) ^ E) ∧
      ((Q + 1 : ℕ) : ℝ) ≤ Real.exp ((b + 2) ^ E) ∧
      ((K + 1 : ℕ) : ℝ) ≤ Real.exp ((b + 2) ^ E) ∧
      16 * ((n : ℝ) + 1) / (ε * δ) ≤ Real.exp ((b + 2) ^ E) ∧
      (δ / 2)⁻¹ ≤ Real.exp ((b + 2) ^ E) ∧
      2 * C ≤ Real.exp ((b + 2) ^ E) ∧
      4 * C / δ ≤ Real.exp ((b + 2) ^ E) ∧
      (∀ L : ℝ, Real.exp ((b + 2) ^ E) ≤ L → 4 ≤ δ * L) ∧
      ∀ ρ : ℝ, Real.exp (-b) ≤ ρ →
        Real.log (2 * (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) / ρ) ≤
          (b + 2) ^ E := by
  obtain ⟨A, _, hmesh⟩ := exists_denseResidueMesh_exponential_budget n hC
  let P : Polynomial ℕ := Polynomial.C (1 + 3 * n) *
    (Polynomial.C A + 2 * Polynomial.X) + Polynomial.X + 2
  obtain ⟨E, hE, hP⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro b δ ε hb hδ hδ1 hε hε1 Q K
  obtain ⟨hQ, hK, hL⟩ := hmesh b δ ε hb hδ hδ1 hε hε1
  let T := (A : ℝ) + 2 * b
  let U := ((1 + 3 * n : ℕ) : ℝ) * T
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hTU : T ≤ U := by
    dsimp only [U]
    exact le_mul_of_one_le_left hT (by exact_mod_cast (show 1 ≤ 1 + 3 * n by omega))
  have hcost : U + b + 2 ≤ (b + 2) ^ E := by
    simpa [P, U, T] using hP b hb
  have hUcost : U ≤ (b + 2) ^ E := by linarith
  have hTcost := hTU.trans hUcost
  have hcard : (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) ≤ Real.exp U :=
    denseResidueCode_card_exp_bound n Q K T hQ hK
  have hcardpos : 0 < (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (DenseResidueSliceNetCode (Fin n) Q K))
  have hcardFinal := hcard.trans (Real.exp_le_exp.mpr hUcost)
  have hQFinal := hQ.trans (Real.exp_le_exp.mpr hTcost)
  have hKFinal := hK.trans (Real.exp_le_exp.mpr hTcost)
  have hLFinal := hL.trans (Real.exp_le_exp.mpr hTcost)
  have hδpos := (Real.exp_pos (-b)).trans_le hδ
  have hεpos := (Real.exp_pos (-b)).trans_le hε
  have hC0 : 0 ≤ C := by linarith
  have hhalf : (δ / 2)⁻¹ ≤ Real.exp ((b + 2) ^ E) := by
    rw [inv_div]
    exact (Nat.le_ceil (2 / δ)).trans
      ((by exact_mod_cast Nat.le_succ Q : (Q : ℝ) ≤ (Q + 1 : ℕ)).trans hQFinal)
  have hfour : 4 * C / δ ≤ Real.exp ((b + 2) ^ E) := by
    have harg : 16 * ((n : ℝ) + 1) * C / (ε * δ) ≤ ((K + 1 : ℕ) : ℝ) := by
      have hceil := Nat.le_ceil (16 * ((n : ℝ) + 1) * C / (ε * δ))
      dsimp only [K, denseResidueMeshCap]
      push_cast
      linarith
    apply (le_trans ?_ harg).trans hKFinal
    calc
      4 * C / δ ≤ 4 * C / (ε * δ) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hεpos hδpos)
          (mul_le_of_le_one_left hδpos.le hε1)
      _ ≤ 16 * ((n : ℝ) + 1) * C / (ε * δ) := by
        apply div_le_div_of_nonneg_right _ (mul_nonneg hεpos.le hδpos.le)
        nlinarith [Nat.cast_nonneg (α := ℝ) n, mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hC0]
  have htwo : 2 * C ≤ Real.exp ((b + 2) ^ E) := by
    apply (le_trans ?_ hfour)
    apply (le_div_iff₀ hδpos).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδ1 (by positivity : 0 ≤ 2 * C)]
  have hlarge (L : ℝ) (hLL : Real.exp ((b + 2) ^ E) ≤ L) : 4 ≤ δ * L := by
    have hbound := (div_le_iff₀ (mul_pos hεpos hδpos)).mp (hLFinal.trans hLL)
    have hLpos := (Real.exp_pos _).trans_le hLL
    have hεL := mul_le_of_le_one_left (mul_nonneg hδpos.le hLpos.le) hε1
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨(Real.log_le_iff_le_exp hcardpos).mpr hcardFinal, hcardFinal,
    hQFinal, hKFinal, hLFinal, hhalf, htwo, hfour, hlarge, ?_⟩
  intro ρ hρ
  have hρpos := (Real.exp_pos (-b)).trans_le hρ
  have hinv : ρ⁻¹ ≤ Real.exp b := by
    apply (inv_le_iff_one_le_mul₀' hρpos).mpr
    calc
      1 = Real.exp (-b) * Real.exp b := by rw [← Real.exp_add]; simp
      _ ≤ ρ * Real.exp b := mul_le_mul_of_nonneg_right hρ (Real.exp_nonneg _)
  apply (Real.log_le_iff_le_exp (by positivity)).mpr
  calc
    2 * (Fintype.card (DenseResidueSliceNetCode (Fin n) Q K) : ℝ) / ρ ≤
        Real.exp 2 * Real.exp U * Real.exp b := by
      rw [div_eq_mul_inv]
      gcongr
      linarith [Real.add_one_le_exp (2 : ℝ)]
    _ = Real.exp (U + b + 2) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp ((b + 2) ^ E) := Real.exp_le_exp.mpr hcost

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RelativeScalarNetPassageBudget
namespace OAI

section

namespace Erdos3

private theorem exp_neg_add_two_lt_half (b : ℝ) :
    Real.exp (-(b + 2)) < Real.exp (-b) / 2 := by
  have htwo : (3 : ℝ) ≤ Real.exp 2 := by
    linarith [Real.add_one_le_exp (2 : ℝ)]
  have hmul : Real.exp (-(b + 2)) * Real.exp 2 = Real.exp (-b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  nlinarith [Real.exp_pos (-(b + 2))]

theorem exists_relativeScalarNetPassage_power_budget (d r : ℕ) (hr : 1 ≤ r) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ (b density : ℝ), 2 ≤ b →
      Real.exp (-b) ≤ density → density ≤ 1 →
      let accuracy := Real.exp (-b)
      let Q := ⌈2 / density⌉₊
      let K := denseResidueMeshCap d density accuracy (r : ℝ)
      let p := (b + 2) ^ E
      let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
      2 ≤ p ∧ b + 2 ≤ p ∧
      (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) ≤ Real.exp p ∧
      (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) *
        Real.exp (-target) < Real.exp (-b) ∧
      Real.exp (-target) < Real.exp (-b) - accuracy / 2 ∧
      (∀ (Λ τ : ℝ), Real.exp (-b) ≤ Λ → τ ≤ 1 / 2 →
        Real.exp (-p) ≤ (1 - τ) * Λ) ∧
      density⁻¹ ≤ Real.exp p ∧
      ((Q + 1 : ℕ) : ℝ) ≤ Real.exp p ∧
      (density / 2)⁻¹ ≤ Real.exp p ∧
      2 * (r : ℝ) ≤ Real.exp p ∧ 4 * (r : ℝ) / density ≤ Real.exp p ∧
      (∀ scalarbudget : ℝ, p ≤ scalarbudget →
        16 * ((d : ℝ) + 1) / (accuracy * density) ≤ Real.exp scalarbudget) ∧
      ∀ L : ℝ, Real.exp p ≤ L → 4 ≤ density * L := by
  obtain ⟨E, hE, hnet⟩ :=
    exists_denseResidueScalarNet_power_budget d (show (1 : ℝ) ≤ r by exact_mod_cast hr)
  refine ⟨E, hE, ?_⟩
  intro b density hb hdensity hdensity1 accuracy Q K p target
  have hb0 : 0 ≤ b := by linarith
  have haccuracy1 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  obtain ⟨_, hcard, hQ, _, hmesh, hhalf, hratio, hwidth, hlarge, _⟩ :=
    hnet b density accuracy hb0 hdensity hdensity1 le_rfl haccuracy1
  have hbase : 1 ≤ b + 2 := by linarith
  have hbp : b + 2 ≤ p := le_self_pow₀ hbase (by omega : E ≠ 0)
  have hp : 2 ≤ p := by linarith
  have htarget : b + 2 ≤ target := by
    have hrd := Nat.cast_nonneg (α := ℝ) (r * d)
    dsimp only [target]
    nlinarith
  have hsubtract : p - target < -b := by
    have hrd := Nat.cast_nonneg (α := ℝ) (r * d)
    dsimp only [target]
    nlinarith
  have hmass : (Fintype.card (DenseResidueSliceNetCode (Fin d) Q K) : ℝ) *
      Real.exp (-target) < Real.exp (-b) := by
    calc
      _ ≤ Real.exp p * Real.exp (-target) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = Real.exp (p - target) := by rw [← Real.exp_add]; rfl
      _ < Real.exp (-b) := Real.exp_lt_exp.mpr hsubtract
  have hgap : Real.exp (-target) < Real.exp (-b) - accuracy / 2 := by
    have hh := (Real.exp_le_exp.mpr (neg_le_neg htarget)).trans_lt
      (exp_neg_add_two_lt_half b)
    dsimp only [accuracy]
    linarith
  have hlevel (Λ τ : ℝ) (hΛ : Real.exp (-b) ≤ Λ) (hτ : τ ≤ 1 / 2) :
      Real.exp (-p) ≤ (1 - τ) * Λ := by
    have hh := (Real.exp_le_exp.mpr (neg_le_neg hbp)).trans_lt
      (exp_neg_add_two_lt_half b)
    have hΛ0 := (Real.exp_pos (-b)).le.trans hΛ
    have hΛhalf : Real.exp (-b) / 2 ≤ Λ / 2 := by linarith
    have hdiscount : Λ / 2 ≤ (1 - τ) * Λ := by nlinarith
    exact hh.le.trans (hΛhalf.trans hdiscount)
  have hdensity0 := (Real.exp_pos (-b)).trans_le hdensity
  have hinv : density⁻¹ ≤ Real.exp p := by
    apply (inv_le_iff_one_le_mul₀' hdensity0).mpr
    calc
      1 = Real.exp (-b) * Real.exp b := by rw [← Real.exp_add]; simp
      _ ≤ density * Real.exp b := mul_le_mul_of_nonneg_right hdensity (Real.exp_nonneg _)
      _ ≤ density * Real.exp p := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) hdensity0.le
  refine ⟨hp, hbp, hcard, hmass, hgap, hlevel, hinv, hQ, hhalf, hratio, hwidth, ?_, hlarge⟩
  intro scalarbudget hbudget
  exact hmesh.trans (Real.exp_le_exp.mpr hbudget)

end Erdos3

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

theorem fullTaggedPhysicalIntegerPoint_zero_layers
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (x : X → ℤ) :
    fullTaggedPhysicalIntegerPoint J poly c x = zeroLayerPhysicalPoint x := by
  funext v
  rcases v with x | a
  · rfl
  · exact Fin.elim0 a.1

namespace PolynomialPatch

variable {V : Type*} {s d : ℕ} (A : PolynomialPatch V s d)

theorem ofZeroLayerShearOrbit_value_integer
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) (x : X → ℤ) :
    (A.ofZeroLayerShearOrbit g).value (fun i => (x i : ℝ)) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (zeroLayerPhysicalPoint x) g)) := by
  rw [ofZeroLayerShearOrbit, ofWeightedChartShearOrbit_value]
  have hpoint : (fun i => MvPolynomial.eval (fun k => (x k : ℝ)) (zeroLayerSpatialChart i)) =
      fun i => (zeroLayerPhysicalPoint (J := J) x i : ℝ) := by
    funext v
    rcases v with k | a
    · simp only [zeroLayerSpatialChart, Sum.elim_inl, MvPolynomial.eval_X,
        zeroLayerPhysicalPoint]
    · exact Fin.elim0 a.1
  rw [hpoint, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateDenseSliceInput
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {step : ℕ}
    (slice : ResidueBoxSlice (fun i : C.Variables => A.sides i.val) step)
    (hstep : 0 < step) (hlen : ∀ i, 0 < slice.length i)
    (hne : slice.integerPoints.Nonempty)

include hstep in
theorem retainedLaw_eq_fiberSliceLaw :
    C.retainedLaw slice.integerPoints hne slice.integerPoints_subset_integerBox =
      slice.fiberSliceLaw hlen C.fixed C.fixed_in_box := by
  classical
  have hm (f : (LayerSamplerVariables G I n B → ℤ) → ℂ) :
      (C.retainedLaw slice.integerPoints hne slice.integerPoints_subset_integerBox).complexMean
          (fun site => f site.val) =
        (slice.fiberSliceLaw hlen C.fixed C.fixed_in_box).complexMean
          (fun site => f site.val) := by
    rw [C.retainedLaw_complexMean_parameter, slice.expect_integerPoints hstep,
      slice.fiberSliceLaw_complexMean]
    congr 1
    · ext u
      simp
  have hw (site : A.Site) := congrArg Complex.re
    (hm (fun x => if x = site.val then 1 else 0))
  simp only [FiniteProbabilityWeights.complexMean_re, apply_ite, Complex.one_re,
    Complex.zero_re, Subtype.val_inj, FiniteProbabilityWeights.mean,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hw
  cases hp : C.retainedLaw slice.integerPoints hne slice.integerPoints_subset_integerBox
  cases hq : slice.fiberSliceLaw hlen C.fixed C.fixed_in_box
  simp only [hp, hq] at hw
  congr
  exact funext hw

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore)

theorem siteLaw_eq_fiberSliceLaw (z : out.retained) :
    out.siteLaw z = (out.slice z).fiberSliceLaw
      ((out.slice z).length_pos_of_dense (out.dense z))
      (P.chart ⟨z.val, out.subset z.property⟩).fixed
      (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box := by
  classical
  exact (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_eq_fiberSliceLaw
    (out.slice z) (out.step_pos z) ((out.slice z).length_pos_of_dense (out.dense z))
    (out.dense z).nonempty

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchPositivePowerInduction
namespace OAI

section

namespace Erdos3.BooleanCubeKernel
open scoped BigOperators

variable {K X : Type*} [Fintype K]

theorem smoothAffineSample_jointIntegerFrame
    (z : (X → ℤ) × (Option K × X → ℤ)) (u : K → ℤ) :
    smoothAffineSample u (fun i => jointIntegerFrame z i.1 i.2) =
      jointIntegerPhysicalSite u z := by
  funext i
  simp only [smoothAffineSample, jointIntegerFrame, jointIntegerPhysicalSite,
    integerPhysicalSite, Pi.add_apply]
  ring

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateAllKeptSliceLaw
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} {N : I → ℕ} {q : ℕ}

variable [Fintype I] [DecidableEq I]

theorem keepTrueSlice_fiberSliceLaw_mean (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {_i : I // ¬True} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    (f : integerBox N → ℝ) :
    (S.fullSliceLaw hlen).mean f =
      (S.keepTrueSlice.fiberSliceLaw (fun i => hlen i.val) fixed hfixed).mean f := by
  refine (S.fullSliceLaw_mean hlen f).trans
    (Eq.trans ?_ (S.keepTrueSlice.fiberSliceLaw_mean
      (fun i => hlen i.val) fixed hfixed f).symm)
  apply Fintype.expect_equiv S.keepTrueParameterEquiv
  intro u
  rfl

theorem keepTrueSlice_fiberSliceLaw (S : ResidueBoxSlice N q)
    (hlen : ∀ i, 0 < S.length i) (fixed : {_i : I // ¬True} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ)) :
    S.fullSliceLaw hlen =
      S.keepTrueSlice.fiberSliceLaw (fun i => hlen i.val) fixed hfixed := by
  have ext_weight {p p' : FiniteProbabilityWeights (integerBox N)}
      (h : p.weight = p'.weight) : p = p' := by
    cases p
    cases p'
    cases h
    rfl
  apply ext_weight
  funext x
  have hm := S.keepTrueSlice_fiberSliceLaw_mean hlen fixed hfixed
    (fun y => if y = x then 1 else 0)
  simpa [FiniteProbabilityWeights.mean] using hm

end Erdos3.ResidueBoxSlice

end

section

namespace Erdos3.ResidueBoxSlice

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] [DecidableEq I]
    {keep : I → Prop} [dkeep : DecidablePred keep] {N : I → ℕ} {q : ℕ}

theorem exists_fullSliceLaw_of_keep_eq_true
    (S : ResidueBoxSlice (fun i : {i // keep i} => N i.val) q)
    (hkeep : keep = (fun _ => True)) (hlen : ∀ i, 0 < S.length i)
    (fixed : {i // ¬keep i} → ℤ)
    (hfixed : ∀ i, 0 ≤ fixed i ∧ fixed i < (N i.val : ℤ))
    {cost : ℝ}
    (hlength : ∀ i, Real.exp (-cost) * (N i.val : ℝ) ≤ (S.length i : ℝ)) :
    ∃ (T : ResidueBoxSlice N q) (hT : ∀ i, 0 < T.length i),
      (∀ i, Real.exp (-cost) * (N i : ℝ) ≤ (T.length i : ℝ)) ∧
      S.fiberSliceLaw hlen fixed hfixed = T.fullSliceLaw hT := by
  subst keep
  have hd : dkeep = (fun _ => instDecidableTrue) := Subsingleton.elim _ _
  cases hd
  let T : ResidueBoxSlice N q := S.comap (fun i => ⟨i, trivial⟩)
  have hT : T.keepTrueSlice = S := rfl
  refine ⟨T, (fun i => hlen ⟨i, trivial⟩), (fun i => hlength ⟨i, trivial⟩), ?_⟩
  have h := T.keepTrueSlice_fiberSliceLaw (fun i => hlen ⟨i, trivial⟩) fixed hfixed
  simpa only [hT] using h.symm

end Erdos3.ResidueBoxSlice

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace AllocatedExternalCandidateProblem.Conclusion

theorem exists_fullSliceLaw (out : P.Conclusion outputCost outputMass outputScore)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = (fun _ => True))
    (z : out.retained) :
    ∃ (T : ResidueBoxSlice A.sides (out.step z)) (hlen : ∀ i, 0 < T.length i),
      (∀ i, Real.exp (-outputCost) * (A.sides i : ℝ) ≤ (T.length i : ℝ)) ∧
      out.siteLaw z = T.fullSliceLaw hlen := by
  classical
  obtain ⟨T, hlen, hlength, hlaw⟩ :=
    (out.slice z).exists_fullSliceLaw_of_keep_eq_true
      (hkeep ⟨z.val, out.subset z.property⟩)
      ((out.slice z).length_pos_of_dense (out.dense z))
      (P.chart ⟨z.val, out.subset z.property⟩).fixed
      (P.chart ⟨z.val, out.subset z.property⟩).fixed_in_box
      ((out.slice z).length_lower_of_dense (out.step_pos z) (out.dense z))
  exact ⟨T, hlen, hlength, (out.siteLaw_eq_fiberSliceLaw z).trans hlaw⟩

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedZeroLayerPhysicalPatchScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin 0 → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {V : Type*} {s d : ℕ} (patch : PolynomialPatch V s d)
    [Fintype (PolynomialShearIndex patch.weight)]
    {f : (X → ℤ) → ℝ} {lam cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le)
      (RationalTorus.trivialFiltration s) 0 1
      (fun _ y => (patch.shearObservable y : ℂ))
      (fun x => ((f x - lam : ℝ) : ℂ)) cost massThreshold scoreThreshold)

namespace AllocatedExternalCandidateProblem

theorem ambientScore_zeroLayer_patch
    (ambient : (polynomialShearFiltration patch.weight s patch.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (z : P.productive) (points : Finset ((P.chart z).Variables → ℤ))
    (hpoints : points ⊆ (P.chart z).slice.integerPoints) :
    P.ambientScore ambient z points =
      𝔼 u ∈ points, (f ((P.chart z).physical u) - lam) *
        (patch.ofZeroLayerShearOrbit ambient).value
          (fun i => ((P.chart z).physical u i : ℝ)) := by
  rw [P.ambientScore_eq_physical
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
    (fun j => Fin.elim0 j) (fun j => Fin.elim0 j) ambient z points hpoints]
  simp only [ambientPhysicalValue, physicalIntegerPoint,
    fullTaggedPhysicalIntegerPoint_zero_layers,
    Complex.re_expect, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply Finset.expect_congr rfl
  intro u _
  congr 1
  exact (patch.ofZeroLayerShearOrbit_value_integer ambient ((P.chart z).physical u)).symm

theorem Conclusion.zeroLayer_patch_score
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore) (z : out.retained) :
    outputScore ≤ 𝔼 u ∈ (out.slice z).integerPoints,
      (f ((P.chart ⟨z.val, out.subset z.property⟩).physical u) - lam) *
        (patch.ofZeroLayerShearOrbit out.ambient).value
          (fun i => ((P.chart ⟨z.val, out.subset z.property⟩).physical u i : ℝ)) := by
  rw [← P.ambientScore_zeroLayer_patch patch out.ambient
    ⟨z.val, out.subset z.property⟩ (out.slice z).integerPoints (out.inside z)]
  exact out.score z

theorem Conclusion.zeroLayer_siteLaw_score
    {outputCost outputMass outputScore : ℝ}
    (out : P.Conclusion outputCost outputMass outputScore) (z : out.retained) :
    outputScore ≤ (out.siteLaw z).mean (fun site =>
      (f (A.physical z.val site) - lam) *
        (patch.ofZeroLayerShearOrbit out.ambient).value
          (fun i => (A.physical z.val site i : ℝ))) := by
  have he := congrArg Complex.re (out.siteLaw_complexMean_physical z (fun x =>
    (((f x - lam) * (patch.ofZeroLayerShearOrbit out.ambient).value
      (fun i => (x i : ℝ)) : ℝ) : ℂ)))
  simp only [FiniteProbabilityWeights.complexMean_re, Complex.re_expect,
    Complex.ofReal_re] at he
  rw [he]
  exact Conclusion.zeroLayer_patch_score patch P out z

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedZeroLayerScalarPassage
namespace OAI

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card
  trimmedSpatialWidths spatialTrimMargin rectangularWeightIndices unconditionedSpatialTrimFraction
  selectedResidueSmoothWeight RelativePatchSliceConclusion
  FiniteProbabilityWeights.eventProbability

theorem exists_indexed_comparable_scalar_early_retained_slice_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ E C F : ℕ, 2 ≤ E ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d)
      {I : Type u} {V : Type v} [Fintype I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {b σ Λ density : ℝ},
    2 ≤ b → (Fintype.card I : ℝ) ≤ b →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp b →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ Λ →
    Real.exp (-b) ≤ density → density ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE b → relativePatchComplexity P ≤ b →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let p := (b + 2) ^ E
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ parameters : K → ℕ,
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := ∑ j, (parameters j : ℝ)
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ retained : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) → Prop,
      Real.exp (-b) ≤ outer.eventProbability retained →
      (∀ z, retained z → ∀ u : integerBox parameters,
        smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2) ∈
          translatedIntegerBox (0 : I → ℤ) N) →
      (∀ z, retained z → ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        Real.exp (-b) ≤ (S.fullSliceLaw hlen).mean (fun u =>
          (f (smoothAffineSample u.val (fun i => jointIntegerFrame (z.1.val,z.2.val) i.1 i.2)) - Λ) *
            P.value (fun i => (smoothAffineSample u.val
              (fun k => jointIntegerFrame (z.1.val,z.2.val) k.1 k.2) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨E, hE, hnumeric⟩ := exists_relativeScalarNetPassage_power_budget d r (by omega)
  obtain ⟨C, F, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_retained_slice_patch_s2.{u,v,w} s d r hd hr hτ hτhalf
  refine ⟨E, C, F, hE, hC, hF, ?_⟩
  intro K _ decK hK I V _ _ _ _ _ _ _ d₀ rank nilmanifold b σ Λ density hb hn
    hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
    p target budget L parameters hlo hhi N hN f hf trim Wsite width margin
  obtain ⟨hp, hbp, _hcard, hmass, hgap, hlevel, hdensityInv, _hQ,
      _hhalf, _hratio, _hwidth, hmesh, _hlong⟩ := hnumeric b density hb hdensity hdensity1
  have hbp' : b ≤ p := by linarith
  have hn' : (Fintype.card I : ℝ) ≤ p := hn.trans hbp'
  have hσinv' : σ⁻¹ ≤ Real.exp p := hσinv.trans (Real.exp_le_exp.mpr hbp')
  have hdensity0 : 0 < density := (Real.exp_pos (-b)).trans_le hdensity
  have haccuracy1 : Real.exp (-b) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpTarget : p ≤ target := by
    dsimp only [target]
    nlinarith [Nat.cast_nonneg (α := ℝ) (r*d)]
  have htargetBudget : target ≤ budget := by
    have hbase : 1 ≤ target + 2 := by linarith
    have hh := le_self_pow₀ hbase (by omega : C ≠ 0)
    change target ≤ (target + 2)^C
    linarith
  obtain ⟨hwidth, hmargin, hZ, hpassage⟩ :=
    hscalar hK nilmanifold hp hn' hσ hσ1 hσinv' hΛ (hlevel Λ τ hΛlower hτhalf)
      hdensity0 hdensity1 hdensityInv (Real.exp_pos (-b)) haccuracy1
      P g (hg.mono hbp') (hP.trans hbp') hgeval hgap
      (hmesh budget (hpTarget.trans htargetBudget)) parameters hlo hhi N hN f hf
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained hretained hinside hscore
  apply hpassage retained
  · simpa only [DenseResidueSliceNetCode.card, hK, Fintype.card_fin,
      outer, margin, width, Wsite, trim] using hmass.trans_le hretained
  · exact hinside
  · exact hscore

end
end Erdos3

end

section

namespace Erdos3
open BooleanCubeKernel
open scoped BigOperators Classical TensorProduct
universe u v w
noncomputable section

attribute [local irreducible] integerBoxUniformWeights selectedJointReference trimmedIntegerBox
  scalarInitialThreshold Fintype.card trimmedSpatialWidths spatialTrimMargin
  rectangularWeightIndices unconditionedSpatialTrimFraction selectedResidueSmoothWeight
  RelativePatchSliceConclusion FiniteProbabilityWeights.eventProbability

theorem exists_indexed_comparable_scalar_physical_family_patch (s d r : ℕ)
    (hd : 2 ≤ d) (hr : 2 ≤ r) {τ : ℝ} (hτ : 0 < τ) (hτhalf : τ ≤ 1 / 2) :
    ∃ E C F : ℕ, 2 ≤ E ∧ 2 ≤ C ∧ 2 ≤ F ∧
    ∀ {K : Type w} [Fintype K] [DecidableEq K] (_hK : Fintype.card K = d)
      {I : Type u} {V : Type v} [Fintype I] [_decI : DecidableEq I] [LieRing V] [LieAlgebra ℚ V]
      [TopologicalSpace (ℝ ⊗[ℚ] V)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] V)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] V)] [T2Space (ℝ ⊗[ℚ] V)]
      {d₀ rank : ℕ} (nilmanifold : RationalFilteredNilmanifold V s d₀)
      {b σ Λ density : ℝ},
    2 ≤ b → (Fintype.card I : ℝ) ≤ b →
    0 < σ → σ ≤ 1 → σ⁻¹ ≤ Real.exp b →
    Λ ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ Λ →
    Real.exp (-b) ≤ density → density ≤ 1 →
    ∀ (P : PolynomialPatch I s rank) (g : nilmanifold.Niltest (fun _ : I => 1)),
      g.ComplexityLE b → relativePatchComplexity P ≤ b →
      (∀ x, g.eval x = (P.value (fun i => (x i : ℝ)) : ℂ)) →
    let p := (b + 2) ^ E
    let target := 8 * ((r * d : ℕ) + 1 : ℝ) * (p + 1)
    let budget := (target + 2) ^ C
    let L := Real.exp budget
    ∀ (parameters : K → ℕ) [∀ j, NeZero (parameters j)],
      (∀ j, L ≤ (parameters j : ℝ)) → (∀ j, (parameters j : ℝ) ≤ (r : ℝ) * L) →
    ∀ N : I → ℕ, (∀ i, Real.exp ((p + F) ^ F) ≤ (N i : ℝ)) →
    ∀ f : (I → ℤ) → ℝ,
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
    let trim := unconditionedSpatialTrimFraction (Fintype.card I) σ
    let Wsite := unconditionedResidueSiteBound parameters
    let width := trimmedSpatialWidths (K := K) Wsite trim N
    let margin := spatialTrimMargin trim N
    ∃ (hwidth : ∀ z, 0 < width z) (hmargin : ∀ i, 2 * margin i < N i)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : I => 1) {0} width z),
    let outer := selectedJointReference (trimmedIntegerBox N margin)
      (trimmedIntegerBox_nonempty N margin hmargin) (fun _ : I => 1) {0} width hwidth hZ
    ∀ (retained : Finset (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1))
      (localLaw : (trimmedIntegerBox N margin × rectangularWeightIndices 0 width 1) →
        FiniteProbabilityWeights (integerBox parameters)),
      Real.exp (-b) ≤ outer.mass retained →
      (∀ z ∈ retained, ∀ u : integerBox parameters,
        jointIntegerPhysicalSite u.val (z.1.val,z.2.val) ∈
          integerBox N) →
      (∀ z ∈ retained, ∃ q, 0 < q ∧ ∃ S : ResidueBoxSlice parameters q,
        ∃ hlen : ∀ j, 0 < S.length j,
        (∀ j, density * (parameters j : ℝ) ≤ (S.length j : ℝ)) ∧
        localLaw z = S.fullSliceLaw hlen) →
      (∀ z ∈ retained, Real.exp (-b) ≤ (localLaw z).mean (fun u =>
        (f (jointIntegerPhysicalSite u.val (z.1.val,z.2.val)) - Λ) *
          P.value (fun i => (jointIntegerPhysicalSite u.val (z.1.val,z.2.val) i : ℝ)))) →
      RelativePatchSliceConclusion s N f ((1 - τ) * Λ) rank ((p + F) ^ F) := by
  obtain ⟨E, C, F, hE, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_early_retained_slice_patch.{u,v,w} s d r hd hr hτ hτhalf
  refine ⟨E, C, F, hE, hC, hF, ?_⟩
  intro K _ decK hK I V _ decI _ _ _ _ _ _ d₀ rank nilmanifold b σ Λ density hb hn
    hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
    p target budget L parameters _ hlo hhi N hN f hf trim Wsite width margin
  have hdec : decI = Classical.decEq I := Subsingleton.elim _ _
  subst decI
  have hzero : translatedIntegerBox (0 : I → ℤ) N = integerBox N := by
    ext x
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hf' : ∀ x ∈ translatedIntegerBox (0 : I → ℤ) N, f x ∈ Set.Icc (0 : ℝ) 1 := by
    simpa only [hzero] using hf
  obtain ⟨hwidth, hmargin, hZ, hpassage⟩ :=
    hscalar hK nilmanifold hb hn hσ hσ1 hσinv hΛ hΛlower hdensity hdensity1 P g hg hP hgeval
      parameters hlo hhi N hN f hf'
  refine ⟨hwidth, hmargin, hZ, ?_⟩
  intro outer retained localLaw hmass hinside hslice hscore
  apply hpassage (fun z => z ∈ retained)
  · change Real.exp (-b) ≤ outer.eventProbability (fun z => z ∈ retained)
    rw [FiniteProbabilityWeights.eventProbability_mem]
    exact hmass
  · intro z hz u
    rw [hzero]
    simpa only [smoothAffineSample_jointIntegerFrame] using hinside z hz u
  · intro z hz
    obtain ⟨q, hq, S, hlen, hdense, hlaw⟩ := hslice z hz
    refine ⟨q, hq, S, hlen, hdense, ?_⟩
    have h := hscore z hz
    rw [hlaw] at h
    simpa only [smoothAffineSample_jointIntegerFrame] using h

end
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] selectedJointReference trimmedIntegerBox
  trimmedSpatialWidths spatialTrimMargin rectangularWeightIndices
  unconditionedSpatialTrimFraction selectedResidueSmoothWeight
  AllocatedExternalCandidateProblem.Conclusion.allSiteLaw

theorem exists_allocatedZeroLayer_scalar_passage_s2_oai (s n₀ ratio : ℕ)
    (hn₀ : 2 ≤ n₀) (hratio : 2 ≤ ratio)
    {discount : ℝ} (hdiscount : 0 < discount) (hdiscountHalf : discount ≤ 1 / 2) :
    ∃ scalarE scalarC scalarF : ℕ,
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
      {outputCost outputMass outputScore : ℝ}
      (out : P.Conclusion outputCost outputMass outputScore)
      (b : ℝ), 2 ≤ b → (Fintype.card X : ℝ) ≤ b →
      0 < σsurplus → σsurplus ≤ 1 → σsurplus⁻¹ ≤ Real.exp b →
      lam ∈ Set.Icc (0 : ℝ) 1 → Real.exp (-b) ≤ lam →
      0 ≤ outputCost → outputCost ≤ b →
      Real.exp (-b) ≤ outputMass → Real.exp (-b) ≤ outputScore →
      relativePatchComplexity patch ≤ b →
      ∀ g : (polynomialShearNilmanifold patch.weight s patch.weight_le).Niltest
        (fun _ : X => 1), g.ComplexityLE b →
      (∀ x : X → ℤ, g.eval x =
        ((patch.ofZeroLayerShearOrbit out.ambient).value (fun i => (x i : ℝ)) : ℂ)) →
      let p := (b + 2) ^ scalarE
      let target := 8 * ((ratio * n₀ : ℕ) + 1 : ℝ) * (p + 1)
      let budget := (target + 2) ^ scalarC
      (∀ i, Real.exp budget ≤ (A.sides i : ℝ)) →
      (∀ i, (A.sides i : ℝ) ≤ (ratio : ℝ) * Real.exp budget) →
      (∀ i, Real.exp ((p + scalarF) ^ scalarF) ≤ (N i : ℝ)) →
      (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
      RelativePatchSliceConclusion s N f ((1 - discount) * lam) d
        ((p + scalarF) ^ scalarF) := by
  obtain ⟨scalarE, scalarC, scalarF, hE, hC, hF, hscalar⟩ :=
    exists_indexed_comparable_scalar_physical_family_patch s n₀ ratio
      hn₀ hratio hdiscount hdiscountHalf
  refine ⟨scalarE, scalarC, scalarF, hE, hC, hF, ?_⟩
  intro G X _ _ I Ecol J _ _ n B _ U basis R σ S hb o hR hσ N poly hm
    σsurplus center _ A hK V d patch _ _ _ _ _ f lam cost massThreshold scoreThreshold
    P hkeep outputCost outputMass outputScore out b hb2 hX hsurplus hsurplus1 hsurplusInv
    hlam hlamLower houtputCost houtputCostB hmass hscore hpatch g hg heval
    p target budget hlo hhi hN hf
  let : ∀ i, NeZero (A.sides i) := fun i => ⟨(A.sides_pos i).ne'⟩
  have hdensity : Real.exp (-b) ≤ Real.exp (-outputCost) :=
    Real.exp_le_exp.mpr (neg_le_neg houtputCostB)
  have hdensity1 : Real.exp (-outputCost) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr houtputCost)
  have hphysicalPatch : relativePatchComplexity (patch.ofZeroLayerShearOrbit out.ambient) ≤ b :=
    hpatch
  have hresult := hscalar hK (polynomialShearNilmanifold patch.weight s patch.weight_le)
    hb2 hX hsurplus hsurplus1 hsurplusInv hlam hlamLower hdensity hdensity1
    (patch.ofZeroLayerShearOrbit out.ambient) g hg hphysicalPatch heval
    A.sides hlo hhi N hN f hf
  have hwidth := allocatedExternalCandidateWidths_eq_scalar_zero_layers
    B U basis S N (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
  dsimp only at hresult
  rw [← hwidth] at hresult
  obtain ⟨hwidth', hmargin, hZ, hpassage⟩ := hresult
  have hlaw := AllocatedExternalCandidateSampler.law_zero_layers
    B U basis S hb o hR hσ poly hm center N
    (unconditionedSpatialTrimFraction (Fintype.card X) σsurplus) 1
    (fun _ => 1) {0} A
  apply hpassage out.retained out.allSiteLaw
  · rw [← hlaw]
    exact hmass.trans out.mass
  · intro z _ u
    exact A.physical_mem_integerBox le_rfl z u
  · intro z hz
    obtain ⟨slice, hlen, hlength, heq⟩ := out.exists_fullSliceLaw hkeep ⟨z, hz⟩
    exact ⟨out.step ⟨z, hz⟩, out.step_pos ⟨z, hz⟩, slice, hlen, hlength,
      (out.allSiteLaw_of_mem z hz).trans heq⟩
  · intro z hz
    rw [out.allSiteLaw_of_mem z hz]
    exact hscore.trans (out.zeroLayer_siteLaw_score patch P ⟨z, hz⟩)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_allocatedZeroLayer_scalar_passage_s2_oai
