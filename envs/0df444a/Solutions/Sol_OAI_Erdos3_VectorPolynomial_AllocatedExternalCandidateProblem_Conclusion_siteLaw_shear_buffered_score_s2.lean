-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:16:53.802396+00:00
-- url     : https://prove2.me/submissions/0576f836-105b-4607-ba1b-ac68d2df3a9c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B262
import Definitions.Def_OAIE3v2B271

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberTest
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · rw [h x hx]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FinitePushforwardComplexWeights
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {U T : Type*} [Fintype U] [Fintype T]

theorem finitePushforward_pos_iff (p : FiniteProbabilityWeights U)
    (f : U → T) (t : T) :
    0 < (p.finitePushforward f).weight t ↔ ∃ u, f u = t ∧ 0 < p.weight u := by
  classical
  change 0 < (∑ u, if f u = t then p.weight u else 0) ↔ _
  rw [Finset.sum_pos_iff_of_nonneg (fun u _ =>
    ite_nonneg (p.nonneg u) (le_refl 0))]
  constructor
  · rintro ⟨u, _, hu⟩
    by_cases he : f u = t
    · exact ⟨u, he, by simpa only [he, ite_true] using hu⟩
    · simp only [he, ite_false, lt_self_iff_false] at hu
  · rintro ⟨u, he, hu⟩
    exact ⟨u, Finset.mem_univ _, by simpa only [he, ite_true] using hu⟩

end Erdos3.FiniteProbabilityWeights

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

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial Module VectorPolynomial
open scoped TensorProduct

section Coordinates

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)

theorem weightedPolynomialShearOrbitParameterCoordinates_eval
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
    (t : σ → ℝ) (a : PolynomialShearIndex w) :
    MvPolynomial.eval t (weightedPolynomialShearOrbitParameterCoordinates s hw weight g a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          weight t g).coord a := by
  exact (VectorPolynomial.coordinate_eval₂
    (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a) t g.log).symm

end Coordinates

variable {σ : Type*} {d : ℕ}

variable (w : Fin d → ℕ) [Fintype (PolynomialShearIndex w)]
variable (s : ℕ) (hw : ∀ i, w i ≤ s) (weight : σ → ℕ)
variable (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit weight)
variable (t : σ → ℝ)

local notation "orbitD" => polynomialShearRealificationEquiv w
  (NilpotentLieBCHGroup.coord
    (NilpotentLieFiltration.polynomialOrbitRealEval
      (NilpotentLieFiltration.realification (polynomialShearFiltration w s hw))
      weight t g))
local notation "symbolicD" => polynomialSymbolicShearDerivation w
  (weightedPolynomialShearOrbitParameterCoordinates s hw weight g)

theorem weightedPolynomialShearOrbitSymbolicDerivation_X_slot_specialization (i : Fin d) :
    patchParameterSpecialization t ((symbolicD).val (X (Sum.inr i))) = (orbitD).val (X i) := by
  rw [polynomialSymbolicShearDerivation_X_slot, polynomialSymbolicShearSlot_specialization,
    polynomialShearBasis_coordinate_eval]
  apply Finset.sum_congr rfl
  intro a ha
  rw [weightedPolynomialShearOrbitParameterCoordinates_eval, polynomialShearRealificationEquiv_repr]
  split_ifs <;> rfl

theorem weightedPolynomialShearOrbitSymbolicDerivation_specialization
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
    exact weightedPolynomialShearOrbitSymbolicDerivation_X_slot_specialization w s hw weight g t i

theorem weightedPolynomialShearOrbitSymbolicExp_specialization
    (P : MvPolynomial (σ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (polynomialShearExp symbolicD P) =
      polynomialShearExp orbitD (patchParameterSpecialization t P) :=
  polynomialShearExp_intertwine (patchParameterSpecialization t) symbolicD orbitD
    (weightedPolynomialShearOrbitSymbolicDerivation_specialization w s hw weight g t) P

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

end PolynomialPatch
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily
namespace OAI

universe u

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

theorem low_residual_on_slice
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (k : ℕ) (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints)
    (i : Fin (Fintype.card (LowTaggedIndex J k))) :
    |MvPolynomial.eval (fun x => (C.physical u x : ℝ)) (lowTaggedPolynomial J k poly i) -
      (C.centerLift (lowTaggedIndex J k i).1).val (lowTaggedIndex J k i).2 -
      (integerSampledLowTags J k C.integerChart u i : ℝ)| ≤ 1 / 8 :=
  C.low_residual hσ1 H hH hchart hsmall hp k u
    (C.slice.integerPoints_subset_integerBox hu) i

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedExternalCandidateRetainedSliceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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
    (points : Finset (C.Variables → ℤ))
    (hpoints : points.Nonempty)
    (hbox : points ⊆ integerBox (fun i : C.Variables => A.sides i.val))

theorem retainedLaw_support (site : A.Site)
    (hsite : 0 < (C.retainedLaw points hpoints hbox).weight site) :
    ∃ u : C.Variables → ℤ, ∃ hu : u ∈ points,
      site = C.site u (hbox hu) ∧ A.physical C.path site = C.physical u := by
  obtain ⟨u, hu, _⟩ :=
    (FiniteProbabilityWeights.finitePushforward_pos_iff
      (FiniteProbabilityWeights.uniformFinset points hpoints)
      (C.retainedSite points hbox) site).mp hsite
  refine ⟨u.val, u.property, hu.symm, ?_⟩
  rw [← hu]
  rfl

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

theorem siteLaw_support (z : out.retained) (site : A.Site)
    (hsite : 0 < (out.siteLaw z).weight site) :
    ∃ u : (P.chart ⟨z.val, out.subset z.property⟩).Variables → ℤ,
      u ∈ (out.slice z).integerPoints ∧
      u ∈ (P.chart ⟨z.val, out.subset z.property⟩).slice.integerPoints ∧
      site.val = (P.chart ⟨z.val, out.subset z.property⟩).parameter u ∧
      A.physical z.val site = (P.chart ⟨z.val, out.subset z.property⟩).physical u := by
  obtain ⟨u, hu, hs, hp⟩ :=
    (P.chart ⟨z.val, out.subset z.property⟩).retainedLaw_support
      (out.slice z).integerPoints (out.dense z).nonempty
      (out.slice z).integerPoints_subset_integerBox site hsite
  refine ⟨u, hu, out.inside z hu, ?_, ?_⟩
  · exact congrArg Subtype.val hs
  · rw [P.chart_path] at hp
    exact hp

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateBufferedCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m d : ℕ} {X : Type*} {J : Fin m → Type*}

theorem fullTaggedPhysicalIntegerPoint_eq_nearest
    (e : Fin d ≃ Σ j, J j) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : ∀ j, J j → ℝ) (x : X → ℤ) :
    fullTaggedPhysicalIntegerPoint J poly c x =
      Sum.elim x (fun a => nearestIntegerLift (fullTaggedBufferedCoordinates e poly c x)
        (e.symm a)) := by
  funext v
  rcases v with a | a
  · rfl
  · simp only [fullTaggedPhysicalIntegerPoint, Sum.elim_inr, nearestIntegerLift,
      fullTaggedBufferedCoordinates]
    rw [e.apply_symm_apply]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem fullTaggedBufferedCoordinates_close_on_slice
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) (i : Fin tagCount) :
    |fullTaggedBufferedCoordinates e poly (fun j => (C.centerLift j).val) (C.physical u) i -
      (nearestIntegerLift
        (fullTaggedBufferedCoordinates e poly (fun j => (C.centerLift j).val)
          (C.physical u)) i : ℝ)| ≤ 1 / 8 := by
  have hj : (e i).1.val + 1 ≤ m + 1 := by omega
  have hr := C.low_residual_on_slice hσ1 H hH hchart hsmall hp (m + 1) u hu
    (lowTaggedSlot J (m + 1) (e i).1 hj (e i).2)
  rw [lowTaggedPolynomial_eval] at hr
  simp only [integerSampledLowTags] at hr
  rw [lowTaggedIndex_slot] at hr
  change |eval (fun x => (C.physical u x : ℝ)) (poly (e i).1) (e i).2 -
    (C.centerLift (e i).1).val (e i).2 -
    (C.chartValues u (Sum.inr (e i)) : ℝ)| ≤ 1 / 8 at hr
  rw [C.chartValues_tag_eq_round hσ1 H hH hchart hsmall hp u
    (C.slice.integerPoints_subset_integerBox hu) (e i).1 (e i).2] at hr
  exact hr

end AllocatedExternalLocalChart

namespace AllocatedExternalCandidateProblem

variable {A} {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {outputCost outputMass outputScore : ℝ}

namespace Conclusion

variable (out : P.Conclusion outputCost outputMass outputScore)

variable (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include hσ1 H hH hchart hsmall hp

theorem siteLaw_fullTaggedBufferedCoordinates_close
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j)
    (z : out.retained) (site : A.Site) (hsite : (out.siteLaw z).weight site ≠ 0)
    (i : Fin tagCount) :
    |fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
        (A.physical z.val site) i -
      (nearestIntegerLift
        (fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val)
          (A.physical z.val site)) i : ℝ)| ≤ 1 / 8 := by
  have hpos : 0 < (out.siteLaw z).weight site :=
    lt_of_le_of_ne ((out.siteLaw z).nonneg site) (Ne.symm hsite)
  obtain ⟨u, _, hu, _, hphysical⟩ := out.siteLaw_support z site hpos
  rw [hphysical]
  have h := (P.chart ⟨z.val, out.subset z.property⟩).fullTaggedBufferedCoordinates_close_on_slice
    hσ1 H hH hchart hsmall hp e u hu i
  rw [P.chart_centerLift] at h
  exact h

end Conclusion
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
variable {σ τ : Type*} {s d : ℕ}

namespace PolynomialPatch
variable (A : PolynomialPatch σ s d) (p : τ → ℕ)
  (f : MvPolynomial (τ ⊕ Fin d) ℝ →ₐ[ℝ] MvPolynomial (τ ⊕ Fin d) ℝ)

variable
  (hdegree : ∀ {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ},
    P ∈ weightedSupportLE (Sum.elim p A.weight) n →
    f P ∈ weightedSupportLE (Sum.elim p A.weight) n)

variable (e : (τ → ℝ) → WeightedLoweringAut A.weight ℝ)
  (hspecialize : ∀ t P, patchParameterSpecialization t (f P) =
    (e t).val (patchParameterSpecialization t P))

include hspecialize in
theorem weightedSymbolicShearForm_slots (t : τ → ℝ) :
    (A.weightedSymbolicShearForm p f hdegree).slots t =
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
theorem weightedSymbolicShearPatch_value (t : τ → ℝ) :
    (A.weightedSymbolicShearPatch p f hdegree).value t =
      ∑' b : Fin d → ℤ, A.kernel.value
        (fun i => aeval (polynomialSubstitutionPoint (e t).val.toAlgHom
          (fun j => (b j : ℝ))) (A.form.topResidualEquiv (X i))) := by
  change ((A.weightedSymbolicShearForm p f hdegree).slots t).patchValue A.kernel = _
  rw [A.weightedSymbolicShearForm_slots p f hdegree e hspecialize]
  simp only [TriangularSlots.patchValue, PolynomialSlots.shearTransformedSlots_residual]

include hspecialize in
theorem weightedSymbolicShearPatch_value_eq_observable
    (g : (τ → ℝ) → (polynomialShearFiltration A.weight s A.weight_le).realification.Group)
    (he : ∀ t, e t = (polynomialShearRealAutEquiv A.weight s A.weight_le (g t))⁻¹)
    (t : τ → ℝ) :
    (A.weightedSymbolicShearPatch p f hdegree).value t =
      A.shearObservable (QuotientGroup.mk (g t)) := by
  rw [A.weightedSymbolicShearPatch_value p f hdegree e hspecialize]
  unfold shearObservable polynomialShearQuotientSum
  change _ = polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel (g t)
  rw [he t]
  rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {τ : Type*} (p : τ → ℕ) {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

theorem weightedPolynomialShearOrbitSymbolicHom_specialization (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p)
    (t : τ → ℝ) (P : MvPolynomial (τ ⊕ Fin d) ℝ) :
    patchParameterSpecialization t (weightedPolynomialShearOrbitSymbolicHom p hw g P) =
      (polynomialShearRealAutEquiv w s hw
        ((polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
          p t g)).val (patchParameterSpecialization t P) :=
  weightedPolynomialShearOrbitSymbolicExp_specialization w s hw p g t P

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

theorem ofWeightedShearOrbit_value_real
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) (t : τ → ℝ) :
    (A.ofWeightedShearOrbit p g).value t = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        p t g)) := by
  let _ := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.weightedSymbolicShearPatch_value_eq_observable p
    (weightedPolynomialShearOrbitSymbolicHom p A.weight_le g⁻¹)
    (weightedPolynomialShearOrbitSymbolicHom_degree p A.weight_le g⁻¹)
    (fun t => polynomialShearRealAutEquiv A.weight s A.weight_le
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        p t g⁻¹))
    (weightedPolynomialShearOrbitSymbolicHom_specialization p A.weight_le g⁻¹)
    (fun t => (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
      p t g)
    (fun t => by rw [map_inv, map_inv]) t

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open VectorPolynomial

variable {X : Type*} {m n : ℕ} {J : Fin m → Type*}

namespace PolynomialPatch
variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

theorem ofTaggedWeightedShearOrbit_value_real (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) (x : X → ℝ) (b : Fin n → ℝ) :
    (A.ofTaggedWeightedShearOrbit e g).value (Sum.elim x b) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
          (fullTaggedVariableWeight J) (Sum.elim x (fun a => b (e.symm a))) g)) := by
  rw [ofTaggedWeightedShearOrbit, ofWeightedShearOrbit_value_real,
    NilpotentLieFiltration.polynomialOrbitRealChart_realEval]
  have h : (fun i => MvPolynomial.eval (Sum.elim x b)
      (taggedShearOrbitReindexChart e i)) = Sum.elim x (fun a => b (e.symm a)) := by
    funext v
    cases v <;> simp [taggedShearOrbitReindexChart]
  rw [h]

theorem ofTaggedWeightedShearOrbit_value_integer (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) (x : X → ℤ) (b : Fin n → ℤ) :
    (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ))) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (Sum.elim x (fun a => b (e.symm a))) g)) := by
  rw [ofTaggedWeightedShearOrbit_value_real]
  have h : Sum.elim (fun i => (x i : ℝ)) (fun a => (b (e.symm a) : ℝ)) =
      fun v => ((Sum.elim x (fun a => b (e.symm a))) v : ℝ) := by
    funext v
    cases v <;> rfl
  rw [h, NilpotentLieFiltration.polynomialOrbitRealEval_integer]

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3.PolynomialPatch

open VectorPolynomial

variable {σ X : Type*} {s d m n : ℕ} {J : Fin m → Type*}
    (A : PolynomialPatch σ s d) (e : Fin n ≃ Σ j, J j)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))

theorem ofTaggedWeightedShearOrbit_value_nearest (x : X → ℤ) :
    (A.ofTaggedWeightedShearOrbit e g).value
      (Sum.elim (fun i => (x i : ℝ))
        (fun i => (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c x) i : ℝ))) =
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c x) g)) := by
  rw [A.ofTaggedWeightedShearOrbit_value_integer,
    fullTaggedPhysicalIntegerPoint_eq_nearest e poly c x]

theorem ofTaggedWeightedShearOrbit_bufferedScalarScore
    (χ : PatchKernel n) (f : (X → ℤ) → ℝ) (lam : ℝ) (x : X → ℤ) :
    bufferedScalarScore χ (fullTaggedBufferedCoordinates e poly c)
      (fun x b => (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ)))) f lam x =
      (f x - lam) * χ.value (fun i => fullTaggedBufferedCoordinates e poly c x i -
        (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c x) i : ℝ)) *
      A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c x) g)) := by
  unfold bufferedScalarScore
  dsimp only
  rw [A.ofTaggedWeightedShearOrbit_value_nearest e poly c g]

theorem ofTaggedWeightedShearOrbit_bufferedMean_eq_score
    {Ω : Type*} [Fintype Ω] (law : FiniteProbabilityWeights Ω) (physical : Ω → X → ℤ)
    (χ : PatchKernel n) (f : (X → ℤ) → ℝ) (lam : ℝ) :
    law.mean (fun u => bufferedScalarScore χ (fullTaggedBufferedCoordinates e poly c)
      (fun x b => (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ)))) f lam (physical u)) =
    (law.complexMean (fun u => ((f (physical u) - lam : ℝ) : ℂ) *
      ((χ.value (fun i => fullTaggedBufferedCoordinates e poly c (physical u) i -
        (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c (physical u)) i : ℝ)) : ℝ) : ℂ) *
      ((A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c (physical u)) g)) : ℝ) : ℂ))).re := by
  simp only [A.ofTaggedWeightedShearOrbit_bufferedScalarScore e poly c g,
    ← Complex.ofReal_mul, law.complexMean_ofReal, Complex.ofReal_re]

theorem ofTaggedWeightedShearOrbit_plateauMean_eq_score
    {Ω : Type*} [Fintype Ω] (law : FiniteProbabilityWeights Ω) (physical : Ω → X → ℤ)
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    (hsmall : ∀ u, law.weight u ≠ 0 → ∀ i,
      |fullTaggedBufferedCoordinates e poly c (physical u) i -
        (nearestIntegerLift (fullTaggedBufferedCoordinates e poly c (physical u)) i : ℝ)| ≤ 1 / 8) :
    law.mean (fun u => bufferedScalarScore (majorPhasePlateauKernel n)
      (fullTaggedBufferedCoordinates e poly c)
      (fun x b => (A.ofTaggedWeightedShearOrbit e g).value
        (Sum.elim (fun i => (x i : ℝ)) (fun i => (b i : ℝ)))) f lam (physical u)) =
    (law.complexMean (fun u => ((f (physical u) - lam : ℝ) : ℂ) *
      ((A.shearObservable (QuotientGroup.mk
        ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
          (fullTaggedVariableWeight J) (fullTaggedPhysicalIntegerPoint J poly c (physical u)) g)) : ℝ) : ℂ))).re := by
  rw [A.ofTaggedWeightedShearOrbit_bufferedMean_eq_score e poly c g]
  apply congrArg Complex.re
  apply law.complexMean_congr_support
  intro u hu
  rw [majorPhasePlateauKernel_one _ (hsmall u hu)]
  simp only [Complex.ofReal_one, mul_one]

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateShearBufferedScore
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

namespace AllocatedExternalCandidateProblem.Conclusion

variable {A} {Y M : Type*} [LieRing M] [LieAlgebra ℚ M] {s d t : ℕ}
    (patch : PolynomialPatch Y s d) [Fintype (PolynomialShearIndex patch.weight)]
    {Fmark : NilpotentLieFiltration M t}
    {φ : PolynomialShearLieAlgebra patch.weight ℚ →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (f : (X → ℤ) → ℝ) (lam : ℝ)
    {cost massThreshold scoreThreshold outputCost outputMass outputScore : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A
      (polynomialShearNilmanifold patch.weight s patch.weight_le) Fmark φ marked
      (fun _ z => (patch.shearObservable z : ℂ)) (fun x => ((f x - lam : ℝ) : ℂ))
      cost massThreshold scoreThreshold}
    (out : P.Conclusion outputCost outputMass outputScore)

theorem siteLaw_shear_buffered_score_s2_oai
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    {tagCount : ℕ} (e : Fin tagCount ≃ Σ j, J j) (z : out.retained) :
    outputScore ≤ (out.siteLaw z).mean (fun site =>
      bufferedScalarScore (majorPhasePlateauKernel tagCount)
        (fullTaggedBufferedCoordinates e poly (fun j => (P.centerLift j).val))
        (fun x lifts => (patch.ofTaggedWeightedShearOrbit e out.ambient).value
          (Sum.elim (fun i => (x i : ℝ)) (fun i => (lifts i : ℝ))))
        f lam (A.physical z.val site)) := by
  rw [patch.ofTaggedWeightedShearOrbit_plateauMean_eq_score e poly
    (fun j => (P.centerLift j).val) out.ambient (out.siteLaw z)
    (A.physical z.val) f lam
    (out.siteLaw_fullTaggedBufferedCoordinates_close hσ1 H hH hchart hsmall hp e z)]
  exact out.siteLaw_score hσ1 H hH hchart hsmall hp z

end AllocatedExternalCandidateProblem.Conclusion
end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} : type_of% @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8} := @OAI.Erdos3.VectorPolynomial.AllocatedExternalCandidateProblem.Conclusion.siteLaw_shear_buffered_score_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6, u_7, u_8}
