-- Prove2me | solution 1 for OAI.Erdos3.exists_retained_epoch_from_records_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:16:05.784506+00:00
-- url     : https://prove2.me/submissions/b28da14b-7902-42c6-a09a-b3378e0a99c4

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B211
import Definitions.Def_OAIE3v2B212
import Definitions.Def_OAIE3v2B213
import Theorems.Thm_OAI_Erdos3_RationalFilteredNilmanifold_exists_fixed_child_affine_residue_descent_s2
import Theorems.Thm_OAI_Erdos3_exists_retained_lattice_normalization_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealCoordinatePolynomialSymbol
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

theorem eval₂_substitute (f : σ → MvPolynomial τ R) (x : τ → S)
    (p : VectorPolynomial σ R V) :
    eval₂ x (substitute f p) = eval₂ (fun i => MvPolynomial.aeval x (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
      simp only [substitute_tmul, eval₂_tmul]
      rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FullAffineCoefficientBound
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem realAxisAffinePullback_eval {σ : Type*} (h r x : σ → ℝ) (P : MvPolynomial σ ℝ) :
    eval x (realAxisAffinePullback h r P) = eval (fun i => h i + r i * x i) P := by
  have heq : (eval x).comp (realAxisAffinePullback h r) = eval (fun i => h i + r i * x i) := by
    ext <;> simp [realAxisAffinePullback, realAxisAffinePolynomial]
  exact RingHom.congr_fun heq P

theorem realAxisAffinePolynomial_mass_le {σ : Type*} (h r : σ → ℝ) (i : σ) :
    realPolynomialMass (realAxisAffinePolynomial h r i) ≤ |h i| + |r i| := by
  apply (realPolynomialMass_add_le _ _).trans
  apply add_le_add
  · exact (realPolynomialMass_C _).le
  · simpa only [realPolynomialMass_X, mul_one] using realPolynomialMass_C_mul_le (r i) (X i)

theorem scaleMvPolynomialAxes_affine {σ : Type*} (T A h r : σ → ℝ)
    (hT : ∀ i, T i ≠ 0) (P : MvPolynomial σ ℝ) :
    scaleMvPolynomialAxes A (realAxisAffinePullback h r P) =
      realAxisAffinePullback (fun i => h i / T i) (fun i => r i * A i / T i)
        (scaleMvPolynomialAxes T P) := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval, realAxisAffinePullback_eval,
    realAxisAffinePullback_eval, scaleMvPolynomialAxes_eval]
  apply congrArg (fun y : σ → ℝ => eval y P)
  funext i
  field_simp [hT i]

theorem realAxisAffinePullback_coeff_bound {σ : Type*}
    (T A h r : σ → ℝ) (hT : ∀ i, 0 < T i) (hA : ∀ i, 0 < A i)
    (P : MvPolynomial σ ℝ) {M B : ℝ} {s : ℕ} (hB : 1 ≤ B)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hphysical : ∀ i, |h i| + |r i| * A i ≤ B * T i)
    (hdegree : P.totalDegree ≤ s) (α : σ →₀ ℕ) :
    |(realAxisAffinePullback h r P).coeff α| ≤
      (P.support.card * M * B ^ s) / monomialScale A α := by
  have hf (i : σ) : realPolynomialMass
      (realAxisAffinePolynomial (fun j => h j / T j) (fun j => r j * A j / T j) i) ≤ B := by
    apply (realAxisAffinePolynomial_mass_le _ _ i).trans
    calc
      _ = (|h i| + |r i| * A i) / T i := by
        rw [abs_div, abs_div, abs_mul, abs_of_pos (hT i), abs_of_pos (hA i)]
        ring
      _ ≤ B := (div_le_iff₀ (hT i)).mpr (hphysical i)
  have hmass : realPolynomialMass (scaleMvPolynomialAxes A (realAxisAffinePullback h r P)) ≤
      P.support.card * M * B ^ s := by
    rw [scaleMvPolynomialAxes_affine T A h r (fun i => (hT i).ne')]
    apply (realPolynomialMass_substitution_le (scaleMvPolynomialAxes T P) _ hB hf
      ((scaleMvPolynomialAxes_totalDegree_le T P).trans hdegree)).trans
    exact mul_le_mul_of_nonneg_right (scaleMvPolynomialAxes_mass_le T hT P hcoeff)
      (pow_nonneg (zero_le_one.trans hB) _)
  have hc := (realPolynomialMass_coeff_le (scaleMvPolynomialAxes A (realAxisAffinePullback h r P)) α).trans hmass
  rw [scaleMvPolynomialAxes_coeff, abs_mul, abs_of_pos (monomialScale_pos A hA α)] at hc
  exact (le_div_iff₀ (monomialScale_pos A hA α)).mpr hc

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_log (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).orbit.log =
      weightedDilation (fun _ => 1) r (VectorPolynomial.translate shift T.orbit.log) :=
  substitute_scalarAffinePolynomial r shift T.orbit.log

theorem scalarAffinePullback_symbol (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).symbol b ω hF =
      D.filtration.realPolynomialSymbolDilationHom (fun _ => 1) r (T.symbol b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (T.scalarAffinePullback r shift).orbit.log =
    D.filtration.realPolynomialSymbolDilation (fun _ => 1) r
      (D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1) T.orbit.log)
  rw [T.scalarAffinePullback_log]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact T.orbit.adapted

theorem scalarAffinePullback_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {S H : σ → ℝ} {p q : ℝ} {M : ℕ} {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S (T.symbol b ω hF) p M U)
    (a : ℤ) (m : ℕ) (ha : a ≠ 0) (hm : 0 < m) (shift : σ → ℚ)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / m : ℚ) : ℝ)| * H i) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H
      ((T.scalarAffinePullback ((a : ℚ) / m) shift).symbol b ω hF)
      (p + (s : ℝ) * q) (M * m ^ s) U := by
  rw [T.scalarAffinePullback_symbol]
  exact NilpotentLieFiltration.SymbolFactorizationIn.dilate_ratio D.filtration b ω hF
    h a m ha hm hS hH hq hphysical

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_eq_of_orbit_eq (T U : D.Niltest w) (h : T.orbit = U.orbit)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    T.symbol b ω hF = U.symbol b ω hF := by
  unfold symbol
  apply congrArg (D.filtration.realPolynomialSymbolHom b ω hF w)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : D.filtration.realification.PolynomialOrbit w => o.log) h

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι V : Type*}

theorem coordinate_scalarAffine
    [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (f : V →ₗ[ℝ] ℝ) (r : ℚ) (h : σ → ℚ) (P : VectorPolynomial σ ℚ V) :
    coordinate f.toAddMonoidHom (weightedDilation (fun _ : σ => 1) r (translate h P)) =
      realAxisAffinePullback (fun i => (h i : ℝ)) (fun _ => (r : ℝ)) (coordinate f.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro x
  have harg : (fun i => MvPolynomial.aeval x (scalarAffinePolynomial r h i)) =
      (fun i => (h i : ℝ) + (r : ℝ) * x i) := by
    funext i
    simp [scalarAffinePolynomial]
  rw [← coordinate_eval₂ f x, ← substitute_scalarAffinePolynomial, eval₂_substitute,
    harg, coordinate_eval₂, realAxisAffinePullback_eval]

theorem CoefficientBound.scalarAffine [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T A : σ → ℝ) (hT : ∀ i, 0 < T i) (hA : ∀ i, 0 < A i)
    {M B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b T M P) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P) (r : ℚ) (h : σ → ℚ)
    (hphysical : ∀ i, |(h i : ℝ)| + |(r : ℝ)| * A i ≤ B * T i) :
    CoefficientBound b A (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * B ^ s)
      (weightedDilation (fun _ : σ => 1) r (translate h P)) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s := (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff : ∀ β, |Q.coeff β| ≤ M / monomialScale T β := by
    intro β
    simp only [Q, coeff_coordinate]
    change |b.repr (coefficients P β) i| ≤ M / monomialScale T β
    exact hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le Q hQdeg
  have hbound := realAxisAffinePullback_coeff_bound T A (fun j => (h j : ℝ)) (fun _ => (r : ℝ))
    hT hA Q hB hQcoeff hphysical hQdeg α
  have heq := congrArg (fun q : MvPolynomial σ ℝ => q.coeff α) (coordinate_scalarAffine (b.coord i) r h P)
  rw [coeff_coordinate] at heq
  change (b.coord i) (coefficients (weightedDilation (fun _ : σ => 1) r (translate h P)) α) = _ at heq
  change |(b.coord i) (coefficients (weightedDilation (fun _ : σ => 1) r (translate h P)) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos A hA α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hM)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

theorem residueTransitionNumerator_pos {M₀ M₁ : ℕ} (hM₁ : 0 < M₁) (hdiv : M₀ ∣ M₁) :
    0 < M₁ / M₀ := by
  apply Nat.pos_of_ne_zero
  intro hz
  have heq := Nat.mul_div_cancel' hdiv
  rw [hz, mul_zero] at heq
  exact hM₁.ne' heq.symm

theorem residueTransition_scale {M₀ M₁ d : ℕ} (hdiv : M₀ ∣ M₁) (hd : 0 < d) :
    ((M₀ : ℚ) * d) * (((M₁ / M₀ : ℕ) : ℚ) / d) = M₁ := by
  have heq : (M₀ : ℚ) * (M₁ / M₀ : ℕ) = M₁ := by
    exact_mod_cast Nat.mul_div_cancel' hdiv
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ = (M₀ : ℚ) * (M₁ / M₀ : ℕ) := by
      field_simp [hdq]
    _ = M₁ := heq

theorem residueTransition_shift {M₀ d : ℕ} (hM₀ : 0 < M₀) (hd : 0 < d) (a₀ a₁ : ℚ) :
    ((M₀ : ℚ) * d) * ((a₁ - a₀) / ((M₀ : ℚ) * d)) + a₀ = a₁ := by
  have hstep : (M₀ : ℚ) * d ≠ 0 := by positivity
  field_simp [hstep]
  ring

theorem residueTransition_physical {M₀ M₁ d : ℕ}
    (hM₀ : 0 < M₀) (hd : 0 < d) (hdiv : M₀ ∣ M₁)
    {ρ W S A : ℝ} (hρ : 0 ≤ ρ)
    (hold : ρ * W ≤ ((M₀ : ℝ) * d) * S) (hcurrent : (M₁ : ℝ) * A ≤ W) :
    ρ * (|((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)| * A) ≤ S := by
  have hstep : 0 < (M₀ : ℝ) * d := by positivity
  have hscale : ((M₀ : ℝ) * d) * ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ) = M₁ := by
    exact_mod_cast residueTransition_scale hdiv hd
  have hr : 0 ≤ ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ hstep).mp
  calc
    ((M₀ : ℝ) * d) * (ρ * (|((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)| * A)) =
        ρ * ((((M₀ : ℝ) * d) * ((((M₁ / M₀ : ℕ) : ℚ) / d : ℚ) : ℝ)) * A) := by
          rw [abs_of_nonneg hr]
          ring
    _ = ρ * ((M₁ : ℝ) * A) := by rw [hscale]
    _ ≤ ρ * W := mul_le_mul_of_nonneg_left hcurrent hρ
    _ ≤ ((M₀ : ℝ) * d) * S := hold

theorem residueTransition_denominator_bound {n d : ℕ} {B : ℝ}
    (hn : (n : ℝ) ≤ Real.exp B) (hd : (d : ℝ) ≤ Real.exp B) (s : ℕ) :
    ((n * d ^ s : ℕ) : ℝ) ≤ Real.exp (((s : ℝ) + 1) * B) := by
  push_cast
  calc
    (n : ℝ) * (d : ℝ) ^ s ≤ Real.exp B * Real.exp B ^ s :=
      mul_le_mul hn (pow_le_pow_left₀ (Nat.cast_nonneg _) hd s)
        (pow_nonneg (Nat.cast_nonneg _) _) (Real.exp_nonneg _)
    _ = Real.exp (((s : ℝ) + 1) * B) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

end Erdos3

end

section

namespace Erdos3

theorem scalarAffinePolynomial_comp {σ : Type*} (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) (i : σ) :
    MvPolynomial.aeval (scalarAffinePolynomial r₁ h₁) (scalarAffinePolynomial r₀ h₀ i) =
      scalarAffinePolynomial (r₀ * r₁) (fun j => r₀ * h₁ j + h₀ j) i := by
  simp only [scalarAffinePolynomial, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  ring

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_comp_orbit (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback r₁ h₁).orbit =
      (T.scalarAffinePullback (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i)).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial r₁ h₁)
      (VectorPolynomial.substitute (scalarAffinePolynomial r₀ h₀) T.orbit.log) =
    VectorPolynomial.substitute (scalarAffinePolynomial (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i))
      T.orbit.log
  rw [VectorPolynomial.substitute_comp]
  simp only [scalarAffinePolynomial_comp]

theorem scalarAffinePullback_comp_orbit_of_eq (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ a : ℚ) (h₀ h₁ shift : σ → ℚ) (hr : r₀ * a = r₁)
    (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback a shift).orbit =
      (T.scalarAffinePullback r₁ h₁).orbit := by
  rw [T.scalarAffinePullback_comp_orbit, hr, funext hh]

theorem scalarAffinePullback_transition_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r₀ r₁ : ℚ) (h₀ h₁ shift : σ → ℚ) {S H : σ → ℝ} {p q : ℝ} {M : ℕ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback r₀ h₀).symbol b ω hF) p M U)
    (a : ℤ) (m : ℕ) (ha : a ≠ 0) (hm : 0 < m)
    (hr : r₀ * ((a : ℚ) / m) = r₁) (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / m : ℚ) : ℝ)| * H i) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H
      ((T.scalarAffinePullback r₁ h₁).symbol b ω hF) (p + (s : ℝ) * q) (M * m ^ s) U := by
  have htransport := (T.scalarAffinePullback r₀ h₀).scalarAffinePullback_factorization
    b ω hF h a m ha hm shift hS hH hq hphysical
  have horbit := T.scalarAffinePullback_comp_orbit_of_eq r₀ r₁ ((a : ℚ) / m) h₀ h₁ shift hr hh
  have hsymbol :=
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback ((a : ℚ) / m) shift).symbol_eq_of_orbit_eq
      (T.scalarAffinePullback r₁ h₁) horbit b ω hF
  rwa [hsymbol] at htransport

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s e}

theorem scalarAffinePullback_residue_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {M₀ M₁ d n : ℕ} (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hd : 0 < d) (hdiv : M₀ ∣ M₁)
    (h₀ h₁ : σ → ℚ) {S A W : σ → ℝ} {p q : ℝ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback ((M₀ : ℚ) * d) h₀).symbol b ω hF) p n U)
    (hS : ∀ i, 0 < S i) (hA : ∀ i, 0 < A i) (hq : 0 ≤ q)
    (hold : ∀ i, Real.exp (-q) * W i ≤ ((M₀ : ℝ) * d) * S i)
    (hcurrent : ∀ i, (M₁ : ℝ) * A i ≤ W i) :
    D.filtration.SymbolFactorizationIn b ω hF A
      ((T.scalarAffinePullback (M₁ : ℚ) h₁).symbol b ω hF)
      (p + (s : ℝ) * q) (n * d ^ s) U := by
  let a : ℤ := (M₁ / M₀ : ℕ)
  have ha : a ≠ 0 := by
    dsimp only [a]
    exact_mod_cast (residueTransitionNumerator_pos hM₁ hdiv).ne'
  apply T.scalarAffinePullback_transition_factorization b ω hF
    ((M₀ : ℚ) * d) (M₁ : ℚ) h₀ h₁ (fun i => (h₁ i - h₀ i) / ((M₀ : ℚ) * d))
    h a d ha hd
  · simpa only [a, Int.cast_natCast] using residueTransition_scale hdiv hd
  · intro i
    exact residueTransition_shift hM₀ hd (h₀ i) (h₁ i)
  · exact hS
  · exact hA
  · exact hq
  · intro i
    simpa only [a, Int.cast_natCast] using
      residueTransition_physical hM₀ hd hdiv (Real.exp_nonneg (-q)) (hold i) (hcurrent i)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredReconstructionDiagram
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

theorem exists_native_refiltered_quotient_orbits {L σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1))
    (W : LieSubalgebra ℚ F.AssociatedGraded) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ (q : (F.gradedRefiltration W).realification.PolynomialOrbit w)
      (qbar : (F.gradedRefiltration W).quotientTop.realification.PolynomialOrbit w),
      VectorPolynomial.map
        (realLieHomToRat (realificationLieHom (F.gradedRefiltrationSubalgebra W).incl)).toLinearMap
        q.log = p ∧ coefficients q.log 0 = 0 ∧ DegreeLE w s qbar.log ∧
      ∀ x, (F.gradedRefiltration W).quotientTop.realification.polynomialOrbitEval w x qbar =
        (F.gradedRefiltration W).realQuotientStepHom
          ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl
          ((F.gradedRefiltration W).realification.polynomialOrbitEval w x q) := by
  obtain ⟨q, hq, hz⟩ := F.exists_native_refiltered_orbit W w hw p hp hzero
  let qbar := (F.gradedRefiltration W).realQuotientPolynomialOrbit
    ((F.gradedRefiltration W).layerIdeal (s + 1)) (t := s) le_rfl q
  exact ⟨q, qbar, hq, hz, qbar.degreeLE, fun x =>
    (F.gradedRefiltration W).realQuotientPolynomialOrbit_eval
      ((F.gradedRefiltration W).layerIdeal (s + 1)) le_rfl q x⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SingleRefilteredKernel
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)

theorem singleRefilteredQuotient_real_kernel
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (x : ℝ ⊗[ℚ] D.filtration.gradedRefiltrationSubalgebra W) :
    realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x = 0 ↔
      realificationLieHom (D.filtration.gradedRefiltrationSubalgebra W).incl x ∈
        D.filtration.realGradedRefiltrationLayer W (s + 1) := by
  change (E.filtration.layerIdeal (s + 1)).toSubmodule.mkQ.baseChange ℝ x = 0 ↔ _
  rw [realification_mkQ_eq_zero_iff]
  change x ∈ E.filtration.realification.layer (s + 1) ↔ _
  rw [hEF]
  exact D.filtration.mem_native_refiltration_layer W (s + 1) x

theorem single_refiltered_frozen_invariant
    (hEF : E.filtration = D.filtration.gradedRefiltration W)
    (S : D.Space → ℂ)
    (hinvariant : ∀ z : D.RealGroup,
      z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
        ∀ x, S (z • x) = S x)
    (l r : D.RealGroup) (z x : E.RealGroup)
    (hz : realificationLieHom (lieQuotientMap (E.filtration.layerIdeal (s + 1))) z.coord = 0) :
    let φ := NilpotentLieBCHGroup.realificationMap
      (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
    S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r)) := by
  let φ := NilpotentLieBCHGroup.realificationMap
    (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := D.filtration.lowerCentralSeries_eq_bot) (D.filtration.gradedRefiltrationSubalgebra W).incl
  have htop : (φ z).coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) :=
    (singleRefilteredQuotient_real_kernel D W E hEF z.coord).mp hz
  have hzlayer : φ z ∈ D.filtration.realification.subgroup (s + 1) :=
    D.filtration.realGradedRefiltrationLayer_le W (s + 1) htop
  have hcomm := D.filtration.realification.top_commutes (φ z) hzlayer l
  change S (QuotientGroup.mk (l * φ (z * x) * r)) = S (QuotientGroup.mk (l * φ x * r))
  rw [map_mul]
  have heq : l * (φ z * φ x) * r = φ z * (l * φ x * r) := by
    calc
      l * (φ z * φ x) * r = (l * φ z) * φ x * r := by simp only [mul_assoc]
      _ = (φ z * l) * φ x * r := by rw [hcomm.eq]
      _ = φ z * (l * φ x * r) := by simp only [mul_assoc]
  rw [heq]
  exact hinvariant (φ z) htop (QuotientGroup.mk (l * φ x * r))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_single_refiltered_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr
          ((D.filtration.gradedRefiltrationSubalgebra W).incl (E.basis j)) i) ≤ (p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            ∀ i j, rationalLogHeight (Q.basis.repr
              (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hsource⟩ := exists_controlled_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 11)
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d D w hF W v hspan p hp hD hκ hv
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hsource D w hF W v hspan hp hD hκ hv
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ := E.exists_controlled_top_quotient ht (hE.mono E hAt)
  have hsum : t + (t + 3) ^ 11 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hQC : (t + 3) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC),
    (fun i j => (hinc j i).trans (hAt.trans htC)), n, hn, Q, hQF, hQL,
    hQ.mono Q hQC, fun i j => (hproj j i).trans (h5.trans hQC)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledSingleRefilteredReconstruction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_single_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded),
      let H := D.filtration.gradedRefiltrationSubalgebra W
      ∀ {e n : ℕ} (E : RationalFilteredNilmanifold H (s + 1) e)
        (Q : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n),
      ∀ [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
        [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
        [TopologicalSpace (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))]
        [T2Space (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))] (p : ℝ),
      E.filtration = D.filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (H.incl (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      let T := Q.raiseStep (Nat.le_succ s)
      ∃ Λ : Subgroup T.filtration.Group, Λ ≤ T.lattice ∧
        (Λ.subgroupOf T.lattice).Characteristic ∧ (Λ.subgroupOf T.lattice).Normal ∧
        (Λ.subgroupOf T.lattice).FiniteIndex ∧ (Λ.relIndex T.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (B : ℕ) (hB : 0 < B)
          (hin : scaledIntegerGrid B ⊆ bchSubgroupCoordinates Q.basis Λ)
          (hout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid B),
          let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
          V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧
          V.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ l r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (let := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W (s + 1) →
                ∀ x, S (z • x) = S x) →
              ∃ (v : V.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (let := V.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧ (∀ x, ‖v x‖ ≤ 1) ∧
                ∀ x : E.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := V.filtration.lowerCentralSeries_eq_bot)
                    (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)) =
                  S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                    (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r)) := by
  obtain ⟨a, _, hrec⟩ := exists_uniform_frozen_reconstruction (s + 1) k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D W H e n E Q _ _ _ _ _ _ _ _ _ _ _ _ p hEF hp hE hD hQ hφ hψ q hq hqp T
  have hsum : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [Polynomial.eval₂_pow] using hbudget p hp
  have ha0 : 0 ≤ (p + a) ^ a := by positivity
  have hpC : p ≤ (p + C) ^ C := by linarith
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout, hV, hfrozen⟩ :=
    hrec E D T H.incl (lieQuotientMap (E.filtration.layerIdeal (s + 1))) p hp hE hD
      (Q.raiseStep_geometry (Nat.le_succ s) hQ) hφ hψ q hq hqp
  let V := Q.loweredCover (Nat.le_succ s) Λ B hB hin hout
  have hVlow : V.GeometryComplexityLE ((p + C) ^ C) :=
    Q.loweredCover_geometry (Nat.le_succ s) Λ B hB hin hout hQ hpC
      (hV.2.1.trans (Real.exp_le_exp.mpr haC))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr haC),
    B, hB, hin, hout, rfl, Q.lowerCoverLattice_le (Nat.le_succ s) Λ hΛ, hVlow, ?_⟩
  intro l r hl hr S ℓ hℓ hS hunit hinvariant
  have hkernel : ∀ z ∈ (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := T.filtration.lowerCentralSeries_eq_bot)
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)))).ker, ∀ x : E.RealGroup,
      S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl (z * x) * r)) =
      S (QuotientGroup.mk (l * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) H.incl x * r)) := by
    intro z hz x
    apply single_refiltered_frozen_invariant D W E hEF S hinvariant l r z x
    exact congrArg NilpotentLieBCHGroup.coord (MonoidHom.mem_ker.mp hz)
  obtain ⟨v, K, hK, hv, hpos, hcap, heval⟩ := hfrozen l r hl hr S ℓ hℓ hS hunit hkernel
  let lower := Q.loweredCoverMap (Nat.le_succ s) Λ B hB hin hout
  let := V.metricSpace
  let := (T.withLattice Λ B hB hin hout).metricSpace
  have hLip : LipschitzWith K (v ∘ lower) := by
    simpa only [mul_one] using hv.comp (Q.loweredCoverMap_lipschitz (Nat.le_succ s) Λ B hB hin hout)
  refine ⟨v ∘ lower, K, hK.trans (Real.exp_le_exp.mpr haC), hLip,
    (fun x => hpos (lower x)), (fun x => hcap (lower x)), ?_⟩
  intro x
  have hmap := Q.loweredCoverMap_mk (Nat.le_succ s) Λ B hB hin hout
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot)
      (lieQuotientMap (E.filtration.layerIdeal (s + 1))) x)
  exact (congrArg v hmap).trans (heval x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d e n : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem SingleRefilteredRecoveryFamily.mono {p p' cost cost' : ℝ} {q k : ℕ}
    (h : SingleRefilteredRecoveryFamily D W E Q p q k cost)
    (hp' : 0 ≤ p') (hpp : p' ≤ p) (hc : cost ≤ cost') :
    SingleRefilteredRecoveryFamily D W E Q p' q k cost' := by
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, B, hB, hin, hout,
    hVF, hVL, hV, hfrozen⟩ := h
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hc),
    B, hB, hin, hout, hVF, hVL, hV.mono _ hc, ?_⟩
  intro l r hl hr S ℓ hℓ hS hunit hinvariant
  have hl' : ∀ i, |(D.basis.baseChange ℝ).repr l.coord i| ≤ Real.exp ((p + 2) ^ k) := by
    intro i
    exact (hl i).trans (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨v, K, hK, hv, hpos, hcap, heval⟩ := hfrozen l r hl' hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp)) hS hunit hinvariant
  exact ⟨v, K, hK.trans (Real.exp_le_exp.mpr hc), hv, hpos, hcap, heval⟩

theorem exists_uniform_single_refilteredRecoveryFamily (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) {e n : ℕ}
      (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
      (p : ℝ), E.filtration = D.filtration.gradedRefiltration W →
      0 ≤ p → E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr
        ((D.filtration.gradedRefiltrationSubalgebra W).incl (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      SingleRefilteredRecoveryFamily D W E Q p q k ((p + C) ^ C) := by
  obtain ⟨C, hC, hrec⟩ := exists_single_refiltered_reconstruction s k
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D _ _ _ _ W e n E Q p hEF hp hE hD hQ hφ hψ q hq hqp
  let H := D.filtration.gradedRefiltrationSubalgebra W
  let N := H ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] H)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] H)
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
  let := realification_moduleTopology_t2 Q.basis
  exact hrec D W E Q p hEF hp hE hD hQ hφ hψ q hq hqp

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_controlled_single_refiltered_reconstruction (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v₀ : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v₀) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) j) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ n : ℕ, n ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            SingleRefilteredRecoveryFamily D W E Q p q k ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_single_refiltered_models
  obtain ⟨B, _, hrec⟩ := exists_uniform_single_refilteredRecoveryFamily s k
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A
  let P := R + (R + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ _ _ _ _ d D w hF W v₀ hspan p hp hD hκ hv q hq hqp
  obtain ⟨E, hEF, hEL, hE, hinc, n, hn, Q, hQF, hQL, hQ, hproj⟩ :=
    hmodels D w hF W v₀ hspan hp hD hκ hv
  let t := p + (p + A) ^ A
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg A)) _)
  have ht : 0 ≤ t := hp.trans hpt
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  have hsum : t + (t + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, R, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg B)) _)).trans hsum
  have hcost : (t + B) ^ B ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have hfamily := hrec D W E Q t hEF ht (hE.mono E hAt) (hD.mono D hpt)
    (hQ.mono Q hAt) (fun i j => (hinc i j).trans hAt) (fun i j => (hproj i j).trans hAt)
    q hq (hqp.trans (Real.exp_le_exp.mpr hpt))
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC), n, hn, Q, hQF, hQL,
    hQ.mono Q (hAt.trans htC), SingleRefilteredRecoveryFamily.mono D W E Q hfamily hp hpt hcost⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem scalarAffineAdaptedHom_coord {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ)
    (g : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.scalarAffineAdaptedHom r h g).coord : VectorPolynomial σ ℚ L) =
      weightedDilation (fun _ : σ => 1) r (translate h (g.coord : VectorPolynomial σ ℚ L)) := by
  change substitute (scalarAffinePolynomial r h) (g.coord : VectorPolynomial σ ℚ L) = _
  exact substitute_scalarAffinePolynomial r h _

theorem PolynomialSlowBound.scalarAffine {σ ι L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (T A : σ → ℝ)
    (hT : ∀ i, 0 < T i) (hA : ∀ i, 0 < A i) {M B : ℝ}
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialSlowBound b (fun _ => 1) T M g) (hM : 0 ≤ M) (hB : 1 ≤ B)
    (r : ℚ) (h : σ → ℚ)
    (hphysical : ∀ i, |(h i : ℝ)| + |(r : ℝ)| * A i ≤ B * T i) :
    F.PolynomialSlowBound b (fun _ => 1) A
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M * B ^ s)
      (F.realification.scalarAffineAdaptedHom r h g) := by
  have hdegree : DegreeLE (fun _ : σ => 1) s (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :=
    (F.realification.adaptedBCHToOrbit (fun _ => 1) g).degreeLE
  change CoefficientBound (b.baseChange ℝ) A _
    ((F.realification.scalarAffineAdaptedHom r h g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
  rw [scalarAffineAdaptedHom_coord]
  exact CoefficientBound.scalarAffine (b.baseChange ℝ) T A hT hA hg hM hB hdegree r h hphysical

theorem exists_scalarAffine_slow_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ ι L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (p : ℝ),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      ∀ T A : σ → ℝ, (∀ i, 0 < T i) → (∀ i, 0 < A i) →
      ∀ g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      F.PolynomialSlowBound b (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g →
      ∀ (r : ℚ) (h : σ → ℚ), (∀ i, |(h i : ℝ)| ≤ T i) →
      (∀ i, |(r : ℝ)| * A i ≤ T i) →
      F.PolynomialSlowBound b (fun _ => 1) A (Real.exp ((p + C) ^ C))
        (F.realification.scalarAffineAdaptedHom r h g) := by
  let P : Polynomial ℕ := Polynomial.C ((s + 1) * 2 ^ s) * (Polynomial.X + 1) ^ s +
    (Polynomial.X + 2) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ F b p hp hσ T A hT hA g hg r h hh hr
  have hbound := PolynomialSlowBound.scalarAffine F b T A hT hA g hg
    (Real.exp_nonneg _) (by norm_num : (1 : ℝ) ≤ 2) r h (fun i => by linarith [hh i, hr i])
  let K := ((s : ℝ) + 1) * (p + 1) ^ s * 2 ^ s
  have hK : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * 2 ^ s ≤ K := by
    dsimp [K]
    gcongr
  have hKe : K ≤ Real.exp K := by linarith [Real.add_one_le_exp K]
  have hcost : K + (p + 2) ^ a ≤ (p + C) ^ C := by
    simpa [P, K, Polynomial.eval₂_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_assoc,
      mul_left_comm, mul_comm] using hbudget p hp
  apply F.polynomialSlowBound_mono b (fun _ => 1) A hA _ _ hbound
  calc
    ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * Real.exp ((p + 2) ^ a) * 2 ^ s =
        (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * 2 ^ s) * Real.exp ((p + 2) ^ a) := by ring
    _ ≤ K * Real.exp ((p + 2) ^ a) := mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
    _ ≤ Real.exp K * Real.exp ((p + 2) ^ a) := mul_le_mul_of_nonneg_right hKe (Real.exp_nonneg _)
    _ = Real.exp (K + (p + 2) ^ a) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hcost

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RetainedPhysicalLowerDegree
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem hasNativeLowerDegreeOrbit_of_coefficients {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer W (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) : F.HasNativeLowerDegreeOrbit W w p := by
  apply F.exists_native_refiltered_quotient_orbits W w hw p hp hzero

end NilpotentLieFiltration

theorem exists_retained_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n : J → ℕ)
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p (n j) (U j)) →
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨C, hC, hnormalize⟩ := exists_retained_lattice_normalization_s2 (s + 1)
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF U v n p hp hD hσ hJ hv hU hheight hn hnp A hA g hfactor
  obtain ⟨v₀, m, κ, E, b, R, hv₀, hW, hvheight, hm, hmp, hnm, hκ, hprod,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hnormalize D w hF U v n p hp hD hσ hJ hv hU hheight hn hnp A hA g hfactor
  refine ⟨v₀, m, κ, E, b, R, hv₀, hW, hvheight, hm, hmp, hnm, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, hvalues, ?_⟩
  apply D.filtration.hasNativeLowerDegreeOrbit_of_coefficients (⨅ j, U j) (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) b.coord hcoeff hb0

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_retained_physical_lower_degree_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n aux oldModulus : J → ℕ)
      (M : ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, 0 < aux j) → (∀ j, 0 < oldModulus j) → 0 < M →
      (∀ j, oldModulus j ∣ M) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      (∀ j, (aux j : ℝ) ≤ Real.exp p) →
      ∀ W A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ (T : D.Niltest (fun _ : σ => 1)) (shift : σ → ℚ)
        (oldShift : J → σ → ℚ) (oldSides : J → σ → ℝ),
      (∀ j i, 0 < oldSides j i) → (∀ i, (M : ℝ) * A i ≤ W i) →
      (∀ j i, Real.exp (-p) * W i ≤ ((oldModulus j : ℝ) * aux j) * oldSides j i) →
      (∀ j, D.filtration.SymbolFactorizationIn D.basis w hF (oldSides j)
        ((T.scalarAffinePullback ((oldModulus j : ℚ) * aux j) (oldShift j)).symbol D.basis w hF)
        p (n j) (U j)) →
      let current := T.scalarAffinePullback (M : ℚ) shift
      let g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨current.orbit.log, current.orbit.property⟩⟩
      ∃ (v₀ : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v₀) = (⨅ j, U j).toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w (⨅ j, U j).toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v₀ i) k) ≤
          (p + C) ^ C) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (∀ j, n j * aux j ^ (s + 1) ∣ m) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer (⨅ j, U j) (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra (⨅ j, U j))) ∧
        D.filtration.HasNativeLowerDegreeOrbit (⨅ j, U j) (fun _ : σ => 1)
          (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_retained_lower_degree_factorization s
  let Q : Polynomial ℕ := (Polynomial.C (s + 2) * Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget Q
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ _ D w hF U v n aux oldModulus M p hp hD hσ hJ
    hv hU hheight hn haux hOld hM hdiv hnp hauxp W A hA T shift oldShift oldSides
    hSides hcurrent hphysical hold current g
  let P : ℝ := (s + 2 : ℕ) * p
  have hpP : p ≤ P := by
    dsimp only [P]
    have hs : (1 : ℝ) ≤ (s + 2 : ℕ) := by exact_mod_cast (by omega : 1 ≤ s + 2)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hs hp
  have hP : 0 ≤ P := hp.trans hpP
  have hcost : (P + a) ^ a ≤ (p + C) ^ C := by
    simpa [P, Q, Polynomial.eval₂_pow] using hbudget p hp
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  have hfactor : ∀ j, D.filtration.SymbolFactorizationIn D.basis w hF A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g)
      P (n j * aux j ^ (s + 1)) (U j) := by
    intro j
    change D.filtration.SymbolFactorizationIn D.basis w hF A
      ((T.scalarAffinePullback (M : ℚ) shift).symbol D.basis w hF) P _ _
    have ht := T.scalarAffinePullback_residue_factorization D.basis w hF
      (hOld j) hM (haux j) (hdiv j) (oldShift j) shift (hold j) (hSides j) hApos hp
      (hphysical j) hcurrent
    have hbound : p + ((s + 1 : ℕ) : ℝ) * p ≤ P := by
      apply le_of_eq
      dsimp only [P]
      push_cast
      ring
    exact ht.mono D.filtration D.basis w hF hbound hApos
  have hden : ∀ j, ((n j * aux j ^ (s + 1) : ℕ) : ℝ) ≤ Real.exp P := by
    intro j
    have he : (((s + 1 : ℕ) : ℝ) + 1) * p = P := by
      dsimp only [P]
      push_cast
      ring
    simpa only [he] using residueTransition_denominator_bound (hnp j) (hauxp j) (s + 1)
  obtain ⟨v₀, m, κ, E, b, R, hv₀, hgraded, hvheight, hm, hmp, hnm, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, hvalues, hlower⟩ :=
    hnormalize D w hF U v (fun j => n j * aux j ^ (s + 1)) P hP (hD.mono D hpP)
      (hσ.trans hpP) (hJ.trans hpP) hv hU (fun j i k => (hheight j i k).trans hpP)
      (fun j => Nat.mul_pos (hn j) (pow_pos (haux j) _)) hden A
      (fun i => (Real.exp_le_exp.mpr hcost).trans (hA i)) g hfactor
  refine ⟨v₀, m, κ, E, b, R, hv₀, hgraded, fun i k => (hvheight i k).trans hcost,
    hm, hmp.trans (Real.exp_le_exp.mpr hcost), hnm, hκ, hprod, ?_, hR, hb0, hR0, hcoeff, hvalues, hlower⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
    (monomialScale_pos A hApos α).le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RetainedAffineResidueEpoch
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct

theorem exists_controlled_affine_residue_child (s a : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ (P : ℕ) (hP : 0 < P), (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (v : Fin d → D.filtration.AssociatedGraded),
          Submodule.span ℚ (Set.range v) = W.toSubmodule →
          (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v i) j) ≤ p) →
          ∀ b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
          (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
            D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) →
          coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 →
          ∃ cost : ℝ, 0 ≤ cost ∧ cost ≤ (p + 2) ^ K ∧
            HasFixedAffineResidueChild D W b p q P hP C a cost := by
  obtain ⟨C, hC, hchild⟩ := exists_fixed_child_affine_residue_descent_s2 s a
  obtain ⟨R, _, hmodels⟩ := exists_controlled_single_refiltered_reconstruction s C
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C R) ^ R + 4
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget B
  refine ⟨C, K, hC, hK, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p hp hD hσ q hq hqp
  obtain ⟨P, hP, hPb, hdesc⟩ := hchild D p hp hD hσ q hq hqp
  refine ⟨P, hP, hPb, ?_⟩
  intro W v hspan hv b hb hb0
  have hd : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hD.1
  obtain ⟨E, hEF, _, _, n, hn, Q, hQF, _, _, hfamily⟩ :=
    hmodels D ω hF W v hspan hp hD hd hv q hq hqp
  have hcost0 : 0 ≤ (p + R) ^ R := by positivity
  have hcost : (p + R) ^ R + 4 ≤ (p + 2) ^ K := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hnD : n ≤ d := by
    have hh := lie_subalgebra_finrank_le D.basis (D.filtration.gradedRefiltrationSubalgebra W)
    simpa only [Fintype.card_fin] using hn.trans hh
  have hfixed := hdesc W E Q hEF hQF b hb hb0 ((p + R) ^ R) hcost0 hfamily
  refine ⟨(p + R) ^ R + 4, by positivity, hcost, E, hEF, n, hnD, Q, hQF, ?_⟩
  intro H N _ _ _
  obtain ⟨Λ, _, _, _, _, _, B₀, hB₀, hin, hout, hVF, hVL, hV, child, hdegree, hresidue⟩ := hfixed
  let V := Q.loweredCover (Nat.le_succ s) Λ B₀ hB₀ hin hout
  exact ⟨V, hVF, hVL, hV.mono V (by linarith), child, hdegree, hresidue⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_retained_affine_residue_epoch (s : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧ ∀ {σ J L : Type*} [Fintype σ] [DecidableEq σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (U : J → LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : J → Fin d → D.filtration.AssociatedGraded) (n aux oldModulus : J → ℕ)
      (M : ℕ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω (U j).toSubmodule) →
      (∀ j i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (v j i) k) ≤ p) →
      (∀ j, 0 < n j) → (∀ j, 0 < aux j) → (∀ j, 0 < oldModulus j) → 0 < M →
      (∀ j, oldModulus j ∣ M) → (∀ j, (n j : ℝ) ≤ Real.exp p) →
      (∀ j, (aux j : ℝ) ≤ Real.exp p) →
      ∀ W A : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ K) ≤ A i) →
      ∀ (T : D.Niltest (fun _ : σ => 1)) (shift : σ → ℚ)
        (oldShift : J → σ → ℚ) (oldSides : J → σ → ℝ),
      (∀ j i, 0 < oldSides j i) → (∀ i, (M : ℝ) * A i ≤ W i) →
      (∀ j i, Real.exp (-p) * W i ≤ ((oldModulus j : ℝ) * aux j) * oldSides j i) →
      (∀ j, D.filtration.SymbolFactorizationIn D.basis ω hF (oldSides j)
        ((T.scalarAffinePullback ((oldModulus j : ℚ) * aux j) (oldShift j)).symbol D.basis ω hF)
        p (n j) (U j)) →
      ∃ work cost : ℝ, p + 16 ≤ work ∧ work ≤ (p + 2) ^ K ∧ 0 ≤ cost ∧ cost ≤ (p + 2) ^ K ∧
        RetainedAffineResidueEpoch D ω hF (⨅ j, U j) (T.scalarAffinePullback (M : ℚ) shift) A work cost C := by
  obtain ⟨F, hFmin, hnormalize⟩ := exists_retained_physical_lower_degree_factorization s
  obtain ⟨S, _, hslow⟩ := exists_scalarAffine_slow_bound (s + 1) ((F + 1) * F)
  obtain ⟨C, D₀, hC, _, hchild⟩ := exists_controlled_affine_residue_child s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C F) ^ F +
    (Polynomial.X + Polynomial.C S) ^ S + 16
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C F) ^ F + Q + (Q + 2) ^ D₀
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget R
  refine ⟨C, K, hC, hK, ?_⟩
  intro σ J L _ _ _ _ _ d _ _ _ _ D ω hF U v n aux oldModulus M p hp hD hσ hJ
    hv hgraded hheight hn haux hOld hM hdiv hnp hauxp W A hA T shift oldShift oldSides
    hSides hcurrent hphysical hold
  let work := p + (p + F) ^ F + (p + S) ^ S + 16
  have hF0 : 0 ≤ (p + F) ^ F := by positivity
  have hS0 : 0 ≤ (p + S) ^ S := by positivity
  have hpwork16 : p + 16 ≤ work := by dsimp only [work]; linarith
  have hpwork : p ≤ work := by linarith
  have hwork0 : 0 ≤ work := hp.trans hpwork
  have hFwork : (p + F) ^ F ≤ work := by dsimp only [work]; linarith
  have hSwork : (p + S) ^ S ≤ work := by dsimp only [work]; linarith
  have htotal : (p + F) ^ F + work + (work + 2) ^ D₀ ≤ (p + 2) ^ K := by
    simpa [R, Q, work, Polynomial.eval₂_pow] using hbudget p hp
  have hpower0 : 0 ≤ (work + 2) ^ D₀ := by positivity
  have hFbound : (p + F) ^ F ≤ (p + 2) ^ K := by linarith
  have hworkbound : work ≤ (p + 2) ^ K := by linarith
  have hchildbound : (work + 2) ^ D₀ ≤ (p + 2) ^ K := by linarith
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  obtain ⟨v₀, m, κ, E, b, R₀, hv₀, hWgraded, hvheight, hm, hmp, _, hκ, hprod,
    hE, hR, hb0, hR0, hcoeff, _, _⟩ :=
    hnormalize D ω hF U v n aux oldModulus M p hp hD hσ hJ hv hgraded hheight
      hn haux hOld hM hdiv hnp hauxp W A
      (fun i => (Real.exp_le_exp.mpr hFbound).trans (hA i))
      T shift oldShift oldSides hSides hcurrent hphysical hold
  have hmpwork : (m : ℝ) ≤ Real.exp work := hmp.trans (Real.exp_le_exp.mpr hFwork)
  obtain ⟨P, hP, hPb, hconstruct⟩ := hchild D ω hF work hwork0 (hD.mono D hpwork)
    (hσ.trans hpwork) m hm hmpwork
  obtain ⟨cost, hcost0, hcost, hfixed⟩ := hconstruct (⨅ j, U j) v₀ hv₀
    (fun i j => (hvheight i j).trans hFwork) b hcoeff hb0
  have hEcoeff := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hApos
    (Real.exp_le_exp.mpr (shifted_power_le_fixed_base hp F hFmin)) E hE
  refine ⟨work, cost, hpwork16, hworkbound, hcost0, hcost.trans hchildbound,
    v₀, m, P, hP, κ, E, b, R₀, hv₀, hWgraded, fun i j => (hvheight i j).trans hFwork,
    hm, hmpwork, hPb, hκ, hprod, ?_, ?_, hR, hb0, hR0, hcoeff, hfixed⟩
  · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hApos
      (Real.exp_le_exp.mpr (by linarith)) E hE
  · intro B hB r h hh hr
    have hpull := hslow D.filtration D.basis p hp hσ A B hApos hB E hEcoeff r h hh hr
    exact D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) B hB
      (Real.exp_le_exp.mpr (by linarith)) _ hpull

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

variable {σ L : Type*}
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {ω : Fin d → ℕ}
  {hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})}
  {T : D.Niltest (fun _ : σ => 1)}

theorem epochRecordIntersection_eq_iInf (rs : List (EpochSymbolRecord D ω hF T)) :
    epochRecordIntersection rs = ⨅ i : Fin rs.length, (rs.get i).fast := by
  induction rs with
  | nil =>
    simp only [epochRecordIntersection]
    exact le_antisymm (le_iInf fun i => Fin.elim0 i) le_top
  | cons r rs ih =>
    change r.fast ⊓ epochRecordIntersection rs = ⨅ i : Fin (r :: rs).length, ((r :: rs).get i).fast
    apply le_antisymm
    · apply le_iInf
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact inf_le_left
      · have hle : epochRecordIntersection rs ≤ (rs.get j).fast := by rw [ih]; exact iInf_le _ j
        exact inf_le_right.trans hle
    · apply le_inf
      · exact iInf_le _ (0 : Fin (r :: rs).length)
      · rw [ih]
        exact le_iInf fun j => iInf_le _ j.succ

theorem EpochRecordHistory.length_add_finrank_le {rs : List (EpochSymbolRecord D ω hF T)}
    (h : EpochRecordHistory rs) :
    rs.length + finrank ℚ (epochRecordIntersection rs) ≤
      finrank ℚ (⊤ : LieSubalgebra ℚ D.filtration.AssociatedGraded) := by
  induction rs with
  | nil =>
    simp only [List.length_nil, epochRecordIntersection, Nat.zero_add]
    exact Nat.le_refl _
  | cons r rs ih =>
    cases h with
    | cons history drop =>
      have htail := ih history
      change rs.length + 1 + finrank ℚ ↥(r.fast ⊓ epochRecordIntersection rs) ≤ _
      rw [inf_comm r.fast]
      omega

theorem EpochRecordHistory.length_le_dimension {rs : List (EpochSymbolRecord D ω hF T)}
    (h : EpochRecordHistory rs) : rs.length ≤ d := by
  have hrank := h.length_add_finrank_le
  have htop := lie_subalgebra_finrank_le (D.filtration.associatedGradedBasis D.basis ω hF)
    (⊤ : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  simp only [Fintype.card_fin] at htop
  omega

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra
  PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup
  PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_retained_epoch_from_records_s2_oai (s : ℕ) :
    ∃ C K : ℕ, 2 ≤ C ∧ 2 ≤ K ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (T : D.Niltest (fun _ : σ => 1))
      (rs : List (EpochSymbolRecord D ω hF T)), EpochRecordHistory rs →
      ∀ (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      ∀ W : σ → ℝ, (∀ r ∈ rs, r.Controlled W p) →
      ∀ M : ℕ, 0 < M → (∀ r ∈ rs, r.modulus ∣ M) →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + 2) ^ K) ≤ A i) →
      (∀ i, (M : ℝ) * A i ≤ W i) → ∀ shift : σ → ℚ,
      ∃ work cost : ℝ, p + 16 ≤ work ∧ work ≤ (p + 2) ^ K ∧ 0 ≤ cost ∧ cost ≤ (p + 2) ^ K ∧
        RetainedAffineResidueEpoch D ω hF (epochRecordIntersection rs)
          (T.scalarAffinePullback (M : ℚ) shift) A work cost C := by
  obtain ⟨C, K, hC, hK, hconstruct⟩ := exists_retained_affine_residue_epoch s
  refine ⟨C, K, hC, hK, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF T rs history p hp hD hσ W hcontrolled M hM hdiv A hA hcurrent shift
  let recordAt : Fin rs.length → EpochSymbolRecord D ω hF T := fun i => rs.get i
  have hmem : ∀ i, recordAt i ∈ rs := fun i => List.get_mem rs i
  have hcontrol : ∀ i, (recordAt i).Controlled W p := fun i => hcontrolled (recordAt i) (hmem i)
  have hcount : (Fintype.card (Fin rs.length) : ℝ) ≤ p := by
    have hc : (rs.length : ℝ) ≤ d := by exact_mod_cast history.length_le_dimension
    simpa only [Fintype.card_fin] using hc.trans hD.1
  have hfactor : ∀ i, D.filtration.SymbolFactorizationIn D.basis ω hF (recordAt i).sides
      ((T.scalarAffinePullback (((recordAt i).modulus : ℚ) * (recordAt i).auxiliary) (recordAt i).shift).symbol D.basis ω hF)
      p (recordAt i).denominator (recordAt i).fast := by
    intro i
    exact (recordAt i).factorization.mono D.filtration D.basis ω hF (hcontrol i).1 (recordAt i).sides_pos
  have hresult := hconstruct D ω hF (fun i => (recordAt i).fast) (fun i => (recordAt i).spanning)
    (fun i => (recordAt i).denominator) (fun i => (recordAt i).auxiliary) (fun i => (recordAt i).modulus)
    M p hp hD hσ hcount (fun i => (recordAt i).span_eq) (fun i => (recordAt i).graded)
    (fun i j k => ((recordAt i).height_le j k).trans (hcontrol i).1)
    (fun i => (recordAt i).denominator_pos) (fun i => (recordAt i).auxiliary_pos) (fun i => (recordAt i).modulus_pos)
    hM (fun i => hdiv (recordAt i) (hmem i))
    (fun i => (recordAt i).denominator_le.trans (Real.exp_le_exp.mpr (hcontrol i).1))
    (fun i => (hcontrol i).2.1) W A hA T shift (fun i => (recordAt i).shift) (fun i => (recordAt i).sides)
    (fun i => (recordAt i).sides_pos) hcurrent (fun i => (hcontrol i).2.2) hfactor
  simpa only [epochRecordIntersection_eq_iInf] using hresult

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.exists_retained_epoch_from_records_s2_oai.{u_1, u_2} := @OAI.Erdos3.exists_retained_epoch_from_records_s2_oai.{u_1, u_2}
