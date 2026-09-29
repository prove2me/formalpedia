-- Prove2me | solution 1 for HlawkaSchatten.rectangularBregmanObjective_isGlobalMinimumValue
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T22:48:27.355984+00:00
-- url     : https://prove2.me/submissions/cd6fc30e-fb3f-4b1b-b784-d33322a2b1cd

import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_HermitianSpectral
import Definitions.Def_HlawkaSchatten_ScalarBregman
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_SpectralLift
import Definitions.Def_HlawkaSchatten_Variational
import Theorems.Thm_HlawkaSchatten_dilatedBregmanTrace_self
import Theorems.Thm_HlawkaSchatten_powerGradient_mul_self
import Theorems.Thm_HlawkaSchatten_scalarBregman_nonneg
import Theorems.Thm_HlawkaSchatten_spectralBregmanTrace_eq_sum
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Instances.Sign

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Variational minima for the Bregman--Mazur argument

This file proves two reusable parts of the variational layer.  First, a
pointwise two-sided comparison transports to attained global minima, even
when the two objectives are indexed by different but equivalent spheres.
Second, the weighted squared-distance objective on a Hilbert unit sphere has
the exact minimum used in the Schatten argument.
-/


open scoped InnerProductSpace ComplexConjugate







variable {𝕜 H ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]











section RectangularMazur

variable {E F κ : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Nonnegative weighted lift of the scalar comparison

The Hermitian spectral argument writes both divergences as finite sums with
weights `Tr(Pᵢ Qⱼ) ≥ 0`.  This file isolates the ordered-algebraic step which
lifts the pointwise scalar bounds through those sums.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace





section SpectralOverlap

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]



theorem orthonormalBasisOverlap_nonneg
    (e : OrthonormalBasis ι ℂ E) (f : OrthonormalBasis κ ℂ E)
    (ij : ι × κ) :
    0 ≤ orthonormalBasisOverlap e f ij := by
  exact sq_nonneg _







end SpectralOverlap

end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite Hermitian spectral trace expansions

This file connects the overlap-weighted scalar comparison to traces of
finite-dimensional symmetric complex-linear maps.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace
open RCLike
open ComplexConjugate

variable {ι κ E : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]



































/-- Trace-level Euler identity for the Hermitian power functional calculus. -/
theorem re_trace_powerGradient_mul_self [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 0 < p) (A : E →ₗ[ℂ] E) (hA : A.IsSymmetric) :
    ((hermitianFunctionalCalculus
      (fun x => powerGradient p x * x) A hA).trace ℂ E).re =
      p * ((hermitianFunctionalCalculus
        (powerPotential p) A hA).trace ℂ E).re := by
  rw [re_trace_hermitianFunctionalCalculus,
    re_trace_hermitianFunctionalCalculus, Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  exact powerGradient_mul_self hp _























theorem spectralBregmanTrace_nonneg [FiniteDimensional ℂ E]
    {p : ℝ} (hp : 1 < p) (e : OrthonormalBasis ι ℂ E) (a : ι → ℝ)
    (f : OrthonormalBasis κ ℂ E) (b : κ → ℝ) :
    0 ≤ spectralBregmanTrace p e a f b := by
  rw [spectralBregmanTrace_eq_sum]
  exact Finset.sum_nonneg fun ij _ ↦
    mul_nonneg (orthonormalBasisOverlap_nonneg e f ij)
      (scalarBregman_nonneg hp (a ij.1) (b ij.2))





















/-- Operator-functional-calculus form of the canonical Hermitian Bregman
quantity. This is the form used by the rectangular dilation step. -/
theorem hermitianBregmanTrace_eq_functionalCalculus [FiniteDimensional ℂ E]
    (p : ℝ) (A B : E →ₗ[ℂ] E) (hA : A.IsSymmetric) (hB : B.IsSymmetric) :
    hermitianBregmanTrace p A B hA hB =
      ((hermitianFunctionalCalculus (powerPotential p) A hA).trace ℂ E).re -
      ((hermitianFunctionalCalculus (powerPotential p) B hB).trace ℂ E).re -
      ((A.comp (hermitianFunctionalCalculus (powerGradient p) B hB)).trace ℂ E).re +
      ((hermitianFunctionalCalculus
        (fun x ↦ powerGradient p x * x) B hB).trace ℂ E).re := by
  unfold hermitianBregmanTrace spectralBregmanTrace hermitianFunctionalCalculus
  rw [spectralDiagonal_eigenvectorBasis_eq A hA]
  congr 3

















end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Rectangular Hermitian dilation

This file begins the passage from rectangular maps to the Hermitian spectral
comparison by constructing the standard off-diagonal dilation.
-/

namespace HlawkaSchatten

open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]









































































/-- The dilated gradient pairing is additive in its first argument. -/
theorem dilatedGradientPairing_add
    (p : ℝ) (R S T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p (R + S) T =
      dilatedGradientPairing p R T + dilatedGradientPairing p S T := by
  unfold dilatedGradientPairing
  rw [hermitianDilation_add, LinearMap.add_comp, map_add, Complex.add_re]
  ring

/-- The dilated gradient pairing is real-homogeneous in its first argument. -/
theorem dilatedGradientPairing_real_smul
    (p r : ℝ) (S T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p ((r : ℂ) • S) T =
      r * dilatedGradientPairing p S T := by
  unfold dilatedGradientPairing
  rw [hermitianDilation_real_smul, LinearMap.smul_comp, map_smul]
  rw [smul_eq_mul, Complex.re_ofReal_mul]
  ring

@[simp]
theorem dilatedGradientPairing_zero (p : ℝ) (T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p 0 T = 0 := by
  unfold dilatedGradientPairing
  simp

/-- Finite real linearity of the dilated gradient pairing. -/
theorem dilatedGradientPairing_sum
    {ι : Type*} [Fintype ι] (p : ℝ) (a : ι → ℝ)
    (u : ι → E →ₗ[ℂ] F) (T : E →ₗ[ℂ] F) :
    dilatedGradientPairing p (∑ i, (a i : ℂ) • u i) T =
      ∑ i, a i * dilatedGradientPairing p (u i) T := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        dilatedGradientPairing_add, dilatedGradientPairing_real_smul, ih]

/-- Dilated Bregman divergence is nonnegative for `p > 1`. -/
theorem dilatedBregmanTrace_nonneg
    {p : ℝ} (hp : 1 < p) (S T : E →ₗ[ℂ] F) :
    0 ≤ dilatedBregmanTrace p S T := by
  unfold dilatedBregmanTrace hermitianBregmanTrace
  exact spectralBregmanTrace_nonneg hp _ _ _ _



/-- On the Schatten-`p` power sphere, the normalized dilated Bregman
divergence is one minus the dilated gradient pairing. -/
theorem dilatedBregmanTrace_div_two_eq_one_sub_pairing
    {p : ℝ} (hp : 0 < p) (S T : E →ₗ[ℂ] F)
    (hS : singularValuePowerSum p S = 1)
    (hT : singularValuePowerSum p T = 1) :
    dilatedBregmanTrace p S T / 2 =
      1 - dilatedGradientPairing p S T := by
  unfold dilatedBregmanTrace dilatedGradientPairing
  rw [hermitianBregmanTrace_eq_functionalCalculus]
  rw [re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp S,
    re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T,
    re_trace_powerGradient_mul_self hp
      (hermitianDilation T) (hermitianDilation_isSymmetric T),
    re_trace_dilated_powerPotential_eq_two_mul_singularValuePowerSum hp T,
    hS, hT]
  field_simp [hp.ne']
  ring



























































end HlawkaSchatten

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Finite-dimensional Schatten quantities

This file gives the definition needed by the Hlawka boundary. Mathlib's
singular-value sequence is finitely supported, so the power sum is finite
without choosing bases or matrix dimensions.
-/

namespace HlawkaSchatten

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]



















@[simp]
theorem singularValuePowerSum_zero (p : ℝ) :
    singularValuePowerSum p (0 : E →ₗ[𝕜] F) = 0 := by
  simp [singularValuePowerSum]

@[simp]
theorem schattenPNorm_zero (p : ℝ) (hp : p ≠ 0) :
    schattenPNorm p (0 : E →ₗ[𝕜] F) = 0 := by
  simp [schattenPNorm, hp]





end HlawkaSchatten

/-- On power-sphere inputs, the finite Bregman objective is the total weight
minus one gradient pairing with the weighted operator sum. -/
theorem rectangularBregmanObjective_eq_sum_sub_pairing
    {p : ℝ} (hp : 0 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (v : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    rectangularBregmanObjective p a u v =
      (∑ i, a i) - dilatedGradientPairing p (rectangularWeightedSum a u) v.1 := by
  unfold rectangularBregmanObjective rectangularWeightedSum
  have hterm : ∀ i,
      dilatedBregmanTrace p (u i).1 v.1 / 2 =
        1 - dilatedGradientPairing p (u i).1 v.1 := fun i =>
    dilatedBregmanTrace_div_two_eq_one_sub_pairing hp _ _
      (u i).property v.property
  simp_rw [hterm]
  rw [dilatedGradientPairing_sum p a (fun i => (u i).1) v.1]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib]

theorem solution
    [Nonempty ι] {p : ℝ} (hp : 1 < p) (a : ι → ℝ)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p) :
    IsGlobalMinimumValue (rectangularBregmanObjective p a u)
      ((∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u)) := by
  let W := rectangularWeightedSum a u
  have hp0 : 0 < p := zero_lt_one.trans hp
  constructor
  · intro v
    rw [rectangularBregmanObjective_eq_sum_sub_pairing hp0 a u v]
    change (∑ i, a i) - schattenPNorm p W ≤
      (∑ i, a i) - dilatedGradientPairing p W v.1
    by_cases hW : W = 0
    · rw [hW, dilatedGradientPairing_zero, schattenPNorm_zero p hp0.ne']
    · let r := schattenPNorm p W
      have hr : 0 < r := schattenPNorm_pos p hW
      let U₀ : E →ₗ[ℂ] F := ((r⁻¹ : ℝ) : ℂ) • W
      have hnormU₀ : schattenPNorm p U₀ = 1 := by
        dsimp only [U₀]
        rw [schattenPNorm_real_smul hp0 (inv_pos.mpr hr),
          inv_mul_cancel₀ hr.ne']
      have hpowerU₀ : singularValuePowerSum p U₀ = 1 :=
        (schattenPNorm_eq_one_iff hp0 U₀).mp hnormU₀
      have hnonneg := dilatedBregmanTrace_nonneg hp U₀ v.1
      have hformula := dilatedBregmanTrace_div_two_eq_one_sub_pairing
        hp0 U₀ v.1 hpowerU₀ v.property
      have hpairU₀ : dilatedGradientPairing p U₀ v.1 ≤ 1 := by
        linarith
      have hWU₀ : W = (r : ℂ) • U₀ := by
        dsimp only [U₀]
        rw [smul_smul]
        simp [hr.ne']
      have hpairW : dilatedGradientPairing p W v.1 =
          r * dilatedGradientPairing p U₀ v.1 := by
        rw [hWU₀, dilatedGradientPairing_real_smul]
      have hle : dilatedGradientPairing p W v.1 ≤ r := by
        rw [hpairW]
        nlinarith
      exact sub_le_sub_left hle _
  · by_cases hW : W = 0
    · let i : ι := Classical.choice inferInstance
      refine ⟨u i, ?_⟩
      rw [rectangularBregmanObjective_eq_sum_sub_pairing hp0 a u (u i)]
      change (∑ j, a j) - dilatedGradientPairing p W (u i).1 =
        (∑ j, a j) - schattenPNorm p W
      rw [hW, dilatedGradientPairing_zero, schattenPNorm_zero p hp0.ne']
    · let r := schattenPNorm p W
      have hr : 0 < r := schattenPNorm_pos p hW
      let U₀ : E →ₗ[ℂ] F := ((r⁻¹ : ℝ) : ℂ) • W
      have hnormU₀ : schattenPNorm p U₀ = 1 := by
        dsimp only [U₀]
        rw [schattenPNorm_real_smul hp0 (inv_pos.mpr hr),
          inv_mul_cancel₀ hr.ne']
      have hpowerU₀ : singularValuePowerSum p U₀ = 1 :=
        (schattenPNorm_eq_one_iff hp0 U₀).mp hnormU₀
      let U : schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p :=
        ⟨U₀, hpowerU₀⟩
      have hWU₀ : W = (r : ℂ) • U₀ := by
        dsimp only [U₀]
        rw [smul_smul]
        simp [hr.ne']
      have hpairSelf : dilatedGradientPairing p U₀ U₀ = 1 := by
        have hformula := dilatedBregmanTrace_div_two_eq_one_sub_pairing
          hp0 U₀ U₀ hpowerU₀ hpowerU₀
        rw [dilatedBregmanTrace_self] at hformula
        linarith
      refine ⟨U, ?_⟩
      rw [rectangularBregmanObjective_eq_sum_sub_pairing hp0 a u U]
      change (∑ i, a i) - dilatedGradientPairing p W U₀ =
        (∑ i, a i) - schattenPNorm p W
      have hpairW : dilatedGradientPairing p W U₀ =
          r * dilatedGradientPairing p U₀ U₀ := by
        rw [hWU₀, dilatedGradientPairing_real_smul]
      rw [hpairW, hpairSelf, mul_one]
