-- Prove2me | solution 1 for HlawkaSchatten.finiteFamilyGap_two_sided
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-09-27T23:40:37.925086+00:00
-- url     : https://prove2.me/submissions/f8421639-9aad-4040-b747-31df12553f7b

import Definitions.Def_HlawkaSchatten_Final
import Definitions.Def_HlawkaSchatten_HermitianDilation
import Definitions.Def_HlawkaSchatten_SchattenNorm
import Definitions.Def_HlawkaSchatten_Variational
import Theorems.Thm_HlawkaSchatten_globalMinimumValue_two_sided_of_equiv
import Theorems.Thm_HlawkaSchatten_rectangularBregmanObjective_isGlobalMinimumValue
import Theorems.Thm_HlawkaSchatten_rectangularBregmanObjective_two_sided
import Theorems.Thm_HlawkaSchatten_rectangularMazurDistanceObjective_isGlobalMinimumValue
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
# Dimension-independent Hlawka constants for Schatten norms

This file removes the unit-sphere normalization from the variational
comparison and performs the final Hilbert-space Hlawka transfer.
-/


open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

open HlawkaSchatten

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









theorem schattenPNorm_nonneg (p : ℝ) (T : E →ₗ[𝕜] F) :
    0 ≤ schattenPNorm p T :=
  Real.rpow_nonneg (singularValuePowerSum_nonneg p T) _

















end HlawkaSchatten

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

namespace HlawkaSchatten

open scoped InnerProductSpace ComplexConjugate







variable {𝕜 H ι : Type*} [RCLike 𝕜] [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]









/-- Equation (7)'s minimization step in its exact abstract form.  A Mazur
sphere equivalence, attained variational representations, and a pointwise
Bregman--distance comparison imply the factors `2*m` and `2*M` between the
two gap values. -/
theorem variationalGap_two_sided_of_mazurEquiv
    {P Q : Type*} (mazur : P ≃ Q) (beta : P → ℝ) (distanceSq : Q → ℝ)
    (deltaP delta₂ m M : ℝ) (hm : 0 ≤ m)
    (hbeta : IsGlobalMinimumValue beta deltaP)
    (hdistance : IsGlobalMinimumValue distanceSq (2 * delta₂))
    (hcompare : ∀ u,
      m * distanceSq (mazur u) ≤ beta u ∧
        beta u ≤ M * distanceSq (mazur u)) :
    2 * m * delta₂ ≤ deltaP ∧ deltaP ≤ 2 * M * delta₂ := by
  have h := globalMinimumValue_two_sided_of_equiv mazur beta distanceSq
    deltaP (2 * delta₂) m M hm hbeta hdistance hcompare
  constructor
  · calc
      2 * m * delta₂ = m * (2 * delta₂) := by ring
      _ ≤ deltaP := h.1
  · calc
      deltaP ≤ M * (2 * delta₂) := h.2
      _ = 2 * M * delta₂ := by ring

section RectangularMazur

variable {E F κ : Type*} [Fintype κ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

























/-- Once Schatten duality supplies the Bregman variational representation,
the already-proved spectral comparison and Hilbert minimum give equation (7)
for the actual rectangular objectives.  Thus `hbeta` is the sole remaining
analytic input at this interface. -/
theorem rectangularVariationalGap_two_sided_of_bregmanRepresentation
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p m M : ℝ} (hp : 0 < p) (hm : 0 ≤ m)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (deltaP : ℝ)
    (hbeta : IsGlobalMinimumValue
      (rectangularBregmanObjective p a u) deltaP)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u)) ≤ deltaP ∧
      deltaP ≤ 2 * M * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u)) := by
  apply variationalGap_two_sided_of_mazurEquiv
    (Equiv.refl (schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p))
    (rectangularBregmanObjective p a u)
    (rectangularMazurDistanceObjective p a u)
    deltaP
    (∑ i, a i - schattenPNorm 2 (rectangularMazurBarycenter p a u))
    m M hm hbeta
    (rectangularMazurDistanceObjective_isGlobalMinimumValue e hp a u)
  intro v
  simpa using rectangularBregmanObjective_two_sided p m M a ha u v hbound

/-- Equation (7) for a finite family of rectangular Schatten-`p` unit
operators.  Both variational representations, the Mazur sphere equivalence,
and the spectral comparison have now been instantiated. -/
theorem rectangularVariationalGap_two_sided
    (e : OrthonormalBasis κ ℂ E) [Nonempty ι]
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * (∑ i, a i - schattenPNorm 2
        (rectangularMazurBarycenter p a u)) ≤
        (∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u) ∧
      (∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u) ≤
        2 * M * (∑ i, a i - schattenPNorm 2
          (rectangularMazurBarycenter p a u)) := by
  exact rectangularVariationalGap_two_sided_of_bregmanRepresentation
    e (zero_lt_one.trans hp) hm a ha u
    ((∑ i, a i) - schattenPNorm p (rectangularWeightedSum a u))
    (rectangularBregmanObjective_isGlobalMinimumValue (E := E) (F := F) hp a u) hbound



end RectangularMazur

end HlawkaSchatten

theorem schattenPNorm_smul_normalized {p : ℝ} (_hp : 0 < p)
    {T : E →ₗ[ℂ] F} (hT : T ≠ 0) :
    ((schattenPNorm p T : ℝ) : ℂ) • schattenNormalized p T = T := by
  unfold schattenNormalized
  rw [smul_smul]
  have hr : 0 < schattenPNorm p T := schattenPNorm_pos p hT
  simp [hr.ne']

theorem solution
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {p m M : ℝ} (hp : 1 < p) (hm : 0 ≤ m)
    (x : ι → E →ₗ[ℂ] F) (hx : ∀ i, x i ≠ 0)
    (hbound : ∀ S T : E →ₗ[ℂ] F,
      m * dilatedMazurDistanceSq p S T ≤ dilatedBregmanTrace p S T ∧
        dilatedBregmanTrace p S T ≤ M * dilatedMazurDistanceSq p S T) :
    2 * m * ((∑ i, schattenPNorm p (x i)) - schattenPNorm 2
        (∑ i, radialRectangularMazurMap p (x i))) ≤
        (∑ i, schattenPNorm p (x i)) - schattenPNorm p (∑ i, x i) ∧
      (∑ i, schattenPNorm p (x i)) - schattenPNorm p (∑ i, x i) ≤
        2 * M * ((∑ i, schattenPNorm p (x i)) - schattenPNorm 2
          (∑ i, radialRectangularMazurMap p (x i))) := by
  let a : ι → ℝ := fun i => schattenPNorm p (x i)
  let u : ι → schattenPowerSphere (𝕜 := ℂ) (E := E) (F := F) p :=
    fun i => schattenPowerDirection (zero_lt_one.trans hp) (x i) (hx i)
  have ha : ∀ i, 0 ≤ a i := fun i => schattenPNorm_nonneg p (x i)
  have hweighted : rectangularWeightedSum a u = ∑ i, x i := by
    unfold rectangularWeightedSum
    apply Finset.sum_congr rfl
    intro i _
    exact schattenPNorm_smul_normalized (zero_lt_one.trans hp) (hx i)
  have hbarycenter : rectangularMazurBarycenter p a u =
      ∑ i, radialRectangularMazurMap p (x i) := by
    unfold rectangularMazurBarycenter radialRectangularMazurMap
    rfl
  have h := rectangularVariationalGap_two_sided
    (stdOrthonormalBasis ℂ E) hp hm a ha u hbound
  rw [hweighted, hbarycenter] at h
  exact h
