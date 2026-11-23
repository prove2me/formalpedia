-- Prove2me | solution 1 for GlobalTheory.SmoothForms.SecondKind.exp_unitary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:47:17.45254+00:00
-- url     : https://prove2.me/submissions/35b2fcf0-5fc5-42cf-8b55-471006c6b54a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_SmoothInExponentialCoordsIffFirstSecondKind
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
namespace GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
private theorem isLieData_star_pow (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) (x : 𝔸) (n : ℕ) :
    σ (x ^ n) = σ x ^ n := by
  induction n with
  | zero => simpa using H.one
  | succ n ih => rw [pow_succ, H.anti, ih, ← pow_succ']
open NumberField Matrix in
open scoped ContDiff Topology in
open NormedSpace in
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G} in
private theorem isLieData_star_exp (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) (x : 𝔸) :
    σ (exp x) = exp (σ x) := by
  haveI := FiniteDimensional.complete ℝ 𝔸
  have h1 := (exp_series_hasSum_exp' (𝕂 := ℝ) x).mapL (LinearMap.toContinuousLinearMap σ)
  have h2 := exp_series_hasSum_exp' (𝕂 := ℝ) (σ x)
  have h3 : (fun n : ℕ => LinearMap.toContinuousLinearMap σ (((n.factorial : ℝ))⁻¹ • x ^ n)) =
      fun n => ((n.factorial : ℝ))⁻¹ • σ x ^ n := by
    funext n
    simp [isLieData_star_pow H]
  rw [h3] at h1
  exact h1.unique h2
variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
end GlobalTheory.SmoothForms.SecondKind
end
end

set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix
open scoped ContDiff Topology
noncomputable section
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.SecondKind
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
open NumberField Matrix
open scoped ContDiff Topology
open NormedSpace
variable {𝔸 L G : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [FiniteDimensional ℝ 𝔸] [NormedAddCommGroup L]
  [NormedSpace ℝ L] [Group G] {σ : 𝔸 →ₗ[ℝ] 𝔸} {j : L →ₗ[ℝ] 𝔸} {s : 𝔸 → G}
namespace GlobalTheory.SmoothForms.SecondKind
namespace _root_.GlobalTheory.SmoothForms.SecondKind
theorem _root_.solution (H : _root_.GlobalTheory.SmoothForms.IsLieData σ j s) (X : L) :
    σ (exp (j X)) * exp (j X) = 1 := by
  haveI := FiniteDimensional.complete ℝ 𝔸
  have hX : σ (j X) = -(j X) := (H.skew _).2 ⟨X, rfl⟩
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [isLieData_star_exp H, hX, ← NormedSpace.exp_add_of_commute (Commute.neg_left (Commute.refl _)),
    neg_add_cancel, exp_zero]
end _root_.GlobalTheory.SmoothForms.SecondKind
end GlobalTheory.SmoothForms.SecondKind
