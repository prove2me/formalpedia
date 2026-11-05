-- Prove2me | solution 1 for Grothendieck.grothendieckExpectation_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T08:27:05.126406+00:00
-- url     : https://prove2.me/submissions/c6372012-8bca-4948-a920-f0587362e641

import Mathlib
import Definitions.Def_Grothendieck_Gaussian
import Definitions.Def_Grothendieck_Reduced
import Theorems.Thm_Grothendieck_grothendieckExpectation_eq_reduced

/-!
# Target 2: `grothendieckExpectation r n u u = 1` for a unit vector `u`

`grothendieckExpectation r n u v` is `E[⟪Zu/‖Zu‖, Zv/‖Zv‖]` for an `r × n` standard Gaussian
matrix `Z` (Definition `Grothendieck.grothendieckExpectation`).  The degenerate correlation
`⟪u, v⟫ = 1`, i.e. `v = u` for unit vectors, is the last open case of Lemma 2.1.

Strategy (the "third route" of the problem, pushed one step further).  The published reduction
`Grothendieck.grothendieckExpectation_congr_inner` says that the expectation only depends on
`⟪u, v⟫`.  Since `⟪u, u⟫ = ‖u‖ ^ 2 = 1`, the case `v = u` may be evaluated at *any* unit
vector in *any* dimension; we take the single unit vector `unitE1 ∈ ℝ¹`.  For `n = 1` the vector
`Zu` is just the first column of `Z`, and the integrand reduces to `⟪ŷ, ŷ⟫ = ‖ŷ‖ ^ 2`, which
is `1` as soon as `y ≠ 0` (and `0` at `y = 0`, since Lean's `‖0‖⁻¹ = 0`).  So it remains only
that `Z ≠ 0` almost surely for the `r`-dimensional standard Gaussian law — which holds because
the law is a finite product of non-atomic laws (`NullSingletonClass`) and `r ≥ 1`.

Nothing here needs the a.e. nonvanishing of `Zu` for a general unit vector `u`, so this is
disjoint from the direct proof of Target 1.
-/

set_option linter.style.haveILetI false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real RealInnerProductSpace NNReal

namespace Grothendieck

/-! ### The reduction to a scalar: the expectation depends only on `⟪u, v⟫` -/

lemma equiv_apply_eq_ofLp {m : Type*} [Fintype m] (x : EuclideanSpace ℝ m) (i : m) :
    (EuclideanSpace.equiv m ℝ) x i = x.ofLp i := by
  rw [EuclideanSpace.equiv, PiLp.continuousLinearEquiv_apply]

/-- **Rotation invariance of the expectation**: `grothendieckExpectation r n u v` depends only
on `⟪u, v⟫` (and not on the dimension `n` or on the individual vectors). -/
theorem grothendieckExpectation_congr_inner {r : ℕ} {n m : ℕ} (u v : EuclideanSpace ℝ (Fin n))
    (u' v' : EuclideanSpace ℝ (Fin m)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hu' : ‖u'‖ = 1)
    (hv' : ‖v'‖ = 1) (h : inner ℝ u v = inner ℝ u' v') :
    grothendieckExpectation r n u v = grothendieckExpectation r m u' v' := by
  rw [grothendieckExpectation_eq_reduced u v hu hv,
    grothendieckExpectation_eq_reduced u' v' hu' hv', h]

/-! ### The single-entry unit vector of `ℝ¹` -/

/-- The unit vector `e₁ = (1)` of `ℝ¹`. -/
def unitE1 : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 fun _ : Fin 1 => (1 : ℝ)

@[simp] lemma unitE1_ofLp (i : Fin 1) : unitE1.ofLp i = 1 := rfl

lemma norm_unitE1 : ‖unitE1‖ = 1 := by
  have h : ‖unitE1‖ ^ 2 = 1 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [unitE1]
  nlinarith [norm_nonneg unitE1]

lemma inner_unitE1_self : inner ℝ unitE1 unitE1 = 1 := by
  rw [real_inner_self_eq_norm_sq, norm_unitE1, one_pow]

/-! ### The integrand at coincident arguments -/

/-- `⟪ŷ, ŷ⟫ = 1` for a nonzero vector `y`: the normalized vector has norm one. -/
lemma inner_normalize_self {r : ℕ} {x : EuclideanSpace ℝ (Fin r)} (hx : x ≠ 0) :
    inner ℝ (normalize r x) (normalize r x) = 1 := by
  rw [real_inner_self_eq_norm_sq]
  show ‖(‖x‖)⁻¹ • x‖ ^ 2 = 1
  have hnorm : ‖(‖x‖)⁻¹ • x‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hx
  rw [hnorm, one_pow]

/-! ### `Zu` in the one-dimensional case `n = 1` -/

lemma equiv_unitE1 :
    (EuclideanSpace.equiv (Fin 1) ℝ) unitE1 = fun _ : Fin 1 => (1 : ℝ) := by
  funext i
  rw [equiv_apply_eq_ofLp]
  exact unitE1_ofLp i

/-- For `n = 1` and `u = e₁`, `Zu` is the first column of `Z`, read as a vector of `ℝ^r`. -/
lemma mulVecE_unitE1 {r : ℕ} (Z : Fin r → Fin 1 → ℝ) :
    mulVecE r 1 Z unitE1 = (EuclideanSpace.equiv (Fin r) ℝ).symm (fun i => Z i 0) := by
  simp only [mulVecE]
  rw [equiv_unitE1]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct]

/-! ### The Gaussian matrix is almost surely nonzero -/

/-- The standard Gaussian law on `r` independent coordinates has no atoms, so it is almost
surely different from the origin. -/
lemma ae_gaussianMatrix_ne_zero (r : ℕ) (hr : 1 ≤ r) :
    ∀ᵐ Z ∂(gaussianMatrix r 1), Z ≠ 0 := by
  haveI hneR : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  haveI hne1 : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  haveI hgauss : NullSingletonClass (ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num)
  haveI hrow : NullSingletonClass
      (Measure.pi fun _ : Fin 1 => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
    infer_instance
  haveI hmat : NullSingletonClass
      (Measure.pi fun _ : Fin r =>
        Measure.pi fun _ : Fin 1 => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) := by
    infer_instance
  show ∀ᵐ Z ∂(Measure.pi fun _ : Fin r =>
      Measure.pi fun _ : Fin 1 => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)), Z ≠ 0
  exact Measure.ae_ne _ 0

/-- For a nonzero matrix, the first column does not vanish. -/
lemma column_zero_ne_zero {r : ℕ} {Z : Fin r → Fin 1 → ℝ} (hZ : Z ≠ 0) :
    (fun i => Z i 0) ≠ 0 := by
  intro h
  apply hZ
  funext i j
  fin_cases j
  simpa using congrFun h i

/-! ### The `n = 1` case -/

/-- The degenerate case at the single unit vector of `ℝ¹`: the integrand is `1` almost surely. -/
theorem grothendieckExpectation_unitE1_self (r : ℕ) (hr : 1 ≤ r) :
    grothendieckExpectation r 1 unitE1 unitE1 = 1 := by
  haveI hneR : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
  haveI hprob : IsProbabilityMeasure (gaussianMatrix r 1) := by
    show IsProbabilityMeasure (Measure.pi fun _ : Fin r =>
      Measure.pi fun _ : Fin 1 => ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal))
    infer_instance
  -- `Zu ≠ 0` almost surely
  have hzero : ∀ᵐ Z ∂(gaussianMatrix r 1), mulVecE r 1 Z unitE1 ≠ 0 := by
    filter_upwards [ae_gaussianMatrix_ne_zero r hr] with Z hZ hmv
    refine column_zero_ne_zero hZ ?_
    have h2 := congrArg (EuclideanSpace.equiv (Fin r) ℝ) hmv
    simpa [mulVecE_unitE1] using h2
  -- hence the integrand is identically `1` almost surely
  have hcongr : ∀ᵐ Z ∂(gaussianMatrix r 1),
      inner ℝ (normalize r (mulVecE r 1 Z unitE1)) (normalize r (mulVecE r 1 Z unitE1))
        = 1 := by
    filter_upwards [hzero] with Z hZ
    exact inner_normalize_self hZ
  unfold grothendieckExpectation
  rw [integral_congr_ae hcongr]
  simp [integral_const]

/-! ### Target 2 -/

/-- **Lemma 2.1 in the degenerate case `⟪u, v⟫ = 1`**: at coincident unit vectors the
normalized Gaussian vectors have inner product `1` almost surely, so the expectation is `1`. -/
theorem grothendieckExpectation_self {r n : ℕ} (hr : 1 ≤ r)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    grothendieckExpectation r n u u = 1 := by
  have hu2 : inner ℝ u u = 1 := by
    have h := real_inner_self_eq_norm_sq u
    rw [hu] at h
    simpa using h
  calc grothendieckExpectation r n u u
      = grothendieckExpectation r 1 unitE1 unitE1 := by
        refine grothendieckExpectation_congr_inner u u unitE1 unitE1 hu hu norm_unitE1
          norm_unitE1 ?_
        rw [hu2, inner_unitE1_self]
    _ = 1 := grothendieckExpectation_unitE1_self r hr

end Grothendieck

open Grothendieck in
theorem solution {r n : ℕ} (hr : 1 ≤ r) (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) :
    grothendieckExpectation r n u u = 1 :=
  grothendieckExpectation_self hr u hu
