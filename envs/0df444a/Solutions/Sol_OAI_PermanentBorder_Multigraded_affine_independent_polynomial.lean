-- Prove2me | solution 1 for OAI.PermanentBorder.Multigraded.affine_independent_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T23:32:47.879551+00:00
-- url     : https://prove2.me/submissions/d5914fe0-fe9e-4091-bc25-99657f702b67

-- Generated from openai/math@1581d4c lean/OAI/Algebra/Determinantal/LinearForms.lean:L427-L462
-- (upload_full_project.md Phase 4): solution for node OAI.PermanentBorder.Multigraded.affine_independent_polynomial. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SmoothInitialForm
import Definitions.Def_OAI_Algebra_Determinantal_Multigraded
import Definitions.Def_OAI_Algebra_Determinantal_LinearForms

-- ---- from OAI.Algebra.Determinantal.LinearForms ----
namespace OAI
namespace PermanentBorder.Multigraded
open MvPolynomial
section LinearCoefficients
variable {K σ τ : Type*} [Field K] [Fintype τ]

end LinearCoefficients

section Vandermonde
variable {K : Type*} [Field K]

end Vandermonde
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section VandermondeLeaves
variable {K ι L : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype L]

end VandermondeLeaves
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section BinaryChoices
variable {K σ G : Type*} [Field K] [AddCommGroup G]
variable (w : σ → G)

end BinaryChoices
end PermanentBorder.Multigraded
namespace PermanentBorder.Multigraded
open MvPolynomial
section MixedCoefficient
variable {ι E : Type*} [Fintype E] [DecidableEq ι]

end MixedCoefficient
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section ComparisonPieceBound
variable {K ι σ : Type*} [Field K] [DecidableEq ι]

variable [Fintype ι]

end ComparisonPieceBound
end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
open MvPolynomial
section HomogeneousIdealMap
variable {K σ G E : Type*} [Field K] [AddCommGroup G] [Fintype E]
variable (w : σ → G) (e : E → G) (F : E → MvPolynomial σ K)
  (hF : ∀ i, (F i).IsWeightedHomogeneous w (e i))

end HomogeneousIdealMap

end PermanentBorder.Multigraded

namespace PermanentBorder.Multigraded
section AffineIndependent
variable {K E V : Type*} [Field K] [Fintype E]
  [AddCommGroup V] [Module K V]

theorem affine_independent_polynomial (v w : E → V) (hv : LinearIndependent K v) :
    ∃ p : Polynomial K, p.eval 0 = 1 ∧ ∀ t : K, p.eval t ≠ 0 →
      LinearIndependent K (fun i => (1-t) • v i + t • w i) := by
  classical
  let f := Fintype.linearCombination K v
  obtain ⟨g,hg⟩ := f.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr hv.fintypeLinearCombination_injective)
  have hgv (i : E) : g (v i) = Pi.single i 1 := by
    have h := LinearMap.congr_fun hg (Pi.single i 1)
    simpa [f, Fintype.linearCombination_apply] using h
  let M : Matrix E E (Polynomial K) := fun j i =>
    (1-Polynomial.X) * Polynomial.C (g (v i) j) + Polynomial.X * Polynomial.C (g (w i) j)
  have hM (t : K) : M.map (Polynomial.evalRingHom t) =
      (fun j i => g ((1-t) • v i + t • w i) j) := by
    ext j i
    change (Polynomial.evalRingHom t) (M j i) = _
    simp [M]
    ring
  have hzero : M.map (Polynomial.evalRingHom 0) = 1 := by
    rw [hM]
    ext j i
    by_cases h : j = i
    · subst j; simp [hgv]
    · simp [hgv, h]
  refine ⟨M.det, ?_, ?_⟩
  · change Polynomial.evalRingHom 0 M.det = 1
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hzero, Matrix.det_one]
  · intro t ht
    have hu : IsUnit ((M.map (Polynomial.evalRingHom t)).det) := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact isUnit_iff_ne_zero.mpr ht
    have hi := (Matrix.linearIndependent_cols_iff_isUnit).mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
    apply LinearIndependent.of_comp g
    rw [hM] at hi
    exact hi

end AffineIndependent
end PermanentBorder.Multigraded

end OAI

-- ---- platform node ----
open OAI OAI.PermanentBorder OAI.PermanentBorder.Multigraded


theorem solution : type_of% @_root_.OAI.PermanentBorder.Multigraded.affine_independent_polynomial := @_root_.OAI.PermanentBorder.Multigraded.affine_independent_polynomial
