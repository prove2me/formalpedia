-- Prove2me | solution 2 for OAI.Cotype.complexProjectionPolynomial_spectral
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T21:53:42.791623+00:00
-- url     : https://prove2.me/submissions/c7a9796d-244e-4b0f-b5ca-f6a68f81b699

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ComplexProjectionSpectrum.lean:L88-L104
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.complexProjectionPolynomial_spectral. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum

-- ---- from OAI.Analysis.Cotype.ComplexProjectionPolynomial ----
namespace OAI

noncomputable section
namespace Cotype

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem complexProjectionProduct_lift {m : ℕ} (P : Fin m → Y →L[ℝ] Y) :
    complexProjectionProduct (fun i => complexDualLift (P i)) =
      complexDualLift (projectionProduct P) := by
  induction m with
  | zero => simp [complexProjectionProduct, projectionProduct]
  | succ m ih => simp [complexProjectionProduct, projectionProduct, ih]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ComplexProjectionSpectrum ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]

theorem complexProjectionProduct_weighted_sum {Ω : Type*} [Fintype Ω] {n : ℕ}
    (w : Fin n → Ω → ℂ) (P : Fin n → Ω → Z →L[ℂ] Z) :
    complexProjectionProduct (fun i => ∑ a, w i a • P i a) =
      ∑ ω : Fin n → Ω, (∏ i, w i (ω i)) • complexProjectionProduct (fun i => P i (ω i)) := by
  classical
  induction n with
  | zero => simp [complexProjectionProduct]
  | succ n ih =>
    rw [← (projectionChoiceCons Ω n).sum_comp]
    simp only [Fintype.sum_prod_type, projectionChoiceCons, Equiv.coe_fn_mk,
      Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, complexProjectionProduct]
    rw [ih]
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
      Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro ω _
    rw [mul_comm]

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem projectionPattern_weight {m : ℕ} (ε : Cube m) (z : ℂ) :
    (∏ i, if ε i then z else 1) = z^(projectionDegree ε) := by
  classical
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const, projectionDegree]

theorem complexProjectionPolynomial_spectral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (z : ℂ) :
    complexProjectionPolynomial P z = complexSpectralEval P (fun ε => z^(projectionDegree ε)) := by
  have h := complexProjectionProduct_weighted_sum
    (fun (_ : Fin m) (b : Bool) => if b then z else 1)
    (fun i (b : Bool) => complexDualLift (if b then 1-P i else P i))
  simp only [Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true, one_smul,
    complexDualLift_sub, complexDualLift_one] at h
  unfold complexProjectionPolynomial complexSpectralEval
  calc
    _ = ∑ ε : Cube m, (∏ i, if ε i then z else 1) •
        complexProjectionProduct (fun i => complexDualLift (if ε i then 1-P i else P i)) := by
      simpa only [add_comm] using h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro ε _
      rw [projectionPattern_weight, complexProjectionProduct_lift]
      rfl

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.complexProjectionPolynomial_spectral := @_root_.OAI.Cotype.complexProjectionPolynomial_spectral
