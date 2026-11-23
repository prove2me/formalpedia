-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.re_det_div_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:19.961111+00:00
-- url     : https://prove2.me/submissions/c0e6929e-8276-4593-a000-4b301f6441ce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (hd : G.det ≠ 0) (τ : E →+* ℂ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj) :
    0 < (τ (G.det / G'.det)).re := by
  obtain ⟨Q, hQ, h⟩ := h
  have e : ∀ M : Matrix (Fin r) (Fin r) E, (M.map τ).det = τ M.det :=
    fun M => (RingHom.map_det τ M).symm
  have e' : (Q.map conj).det = conj Q.det := (RingHom.map_det (starRingEnd ℂ) Q).symm
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, e, e, e'] at h2
  have hτ : τ G.det ≠ 0 := (map_ne_zero τ).mpr hd
  have hc : conj Q.det ≠ 0 := (map_ne_zero _).mpr hQ
  have h3 : τ (G.det / G'.det) = (((Complex.normSq Q.det)⁻¹ : ℝ) : ℂ) := by
    rw [map_div₀, h2, Complex.ofReal_inv, ← Complex.mul_conj]
    field_simp
  rw [h3, Complex.ofReal_re]
  exact inv_pos.mpr (Complex.normSq_pos.mpr hQ)
end GlobalTheory.Published.Landherr
