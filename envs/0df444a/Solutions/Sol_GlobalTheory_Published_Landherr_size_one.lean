-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.size_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:58.265193+00:00
-- url     : https://prove2.me/submissions/82d2733e-71e3-46bb-b815-df819b53361c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_cc_ne_zero

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
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (G G' : Matrix (Fin 1) (Fin 1) E) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0)
    (h : ∃ x : E, G.det / G'.det = x * cc x) :
    ∃ P : Matrix (Fin 1) (Fin 1) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc := by
  obtain ⟨x, hx⟩ := h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact div_ne_zero hd hd' (by simpa using hx)
  have hc := cc_ne_zero hx0
  have h1 : cc x⁻¹ = (cc x)⁻¹ := by simp [cc]
  rw [Matrix.det_fin_one] at hd hd'
  rw [Matrix.det_fin_one, Matrix.det_fin_one, div_eq_iff hd'] at hx
  refine ⟨!![x⁻¹], by simpa using hx0, ?_⟩
  ext a b
  fin_cases a; fin_cases b
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.transpose_apply, Matrix.map_apply,
    Fin.zero_eta, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one, h1, hx]
  field_simp
end GlobalTheory.Published.Landherr
