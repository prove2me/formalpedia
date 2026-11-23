-- Prove2me | solution 1 for GlobalTheory.Published.exists_basis_one_imaginary
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:24.512797+00:00
-- url     : https://prove2.me/submissions/ed3d1f0d-05fa-4a02-b24d-fb1cb3070751

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.Published
theorem _root_.solution {θ : E} (h0 : θ ≠ 0) (hθ : cc θ = -θ) :
    ∃ b : Module.Basis (Fin 2) (maximalRealSubfield E) E, b 0 = 1 ∧ b 1 = θ := by
  have hli : LinearIndependent (maximalRealSubfield E) ![(1 : E), θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : (s : E) + (t : E) * θ = 0 := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      exact hst
    have h2 : (s : E) - (t : E) * θ = 0 := by
      have := congrArg (IsCMField.complexConj E) h1
      rw [map_add, map_mul, IsCMField.complexConj_apply_eq_self,
        IsCMField.complexConj_apply_eq_self, map_zero,
        show IsCMField.complexConj E θ = -θ from hθ] at this
      linear_combination this
    have hs : (s : E) = 0 := by linear_combination (h1 + h2) / 2
    have ht : (t : E) * θ = 0 := by linear_combination h1 - hs
    exact ⟨by exact_mod_cast hs, by exact_mod_cast (mul_eq_zero.mp ht).resolve_right h0⟩
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hli
    (by rw [Algebra.IsQuadraticExtension.finrank_eq_two]; simp), ?_, ?_⟩ <;> simp
end GlobalTheory.Published
