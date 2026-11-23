-- Prove2me | solution 1 for GlobalTheory.CMTransference.trace_eq_two_mul_sum_re
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:22.51334+00:00
-- url     : https://prove2.me/submissions/1a58a7c4-a549-454e-a613-b7e119e0e913

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CoveringRadiusStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_BabaiCovering
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ConjugateConjugate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_CmApproximationTransference
import Theorems.Thm_GlobalTheory_CMTransference_sumElim_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CMTransference
open NumberField Matrix Module Submodule ReciprocityTheory.MultiplicativeHeights ComplexConjugate
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {σ : ι → K →+* ℂ}
namespace GlobalTheory.CMTransference
theorem _root_.solution (hσ : Function.Injective σ)
    (hcm : ∀ τ : K →+* ℂ, (∃ i, σ i = τ) ↔ ¬ ∃ i, σ i = ComplexEmbedding.conjugate τ) (y : K) :
    (Algebra.trace ℚ K y : ℝ) = 2 * ∑ i, (σ i y).re := by
  have h1 := trace_eq_sum_embeddings (K := ℚ) (L := K) (E := ℂ) (x := y)
  have h2 : ∑ σ : K →ₐ[ℚ] ℂ, σ y = ∑ φ : K →+* ℂ, φ y :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ => φ y) (fun σ => σ y)
      (fun φ => by simp [RingHom.equivRatAlgHom_apply])).symm
  rw [h2, ← (sumElim_bijective hσ hcm).sum_comp (fun φ : K →+* ℂ => φ y),
    Fintype.sum_sum_type] at h1
  have h := congrArg Complex.re h1
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq, Complex.add_re,
    Complex.re_sum, Complex.conj_re] at h
  rw [two_mul, ← h]
  simp
end GlobalTheory.CMTransference
