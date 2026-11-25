-- Prove2me | solution 1 for GlobalTheory.Published.HasseNorm.local_of_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:11:54.99544+00:00
-- url     : https://prove2.me/submissions/30d768a4-910e-4bb9-a48e-346a0967677c

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
open GlobalTheory.Published.HasseNorm
namespace GlobalTheory.Published.HasseNorm
theorem _root_.solution {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (A : Type*) [CommRing A] [Algebra K A] {a : K} (h : ∃ x : L, Algebra.norm K x = a) :
    ∃ z : A ⊗[K] L, Algebra.norm A z = algebraMap K A a := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨1 ⊗ₜ x, ?_⟩
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  exact (Algebra.baseChange_lmul x).symm
end GlobalTheory.Published.HasseNorm
