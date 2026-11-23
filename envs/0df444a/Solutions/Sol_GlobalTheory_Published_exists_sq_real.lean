-- Prove2me | solution 1 for GlobalTheory.Published.exists_sq_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:25.862692+00:00
-- url     : https://prove2.me/submissions/2546bf22-5597-488c-b594-fa510ba50b1b

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
theorem _root_.solution {θ : E} (hθ : cc θ = -θ) :
    ∃ d : maximalRealSubfield E, (d : E) = θ * θ :=
  ⟨⟨θ * θ, (IsCMField.complexConj_eq_self_iff E _).mp (by
    rw [map_mul, show IsCMField.complexConj E θ = -θ from hθ]; ring)⟩, rfl⟩
end GlobalTheory.Published
