-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.size_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:59.038882+00:00
-- url     : https://prove2.me/submissions/232c8cdb-325f-452a-8cb2-ea394b598db6

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
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (G G' : Matrix (Fin 0) (Fin 0) E) :
    ∃ P : Matrix (Fin 0) (Fin 0) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc :=
  ⟨1, by simp, Subsingleton.elim _ _⟩
end GlobalTheory.Published.Landherr
