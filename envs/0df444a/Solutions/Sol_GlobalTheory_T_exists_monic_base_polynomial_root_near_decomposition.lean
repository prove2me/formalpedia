-- Prove2me | solution 1 for GlobalTheory.T.exists_monic_base_polynomial_root_near_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:00:01.076449+00:00
-- url     : https://prove2.me/submissions/a4ffaf47-f4d5-406c-9823-cb9b94eed1ec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicBasePolynomialRootNearDecomposition
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMonicBasePolynomialRootNearDecompositionStatement
import Theorems.Thm_GlobalTheory_WeilDeligne_exists_monic_base_root_near


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω), (∀ z : Ω, (∀ d ∈ Dec (F := E) A, d z = z) → ∀ r : Ω, r ≠ 0 → ∃ e : E, A.valuation (algebraMap E Ω e - z) < A.valuation r) → ∀ f : Polynomial Ω, f.Monic → (∀ d ∈ Dec (F := E) A, ∀ i, d (f.coeff i) = f.coeff i) → ∀ β : Ω, f.eval β = 0 → ∀ r : Ω, r ≠ 0 → ∃ g : Polynomial E, g.Monic ∧ g.natDegree = f.natDegree ∧ ∃ β' : Ω, aeval β' g = 0 ∧ A.valuation (β' - β) < A.valuation r := by
  first | exact @GlobalTheory.WeilDeligne.exists_monic_base_root_near | exact GlobalTheory.WeilDeligne.exists_monic_base_root_near | (intros; apply GlobalTheory.WeilDeligne.exists_monic_base_root_near <;> assumption)
end _root_.GlobalTheory.T
