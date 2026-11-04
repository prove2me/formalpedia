-- Prove2me | solution 1 for OAI.KadisonSimilarity.automorphism_alternatingProduct
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-03T17:21:18.677889+00:00
-- url     : https://prove2.me/submissions/c1ed12ba-cc07-4480-a331-906658e9ed1d

import Mathlib
import Definitions.Def_OAIQ075A004

section
-- module Solutions.OAIQ075_KS.KadisonSimilarity_FreeProduct_TracialAutomorphismWords
attribute [-instance] _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The matrix-unitary word formula is derived from the algebraic product
formula and the actual implementation of a trace-preserving automorphism. -/

noncomputable section
namespace KadisonSimilarity

attribute [local irreducible] tensorWordSpace

variable {P H : Type*} [CStarAlgebra P]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A star-algebra automorphism transports a finite alternating product letterwise. -/
theorem automorphism_alternatingProduct_oai (θ : P ≃⋆ₐ[ℂ] P) {n : ℕ}
    (a c : Fin n → P) :
    θ (alternatingProduct a c) =
      alternatingProduct (fun i => θ (a i)) (fun i => θ (c i)) := by
  simp only [alternatingProduct, map_list_prod, List.map_ofFn, Function.comp_def, map_mul]

end KadisonSimilarity

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KadisonSimilarity.automorphism_alternatingProduct_oai.{u_1} := @OAI.KadisonSimilarity.automorphism_alternatingProduct_oai.{u_1}
