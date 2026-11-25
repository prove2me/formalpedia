-- Prove2me | solution 1 for GlobalTheory.Inertia.negIndex_map_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:57:25.076861+00:00
-- url     : https://prove2.me/submissions/1eaaab33-b6c3-44dc-9673-951d46754f80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_negIndex_map_conj
import Theorems.Thm_GlobalTheory_Inertia_isHermitian_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution (τ : E →+* ℂ) {G : Matrix n n E}
    (hG : ∀ a b, FD.cc (G a b) = G b a) :
    negIndex (G.map (ComplexEmbedding.conjugate τ)) = negIndex (G.map τ) :=
  negIndex_map_conj (isHermitian_map τ hG)
end GlobalTheory.Inertia
