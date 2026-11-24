-- Prove2me | solution 1 for GlobalTheory.Inertia.map_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:59:31.932212+00:00
-- url     : https://prove2.me/submissions/50a216b0-8f1c-42a7-b5c5-2b3a11a7d19f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_embedding_cc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]
omit [DecidableEq n]
namespace GlobalTheory.Inertia
theorem _root_.solution {m : Type*} (τ : E →+* ℂ) (G : Matrix n n E) (P : Matrix n m E) :
    (Pᵀ * G * P.map FD.cc).map τ = (P.map τ)ᵀ * G.map τ * (P.map τ).map conj := by
  have h : (P.map FD.cc).map τ = (P.map τ).map conj := by
    ext a b
    exact embedding_cc τ _
  rw [Matrix.map_mul, Matrix.map_mul, transpose_map, h]
end GlobalTheory.Inertia
