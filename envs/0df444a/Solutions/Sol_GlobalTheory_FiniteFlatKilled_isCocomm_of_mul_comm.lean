-- Prove2me | solution 1 for GlobalTheory.FiniteFlatKilled.isCocomm_of_mul_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:07:50.730026+00:00
-- url     : https://prove2.me/submissions/ca260f30-bcde-4406-8fb2-8e916bb6ab32

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
import Theorems.Thm_GlobalTheory_FiniteFlatKilled_postcomp_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FiniteFlatKilled.postcomp_apply

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FiniteFlatKilled
theorem _root_.solution {R B : Type*} [CommRing R] [CommRing B] [Bialgebra R B]
    (h : ∀ f g : WithConv (B →ₐ[R] B ⊗[R] B), f * g = g * f) : Coalgebra.IsCocomm R B := by
  let l : WithConv (B →ₐ[R] B ⊗[R] B) := toConv Algebra.TensorProduct.includeLeft
  let r : WithConv (B →ₐ[R] B ⊗[R] B) := toConv Algebra.TensorProduct.includeRight
  have h1 : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map l.ofConv r.ofConv) =
      AlgHom.id R (B ⊗[R] B) := by
    ext <;> simp [l, r, ← Algebra.TensorProduct.one_def]
  have h2 : (Algebra.TensorProduct.lmul' R).comp (Algebra.TensorProduct.map r.ofConv l.ofConv) =
      (Algebra.TensorProduct.comm R B B).toAlgHom := by
    ext <;> simp [l, r, ← Algebra.TensorProduct.one_def]
  have h3 := congrArg ofConv (h r l)
  rw [AlgHom.convMul_def, AlgHom.convMul_def, ofConv_toConv, ofConv_toConv, ← AlgHom.comp_assoc,
    ← AlgHom.comp_assoc, h1, h2] at h3
  exact ⟨LinearMap.ext fun c => congr($h3 c)⟩
end GlobalTheory.FiniteFlatKilled
