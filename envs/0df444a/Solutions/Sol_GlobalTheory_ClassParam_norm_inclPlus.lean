-- Prove2me | solution 1 for GlobalTheory.ClassParam.norm_inclPlus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:27.047561+00:00
-- url     : https://prove2.me/submissions/f7dc210e-7e0f-4f81-ad1f-c45e232dbbbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeftMulMatrixTransfer
import Theorems.Thm_GlobalTheory_ClassParam_norm_transfer
import Theorems.Thm_GlobalTheory_ClassParam_algebraMap_tmul
import Theorems.Thm_GlobalTheory_ClassParam_exists_basis_tensor
import Theorems.Thm_GlobalTheory_ClassParam_exists_pow_basis
import Theorems.Thm_GlobalTheory_ClassParam_exists_basis_plus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial TensorProduct Matrix Formalism.UG
open GlobalTheory GlobalTheory.ClassParam
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
attribute [local instance] algLk
variable {F E : Type} [Field F] [Field E] [Algebra F E] {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
  (k : Type) [Field k] [Algebra F k]
namespace GlobalTheory.ClassParam
theorem _root_.solution [CharZero E] [FiniteDimensional F E] (hP : IsPPol c r P)
    (hc : ∀ e, c (c e) = e) (hc1 : c ≠ 1)
    (hF : ∀ e, c e = e → ∃ a, algebraMap F E a = e) (x : (Lplus hP ⊗[F] k)ˣ) :
    Algebra.norm (E ⊗[F] k) (inclPlus k hP x) = (1 : E) ⊗ₜ[F] (normPlus hP x : k) := by
  classical
  obtain ⟨b₀, -⟩ := exists_pow_basis hP
  haveI := Module.Finite.of_basis b₀
  haveI : Module.Finite F (AdjoinRoot P) := Module.Finite.trans E _
  haveI : Module.Finite F (Lplus hP) :=
    Module.Finite.of_injective (Lplus hP).val.toLinearMap Subtype.val_injective
  let b := Module.finBasis F (Lplus hP)
  obtain ⟨b1, hb1⟩ := exists_basis_plus hP hc hc1 hF b
  obtain ⟨b2, hb2⟩ := exists_basis_tensor (F := F) k b1
  have := norm_transfer (Algebra.TensorProduct.includeRight : k →ₐ[F] E ⊗[F] k).toRingHom
    ((inclPlus k hP).comp (Algebra.TensorProduct.comm F k (Lplus hP)).toAlgHom.toRingHom)
    (fun a => by simp [inclPlus, algebraMap_tmul]) (Algebra.TensorProduct.basis k b) b2
    (fun i => by simp [inclPlus, hb2, hb1])
    (Algebra.TensorProduct.comm F (Lplus hP) k x)
  refine Eq.trans ?_ this
  congr 1
  show _ = inclPlus k hP ((Algebra.TensorProduct.comm F (Lplus hP) k).symm _)
  rw [AlgEquiv.symm_apply_apply]
end GlobalTheory.ClassParam
