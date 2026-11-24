-- Prove2me | solution 1 for GlobalTheory.RegSS.continuous_rTensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:55:14.539176+00:00
-- url     : https://prove2.me/submissions/de4df15f-38f8-4642-8470-e1e46da3e850

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix Formalism.UG NumberField GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct
open GlobalTheory GlobalTheory.RegSS
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
open Matrix NumberField
open scoped TensorProduct
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {σ : E →ₐ[F] E}
namespace GlobalTheory.RegSS
namespace _root_.GlobalTheory.RegSS
theorem _root_.solution {B B' : Type} [CommRing B] [Algebra F B]
    [CommRing B'] [Algebra F B'] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    (f : B →ₗ[F] B') :
    @Continuous _ _ (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := B) R) (_root_.Formalism.BasicNotions.tensTopL (F := F) (E := B') R)
      (LinearMap.rTensor R f) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := B) (B := R)
  letI := Algebra.TensorProduct.rightAlgebra (R := F) (A := B') (B := R)
  letI : TopologicalSpace (B ⊗[F] R) := moduleTopology R (B ⊗[F] R)
  letI : TopologicalSpace (B' ⊗[F] R) := moduleTopology R (B' ⊗[F] R)
  haveI : IsModuleTopology R (B ⊗[F] R) := ⟨rfl⟩
  haveI : IsModuleTopology R (B' ⊗[F] R) := ⟨rfl⟩
  haveI : ContinuousAdd (B' ⊗[F] R) := IsModuleTopology.toContinuousAdd R _
  haveI : ContinuousSMul R (B' ⊗[F] R) := IsModuleTopology.toContinuousSMul R _
  let g : B ⊗[F] R →ₗ[R] B' ⊗[F] R :=
    { toFun := LinearMap.rTensor R f
      map_add' := map_add _
      map_smul' := by
        intro r x
        simp only [Algebra.smul_def, RingHom.id_apply]
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul b s =>
          show LinearMap.rTensor R f (((1 : B) ⊗ₜ[F] r) * b ⊗ₜ[F] s) =
            ((1 : B') ⊗ₜ[F] r) * f b ⊗ₜ[F] s
          simp
        | add x y hx hy => simp only [mul_add, map_add, hx, hy] }
  exact IsModuleTopology.continuous_of_linearMap g
end _root_.GlobalTheory.RegSS
end GlobalTheory.RegSS
