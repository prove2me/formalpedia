-- Prove2me | solution 1 for GlobalTheory.FlatIdealInf.mem_map_algebraMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:15:50.332183+00:00
-- url     : https://prove2.me/submissions/2a114be8-de8d-4bed-8096-e4130e126de3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IInfMapLeMapIInfOfFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FlatIdealInf
open TensorProduct
namespace GlobalTheory.FlatIdealInf
theorem _root_.solution {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
    (I : Ideal B) (x : R) :
    x ∈ I.map (algebraMap B R) ↔
      x ⊗ₜ[B] (1 : B) ∈ LinearMap.range (LinearMap.lTensor R (Submodule.subtype (I.restrictScalars B))) := by
  rw [← Ideal.map_includeRight_eq (R := B) (A := R) I, Submodule.restrictScalars_mem]
  let e := (Algebra.TensorProduct.rid B R R).toRingEquiv
  have he : (e : R ⊗[B] B →+* R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[B] R ⊗[B] B) : B →+* R ⊗[B] B) = algebraMap B R := by
    ext b
    simp [e, Algebra.algebraMap_eq_smul_one]
  rw [← he, ← Ideal.map_map, Ideal.map_comap_of_equiv, Ideal.mem_comap]
  rfl
end GlobalTheory.FlatIdealInf
