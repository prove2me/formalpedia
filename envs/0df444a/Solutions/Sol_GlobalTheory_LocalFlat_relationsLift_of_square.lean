-- Prove2me | solution 1 for GlobalTheory.LocalFlat.relationsLift_of_square
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:44.532588+00:00
-- url     : https://prove2.me/submissions/18073451-5328-494a-a06f-efb4df77bd03

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_LocalFlat_relationsLift_of_flat
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open GlobalTheory.LocalFlat
variable {A : Type u} [CommRing A]
variable {M : Type w} [AddCommGroup M] [Module A M]
namespace GlobalTheory.LocalFlat
theorem _root_.solution {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] {I : Ideal A} (p : A →+* C) (q : B →+* D) (ψ : C →+* D)
    (hp : Function.Surjective p) (hq : Function.Surjective q) (hpI : RingHom.ker p = I)
    (hqI : RingHom.ker q = I.map (algebraMap A B)) (hsq : ψ.comp p = q.comp (algebraMap A B))
    (hψ : ψ.Flat) : RelationsLift I B := by
  letI := p.toAlgebra
  letI := ψ.toAlgebra
  letI := (q.comp (algebraMap A B)).toAlgebra
  haveI : IsScalarTower A C D := IsScalarTower.of_algebraMap_eq' hsq.symm
  haveI : Module.Flat C D := hψ
  let q' : B →ₐ[A] D := { q with commutes' := fun _ => rfl }
  refine relationsLift_of_flat (C := C) hp hpI q'.toLinearMap hq ?_
  rw [Ideal.smul_top_eq_map, ← hqI]
  rfl
end GlobalTheory.LocalFlat
