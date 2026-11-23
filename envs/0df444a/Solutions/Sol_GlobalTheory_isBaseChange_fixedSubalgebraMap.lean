-- Prove2me | solution 1 for GlobalTheory.isBaseChange_fixedSubalgebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:47.902165+00:00
-- url     : https://prove2.me/submissions/3086c1c1-a3cd-4afa-baf8-39a53251a181

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isBaseChange_of_forall_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable {R S A A' : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing A']
  [Algebra R S] [Algebra R A] [Algebra R A'] [Algebra S A'] [IsScalarTower R S A']
  [MulSemiringAction G A] [SMulCommClass G R A] [MulSemiringAction G A'] [SMulCommClass G S A']
namespace GlobalTheory
theorem _root_.solution [Finite G] [Module.Flat R S] (f : A →ₐ[R] A')
    (hb : IsBaseChange S f.toLinearMap) (hf : ∀ (g : G) a, f (g • a) = g • f a) :
    IsBaseChange S (fixedSubalgebraMap G S f hf).toLinearMap :=
  isBaseChange_of_forall_eq S (ι := G) (fun g ↦ (MulSemiringAction.toAlgHom R A g).toLinearMap)
    (fun _ ↦ .id) (fun g ↦ (MulSemiringAction.toAlgHom S A' g).toLinearMap) (fun _ ↦ .id)
    f.toLinearMap hb (fun _ ↦ f.toLinearMap) (fun _ ↦ hb) hf (fun _ _ ↦ rfl)
    (FixedPoints.subalgebra R A G).val.toLinearMap Subtype.val_injective
    (fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩)
    (FixedPoints.subalgebra S A' G).val.toLinearMap Subtype.val_injective
    (fun x ↦ ⟨by rintro ⟨y, rfl⟩; exact y.2, fun h ↦ ⟨⟨x, h⟩, rfl⟩⟩) _ (fun _ ↦ rfl)
end GlobalTheory
