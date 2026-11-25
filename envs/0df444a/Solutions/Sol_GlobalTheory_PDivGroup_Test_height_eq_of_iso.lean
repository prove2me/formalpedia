-- Prove2me | solution 1 for GlobalTheory.PDivGroup.Test.height_eq_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:05:30.828207+00:00
-- url     : https://prove2.me/submissions/279c2f90-fbb3-4fbc-96d5-403aa2f6ca5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PadicActionConstInjective
import Theorems.Thm_GlobalTheory_PDiv_fibreDim_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct Coalgebra Bialgebra WithConv Module CategoryTheory
open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.PDivGroup.Test
open PDiv
variable {p : ℕ} {O : Type} [CommRing O]
namespace GlobalTheory.PDivGroup.Test
theorem _root_.solution [Fact p.Prime] [Nontrivial O] {G H : PDivGroup p O} (e : G ≅ H) :
    G.height = H.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum O) := inferInstance
  have h1 : ∀ a, e.hom.app 1 (e.inv.app 1 a) = a := fun a =>
    DFunLike.congr_fun (congrArg (fun f => Hom.app f 1) e.hom_inv_id) a
  have h2 : ∀ a, e.inv.app 1 (e.hom.app 1 a) = a := fun a =>
    DFunLike.congr_fun (congrArg (fun f => Hom.app f 1) e.inv_hom_id) a
  let l : H.A 1 ≃ₗ[O] G.A 1 :=
    { toFun := e.hom.app 1, map_add' := map_add _, map_smul' := map_smul _,
      invFun := e.inv.app 1, left_inv := h2, right_inv := h1 }
  have h := fibreDim_congr l q
  rw [fibreDim_eq, fibreDim_eq, one_mul, one_mul] at h
  exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
end GlobalTheory.PDivGroup.Test
