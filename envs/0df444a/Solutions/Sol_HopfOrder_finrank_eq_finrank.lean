-- Prove2me | solution 1 for HopfOrder.finrank_eq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/b7c74871-c333-53ba-a25b-ac689a8cb47f

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfOrder_finrank_eq_finrank

open scoped TensorProduct

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤) :
    Module.finrank R ↥S = Module.finrank K A := by
  classical
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K

  haveI hRA : Module.IsTorsionFree R A :=
    Module.IsTorsionFree.comap (algebraMap R K)
      (fun r hr => IsRegular.of_ne_zero (fun h0 =>
        hr.ne_zero (hinj (by rw [h0, map_zero]))))
      (fun r m => algebraMap_smul K r m)
  haveI hRS : Module.IsTorsionFree R ↥S :=
    Function.Injective.moduleIsTorsionFree (fun x : ↥S => (x : A)) Subtype.val_injective
      (fun _ _ => rfl)
  haveI : Module.Finite R ↥S := hfin
  haveI : Module.Free R ↥S := inferInstance

  let b := Module.Free.chooseBasis R ↥S
  let v : Module.Free.ChooseBasisIndex R ↥S → A := fun i => (b i : A)
  have hvR : LinearIndependent R v :=
    b.linearIndependent.map' (S.val.toLinearMap) (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hvK : LinearIndependent K v := (LinearIndependent.iff_fractionRing R K).mp hvR
  have hsp : ⊤ ≤ Submodule.span K (Set.range v) := by
    rw [← hspan, Submodule.span_le]
    intro x hx
    have hxR : x ∈ Submodule.span R (Set.range v) := by
      have hmem : (⟨x, hx⟩ : ↥S) ∈ Submodule.span R (Set.range b) := by
        rw [b.span_eq]; exact Submodule.mem_top
      have himg := Submodule.mem_map_of_mem (f := S.val.toLinearMap) hmem
      rw [Submodule.map_span, ← Set.range_comp] at himg
      exact himg
    exact Submodule.span_le_restrictScalars R K (Set.range v) hxR
  let bK : Module.Basis (Module.Free.ChooseBasisIndex R ↥S) K A := Module.Basis.mk hvK hsp
  rw [Module.finrank_eq_card_chooseBasisIndex, Module.finrank_eq_card_basis bK]

end S_HopfOrder_finrank_eq_finrank
end P2MW
export P2MW.S_HopfOrder_finrank_eq_finrank (solution)
