-- Prove2me | solution 1 for NumberField.InfiniteAdeleRing.exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/f0dee16f-6176-5e53-85fc-d4f9f8c0e6b8

import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre

set_option autoImplicit false

open NumberField

set_option linter.unusedSectionVars false

noncomputable section

namespace ArchRegroup

open NumberField

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

abbrev below (w : InfinitePlace L) : InfinitePlace K := w.comap (algebraMap K L)

abbrev asExt (w : InfinitePlace L) : (below K L w).Extension L := ⟨w, rfl⟩

def invVal (x : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) : InfiniteAdeleRing L :=
  fun w => ((x (below K L w) : (∀ w' : (below K L w).Extension L, w'.1.Completion)) (asExt K L w))

def invInv (x : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) : InfiniteAdeleRing L :=
  fun w => (((x (below K L w))⁻¹ : (∀ w' : (below K L w).Extension L, w'.1.Completion)ˣ) :
    (∀ w' : (below K L w).Extension L, w'.1.Completion)) (asExt K L w)

theorem invVal_mul_invInv (x : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) :
    invVal K L x * invInv K L x = 1 := by
  funext w
  show ((x (below K L w) : (∀ w' : (below K L w).Extension L, w'.1.Completion)) *
      (((x (below K L w))⁻¹ : (∀ w' : (below K L w).Extension L, w'.1.Completion)ˣ) : _)) (asExt K L w) = 1
  rw [Units.mul_inv]
  rfl

theorem invInv_mul_invVal (x : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) :
    invInv K L x * invVal K L x = 1 := by
  funext w
  show ((((x (below K L w))⁻¹ : (∀ w' : (below K L w).Extension L, w'.1.Completion)ˣ) : _) *
      (x (below K L w) : (∀ w' : (below K L w).Extension L, w'.1.Completion))) (asExt K L w) = 1
  rw [Units.inv_mul]
  rfl

def inv (x : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) : (InfiniteAdeleRing L)ˣ :=
  ⟨invVal K L x, invInv K L x, invVal_mul_invInv K L x, invInv_mul_invVal K L x⟩

def fwd (y : (InfiniteAdeleRing L)ˣ) : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ :=
  fun v => AutomorphicForm.TransversalMeasure.archFibre K L v y

theorem fwd_val (y : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K) (w : v.Extension L) :
    ((fwd K L y v : (∀ w : v.Extension L, w.1.Completion)ˣ) : ∀ w : v.Extension L, w.1.Completion) w =
      (y : InfiniteAdeleRing L) w.1 := rfl

theorem inv_fwd (y : (InfiniteAdeleRing L)ˣ) : inv K L (fwd K L y) = y := by
  apply Units.ext
  funext w
  rfl

theorem fwd_inv (x : ∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) : fwd K L (inv K L x) = x := by
  funext v
  apply Units.ext
  funext w
  obtain ⟨w, hw⟩ := w
  subst hw
  rfl

def mulEquiv : (InfiniteAdeleRing L)ˣ ≃* (∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) where
  toFun := fwd K L
  invFun := inv K L
  left_inv := inv_fwd K L
  right_inv := fwd_inv K L
  map_mul' y z := by funext v; exact map_mul _ y z

theorem continuous_fwd : Continuous (fwd K L) := by
  refine continuous_pi fun v => ?_
  exact Continuous.units_map _ (continuous_pi fun w => continuous_apply w.1)

theorem continuous_inv : Continuous (inv K L) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun x => invVal K L x
    refine continuous_pi fun w => ?_
    exact (continuous_apply (asExt K L w)).comp (Units.continuous_val.comp (continuous_apply (below K L w)))
  · show Continuous fun x => invInv K L x
    refine continuous_pi fun w => ?_
    exact (continuous_apply (asExt K L w)).comp (Units.continuous_coe_inv.comp (continuous_apply (below K L w)))

def contMulEquiv : (InfiniteAdeleRing L)ˣ ≃ₜ* (∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ) :=
  { mulEquiv K L with
    continuous_toFun := continuous_fwd K L
    continuous_invFun := continuous_inv K L }

end ArchRegroup

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ E : (InfiniteAdeleRing L)ˣ ≃ₜ* (∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ),
      ∀ (y : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K),
        E y v = AutomorphicForm.TransversalMeasure.archFibre K L v y :=
  ⟨ArchRegroup.contMulEquiv K L, fun _ _ => rfl⟩

end
end S_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
end P2MW
export P2MW.S_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre (solution)
