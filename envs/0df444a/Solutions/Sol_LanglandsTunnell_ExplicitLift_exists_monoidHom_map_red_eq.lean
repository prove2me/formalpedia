-- Prove2me | solution 1 for LanglandsTunnell.ExplicitLift.exists_monoidHom_map_red_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/4a9ed99f-c4a8-526b-ac91-d80a646e3ef5

import Mathlib
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Theorems.Thm_LanglandsTunnell_ExplicitLift_map_red_injOn_closure
import Theorems.Thm_LanglandsTunnell_ExplicitLift_exists_mem_closure_map_red_eq_of_det_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq

set_option autoImplicit false

open scoped MatrixGroups

noncomputable section

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ExplicitLift.map_red_injOn_closure ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero"
namespace ExplicitLift
p2m_export "LanglandsTunnell.ExplicitLift" "map_red_injOn_closure exists_mem_closure_map_red_eq_of_det_ne_zero"
namespace SEC
p2m_open "LanglandsTunnell.ExplicitLift LanglandsTunnell"

open FLT.ExplicitLift

abbrev G48 : Submonoid (Matrix (Fin 2) (Fin 2) (ℤ√(-2))) :=
  Submonoid.closure ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))

noncomputable def lift (g : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ℤ√(-2)) :=
  (LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (g.det_ne_zero)).choose

theorem lift_mem (g : GL (Fin 2) (ZMod 3)) : lift g ∈ G48 :=
  (LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (g.det_ne_zero)).choose_spec.1

theorem lift_map (g : GL (Fin 2) (ZMod 3)) :
    (lift g).map red = (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) :=
  (LanglandsTunnell.ExplicitLift.exists_mem_closure_map_red_eq_of_det_ne_zero
    (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (g.det_ne_zero)).choose_spec.2

theorem map_mul_red (A B : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) :
    (A * B).map red = A.map red * B.map red := Matrix.map_mul

theorem lift_one : lift 1 = 1 := by
  apply LanglandsTunnell.ExplicitLift.map_red_injOn_closure (lift_mem 1) (Submonoid.one_mem _)
  show (lift 1).map red = (1 : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).map red
  rw [lift_map, Units.val_one, Matrix.map_one _ (map_zero red) (map_one red)]

theorem lift_mul (g h : GL (Fin 2) (ZMod 3)) : lift (g * h) = lift g * lift h := by
  apply LanglandsTunnell.ExplicitLift.map_red_injOn_closure (lift_mem (g * h))
    (Submonoid.mul_mem _ (lift_mem g) (lift_mem h))
  show (lift (g * h)).map red = (lift g * lift h).map red
  rw [map_mul_red, lift_map, lift_map, lift_map, Units.val_mul]

noncomputable def liftUnit (g : GL (Fin 2) (ZMod 3)) : GL (Fin 2) (ℤ√(-2)) where
  val := lift g
  inv := lift g⁻¹
  val_inv := by rw [← lift_mul, mul_inv_cancel, lift_one]
  inv_val := by rw [← lift_mul, inv_mul_cancel, lift_one]

noncomputable def psi : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)) where
  toFun := liftUnit
  map_one' := Units.ext lift_one
  map_mul' g h := Units.ext (lift_mul g h)

theorem map_red_psi (g : GL (Fin 2) (ZMod 3)) : Matrix.GeneralLinearGroup.map red (psi g) = g := by
  apply Units.ext
  change red.mapMatrix (lift g) = (g : Matrix (Fin 2) (Fin 2) (ZMod 3))
  rw [RingHom.mapMatrix_apply, lift_map]

theorem psi_mem (g : GL (Fin 2) (ZMod 3)) : ((psi g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) ∈ G48 :=
  lift_mem g

end LanglandsTunnell.ExplicitLift.SEC

open LanglandsTunnell.ExplicitLift.SEC in
theorem solution :
    ∃ Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)),
      (∀ g : GL (Fin 2) (ZMod 3), Matrix.GeneralLinearGroup.map FLT.ExplicitLift.red (Ψ g) = g) ∧
      (∀ g : GL (Fin 2) (ZMod 3), ((Ψ g : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))) ∈
        Submonoid.closure
          ({FLT.ExplicitLift.Slift, FLT.ExplicitLift.Tlift} : Set (Matrix (Fin 2) (Fin 2) (ℤ√(-2))))) :=
  ⟨psi, map_red_psi, psi_mem⟩

end

end S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq
end P2MW
export P2MW.S_LanglandsTunnell_ExplicitLift_exists_monoidHom_map_red_eq (solution)
