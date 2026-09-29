-- Prove2me | solution 1 for ModularCurve.LevelModuliPackageAbs.natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/561563d3-bfa8-586d-b6b8-d3d834278fb4

import Mathlib
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq

set_option autoImplicit false

universe u

open ModularCurve

theorem solution
    {A : Type u} [CommRing A] {D : LevelModuliDatum.{u} A} (P₀ : LevelModuliPackageAbs A D)
    (T : Type u) [CommRing T] [Algebra A T] (t : T) :
    Nat.card {φ : P₀.B₀ →ₐ[A] T // φ (D.jOf P₀.univ) = t} = Nat.card {x : D.Pt T // D.jOf x = t} := by
  classical
  refine Nat.card_congr ?_
  refine
    { toFun := fun φ => ⟨D.map φ.1 P₀.univ, by rw [D.jOf_map]; exact φ.2⟩
      invFun := fun x => ⟨P₀.classify x.1, by rw [← D.jOf_map, P₀.map_classify]; exact x.2⟩
      left_inv := fun φ => ?_
      right_inv := fun x => ?_ }
  · apply Subtype.ext
    exact (P₀.classify_unique _ φ.1 rfl).symm
  · apply Subtype.ext
    exact P₀.map_classify x.1

end S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq
end P2MW
export P2MW.S_ModularCurve_LevelModuliPackageAbs_natCard_algHom_apply_jOf_univ_eq_natCard_pt_jOf_eq (solution)
