-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/e2ee0657-cf87-5fde-b957-e3d28b78abe1

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_natCast_ne_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_not_dvd
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

namespace ModularCurve p2m_export "ModularCurve" "ModularPolynomialData ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero" namespace IgusaSepFinAux end ModularCurve.IgusaSepFinAux
p2m_open_scoped "ModularCurve" in
theorem ModularCurve.IgusaSepFinAux.natCast_ne_zero_algClosure_zmod (ℓ N : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    (N : AlgebraicClosure (ZMod ℓ)) ≠ 0 := by
  haveI : CharP (AlgebraicClosure (ZMod ℓ)) ℓ :=
    charP_of_injective_algebraMap (algebraMap (ZMod ℓ) (AlgebraicClosure (ZMod ℓ))).injective ℓ
  intro h
  exact hℓ ((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod ℓ)) ℓ N).mp h)

theorem solution (N : ℕ) [NeZero N] (data : ModularCurve.ModularPolynomialData N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure (ZMod ℓ))))).map
      (algebraMap (Polynomial (AlgebraicClosure (ZMod ℓ))) (RatFunc (AlgebraicClosure (ZMod ℓ))))).Separable :=
  ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_natCast_ne_zero (AlgebraicClosure (ZMod ℓ)) N data
    (ModularCurve.IgusaSepFinAux.natCast_ne_zero_algClosure_zmod ℓ N hℓ)

end S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_not_dvd (solution)
