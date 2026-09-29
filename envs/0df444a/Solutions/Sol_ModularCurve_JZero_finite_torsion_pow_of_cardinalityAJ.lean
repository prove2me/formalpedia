-- Prove2me | solution 1 for ModularCurve.JZero.finite_torsion_pow_of_cardinalityAJ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/917ed301-ce45-5a61-8f20-4ff52e726a72

import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_ModularCurve_EichlerShimuraData
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ

open AlgebraicCurve ModularCurve

def Pic0TorsionEquivSubtype (K F : Type*) [Field K] [Field F] [Algebra K F] (n : ℕ) :
    Pic0.torsion K F n ≃ {x : Pic0 K F // n • x = 0} :=
  Equiv.subtypeEquivRight (fun x => (Pic0.mem_torsion).trans (by rw [natCast_zsmul]))

theorem Pic0.natCard_torsion_eq_natCard_subtype (K F : Type*) [Field K] [Field F] [Algebra K F]
    (n : ℕ) : Nat.card (Pic0.torsion K F n) = Nat.card {x : Pic0 K F // n • x = 0} :=
  Nat.card_congr (Pic0TorsionEquivSubtype K F n)

theorem solution (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
    (hK1 : CardinalityAJ p (JZero N) (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N)))
    (k : ℕ) : Finite (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (p ^ k)) := by
  apply Nat.finite_of_card_ne_zero
  rw [Pic0.natCard_torsion_eq_natCard_subtype]
  have h := hK1 k
  rw [h]
  exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

end S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ
end P2MW
export P2MW.S_ModularCurve_JZero_finite_torsion_pow_of_cardinalityAJ (solution)
