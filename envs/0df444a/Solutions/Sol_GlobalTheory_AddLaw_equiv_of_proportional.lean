-- Prove2me | solution 1 for GlobalTheory.AddLaw.equiv_of_proportional
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:18.175527+00:00
-- url     : https://prove2.me/submissions/14e55d54-ac3c-4880-8472-1442b27ece05

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DiagZEqNegAddY
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SubMulOriginD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Projective
open GlobalTheory GlobalTheory.AddLaw
variable {F : Type*} [Field F] {W : Projective F}
namespace GlobalTheory.AddLaw
theorem _root_.solution {T U : Fin 3 → F} (h : Proportional T U) (hT : T ≠ 0) (hU : U ≠ 0) :
    T ≈ U := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hU
  replace hj : U j ≠ 0 := hj
  have e : (T j / U j) • U = T := by
    ext i
    rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, div_eq_iff hj, h i j]
  have hu : T j / U j ≠ 0 := fun h0 => hT <| by rw [← e, h0, zero_smul]
  exact ⟨Units.mk0 _ hu, e⟩
end GlobalTheory.AddLaw
