-- Prove2me | solution 1 for GlobalTheory.DI.extD_algebraMap_pow_char_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:35.140602+00:00
-- url     : https://prove2.me/submissions/3dd3eb3b-36d8-47ef-a9c1-d6748ded56f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtDAlgebraMapPowCharMul
import Theorems.Thm_GlobalTheory_DI_kaehlerZ_D_pow_char

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K]
variable (p : ℕ) [Fact p.Prime] [CharP K p]
namespace GlobalTheory.DI
theorem _root_.solution {d : ExteriorAlgebra K Ω[K⁄ℤ] →+ ExteriorAlgebra K Ω[K⁄ℤ]} (hd : IsExtD ℤ K d)
    (c : K) (x : ExteriorAlgebra K Ω[K⁄ℤ]) :
    d (algebraMap K _ (c ^ p) * x) = algebraMap K _ (c ^ p) * d x := by
  rw [hd.mul, hd.alg, kaehlerZ_D_pow_char p, map_zero, zero_mul, zero_add]
  congr 1
  exact AlgHom.commutes _ _
end GlobalTheory.DI
