-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_G_eq_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:48:17.563776+00:00
-- url     : https://prove2.me/submissions/507968aa-174d-4423-b817-b654362aeab2

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_Uniformization
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationAddition
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_UniformizationEisenstein
import Theorems.Thm_GroundTheory_Global_Elliptic_G_eq_aeval_eisensteinPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set
open scoped PeriodPair Nat
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {k : ℕ} (hk : 2 ≤ k) :
    ∃ P : MvPolynomial (Fin 2) ℚ, ∀ L : PeriodPair,
      L.G (2 * k) = MvPolynomial.aeval ![L.g₂, L.g₃] P := by
  refine ⟨eisensteinPoly (k - 1), fun L ↦ ?_⟩
  rw [show 2 * k = 2 * (k - 1) + 2 by omega]
  exact G_eq_aeval_eisensteinPoly (by omega)
end GroundTheory.Global.Elliptic
