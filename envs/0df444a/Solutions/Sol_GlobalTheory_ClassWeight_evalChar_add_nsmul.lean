-- Prove2me | solution 1 for GlobalTheory.ClassWeight.evalChar_add_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:01:45.752041+00:00
-- url     : https://prove2.me/submissions/24c93728-b86b-4ea6-9fcc-b18507540d2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PerfectPairingOrthogonalOfCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceFinrank
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_HeisenbergWeightSpaceIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ClassSubStructure
import Theorems.Thm_GlobalTheory_ClassWeight_evalChar_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassWeight
variable {X : Type} [AddCommGroup X] {F : Type} [Field F] {N : ℕ}
namespace GlobalTheory.ClassWeight
theorem _root_.solution (α mu : X) (τ : TorChar X F N) : evalChar F N (α + N • mu) τ = evalChar F N α τ := by
  have h : evalChar F N (N • mu) τ = 1 :=
    (map_pow τ.1 (Multiplicative.ofAdd mu) N).trans (DFunLike.congr_fun (show τ.1 ^ N = 1 from τ.2) _)
  rw [evalChar_add, h, mul_one]
end GlobalTheory.ClassWeight
