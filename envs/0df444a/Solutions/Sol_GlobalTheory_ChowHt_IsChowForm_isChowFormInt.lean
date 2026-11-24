-- Prove2me | solution 1 for GlobalTheory.ChowHt.IsChowForm.isChowFormInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:34:38.672181+00:00
-- url     : https://prove2.me/submissions/196e67e7-3c25-445d-900c-e77fede316e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AevalEqZeroOfHomogeneousComponent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IrreducibleOfIrreducibleMap
import Theorems.Thm_GlobalTheory_ChowHt_irreducible_of_irreducible_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type} [Field k] {N : ℕ}
namespace GlobalTheory.ChowHt
namespace IsChowForm
theorem _root_.solution {I : Ideal (MvPolynomial (Fin N) k)} {e dl : ℕ}
    {f : MvPolynomial (Fin (e + 1) × Fin N) k} (h : IsChowForm I e dl f) :
    IsChowFormInt I e dl f :=
  ⟨h.homog, irreducible_of_irreducible_map h.irred, h.zero_iff⟩
end IsChowForm
end GlobalTheory.ChowHt
