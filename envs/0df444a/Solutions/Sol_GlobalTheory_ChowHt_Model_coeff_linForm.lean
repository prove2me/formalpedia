-- Prove2me | solution 1 for GlobalTheory.ChowHt.Model.coeff_linForm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:55:14.793902+00:00
-- url     : https://prove2.me/submissions/7ebcb7a6-8831-4b3d-ab12-a3b51c0b5a47

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsIsHomogeneousOfEquivariant
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm

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
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.ChowHt.Model
set_option autoImplicit false
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt.Model
namespace _root_.GlobalTheory.ChowHt.Model
theorem _root_.solution {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R)
    (k : Fin N) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) = c k := by
  classical
  simp only [_root_.GlobalTheory.ChowHt.Model.linForm, coeff_sum, coeff_C_mul, coeff_X']
  have key : ∀ j : Fin N,
      (Finsupp.single ((0 : Fin 1), j) 1 = Finsupp.single ((0 : Fin 1), k) 1) ↔ j = k := by
    intro j
    constructor
    · intro h
      have := Finsupp.single_left_injective (one_ne_zero) h
      simpa using this
    · rintro rfl; rfl
  simp [key]
end _root_.GlobalTheory.ChowHt.Model
end GlobalTheory.ChowHt.Model
