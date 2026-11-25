-- Prove2me | solution 1 for GlobalTheory.ChowHt.irreducible_linForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:29:44.496613+00:00
-- url     : https://prove2.me/submissions/05ca705c-86cc-4ae8-b191-9433b467cb93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PointHeight
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_BlockSphereMeanLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallAevalLineVanishingIdealIff
import Theorems.Thm_GlobalTheory_ChowHt_Model_coeff_linForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
namespace GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false in
open MvPolynomial NumberField in
attribute [local instance] MvPolynomial.gradedAlgebra in
private lemma linForm_isHomogeneous_one' {K : Type} [Field K] {N : ℕ} (c : Fin N → K) :
    (_root_.GlobalTheory.ChowHt.Model.linForm c).IsHomogeneous 1 := by
  unfold _root_.GlobalTheory.ChowHt.Model.linForm
  refine IsHomogeneous.sum _ _ _ fun j _ => ?_
  simpa using (isHomogeneous_C (Fin 1 × Fin N) (c j)).mul (isHomogeneous_X K ((0 : Fin 1), j))
end GlobalTheory.ChowHt
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial NumberField
open GlobalTheory GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
open MvPolynomial NumberField
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.ChowHt
namespace _root_.GlobalTheory.ChowHt
theorem _root_.solution {K : Type} [Field K] {N : ℕ} {c : Fin N → K}
    (hc : c ≠ 0) :
    Irreducible (_root_.GlobalTheory.ChowHt.Model.linForm c) := by
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hc
  have hk' : (_root_.GlobalTheory.ChowHt.Model.linForm c).coeff (Finsupp.single (0, k) 1) ≠ 0 := by
    rw [_root_.GlobalTheory.ChowHt.Model.coeff_linForm]; exact hk
  have hne : _root_.GlobalTheory.ChowHt.Model.linForm c ≠ 0 := by
    intro h; rw [h, coeff_zero] at hk'; exact hk' rfl
  refine irreducible_of_totalDegree_eq_one
    ((linForm_isHomogeneous_one' c).totalDegree hne) fun x hx => ?_
  refine isUnit_iff_ne_zero.mpr fun hx0 => hk' ?_
  have := hx (Finsupp.single (0, k) 1)
  rw [hx0] at this
  exact zero_dvd_iff.mp this
end _root_.GlobalTheory.ChowHt
end GlobalTheory.ChowHt
