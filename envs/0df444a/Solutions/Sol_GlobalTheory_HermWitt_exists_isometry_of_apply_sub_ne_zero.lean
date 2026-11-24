-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_of_apply_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:23:43.009747+00:00
-- url     : https://prove2.me/submissions/e13f4bfb-5069-4b8f-8bc0-6418fff1f4f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_apply
import Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_quasiRefl
import Theorems.Thm_GlobalTheory_HermWitt_apply_quasiRefl_quasiRefl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {x y : V} (hxy : B x x = B y y) (ha : B x (x - y) ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧
      ∀ u, B u (x - y) = 0 → γ u = u := by
  have hca : c (B x (x - y)) ≠ 0 := (map_ne_zero c).2 ha
  have hab : B x (x - y) + c (B x (x - y)) = B (x - y) (x - y) := by
    rw [hB]
    simp only [map_sub, LinearMap.sub_apply]
    linear_combination hxy
  refine ⟨LinearEquiv.ofLinear (quasiRefl B (x - y) (B x (x - y)))
    (quasiRefl B (x - y) (c (B x (x - y)))) ?_ ?_, ?_, ?_, ?_⟩
  · ext z
    exact quasiRefl_quasiRefl B hca ha (by rw [add_comm, hab]) z
  · ext z
    exact quasiRefl_quasiRefl B ha hca hab z
  · exact apply_quasiRefl_quasiRefl hB ha hab
  · rw [LinearEquiv.ofLinear_apply, quasiRefl_apply, inv_mul_cancel₀ ha, one_smul, sub_sub_cancel]
  · intro u hu
    rw [LinearEquiv.ofLinear_apply, quasiRefl_apply, hu, mul_zero, zero_smul, sub_zero]
end GlobalTheory.HermWitt
