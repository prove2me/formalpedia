-- Prove2me | solution 1 for GlobalTheory.HermWitt.apply_quasiRefl_quasiRefl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:59.208905+00:00
-- url     : https://prove2.me/submissions/538ce56d-c1cb-4a34-be37-1ff670651739

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_quasiRefl_apply

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
theorem _root_.solution {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x)
    {v : V} {a : E} (ha : a ≠ 0) (hab : a + c a = B v v) (z w : V) :
    B (quasiRefl B v a z) (quasiRefl B v a w) = B z w := by
  have hca : c a ≠ 0 := (map_ne_zero c).2 ha
  simp only [quasiRefl_apply, map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, map_mul, map_inv₀, hB, ← hab]
  field_simp
  ring
end GlobalTheory.HermWitt
