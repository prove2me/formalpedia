-- Prove2me | solution 1 for GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:22.466936+00:00
-- url     : https://prove2.me/submissions/440b2280-3051-446b-8c48-7378591cbc1a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexMapNsmulComapEqAbsNormDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RelIndexMapNsmulComapEqAbsNormDetStatement
import Theorems.Thm_GlobalTheory_relIndex_map_nsmul_comap_eq_abs_norm_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  first | exact @GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | exact GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | (intros; apply GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det <;> assumption)
end _root_.GlobalTheory.T
