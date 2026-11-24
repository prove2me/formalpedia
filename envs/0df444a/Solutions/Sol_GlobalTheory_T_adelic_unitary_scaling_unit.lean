-- Prove2me | solution 1 for GlobalTheory.T.adelic_unitary_scaling_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:21:11.030625+00:00
-- url     : https://prove2.me/submissions/880227d5-4757-4986-9cd6-fd3bc3d61165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnit
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Theorems.Thm_GlobalTheory_UnRep_exists_norm_one_isUnit_det


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  first | exact @GlobalTheory.UnRep.exists_norm_one_isUnit_det | exact GlobalTheory.UnRep.exists_norm_one_isUnit_det | (intros; apply GlobalTheory.UnRep.exists_norm_one_isUnit_det <;> assumption)
end _root_.GlobalTheory.T
