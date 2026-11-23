-- Prove2me | solution 1 for GlobalTheory.T.unitaryQuasiReflection_laws
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:20:39.903579+00:00
-- url     : https://prove2.me/submissions/524a25b2-90e3-41ff-bcb5-19f52b707781

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLaws
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryQuasiReflectionLawsStatement
import Theorems.Thm_GlobalTheory_UnRep_ReflLaws_refl_laws


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
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ x : Fin n → E, hermE c G x x ≠ 0 → (∀ u v, refl c G x u *ᵥ v = v + ((u - 1) * hermE c G v x / hermE c G x x) • x) ∧ refl c G x 1 = 1 ∧ (∀ u u', refl c G x u * refl c G x u' = refl c G x (u * u')) ∧ ∀ u, u * c u = 1 → IsUnE c G (refl c G x u) := by
  first | exact @GlobalTheory.UnRep.ReflLaws.refl_laws | exact GlobalTheory.UnRep.ReflLaws.refl_laws | (intros; apply GlobalTheory.UnRep.ReflLaws.refl_laws <;> assumption)
end _root_.GlobalTheory.T
