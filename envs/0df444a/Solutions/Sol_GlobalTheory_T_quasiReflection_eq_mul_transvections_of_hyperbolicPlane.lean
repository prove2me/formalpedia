-- Prove2me | solution 1 for GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:58:06.325212+00:00
-- url     : https://prove2.me/submissions/5ea58815-99ad-4d25-9de3-8bdbba9a16d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPla
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement
import Theorems.Thm_GlobalTheory_UTrans_PlaneRefl_quasiRefl_eq_mul_of_plane


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → ∀ (x z : Fin n → E) (a u : E), hf σ G z z = 0 → hf σ G x z ≠ 0 → hf σ G x x ≠ 0 → hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G (x + a • z) ((u - 1) / hf σ G (x + a • z) (x + a • z)) := by
  first | exact @GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane | exact GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane | (intros; apply GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane <;> assumption)
end _root_.GlobalTheory.T
