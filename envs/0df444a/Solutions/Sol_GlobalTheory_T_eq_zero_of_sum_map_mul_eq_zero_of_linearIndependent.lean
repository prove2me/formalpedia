-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:12:57.854131+00:00
-- url     : https://prove2.me/submissions/45e9ec89-d46f-4f9e-b5fe-a8010873dddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_GaloisLinearDisjointStatement
import Theorems.Thm_GlobalTheory_GalDisj_galois_linearDisjoint


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k Ω D : Type) [Field k] [Field Ω] [Field D] [Algebra k Ω] [IsGalois k Ω] (o : Ω →+* D) (F : Subfield D), (∀ x : Ω, o x ∈ F ↔ x ∈ (algebraMap k Ω).range) → ∀ (m : ℕ) (x : Fin m → Ω), LinearIndependent k x → ∀ b : Fin m → D, (∀ i, b i ∈ F) → ∑ i, o (x i) * b i = 0 → ∀ i, b i = 0 := by
  first | exact @GlobalTheory.GalDisj.galois_linearDisjoint | exact GlobalTheory.GalDisj.galois_linearDisjoint | (intros; apply GlobalTheory.GalDisj.galois_linearDisjoint <;> assumption)
end _root_.GlobalTheory.T
