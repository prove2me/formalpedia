-- Prove2me | solution 1 for GlobalTheory.SupNormExample.bddAt_of_fnorm_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:01.81944+00:00
-- url     : https://prove2.me/submissions/bff84c4e-1156-4045-8579-deb9e40aa10f

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SupNormExample
open Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
namespace GlobalTheory.SupNormExample
theorem _root_.solution (σ : K →+* ℂ) (e : ι → ℕ) (i : ι) (hi : e i ≠ 0) (f : Rules pts) :
    BddAt pts mapR σ (fun _ _ => 0) e f ∧ supAt pts mapR σ (fun _ _ => 0) e f = 0 := by
  have h : ∀ y, ptNorm pts mapR σ (fun _ _ => 0) e f y = 0 := fun y => by
    unfold ptNorm
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]), mul_zero]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rintro _ ⟨y, rfl⟩; exact (h y).le
  · unfold supAt; simp [h]
end GlobalTheory.SupNormExample
