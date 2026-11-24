-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeBern.fixed_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:36:57.588459+00:00
-- url     : https://prove2.me/submissions/21beed46-aa6d-4a84-95e7-7e12c1f377b4

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeBern
theorem _root_.solution (w : (G ⧸ K) →₀ ℂ) (hw : ∀ k ∈ K, lam K k w = w) (u : G) (S : Finset (G ⧸ K))
    (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (u : G ⧸ K))
    (hsupp : ∀ y, y ∉ S → w y = 0) :
    w = w (u : G ⧸ K) • ∑ y ∈ S, Finsupp.single y (1 : ℂ) := by
  classical
  ext y
  have hsum : (∑ x ∈ S, Finsupp.single x (1 : ℂ)) y = if y ∈ S then 1 else 0 := by
    rw [Finsupp.finsetSum_apply]
    simp [Finsupp.single_apply]
  rw [Finsupp.smul_apply, hsum]
  by_cases hy : y ∈ S
  · have hy' : y ∈ MulAction.orbit K (u : G ⧸ K) := by rw [← hS]; exact hy
    obtain ⟨k, rfl⟩ := hy'
    have h1 : (lam K (k : G) w) ((k : G) • (u : G ⧸ K)) = w (u : G ⧸ K) :=
      Finsupp.mapDomain_apply (MulAction.injective (k : G)) _ _
    rw [hw k k.2] at h1
    rw [if_pos hy, smul_eq_mul, mul_one]
    exact h1
  · rw [if_neg hy, hsupp y hy]; simp
end GlobalTheory.CompanionTheory.HeckeBern
