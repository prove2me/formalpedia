-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSICWLem.wlem_of_gfacts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:51.027893+00:00
-- url     : https://prove2.me/submissions/a4982ae3-cee0-4258-bf50-bb7659078c25

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WlemOfGfacts
import Theorems.Thm_GlobalTheory_CompanionTheory_DSICWLem_ht_add_root
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSICWLem
open CompanionTheory.D.DSIC
open Formalism.REAL (KHighest IsWeight)
namespace GlobalTheory.CompanionTheory.DSICWLem
theorem _root_.solution (hG : GFacts) : WLem := by
  intro n ε V _ _ E γ x hx hK
  obtain ⟨g, hg, -, hwt, hdiag, -⟩ := hG n ε
  classical
  have hne : (univ.filter fun A : Finset (NC ε) => x A ≠ 0).Nonempty := by
    by_contra hc
    apply hx
    funext A
    by_contra hA
    exact hc ⟨A, by simpa using hA⟩
  obtain ⟨A, hA, hmin⟩ := Finset.exists_min_image _ (fun A : Finset (NC ε) => ht (wtA A)) hne
  have hA0 : x A ≠ 0 := by simpa using hA
  refine ⟨A, hA0, ?_⟩
  have hF : ∀ c d, Fop ε E c d x A = E c d (x A) + ∑ B, (g c d A B : ℂ) • x B := by
    intro c d
    rw [← hg V c d x A]
    rfl
  refine ⟨fun a => ?_, fun a b hab hε => ?_⟩
  · have h1 := congrFun (hK.1 a) A
    rw [hF] at h1
    have h2 : ∑ B, (g a a A B : ℂ) • x B = (wtA A a : ℂ) • x A := by
      rw [Finset.sum_eq_single A]
      · simp [hdiag]
      · intro B _ hB
        simp [hdiag, Ne.symm hB]
      · simp
    rw [h2, Pi.smul_apply] at h1
    rw [Pi.sub_apply, Complex.ofReal_sub, sub_smul, ← h1, add_sub_cancel_right]
  · have h1 := congrFun (hK.2 a b hab hε) A
    rw [hF] at h1
    have h2 : ∑ B, (g a b A B : ℂ) • x B = 0 := by
      refine Finset.sum_eq_zero fun B _ => ?_
      by_cases hgB : g a b A B = 0
      · simp [hgB]
      by_cases hxB : x B = 0
      · simp [hxB]
      exfalso
      have h3 := hmin B (by simpa using hxB)
      have h4 := ht_add_root (wtA B) a b hab
      rw [← (hwt a b A B hgB).2] at h4
      exact absurd h3 (not_le.mpr h4)
    rw [h2, add_zero] at h1
    exact h1
end GlobalTheory.CompanionTheory.DSICWLem
