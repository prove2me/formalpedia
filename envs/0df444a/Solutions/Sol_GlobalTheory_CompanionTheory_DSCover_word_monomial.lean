-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCover.word_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:26:31.442138+00:00
-- url     : https://prove2.me/submissions/ef6e2454-6a33-4fff-b164-c2bffe37a977

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WordMonomial
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCover_pd_apply
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
open scoped TensorProduct
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCover
open Formalism.REAL (GlRel)
open CompanionTheory.D.DSIC
variable {σ : Type}
namespace GlobalTheory.CompanionTheory.DSCover
theorem _root_.solution (l : List σ) : ∀ (s : σ →₀ ℕ) (c : ℂ), s.degree < l.length →
    (l.map pd).prod (monomial s c) = 0 := by
  induction l using List.reverseRecOn with
  | nil => intro s c h; simp at h
  | append_singleton l i ih =>
    intro s c h
    rw [List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Module.End.mul_apply, pd_apply,
      pderiv_monomial]
    by_cases hs : s i = 0
    · simp [hs]
    · apply ih
      have e : s = (s - Finsupp.single i 1) + Finsupp.single i 1 := by
        rw [tsub_add_cancel_of_le]
        rw [Finsupp.single_le_iff]
        omega
      have e2 := congrArg Finsupp.degree e
      rw [map_add, Finsupp.degree_single] at e2
      simp only [List.length_append, List.length_singleton] at h
      omega
end GlobalTheory.CompanionTheory.DSCover
