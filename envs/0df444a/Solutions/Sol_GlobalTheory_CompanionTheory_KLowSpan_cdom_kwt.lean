-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.cdom_kwt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:29.134364+00:00
-- url     : https://prove2.me/submissions/bd693f58-af4f-4251-a882-451eff9db879

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_EqSmulOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kwt_nil
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kwt_cons
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil



set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open CompanionTheory.D.gk.HwAlg (word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KLowSpan
variable {n : ℕ} {ε : Fin n → Bool}
variable {U : Type} [AddCommGroup U] [Module ℂ U]
variable {F : Fin n → Fin n → Module.End ℂ U} {μ : Fin n → ℝ} {w : U}
namespace GlobalTheory.CompanionTheory.KLowSpan
theorem _root_.solution (μ : Fin n → ℝ) :
    ∀ l : List (Fin n × Fin n), KLower ε l → PI.UpqRep.CDom ε (kwt μ l) μ := by
  intro l
  induction l with
  | nil => intro; exact ⟨0, by simp, by simp [kwt_nil]⟩
  | cons p l ih =>
    intro hl
    have hl' : KLower ε l := fun q hq => hl q (List.mem_cons_of_mem _ hq)
    have hp := hl p (by simp)
    obtain ⟨c, hc, hs⟩ := ih hl'
    refine ⟨fun a b => c a b + if b = p.1 then (if a = p.2 then 1 else 0) else 0, ?_, ?_⟩
    · intro a b h
      by_cases h0 : c a b = 0
      · simp only [h0, zero_add] at h
        split_ifs at h with h1 h2
        · subst h1 h2; exact ⟨hp.1, hp.2.symm⟩
        · exact absurd rfl h
        · exact absurd rfl h
      · exact hc a b h0
    · simp only [Nat.cast_add, add_smul, Finset.sum_add_distrib, ← hs, Nat.cast_ite, ite_smul,
        Nat.cast_zero, Nat.cast_one, zero_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, kwt_cons]
      simp only [PI.UpqRep.root]
      abel
end GlobalTheory.CompanionTheory.KLowSpan
