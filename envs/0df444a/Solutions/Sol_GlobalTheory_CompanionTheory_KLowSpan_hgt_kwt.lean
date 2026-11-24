-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KLowSpan.hgt_kwt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:29.708802+00:00
-- url     : https://prove2.me/submissions/a3b16a91-d60a-42e5-b3a0-688ca1e5221f

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
    ∀ l : List (Fin n × Fin n), KLower ε l →
      ∑ c : Fin n, ((c : ℕ) : ℝ) * μ c + l.length ≤ ∑ c : Fin n, ((c : ℕ) : ℝ) * kwt μ l c := by
  intro l
  induction l with
  | nil => intro _; simp [kwt_nil]
  | cons p l ih =>
    intro hl
    have hp := (hl p (List.mem_cons_self ..)).1
    have ih' := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    have key : ∑ c : Fin n, ((c : ℕ) : ℝ) * kwt μ (p :: l) c =
        ∑ c : Fin n, ((c : ℕ) : ℝ) * kwt μ l c + (((p.1 : ℕ) : ℝ) - ((p.2 : ℕ) : ℝ)) := by
      rw [kwt_cons]
      simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      simp [Pi.single_apply]
    have h1 : (1 : ℝ) ≤ ((p.1 : ℕ) : ℝ) - ((p.2 : ℕ) : ℝ) := by
      have h2 : (p.2 : ℕ) + 1 ≤ (p.1 : ℕ) := Fin.lt_def.mp hp
      have h3 : ((p.2 : ℕ) : ℝ) + 1 ≤ ((p.1 : ℕ) : ℝ) := by exact_mod_cast h2
      linarith
    rw [key, List.length_cons]
    push_cast
    linarith
end GlobalTheory.CompanionTheory.KLowSpan
