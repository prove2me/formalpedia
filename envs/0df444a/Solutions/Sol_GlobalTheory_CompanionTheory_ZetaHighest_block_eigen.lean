-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZetaHighest.block_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:25.075137+00:00
-- url     : https://prove2.me/submissions/be557246-a35b-4504-9d79-8e79be3f055e

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_BlkStrictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_strictMono
import Theorems.Thm_GlobalTheory_CompanionTheory_ZetaHighest_blk_mem
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_Formalism_REAL_qDetHW
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZetaHighest
open CompanionTheory.D.DSIC Formalism.REAL
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.ZetaHighest
theorem _root_.solution (ε : Fin n → Bool) (s : Bool) (μ : Fin n → ℝ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) (hF : KRel ε F) (hx : KHighest ε F μ x) (u : ℂ) :
    qminor F (blk ε s) (blk ε s) u x = (∏ i : Fin (nb ε s), (u - (i : ℂ) + (μ (blk ε s i) : ℂ))) • x := by
  have inj : ∀ i j, blk ε s i = blk ε s j ↔ i = j := fun i j => (blk_strictMono ε s).injective.eq_iff
  have hgl : GlRel (fun i j => F (blk ε s i) (blk ε s j)) := by
    intro a b c d
    have := hF (blk ε s a) (blk ε s b) (blk ε s c) (blk ε s d) (by simp [blk_mem]) (by simp [blk_mem])
    simpa only [inj] using this
  have hw : IsHW (fun i j => F (blk ε s i) (blk ε s j)) (fun i => (μ (blk ε s i) : ℂ)) x :=
    ⟨fun a => hx.1 _, fun a b h => hx.2 _ _ (blk_strictMono ε s h) (by simp [blk_mem])⟩
  have hq : qminor F (blk ε s) (blk ε s) u = qdet (fun i j => F (blk ε s i) (blk ε s j)) u := by
    simp only [qdet, qminor, Tm, inj, id]
  rw [hq]
  exact qDetHW V _ _ _ x hgl hw u
end GlobalTheory.CompanionTheory.ZetaHighest
