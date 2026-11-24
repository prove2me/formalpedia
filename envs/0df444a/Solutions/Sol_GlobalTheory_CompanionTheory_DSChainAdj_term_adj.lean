-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSChainAdj.term_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:43:45.555484+00:00
-- url     : https://prove2.me/submissions/4040ad2d-3dd4-4ed9-b7fe-e400dbdad6f5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SumInsertErase
import Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_sg_insert
import Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_conj_sg
import Theorems.Thm_GlobalTheory_CompanionTheory_DSChainAdj_sum_insert_erase
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
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSChainAdj
open CompanionTheory.D.DSIC
variable {n : ℕ} {ε : Fin n → Bool}
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
namespace GlobalTheory.CompanionTheory.DSChainAdj
theorem _root_.solution (i : NC ε) (T T' : Module.End ℂ V) (h : ∀ x y : V, ⟪T x, y⟫_ℂ = -⟪x, T' y⟫_ℂ) (w x : Ch ε V) :
    ip (lift ε T (ann i w)) x = -ip w (lift ε T' (cre i x)) := by
  unfold ip
  have key := sum_insert_erase i (fun B A => sg i B * ⟪T (w B), x A⟫_ℂ)
  have hL : (∑ A, ⟪lift ε T (ann i w) A, x A⟫_ℂ) =
      ∑ A : Finset (NC ε), if i ∈ A then 0 else sg i (insert i A) * ⟪T (w (insert i A)), x A⟫_ℂ := by
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [ann, hA]
    · simp [ann, hA, conj_sg, sg_insert, mul_comm]
  have hR : -(∑ A, ⟪w A, lift ε T' (cre i x) A⟫_ℂ) =
      ∑ B : Finset (NC ε), if i ∈ B then sg i B * ⟪T (w B), x (B.erase i)⟫_ℂ else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun A _ => ?_
    by_cases hA : i ∈ A
    · simp [cre, hA, h]
    · simp [cre, hA]
  rw [hL, hR, key]
end GlobalTheory.CompanionTheory.DSChainAdj
