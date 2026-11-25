-- Prove2me | solution 1 for GlobalTheory.ZetaPole.bdd_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:36:08.868435+00:00
-- url     : https://prove2.me/submissions/e98d036c-16e6-42ec-a9f3-efcd98e4384d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PartialZetaTotallyRealAtMostSimplePole
import Theorems.Thm_GlobalTheory_ZetaPole_norm_le_idealZetaR
import Theorems.Thm_ReciprocityTheory_Cheb_dedekindZeta_eq_idealZetaR


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
noncomputable section
open GlobalTheory GlobalTheory.ZetaPole
namespace GlobalTheory.ZetaPole
theorem _root_.solution (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) : ∃ B : ℝ, ∀ᶠ x : ℝ in 𝓝[>] 1, ‖((x : ℂ) - 1) * Z x‖ ≤ B := by
  refine ⟨dedekindZeta_residue F + 1, ?_⟩
  have ht := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have hlt : ‖(dedekindZeta_residue F : ℂ)‖ < dedekindZeta_residue F + 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (dedekindZeta_residue_pos F)]; linarith
  filter_upwards [ht.eventually (eventually_lt_nhds hlt), self_mem_nhdsWithin] with x hx hx1
  have hx1' : 1 < x := hx1
  rw [ReciprocityTheory.Cheb.dedekindZeta_eq_idealZetaR F hx1'] at hx
  have h0 : 0 ≤ x - 1 := by linarith
  calc ‖((x : ℂ) - 1) * Z x‖ = (x - 1) * ‖Z x‖ := by
        rw [norm_mul, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_eq_abs, abs_of_nonneg h0]
    _ ≤ (x - 1) * ReciprocityTheory.Cheb.idealZetaR F x := mul_le_mul_of_nonneg_left (norm_le_idealZetaR F C Z hZ hx1') h0
    _ ≤ ‖((x : ℂ) - 1) * ((ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ)‖ := by
        rw [show ((x : ℂ) - 1) * ((ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ) =
          (((x - 1) * ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
        exact le_abs_self _
    _ ≤ dedekindZeta_residue F + 1 := hx.le
end GlobalTheory.ZetaPole
