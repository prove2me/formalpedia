-- Prove2me | solution 1 for GlobalTheory.Cyc.DiffSmall.norm_eval_le_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:27.873715+00:00
-- url     : https://prove2.me/submissions/ec6ad1e5-f450-4f3f-b6d7-0978934414b9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AvMono
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCycCycChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjectiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsTraceNormGe
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_norm_sum_le_of_le
import Theorems.Thm_GlobalTheory_Cyc_DiffSmall_mem_intPoly
import Theorems.Thm_GlobalTheory_isIntegral_padicInt_iff_norm_le_one
import Theorems.Thm_ReciprocityTheory_CA_ModDepthGE_mono


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Polynomial
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open GlobalTheory.Cyc.DiffSmall
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.DiffSmall
theorem _root_.solution {ι : Type*} (T : Finset ι) (r : ι → Om l) (hinj : Set.InjOn r T)
    (hr : ∀ k ∈ T, ‖r k‖ ≤ 1) {x : Om l} (hx : ‖x‖ ≤ 1) :
    ∀ Q ∈ intPoly l, (∀ k ∈ T, Q.eval (r k) = 0) → ‖Q.eval x‖ ≤ ∏ k ∈ T, ‖x - r k‖ := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro Q hQ _
    rw [Finset.prod_empty, eval_eq_sum_range]
    refine norm_sum_le_of_le _ _ zero_le_one fun n _ => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (mem_intPoly.1 hQ n) (by positivity) (pow_le_one₀ (norm_nonneg _) hx)
  | insert a T ha ih =>
    intro Q hQ hroot
    obtain ⟨Q₀, rfl⟩ := hQ
    let a₀ : integralClosure ℤ_[l] (Om l) :=
      ⟨r a, (isIntegral_padicInt_iff_norm_le_one _).2 (hr a (Finset.mem_insert_self _ _))⟩
    have h0 : Q₀.IsRoot a₀ := by
      have := hroot a (Finset.mem_insert_self _ _)
      rw [coe_mapRingHom, show r a = algebraMap _ (Om l) a₀ from rfl, eval_map, eval₂_at_apply] at this
      exact Subtype.ext this
    obtain ⟨Q₁, rfl⟩ := dvd_iff_isRoot.2 h0
    have he : ∀ z, eval z (mapRingHom (algebraMap (integralClosure ℤ_[l] (Om l)) (Om l))
        ((X - C a₀) * Q₁)) = (z - r a) * eval z (Q₁.map (algebraMap _ (Om l))) := by
      intro z
      simp [a₀]
    rw [he, Finset.prod_insert ha, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine ih (hinj.mono (by simp)) (fun k hk => hr k (Finset.mem_insert_of_mem hk)) _ ⟨Q₁, rfl⟩
      fun k hk => ?_
    have := hroot k (Finset.mem_insert_of_mem hk)
    rw [he] at this
    refine (mul_eq_zero.1 this).resolve_left fun h => ha ?_
    have := hinj (by simp [hk]) (by simp) (sub_eq_zero.1 h)
    exact this ▸ hk
end GlobalTheory.Cyc.DiffSmall
