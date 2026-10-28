-- Prove2me | solution 1 for LipschitzEnvelope.tendsto_of_linear_upper
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:53:27.763039+00:00
-- url     : https://prove2.me/submissions/3972453e-47cd-44d7-a62c-981efb1f85cc

import Mathlib
import Definitions.Def_WassDDRO_Extremal_Setting
import Definitions.Def_WassDDRO_Reduction_Setting
import Theorems.Thm_LipschitzEnvelope_exists_penalty_le_of_lt

-- carved verbatim out of submission 9d9b1da1-23a8-4b1d-b0ad-3d6a8366c2eb, lines 855-928

section
set_option autoImplicit false
open Filter Topology

theorem solution {E : Type*} [NormedAddCommGroup E]
    (Ξ : Set E) (L : E → EReal) (xhat : E) (hxhat : xhat ∈ Ξ) (C A : ℝ)
    (husc : UpperSemicontinuousAt L xhat)
    (hupper : ∀ x ∈ Ξ, L x ≤ ((C+A*‖x-xhat‖ : ℝ) : EReal)) :
    Tendsto (fun lam : ℝ => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal))
      atTop (𝓝 (L xhat)) := by
  let F : ℝ → EReal := fun lam => ⨆ x ∈ Ξ, L x-((lam*‖x-xhat‖ : ℝ) : EReal)
  have hanti : Antitone F := by
    intro a b hab
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply le_trans _ (le_iSup₂_of_le x hx le_rfl)
    apply EReal.sub_le_sub le_rfl
    exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  have hle : L xhat ≤ ⨅ lam, F lam := by
    apply le_iInf
    intro lam
    have hh : L xhat-((lam*‖xhat-xhat‖ : ℝ) : EReal) ≤ F lam :=
      le_iSup₂_of_le xhat hxhat le_rfl
    simpa [F] using hh
  have hge : (⨅ lam, F lam) ≤ L xhat := by
    by_contra hh
    obtain ⟨r,hr,hri⟩ := EReal.exists_between_coe_real (lt_of_not_ge hh)
    obtain ⟨lam,_,hlam⟩ := LipschitzEnvelope.exists_penalty_le_of_lt Ξ L xhat C A r husc hupper hr
    exact (not_le_of_gt hri) ((iInf_le F lam).trans hlam)
  have he : (⨅ lam, F lam)=L xhat := le_antisymm hge hle
  rw [←he]
  exact tendsto_atTop_iInf hanti

end
