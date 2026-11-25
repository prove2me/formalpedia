-- Prove2me | solution 1 for GlobalTheory.RealWeil.SchrFamily.tendsto_rhoSch_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:59:01.68327+00:00
-- url     : https://prove2.me/submissions/bcf4d816-3775-4ae4-88ae-24bc8ba4c320

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslationSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzCharacterSeminormBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchrodingerRepSchwartzPolynomialBound
import Theorems.Thm_GlobalTheory_RealWeil_SchrFamily_seminorm_rhoSch_sub_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.RealWeil Filter Topology
open scoped SchwartzMap RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.RealWeil GlobalTheory.RealWeil.SchrFamily
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil.SchrFamily
theorem _root_.solution (g : Sch l) : Tendsto (fun u => rhoSch u g) (𝓝 0) (𝓝 g) := by
  rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).tendsto_nhds _ g]
  intro i ε hε
  obtain ⟨q₁, q₂, q₃, M₁, M₂, M₃, hb⟩ := seminorm_rhoSch_sub_le (schwartzSeminormFamily ℂ _ ℂ i)
    ((schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_seminorm i)
  have hpc : Tendsto (fun u : l ⊕ l → ℝ => pPart u) (𝓝 0) (𝓝 0) := by
    have := (pCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hqc : Tendsto (fun u : l ⊕ l → ℝ => qPart u) (𝓝 0) (𝓝 0) := by
    have := (qCLM l).continuous.tendsto 0
    rw [map_zero] at this
    exact this
  have hpn : Tendsto (fun u : l ⊕ l → ℝ => ‖pPart u‖) (𝓝 0) (𝓝 0) := by simpa using hpc.norm
  have hqn : Tendsto (fun u : l ⊕ l → ℝ => ‖qPart u‖) (𝓝 0) (𝓝 0) := by simpa using hqc.norm
  have hk : Tendsto (fun u : l ⊕ l → ℝ => |⟪pPart u, qPart u⟫ / 2|) (𝓝 0) (𝓝 0) := by
    have := ((hpc.inner (𝕜 := ℝ) hqc).div_const 2).abs
    simpa using this
  have lim : Tendsto (fun u : l ⊕ l → ℝ => (‖qPart u‖ + |⟪pPart u, qPart u⟫ / 2|) * (1 + ‖qPart u‖) ^ M₁ *
          (‖pPart u‖ * (1 + ‖pPart u‖) ^ M₃ * q₃ g + q₁ g) + ‖pPart u‖ * (1 + ‖pPart u‖) ^ M₂ * q₂ g)
      (𝓝 0) (𝓝 0) := by
    have := (((hqn.add hk).mul ((hqn.const_add 1).pow M₁)).mul
      (((hpn.mul ((hpn.const_add 1).pow M₃)).mul_const (q₃ g)).add_const (q₁ g))).add
      ((hpn.mul ((hpn.const_add 1).pow M₂)).mul_const (q₂ g))
    simpa using this
  filter_upwards [lim.eventually (gt_mem_nhds hε)] with u hu
  exact (hb u g).trans_lt hu
end GlobalTheory.RealWeil.SchrFamily
