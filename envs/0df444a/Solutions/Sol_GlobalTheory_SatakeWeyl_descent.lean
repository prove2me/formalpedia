-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:49:18.782796+00:00
-- url     : https://prove2.me/submissions/c68457fe-d832-46fc-97ea-951610b3b37a

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CellSumTwoStageDescentUnipotent
import Theorems.Thm_GlobalTheory_SatakeWeyl_finsum_partition
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution : GlobalTheory.SatakeWeyl.Descent := by
  intro G A _ _ K N N' ι h g hf hle hN hdec hK hconj
  have key := finsum_partition (fun x : G ⧸ K => h x.out)
    (fun x => ∃ u ∈ N, ∃ k ∈ K, x.out = g * u * k)
    (fun (y : A ⧸ K.comap ι) x => ∃ u ∈ N', ∃ k ∈ K, x.out = g * ι y.out * u * k) hf ?_ ?_
  · unfold cellSum
    convert key
  · intro x
    constructor
    · rintro ⟨u, hu, k, hk, e⟩
      obtain ⟨a, u', hu', rfl⟩ := hdec u hu
      obtain ⟨⟨u₀, hu₀⟩, e₀⟩ := QuotientGroup.mk_out_eq_mul (K.comap ι) a
      refine ⟨QuotientGroup.mk a, ι u₀⁻¹ * u' * (ι u₀⁻¹)⁻¹, hconj _ _ hu', ι u₀⁻¹ * k,
        K.mul_mem (by rw [map_inv]; exact K.inv_mem hu₀) hk, ?_⟩
      rw [e, e₀]
      simp only [map_mul, map_inv]
      group
    · rintro ⟨y, u, hu, k, hk, e⟩
      exact ⟨ι y.out * u, N.mul_mem (hN _) (hle hu), k, hk, by rw [e]; group⟩
  · rintro x y y' ⟨u₁, hu₁, k₁, hk₁, e₁⟩ ⟨u₂, hu₂, k₂, hk₂, e₂⟩
    have e : ι y.out * u₁ * k₁ = ι y'.out * u₂ * k₂ := by
      apply mul_left_cancel (a := g)
      have := e₁.symm.trans e₂
      simpa only [mul_assoc] using this
    set b := y'.out⁻¹ * y.out with hb
    have hb' : ι b ∈ K := by
      refine hK b (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) (N'.mul_mem (hconj _ _ (N'.inv_mem hu₂)) hu₁) ?_
      have : ι b * (ι b⁻¹ * u₂⁻¹ * (ι b⁻¹)⁻¹ * u₁) = k₂ * k₁⁻¹ := by
        have e' : ι y.out * u₁ = ι y'.out * u₂ * k₂ * k₁⁻¹ := by rw [← e]; group
        calc _ = u₂⁻¹ * (ι y'.out)⁻¹ * (ι y.out * u₁) := by
              simp only [hb, map_mul, map_inv]; group
          _ = _ := by rw [e']; group
      rw [this]
      exact K.mul_mem hk₂ (K.inv_mem hk₁)
    rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
    exact (QuotientGroup.eq.2 hb').symm
end GlobalTheory.SatakeWeyl
