-- Prove2me | solution 1 for GlobalTheory.EtaCompare.eta_eq_uq_eta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:01:12.082221+00:00
-- url     : https://prove2.me/submissions/bf16e8dc-ad4b-4dfe-9890-9d0729dd3f1d

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormLeIffValuationLe
import Theorems.Thm_GlobalTheory_EtaCompare_norm_eq_iff_valuation_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Matrix MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.EtaCompare
open WithZero
namespace GlobalTheory.EtaCompare
theorem _root_.solution : ∀ (K : UQ) (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (φ : K.E ≃+* E),
    (∀ y : K.E, ‖φ y‖ ≤ 1 ↔ y ∈ (algebraMap K.O K.E).range) →
    ∀ x : F, GlobalTheory.JR.eta x = ((K.eta (φ.symm (algebraMap F E x)) : ℚ) : ℂ) := by
  intro K F E _ _ _ _ hU φ hball x
  set v := (IsDiscreteValuationRing.maximalIdeal K.O).valuation K.E with hv
  have hn : ∀ t : F, ‖φ (φ.symm (algebraMap F E t))‖ = ‖t‖ := fun t => by
    rw [RingEquiv.apply_symm_apply, norm_algebraMap']
  have key : (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔
      ∃ y : F, v (φ.symm (algebraMap F E x)) = v (φ.symm (algebraMap F E y)) ^ 2 := by
    refine exists_congr fun y => ?_
    rw [← hn x, ← hn y, ← norm_pow, ← map_pow φ, norm_eq_iff_valuation_eq K φ hball, map_pow]

  obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
  obtain ⟨p, hp⟩ := hU.unram (φ π)
  have hvp : v (φ.symm (algebraMap F E p)) = exp (-1) := by
    rw [← hπ]
    refine ((norm_eq_iff_valuation_eq K φ hball _ _).1 ?_)
    rw [hn, hp]
  unfold GlobalTheory.JR.eta UQ.eta val
  rw [key]
  rw [← hv]
  by_cases hx : x = 0
  · subst hx
    simp only [map_zero, WithZero.log_zero, neg_zero, zpow_zero, Rat.cast_one]
    rw [if_pos ⟨0, by simp⟩]
  set z := φ.symm (algebraMap F E x) with hz
  have hz0 : z ≠ 0 := by simpa [z] using hx
  have hvz : v z ≠ 0 := (Valuation.ne_zero_iff v).2 hz0
  set m := log (v z) with hm
  have hiff : (∃ y : F, v z = v (φ.symm (algebraMap F E y)) ^ 2) ↔ Even m := by
    constructor
    · rintro ⟨y, hy⟩
      refine ⟨log (v (φ.symm (algebraMap F E y))), ?_⟩
      rw [hm, hy, log_pow, two_nsmul]
    · rintro ⟨l, hl⟩
      refine ⟨p ^ (-l), ?_⟩
      have hl' : log (v z) = l + l := hl
      rw [map_zpow₀, map_zpow₀, map_zpow₀, hvp, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, ← WithZero.exp_log hvz, hl']
      congr 1
      simp only [smul_eq_mul, nsmul_eq_mul]
      push_cast
      ring
  split_ifs with h
  · rw [Even.neg_one_zpow ((hiff.1 h).neg)]; simp
  · have ho : Odd (-m) := (Int.not_even_iff_odd.1 (fun he => h (hiff.2 (by simpa using he.neg))))
    rw [Odd.neg_one_zpow ho]; simp
end GlobalTheory.EtaCompare
