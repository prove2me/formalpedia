-- Prove2me | solution 1 for GlobalTheory.ContinuousValuationExtension.valuation_eq_of_denseRange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:29.028548+00:00
-- url     : https://prove2.me/submissions/fc259bcf-072c-475e-805d-61322fad3728

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsContinuousExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open GlobalTheory GlobalTheory.ContinuousValuationExtension
namespace GlobalTheory.ContinuousValuationExtension
theorem _root_.solution {A B Γ ι : Type} [Field A] [Field B]
    [LinearOrderedCommGroupWithZero Γ] [Valued A Γ] [Valued B Γ] (φ : A →+* B)
    (hφ : Continuous φ) (j : ι → A) (hj : DenseRange j)
    (h : ∀ x : ι, (Valued.v (φ (j x)) : Γ) = Valued.v (j x)) (y : A) :
    (Valued.v (φ y) : Γ) = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  have hφy : φ y ≠ 0 := (map_ne_zero φ).2 hy

  have h1 : {z : A | (Valued.v z : Γ) = Valued.v y} ∈ nhds y :=
    Valued.locally_const ((Valuation.ne_zero_iff _).2 hy)
  have h2 : {z : A | (Valued.v (φ z) : Γ) = Valued.v (φ y)} ∈ nhds y :=
    hφ.continuousAt.preimage_mem_nhds (Valued.locally_const ((Valuation.ne_zero_iff _).2 hφy))
  obtain ⟨_, ⟨x, rfl⟩, hx1, hx2⟩ := hj.inter_nhds_nonempty (Filter.inter_mem h1 h2)
  have e1 : (Valued.v (j x) : Γ) = Valued.v y := hx1
  have e2 : (Valued.v (φ (j x)) : Γ) = Valued.v (φ y) := hx2
  rw [← e2, h x, e1]
end GlobalTheory.ContinuousValuationExtension
