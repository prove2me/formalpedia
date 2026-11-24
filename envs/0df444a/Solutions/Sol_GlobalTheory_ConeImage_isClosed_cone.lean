-- Prove2me | solution 1 for GlobalTheory.ConeImage.isClosed_cone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:58:44.271482+00:00
-- url     : https://prove2.me/submissions/92bd36a3-93c2-4b33-8c42-a49746506e11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Change
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsNhdsSubsetRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.PTheta Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ConeImage
namespace GlobalTheory.ConeImage
theorem _root_.solution {E ι : Type*} [TopologicalSpace E] {f : E → ι → ℂ} (hf : Continuous f)
    (h0 : ∀ z, f z ≠ 0) {K : Set E} (hK : IsCompact K) :
    IsClosed {p : ι → ℂ | ∃ t : ℂ, ∃ z ∈ K, p = t • f z} := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have h1 : IsClosed {x : (ι → ℂ) × K | ∀ c c', x.1 c * f x.2 c' = x.1 c' * f x.2 c} := by
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun c => isClosed_iInter fun c' => isClosed_eq ?_ ?_ <;> fun_prop
  convert isClosedMap_fst_of_compactSpace _ h1 using 1
  ext p
  constructor
  · rintro ⟨t, z, hz, rfl⟩
    refine ⟨(t • f z, ⟨z, hz⟩), fun c c' => ?_, rfl⟩
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rintro ⟨⟨p, z, hz⟩, h, rfl⟩
    obtain ⟨c, hc⟩ := Function.ne_iff.mp (h0 z)
    have hc' : f z c ≠ 0 := hc
    refine ⟨p c / f z c, z, hz, ?_⟩
    ext c'
    have := h c c'
    simp only at this
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
    linear_combination -this
end GlobalTheory.ConeImage
