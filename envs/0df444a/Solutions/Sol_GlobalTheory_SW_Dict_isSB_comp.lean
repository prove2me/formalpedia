-- Prove2me | solution 1 for GlobalTheory.SW.Dict.isSB_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:27:40.13789+00:00
-- url     : https://prove2.me/submissions/01f2dc03-396e-4cc3-a68c-3bae3b669233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Theorems.Thm_GlobalTheory_SW_Dict_intM_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Dict
noncomputable section
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.Dict
namespace _root_.GlobalTheory.SW.Dict
theorem _root_.solution {K K' κ ι κ' ι' : Type} [Field K] [Field K']
    (e : Matrix κ ι K →+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, _root_.GlobalTheory.SW.IntM x → _root_.GlobalTheory.SW.IntM (D • e x))
    (h2 : ∀ x, _root_.GlobalTheory.SW.IntM (e x) → _root_.GlobalTheory.SW.IntM (D' • x))
    {φ : Matrix κ' ι' K' → ℂ} (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB (fun x => φ (e x)) := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  simp only [Nat.cast_smul_eq_nsmul] at hsupp hper
  refine ⟨D * (D' * R), by positivity, ?_, ?_⟩ <;> simp only [Nat.cast_smul_eq_nsmul]
  · intro x hx
    have hx' := hsupp (e x) hx
    have h3 : _root_.GlobalTheory.SW.IntM (e (R • x)) := by rwa [map_nsmul]
    have h4 := _root_.GlobalTheory.SW.Dict.intM_nsmul D (h2 _ h3)
    rwa [smul_smul, smul_smul, mul_assoc] at h4
  · intro x y hy
    have h3 := _root_.GlobalTheory.SW.Dict.intM_nsmul D' (h1 y hy)
    have h4 := hper (e x) _ h3
    simp only [map_add, map_nsmul]
    rw [← h4, smul_smul, smul_smul]
    congr 2
    ring_nf
end _root_.GlobalTheory.SW.Dict
end GlobalTheory.SW.Dict
