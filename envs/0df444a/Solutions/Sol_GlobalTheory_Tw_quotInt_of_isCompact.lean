-- Prove2me | solution 1 for GlobalTheory.Tw.quotInt_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:17.75364+00:00
-- url     : https://prove2.me/submissions/a53de167-9247-4ad3-aa7e-5092089bafe1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_BruhatFunctionExistsClosedSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_QuotIntegrableIffCutoff
import Theorems.Thm_GlobalTheory_Tw_quotInt_eq_cutoff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}
variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]
namespace GlobalTheory.Tw
theorem _root_.solution (hT : IsCompact (T : Set G)) {F : G → ℂ} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ((μT.real Set.univ : ℝ) : ℂ)⁻¹ * ∫ x, F x ∂μ := by
  have : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have h0 : μT Set.univ ≠ 0 := (isOpen_univ.measure_pos μT ⟨1, trivial⟩).ne'
  have h1 : μT Set.univ ≠ ⊤ := measure_ne_top _ _
  have hβ : IsCosetCutoff T μT fun _ => (μT Set.univ).toNNReal⁻¹ := ⟨measurable_const, fun x => by
    rw [lintegral_const, ENNReal.coe_inv (ENNReal.toNNReal_ne_zero.2 ⟨h0, h1⟩), ENNReal.coe_toNNReal h1,
      ENNReal.inv_mul_cancel h0 h1]⟩
  rw [quotInt_eq_cutoff hT.isClosed hβ hm hF, integral_smul]
  simp [Measure.real, ENNReal.toReal]
end GlobalTheory.Tw
