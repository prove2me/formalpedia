-- Prove2me | solution 1 for GlobalTheory.RootEx.exists_SB_supported_integral_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:04:57.635692+00:00
-- url     : https://prove2.me/submissions/919eeebe-7c63-446b-bb8e-103948c1dc00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierTransformInversionLocalFieldPi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSchwartzBruhatSupportedNhdsIntegralOne
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_exists_box_subset
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isCompact_box
import Theorems.Thm_GlobalTheory_SplitWeil_FourierPi_isOpen_box
import Theorems.Thm_GlobalTheory_SplitWeil_add_mem_cball
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_cball
import Theorems.Thm_GlobalTheory_SplitWeil_neg_mem_cball

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
namespace GlobalTheory.RootEx
private theorem isLocallyConstant_indicator_const_of_isClopen {X : Type} [TopologicalSpace X] {B : Set X}
    (hB : IsClopen B) (c : ℂ) : IsLocallyConstant (B.indicator fun _ => c) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨B, hB.isOpen, hx, fun y hy => ?_⟩
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
  · refine ⟨Bᶜ, hB.isClosed.isOpen_compl, hx, fun y hy => ?_⟩
    rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
private theorem sigmaCompactSpace_of_isNonarchimedeanLocalField (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] : SigmaCompactSpace k := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ValueGroupWithZero k)ˣ)
  refine SigmaCompactSpace.of_countable
    (Set.range fun m : ℤ => {x : k | valuation k x ≤ ((g ^ m : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)})
    (Set.countable_range _) ?_ ?_
  · rintro _ ⟨m, rfl⟩
    exact IsNonarchimedeanLocalField.isCompact_closedBall k _
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x = 0
    · subst hx
      refine Set.mem_sUnion.mpr ⟨_, ⟨0, rfl⟩, ?_⟩
      rw [Set.mem_ofPred_eq, map_zero]
      exact zero_le
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (hg (Units.mk0 (valuation k x) ((map_ne_zero (valuation k)).mpr hx)))
      refine Set.mem_sUnion.mpr ⟨_, ⟨m, rfl⟩, ?_⟩
      rw [Set.mem_ofPred_eq, hm, Units.val_mk0]
end GlobalTheory.RootEx
end

set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx
open GlobalTheory.SplitWeil.FourierPi
namespace GlobalTheory.RootEx
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (ν : Measure k) [ν.IsAddHaarMeasure] (U : Set (n → k)) (_ : U ∈ nhds (0 : n → k)), ∃ Ψ : SB (n → k), (∀ y, y ∉ U → Ψ.1 y = 0) ∧ ∫ y, Ψ.1 y ∂(Measure.pi fun _ => ν) = 1 := by
  intro k _ _ _ _ _ _ n _ _ ν _ U hU
  have := sigmaCompactSpace_of_isNonarchimedeanLocalField k
  obtain ⟨s, hsU⟩ := exists_box_subset (k := k) (n := n) hU
  have hBo : IsOpen (box (k := k) n s) := isOpen_box s
  have hBc : IsCompact (box (k := k) n s) := isCompact_box s
  have hBcl : IsClosed (box (k := k) n s) := isClosed_set_pi fun _ _ =>
    AddSubgroup.isClosed_of_isOpen
      { carrier := cball s
        zero_mem' := by
          show valuation k (0 : k) ≤ valuation k (s : k)
          rw [map_zero]
          exact zero_le
        add_mem' := add_mem_cball
        neg_mem' := neg_mem_cball } (isOpen_cball s)
  have hBm : MeasurableSet (box (k := k) n s) :=
    MeasurableSet.univ_pi fun _ => (isOpen_cball s).measurableSet
  have h0 : (0 : n → k) ∈ box (k := k) n s := by
    intro i _
    show valuation k (0 : k) ≤ valuation k (s : k)
    rw [map_zero]
    exact zero_le
  have hpos : 0 < (Measure.pi fun _ : n => ν) (box n s) := hBo.measure_pos _ ⟨0, h0⟩
  have hfin : (Measure.pi fun _ : n => ν) (box n s) < ⊤ := hBc.measure_lt_top
  have hreal : (Measure.pi fun _ : n => ν).real (box n s) ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' hfin.ne).ne'
  set c : ℂ := (((Measure.pi fun _ : n => ν).real (box n s) : ℝ) : ℂ)⁻¹ with hc
  refine ⟨⟨(box (k := k) n s).indicator fun _ => c,
    isLocallyConstant_indicator_const_of_isClopen ⟨hBcl, hBo⟩ c,
    HasCompactSupport.intro' hBc hBcl fun y hy => Set.indicator_of_notMem hy _⟩, ?_, ?_⟩
  · intro y hy
    show (box (k := k) n s).indicator (fun _ => c) y = 0
    exact Set.indicator_of_notMem (fun hb => hy (hsU hb)) _
  · show ∫ y, (box (k := k) n s).indicator (fun _ => c) y ∂(Measure.pi fun _ => ν) = 1
    rw [integral_indicator_const c hBm, Complex.real_smul, hc,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hreal)]
end GlobalTheory.RootEx
