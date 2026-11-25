-- Prove2me | solution 1 for HcInf.lhu_key
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:21:26.835345+00:00
-- url     : https://prove2.me/submissions/342b9b2c-89d2-4c79-a59c-1923e1b91eb6

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExCayH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_CayDensExLHU
import Theorems.Thm_HcInf_lhu_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HcInf
open MeasureTheory Filter Topology
open scoped ENNReal NNReal Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace HcInf
theorem _root_.solution (m : Measure G) [m.IsHaarMeasure] (β : Measure G) (W V : Set G)
    (hinv : ∀ (h : G) (S : Set G), MeasurableSet S → S ⊆ W → (fun g => h * g) '' S ⊆ W →
      β ((fun g => h * g) '' S) = β S)
    (hVc : IsCompact V) (hVW : V ⊆ W) (hVW' : ∀ v ∈ V, v⁻¹ ∈ W) (hβV : β V ≠ ⊤) (hβVi : β V⁻¹ ≠ ⊤) :
    ∃ K : ℝ≥0∞, ∀ B : Set G, MeasurableSet B → B ⊆ V → m V * β B = K * m B := by

  have hVm : MeasurableSet V := hVc.isClosed.measurableSet
  have hVim : MeasurableSet V⁻¹ := hVc.inv.isClosed.measurableSet
  have hViW : V⁻¹ ⊆ W := fun x hx => by simpa using hVW' x⁻¹ hx
  choose r hr using fun z => lhu_right m z
  refine ⟨∫⁻ x in V⁻¹, r x ∂β, fun B hB hBV => ?_⟩
  haveI : IsFiniteMeasure (β.restrict V⁻¹) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hβVi⟩
  haveI : IsFiniteMeasure (β.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact lt_of_le_of_lt (measure_mono hBV) (lt_top_iff_ne_top.2 hβV)⟩
  have hmB : m B ≠ ⊤ := ne_top_of_le_ne_top hVc.measure_lt_top.ne (measure_mono hBV)
  have hE : MeasurableSet {p : G × G | p.2 * p.1 ∈ B} := (measurable_snd.mul measurable_fst) hB
  have hF : MeasurableSet {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} :=
    (measurable_snd.inv.mul measurable_fst) hVim
  have ha : ((β.restrict V⁻¹).prod m) {p : G × G | p.2 * p.1 ∈ B}
      = (∫⁻ x in V⁻¹, r x ∂β) * m B := by
    rw [Measure.prod_apply hE]
    calc _ = ∫⁻ x, r x * m B ∂(β.restrict V⁻¹) := lintegral_congr (fun x => hr x B hB)
      _ = (∫⁻ x in V⁻¹, r x ∂β) * m B := lintegral_mul_const' _ _ hmB
  have h1 : ∀ t : G, (β.restrict V⁻¹) ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B})
      = (β.restrict B) ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) := by
    intro t
    have hS : MeasurableSet ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B}) :=
      measurable_const_mul t hB
    have hT : MeasurableSet ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) :=
      measurable_const_mul t⁻¹ hVim
    rw [Measure.restrict_apply hS, Measure.restrict_apply hT]
    have himg : (fun g => t * g) '' ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B} ∩ V⁻¹)
        = (fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} ∩ B := by
      ext y
      constructor
      · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
        refine ⟨?_, hx1⟩
        show t⁻¹ * (t * x) ∈ V⁻¹
        rwa [inv_mul_cancel_left]
      · rintro ⟨hy1, hy2⟩
        refine ⟨t⁻¹ * y, ⟨?_, hy1⟩, mul_inv_cancel_left t y⟩
        show t * (t⁻¹ * y) ∈ B
        rwa [mul_inv_cancel_left]
    have hsub : (fun g => t * g) '' ((fun x => (x, t)) ⁻¹' {p : G × G | p.2 * p.1 ∈ B} ∩ V⁻¹) ⊆ W := by
      rw [himg]; exact fun y hy => hVW (hBV hy.2)
    rw [← himg]
    exact (hinv t _ (hS.inter hVim) (fun x hx => hViW hx.2) hsub).symm
  have hb : ((β.restrict V⁻¹).prod m) {p : G × G | p.2 * p.1 ∈ B} = m V * β B := by
    rw [Measure.prod_apply_symm hE]
    calc _ = ∫⁻ t, (β.restrict B) ((fun y => (y, t)) ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) ∂m :=
          lintegral_congr h1
      _ = ((β.restrict B).prod m) {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} :=
          (Measure.prod_apply_symm hF).symm
      _ = ∫⁻ y, m (Prod.mk y ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹}) ∂(β.restrict B) :=
          Measure.prod_apply hF
      _ = ∫⁻ y, m V ∂(β.restrict B) := by
          refine lintegral_congr (fun y => ?_)
          have hpre : Prod.mk y ⁻¹' {p : G × G | p.2⁻¹ * p.1 ∈ V⁻¹} = (fun t => y⁻¹ * t) ⁻¹' V := by
            ext t; simp [mul_inv_rev]
          rw [hpre, measure_preimage_mul]
      _ = m V * β B := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact hb.symm.trans ha
end HcInf
