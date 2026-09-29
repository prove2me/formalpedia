-- Prove2me | solution 1 for HaarQuotient.integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/311eb398-6ec9-5e24-91a0-35f286451eb4

import Mathlib
import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer
import Theorems.Thm_HaarQuotient_lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal

namespace PeelC

variable {G : Type*} [Group G] (H : Subgroup G)

theorem exists_out_mk_eq (g : G) :
    ∃ x : H, (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out = (x : G) * g := by
  obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (@Quotient.mk_out _ (MulAction.orbitRel H G) g))
  exact ⟨x, hx.symm⟩

theorem comp_out_comp_mk_eq {β : Type*} (f : G → β) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    (fun q : MulAction.orbitRel.Quotient H G => f q.out) ∘ (Quotient.mk'' : G → _) = f := by
  funext g
  obtain ⟨x, hx⟩ := exists_out_mk_eq H g
  simp only [Function.comp_apply]
  rw [hx]
  exact hfH _ x.2 g

theorem measurable_comp_out [MeasurableSpace G] {β : Type*} [MeasurableSpace β] (f : G → β) (hf : Measurable f)
    (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) :
    Measurable (fun q : MulAction.orbitRel.Quotient H G => f q.out) :=
  measurable_from_quotient.mpr (by rw [comp_out_comp_mk_eq H f hfH]; exact hf)

def leftTranslate (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) :
    MulAction.orbitRel.Quotient H G → MulAction.orbitRel.Quotient H G :=
  Quotient.map' (fun g => b * g) (by
    intro g₁ g₂ h
    obtain ⟨x, hx⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
    refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨b * (x : G) * b⁻¹, (hb _).mp x.2⟩, ?_⟩)
    rw [Subgroup.smul_def, smul_eq_mul] at hx ⊢
    rw [← hx]; group)

theorem leftTranslate_mk (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (g : G) :
    leftTranslate H b hb (Quotient.mk'' g) = Quotient.mk'' (b * g) := rfl

theorem inv_conj_iff (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) :
    ∀ y : G, y ∈ H ↔ b⁻¹ * y * b⁻¹⁻¹ ∈ H := by
  intro y
  rw [inv_inv, hb (b⁻¹ * y * b)]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem leftTranslate_leftTranslate_inv (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) :
    leftTranslate H b hb (leftTranslate H b⁻¹ (inv_conj_iff H b hb) q) = q := by
  induction q using Quotient.inductionOn' with
  | h g => rw [leftTranslate_mk, leftTranslate_mk, mul_inv_cancel_left]

theorem leftTranslate_inv_leftTranslate (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) :
    leftTranslate H b⁻¹ (inv_conj_iff H b hb) (leftTranslate H b hb q) = q := by
  induction q using Quotient.inductionOn' with
  | h g => rw [leftTranslate_mk, leftTranslate_mk, inv_mul_cancel_left]

variable [MeasurableSpace G]

theorem measurable_leftTranslate [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) :
    Measurable (leftTranslate H b hb) :=
  measurable_from_quotient.mpr (measurable_quotient_mk''.comp (measurable_const_mul b))

def leftTranslateEquiv [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) :
    MulAction.orbitRel.Quotient H G ≃ᵐ MulAction.orbitRel.Quotient H G where
  toFun := leftTranslate H b hb
  invFun := leftTranslate H b⁻¹ (inv_conj_iff H b hb)
  left_inv := leftTranslate_inv_leftTranslate H b hb
  right_inv := leftTranslate_leftTranslate_inv H b hb
  measurable_toFun := measurable_leftTranslate H b hb
  measurable_invFun := measurable_leftTranslate H b⁻¹ (inv_conj_iff H b hb)

theorem leftTranslateEquiv_apply [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) : leftTranslateEquiv H b hb q = leftTranslate H b hb q := rfl

theorem leftTranslateEquiv_symm_apply [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) :
    (leftTranslateEquiv H b hb).symm q = leftTranslate H b⁻¹ (inv_conj_iff H b hb) q := rfl

theorem leftTranslateEquiv_apply_eq_mk [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) : leftTranslateEquiv H b hb q = Quotient.mk'' (b * q.out) := by
  rw [leftTranslateEquiv_apply]
  conv_lhs => rw [← Quotient.out_eq' q]
  exact leftTranslate_mk H b hb q.out

theorem leftTranslateEquiv_symm_apply_eq_mk [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) : (leftTranslateEquiv H b hb).symm q = Quotient.mk'' (b⁻¹ * q.out) := by
  rw [leftTranslateEquiv_symm_apply]
  conv_lhs => rw [← Quotient.out_eq' q]
  exact leftTranslate_mk H b⁻¹ _ q.out

theorem leftTranslateEquiv_out [MeasurableMul G] (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H)
    (q : MulAction.orbitRel.Quotient H G) :
    ∃ x : H, (leftTranslateEquiv H b hb q).out = (x : G) * (b * q.out) := by
  rw [leftTranslateEquiv_apply_eq_mk]
  exact exists_out_mk_eq H (b * q.out)

end PeelC

open PeelC in
theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0) (hD₀ : D ≠ 0)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = (D : ℝ≥0∞) * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℂ) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (hint : IntegrableOn (fun q : MulAction.orbitRel.Quotient H G => h q.out)
      {q : MulAction.orbitRel.Quotient H G | m q.out = 0} (HaarQuotient.measure μ H μH))
    (Φ : ℤ → ℂ) (hΦ : Summable fun n : ℤ => (D : ℝ) ^ n * ‖Φ n‖) :
    Integrable (fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out)) (HaarQuotient.measure μ H μH) ∧
    (∫ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH)) =
      (∑' n : ℤ, ((D : ℝ) : ℂ) ^ n * Φ n) *
        ∫ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH) := by
  set ν := HaarQuotient.measure μ H μH with hν
  set T := PeelC.leftTranslateEquiv H b hb with hT_def
  have hD₀' : (D : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hD₀
  have hDtop : (D : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hDC : ((D : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr hD₀)

  have hT : ∀ s : Set (MulAction.orbitRel.Quotient H G), MeasurableSet s → ν (T '' s) = (D : ℝ≥0∞) * ν s := by
    intro s hs
    set f : G → ℝ≥0∞ := fun g => s.indicator 1 (Quotient.mk'' g) with hf_def
    have hf : Measurable f := (measurable_one.indicator hs).comp measurable_quotient_mk''
    have hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g := by
      intro x hx g
      simp only [hf_def]
      congr 1
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨x, hx⟩, rfl⟩))
    have key := HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer μ H hH μH b hb
      (D : ℝ≥0∞) hbD f hf hfH
    have hR : ∫⁻ q, f q.out ∂ν = ν s := by
      have : ∀ q : MulAction.orbitRel.Quotient H G, f q.out = s.indicator 1 q := fun q => by
        simp only [hf_def, Quotient.out_eq']
      simp_rw [this, lintegral_indicator_one hs]
    have hL : ∫⁻ q, f (b⁻¹ * q.out) ∂ν = ν (T '' s) := by
      rw [MeasurableEquiv.image_eq_preimage_symm]
      have : ∀ q : MulAction.orbitRel.Quotient H G, f (b⁻¹ * q.out) = (T.symm ⁻¹' s).indicator 1 q := by
        intro q
        have hq : (Quotient.mk'' (b⁻¹ * q.out) : MulAction.orbitRel.Quotient H G) = T.symm q :=
          (PeelC.leftTranslateEquiv_symm_apply_eq_mk H b hb q).symm
        simp only [hf_def, hq]
        exact (Set.indicator_comp_right _).symm
      simp_rw [this]
      exact lintegral_indicator_one (T.symm.measurable hs)
    rw [← hL, ← hR, key]

  have hm' : Measurable fun q : MulAction.orbitRel.Quotient H G => m q.out :=
    PeelC.measurable_comp_out H m hm hmH
  have hh' : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out :=
    PeelC.measurable_comp_out H h hh hhH
  have hmT : ∀ q, m (T q).out = m q.out + 1 := by
    intro q
    obtain ⟨x, hx⟩ := PeelC.leftTranslateEquiv_out H b hb q
    rw [hx, hmH _ x.2, hmb]
  have hhT : ∀ q, h (T q).out = h q.out := by
    intro q
    obtain ⟨x, hx⟩ := PeelC.leftTranslateEquiv_out H b hb q
    rw [hx, hhH _ x.2, hhb]
  have hhS : ∀ q, h (T.symm q).out = h q.out := fun q => by
    conv_rhs => rw [← MeasurableEquiv.apply_symm_apply T q]
    exact (hhT _).symm

  set A : ℤ → Set (MulAction.orbitRel.Quotient H G) := fun n => {q | m q.out = n} with hA_def
  have hA : ∀ n, MeasurableSet (A n) := fun n => hm' (measurableSet_singleton n)
  have hdisj : Pairwise (Function.onFun Disjoint A) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun q hqi hqj => hij ?_
    rw [hA_def] at hqi hqj
    exact hqi.symm.trans hqj
  have hunion : (⋃ n, A n) = Set.univ := by
    ext q; simp [hA_def]
  have hAsucc : ∀ n, A (n + 1) = T.symm ⁻¹' (A n) := by
    intro n; ext q
    simp only [hA_def, Set.mem_setOf_eq, Set.mem_preimage]
    have := hmT (T.symm q)
    rw [MeasurableEquiv.apply_symm_apply] at this
    rw [this]; exact add_left_inj 1

  have hmap : ν.map T.symm = (D : ℝ≥0∞) • ν := by
    refine Measure.ext fun s hs => ?_
    rw [Measure.map_apply T.symm.measurable hs, Measure.smul_apply, smul_eq_mul, ← hT s hs,
      MeasurableEquiv.image_eq_preimage_symm]

  have hΦ' : Summable fun n : ℤ => D ^ n * ‖Φ n‖₊ := by
    rw [← NNReal.summable_coe]
    simpa using hΦ
  have htsum : (∑' n : ℤ, (D : ℝ≥0∞) ^ n * ‖Φ n‖ₑ) ≠ ∞ := by
    have : ∀ n : ℤ, ((D ^ n * ‖Φ n‖₊ : ℝ≥0) : ℝ≥0∞) = (D : ℝ≥0∞) ^ n * ‖Φ n‖ₑ := fun n => by
      rw [ENNReal.coe_mul, ENNReal.coe_zpow hD₀]
      rfl
    simp_rw [← this]
    exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hΦ'
  have hmeas : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out) :=
    hh'.mul ((measurable_of_countable Φ).comp hm')
  have hfi : Integrable (fun q : MulAction.orbitRel.Quotient H G => h q.out * Φ (m q.out)) ν := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hpeel := HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer μ H hH μH
      b hb (D : ℝ≥0∞) hD₀' hDtop hbD m hm hmH hmb (fun g => ‖h g‖ₑ) hh.enorm
      (fun x hx g => by simp only [hhH x hx g]) (fun g => by simp only [hhb g]) (fun n => ‖Φ n‖ₑ)
    show ∫⁻ q, ‖h q.out * Φ (m q.out)‖ₑ ∂ν < ∞
    simp_rw [enorm_mul]
    rw [hpeel]
    exact ENNReal.mul_lt_top htsum.lt_top hint.2
  refine ⟨hfi, ?_⟩

  set I : ℤ → ℂ := fun n => ∫ q in A n, h q.out ∂ν with hI_def
  have hstep : ∀ n, I (n + 1) = ((D : ℝ) : ℂ) * I n := by
    intro n
    simp only [hI_def]
    rw [hAsucc]
    calc ∫ q in T.symm ⁻¹' A n, h q.out ∂ν
        = ∫ q, (T.symm ⁻¹' A n).indicator (fun q => h q.out) q ∂ν := (integral_indicator (T.symm.measurable (hA n))).symm
      _ = ∫ q, (A n).indicator (fun q => h q.out) (T.symm q) ∂ν := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
          simp only [Set.indicator, Set.mem_preimage, hhS]
      _ = ∫ q, (A n).indicator (fun q => h q.out) q ∂(ν.map T.symm) := (integral_map_equiv T.symm _).symm
      _ = ((D : ℝ) : ℂ) * ∫ q in A n, h q.out ∂ν := by
          rw [hmap, integral_smul_measure, integral_indicator (hA n), ENNReal.coe_toReal, Complex.real_smul]
  have hI : ∀ n : ℤ, I n = ((D : ℝ) : ℂ) ^ n * I 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
        rw [hstep, ih, ← mul_assoc, zpow_add_one₀ hDC, mul_comm (((D : ℝ) : ℂ) ^ (k : ℤ))]
    | pred k ih =>
        have h1 : I (-(k : ℤ)) = ((D : ℝ) : ℂ) * I (-(k : ℤ) - 1) := by
          rw [← hstep]; congr 1; ring
        have h2 : I (-(k : ℤ) - 1) = ((D : ℝ) : ℂ)⁻¹ * I (-(k : ℤ)) := by
          rw [h1, ← mul_assoc, inv_mul_cancel₀ hDC, one_mul]
        rw [h2, ih, ← mul_assoc, zpow_sub_one₀ hDC, mul_comm _⁻¹]

  have hlevel : ∀ n, ∫ q in A n, h q.out * Φ (m q.out) ∂ν = I n * Φ n := by
    intro n
    simp only [hI_def]
    rw [← integral_mul_const]
    refine setIntegral_congr_fun (hA n) fun q hq => ?_
    simp only [hA_def, Set.mem_setOf_eq] at hq
    simp only [hq]
  have hsplit : ∫ q, h q.out * Φ (m q.out) ∂ν = ∑' n, I n * Φ n := by
    rw [← setIntegral_univ, ← hunion, integral_iUnion hA hdisj hfi.integrableOn]
    exact tsum_congr hlevel
  rw [hsplit, ← tsum_mul_right]
  refine tsum_congr fun n => ?_
  rw [hI n]
  simp only [hI_def, hA_def]
  ring

end S_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer
end P2MW
export P2MW.S_HaarQuotient_integrable_and_integral_mul_comp_out_eq_tsum_mul_setIntegral_of_mem_normalizer (solution)
