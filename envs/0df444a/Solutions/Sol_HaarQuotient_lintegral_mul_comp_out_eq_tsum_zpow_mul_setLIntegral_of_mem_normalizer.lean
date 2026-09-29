-- Prove2me | solution 1 for HaarQuotient.lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/728e5d7f-a286-5d62-90ce-fb10689b31c4

import Definitions.Def_HaarQuotient
import Theorems.Thm_MeasureTheory_lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul
import Theorems.Thm_HaarQuotient_lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

namespace HaarQuotient
p2m_export "HaarQuotient" "measure lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer"
p2m_open "HaarQuotient"

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

end HaarQuotient

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (b : G) (hb : ∀ y : G, y ∈ H ↔ b * y * b⁻¹ ∈ H) (D : ℝ≥0∞) (hD₀ : D ≠ 0) (hD : D ≠ ∞)
    (hbD : ∀ F : H → ℝ≥0∞, Measurable F →
      ∫⁻ x, F ⟨b * (x : G) * b⁻¹, (hb (x : G)).mp x.2⟩ ∂μH = D * ∫⁻ x, F x ∂μH)
    (m : G → ℤ) (hm : Measurable m) (hmH : ∀ x ∈ H, ∀ g : G, m (x * g) = m g)
    (hmb : ∀ g : G, m (b * g) = m g + 1)
    (h : G → ℝ≥0∞) (hh : Measurable h) (hhH : ∀ x ∈ H, ∀ g : G, h (x * g) = h g)
    (hhb : ∀ g : G, h (b * g) = h g)
    (Φ : ℤ → ℝ≥0∞) :
    ∫⁻ q, h q.out * Φ (m q.out) ∂(HaarQuotient.measure μ H μH) =
      (∑' n : ℤ, D ^ n * Φ n) *
        ∫⁻ q in {q : MulAction.orbitRel.Quotient H G | m q.out = 0}, h q.out ∂(HaarQuotient.measure μ H μH) := by
  set ν := HaarQuotient.measure μ H μH with hν
  set T := HaarQuotient.leftTranslateEquiv H b hb with hT_def

  have hT : ∀ s : Set (MulAction.orbitRel.Quotient H G), MeasurableSet s → ν (T '' s) = D * ν s := by
    intro s hs

    set f : G → ℝ≥0∞ := fun g => s.indicator 1 (Quotient.mk'' g) with hf_def
    have hf : Measurable f := (measurable_one.indicator hs).comp measurable_quotient_mk''
    have hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g := by
      intro x hx g
      simp only [hf_def]
      congr 1
      exact Quotient.sound' (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨x, hx⟩, rfl⟩))
    have key := HaarQuotient.lintegral_comp_inv_mul_out_eq_mul_lintegral_of_mem_normalizer μ H hH μH b hb D hbD
      f hf hfH

    have hR : ∫⁻ q, f q.out ∂ν = ν s := by
      have : ∀ q : MulAction.orbitRel.Quotient H G, f q.out = s.indicator 1 q := fun q => by
        simp only [hf_def, Quotient.out_eq']
      simp_rw [this, lintegral_indicator_one hs]

    have hL : ∫⁻ q, f (b⁻¹ * q.out) ∂ν = ν (T '' s) := by
      rw [MeasurableEquiv.image_eq_preimage_symm]
      have : ∀ q : MulAction.orbitRel.Quotient H G, f (b⁻¹ * q.out) = (T.symm ⁻¹' s).indicator 1 q := by
        intro q
        have hq : (Quotient.mk'' (b⁻¹ * q.out) : MulAction.orbitRel.Quotient H G) = T.symm q :=
          (HaarQuotient.leftTranslateEquiv_symm_apply_eq_mk H b hb q).symm
        simp only [hf_def, hq]
        exact (Set.indicator_comp_right _).symm
      simp_rw [this]
      exact lintegral_indicator_one (T.symm.measurable hs)
    rw [← hL, ← hR, key]

  have hm' : Measurable fun q : MulAction.orbitRel.Quotient H G => m q.out := HaarQuotient.measurable_comp_out H m hm hmH
  have hh' : Measurable fun q : MulAction.orbitRel.Quotient H G => h q.out := HaarQuotient.measurable_comp_out H h hh hhH
  have hmT : ∀ q, m (T q).out = m q.out + 1 := by
    intro q
    obtain ⟨x, hx⟩ := HaarQuotient.leftTranslateEquiv_out H b hb q
    rw [hx, hmH _ x.2, hmb]
  have hhT : ∀ q, h (T q).out = h q.out := by
    intro q
    obtain ⟨x, hx⟩ := HaarQuotient.leftTranslateEquiv_out H b hb q
    rw [hx, hhH _ x.2, hhb]
  exact MeasureTheory.lintegral_mul_comp_eq_tsum_zpow_mul_setLIntegral_of_measure_image_eq_mul ν T D hD₀ hD hT
    (fun q => m q.out) hm' hmT (fun q => h q.out) hh' hhT Φ

end S_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer
end P2MW
export P2MW.S_HaarQuotient_lintegral_mul_comp_out_eq_tsum_zpow_mul_setLIntegral_of_mem_normalizer (solution)
