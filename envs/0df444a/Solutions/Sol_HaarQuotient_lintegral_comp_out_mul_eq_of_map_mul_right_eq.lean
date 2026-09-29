-- Prove2me | solution 1 for HaarQuotient.lintegral_comp_out_mul_eq_of_map_mul_right_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bc8183f6-5bb7-54a2-a714-403bda94046b

import Definitions.Def_HaarQuotient
import Theorems.Thm_HaarQuotient_lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq
import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace HaarQuotientRightTranslate

variable {G : Type*} [Group G]

abbrev Q (H : Subgroup G) : Type _ := MulAction.orbitRel.Quotient H G

abbrev mkQ (H : Subgroup G) : G → Q H := Quotient.mk''

theorem mkQ_eq_iff (H : Subgroup G) (a b : G) : mkQ H a = mkQ H b ↔ ∃ x ∈ H, x * b = a := by
  rw [Quotient.eq'']
  change MulAction.orbitRel H G a b ↔ _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, x.2, hx⟩
  · rintro ⟨x, hx, hxb⟩
    exact ⟨⟨x, hx⟩, hxb⟩

theorem mkQ_mul_of_mem (H : Subgroup G) {x : G} (hx : x ∈ H) (g : G) : mkQ H (x * g) = mkQ H g :=
  (mkQ_eq_iff H _ _).2 ⟨x, hx, rfl⟩

theorem exists_out_mkQ (H : Subgroup G) (g : G) : ∃ x ∈ H, x * g = (mkQ H g).out := by
  have h : mkQ H ((mkQ H g).out) = mkQ H g := Quotient.out_eq' _
  exact (mkQ_eq_iff H _ _).1 h

def rt (H : Subgroup G) (k : G) : Q H → Q H :=
  Quotient.map' (fun g : G => g * k) fun a b hab => by
    change MulAction.orbitRel H G a b at hab
    change MulAction.orbitRel H G (a * k) (b * k)
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hab ⊢
    obtain ⟨x, hx⟩ := hab
    refine ⟨x, ?_⟩
    change (x : G) * (b * k) = a * k
    rw [← mul_assoc]
    congr 1

theorem rt_mkQ (H : Subgroup G) (k g : G) : rt H k (mkQ H g) = mkQ H (g * k) := rfl

theorem rt_comp_mkQ (H : Subgroup G) (k : G) : rt H k ∘ mkQ H = mkQ H ∘ fun g => g * k := rfl

theorem rt_rt (H : Subgroup G) (k k' : G) (q : Q H) : rt H k' (rt H k q) = rt H (k * k') q := by
  induction q using Quotient.inductionOn' with
  | h g =>
    change rt H k' (rt H k (mkQ H g)) = rt H (k * k') (mkQ H g)
    rw [rt_mkQ, rt_mkQ, rt_mkQ, mul_assoc]

theorem rt_one (H : Subgroup G) (q : Q H) : rt H 1 q = q := by
  induction q using Quotient.inductionOn' with
  | h g =>
    change rt H 1 (mkQ H g) = mkQ H g
    rw [rt_mkQ, mul_one]

variable [MeasurableSpace G] [MeasurableMul G]

theorem measurable_rt (H : Subgroup G) (k : G) : Measurable (rt H k) := by
  rw [measurable_from_quotient]
  change Measurable (rt H k ∘ mkQ H)
  rw [rt_comp_mkQ]
  exact measurable_quotient_mk''.comp (measurable_mul_const k)

def rtEquiv (H : Subgroup G) (k : G) : Q H ≃ᵐ Q H where
  toFun := rt H k
  invFun := rt H k⁻¹
  left_inv q := by rw [rt_rt, mul_inv_cancel, rt_one]
  right_inv q := by rw [rt_rt, inv_mul_cancel, rt_one]
  measurable_toFun := measurable_rt H k
  measurable_invFun := measurable_rt H k⁻¹

theorem rtEquiv_apply (H : Subgroup G) (k : G) (q : Q H) : rtEquiv H k q = rt H k q := rfl

end HaarQuotientRightTranslate

namespace HaarQuotientRightTranslate

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

theorem sigmaFinite_subgroupHaar (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] : SigmaFinite μH := by
  haveI : LocallyCompactSpace H := hH.locallyCompactSpace
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace H := sigmaCompactSpace_of_locallyCompact_secondCountable
  infer_instance

theorem map_rtEquiv_measure (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (k : G) (hμk : Measure.map (· * k) μ = μ) :
    Measure.map (rtEquiv H k) (HaarQuotient.measure μ H μH) = HaarQuotient.measure μ H μH := by
  haveI : SigmaFinite μH := sigmaFinite_subgroupHaar H hH μH
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply (rtEquiv H k).measurable hA]
  have hA' : MeasurableSet ((rtEquiv H k) ⁻¹' A) := (rtEquiv H k).measurable hA
  unfold HaarQuotient.measure
  rw [Measure.map_apply measurable_quotient_mk'' hA', Measure.map_apply measurable_quotient_mk'' hA,
    withDensity_apply _ (measurable_quotient_mk'' hA'), withDensity_apply _ (measurable_quotient_mk'' hA),
    ← lintegral_indicator (measurable_quotient_mk'' hA'), ← lintegral_indicator (measurable_quotient_mk'' hA)]

  set F : G → ℝ≥0∞ := ((Quotient.mk'' : G → Q H) ⁻¹' A).indicator fun _ => (1 : ℝ≥0∞) with hF
  have hFm : Measurable F := (measurable_one.indicator (measurable_quotient_mk'' hA))
  have hFH : ∀ x ∈ H, ∀ g : G, F (x * g) = F g := by
    intro x hx g
    have hmem : (x * g ∈ (Quotient.mk'' : G → Q H) ⁻¹' A) ↔ (g ∈ (Quotient.mk'' : G → Q H) ⁻¹' A) := by
      rw [Set.mem_preimage, Set.mem_preimage]
      have : (Quotient.mk'' (x * g) : Q H) = Quotient.mk'' g := mkQ_mul_of_mem H hx g
      rw [this]
    by_cases hg : g ∈ (Quotient.mk'' : G → Q H) ⁻¹' A
    · rw [hF, Set.indicator_of_mem hg, Set.indicator_of_mem (hmem.2 hg)]
    · rw [hF, Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h => hg (hmem.1 h))]
  have h1 : ((Quotient.mk'' : G → Q H) ⁻¹' ((rtEquiv H k) ⁻¹' A)).indicator (HaarQuotient.density H μH) =
      fun g => HaarQuotient.density H μH g * F (g * k) := by
    funext g
    have hiff : g ∈ (Quotient.mk'' : G → Q H) ⁻¹' ((rtEquiv H k) ⁻¹' A) ↔
        g * k ∈ (Quotient.mk'' : G → Q H) ⁻¹' A := by
      rw [Set.mem_preimage, Set.mem_preimage, Set.mem_preimage]
      exact Iff.rfl
    by_cases hg : g * k ∈ (Quotient.mk'' : G → Q H) ⁻¹' A
    · rw [Set.indicator_of_mem (hiff.2 hg), hF, Set.indicator_of_mem hg, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hg (hiff.1 h)), hF, Set.indicator_of_notMem hg, mul_zero]
  have h2 : ((Quotient.mk'' : G → Q H) ⁻¹' A).indicator (HaarQuotient.density H μH) =
      fun g => HaarQuotient.density H μH g * F g := by
    funext g
    by_cases hg : g ∈ (Quotient.mk'' : G → Q H) ⁻¹' A
    · rw [Set.indicator_of_mem hg, hF, Set.indicator_of_mem hg, mul_one]
    · rw [Set.indicator_of_notMem hg, hF, Set.indicator_of_notMem hg, mul_zero]
  rw [h1, h2]
  exact HaarQuotient.lintegral_density_mul_comp_mul_right_eq_of_map_mul_right_eq μ H hH μH F hFm hFH k hμk

theorem main (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (k : G)
    (hμk : Measure.map (· * k) μ = μ) :
    ∫⁻ q : Q H, f (q.out * k) ∂(HaarQuotient.measure μ H μH) =
      ∫⁻ q : Q H, f q.out ∂(HaarQuotient.measure μ H μH) := by

  have hpt : ∀ q : Q H, f (q.out * k) = f ((rtEquiv H k q).out) := by
    intro q
    induction q using Quotient.inductionOn' with
    | h g =>
      change f ((mkQ H g).out * k) = f ((rt H k (mkQ H g)).out)
      rw [rt_mkQ]
      obtain ⟨x, hx, hxg⟩ := exists_out_mkQ H g
      obtain ⟨y, hy, hyg⟩ := exists_out_mkQ H (g * k)
      rw [← hxg, ← hyg, mul_assoc, hfH x hx, hfH y hy]
  simp_rw [hpt]

  have h := lintegral_map_equiv (μ := HaarQuotient.measure μ H μH) (fun q : Q H => f q.out) (rtEquiv H k)
  rw [map_rtEquiv_measure μ H hH μH k hμk] at h
  exact h.symm

end HaarQuotientRightTranslate

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ENNReal) (hfH : ∀ x ∈ H, ∀ g : G, f (x * g) = f g) (k : G)
    (hμk : Measure.map (· * k) μ = μ) :
    ∫⁻ q : MulAction.orbitRel.Quotient H G, f (q.out * k) ∂(HaarQuotient.measure μ H μH) =
      ∫⁻ q : MulAction.orbitRel.Quotient H G, f q.out ∂(HaarQuotient.measure μ H μH) :=
  HaarQuotientRightTranslate.main μ H hH μH f hfH k hμk

end

end S_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq
end P2MW
export P2MW.S_HaarQuotient_lintegral_comp_out_mul_eq_of_map_mul_right_eq (solution)
