-- Prove2me | solution 1 for HaarQuotient.measurable_lintegral_mul_out
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f05249d6-277f-51de-a08c-110798da66ea

import Definitions.Def_HaarQuotient
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HaarQuotient_measurable_lintegral_mul_out

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

open scoped ENNReal NNReal Pointwise Topology

noncomputable section

namespace HaarDisM65

open HaarQuotient

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

private noncomputable def orb (H : Subgroup G) (μH : Measure H) (φ : G → ℝ≥0∞) (g : G) : ℝ≥0∞ :=
  ∫⁻ x : H, φ ((x : G) * g) ∂μH

section Orbit

variable (H : Subgroup G) (μH : Measure H)

private theorem orb_mul_left [μH.IsMulRightInvariant] (φ : G → ℝ≥0∞) (x₀ : H) (g : G) :
    orb H μH φ ((x₀ : G) * g) = orb H μH φ g := by
  unfold orb
  have : (fun x : H => φ ((x : G) * ((x₀ : G) * g))) = fun x : H => φ (((x * x₀ : H) : G) * g) := by
    funext x
    simp [mul_assoc]
  rw [this]
  exact lintegral_mul_right_eq_self (fun x : H => φ ((x : G) * g)) x₀

private theorem orb_out_mk [μH.IsMulRightInvariant] (φ : G → ℝ≥0∞) (g : G) :
    orb H μH φ (Quotient.mk (MulAction.orbitRel H G) g).out = orb H μH φ g := by
  have h : (MulAction.orbitRel H G) ((Quotient.mk (MulAction.orbitRel H G) g).out) g :=
    Quotient.mk_out g
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨x₀, hx₀⟩ := h
  rw [← hx₀]
  exact orb_mul_left H μH φ x₀ g

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] in

private theorem exists_mul_eq_out (g : G) :
    ∃ x₀ : H, (x₀ : G) * g = (Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out := by
  have h : (MulAction.orbitRel H G) ((Quotient.mk'' g : MulAction.orbitRel.Quotient H G).out) g :=
    Quotient.mk_out g
  rw [MulAction.orbitRel_apply] at h
  obtain ⟨x₀, hx₀⟩ := h
  exact ⟨x₀, hx₀⟩

private theorem measurable_comp_mul {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : G × H => φ ((p.2 : G) * p.1) := by
  apply hφ.comp
  have : Continuous fun p : G × H => (p.2 : G) * p.1 := by
    exact (continuous_subtype_val.comp continuous_snd).mul continuous_fst
  exact this.measurable

private theorem measurable_subtype_mul (g : G) : Measurable fun x : H => (x : G) * g :=
  (continuous_subtype_val.mul continuous_const).measurable

private theorem measurable_orb [SFinite μH] {φ : G → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable (orb H μH φ) := by
  unfold orb
  exact (measurable_comp_mul H hφ).lintegral_prod_right'

private theorem secondCountable_subgroup : SecondCountableTopology H :=
  Topology.IsInducing.subtypeVal.secondCountableTopology

private theorem sigmaFinite_of_isClosed (hH : IsClosed (H : Set G)) [μH.IsHaarMeasure] :
    SigmaFinite μH := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := secondCountable_subgroup H
  infer_instance

end Orbit

section Weight

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

private noncomputable def E : CompactExhaustion G := CompactExhaustion.choice G

private noncomputable def M (n : ℕ) : ℝ≥0∞ :=
  μH (((↑) : H → G) ⁻¹' ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹))

private noncomputable def coef (n : ℕ) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ n * (1 + M H μH n)⁻¹

private def V (n : ℕ) : Set G := interior (E (G := G) (n + 1) : Set G)

private theorem weight_eq (g : G) :
    weight H μH g = ∑' n : ℕ, coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) g := by
  have h : SigmaCompactSpace G ∧ WeaklyLocallyCompactSpace G := ⟨inferInstance, inferInstance⟩
  unfold weight
  rw [dif_pos h]
  rfl

private theorem isOpen_V (n : ℕ) : IsOpen (V (G := G) n) := isOpen_interior

private theorem V_subset (n : ℕ) : V (G := G) n ⊆ (E (G := G) (n + 1) : Set G) := interior_subset

include hH in
private theorem M_lt_top (n : ℕ) : M H μH n < ⊤ := by
  unfold M
  have hc : IsCompact ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹) :=
    ((E (G := G)).isCompact (n + 1)).mul ((E (G := G)).isCompact (n + 1)).inv
  have hce : Topology.IsClosedEmbedding ((↑) : H → G) := hH.isClosedEmbedding_subtypeVal
  exact (hce.isCompact_preimage hc).measure_lt_top

include hH in
private theorem coef_pos (n : ℕ) : 0 < coef H μH n := by
  unfold coef
  apply ENNReal.mul_pos
  · exact (ENNReal.pow_pos (by norm_num) n).ne'
  · apply (ENNReal.inv_pos.mpr ?_).ne'
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, (M_lt_top H hH μH n).ne⟩

private theorem coef_mul_M_le (n : ℕ) : coef H μH n * M H μH n ≤ (2⁻¹ : ℝ≥0∞) ^ n := by
  unfold coef
  rw [mul_assoc]
  calc (2⁻¹ : ℝ≥0∞) ^ n * ((1 + M H μH n)⁻¹ * M H μH n)
      ≤ (2⁻¹ : ℝ≥0∞) ^ n * 1 := by
        gcongr
        calc (1 + M H μH n)⁻¹ * M H μH n ≤ (1 + M H μH n)⁻¹ * (1 + M H μH n) := by
              gcongr
              exact le_add_self
          _ ≤ 1 := ENNReal.inv_mul_le_one _
    _ = (2⁻¹ : ℝ≥0∞) ^ n := mul_one _

private theorem measurable_weight : Measurable (weight H μH) := by
  have : weight H μH = fun g => ∑' n : ℕ, coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) g := by
    funext g; exact weight_eq H μH g
  rw [this]
  refine Measurable.ennreal_tsum fun n => ?_
  exact (measurable_const.indicator (isOpen_V n).measurableSet).const_mul _

private def slice (n : ℕ) (g : G) : Set H := {x : H | (x : G) * g ∈ V (G := G) n}

private theorem isOpen_slice (n : ℕ) (g : G) : IsOpen (slice H n g) := by
  unfold slice
  exact (isOpen_V n).preimage ((continuous_subtype_val.mul continuous_const))

private theorem orb_weight_eq (g : G) :
    orb H μH (weight H μH) g = ∑' n : ℕ, coef H μH n * μH (slice H n g) := by
  unfold orb
  have hind : ∀ n, Measurable fun x : H =>
      (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) := fun n =>
    (measurable_const.indicator (isOpen_V n).measurableSet).comp (measurable_subtype_mul H g)
  have hterm : ∀ n, Measurable fun x : H =>
      coef H μH n * (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g) := fun n =>
    (hind n).const_mul _
  simp_rw [weight_eq H μH]
  rw [lintegral_tsum fun n => (hterm n).aemeasurable]
  refine tsum_congr fun n => ?_
  rw [lintegral_const_mul _ (hind n)]
  congr 1
  have : (fun x : H => (V (G := G) n).indicator (fun _ => (1 : ℝ≥0∞)) ((x : G) * g))
      = (slice H n g).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    unfold slice
    by_cases hx : (x : G) * g ∈ V (G := G) n
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ {x : H | (x : G) * g ∈ V n} from hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ {x : H | (x : G) * g ∈ V n} from hx)]
  rw [this, lintegral_indicator ((isOpen_slice H n g).measurableSet), setLIntegral_one]

private theorem measure_slice_le (n : ℕ) (g : G) : μH (slice H n g) ≤ M H μH n := by
  by_cases hne : (slice H n g).Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    have hsub : slice H n g ⊆
        (fun y : H => y * x₀⁻¹) ⁻¹'
          (((↑) : H → G) ⁻¹' ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹)) := by
      intro x hx
      simp only [Set.mem_preimage]
      have h1 : (x : G) * g ∈ (E (G := G) (n + 1) : Set G) := V_subset n hx
      have h2 : (x₀ : G) * g ∈ (E (G := G) (n + 1) : Set G) := V_subset n hx₀
      have : ((x * x₀⁻¹ : H) : G) = ((x : G) * g) * ((x₀ : G) * g)⁻¹ := by
        push_cast
        group
      rw [this]
      exact Set.mul_mem_mul h1 (Set.inv_mem_inv.mpr h2)
    calc μH (slice H n g)
        ≤ μH ((fun y : H => y * x₀⁻¹) ⁻¹'
            (((↑) : H → G) ⁻¹' ((E (G := G) (n + 1) : Set G) * (E (G := G) (n + 1) : Set G)⁻¹))) :=
          measure_mono hsub
      _ = M H μH n := by
          unfold M
          rw [measure_preimage_mul_right]
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, measure_empty]
    exact zero_le

private theorem orb_weight_le_two (g : G) : orb H μH (weight H μH) g ≤ 2 := by
  rw [orb_weight_eq H μH g]
  calc ∑' n : ℕ, coef H μH n * μH (slice H n g)
      ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n := by
        refine ENNReal.tsum_le_tsum fun n => ?_
        exact (mul_le_mul_right (measure_slice_le H μH n g) _).trans (coef_mul_M_le H μH n)
    _ = 2 := by
        rw [ENNReal.tsum_geometric]
        norm_num

private theorem orb_weight_lt_top (g : G) : orb H μH (weight H μH) g < ⊤ :=
  (orb_weight_le_two H μH g).trans_lt ENNReal.ofNat_lt_top

include hH in
private theorem orb_weight_pos (g : G) : 0 < orb H μH (weight H μH) g := by
  rw [orb_weight_eq H μH g]

  set m := (E (G := G)).find g with hm
  have hg : g ∈ V (G := G) m := (E (G := G)).subset_interior_succ m ((E (G := G)).mem_find g)
  have h1 : (1 : H) ∈ slice H m g := by
    show ((1 : H) : G) * g ∈ V (G := G) m
    simpa using hg
  have hpos : 0 < μH (slice H m g) :=
    (isOpen_slice H m g).measure_pos μH ⟨1, h1⟩
  have hterm : 0 < coef H μH m * μH (slice H m g) :=
    ENNReal.mul_pos (coef_pos H hH μH m).ne' hpos.ne'
  exact hterm.trans_le (ENNReal.le_tsum m)

include hH in
private theorem orb_weight_ne_zero (g : G) : orb H μH (weight H μH) g ≠ 0 :=
  (orb_weight_pos H hH μH g).ne'

private theorem density_eq (g : G) :
    density H μH g = weight H μH g / orb H μH (weight H μH) g := rfl

include hH in
private theorem measurable_density : Measurable (density H μH) := by
  haveI : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  have : density H μH = fun g => weight H μH g / orb H μH (weight H μH) g := rfl
  rw [this]
  exact (measurable_weight H μH).div (measurable_orb H μH (measurable_weight H μH))

include hH in
private theorem orb_density (g : G) : orb H μH (density H μH) g = 1 := by
  have hrw : (fun x : H => density H μH ((x : G) * g))
      = fun x : H => weight H μH ((x : G) * g) * (orb H μH (weight H μH) g)⁻¹ := by
    funext x
    rw [density_eq, orb_mul_left H μH (weight H μH) x g, div_eq_mul_inv]
  have hmeas : Measurable fun x : H => weight H μH ((x : G) * g) :=
    (measurable_weight H μH).comp (measurable_subtype_mul H g)
  unfold orb
  rw [show (fun x : H => density H μH ((x : G) * g)) = _ from hrw]
  rw [lintegral_mul_const _ hmeas]
  exact ENNReal.mul_inv_cancel (orb_weight_ne_zero H hH μH g) (orb_weight_lt_top H μH g).ne

end Weight

section Inv

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem isInvInvariant : μH.IsInvInvariant := by
  haveI : LocallyCompactSpace H := hH.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := secondCountable_subgroup H
  constructor
  let c : ℝ≥0∞ := Measure.haarScalarFactor μH.inv μH
  have hc : μH.inv = c • μH := Measure.isMulLeftInvariant_eq_smul μH.inv μH
  have : Measure.map Inv.inv (Measure.map Inv.inv μH) = c ^ 2 • μH := by
    rw [← Measure.inv_def μH, hc, Measure.map_smul, ← Measure.inv_def μH, hc, smul_smul, pow_two]
  have μeq : μH = c ^ 2 • μH := by
    rw [Measure.map_map continuous_inv.measurable continuous_inv.measurable] at this
    simpa only [inv_involutive, Function.Involutive.comp_self, Measure.map_id]
  have K : TopologicalSpace.PositiveCompacts H := Classical.arbitrary _
  have hKpos : 0 < μH K :=
    (isOpen_interior.measure_pos μH K.interior_nonempty).trans_le (measure_mono interior_subset)
  have h1 : c ^ 2 * μH K = 1 ^ 2 * μH K := by
    conv_rhs => rw [μeq]
    simp
  have h2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj hKpos.ne' K.isCompact.measure_lt_top.ne).1 h1
  have h3 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective h2
  change μH.inv = μH
  rw [hc, h3, one_smul]

end Inv

section Symmetry

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem lintegral_mul_orb {φ β : G → ℝ≥0∞} (hφ : Measurable φ) (hβ : Measurable β) :
    ∫⁻ g, φ g * orb H μH β g ∂μ = ∫⁻ g, orb H μH φ g * β g ∂μ := by
  haveI : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  haveI : μH.IsInvInvariant := isInvInvariant H hH μH
  have hmβ : ∀ g, Measurable fun x : H => β ((x : G) * g) := fun g =>
    hβ.comp (measurable_subtype_mul H g)
  have hmφ : ∀ g, Measurable fun x : H => φ ((x : G) * g) := fun g =>
    hφ.comp (measurable_subtype_mul H g)

  have hL : ∀ g, φ g * orb H μH β g = ∫⁻ x : H, φ g * β ((x : G) * g) ∂μH := by
    intro g
    unfold orb
    exact (lintegral_const_mul (φ g) (hmβ g)).symm
  have hR : ∀ g, orb H μH φ g * β g = ∫⁻ x : H, φ ((x : G) * g) * β g ∂μH := by
    intro g
    unfold orb
    exact (lintegral_mul_const (β g) (hmφ g)).symm
  simp_rw [hL, hR]

  have hm1 : Measurable (Function.uncurry fun (g : G) (x : H) => φ g * β ((x : G) * g)) := by
    exact (hφ.comp measurable_fst).mul (measurable_comp_mul H hβ)
  have hm2 : Measurable (Function.uncurry fun (g : G) (x : H) => φ ((x : G) * g) * β g) := by
    exact (measurable_comp_mul H hφ).mul (hβ.comp measurable_fst)
  rw [lintegral_lintegral_swap hm1.aemeasurable, lintegral_lintegral_swap hm2.aemeasurable]

  have hsub : ∀ x : H, ∫⁻ g, φ g * β ((x : G) * g) ∂μ = ∫⁻ g, φ (((x⁻¹ : H) : G) * g) * β g ∂μ := by
    intro x
    have := lintegral_mul_left_eq_self (μ := μ) (fun g => φ g * β ((x : G) * g)) ((x⁻¹ : H) : G)
    rw [← this]
    refine lintegral_congr fun g => ?_
    simp [← mul_assoc]
  simp_rw [hsub]

  have := lintegral_inv_eq_self (μ := μH) (fun x : H => ∫⁻ g, φ ((x : G) * g) * β g ∂μ)
  simpa using this

end Symmetry

section Core

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem lintegral_eq_lintegral_measure {f : G → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, orb H μH f q.out ∂(HaarQuotient.measure μ H μH) := by
  haveI : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH

  have hF : (fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out) ∘
      Quotient.mk (MulAction.orbitRel H G) = orb H μH f := by
    funext g
    exact orb_out_mk H μH f g
  have hFm : Measurable fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out := by
    rw [measurable_from_quotient]
    show Measurable ((fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out) ∘
      Quotient.mk (MulAction.orbitRel H G))
    rw [hF]
    exact measurable_orb H μH hf
  unfold HaarQuotient.measure
  rw [lintegral_map hFm (measurable_quotient_mk'' (s := MulAction.orbitRel H G))]
  show ∫⁻ g, f g ∂μ = ∫⁻ g, ((fun q : MulAction.orbitRel.Quotient H G => orb H μH f q.out) ∘
      Quotient.mk (MulAction.orbitRel H G)) g ∂(μ.withDensity (density H μH))
  rw [hF, lintegral_withDensity_eq_lintegral_mul μ (measurable_density H hH μH)
    (measurable_orb H μH hf)]
  show ∫⁻ g, f g ∂μ = ∫⁻ g, density H μH g * orb H μH f g ∂μ
  simp_rw [mul_comm (density H μH _)]
  rw [← lintegral_mul_orb μ H hH μH hf (measurable_density H hH μH)]
  simp_rw [orb_density H hH μH, mul_one]

include hH in

private theorem core (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂μ = ∫⁻ q, (∫⁻ x, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) :=
  lintegral_eq_lintegral_measure μ H hH μH hf

end Core

section FDae

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G]

variable {α : Type*} [MeasurableSpace α] {Γ : Type*} [Group Γ] [MulAction Γ α] [Countable Γ]
  [MeasurableConstSMul Γ α]

private theorem isFundamentalDomain_of_ae_eq {μ : Measure α} [SMulInvariantMeasure Γ α μ] {s t : Set α}
    (hs : IsFundamentalDomain Γ s μ) (hst : s =ᵐ[μ] t) (ht : NullMeasurableSet t μ) :
    IsFundamentalDomain Γ t μ := by
  have hg : ∀ g : Γ, g • s =ᵐ[μ] g • t := fun g => by
    have := ((measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving).preimage_ae_eq hst
    rwa [Set.preimage_smul_inv, Set.preimage_smul_inv] at this
  refine ⟨ht, ?_, ?_⟩
  · have h1 := hs.ae_covers
    have h2 : ∀ᵐ x ∂μ, ∀ g : Γ, x ∈ g⁻¹ • s ↔ x ∈ g⁻¹ • t := by
      rw [ae_all_iff]
      intro g
      exact (hg g⁻¹).mem_iff
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hgx⟩ := hx1
    refine ⟨g, ?_⟩
    have := (hx2 g).1 (Set.mem_inv_smul_set_iff.mpr hgx)
    exact Set.mem_inv_smul_set_iff.mp this
  · intro a b hab
    have hs' := hs.aedisjoint hab
    exact hs'.congr (hg a).symm (hg b).symm

end FDae

section D2

variable (μ : Measure G) [μ.IsMulLeftInvariant] [SFinite μ]
  (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
  (Γ : Subgroup G) (hΓ : Γ ≤ H) [Countable Γ]

private def fibre (S : Set G) (g : G) : Set H := {x : H | (x : G) * g ∈ S}

omit [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [BorelSpace G]
  [Countable Γ] in
include hΓ in

private theorem mem_subgroupOf_of_mem {γ : G} (hγ : γ ∈ Γ) :
    (⟨γ, hΓ hγ⟩ : H) ∈ Γ.subgroupOf H := by
  rw [Subgroup.mem_subgroupOf]
  exact hγ

private def bad (S : Set G) : Set G :=
  {g : G | ∀ γ : Γ, (γ : G) * g ∉ S} ∪ ⋃ γ₁ : Γ, ⋃ γ₂ : Γ, ⋃ (_ : γ₁ ≠ γ₂),
    {g : G | (γ₁ : G) * g ∈ S ∧ (γ₂ : G) * g ∈ S}

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
private theorem measurableSet_bad {S : Set G} (hS : MeasurableSet S) : MeasurableSet (bad Γ S) := by
  unfold bad
  refine MeasurableSet.union ?_ ?_
  · have : {g : G | ∀ γ : Γ, (γ : G) * g ∉ S} = ⋂ γ : Γ, (fun g => (γ : G) * g) ⁻¹' Sᶜ := by
      ext g; simp
    rw [this]
    exact MeasurableSet.iInter fun γ => (measurable_const_mul (γ : G)) hS.compl
  · refine MeasurableSet.iUnion fun γ₁ => MeasurableSet.iUnion fun γ₂ => MeasurableSet.iUnion fun _ => ?_
    exact ((measurable_const_mul (γ₁ : G)) hS).inter ((measurable_const_mul (γ₂ : G)) hS)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in

private theorem measure_bad_eq_zero {S : Set G} (hS : IsFundamentalDomain Γ S μ) : μ (bad Γ S) = 0 := by
  unfold bad
  refine measure_union_null ?_ ?_
  · have hc := hS.ae_covers
    apply compl_mem_ae_iff.mp
    filter_upwards [hc] with g hg
    obtain ⟨γ, hγ⟩ := hg
    have hγ' : (γ : G) * g ∈ S := by simpa [Subgroup.smul_def] using hγ
    exact fun h => h γ hγ'
  · refine (measure_iUnion_null_iff).mpr fun γ₁ => (measure_iUnion_null_iff).mpr fun γ₂ =>
      (measure_iUnion_null_iff).mpr fun hne => ?_
    have hdis := hS.aedisjoint (inv_injective.ne hne : γ₁⁻¹ ≠ γ₂⁻¹)
    refine measure_mono_null ?_ hdis
    intro g hg
    simp only [Set.mem_setOf_eq] at hg
    refine ⟨?_, ?_⟩
    · rw [Set.mem_inv_smul_set_iff, Subgroup.smul_def, smul_eq_mul]; exact hg.1
    · rw [Set.mem_inv_smul_set_iff, Subgroup.smul_def, smul_eq_mul]; exact hg.2

include hΓ in
omit [LocallyCompactSpace G] [SecondCountableTopology G] in

private theorem isFundamentalDomain_fibre {S : Set G} (hS : MeasurableSet S) (g : G)
    (hg : μH (fibre H (bad Γ S) g) = 0) :
    IsFundamentalDomain (Γ.subgroupOf H) (fibre H S g) μH := by
  have hmeas : MeasurableSet (fibre H S g) :=
    (continuous_subtype_val.mul continuous_const).measurable hS
  refine IsFundamentalDomain.mk'' hmeas.nullMeasurableSet ?_ ?_ ?_
  ·
    have hg' : ∀ᵐ x ∂μH, x ∉ fibre H (bad Γ S) g := compl_mem_ae_iff.mpr hg
    filter_upwards [hg'] with x hx
    have hx' : (x : G) * g ∉ bad Γ S := hx
    unfold bad at hx'
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_forall, not_not] at hx'
    obtain ⟨⟨γ, hγS⟩, -⟩ := hx'
    refine ⟨⟨⟨(γ : G), hΓ γ.2⟩, mem_subgroupOf_of_mem H Γ hΓ γ.2⟩, ?_⟩
    show (((⟨⟨(γ : G), hΓ γ.2⟩, mem_subgroupOf_of_mem H Γ hΓ γ.2⟩ : Γ.subgroupOf H) • x : H) : G)
      * g ∈ S
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul]
    simpa [mul_assoc] using hγS
  ·
    intro γ' hγ'
    refine measure_mono_null ?_ hg
    rintro x ⟨hx1, hx2⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem] at hx1
    have h1 : (((γ'⁻¹ • x : H)) : G) * g ∈ S := hx1
    have h2 : (x : G) * g ∈ S := hx2
    rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul] at h1

    have hγmem : (((γ'⁻¹ : Γ.subgroupOf H) : H) : G) ∈ Γ := by
      have := (γ'⁻¹).2
      rw [Subgroup.mem_subgroupOf] at this
      exact this
    have hne : (⟨_, hγmem⟩ : Γ) ≠ 1 := by
      intro h
      apply hγ'
      have h' : (((γ'⁻¹ : Γ.subgroupOf H) : H) : G) = 1 := by
        simpa using congrArg (fun z : Γ => (z : G)) h
      have : γ'⁻¹ = 1 := by
        ext
        exact_mod_cast h'
      simpa using this
    show (x : G) * g ∈ bad Γ S
    unfold bad
    refine Or.inr (Set.mem_iUnion.mpr ⟨1, Set.mem_iUnion.mpr ⟨⟨_, hγmem⟩, Set.mem_iUnion.mpr
      ⟨hne.symm, ?_⟩⟩⟩)
    refine ⟨by simpa using h2, ?_⟩
    simpa [mul_assoc] using h1
  · intro γ'
    exact (measurePreserving_smul γ' μH).quasiMeasurePreserving

omit [LocallyCompactSpace G] [SecondCountableTopology G] in

private theorem orb_indicator {S : Set G} (hS : MeasurableSet S) (f : G → ℝ≥0∞) (g : G) :
    orb H μH (S.indicator f) g = ∫⁻ x in fibre H S g, f ((x : G) * g) ∂μH := by
  have hfm : MeasurableSet (fibre H S g) :=
    (continuous_subtype_val.mul continuous_const).measurable hS
  unfold orb
  rw [← lintegral_indicator hfm]
  refine lintegral_congr fun x => ?_
  exact (Set.indicator_comp_right (fun x : H => (x : G) * g) (s := S) (g := f)).symm

include hH hΓ in

private theorem d2 (f : G → ℝ≥0∞) (hf : Measurable f) (hfΓ : ∀ γ ∈ Γ, ∀ g : G, f (γ * g) = f g)
    (S : Set G) (hS : IsFundamentalDomain Γ S μ)
    (T : Set H) (hT : IsFundamentalDomain (Γ.subgroupOf H) T μH) :
    ∫⁻ g in S, f g ∂μ =
      ∫⁻ q, (∫⁻ x in T, f ((x : G) * q.out) ∂μH) ∂(HaarQuotient.measure μ H μH) := by
  haveI : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  haveI : Countable (Γ.subgroupOf H) := by
    have : Function.Injective fun x : Γ.subgroupOf H => (⟨((x : H) : G), x.2⟩ : Γ) := by
      intro a b h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
    exact this.countable

  obtain ⟨S', hS'sub, hS'm, hS'eq⟩ := hS.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hS' : IsFundamentalDomain Γ S' μ :=
    isFundamentalDomain_of_ae_eq hS hS'eq.symm hS'm.nullMeasurableSet
  rw [setLIntegral_congr hS'eq.symm]

  rw [← lintegral_indicator hS'm]
  rw [lintegral_eq_lintegral_measure μ H hH μH (hf.indicator hS'm)]

  have hbad0 : μ (bad Γ S') = 0 := measure_bad_eq_zero μ Γ hS'
  have hbadm : MeasurableSet (bad Γ S') := measurableSet_bad Γ hS'm
  have h1m : Measurable ((bad Γ S').indicator fun _ : G => (1 : ℝ≥0∞)) :=
    measurable_const.indicator hbadm
  have horb0 : ∫⁻ q, orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out
      ∂(HaarQuotient.measure μ H μH) = 0 := by
    rw [← lintegral_eq_lintegral_measure μ H hH μH h1m, lintegral_indicator hbadm,
      setLIntegral_const, one_mul, hbad0]
  have hmeas_out : Measurable fun q : MulAction.orbitRel.Quotient H G =>
      orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out := by
    rw [measurable_from_quotient]
    have : (fun q : MulAction.orbitRel.Quotient H G =>
        orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out) ∘ Quotient.mk'' =
        orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) := by
      funext g; exact orb_out_mk H μH _ g
    rw [this]
    exact measurable_orb H μH h1m
  have hae : ∀ᵐ q ∂(HaarQuotient.measure μ H μH),
      orb H μH ((bad Γ S').indicator fun _ => (1 : ℝ≥0∞)) q.out = 0 :=
    (lintegral_eq_zero_iff hmeas_out).mp horb0
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with q hq

  have hfib0 : μH (fibre H (bad Γ S') q.out) = 0 := by
    rw [orb_indicator H μH hbadm (fun _ => (1 : ℝ≥0∞)) q.out, setLIntegral_const, one_mul] at hq
    exact hq
  have hFD : IsFundamentalDomain (Γ.subgroupOf H) (fibre H S' q.out) μH :=
    isFundamentalDomain_fibre H μH Γ hΓ hS'm q.out hfib0
  rw [orb_indicator H μH hS'm f q.out]

  refine hFD.setLIntegral_eq hT (fun x : H => f ((x : G) * q.out)) ?_
  intro γ' x
  show f ((((γ' • x : H)) : G) * q.out) = f ((x : G) * q.out)
  rw [Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, mul_assoc]
  have hmem : (((γ' : Γ.subgroupOf H) : H) : G) ∈ Γ := by
    have := γ'.2; rw [Subgroup.mem_subgroupOf] at this; exact this
  exact hfΓ _ hmem _

end D2

section OuterMeasurability

variable (H : Subgroup G) (hH : IsClosed (H : Set G)) (μH : Measure H)
  [μH.IsHaarMeasure] [μH.IsMulRightInvariant]

include hH in
private theorem measurable_lintegral_mul_out (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x, f ((x : G) * q.out) ∂μH := by
  haveI : SigmaFinite μH := sigmaFinite_of_isClosed H μH hH
  rw [measurable_from_quotient]
  have hF : (fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x, f ((x : G) * q.out) ∂μH) ∘
      Quotient.mk'' = orb H μH f := by
    funext g
    exact orb_out_mk H μH f g
  rw [hF]
  exact measurable_orb H μH hf

end OuterMeasurability

end HaarDisM65

theorem solution
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (H : Subgroup G) (hH : IsClosed (H : Set G))
    (μH : Measure H) [μH.IsHaarMeasure] [μH.IsMulRightInvariant]
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    Measurable fun q : MulAction.orbitRel.Quotient H G => ∫⁻ x, f ((x : G) * q.out) ∂μH :=
  HaarDisM65.measurable_lintegral_mul_out H hH μH f hf

end

end S_HaarQuotient_measurable_lintegral_mul_out
end P2MW
export P2MW.S_HaarQuotient_measurable_lintegral_mul_out (solution)
