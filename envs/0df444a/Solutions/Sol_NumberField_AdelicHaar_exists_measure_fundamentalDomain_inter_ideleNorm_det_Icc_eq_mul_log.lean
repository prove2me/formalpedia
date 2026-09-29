-- Prove2me | solution 1 for NumberField.AdelicHaar.exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c431357a-102a-5199-9253-db539e4e5681

import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.FundamentalDomain
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Set NumberField IsDedekindDomain NumberField.TateGlobal Matrix
open scoped ENNReal NNReal Pointwise

noncomputable section

namespace T8SlabVolume

section Abstract

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [μ.IsMulLeftInvariant]
  (Γ : Subgroup G) [Countable Γ]
  (φ : G → ℝ) (s : ℝ → G)

theorem isFundamentalDomain_smul_of_comm {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) (g : G)
    (hg : ∀ γ ∈ Γ, γ * g = g * γ) : IsFundamentalDomain Γ (g • Ω) μ := by
  refine hΩ.image_of_equiv (MulAction.toPerm g)
    (measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving (Equiv.refl _) fun γ x => ?_
  show g • ((γ : G) * x) = (γ : G) * (g • x)
  rw [smul_eq_mul, smul_eq_mul, ← mul_assoc, ← mul_assoc, hg γ γ.2]

def slabMeasure (Ω : Set G) : Measure ℝ := Measure.map φ (μ.restrict Ω)

variable {μ φ}

theorem slabMeasure_apply (hφ : Measurable φ) (Ω : Set G) {B : Set ℝ} (hB : MeasurableSet B) :
    slabMeasure μ φ Ω B = μ (φ ⁻¹' B ∩ Ω) := by
  rw [slabMeasure, Measure.map_apply hφ hB, Measure.restrict_apply (hφ hB)]

theorem slabMeasure_mono (Ω : Set G) {B B' : Set ℝ} (h : B ⊆ B') :
    slabMeasure μ φ Ω B ≤ slabMeasure μ φ Ω B' := measure_mono h

variable {Γ s}

theorem preimage_smul_preimage_eq (hφmul : ∀ x y, φ (x * y) = φ x + φ y)
    (hΓ : ∀ γ ∈ Γ, φ γ = 0) (B : Set ℝ) (γ : Γ) :
    (fun x : G => γ • x) ⁻¹' (φ ⁻¹' B) = φ ⁻¹' B := by
  ext x
  simp only [mem_preimage, Subgroup.smul_def, smul_eq_mul, hφmul, hΓ γ γ.2, zero_add]

theorem slabMeasure_preimage_const_add (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) (t : ℝ) {B : Set ℝ} (hB : MeasurableSet B) :
    slabMeasure μ φ Ω ((fun x => t + x) ⁻¹' B) = slabMeasure μ φ Ω B := by
  have hB' : MeasurableSet ((fun x => t + x) ⁻¹' B) := measurable_const_add t hB
  rw [slabMeasure_apply hφ Ω hB', slabMeasure_apply hφ Ω hB]

  have hpre : φ ⁻¹' ((fun x => t + x) ⁻¹' B) = (fun h => s t * h) ⁻¹' (φ ⁻¹' B) := by
    ext x
    simp only [mem_preimage, hφmul, hs]
  have hΩ' : IsFundamentalDomain Γ (s t • Ω) μ := isFundamentalDomain_smul_of_comm μ Γ hΩ (s t) (hcomm t)
  have hinj : Function.Injective fun h : G => s t * h := mul_right_injective (s t)
  have hpreΩ : (fun h => s t * h) ⁻¹' (s t • Ω) = Ω := by
    rw [← image_smul]
    exact hinj.preimage_image Ω
  calc μ (φ ⁻¹' ((fun x => t + x) ⁻¹' B) ∩ Ω)
      = μ ((fun h => s t * h) ⁻¹' (φ ⁻¹' B ∩ s t • Ω)) := by
        rw [preimage_inter, hpre, hpreΩ]
    _ = μ (φ ⁻¹' B ∩ s t • Ω) := measure_preimage_mul μ (s t) _
    _ = μ (φ ⁻¹' B ∩ Ω) :=
        hΩ'.measure_set_eq hΩ (hφ hB) (preimage_smul_preimage_eq hφmul hΓ B)

theorem isAddLeftInvariant_slabMeasure (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) :
    (slabMeasure μ φ Ω).IsAddLeftInvariant := by
  refine ⟨fun t => Measure.ext fun B hB => ?_⟩
  rw [Measure.map_apply (measurable_const_add t) hB]
  exact slabMeasure_preimage_const_add hφ hφmul hΓ hs hcomm hΩ t hB

theorem isFiniteMeasureOnCompacts_slabMeasure (hφ : Measurable φ) {Ω : Set G}
    (hfin : ∀ R : ℝ, μ (φ ⁻¹' Icc (-R) R ∩ Ω) < ⊤) :
    IsFiniteMeasureOnCompacts (slabMeasure μ φ Ω) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hK.isBounded
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hR
  calc slabMeasure μ φ Ω K ≤ slabMeasure μ φ Ω (Icc (-R) R) := measure_mono hR
    _ = μ (φ ⁻¹' Icc (-R) R ∩ Ω) := slabMeasure_apply hφ Ω measurableSet_Icc
    _ < ⊤ := hfin R

theorem exists_measure_preimage_Icc_inter_eq (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω₀ : Set G} (hΩ₀ : IsFundamentalDomain Γ Ω₀ μ)
    (hfin : ∀ R : ℝ, μ (φ ⁻¹' Icc (-R) R ∩ Ω₀) < ⊤) :
    ∃ c : ℝ≥0, (μ ≠ 0 → c ≠ 0) ∧
      ∀ Ω : Set G, IsFundamentalDomain Γ Ω μ → ∀ a b : ℝ,
        μ (φ ⁻¹' Icc a b ∩ Ω) = (c : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  set m : Measure ℝ := slabMeasure μ φ Ω₀ with hm
  haveI : m.IsAddLeftInvariant := isAddLeftInvariant_slabMeasure hφ hφmul hΓ hs hcomm hΩ₀
  haveI : IsFiniteMeasureOnCompacts m := isFiniteMeasureOnCompacts_slabMeasure hφ hfin
  have hIcc : ∀ a b : ℝ, m (Icc a b) = (m.addHaarScalarFactor volume : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
    intro a b
    have h := Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure m volume
      (s := Icc a b) (by rw [closure_Icc]; exact isCompact_Icc)
    rw [h, Real.volume_Icc, ENNReal.smul_def, smul_eq_mul]
  refine ⟨m.addHaarScalarFactor volume, fun hμ hc => ?_, fun Ω hΩ a b => ?_⟩
  ·
    apply hΩ₀.measure_ne_zero hμ
    have huniv : m univ = 0 := by
      have hcov : (univ : Set ℝ) = ⋃ n : ℕ, Icc (-(n : ℝ)) n := by
        refine (eq_univ_of_forall fun x => mem_iUnion.2 ?_).symm
        obtain ⟨n, hn⟩ := exists_nat_ge |x|
        exact ⟨n, abs_le.1 hn⟩
      rw [hcov]
      refine measure_iUnion_null fun n => ?_
      rw [hIcc, hc, ENNReal.coe_zero, zero_mul]
    have := slabMeasure_apply (μ := μ) hφ Ω₀ MeasurableSet.univ
    rw [preimage_univ, univ_inter] at this
    rw [← this]
    exact huniv
  · rw [← hΩ₀.measure_set_eq hΩ (hφ measurableSet_Icc) (preimage_smul_preimage_eq hφmul hΓ _),
      ← slabMeasure_apply hφ Ω₀ measurableSet_Icc]
    exact hIcc a b

theorem measure_preimage_inter_lt_top_of_subset_iUnion_smul [IsFiniteMeasureOnCompacts μ]
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) {A C : Set G} (hC : IsCompact C)
    (hAC : A ⊆ ⋃ γ : Γ, γ • C) : μ (A ∩ Ω) < ⊤ := by
  calc μ (A ∩ Ω) ≤ μ ((⋃ γ : Γ, γ • C) ∩ Ω) := measure_mono (inter_subset_inter_left _ hAC)
    _ = μ (⋃ γ : Γ, γ • C ∩ Ω) := by rw [iUnion_inter]
    _ ≤ ∑' γ : Γ, μ (γ • C ∩ Ω) := measure_iUnion_le _
    _ = μ C := (hΩ.measure_eq_tsum C).symm
    _ < ⊤ := hC.measure_lt_top

theorem measure_preimage_Icc_inter_lt_top_of_one (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {Ω : Set G} (hΩ : IsFundamentalDomain Γ Ω μ) {a₀ b₀ : ℝ} (hab₀ : a₀ < b₀)
    (hfin₀ : μ (φ ⁻¹' Icc a₀ b₀ ∩ Ω) < ⊤) (R : ℝ) :
    μ (φ ⁻¹' Icc (-R) R ∩ Ω) < ⊤ := by
  set m : Measure ℝ := slabMeasure μ φ Ω with hm
  have hm₀ : m (Icc a₀ b₀) < ⊤ := by rwa [hm, slabMeasure_apply hφ Ω measurableSet_Icc]

  have htrans : ∀ t : ℝ, m (Icc (a₀ + t) (b₀ + t)) = m (Icc a₀ b₀) := by
    intro t
    have h := slabMeasure_preimage_const_add hφ hφmul hΓ hs hcomm hΩ (-t) (measurableSet_Icc (a := a₀) (b := b₀))
    rw [Set.preimage_const_add_Icc, sub_neg_eq_add, sub_neg_eq_add] at h
    exact h

  set w : ℝ := b₀ - a₀ with hw
  have hw0 : 0 < w := sub_pos.2 hab₀
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (R + |a₀|) / w + 1 ≤ M := exists_nat_ge _
  have hcov : Icc (-R) R ⊆ ⋃ k ∈ Finset.Icc (-(M : ℤ)) M, Icc (a₀ + (k : ℝ) * w) (b₀ + (k : ℝ) * w) := by
    intro x hx
    set k : ℤ := ⌊(x - a₀) / w⌋ with hk
    have hk1 : (k : ℝ) ≤ (x - a₀) / w := Int.floor_le _
    have hk2 : (x - a₀) / w < k + 1 := Int.lt_floor_add_one _
    have hxR : |x| ≤ R := abs_le.2 hx
    have hbound : |(x - a₀) / w| ≤ (R + |a₀|) / w := by
      rw [abs_div, abs_of_pos hw0]
      exact div_le_div_of_nonneg_right ((abs_sub _ _).trans (by linarith)) hw0.le
    have hkabs : |(k : ℝ)| ≤ (R + |a₀|) / w + 1 := by
      rw [abs_le]
      constructor
      · have := (abs_le.1 hbound).1
        linarith
      · have := (abs_le.1 hbound).2
        linarith
    have hkM : -(M : ℤ) ≤ k ∧ k ≤ M := by
      have h := abs_le.1 (hkabs.trans hM)
      constructor
      · have h1 : ((-(M : ℤ) : ℤ) : ℝ) ≤ (k : ℝ) := by push_cast; exact h.1
        exact Int.cast_le.1 h1
      · have h2 : ((k : ℤ) : ℝ) ≤ ((M : ℤ) : ℝ) := by push_cast; exact h.2
        exact Int.cast_le.1 h2
    refine mem_iUnion₂.2 ⟨k, Finset.mem_Icc.2 hkM, ?_⟩
    have h1 : (k : ℝ) * w ≤ x - a₀ := (le_div_iff₀ hw0).1 hk1
    have h2 : x - a₀ < ((k : ℝ) + 1) * w := (div_lt_iff₀ hw0).1 hk2
    constructor <;> [linarith; (rw [hw] at h2 ⊢; linarith)]
  calc μ (φ ⁻¹' Icc (-R) R ∩ Ω) = m (Icc (-R) R) := (slabMeasure_apply hφ Ω measurableSet_Icc).symm
    _ ≤ m (⋃ k ∈ Finset.Icc (-(M : ℤ)) M, Icc (a₀ + (k : ℝ) * w) (b₀ + (k : ℝ) * w)) := measure_mono hcov
    _ ≤ ∑ k ∈ Finset.Icc (-(M : ℤ)) M, m (Icc (a₀ + (k : ℝ) * w) (b₀ + (k : ℝ) * w)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ k ∈ Finset.Icc (-(M : ℤ)) M, m (Icc a₀ b₀) := Finset.sum_congr rfl fun k _ => htrans _
    _ < ⊤ := ENNReal.sum_lt_top.2 fun _ _ => hm₀

end Abstract

section Tile

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsMulLeftInvariant]
  {Γ : Subgroup G} [Countable Γ]
  {φ : G → ℝ} {s : ℝ → G}

theorem phi_smul (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hs : ∀ t, φ (s t) = t) (t : ℝ) (x : G) :
    φ (s t • x) = t + φ x := by
  rw [smul_eq_mul, hφmul, hs]

theorem phi_inv_smul (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hs : ∀ t, φ (s t) = t) (t : ℝ) (x : G) :
    φ ((s t)⁻¹ • x) = φ x - t := by
  have h := phi_smul hφmul hs t ((s t)⁻¹ • x)
  rw [smul_inv_smul] at h
  linarith

theorem phi_subgroup_smul (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (γ : Γ) (x : G) : φ (γ • x) = φ x := by
  rw [Subgroup.smul_def, smul_eq_mul, hφmul, hΓ γ γ.2, zero_add]

theorem int_eq_of_mem_Ico {A w : ℝ} (hw : 0 < w) {u : ℝ} {k k' : ℤ}
    (hk : u - k * w ∈ Ico A (A + w)) (hk' : u - k' * w ∈ Ico A (A + w)) : k = k' := by
  have h1 : k = ⌊(u - A) / w⌋ := by
    rw [eq_comm, Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hw]; linarith [hk.1]
    · rw [div_lt_iff₀ hw]; linarith [hk.2]
  have h2 : k' = ⌊(u - A) / w⌋ := by
    rw [eq_comm, Int.floor_eq_iff]
    constructor
    · rw [le_div_iff₀ hw]; linarith [hk'.1]
    · rw [div_lt_iff₀ hw]; linarith [hk'.2]
  rw [h1, h2]

theorem exists_isFundamentalDomain_of_slab (hφ : Measurable φ)
    (hφmul : ∀ x y, φ (x * y) = φ x + φ y) (hΓ : ∀ γ ∈ Γ, φ γ = 0)
    (hs : ∀ t, φ (s t) = t) (hcomm : ∀ t, ∀ γ ∈ Γ, γ * s t = s t * γ)
    {A B : ℝ} (hAB : A < B) {Φ₁ : Set G} (hΦ₁S : Φ₁ ⊆ φ ⁻¹' Icc A B)
    (hΦ₁ : IsFundamentalDomain Γ Φ₁ (μ.restrict (φ ⁻¹' Icc A B))) :
    ∃ Ω : Set G, IsFundamentalDomain Γ Ω μ ∧ μ (φ ⁻¹' Icc A B ∩ Ω) ≤ μ Φ₁ + μ Φ₁ := by

  set w : ℝ := B - A with hw
  have hw0 : 0 < w := sub_pos.2 hAB
  set S : Set G := φ ⁻¹' Icc A B with hSdef
  have hSm : MeasurableSet S := hφ measurableSet_Icc
  set T₀ : Set G := φ ⁻¹' Ico A B with hT₀
  have hT₀m : MeasurableSet T₀ := hφ measurableSet_Ico
  have hT₀S : T₀ ⊆ S := fun x hx => Ico_subset_Icc_self hx
  set P : Set G := Φ₁ ∩ T₀ with hP
  have hPS : P ⊆ S := fun x hx => hΦ₁S hx.1
  let g : ℤ → G := fun k => s (k * w)
  have hg : ∀ (k : ℤ) (x : G), φ (g k • x) = k * w + φ x := fun k x => phi_smul hφmul hs _ x
  have hginv : ∀ (k : ℤ) (x : G), φ ((g k)⁻¹ • x) = φ x - k * w := fun k x => phi_inv_smul hφmul hs _ x
  have hcomm' : ∀ (k : ℤ) (γ : Γ), (γ : G) * g k = g k * γ := fun k γ => hcomm _ γ γ.2
  have hgcommx : ∀ (k : ℤ) (γ : Γ) (y : G), γ • (g k • y) = g k • (γ • y) := by
    intro k γ y
    rw [Subgroup.smul_def, Subgroup.smul_def, smul_smul, smul_smul, hcomm' k γ]
  have hgcomm : ∀ (k : ℤ) (γ : Γ) (X : Set G), (γ • (g k • X) : Set G) = g k • (γ • X) := by
    intro k γ X
    rw [Subgroup.smul_def, smul_smul, Subgroup.smul_def, smul_smul, hcomm' k γ]

  have hmemT : ∀ (k : ℤ) (x : G), x ∈ g k • T₀ ↔ φ x - k * w ∈ Ico A (A + w) := by
    intro k x
    rw [← smul_inv_smul (g k) x, smul_mem_smul_set_iff, hT₀, mem_preimage, hginv,
      smul_inv_smul, hw, add_sub_cancel]
  have hidx : ∀ (k k' : ℤ) (x : G), x ∈ g k • T₀ → x ∈ g k' • T₀ → k = k' := by
    intro k k' x hk hk'
    exact int_eq_of_mem_Ico hw0 ((hmemT k x).1 hk) ((hmemT k' x).1 hk')

  have hΓT₀ : ∀ (γ : Γ) (X : Set G), X ⊆ T₀ → (γ • X : Set G) ⊆ T₀ := by
    intro γ X hX y hy
    obtain ⟨x, hx, rfl⟩ := mem_smul_set.1 hy
    show φ (γ • x) ∈ Ico A B
    rw [phi_subgroup_smul hφmul hΓ]
    exact hX hx

  set Ω : Set G := ⋃ k : ℤ, g k • P with hΩ

  have hΦ₁n : NullMeasurableSet Φ₁ μ := (nullMeasurableSet_restrict_of_subset hΦ₁S).1 hΦ₁.nullMeasurableSet
  have hPn : NullMeasurableSet P μ := hΦ₁n.inter hT₀m.nullMeasurableSet
  have hΩn : NullMeasurableSet Ω μ := NullMeasurableSet.iUnion fun k => hPn.smul (g k)
  refine ⟨Ω, IsFundamentalDomain.mk'' hΩn ?_ ?_ fun γ =>
    (measurePreserving_smul γ μ).quasiMeasurePreserving, ?_⟩
  ·
    rw [ae_iff]
    set N₀ : Set G := {y | y ∈ T₀ ∧ ¬ ∃ γ : Γ, γ • y ∈ Φ₁} with hN₀
    have hN₀0 : μ N₀ = 0 := by
      have h1 : μ N₀ = μ.restrict S N₀ := by
        rw [Measure.restrict_apply' hSm, inter_eq_left.2 (fun y hy => hT₀S hy.1)]
      rw [h1]
      refine measure_mono_null (fun y hy => hy.2) ?_
      exact ae_iff.1 hΦ₁.ae_covers
    have hsub : {x | ¬ ∃ γ : Γ, γ • x ∈ Ω} ⊆ ⋃ k : ℤ, g k • N₀ := by
      intro x hx
      set k : ℤ := ⌊(φ x - A) / w⌋ with hk
      have hy : (g k)⁻¹ • x ∈ T₀ := by
        show φ ((g k)⁻¹ • x) ∈ Ico A B
        rw [hginv]
        have h1 : (k : ℝ) ≤ (φ x - A) / w := Int.floor_le _
        have h2 : (φ x - A) / w < k + 1 := Int.lt_floor_add_one _
        rw [le_div_iff₀ hw0] at h1
        rw [div_lt_iff₀ hw0] at h2
        constructor <;> [linarith; (rw [hw] at h2; linarith)]
      refine mem_iUnion.2 ⟨k, mem_smul_set.2 ⟨(g k)⁻¹ • x, ⟨hy, ?_⟩, smul_inv_smul _ _⟩⟩
      rintro ⟨γ, hγ⟩
      apply hx
      refine ⟨γ, mem_iUnion.2 ⟨k, ?_⟩⟩
      have hmem : γ • ((g k)⁻¹ • x) ∈ P :=
        ⟨hγ, hΓT₀ γ {(g k)⁻¹ • x} (singleton_subset_iff.2 hy) (smul_mem_smul_set (mem_singleton _))⟩
      have : γ • x = g k • (γ • ((g k)⁻¹ • x)) := by
        conv_lhs => rw [← smul_inv_smul (g k) x]
        exact hgcommx k γ _
      rw [this]
      exact smul_mem_smul_set hmem
    refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
    rw [measure_smul, hN₀0]
  ·
    intro γ hγ
    show μ (γ • Ω ∩ Ω) = 0
    have hγΩ : (γ • Ω : Set G) = ⋃ k : ℤ, g k • (γ • P) := by
      rw [hΩ, smul_set_iUnion]
      exact iUnion_congr fun k => hgcomm k γ P
    have hsub : (γ • Ω ∩ Ω : Set G) ⊆ ⋃ k : ℤ, g k • (γ • P ∩ P) := by
      intro x hx
      rw [hγΩ] at hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hx.1
      obtain ⟨k', hk'⟩ := mem_iUnion.1 hx.2
      have h1 : x ∈ g k • T₀ := smul_set_mono (hΓT₀ γ P inter_subset_right) hk
      have h2 : x ∈ g k' • T₀ := smul_set_mono inter_subset_right hk'
      have hkk : k = k' := hidx k k' x h1 h2
      subst hkk
      refine mem_iUnion.2 ⟨k, ?_⟩
      rw [smul_set_inter]
      exact ⟨hk, hk'⟩
    refine measure_mono_null hsub (measure_iUnion_null fun k => ?_)
    rw [measure_smul]
    have hdisj : μ.restrict S (γ • Φ₁ ∩ Φ₁) = 0 := by
      have h := hΦ₁.aedisjoint (show γ ≠ (1 : Γ) from hγ)
      rw [Function.onFun, one_smul] at h
      exact h
    rw [Measure.restrict_apply' hSm] at hdisj
    have hsub2 : (γ • P ∩ P : Set G) ⊆ γ • Φ₁ ∩ Φ₁ ∩ S := fun x hx =>
      ⟨⟨smul_set_mono inter_subset_left hx.1, hx.2.1⟩, hPS hx.2⟩
    exact measure_mono_null hsub2 hdisj
  ·
    have hsub : S ∩ Ω ⊆ g 0 • P ∪ g 1 • P := by
      intro x hx
      obtain ⟨k, hk⟩ := mem_iUnion.1 hx.2
      have hkT : φ x - k * w ∈ Ico A (A + w) := (hmemT k x).1 (smul_set_mono inter_subset_right hk)
      have hxS : φ x ∈ Icc A B := hx.1
      have hk01 : k = 0 ∨ k = 1 := by
        have h1 : (k : ℝ) * w ≤ φ x - A := by linarith [hkT.1]
        have h2 : φ x - A < (k + 1) * w := by linarith [hkT.2]
        have h3 : (k : ℝ) * w ≤ w := by linarith [hxS.2]
        have h4 : (0 : ℝ) < (k + 1) * w := by linarith [hxS.1]
        have hk1 : (k : ℝ) ≤ 1 := by
          by_contra h; rw [not_le] at h; nlinarith
        have hk0 : (-1 : ℝ) < k := by
          by_contra h; rw [not_lt] at h; nlinarith
        have hk1' : k ≤ 1 := by exact_mod_cast hk1
        have hk0' : -1 < k := by exact_mod_cast hk0
        omega
      rcases hk01 with rfl | rfl
      · exact Or.inl hk
      · exact Or.inr hk
    calc μ (S ∩ Ω) ≤ μ (g 0 • P ∪ g 1 • P) := measure_mono hsub
      _ ≤ μ (g 0 • P) + μ (g 1 • P) := measure_union_le _ _
      _ = μ P + μ P := by rw [measure_smul, measure_smul]
      _ ≤ μ Φ₁ + μ Φ₁ := add_le_add (measure_mono inter_subset_left) (measure_mono inter_subset_left)

end Tile

section Ideles

variable (F : Type) [Field F] [NumberField F]

abbrev principalUnits : Subgroup (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F)).range

theorem countable_numberField : Countable F :=
  (Module.Free.chooseBasis ℚ F).equivFun.toEquiv.countable_iff.2 inferInstance

theorem countable_units_numberField : Countable Fˣ := by
  haveI := countable_numberField F
  exact Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective

scoped instance countable_principalUnits : Countable (principalUnits F) := by
  haveI := countable_units_numberField F
  exact (MonoidHom.rangeRestrict_surjective _).countable

def logNorm (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ := Real.log (ideleNorm F x)

theorem logNorm_mul (x y : (AdeleRing (𝓞 F) F)ˣ) : logNorm F (x * y) = logNorm F x + logNorm F y := by
  simp only [logNorm, ideleNorm_mul]
  exact Real.log_mul (ideleNorm_pos x).ne' (ideleNorm_pos y).ne'

theorem continuous_logNorm : Continuous (logNorm F) :=
  (NumberField.TateGlobal.continuous_ideleNorm F).log fun x => (ideleNorm_pos x).ne'

theorem ideleNorm_principal (a : Fˣ) :
    ideleNorm F (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F) a) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  simp only [ideleNorm]
  rw [RingHom.toMonoidHom_eq_coe] at h
  rw [h]
  rfl

theorem logNorm_principal (γ : (AdeleRing (𝓞 F) F)ˣ) (hγ : γ ∈ principalUnits F) : logNorm F γ = 0 := by
  obtain ⟨a, rfl⟩ := hγ
  simp [logNorm, ideleNorm_principal]

theorem mem_normOneIdeles_iff_logNorm (x : (AdeleRing (𝓞 F) F)ˣ) :
    x ∈ normOneIdeles F ↔ logNorm F x = 0 := by
  rw [mem_normOneIdeles_iff, logNorm]
  constructor
  · intro h; rw [h, Real.log_one]
  · intro h
    exact Real.eq_one_of_pos_of_log_eq_zero (ideleNorm_pos x) h

theorem isClosed_normOneIdeles : IsClosed (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have : (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) = logNorm F ⁻¹' {0} := by
    ext x; exact mem_normOneIdeles_iff_logNorm F x
  rw [this]
  exact isClosed_singleton.preimage (continuous_logNorm F)

scoped instance locallyCompactSpace_normOneIdeles : LocallyCompactSpace (normOneIdeles F) :=
  (isClosed_normOneIdeles F).isClosedEmbedding_subtypeVal.locallyCompactSpace

def basePlace : InfinitePlace F := Classical.arbitrary _

variable {F} in
open scoped Classical in

def toCompletion (w : InfinitePlace F) (r : ℝ) : w.Completion :=
  if hw : w.IsReal then (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm r
  else (InfinitePlace.Completion.ringEquivComplexOfIsComplex
    (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm r

variable {F} in
theorem isometry_ringEquiv_symm {A B : Type*} [NormedField A] [NormedField B] (e : A ≃+* B)
    (he : Isometry e) : Isometry e.symm := fun a b => by
  rw [← he.edist_eq, e.apply_symm_apply, e.apply_symm_apply]

variable {F} in
theorem isometry_toCompletion (w : InfinitePlace F) : Isometry (toCompletion w) := by
  by_cases hw : w.IsReal
  · have h : Isometry (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm :=
      isometry_ringEquiv_symm _ (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw)
    intro a b
    simp only [toCompletion, dif_pos hw]
    exact h.edist_eq a b
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have h : Isometry (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm :=
      isometry_ringEquiv_symm _ (InfinitePlace.Completion.isometry_extensionEmbedding w)
    intro a b
    simp only [toCompletion, dif_neg hw]
    exact (h.comp Complex.isometry_ofReal).edist_eq a b

variable {F} in
theorem toCompletion_zero (w : InfinitePlace F) : toCompletion w 0 = 0 := by
  by_cases hw : w.IsReal
  · simp only [toCompletion, dif_pos hw, map_zero]
  · simp only [toCompletion, dif_neg hw, Complex.ofReal_zero, map_zero]

variable {F} in
theorem norm_toCompletion (w : InfinitePlace F) (r : ℝ) : ‖toCompletion w r‖ = |r| := by
  rw [(isometry_toCompletion w).norm_map_of_map_zero (toCompletion_zero w), Real.norm_eq_abs]

variable {F} in
theorem continuous_toCompletion (w : InfinitePlace F) : Continuous (toCompletion w) :=
  (isometry_toCompletion w).continuous

variable {F} in
theorem toCompletion_ne_zero (w : InfinitePlace F) {r : ℝ} (hr : r ≠ 0) : toCompletion w r ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_toCompletion]
  exact abs_ne_zero.mpr hr

variable {F} in

def expUnit (w : InfinitePlace F) (t : ℝ) : (w.Completion)ˣ :=
  Units.mk0 (toCompletion w (Real.exp (t / w.mult))) (toCompletion_ne_zero w (Real.exp_pos _).ne')

variable {F} in
theorem norm_expUnit (w : InfinitePlace F) (t : ℝ) :
    ‖((expUnit w t : (w.Completion)ˣ) : w.Completion)‖ = Real.exp (t / w.mult) := by
  rw [expUnit, Units.val_mk0, norm_toCompletion, abs_of_pos (Real.exp_pos _)]

variable {F} in
theorem continuous_expUnit (w : InfinitePlace F) : Continuous (expUnit w) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact (continuous_toCompletion w).comp (Real.continuous_exp.comp (continuous_id.div_const _))
  · have : (fun t => ((expUnit w t)⁻¹ : (w.Completion)ˣ) : ℝ → w.Completion) =
        fun t => (toCompletion w (Real.exp (t / w.mult)))⁻¹ := by
      funext t; rfl
    rw [this]
    exact ((continuous_toCompletion w).comp
      (Real.continuous_exp.comp (continuous_id.div_const _))).inv₀
      fun t => toCompletion_ne_zero w (Real.exp_pos _).ne'

def archSection (t : ℝ) : (AdeleRing (𝓞 F) F)ˣ :=
  archUnitHom (basePlace F) (expUnit (basePlace F) t)

theorem continuous_archSection : Continuous (archSection F) := by
  classical
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have h1 : Continuous fun t => ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) :
        (basePlace F).Completion) := Units.continuous_val.comp (continuous_expUnit _)
    have : (Units.val ∘ archSection F) = fun t =>
        ((Function.update (1 : InfiniteAdeleRing F) (basePlace F)
          ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) : (basePlace F).Completion), 1) :
            InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext t; rfl
    rw [this]
    exact (continuous_const.update (basePlace F) h1).prodMk continuous_const
  · have h1 : Continuous fun t => (((expUnit (basePlace F) t)⁻¹ : ((basePlace F).Completion)ˣ) :
        (basePlace F).Completion) := Units.continuous_coe_inv.comp (continuous_expUnit _)
    have : (fun t => ((archSection F t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : ℝ → AdeleRing (𝓞 F) F) = fun t =>
        ((Function.update (1 : InfiniteAdeleRing F) (basePlace F)
          (((expUnit (basePlace F) t)⁻¹ : ((basePlace F).Completion)ˣ) : (basePlace F).Completion), 1) :
            InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := by
      funext t; rfl
    rw [this]
    exact (continuous_const.update (basePlace F) h1).prodMk continuous_const

theorem ideleNorm_archSection (t : ℝ) : ideleNorm F (archSection F t) = Real.exp t := by
  classical
  have h2 : ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := rfl
  have h := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one F
    (archSection F t) h2
  simp only [ideleNorm]
  rw [h, Finset.prod_eq_single (basePlace F)]
  · rw [show ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 (basePlace F) =
        ((expUnit (basePlace F) t : ((basePlace F).Completion)ˣ) : (basePlace F).Completion) from
        NumberField.AdelicVolume.archCentralUnit_fst_self _ _,
      norm_expUnit, ← Real.exp_nat_mul, mul_div_cancel₀]
    exact Nat.cast_ne_zero.mpr (InfinitePlace.mult_pos (w := basePlace F)).ne'
  · intro w _ hw
    rw [show ((archSection F t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 from
      NumberField.AdelicVolume.archCentralUnit_fst_of_ne _ _ hw, norm_one, one_pow]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem logNorm_archSection (t : ℝ) : logNorm F (archSection F t) = t := by
  rw [logNorm, ideleNorm_archSection, Real.log_exp]

end Ideles

section GeneralLinear

attribute [local instance] NumberField.AdelicHaar.glBorel

variable (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K] [NumberField K]

abbrev globalGL : Subgroup (GL n (AdeleRing (𝓞 K) K)) :=
  (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
    GL n K →* GL n (AdeleRing (𝓞 K) K)).range

scoped instance countable_globalGL : Countable (globalGL n K) := by
  haveI := countable_numberField K
  haveI : Countable (Matrix n n K) := inferInstanceAs (Countable (n → n → K))
  haveI : Countable (GL n K) :=
    Function.Injective.countable (f := fun g : GL n K => (g : Matrix n n K)) fun g h hgh => Units.ext hgh
  exact (MonoidHom.rangeRestrict_surjective _).countable

def logNormDet (g : GL n (AdeleRing (𝓞 K) K)) : ℝ := logNorm K (Matrix.GeneralLinearGroup.det g)

theorem logNormDet_mul (g h : GL n (AdeleRing (𝓞 K) K)) :
    logNormDet n K (g * h) = logNormDet n K g + logNormDet n K h := by
  simp only [logNormDet, map_mul, logNorm_mul]

theorem continuous_logNormDet : Continuous (logNormDet n K) :=
  (continuous_logNorm K).comp Matrix.GeneralLinearGroup.continuous_det

theorem det_map_algebraMap (γ : GL n K) :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)
        (Matrix.GeneralLinearGroup.det γ) := by
  ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, MonoidHom.coe_coe,
    Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

theorem logNormDet_global (γ : GL n (AdeleRing (𝓞 K) K)) (hγ : γ ∈ globalGL n K) :
    logNormDet n K γ = 0 := by
  obtain ⟨g, rfl⟩ := hγ
  simp only [logNormDet]
  rw [det_map_algebraMap]
  exact logNorm_principal K _ ⟨_, rfl⟩

variable [Nonempty n]

def glSection (t : ℝ) : GL n (AdeleRing (𝓞 K) K) :=
  Matrix.GeneralLinearGroup.scalar n (archSection K (t / Fintype.card n))

theorem logNormDet_glSection (t : ℝ) : logNormDet n K (glSection n K t) = t := by
  simp only [logNormDet, glSection, Matrix.GeneralLinearGroup.det_scalar, logNorm, map_pow,
    ideleNorm]
  push_cast
  rw [Real.log_pow]
  have h := logNorm_archSection K (t / Fintype.card n)
  simp only [logNorm, ideleNorm] at h
  rw [h, mul_div_cancel₀]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

theorem glSection_comm (t : ℝ) (g : GL n (AdeleRing (𝓞 K) K)) : g * glSection n K t = glSection n K t * g := by
  apply Units.ext
  simp only [glSection, Units.val_mul, Matrix.GeneralLinearGroup.scalar, Units.coe_map,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact ((Matrix.scalar_commute _ (fun r' => Commute.all _ r') (g : Matrix n n (AdeleRing (𝓞 K) K))).eq).symm

variable (μ : Measure (GL n (AdeleRing (𝓞 K) K))) [μ.IsHaarMeasure]

theorem exists_measure_inter_ideleNorm_det_mem_Icc_eq
    (Φ₀ : Set (GL n (AdeleRing (𝓞 K) K))) (hΦ₀ : IsFundamentalDomain (globalGL n K) Φ₀ μ)
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀)
    (hfin : μ (Φ₀ ∩ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a₀ b₀}) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      ∀ Φ : Set (GL n (AdeleRing (𝓞 K) K)), IsFundamentalDomain (globalGL n K) Φ μ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          μ (Φ ∩ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a)) := by
  haveI : BorelSpace (GL n (AdeleRing (𝓞 K) K)) := NumberField.AdelicHaar.borelSpace_glBorel n (𝓞 K) K
  have hφ : Measurable (logNormDet n K) := (continuous_logNormDet n K).measurable
  have hset : ∀ (Φ : Set (GL n (AdeleRing (𝓞 K) K))) (a b : ℝ), 0 < a → 0 < b →
      Φ ∩ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b} =
        logNormDet n K ⁻¹' Icc (Real.log a) (Real.log b) ∩ Φ := by
    intro Φ a b ha hb
    rw [inter_comm]
    congr 1
    ext g
    simp only [mem_setOf_eq, mem_preimage, mem_Icc, logNormDet, logNorm]
    rw [Real.log_le_log_iff ha (ideleNorm_pos _), Real.log_le_log_iff (ideleNorm_pos _) hb]
  have hfin' : μ (logNormDet n K ⁻¹' Icc (Real.log a₀) (Real.log b₀) ∩ Φ₀) < ⊤ := by
    rw [← hset Φ₀ a₀ b₀ ha₀ (ha₀.trans hab₀)]
    exact lt_top_iff_ne_top.2 hfin
  have hfinR := measure_preimage_Icc_inter_lt_top_of_one (μ := μ) (Γ := globalGL n K)
    (φ := logNormDet n K) (s := glSection n K) hφ (logNormDet_mul n K) (logNormDet_global n K)
    (logNormDet_glSection n K) (fun t γ _ => glSection_comm n K t γ) hΦ₀
    (Real.log_lt_log ha₀ hab₀) hfin'
  obtain ⟨c, hc0, hc⟩ := exists_measure_preimage_Icc_inter_eq (μ := μ) (Γ := globalGL n K)
    (φ := logNormDet n K) (s := glSection n K) hφ (logNormDet_mul n K) (logNormDet_global n K)
    (logNormDet_glSection n K) (fun t γ _ => glSection_comm n K t γ) hΦ₀ hfinR
  have hμ : μ ≠ 0 :=
    Measure.measure_univ_ne_zero.1 (IsOpen.measure_ne_zero μ isOpen_univ univ_nonempty)
  refine ⟨c, ENNReal.coe_ne_zero.2 (hc0 hμ), ENNReal.coe_ne_top, fun Φ hΦ a b ha hab => ?_⟩
  rw [hset Φ a b ha (ha.trans_le hab), hc Φ hΦ, Real.log_div (ha.trans_le hab).ne' ha.ne']

theorem smulInvariantMeasure_restrict {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α]
    [MeasurableConstSMul G α] {ν : Measure α} [SMulInvariantMeasure G α ν] {S : Set α}
    (hS : MeasurableSet S) (hinv : ∀ g : G, (fun x => g • x) ⁻¹' S = S) :
    SMulInvariantMeasure G α (ν.restrict S) := by
  refine ⟨fun g A hA => ?_⟩
  rw [Measure.restrict_apply hA, Measure.restrict_apply (measurable_const_smul g hA),
    ← SMulInvariantMeasure.measure_preimage_smul (μ := ν) g (hA.inter hS), preimage_inter, hinv g]

theorem measure_eq_of_subset_slab_of_isFundamentalDomain_restrict
    (Φ₀ : Set (GL n (AdeleRing (𝓞 K) K))) (hΦ₀ : IsFundamentalDomain (globalGL n K) Φ₀ μ)
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀)
    (hfin : μ (Φ₀ ∩ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a₀ b₀}) ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ Φ : Set (GL n (AdeleRing (𝓞 K) K)), IsFundamentalDomain (globalGL n K) Φ μ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          μ (Φ ∩ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a))) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (GL n (AdeleRing (𝓞 K) K)),
        Φ ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b} →
        IsFundamentalDomain (globalGL n K) Φ
          (μ.restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b}) →
        μ Φ = C * ENNReal.ofReal (Real.log (b / a))) := by
  haveI : BorelSpace (GL n (AdeleRing (𝓞 K) K)) := NumberField.AdelicHaar.borelSpace_glBorel n (𝓞 K) K
  obtain ⟨C, hC0, hCt, hC⟩ := exists_measure_inter_ideleNorm_det_mem_Icc_eq n K μ Φ₀ hΦ₀ a₀ b₀ ha₀ hab₀ hfin
  refine ⟨C, hC0, hCt, hC, fun a b ha hab Φ hΦS hΦ => ?_⟩
  set S : Set (GL n (AdeleRing (𝓞 K) K)) :=
    {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b} with hSdef
  have hSeq : S = logNormDet n K ⁻¹' Icc (Real.log a) (Real.log b) := by
    ext g
    simp only [hSdef, mem_setOf_eq, mem_preimage, mem_Icc, logNormDet, logNorm]
    rw [Real.log_le_log_iff ha (ideleNorm_pos _), Real.log_le_log_iff (ideleNorm_pos _) (ha.trans_le hab)]
  have hSm : MeasurableSet S := by
    rw [hSeq]
    exact (continuous_logNormDet n K).measurable measurableSet_Icc
  have hSinv : ∀ γ : globalGL n K, (fun x => γ • x) ⁻¹' S = S := by
    intro γ
    rw [hSeq]
    exact preimage_smul_preimage_eq (logNormDet_mul n K) (logNormDet_global n K) _ γ
  haveI : SMulInvariantMeasure (globalGL n K) (GL n (AdeleRing (𝓞 K) K)) (μ.restrict S) :=
    smulInvariantMeasure_restrict hSm hSinv
  have hΦ₀S : IsFundamentalDomain (globalGL n K) Φ₀ (μ.restrict S) :=
    hΦ₀.mono (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
  calc μ Φ = μ.restrict S Φ := by rw [Measure.restrict_apply' hSm, inter_eq_left.2 hΦS]
    _ = μ.restrict S Φ₀ := hΦ.measure_eq hΦ₀S
    _ = μ (Φ₀ ∩ S) := Measure.restrict_apply' hSm
    _ = C * ENNReal.ofReal (Real.log (b / a)) := hC Φ₀ hΦ₀ a b ha hab

end GeneralLinear

section GeneralLinearSlab

attribute [local instance] NumberField.AdelicHaar.glBorel

variable (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (K : Type) [Field K] [NumberField K]
  (μ : Measure (GL n (AdeleRing (𝓞 K) K))) [μ.IsHaarMeasure]

theorem measure_slab_of_isFundamentalDomain_restrict
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀)
    (Φ₀ : Set (GL n (AdeleRing (𝓞 K) K)))
    (hΦ₀s : Φ₀ ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a₀ b₀})
    (hΦ₀ : IsFundamentalDomain (globalGL n K) Φ₀
      (μ.restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a₀ b₀}))
    (hfin : μ Φ₀ ≠ ⊤) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ Φ : Set (GL n (AdeleRing (𝓞 K) K)), IsFundamentalDomain (globalGL n K) Φ μ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          μ (Φ ∩ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a))) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (GL n (AdeleRing (𝓞 K) K)),
        Φ ⊆ {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b} →
        IsFundamentalDomain (globalGL n K) Φ
          (μ.restrict {g | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a b}) →
        μ Φ = C * ENNReal.ofReal (Real.log (b / a))) := by
  haveI : BorelSpace (GL n (AdeleRing (𝓞 K) K)) := NumberField.AdelicHaar.borelSpace_glBorel n (𝓞 K) K
  have hφ : Measurable (logNormDet n K) := (continuous_logNormDet n K).measurable
  have hSeq : {g : GL n (AdeleRing (𝓞 K) K) | ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Icc a₀ b₀} =
      logNormDet n K ⁻¹' Icc (Real.log a₀) (Real.log b₀) := by
    ext g
    simp only [mem_setOf_eq, mem_preimage, mem_Icc, logNormDet, logNorm]
    rw [Real.log_le_log_iff ha₀ (ideleNorm_pos _), Real.log_le_log_iff (ideleNorm_pos _) (ha₀.trans hab₀)]
  rw [hSeq] at hΦ₀s hΦ₀
  obtain ⟨Ω, hΩ, hΩfin⟩ := exists_isFundamentalDomain_of_slab (μ := μ) (Γ := globalGL n K)
    (φ := logNormDet n K) (s := glSection n K) hφ (logNormDet_mul n K) (logNormDet_global n K)
    (logNormDet_glSection n K) (fun t γ _ => glSection_comm n K t γ)
    (Real.log_lt_log ha₀ hab₀) hΦ₀s hΦ₀
  refine measure_eq_of_subset_slab_of_isFundamentalDomain_restrict n K μ Ω hΩ a₀ b₀ ha₀ hab₀ ?_
  rw [hSeq, inter_comm]
  exact (hΩfin.trans_lt (ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hfin, lt_top_iff_ne_top.2 hfin⟩)).ne

end GeneralLinearSlab

end T8SlabVolume
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log.T8SlabVolume"

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log.T8SlabVolume"

section

attribute [local instance] NumberField.AdelicHaar.glBorel

open MeasureTheory NumberField IsDedekindDomain in
theorem solution
    (n : Type) [Fintype n] [DecidableEq n] [Nonempty n] (K : Type) [Field K] [NumberField K]
    (μ : Measure (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K))) [μ.IsHaarMeasure]
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab₀ : a₀ < b₀)
    (Φ₀ : Set (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a₀ b₀})
    (hΦ₀ : IsFundamentalDomain
      (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
        Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)).range Φ₀
      (μ.restrict {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
        Set.Icc a₀ b₀}))
    (hfin : μ Φ₀ ≠ ⊤) :
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ Φ : Set (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)),
        IsFundamentalDomain
          (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
            Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)).range Φ μ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          μ (Φ ∩ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
            Set.Icc a b}) = C * ENNReal.ofReal (Real.log (b / a))) ∧
      (∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)),
        Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
        IsFundamentalDomain
          (Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) :
            Matrix.GeneralLinearGroup n K →* Matrix.GeneralLinearGroup n (AdeleRing (𝓞 K) K)).range Φ
          (μ.restrict {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈
            Set.Icc a b}) →
        μ Φ = C * ENNReal.ofReal (Real.log (b / a))) :=
  T8SlabVolume.measure_slab_of_isFundamentalDomain_restrict n K μ a₀ b₀ ha₀ hab₀ Φ₀ hΦ₀s hΦ₀ hfin

end
p2m_reactivate "P2MW.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log.T8SlabVolume"

end S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log
end P2MW
export P2MW.S_NumberField_AdelicHaar_exists_measure_fundamentalDomain_inter_ideleNorm_det_Icc_eq_mul_log (solution)
