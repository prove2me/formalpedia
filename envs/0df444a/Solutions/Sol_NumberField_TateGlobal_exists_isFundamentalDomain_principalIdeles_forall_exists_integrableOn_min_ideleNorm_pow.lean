-- Prove2me | solution 1 for NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/dfa9ef8a-839b-5c83-bc87-a9fcdb569b88

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq
import Theorems.Thm_NumberField_AdeleRing_exists_isOpen_inter_principalIdeles_eq_singleton
import Theorems.Thm_Subgroup_exists_exact_fundamental_domain_of_secondCountableTopology
import Theorems.Thm_NumberField_TateGlobal_compactSpace_normOneIdeleClass
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "LanglandsTunnell.TateLocal.charExt_coe_units LanglandsTunnell.TateLocal.modulus_one LanglandsTunnell.TateLocal.modulus_zero LanglandsTunnell.TateLocal.modulus_coe_units LanglandsTunnell.TateLocal.charExt_zero ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply RingEquiv.restrictedProductCongr_symm_apply RingEquiv.restrictedProductCongrRight_apply MulEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductProd_symm_apply_coe Equiv.restrictedProductCongrRight_apply AddEquiv.restrictedProductCongr_apply Equiv.restrictedProductCongrLeft'_symm_apply_apply Equiv.restrictedProductCongr_apply_apply Equiv.restrictedProductCongrLeft_apply_apply RestrictedProduct.flatten_equiv'_apply AddEquiv.restrictedProductCongrRight_apply Equiv.restrictedProductCongr_symm_apply Equiv.restrictedProductCongrRight_symm_apply RestrictedProduct.flatten_equiv'_symm_apply AddEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductCongrLeft'_apply RestrictedProduct.flatten_apply RingEquiv.restrictedProductCongr_apply_apply RingEquiv.restrictedProductCongrLeft'_apply Equiv.restrictedProductProd_apply RestrictedProduct.flatten_equiv_apply RestrictedProduct.flatten_equiv_symm_apply LinearEquiv.restrictedProductCongrLeft'_apply RestrictedProduct.not_mem_support RestrictedProduct.mem_structureSubring_iff RestrictedProduct.not_mem_mulSupport RestrictedProduct.support_neg"
p2m_attr_erase "simp" "RestrictedProduct.mem_indexSupport_iff RestrictedProduct.mulSupport_inv RestrictedProduct.mapAlongLinearMap_apply"

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField NumberField.TateGlobal MeasureTheory

scoped instance (F : Type) [Field F] [NumberField F] :
    LocallyCompactSpace (NumberField.AdeleRing (NumberField.RingOfIntegers F) F)ˣ :=
  inferInstance

noncomputable section

namespace Ws1
namespace K2

open scoped NNReal ENNReal Pointwise

section FD

variable {P α : Type*} [Group P] [MulAction P α] [MeasurableSpace α] {μ : Measure α}
  [MeasurableConstSMul P α] [SMulInvariantMeasure P α μ] [Countable P]

theorem measure_fd_lt_top_of_smul_cover {D K : Set α} (hD : IsFundamentalDomain P D μ)
    (hKm : MeasurableSet K) (hKt : μ K < ⊤) (hcov : ∀ x : α, ∃ p : P, x ∈ p • K) :
    μ D < ⊤ := by
  have hsub : D ⊆ ⋃ p : P, p • K := fun x _ => Set.mem_iUnion.mpr (hcov x)
  have h2 : ∀ p : P, μ (D ∩ p • K) = μ ((p⁻¹ • D) ∩ K) := by
    intro p
    simp
  have h3 : (∑' p : P, μ ((p⁻¹ • D) ∩ K)) = ∑' p : P, μ ((p • D) ∩ K) := by
    exact (Equiv.inv P).tsum_eq fun q : P => μ ((q • D) ∩ K)
  have h4 : (∑' p : P, μ ((p • D) ∩ K)) = μ K := by
    have h5 := hD.lintegral_eq_tsum (K.indicator 1)
    rw [lintegral_indicator_one hKm] at h5
    have h6 : ∀ p : P, (∫⁻ x in p • D, K.indicator 1 x ∂μ) = μ ((p • D) ∩ K) := by
      intro p
      rw [lintegral_indicator_one hKm, Measure.restrict_apply hKm, Set.inter_comm]
    rw [tsum_congr h6] at h5
    exact h5.symm
  calc μ D ≤ μ (D ∩ ⋃ p : P, p • K) := measure_mono (Set.subset_inter Set.Subset.rfl hsub)
    _ = μ (⋃ p : P, D ∩ p • K) := by rw [Set.inter_iUnion]
    _ ≤ ∑' p : P, μ (D ∩ p • K) := measure_iUnion_le _
    _ = ∑' p : P, μ ((p⁻¹ • D) ∩ K) := tsum_congr h2
    _ = ∑' p : P, μ ((p • D) ∩ K) := h3
    _ = μ K := h4
    _ < ⊤ := hKt

end FD

section ExpUnit

def expUnit (x : ℝ) : ℝ≥0ˣ :=
  Units.mk (Real.exp x).toNNReal (Real.exp (-x)).toNNReal
    (by
      rw [← Real.toNNReal_mul (Real.exp_pos x).le, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, Real.toNNReal_one])
    (by
      rw [← Real.toNNReal_mul (Real.exp_pos (-x)).le, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, Real.toNNReal_one])

@[scoped simp] theorem coe_val_expUnit (x : ℝ) : (((expUnit x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp x := by
  show (((Real.exp x).toNNReal : ℝ≥0) : ℝ) = Real.exp x
  rw [Real.coe_toNNReal _ (Real.exp_pos x).le]

theorem continuous_expUnit : Continuous expUnit := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact continuous_real_toNNReal.comp Real.continuous_exp

end ExpUnit

section Restrict

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G)
  (μ : Measure G) [μ.IsMulLeftInvariant]

theorem smulInvariantMeasure_restrict_of_invariant {S : Set G} (hS : MeasurableSet S)
    (hinv : ∀ γ : Γ, (fun x : G => γ • x) ⁻¹' S = S) :
    SMulInvariantMeasure Γ G (μ.restrict S) := by
  refine ⟨fun γ t ht => ?_⟩
  have hmeas : Measurable fun x : G => (γ : G) * x := measurable_const_mul _
  have hpre : (fun x : G => γ • x) ⁻¹' t = (fun x : G => (γ : G) * x) ⁻¹' t := rfl
  rw [hpre, Measure.restrict_apply (hmeas ht), Measure.restrict_apply ht]
  have hS' : (fun x : G => (γ : G) * x) ⁻¹' S = S := hinv γ
  have hset : (fun x : G => (γ : G) * x) ⁻¹' t ∩ S = (fun x : G => (γ : G) * x) ⁻¹' (t ∩ S) := by
    rw [Set.preimage_inter, hS']
  rw [hset, measure_preimage_mul]

end Restrict

section NF

open NumberField NumberField.TateGlobal MeasureTheory

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_one' : ideleNorm F (1 : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  have h := ideleNorm_mul (1 : (AdeleRing (𝓞 F) F)ˣ) 1
  rw [one_mul] at h
  exact (mul_eq_left₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 F) F)ˣ)).ne').mp h.symm

theorem ideleNorm_inv' (a : (AdeleRing (𝓞 F) F)ˣ) : ideleNorm F a⁻¹ = (ideleNorm F a)⁻¹ := by
  have h := ideleNorm_mul a a⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem ideleNorm_principal (γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F)) :
    ideleNorm F (γ : (AdeleRing (𝓞 F) F)ˣ) = 1 := by
  obtain ⟨_, a, rfl⟩ := γ
  borelize (AdeleRing (𝓞 F) F)
  have h := NumberField.AdeleRing.distribHaarChar_algebraMap F a
  unfold ideleNorm
  simp only [RingHom.toMonoidHom_eq_coe] at h ⊢
  rw [h]
  rfl

def shell (n : ℤ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {a | Real.exp (n : ℝ) ≤ ideleNorm F a ∧ ideleNorm F a < Real.exp ((n : ℝ) + 1)}

variable {F}

theorem mem_shell_iff (n : ℤ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ shell F n ↔ Real.exp (n : ℝ) ≤ ideleNorm F a ∧ ideleNorm F a < Real.exp ((n : ℝ) + 1) := Iff.rfl

theorem measurableSet_shell [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] (n : ℤ) :
    MeasurableSet (shell F n) := by
  have hNm : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  exact (measurableSet_le measurable_const hNm).inter (measurableSet_lt hNm measurable_const)

theorem preimage_mul_shell_of_norm_one {u : (AdeleRing (𝓞 F) F)ˣ} (hu : ideleNorm F u = 1) (n : ℤ) :
    (fun x : (AdeleRing (𝓞 F) F)ˣ => u * x) ⁻¹' shell F n = shell F n := by
  ext x
  simp only [Set.mem_preimage, mem_shell_iff, ideleNorm_mul, hu, one_mul]

theorem exists_mem_shell (a : (AdeleRing (𝓞 F) F)ˣ) : ∃ n : ℤ, a ∈ shell F n := by
  refine ⟨⌊Real.log (ideleNorm F a)⌋, ?_, ?_⟩
  · calc Real.exp ((⌊Real.log (ideleNorm F a)⌋ : ℤ) : ℝ)
        ≤ Real.exp (Real.log (ideleNorm F a)) := Real.exp_le_exp.mpr (Int.floor_le _)
      _ = ideleNorm F a := Real.exp_log (ideleNorm_pos a)
  · calc ideleNorm F a = Real.exp (Real.log (ideleNorm F a)) := (Real.exp_log (ideleNorm_pos a)).symm
      _ < Real.exp (((⌊Real.log (ideleNorm F a)⌋ : ℤ) : ℝ) + 1) :=
        Real.exp_lt_exp.mpr (Int.lt_floor_add_one _)

theorem shell_inter_preimage_mul_inv {g : (AdeleRing (𝓞 F) F)ˣ} {n : ℤ} (hg : ideleNorm F g = Real.exp n)
    (T : Set (AdeleRing (𝓞 F) F)ˣ) :
    shell F n ∩ ((fun x : (AdeleRing (𝓞 F) F)ˣ => x * g⁻¹) ⁻¹' T)
      = (fun x : (AdeleRing (𝓞 F) F)ˣ => x * g⁻¹) ⁻¹' (shell F 0 ∩ T) := by
  have hen : 0 < Real.exp (n : ℝ) := Real.exp_pos _
  have key : ∀ y : ℝ, (Real.exp (n : ℝ) ≤ y ∧ y < Real.exp ((n : ℝ) + 1)) ↔
      (Real.exp ((0 : ℤ) : ℝ) ≤ y * (Real.exp (n : ℝ))⁻¹ ∧
        y * (Real.exp (n : ℝ))⁻¹ < Real.exp (((0 : ℤ) : ℝ) + 1)) := by
    intro y
    rw [Int.cast_zero, Real.exp_zero, zero_add, ← div_eq_mul_inv, one_le_div hen, div_lt_iff₀ hen,
      ← Real.exp_add, add_comm (1 : ℝ) n]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, mem_shell_iff]
  rw [ideleNorm_mul, ideleNorm_inv', hg]
  exact and_congr (key _) Iff.rfl

theorem weight_le_of_mem_shell {r : ℝ} {k : ℕ} (hkr : |r| < k) {n : ℤ} {a : (AdeleRing (𝓞 F) F)ˣ}
    (ha : a ∈ shell F n) :
    min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r ≤
      Real.exp ((k : ℝ) + |r|) * Real.exp (-(((k : ℝ) - |r|) * |(n : ℝ)|)) := by
  have h1 : Real.exp (n : ℝ) ≤ ideleNorm F a := ha.1
  have h2 : ideleNorm F a < Real.exp ((n : ℝ) + 1) := ha.2
  have hNpos : 0 < ideleNorm F a := ideleNorm_pos a
  have hl1 : (n : ℝ) ≤ Real.log (ideleNorm F a) := by
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  have hl2 : Real.log (ideleNorm F a) < (n : ℝ) + 1 := by
    have := Real.log_lt_log hNpos h2
    rwa [Real.log_exp] at this
  have hmin : min (ideleNorm F a) (ideleNorm F a)⁻¹ = Real.exp (-|Real.log (ideleNorm F a)|) := by
    rcases le_or_gt 1 (ideleNorm F a) with hN1' | hN1'
    · rw [min_eq_right (le_trans (inv_le_one_of_one_le₀ hN1') hN1'),
        abs_of_nonneg (Real.log_nonneg hN1'), Real.exp_neg, Real.exp_log hNpos]
    · rw [min_eq_left (le_trans hN1'.le (one_le_inv_iff₀.mpr ⟨hNpos, hN1'.le⟩)),
        abs_of_neg (Real.log_neg hNpos hN1'), neg_neg, Real.exp_log hNpos]
  have hpow : min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k =
      Real.exp (-(k : ℝ) * |Real.log (ideleNorm F a)|) := by
    rw [hmin, ← Real.exp_nat_mul]
    ring_nf
  have hrpow : ideleNorm F a ^ r = Real.exp (r * Real.log (ideleNorm F a)) := by
    rw [Real.rpow_def_of_pos hNpos, mul_comm]
  have hrle : r * Real.log (ideleNorm F a) ≤ |r| * |Real.log (ideleNorm F a)| := by
    rw [← abs_mul]
    exact le_abs_self _
  have habs : |(n : ℝ)| - 1 ≤ |Real.log (ideleNorm F a)| := by
    rcases le_or_gt 0 (n : ℝ) with hn | hn
    · rw [abs_of_nonneg hn]
      have : (n : ℝ) ≤ |Real.log (ideleNorm F a)| := le_trans hl1 (le_abs_self _)
      linarith
    · rw [abs_of_neg hn]
      have : -Real.log (ideleNorm F a) ≤ |Real.log (ideleNorm F a)| := neg_le_abs _
      linarith
  have hkpos : (0 : ℝ) ≤ k - |r| := by linarith
  calc min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r
      = Real.exp (-(k : ℝ) * |Real.log (ideleNorm F a)|) * Real.exp (r * Real.log (ideleNorm F a)) := by
          rw [hpow, hrpow]
    _ ≤ Real.exp (-(k : ℝ) * |Real.log (ideleNorm F a)|) * Real.exp (|r| * |Real.log (ideleNorm F a)|) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hrle) (Real.exp_pos _).le
    _ = Real.exp (-((k : ℝ) - |r|) * |Real.log (ideleNorm F a)|) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp (-((k : ℝ) - |r|) * (|(n : ℝ)| - 1)) := by
          refine Real.exp_le_exp.mpr ?_
          have := mul_le_mul_of_nonneg_left habs hkpos
          linarith
    _ = Real.exp ((k : ℝ) - |r|) * Real.exp (-(((k : ℝ) - |r|) * |(n : ℝ)|)) := by
          rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((k : ℝ) + |r|) * Real.exp (-(((k : ℝ) - |r|) * |(n : ℝ)|)) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [abs_nonneg r])) (Real.exp_pos _).le

theorem summable_shell_bound {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    Summable fun n : ℤ => c * Real.exp (-(δ * |(n : ℝ)|)) := by
  have hnat : Summable fun n : ℕ => Real.exp (-(δ * n)) := by
    have := Real.summable_exp_nat_mul_iff.mpr (neg_lt_zero.mpr hδ)
    refine this.congr fun n => ?_
    ring_nf
  refine (Summable.of_nat_of_neg ?_ ?_).mul_left c
  · refine hnat.congr fun n => ?_
    simp only [Int.cast_natCast, Nat.abs_cast]
  · refine hnat.congr fun n => ?_
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]

theorem exists_isCompact_principal_cover :
    ∃ K₁ : Set ↥(normOneIdeles F), IsCompact K₁ ∧
      ∀ x : ↥(normOneIdeles F),
        ∃ p ∈ (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F), p * x ∈ K₁ := by
  haveI : CompactSpace (↥(normOneIdeles F) ⧸
      (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) :=
    NumberField.TateGlobal.compactSpace_normOneIdeleClass F
  have hcl : IsClosed (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) := by
    have h : (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) = ideleNorm F ⁻¹' {1} := by
      ext x
      exact mem_normOneIdeles_iff x
    rw [h]
    exact isClosed_singleton.preimage (NumberField.TateGlobal.continuous_ideleNorm F)
  haveI : LocallyCompactSpace ↥(normOneIdeles F) := hcl.locallyCompactSpace
  have hC : ∀ q : ↥(normOneIdeles F) ⧸
      (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F),
      ∃ C : Set ↥(normOneIdeles F), IsCompact C ∧ C ∈ nhds (Quotient.out q) := fun _ =>
    exists_compact_mem_nhds _
  choose Cq hCc hCn using hC
  have hopen : ∀ q, IsOpen (QuotientGroup.mk '' interior (Cq q) :
      Set (↥(normOneIdeles F) ⧸
        (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F))) := fun q =>
    QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ isOpen_interior
  have hcover : (Set.univ : Set (↥(normOneIdeles F) ⧸
      (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F))) ⊆
      ⋃ q, QuotientGroup.mk '' interior (Cq q) := by
    intro q _
    exact Set.mem_iUnion.mpr ⟨q, Quotient.out q,
      mem_interior_iff_mem_nhds.mpr (hCn q), Quotient.out_eq q⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ hopen hcover
  refine ⟨⋃ q ∈ t, Cq q, t.finite_toSet.isCompact_biUnion (fun q _ => hCc q), ?_⟩
  intro x
  have hx : (QuotientGroup.mk x : ↥(normOneIdeles F) ⧸
      (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F)) ∈
      ⋃ q ∈ t, QuotientGroup.mk '' interior (Cq q) := ht (Set.mem_univ _)
  obtain ⟨q, hqt, hmem⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨y, hy, hyx⟩ := hmem
  have hg : y⁻¹ * x ∈
      (M4aHerbrand.principalIdeles (𝓞 F) F).subgroupOf (normOneIdeles F) :=
    QuotientGroup.eq.mp hyx
  refine ⟨x⁻¹ * y, ?_, ?_⟩
  · have hid : x⁻¹ * y = (y⁻¹ * x)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [hid]
    exact inv_mem hg
  · have hpx : (x⁻¹ * y) * x = y := by
      rw [mul_comm (x⁻¹) y, mul_assoc, inv_mul_cancel, mul_one]
    rw [hpx]
    exact Set.mem_biUnion hqt (interior_subset hy)

set_option maxHeartbeats 4000000 in

theorem measure_shell_zero_inter_lt_top
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    [Countable ↥(M4aHerbrand.principalIdeles (𝓞 F) F)]
    {T : Set (AdeleRing (𝓞 F) F)ˣ} (hTm : MeasurableSet T)
    (hT : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ∃! γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
      (γ : (AdeleRing (𝓞 F) F)ˣ) * x ∈ T)
    (σ : ℝ → (AdeleRing (𝓞 F) F)ˣ) (hσc : Continuous σ) (hσN : ∀ y, ideleNorm F (σ y) = Real.exp y) :
    ν (shell F 0 ∩ T) < ⊤ := by
  obtain ⟨K₁, hK₁c, hK₁cov⟩ := exists_isCompact_principal_cover (F := F)
  obtain ⟨K₁', hK₁'def⟩ : ∃ K₁' : Set (AdeleRing (𝓞 F) F)ˣ,
      K₁' = ((↑) : ↥(normOneIdeles F) → (AdeleRing (𝓞 F) F)ˣ) '' K₁ := ⟨_, rfl⟩
  have hK₁'c : IsCompact K₁' := by rw [hK₁'def]; exact hK₁c.image continuous_subtype_val
  have hK₁'N : ∀ k ∈ K₁', ideleNorm F k = 1 := by
    rintro k hk
    rw [hK₁'def] at hk
    obtain ⟨k', -, rfl⟩ := hk
    exact (mem_normOneIdeles_iff _).mp k'.2
  have hK₁'mem : ∀ (p : ↥(normOneIdeles F)) (z : ↥(normOneIdeles F)), p * z ∈ K₁ →
      (p : (AdeleRing (𝓞 F) F)ˣ) * (z : (AdeleRing (𝓞 F) F)ˣ) ∈ K₁' := by
    intro p z hpz
    rw [hK₁'def]
    exact ⟨p * z, hpz, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Set (AdeleRing (𝓞 F) F)ˣ,
      K = ⋃ m : ℤ, K₁' * (σ '' Set.Icc (m : ℝ) ((m : ℝ) + 1)) := ⟨_, rfl⟩
  have hKpiece : ∀ m : ℤ, IsCompact (K₁' * (σ '' Set.Icc (m : ℝ) ((m : ℝ) + 1))) := fun m =>
    hK₁'c.mul (isCompact_Icc.image hσc)
  have hKm : MeasurableSet K := by
    rw [hKdef]
    exact MeasurableSet.iUnion fun m => (hKpiece m).measurableSet
  have hKcov : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ∃ p : ↥(M4aHerbrand.principalIdeles (𝓞 F) F), x ∈ p • K := by
    intro x
    set y : ℝ := Real.log (ideleNorm F x) with hydef
    have hx1 : x * (σ y)⁻¹ ∈ normOneIdeles F := by
      rw [mem_normOneIdeles_iff, ideleNorm_mul, ideleNorm_inv', hσN, hydef, Real.exp_log (ideleNorm_pos x),
        mul_inv_cancel₀ (ideleNorm_pos x).ne']
    obtain ⟨p, hp, hpK⟩ := hK₁cov ⟨x * (σ y)⁻¹, hx1⟩
    have hp' : ((p : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) ∈ M4aHerbrand.principalIdeles (𝓞 F) F :=
      (Subgroup.mem_subgroupOf).mp hp
    have hmem : ((p : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) * (x * (σ y)⁻¹) ∈ K₁' :=
      hK₁'mem p ⟨x * (σ y)⁻¹, hx1⟩ hpK
    have hσy : σ y ∈ σ '' Set.Icc ((⌊y⌋ : ℤ) : ℝ) (((⌊y⌋ : ℤ) : ℝ) + 1) :=
      ⟨y, ⟨Int.floor_le y, (Int.lt_floor_add_one y).le⟩, rfl⟩
    have hprod : ((p : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ) * x ∈ K := by
      rw [hKdef]
      refine Set.mem_iUnion.mpr ⟨⌊y⌋, ?_⟩
      have h := Set.mul_mem_mul hmem hσy
      rwa [mul_assoc, inv_mul_cancel_right] at h
    refine ⟨⟨((p : ↥(normOneIdeles F)) : (AdeleRing (𝓞 F) F)ˣ), hp'⟩⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Subgroup.mk_smul, smul_eq_mul]
    exact hprod
  have hinv0 : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
      (fun x : (AdeleRing (𝓞 F) F)ˣ => γ • x) ⁻¹' shell F 0 = shell F 0 := fun γ =>
    preimage_mul_shell_of_norm_one (ideleNorm_principal F γ) 0
  haveI : SMulInvariantMeasure ↥(M4aHerbrand.principalIdeles (𝓞 F) F) (AdeleRing (𝓞 F) F)ˣ
      (ν.restrict (shell F 0)) :=
    smulInvariantMeasure_restrict_of_invariant _ ν (measurableSet_shell 0) hinv0
  have hKfin : ν.restrict (shell F 0) K < ⊤ := by
    rw [Measure.restrict_apply hKm]
    have hsub : K ∩ shell F 0 ⊆ K₁' * (σ '' Set.Icc (-1 : ℝ) 1) := by
      rintro z ⟨hzK, hzS⟩
      rw [hKdef] at hzK
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hzK
      obtain ⟨k, hk, w, ⟨yy, hyy, rfl⟩, rfl⟩ := Set.mem_mul.mp hm
      have hk1 : ideleNorm F k = 1 := hK₁'N k hk
      have hzN : ideleNorm F (k * σ yy) = Real.exp yy := by rw [ideleNorm_mul, hk1, one_mul, hσN]
      have hzS' := (mem_shell_iff 0 _).mp hzS
      rw [hzN, Int.cast_zero, zero_add, Real.exp_le_exp, Real.exp_lt_exp] at hzS'
      exact Set.mem_mul.mpr ⟨k, hk, σ yy, ⟨yy, ⟨by linarith [hzS'.1], hzS'.2.le⟩, rfl⟩, rfl⟩
    exact lt_of_le_of_lt (measure_mono hsub) (hK₁'c.mul (isCompact_Icc.image hσc)).measure_lt_top
  have hFD : IsFundamentalDomain ↥(M4aHerbrand.principalIdeles (𝓞 F) F) T (ν.restrict (shell F 0)) :=
    IsFundamentalDomain.mk' hTm.nullMeasurableSet (fun x => by
      simpa only [Subgroup.mk_smul, Subgroup.smul_def, smul_eq_mul] using hT x)
  have h := measure_fd_lt_top_of_smul_cover (μ := ν.restrict (shell F 0)) hFD hKm hKfin hKcov
  rwa [Measure.restrict_apply hTm, Set.inter_comm] at h

theorem tempered_of_shell_measure
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) {T : Set (AdeleRing (𝓞 F) F)ˣ} (hTm : MeasurableSet T)
    (hshift : ∀ n : ℤ, ν (shell F n ∩ T) = ν (shell F 0 ∩ T)) (hfin : ν (shell F 0 ∩ T) < ⊤) (r : ℝ) :
    ∃ k : ℕ, IntegrableOn (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r) T ν := by
  refine ⟨⌊|r|⌋₊ + 1, ?_⟩
  set k : ℕ := ⌊|r|⌋₊ + 1 with hkdef
  have hkr : |r| < k := by
    rw [hkdef]
    push_cast
    exact Nat.lt_floor_add_one |r|
  have hNm : Measurable (ideleNorm F) := (NumberField.TateGlobal.continuous_ideleNorm F).measurable
  set gfun : (AdeleRing (𝓞 F) F)ˣ → ℝ := fun a =>
    min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r with hgdef
  have hgm : Measurable gfun := ((hNm.min hNm.inv).pow_const k).mul (hNm.pow_const r)
  have hg0 : ∀ a, 0 ≤ gfun a := fun a =>
    mul_nonneg (pow_nonneg (le_min (ideleNorm_pos a).le (inv_pos.mpr (ideleNorm_pos a)).le) k)
      (Real.rpow_nonneg (ideleNorm_pos a).le r)
  set c : ℤ → ℝ := fun n =>
    Real.exp ((k : ℝ) + |r|) * Real.exp (-(((k : ℝ) - |r|) * |(n : ℝ)|)) with hcdef
  have hbound : ∀ (n : ℤ) (a : (AdeleRing (𝓞 F) F)ˣ), a ∈ shell F n → gfun a ≤ c n :=
    fun n a ha => weight_le_of_mem_shell hkr ha
  have hcsum : Summable c := summable_shell_bound (by linarith) _
  have hpiece : ∀ n : ℤ, IntegrableOn gfun (shell F n ∩ T) ν := by
    intro n
    refine Measure.integrableOn_of_bounded (M := c n) ?_ hgm.aestronglyMeasurable ?_
    · rw [hshift]
      exact hfin.ne
    · filter_upwards [ae_restrict_mem ((measurableSet_shell n).inter hTm)] with a ha
      rw [Real.norm_of_nonneg (hg0 a)]
      exact hbound n a ha.1
  have hint_le : ∀ n : ℤ, ∫ a in shell F n ∩ T, ‖gfun a‖ ∂ν ≤ c n * (ν (shell F 0 ∩ T)).toReal := by
    intro n
    have h := norm_setIntegral_le_of_norm_le_const (μ := ν) (f := fun a => ‖gfun a‖) (s := shell F n ∩ T)
      (C := c n) (by rw [hshift]; exact hfin)
      (fun a ha => by rw [norm_norm, Real.norm_of_nonneg (hg0 a)]; exact hbound n a ha.1)
    rw [Real.norm_of_nonneg (integral_nonneg fun a => norm_nonneg _), measureReal_def, hshift] at h
    exact h
  have hsumint : Summable fun n : ℤ => ∫ a in shell F n ∩ T, ‖gfun a‖ ∂ν :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun a => norm_nonneg _) hint_le (hcsum.mul_right _)
  have hU : IntegrableOn gfun (⋃ n : ℤ, shell F n ∩ T) ν :=
    integrableOn_iUnion_of_summable_integral_norm hpiece hsumint
  have hTsub : T ⊆ ⋃ n : ℤ, shell F n ∩ T := fun a ha => by
    obtain ⟨n, hn⟩ := exists_mem_shell a
    exact Set.mem_iUnion.mpr ⟨n, hn, ha⟩
  exact hU.mono_set hTsub

end NF

end Ws1.K2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow.Ws1 P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow.Ws1.K2"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow.Ws1"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow.Ws1 P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow.Ws1.K2"

open scoped Pointwise in

theorem solution
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    ∃ D : Set (AdeleRing (𝓞 F) F)ˣ, MeasurableSet D ∧
      IsFundamentalDomain (M4aHerbrand.principalIdeles (𝓞 F) F) D ν ∧
      ∀ r : ℝ, ∃ k : ℕ, IntegrableOn
        (fun a => min (ideleNorm F a) (ideleNorm F a)⁻¹ ^ k * ideleNorm F a ^ r) D ν := by
  classical

  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F) := NumberField.AdeleRing.secondCountableTopology F
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (AdeleRing (𝓞 F) F)ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : Countable F := (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable
  haveI : Countable ↥(M4aHerbrand.principalIdeles (𝓞 F) F) := by
    have hFu : Countable Fˣ :=
      Function.Injective.countable (f := (Units.val : Fˣ → F)) Units.val_injective
    exact (MonoidHom.rangeRestrict_surjective
      (Units.map (algebraMap F (AdeleRing (𝓞 F) F) : F →* AdeleRing (𝓞 F) F))).countable

  obtain ⟨V, hVo, hVΓ⟩ := NumberField.AdeleRing.exists_isOpen_inter_principalIdeles_eq_singleton F
  obtain ⟨T, ⟨U, C, hU, hC, hTUC⟩, hT⟩ :=
    Subgroup.exists_exact_fundamental_domain_of_secondCountableTopology
      (M4aHerbrand.principalIdeles (𝓞 F) F) ⟨V, hVo, hVΓ⟩
  have hTm : MeasurableSet T := by
    rw [hTUC]
    exact MeasurableSet.iUnion fun n => (hU n).measurableSet.diff (hC n).measurableSet
  have hTsmul : ∀ x : (AdeleRing (𝓞 F) F)ˣ, ∃! γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F), γ • x ∈ T :=
    fun x => by simpa only [Subgroup.mk_smul, Subgroup.smul_def, smul_eq_mul] using hT x
  have hFD : IsFundamentalDomain ↥(M4aHerbrand.principalIdeles (𝓞 F) F) T ν :=
    IsFundamentalDomain.mk' hTm.nullMeasurableSet hTsmul

  obtain ⟨s, hsc, hsN, -⟩ := NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq F
  set σ : ℝ → (AdeleRing (𝓞 F) F)ˣ := fun y => s (Ws1.K2.expUnit y) with hσdef
  have hσc : Continuous σ := hsc.comp Ws1.K2.continuous_expUnit
  have hσN : ∀ y : ℝ, ideleNorm F (σ y) = Real.exp y := by
    intro y
    show ideleNorm F (s _) = _
    rw [hsN, Ws1.K2.coe_val_expUnit]

  have hshift : ∀ n : ℤ, ν (Ws1.K2.shell F n ∩ T) = ν (Ws1.K2.shell F 0 ∩ T) := by
    intro n
    have hT' : IsFundamentalDomain ↥(M4aHerbrand.principalIdeles (𝓞 F) F)
        ((fun x : (AdeleRing (𝓞 F) F)ˣ => x * (σ n)⁻¹) ⁻¹' T) ν := by
      refine IsFundamentalDomain.mk' ((measurable_mul_const _ hTm).nullMeasurableSet) fun x => ?_
      obtain ⟨γ, hγ, huniq⟩ := hTsmul (x * (σ n)⁻¹)
      refine ⟨γ, ?_, fun γ' hγ' => huniq γ' ?_⟩
      · simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul] at hγ ⊢
        rwa [mul_assoc]
      · simp only [Set.mem_preimage, Subgroup.smul_def, smul_eq_mul] at hγ' ⊢
        rwa [mul_assoc] at hγ'
    have hinv : ∀ γ : ↥(M4aHerbrand.principalIdeles (𝓞 F) F),
        (fun x : (AdeleRing (𝓞 F) F)ˣ => γ • x) ⁻¹' Ws1.K2.shell F n = Ws1.K2.shell F n := fun γ =>
      Ws1.K2.preimage_mul_shell_of_norm_one (Ws1.K2.ideleNorm_principal F γ) n
    rw [IsFundamentalDomain.measure_set_eq hFD hT' (Ws1.K2.measurableSet_shell n) hinv,
      Ws1.K2.shell_inter_preimage_mul_inv (hσN n) T, measure_preimage_mul_right]

  have hfin : ν (Ws1.K2.shell F 0 ∩ T) < ⊤ :=
    Ws1.K2.measure_shell_zero_inter_lt_top ν hTm hT σ hσc hσN
  exact ⟨T, hTm, hFD, fun r => Ws1.K2.tempered_of_shell_measure ν hTm hshift hfin r⟩

end S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow (solution)
