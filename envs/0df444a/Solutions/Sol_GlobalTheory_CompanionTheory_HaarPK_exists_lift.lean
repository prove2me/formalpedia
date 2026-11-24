-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HaarPK.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:54:05.421863+00:00
-- url     : https://prove2.me/submissions/4c26e598-2aa3-48f4-9431-2129f6fbb9b2

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_HaarProductClosedCompact
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HaarProductClosedCompactHolds
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_measurable_transl_fun
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_transl_mul_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_transl_mul
import Theorems.Thm_GlobalTheory_CompanionTheory_HaarPK_isClosed_transl_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HaarPK
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
namespace GlobalTheory.CompanionTheory.HaarPK
theorem _root_.solution [SecondCountableTopology G] [T2Space G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (P K : Subgroup G) (hP : IsClosed (P : Set G))
    (hK : IsCompact (K : Set G)) (hPK : ∀ g, ∃ p ∈ P, ∃ k ∈ K, g = p * k) :
    ∃ l : Measure G, l (P : Set G)ᶜ = 0 ∧ (∀ p ∈ P, l.map (fun x => p * x) = l) ∧
      (∀ s : Set G, IsCompact s → l s ≠ ⊤) ∧
      ∀ φ : G → ℝ≥0∞, Measurable φ → (∀ x, ∀ k ∈ K, φ (x * k) = φ x) → ∫⁻ x, φ x ∂l = ∫⁻ x, φ x ∂μ := by
  set M : Subgroup G := P ⊓ K with hM
  have hMc : IsCompact (M : Set G) := hK.inter_left hP
  haveI : CompactSpace M := isCompact_iff_compactSpace.1 hMc
  let η : Measure M := Measure.haarMeasure (⊤ : PositiveCompacts M)
  haveI : IsProbabilityMeasure η := ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : PositiveCompacts M))
    simpa using this⟩
  choose s hs r hr hsr using hPK
  let κ : G → Measure G := fun g => transl M η (s g)
  haveI hκp : ∀ g, IsProbabilityMeasure (κ g) := fun g =>
    Measure.isProbabilityMeasure_map (measurable_transl_fun M _).aemeasurable
  have hκ : ∀ p ∈ P, ∀ k ∈ K, κ (p * k) = transl M η p := by
    intro p hp k hk
    have h := hsr (p * k)
    have e : p⁻¹ * s (p * k) = k * (r (p * k))⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq]; exact h.symm
    have hm : p⁻¹ * s (p * k) ∈ M :=
      ⟨P.mul_mem (P.inv_mem hp) (hs _), by rw [e]; exact K.mul_mem hk (K.inv_mem (hr _))⟩
    rw [← transl_mul_mem M η p hm]
    simp [κ]
  have hmeas : Measurable κ := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    induction A, hA using MeasurableSet.induction_on_open with
    | isOpen U hU =>
      apply measurable_of_Iic
      intro t
      have : (fun g => κ g U) ⁻¹' Iic t = ({x | transl M η x U ≤ t} ∩ (P : Set G)) * (K : Set G) := by
        ext g
        constructor
        · intro hg
          exact ⟨s g, ⟨hg, hs g⟩, r g, hr g, (hsr g).symm⟩
        · rintro ⟨p, ⟨hp1, hp2⟩, k, hk, rfl⟩
          simp only [mem_preimage, mem_Iic]
          rw [hκ p hp2 k hk]
          exact hp1
      rw [this]
      exact (((isClosed_transl_le M η hU t).inter hP).mul_right_of_isCompact hK).measurableSet
    | compl A hA ih =>
      simp only [prob_compl_eq_one_sub hA]
      exact ih.const_sub 1
    | iUnion f hd hf ih =>
      simp only [measure_iUnion hd hf]
      exact Measurable.ennreal_tsum ih
  have happ : ∀ g, ∀ A, MeasurableSet A → κ g A = η ((fun m : M => s g * (m : G)) ⁻¹' A) := fun g A hA =>
    Measure.map_apply (measurable_transl_fun M _) hA
  refine ⟨μ.bind κ, ?_, ?_, ?_, ?_⟩
  · rw [Measure.bind_apply hP.measurableSet.compl hmeas.aemeasurable]
    have : ∀ g, κ g (P : Set G)ᶜ = 0 := by
      intro g
      rw [happ g _ hP.measurableSet.compl]
      convert measure_empty (μ := η)
      ext m
      simpa using P.mul_mem (hs g) m.2.1
    simp [this]
  · intro p hp
    ext A hA
    have hA' : MeasurableSet ((fun x => p * x) ⁻¹' A) := measurable_const_mul p hA
    rw [Measure.map_apply (measurable_const_mul p) hA, Measure.bind_apply hA' hmeas.aemeasurable,
      Measure.bind_apply hA hmeas.aemeasurable, ← lintegral_mul_left_eq_self (fun g => κ g A) p]
    refine lintegral_congr fun g => ?_
    have : κ (p * g) = (κ g).map (fun x => p * x) := by
      conv_lhs => rw [hsr g, ← mul_assoc, hκ _ (P.mul_mem hp (hs g)) _ (hr g), transl_mul]
    rw [this, Measure.map_apply (measurable_const_mul p) hA]
  · intro C hC
    have hCK : IsCompact (C * (K : Set G)) := hC.mul hK
    rw [Measure.bind_apply hC.measurableSet hmeas.aemeasurable]
    refine ne_top_of_le_ne_top (hCK.measure_lt_top (μ := μ)).ne ?_
    rw [← lintegral_indicator_one hCK.measurableSet]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ C * (K : Set G)
    · rw [indicator_of_mem hg]
      exact prob_le_one
    · rw [indicator_of_notMem hg, happ g _ hC.measurableSet]
      refine le_of_eq ?_
      convert measure_empty (μ := η)
      ext m
      simp only [mem_preimage, mem_empty_iff_false, iff_false]
      intro hm
      refine hg ⟨_, hm, (m : G)⁻¹ * r g, K.mul_mem (K.inv_mem m.2.2) (hr g), ?_⟩
      simp only
      rw [mul_assoc, mul_inv_cancel_left, ← hsr]
  · intro φ hφ hinv
    rw [Measure.lintegral_bind hmeas.aemeasurable hφ.aemeasurable]
    refine lintegral_congr fun g => ?_
    simp only [κ, transl]
    rw [lintegral_map hφ (measurable_transl_fun M _)]
    have : ∀ m : M, φ (s g * m) = φ g := fun m => by
      rw [hinv _ _ m.2.2]
      conv_rhs => rw [hsr g, hinv _ _ (hr g)]
    simp [this]
end GlobalTheory.CompanionTheory.HaarPK
