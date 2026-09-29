-- Prove2me | solution 1 for NumberField.AdelicFourier.schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2e7cbdb0-db30-5a50-bc23-5db1af3d119a

import Definitions.Def_AutomorphicForm_BaseChangePlaces
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_GodementSection
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_AdelicBox_lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
p2m_attr_erase "instance" "instCountableOfNumberField_definitions RestrictedProduct.SecondCountableTopology_of_principal instCountableElemSetSetsCofinite_definitions"
p2m_attr_erase "simp" "ContinuousAddEquiv.restrictedProductPi_apply RestrictedProduct.flatten_homeomorph_apply RestrictedProduct.flatten_homeomorph'_symm_apply ContinuousMulEquiv.restrictedProductPi_symm_apply RestrictedProduct.flatten_homeomorph'_apply RestrictedProduct.flatten_homeomorph_symm_apply ContinuousMulEquiv.restrictedProductPi_apply ContinuousAddEquiv.restrictedProductPi_symm_apply"

set_option autoImplicit false
set_option synthInstance.maxSize 1024
set_option synthInstance.maxHeartbeats 800000

open MeasureTheory Filter NumberField NumberField.InfinitePlace NumberField.AdelicHaar NumberField.AdelicFourier NumberField.AdelicBox NumberField.TateGlobal IsDedekindDomain AutomorphicForm

open scoped TensorProduct TensorProduct.RightActions ENNReal Topology SchwartzMap Classical

namespace StandardPhiE1

theorem measurableSet_of_isOpen_isCompact_pi {ι : Type} [Fintype ι] {X : Type} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (U : Set (ι → X)) (hUo : IsOpen U) (hUc : IsCompact U) :
    MeasurableSet U := by

  have hbox : ∀ f ∈ U, ∃ u : ι → Set X, (∀ a, IsOpen (u a) ∧ f a ∈ u a) ∧ Set.univ.pi u ⊆ U :=
    fun f hf => (isOpen_pi_iff'.1 hUo) f hf
  choose! u hu husub using hbox

  obtain ⟨t, hcover⟩ := hUc.elim_finite_subcover (fun f : U => Set.univ.pi (u f))
    (fun f => isOpen_set_pi Set.finite_univ fun a _ => ((hu f f.2) a).1)
    (fun f hf => Set.mem_iUnion.2 ⟨⟨f, hf⟩, fun a _ => ((hu f hf) a).2⟩)
  have hU : U = ⋃ f ∈ t, Set.univ.pi (u (f : ι → X)) := by
    refine le_antisymm hcover ?_
    exact Set.iUnion₂_subset fun f _ => husub f f.2
  rw [hU]
  exact MeasurableSet.biUnion (Finset.countable_toSet t) fun f _ =>
    MeasurableSet.univ_pi fun a => ((hu f f.2) a).1.measurableSet

variable {L : Type} [Field L] [NumberField L]

noncomputable def Φ (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ)) (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))
    (x : Fin 2 → AdeleRing (𝓞 L) L) : ℂ :=
  g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) * U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)

section Membership

variable (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ)) (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))

theorem indicator_isLocallyConstant (hUo : IsOpen U) (hUc : IsCompact U) :
    IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) :=
  AutomorphicForm.isLocallyConstant_indicator_one hUo hUc.isClosed

theorem indicator_hasCompactSupport (hUc : IsCompact U) :
    HasCompactSupport (U.indicator fun _ => (1 : ℂ)) :=
  HasCompactSupport.intro' hUc hUc.isClosed fun x hx => by simp [Set.indicator_of_notMem hx]

theorem mem_schwartzBruhat2 (hUo : IsOpen U) (hUc : IsCompact U) : Φ g U ∈ schwartzBruhat2 L :=
  mem_schwartzBruhat2_of_mem_pureTensorSet2
    (tensor_mem_pureTensorSet2 g _ (indicator_isLocallyConstant U hUo hUc) (indicator_hasCompactSupport U hUc))

theorem re_nonneg_im_eq_zero (hg : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0) (x : Fin 2 → AdeleRing (𝓞 L) L) :
    0 ≤ (Φ g U x).re ∧ (Φ g U x).im = 0 := by
  unfold Φ
  by_cases hx : (fun i => (x i).2) ∈ U
  · rw [Set.indicator_of_mem hx, mul_one]; exact hg _
  · rw [Set.indicator_of_notMem hx, mul_zero]; simp

theorem ofReal_re_eq (x : Fin 2 → AdeleRing (𝓞 L) L) :
    ENNReal.ofReal (Φ g U x).re =
      (fun y => ENNReal.ofReal (g y).re) (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
        (U.indicator fun _ => (1 : ℝ≥0∞)) (fun i => (x i).2) := by
  unfold Φ
  by_cases hx : (fun i => (x i).2) ∈ U
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one, mul_one]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero]; simp

end Membership

section Arch

variable (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))

theorem measurable_G : Measurable fun y : Fin 2 → mixedEmbedding.mixedSpace L => ENNReal.ofReal (g y).re :=
  ENNReal.measurable_ofReal.comp (Complex.continuous_re.measurable.comp g.continuous.measurable)

scoped instance isAddHaarMeasure_pi_volume :
    (Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))).IsAddHaarMeasure :=
  Measure.pi.isAddHaarMeasure _

theorem lintegral_G_ne_top :
    (∫⁻ y, ENNReal.ofReal (g y).re ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))))
      ≠ ⊤ := by
  have hint : Integrable (fun y => g y) (Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))) :=
    g.integrable
  have h2 : (∫⁻ y, ENNReal.ofReal (g y).re ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))))
      ≤ ∫⁻ y, ‖g y‖ₑ ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))) := by
    refine lintegral_mono fun y => ?_
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (Complex.re_le_norm _)
  exact ne_top_of_le_ne_top hint.2.ne h2

theorem lintegral_G_ne_zero (hg : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0) (hg0 : ∃ y, g y ≠ 0) :
    (∫⁻ y, ENNReal.ofReal (g y).re ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))))
      ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hg0
  have hre : 0 < (g y₀).re := by
    rcases (hg y₀).1.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext (by simpa using h.symm) (by simpa using (hg y₀).2)) hy₀

  set c : ℝ := (g y₀).re / 2 with hc
  have hcpos : 0 < c := by positivity
  set V : Set (Fin 2 → mixedEmbedding.mixedSpace L) := {y | c < (g y).re} with hV
  have hVo : IsOpen V := isOpen_lt continuous_const (Complex.continuous_re.comp g.continuous)
  have hy₀V : y₀ ∈ V := by show c < (g y₀).re; rw [hc]; linarith
  have hVpos : (Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))) V ≠ 0 :=
    (hVo.measure_pos _ ⟨y₀, hy₀V⟩).ne'
  intro h0
  have hle : ENNReal.ofReal c * (Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))) V ≤
      ∫⁻ y, ENNReal.ofReal (g y).re ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L))) := by
    rw [← lintegral_indicator_const hVo.measurableSet]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ V
    · rw [Set.indicator_of_mem hy]; exact ENNReal.ofReal_le_ofReal (le_of_lt hy)
    · rw [Set.indicator_of_notMem hy]; exact zero_le
  rw [h0, nonpos_iff_eq_zero, mul_eq_zero] at hle
  rcases hle with h | h
  · exact (ENNReal.ofReal_pos.2 hcpos).ne' h
  · exact hVpos h

end Arch

section Fin

variable (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L))

theorem measurable_H [MeasurableSpace (FiniteAdeleRing (𝓞 L) L)] [BorelSpace (FiniteAdeleRing (𝓞 L) L)]
    (hUo : IsOpen U) (hUc : IsCompact U) : Measurable (U.indicator fun _ => (1 : ℝ≥0∞)) :=
  measurable_const.indicator (measurableSet_of_isOpen_isCompact_pi U hUo hUc)

theorem lintegral_H_eq [MeasurableSpace (FiniteAdeleRing (𝓞 L) L)] [BorelSpace (FiniteAdeleRing (𝓞 L) L)]
    (ν : Measure (FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U) :
    ∫⁻ z, (U.indicator fun _ => (1 : ℝ≥0∞)) z ∂(Measure.pi fun _ : Fin 2 => ν) = (Measure.pi fun _ : Fin 2 => ν) U := by
  rw [lintegral_indicator_const (measurableSet_of_isOpen_isCompact_pi U hUo hUc), one_mul]

theorem pi_U_ne_top [MeasurableSpace (FiniteAdeleRing (𝓞 L) L)] [BorelSpace (FiniteAdeleRing (𝓞 L) L)]
    (ν : Measure (FiniteAdeleRing (𝓞 L) L)) [IsFiniteMeasureOnCompacts ν] [SigmaFinite ν] (hUc : IsCompact U) :
    (Measure.pi fun _ : Fin 2 => ν) U ≠ ⊤ := by

  have hsub : U ⊆ Set.pi Set.univ fun i : Fin 2 => (fun z : Fin 2 → FiniteAdeleRing (𝓞 L) L => z i) '' U := by
    intro z hz i _; exact ⟨z, hz, rfl⟩
  refine ne_top_of_le_ne_top ?_ (measure_mono hsub)
  rw [Measure.pi_pi]
  refine ENNReal.prod_ne_top fun i _ => ?_
  exact ((hUc.image (continuous_apply i)).measure_lt_top).ne

theorem pi_U_ne_zero [MeasurableSpace (FiniteAdeleRing (𝓞 L) L)] [BorelSpace (FiniteAdeleRing (𝓞 L) L)]
    (ν : Measure (FiniteAdeleRing (𝓞 L) L)) [ν.IsOpenPosMeasure] [SigmaFinite ν] (hUo : IsOpen U)
    (hUn : U.Nonempty) : (Measure.pi fun _ : Fin 2 => ν) U ≠ 0 :=
  (hUo.measure_pos _ hUn).ne'

end Fin

theorem adelicBox_pos [MeasurableSpace (AdeleRing (𝓞 L) L)]
    (μ : Measure (AdeleRing (𝓞 L) L)) [μ.IsOpenPosMeasure] : 0 < μ (adelicBox L) := by
  obtain ⟨V, hV, hne, hsub⟩ := exists_isOpen_subset_adelicBox L
  exact (hV.measure_pos μ hne).trans_le (measure_mono hsub)

theorem adelicBox_lt_top [MeasurableSpace (AdeleRing (𝓞 L) L)]
    (μ : Measure (AdeleRing (𝓞 L) L)) [IsFiniteMeasureOnCompacts μ] : μ (adelicBox L) < ⊤ := by
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset L
  exact (measure_mono hsub).trans_lt hC.measure_lt_top

theorem kappa_pos [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ : Measure (AdeleRing (𝓞 L) L)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 L) L)] [BorelSpace (FiniteAdeleRing (𝓞 L) L)]
    (ν : Measure (FiniteAdeleRing (𝓞 L) L)) [ν.IsAddHaarMeasure] :
    0 < (μ (adelicBox L)).toReal * 2 ^ nrComplexPlaces L /
        (Real.sqrt |(discr L : ℝ)| * (ν (integralFiniteAdeles (𝓞 L) L)).toReal) := by
  have h1 : 0 < (μ (adelicBox L)).toReal :=
    ENNReal.toReal_pos (adelicBox_pos μ).ne' (adelicBox_lt_top μ).ne
  have h2 : 0 < (ν (integralFiniteAdeles (𝓞 L) L)).toReal :=
    ENNReal.toReal_pos
      ((isOpen_integralFiniteAdeles L).measure_pos ν ⟨0, fun v => (v.adicCompletionIntegers L).zero_mem⟩).ne'
      (isCompact_integralFiniteAdeles L).measure_lt_top.ne
  have h3 : 0 < Real.sqrt |(discr L : ℝ)| :=
    Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero L)))
  positivity

end StandardPhiE1
p2m_reactivate "P2MW.S_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top.StandardPhiE1"

open StandardPhiE1 in
theorem solution
    (L : Type) [Field L] [NumberField L]
    (g : 𝓢((Fin 2 → mixedEmbedding.mixedSpace L), ℂ))
    (hg : ∀ y, 0 ≤ (g y).re ∧ (g y).im = 0) (hg0 : ∃ y, g y ≠ 0)
    (U : Set (Fin 2 → FiniteAdeleRing (𝓞 L) L)) (hUo : IsOpen U) (hUc : IsCompact U) (hUn : U.Nonempty)
    [MeasurableSpace (AdeleRing (𝓞 L) L)] [BorelSpace (AdeleRing (𝓞 L) L)]
    (μ₁ : Measure (AdeleRing (𝓞 L) L)) [μ₁.IsAddHaarMeasure] :
    (fun x : Fin 2 → AdeleRing (𝓞 L) L =>
        g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)) ∈ schwartzBruhat2 L ∧
    (∀ x : Fin 2 → AdeleRing (𝓞 L) L,
      0 ≤ (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∧
      (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).im = 0) ∧
    (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) ≠ 0 ∧
    (∫⁻ x, ENNReal.ofReal (g (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace L (x i).1) *
          U.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2)).re ∂(pairHaar μ₁)) ≠ ⊤ := by
  refine ⟨mem_schwartzBruhat2 g U hUo hUc, re_nonneg_im_eq_zero g U hg, ?_⟩

  letI : MeasurableSpace (FiniteAdeleRing (𝓞 L) L) := borel _
  haveI : BorelSpace (FiniteAdeleRing (𝓞 L) L) := ⟨rfl⟩
  let ν : Measure (FiniteAdeleRing (𝓞 L) L) := Measure.addHaar
  have hmass := NumberField.AdelicBox.lintegral_pi_pureTensor_two_eq_sq_mul_lintegral_pi_volume_mul_lintegral_pi
    L μ₁ ν (fun y => ENNReal.ofReal (g y).re) (measurable_G g) (U.indicator fun _ => (1 : ℝ≥0∞))
    (measurable_H U hUo hUc)
  have hΦ : (∫⁻ x, ENNReal.ofReal (Φ g U x).re ∂(pairHaar μ₁)) =
      ENNReal.ofReal ((μ₁ (adelicBox L)).toReal * 2 ^ nrComplexPlaces L /
            (Real.sqrt |(discr L : ℝ)| * (ν (integralFiniteAdeles (𝓞 L) L)).toReal)) ^ 2 *
        (∫⁻ y, ENNReal.ofReal (g y).re ∂(Measure.pi fun _ : Fin 2 => (volume : Measure (mixedEmbedding.mixedSpace L)))) *
        (Measure.pi fun _ : Fin 2 => ν) U := by
    rw [← lintegral_H_eq U ν hUo hUc, ← hmass]
    exact lintegral_congr fun x => ofReal_re_eq g U x
  change (∫⁻ x, ENNReal.ofReal (Φ g U x).re ∂(pairHaar μ₁)) ≠ 0 ∧ (∫⁻ x, ENNReal.ofReal (Φ g U x).re ∂(pairHaar μ₁)) ≠ ⊤
  rw [hΦ]
  have hκ := kappa_pos (L := L) μ₁ ν
  refine ⟨mul_ne_zero (mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.2 hκ).ne') (lintegral_G_ne_zero g hg hg0))
      (pi_U_ne_zero U ν hUo hUn), ?_⟩
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (lintegral_G_ne_top g))
    (pi_U_ne_top U ν hUc)

end S_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top
end P2MW
export P2MW.S_NumberField_AdelicFourier_schwartzMap_mul_indicator_mem_schwartzBruhat2_and_lintegral_pairHaar_ne_zero_and_ne_top (solution)
