-- Prove2me | solution 1 for NumberField.TateGlobal.exists_meromorphicOn_eq_partialEulerProduct
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/86651476-83b5-573f-af53-778abb8deee9

import Theorems.Thm_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe
import Theorems.Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq
import Theorems.Thm_LanglandsTunnell_TateLocal_realZeta_eq_localZeta
import Theorems.Thm_LanglandsTunnell_TateLocal_complexZeta_eq_localZeta
import Theorems.Thm_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
import Theorems.Thm_NumberField_AdelicFourier_exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_LanglandsTunnell_ArchPlace
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_StandardGlobalAddChar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.mk.sizeOf_spec M4aHerbrand.IdeleGaloisDescent.mk.injEq"

set_option autoImplicit false
set_option Elab.async false

section Fold_ArchMulHaarComplex

open MeasureTheory Set

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarComplex

private theorem det_lmul_complex (c : ℂ) :
    LinearMap.det (Algebra.lmul ℝ ℂ c) = Complex.normSq c := by
  have hap : ∀ x : ℂ, (Algebra.lmul ℝ ℂ c) x = c * x := fun _ => rfl
  rw [← LinearMap.det_toMatrix Complex.basisOneI]
  rw [Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, hap]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

private theorem smul_set_eq_image_lmul (c : ℂ) (s : Set ℂ) :
    c • s = (Algebra.lmul ℝ ℂ c) '' s := by
  ext x
  simp [Set.mem_smul_set]

private theorem measure_smul_complex (μ : Measure ℂ) [μ.IsAddHaarMeasure] (c : ℂ)
    (s : Set ℂ) :
    μ (c • s) = (‖c‖₊ ^ 2 : ℝ≥0∞) * μ s := by
  rw [smul_set_eq_image_lmul, Measure.addHaar_image_linearMap μ _ s, det_lmul_complex]
  congr 1
  rw [abs_of_nonneg (Complex.normSq_nonneg c), ← Complex.norm_mul_self_eq_normSq,
    ENNReal.ofReal_mul (norm_nonneg c), ofReal_norm, sq]
  rfl

private theorem distribHaarChar_complex (t : ℂˣ) : distribHaarChar ℂ t = ‖(t : ℂ)‖₊ ^ 2 := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume)
    (s := Metric.ball (0 : ℂ) 1)
    (ne_of_gt (Metric.measure_ball_pos volume 0 one_pos)) measure_ball_lt_top.ne ?_
  have hset : t • Metric.ball (0 : ℂ) 1 = ((t : ℂ)) • Metric.ball (0 : ℂ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, measure_smul_complex volume (t : ℂ)]
  norm_cast

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

variable [MeasurableSpace ℂˣ] [BorelSpace ℂˣ]

end ArchMulHaarComplex

end M4aLocalCFT

end

section Foot

end Foot

end Fold_ArchMulHaarComplex

section Fold_ArchMulHaarReal

open MeasureTheory Set Filter Topology

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarReal

variable (μ : Measure ℝ) [μ.IsAddHaarMeasure]

private theorem distribHaarChar_real (t : ℝˣ) : distribHaarChar ℝ t = ‖(t : ℝ)‖₊ := by
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := volume) (s := Icc (0 : ℝ) 1)
    (by simp [Real.volume_Icc]) (by simp [Real.volume_Icc]) ?_
  have hset : t • Icc (0 : ℝ) 1 = (t : ℝ) • Icc (0 : ℝ) 1 := by
    ext x
    simp only [Set.mem_smul_set, Units.smul_def]
  rw [hset, Measure.addHaar_smul volume (t : ℝ) (Icc (0 : ℝ) 1),
    Module.finrank_self, pow_one, Real.volume_Icc]
  rw [← Real.norm_eq_abs, ofReal_norm]
  rfl

variable [MeasurableSpace ℝˣ] [BorelSpace ℝˣ]

end ArchMulHaarReal

end M4aLocalCFT

end

section Foot

end Foot

end Fold_ArchMulHaarReal

section Fold_ArchMulHaarCompletion

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace ArchMulHaarCompletion

private theorem distribHaarChar_eq_of_ringEquiv {K L : Type} [Field K] [Field L]
    [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [TopologicalSpace L] [IsTopologicalRing L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L]
    (Φ : K ≃+* L) (hΦ : Continuous Φ) (hΦs : Continuous Φ.symm)
    (μL : Measure L) [μL.IsAddHaarMeasure] [μL.Regular]
    {B : Set L} (hB : MeasurableSet B) (hB0 : μL B ≠ 0) (hBt : μL B ≠ ∞)
    (t : Kˣ) :
    distribHaarChar K t = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) := by
  set e : L ≃+ K := Φ.symm.toAddEquiv with he
  have hecont : Continuous e := hΦs
  have hescont : Continuous e.symm := hΦ
  letI μK : Measure K := μL.map e
  haveI : μK.IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μL e hecont hescont
  haveI : μK.Regular :=
    Measure.Regular.map (⟨e.toEquiv, hecont, hescont⟩ : L ≃ₜ K)
  have key : ∀ (S : Set L), MeasurableSet S → μK (⇑Φ ⁻¹' S) = μL S := by
    intro S hS
    have hpre : ⇑e ⁻¹' (⇑Φ ⁻¹' S) = S := by
      ext x
      simp only [Set.mem_preimage, he]
      rw [show (Φ.symm.toAddEquiv x : K) = Φ.symm x from rfl, RingEquiv.apply_symm_apply]
    rw [show μK = μL.map e from rfl,
      Measure.map_apply hecont.measurable (hΦ.measurable hS), hpre]
  have hsmeas : MeasurableSet (⇑Φ ⁻¹' B) := hΦ.measurable hB
  have hs0 : μK (⇑Φ ⁻¹' B) ≠ 0 := by rw [key B hB]; exact hB0
  have hst : μK (⇑Φ ⁻¹' B) ≠ ∞ := by rw [key B hB]; exact hBt
  have hcomm : ∀ (u : Kˣ) (y : K),
      Φ ((u : K) * y) = ((Units.map (Φ : K →+* L).toMonoidHom u : Lˣ) : L) * Φ y := by
    intro u y
    rw [map_mul]
    rfl
  have hts : (t • (⇑Φ ⁻¹' B) : Set K)
      = ⇑Φ ⁻¹' ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine Set.mem_preimage.mpr ?_
      have hfwd : Φ (t • y) = (Units.map (Φ : K →+* L).toMonoidHom t) • Φ y := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul]
        exact hcomm t y
      show Φ (t • y) ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B
      rw [hfwd]
      exact Set.smul_mem_smul_set hy
    · intro hx
      have hx' : Φ x ∈ (Units.map (Φ : K →+* L).toMonoidHom t) • B := Set.mem_preimage.mp hx
      refine ⟨(t⁻¹ : Kˣ) • x, Set.mem_preimage.mpr ?_, smul_inv_smul t x⟩
      have hbwd : Φ ((t⁻¹ : Kˣ) • x)
          = ((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) • Φ x := by
        rw [Units.smul_def, Units.smul_def, smul_eq_mul, smul_eq_mul, hcomm t⁻¹ x, map_inv]
      rw [hbwd]
      exact Set.mem_smul_set_iff_inv_smul_mem.mp hx'
  have hmul : μK (t • (⇑Φ ⁻¹' B))
      = distribHaarChar L (Units.map (Φ : K →+* L).toMonoidHom t) * μK (⇑Φ ⁻¹' B) := by
    have hBs : MeasurableSet ((Units.map (Φ : K →+* L).toMonoidHom t) • B) := by
      have : ((Units.map (Φ : K →+* L).toMonoidHom t) • B : Set L)
          = (fun y => (((Units.map (Φ : K →+* L).toMonoidHom t)⁻¹ : Lˣ) : L) * y) ⁻¹' B := by
        ext y
        rw [Set.mem_smul_set_iff_inv_smul_mem]
        rfl
      rw [this]
      exact hB.preimage (measurable_const_mul _)
    rw [hts, key _ hBs, key B hB, ← distribHaarChar_mul (μ := μL)]
  exact distribHaarChar_eq_of_measure_smul_eq_mul hs0 hst hmul

variable {F : Type} [Field F]

private theorem nnnorm_ringEquivReal {w : InfinitePlace F} (hv : w.IsReal)
    (x : w.Completion) : ‖ringEquivRealOfIsReal hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) x

private theorem nnnorm_ringEquivComplex {w : InfinitePlace F} (hv : w.IsComplex)
    (x : w.Completion) : ‖ringEquivComplexOfIsComplex hv x‖₊ = ‖x‖₊ := by
  ext
  exact (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

variable (w : InfinitePlace F) [MeasurableSpace w.Completion] [BorelSpace w.Completion]

private theorem distribHaarChar_completion_of_isReal (hv : w.IsReal) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 1 := by
  have hiso := isometry_extensionEmbeddingOfIsReal hv
  have hcont : Continuous (ringEquivRealOfIsReal hv) := hiso.continuous
  have hconts : Continuous (ringEquivRealOfIsReal hv).symm := by
    have : Isometry (isometryEquivRealOfIsReal hv).symm := (isometryEquivRealOfIsReal hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivRealOfIsReal hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarReal.distribHaarChar_real, pow_one]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact nnnorm_ringEquivReal hv _

private theorem distribHaarChar_completion_of_isComplex (hv : w.IsComplex) (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ 2 := by
  have hcont : Continuous (ringEquivComplexOfIsComplex hv) := (isometry_extensionEmbedding w).continuous
  have hconts : Continuous (ringEquivComplexOfIsComplex hv).symm := by
    have : Isometry (isometryEquivComplexOfIsComplex hv).symm :=
      (isometryEquivComplexOfIsComplex hv).symm.isometry
    exact this.continuous
  rw [distribHaarChar_eq_of_ringEquiv (ringEquivComplexOfIsComplex hv) hcont hconts volume
    (B := Metric.ball 0 1) measurableSet_ball
    ((Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr one_pos)).ne')
    measure_ball_lt_top.ne t, ArchMulHaarComplex.distribHaarChar_complex]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  exact congrArg (fun a => a ^ 2) (nnnorm_ringEquivComplex hv _)

variable {μ : Measure w.Completion} [μ.IsAddHaarMeasure] [μ.Regular]

variable [MeasurableSpace (w.Completion)ˣ] [BorelSpace (w.Completion)ˣ]

end ArchMulHaarCompletion

end M4aLocalCFT

end

section Foot

end Foot

end Fold_ArchMulHaarCompletion

section Fold_PlaceSum

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain"

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type*} [Field F] [NumberField F]

private abbrev underZ (v : HeightOneSpectrum (𝓞 F)) : Ideal ℤ := v.asIdeal.under ℤ

private theorem absNorm_ne_zero (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm v.asIdeal ≠ 0 := by
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact v.ne_bot

private theorem underZ_ne_bot (v : HeightOneSpectrum (𝓞 F)) : underZ v ≠ ⊥ := by
  intro h
  have hmem : ((Ideal.absNorm v.asIdeal : ℤ)) ∈ underZ v := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem v.asIdeal
  rw [h, Ideal.mem_bot] at hmem
  exact absNorm_ne_zero v (by exact_mod_cast hmem)

private theorem absNorm_underZ_dvd (v : HeightOneSpectrum (𝓞 F)) :
    Ideal.absNorm (underZ v) ∣ Ideal.absNorm v.asIdeal := by
  have hinj : Function.Injective (Ideal.quotientMap v.asIdeal (algebraMap ℤ (𝓞 F)) le_rfl) :=
    Ideal.quotientMap_injective
  have h := AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap v.asIdeal (algebraMap ℤ (𝓞 F)) le_rfl).toAddMonoidHom hinj
  rwa [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]

private theorem absNorm_underZ_pos (v : HeightOneSpectrum (𝓞 F)) : 0 < Ideal.absNorm (underZ v) := by
  rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact underZ_ne_bot v

private theorem absNorm_underZ_le (v : HeightOneSpectrum (𝓞 F)) : Ideal.absNorm (underZ v) ≤ Ideal.absNorm v.asIdeal :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero (absNorm_ne_zero v)) (absNorm_underZ_dvd v)

private theorem card_filter_underZ_le [DecidableEq (Ideal ℤ)] (U : Finset (HeightOneSpectrum (𝓞 F))) (q : Ideal ℤ)
    (hq : ∃ v ∈ U, underZ v = q) :
    (U.filter fun v => underZ v = q).card ≤ Module.finrank ℚ F := by
  obtain ⟨v₀, _, hv₀⟩ := hq
  haveI : v₀.asIdeal.IsMaximal := v₀.isPrime.isMaximal v₀.ne_bot
  haveI : q.IsMaximal := hv₀ ▸ (Ideal.IsMaximal.under ℤ v₀.asIdeal)
  have hq0 : q ≠ ⊥ := hv₀ ▸ underZ_ne_bot v₀
  refine le_trans ?_ (Ideal.card_primesOverFinset_le_finrank (𝓞 F) ℚ F hq0)
  refine Finset.card_le_card_of_injOn (fun v => v.asIdeal) (fun v hv => ?_) ?_
  · rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hq0]
    exact ⟨v.isPrime, ⟨hv.2.symm⟩⟩
  · intro v _ w _ h
    exact HeightOneSpectrum.ext h

private theorem int_ideal_eq_span_absNorm (q : Ideal ℤ) : q = Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)} := by
  set g : ℤ := Submodule.IsPrincipal.generator q with hg
  have hq : q = Ideal.span {g} := (Submodule.IsPrincipal.span_singleton_generator q).symm
  rw [hq, Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply, Int.span_natAbs]

private theorem summable_absNorm_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  classical
  set g : ℕ → ℝ := fun n => (n : ℝ) ^ (-σ) with hg
  have hg0 : ∀ n, 0 ≤ g n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hgs : Summable g := Real.summable_nat_rpow.mpr (by linarith)
  have hdecay : ∀ v : HeightOneSpectrum (𝓞 F),
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) ≤ g (Ideal.absNorm (underZ v)) := by
    intro v
    refine Real.rpow_le_rpow_of_nonpos ?_ ?_ (by linarith)
    · exact_mod_cast absNorm_underZ_pos v
    · exact_mod_cast absNorm_underZ_le v
  refine summable_of_sum_le (fun v => Real.rpow_nonneg (Nat.cast_nonneg _) _) (c := Module.finrank ℚ F * ∑' n, g n)
    fun U => ?_
  set key : HeightOneSpectrum (𝓞 F) → Ideal ℤ := underZ with hkey
  calc ∑ v ∈ U, (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ)
      ≤ ∑ v ∈ U, g (Ideal.absNorm (key v)) := Finset.sum_le_sum fun v _ => hdecay v
    _ = ∑ q ∈ U.image key, ((U.filter fun v => key v = q).card : ℝ) * g (Ideal.absNorm q) := by
        rw [Finset.sum_comp (fun q : Ideal ℤ => g (Ideal.absNorm q)) key]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [nsmul_eq_mul]
    _ ≤ ∑ q ∈ U.image key, (Module.finrank ℚ F : ℝ) * g (Ideal.absNorm q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨v, hv, hvq⟩ := Finset.mem_image.mp hq
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_filter_underZ_le U q ⟨v, hv, hvq⟩) (hg0 _)
    _ = (Module.finrank ℚ F : ℝ) * ∑ q ∈ U.image key, g (Ideal.absNorm q) := by rw [Finset.mul_sum]
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑ n ∈ (U.image key).image Ideal.absNorm, g n := by
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hinj : Set.InjOn (fun q : Ideal ℤ => Ideal.absNorm q) ↑(U.image key) := by
          intro q _ q' _ h
          rw [int_ideal_eq_span_absNorm q, int_ideal_eq_span_absNorm q']
          simp only at h
          rw [h]
        exact le_of_eq (Finset.sum_image hinj).symm
    _ ≤ (Module.finrank ℚ F : ℝ) * ∑' n, g n :=
        mul_le_mul_of_nonneg_left (hgs.sum_le_tsum _ fun n _ => hg0 n) (Nat.cast_nonneg _)

end NumberField.TateGlobal

end

end Fold_PlaceSum

section Fold_TateSDecomp

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

private theorem one_mem_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (1 : AdeleRing (𝓞 F) F) ∈ integralOutside S :=
  fun v _ => (v.adicCompletionIntegers F).one_mem

private theorem mul_mem_integralOutside {S : Finset (HeightOneSpectrum (𝓞 F))} {x y : AdeleRing (𝓞 F) F}
    (hx : x ∈ integralOutside S) (hy : y ∈ integralOutside S) : x * y ∈ integralOutside S :=
  fun v hv => mul_mem (hx v hv) (hy v hv)

private theorem isOpen_integralOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOutside (F := F) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    Fact.out (p := fun v => v ∉ S)
  exact h.preimage (continuous_adeleFin (𝓞 F) F)

private def unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) : Subgroup (AdeleRing (𝓞 F) F)ˣ where
  carrier := {x | (x : AdeleRing (𝓞 F) F) ∈ integralOutside S ∧
    ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ integralOutside S}
  one_mem' := ⟨by simpa using one_mem_integralOutside S, by simpa using one_mem_integralOutside S⟩
  mul_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨?_, ?_⟩
    · simpa using mul_mem_integralOutside hx hy
    · simpa [mul_inv_rev] using mul_mem_integralOutside hy' hx'
  inv_mem' := by
    rintro x ⟨hx, hx'⟩
    exact ⟨hx', by simpa using hx⟩

private theorem mem_unitsOutside_iff (S : Finset (HeightOneSpectrum (𝓞 F))) (x : (AdeleRing (𝓞 F) F)ˣ) :
    x ∈ unitsOutside S ↔
      (∀ v ∉ S, ((x : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F) ∧
      (∀ v ∉ S, (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F) :=
  Iff.rfl

private theorem isOpen_unitsOutside (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (unitsOutside (F := F) S : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have h1 : IsOpen ((fun x : (AdeleRing (𝓞 F) F)ˣ => (x : AdeleRing (𝓞 F) F)) ⁻¹' integralOutside S) :=
    (isOpen_integralOutside S).preimage Units.continuous_val
  have h2 : IsOpen ((fun x : (AdeleRing (𝓞 F) F)ˣ => ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
      ⁻¹' integralOutside S) :=
    (isOpen_integralOutside S).preimage Units.continuous_coe_inv
  exact h1.inter h2

section CharTriviality

open Filter Topology

variable (x : (AdeleRing (𝓞 F) F)ˣ)

private theorem inv_val_fst_eq_one (h1 : ((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1) :
    (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 = 1 := by
  have h := congrArg Prod.fst x.mul_inv
  change (x : AdeleRing (𝓞 F) F).1 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1
    = (1 : InfiniteAdeleRing F) at h
  rw [h1, one_mul] at h
  exact h

end CharTriviality

end NumberField.TateGlobal

end

end Fold_TateSDecomp

section Fold_ValuationOrd

namespace M4aLocalCFT

namespace ValuationOrd

open Ideal IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

private theorem exists_span_eq_pow {a : A} (ha : a ≠ 0) :
    ∃ n, span {a} = maximalIdeal A ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible ha hϖ
  refine ⟨n, ?_⟩
  rw [span_singleton_eq_span_singleton.mpr hn, ← span_singleton_pow, ← hϖ.maximalIdeal_eq]

private theorem pow_maximalIdeal_ne_of_lt {n k : ℕ} (h : n < k) :
    (maximalIdeal A) ^ n ≠ maximalIdeal A ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  intro heq
  have hmem : ϖ ^ n ∈ maximalIdeal A ^ k := by
    rw [← heq, hϖ.maximalIdeal_eq, span_singleton_pow]
    exact mem_span_singleton_self _
  rw [hϖ.maximalIdeal_eq, span_singleton_pow, mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have h1 : (1 : A) = ϖ ^ (k - n) * c := by
    refine mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) ?_
    rw [mul_one, ← mul_assoc, ← pow_add]
    rw [show n + (k - n) = k from by omega]
    exact hc
  have hkn : k - n - 1 + 1 = k - n := by omega
  exact hϖ.not_isUnit (isUnit_of_dvd_one ⟨ϖ ^ (k - n - 1) * c, by
    rw [h1, ← mul_assoc, ← pow_succ', hkn]⟩)

private theorem pow_maximalIdeal_injective {n k : ℕ}
    (h : (maximalIdeal A) ^ n = maximalIdeal A ^ k) : n = k := by
  rcases Nat.lt_trichotomy n k with hlt | heq | hgt
  · exact absurd h (pow_maximalIdeal_ne_of_lt A hlt)
  · exact heq
  · exact absurd h.symm (pow_maximalIdeal_ne_of_lt A hgt)

open Classical in
private noncomputable def ordA (a : A) : ℕ :=
  if h : a = 0 then 0 else (exists_span_eq_pow A h).choose

private theorem ordA_span {a : A} (ha : a ≠ 0) :
    span {a} = maximalIdeal A ^ ordA A a := by
  classical
  rw [ordA, dif_neg ha]
  exact (exists_span_eq_pow A ha).choose_spec

private theorem ordA_unique {a : A} (ha : a ≠ 0) {n : ℕ}
    (h : span {a} = maximalIdeal A ^ n) : ordA A a = n :=
  pow_maximalIdeal_injective A ((ordA_span A ha).symm.trans h)

private theorem ordA_mul {a b : A} (ha : a ≠ 0) (hb : b ≠ 0) :
    ordA A (a * b) = ordA A a + ordA A b := by
  refine ordA_unique A (mul_ne_zero ha hb) ?_
  rw [← span_singleton_mul_span_singleton, ordA_span A ha, ordA_span A hb, pow_add]

open Classical in
private noncomputable def ordZ (x : Lˣ) : ℤ :=
  if h : (x : L) ∈ A then (ordA A ⟨(x : L), h⟩ : ℤ)
  else -(ordA A ⟨((x⁻¹ : Lˣ) : L), by
    rw [Units.val_inv_eq_inv_val]
    exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ : ℤ)

omit [IsDiscreteValuationRing ↥A] in
private theorem coe_mk_ne_zero (x : Lˣ) {y : L} (hy : y ∈ A) (hxy : y = (x : L)) :
    (⟨y, hy⟩ : A) ≠ 0 := by
  intro h0
  have : y = 0 := congrArg Subtype.val h0
  exact x.ne_zero (hxy ▸ this)

private theorem ordZ_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) : ordZ A x = (ordA A a : ℤ) - ordA A b := by
  classical
  by_cases h : (x : L) ∈ A
  · rw [ordZ, dif_pos h]
    have hab : (⟨(x : L), h⟩ : A) * b = a := Subtype.ext hx
    have hmul := ordA_mul A (coe_mk_ne_zero A x h rfl) hb
    rw [hab] at hmul
    omega
  · rw [ordZ, dif_neg h]
    set c : A := ⟨((x⁻¹ : Lˣ) : L), by
      rw [Units.val_inv_eq_inv_val]
      exact (A.mem_or_inv_mem (x : L)).resolve_left h⟩ with hc
    have hcx : (c : A) ≠ 0 := coe_mk_ne_zero A x⁻¹ _ rfl
    have hab : a * c = b := by
      refine Subtype.ext ?_
      push_cast
      have hcL : (c : L) = ((x : L))⁻¹ := by rw [hc]; exact Units.val_inv_eq_inv_val x
      rw [hcL, ← hx, mul_comm ((x : L)) ((b : L)), mul_assoc,
        mul_inv_cancel₀ x.ne_zero, mul_one]
    have hmul := ordA_mul A ha hcx
    rw [hab] at hmul
    omega

omit [IsDiscreteValuationRing ↥A] in
private theorem exists_rep (x : Lˣ) :
    ∃ a b : A, a ≠ 0 ∧ b ≠ 0 ∧ (x : L) * (b : L) = (a : L) := by
  rcases A.mem_or_inv_mem (x : L) with h | h
  · exact ⟨⟨(x : L), h⟩, 1, coe_mk_ne_zero A x h rfl, one_ne_zero, by
      push_cast; exact mul_one _⟩
  · refine ⟨1, ⟨((x⁻¹ : Lˣ) : L), by rwa [Units.val_inv_eq_inv_val]⟩,
      one_ne_zero, coe_mk_ne_zero A x⁻¹ _ rfl, ?_⟩
    show (x : L) * ((x⁻¹ : Lˣ) : L) = (1 : L)
    exact x.mul_inv

private noncomputable def ord : Additive Lˣ →+ ℤ where
  toFun x := ordZ A x.toMul
  map_zero' := by
    show ordZ A (1 : Lˣ) = 0
    have h1 := ordZ_spec A (x := 1) (a := 1) (b := 1) one_ne_zero one_ne_zero
      (by rw [Units.val_one, one_mul])
    rw [h1]
    ring
  map_add' x y := by
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x.toMul
    obtain ⟨c, d, hc, hd, hy⟩ := exists_rep A y.toMul
    have hxy : (((x + y).toMul : Lˣ) : L) * ((b * d : A) : L) = ((a * c : A) : L) := by
      push_cast
      calc (x.toMul : L) * (y.toMul : L) * ((b : L) * (d : L))
          = ((x.toMul : L) * (b : L)) * ((y.toMul : L) * (d : L)) := by ring
        _ = (a : L) * (c : L) := by rw [hx, hy]
    show ordZ A (x + y).toMul = ordZ A x.toMul + ordZ A y.toMul
    rw [ordZ_spec A (mul_ne_zero ha hc) (mul_ne_zero hb hd) hxy,
      ordZ_spec A ha hb hx, ordZ_spec A hc hd hy, ordA_mul A ha hc, ordA_mul A hb hd]
    push_cast
    ring

private theorem ord_spec {x : Lˣ} {a b : A} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : (x : L) * (b : L) = (a : L)) {na nb : ℕ}
    (hna : span {a} = maximalIdeal A ^ na) (hnb : span {b} = maximalIdeal A ^ nb) :
    ord A (.ofMul x) = (na : ℤ) - nb := by
  have := ordZ_spec A ha hb hx
  rw [ordA_unique A ha hna, ordA_unique A hb hnb] at this
  exact this

private theorem ord_ofMul_of_mem {x : Lˣ} (hx : (x : L) ∈ A) {n : ℕ}
    (hspan : span {(⟨(x : L), hx⟩ : A)} = maximalIdeal A ^ n) :
    ord A (.ofMul x) = n := by
  have h := ord_spec A (coe_mk_ne_zero A x hx rfl) one_ne_zero
    (b := 1) (by push_cast; exact mul_one _) hspan
    (by rw [span_singleton_eq_top.mpr isUnit_one, pow_zero, one_eq_top])
  simpa using h

private theorem ord_ofMul_mk0_of_irreducible {ϖ : A} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : A) : L) ≠ 0) :
    ord A (.ofMul (Units.mk0 ((ϖ : A) : L) h0)) = 1 := by
  refine ord_ofMul_of_mem A (x := Units.mk0 ((ϖ : A) : L) h0) (ϖ : A).2 ?_
  have hmk : (⟨((Units.mk0 ((ϖ : A) : L) h0 : Lˣ) : L), (ϖ : A).2⟩ : A) = ϖ :=
    Subtype.ext rfl
  rw [hmk, pow_one, ← hϖ.maximalIdeal_eq]

private theorem ord_eq_zero_iff (x : Lˣ) :
    ord A (.ofMul x) = 0 ↔ x ∈ (Units.map (A.subtype.toMonoidHom)).range := by
  constructor
  · intro h
    obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x
    have hspec : ordZ A x = (ordA A a : ℤ) - ordA A b := ordZ_spec A ha hb hx
    have h0 : ordZ A x = 0 := h
    have hord : ordA A a = ordA A b := by omega
    have hassoc : Associated a b := span_singleton_eq_span_singleton.mp
      (by rw [ordA_span A ha, ordA_span A hb, hord])
    obtain ⟨u, hu⟩ := hassoc
    have haL : (a : L) ≠ 0 := fun hz => ha (Subtype.ext hz)
    have hab : (a : L) * (((u : Aˣ) : A) : L) = (b : L) := by
      exact_mod_cast congrArg (fun s : A => (s : L)) hu
    have h1 : (x : L) * (((u : Aˣ) : A) : L) = 1 := by
      have h2 : (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) = (a : L) := by
        rw [hab]; exact hx
      have h3 : ((x : L) * (((u : Aˣ) : A) : L)) * (a : L) = 1 * (a : L) := by
        rw [one_mul]
        calc ((x : L) * (((u : Aˣ) : A) : L)) * (a : L)
            = (x : L) * ((a : L) * (((u : Aˣ) : A) : L)) := by ring
          _ = (a : L) := h2
      exact mul_right_cancel₀ haL h3
    have huL : (((u : Aˣ) : A) : L) * (((u⁻¹ : Aˣ) : A) : L) = 1 := by
      exact_mod_cast congrArg (fun s : A => (s : L)) u.mul_inv
    have hxinv : (x : L) = ((((u : Aˣ) : A) : L))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have huinv : (((u⁻¹ : Aˣ) : A) : L) = ((((u : Aˣ) : A) : L))⁻¹ :=
      eq_inv_of_mul_eq_one_right huL
    refine ⟨u⁻¹, Units.ext ?_⟩
    show (((u⁻¹ : Aˣ) : A) : L) = (x : L)
    rw [huinv, hxinv]
  · rintro ⟨u, rfl⟩
    have hmem : ((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L) ∈ A := by
      show ((A.subtype) ((u : Aˣ) : A) : L) ∈ A
      exact ((u : Aˣ) : A).2
    have hspan : span {(⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A)}
        = maximalIdeal A ^ 0 := by
      rw [show (⟨((Units.map (A.subtype.toMonoidHom) u : Lˣ) : L), hmem⟩ : A) = ((u : Aˣ) : A)
        from Subtype.ext rfl]
      rw [span_singleton_eq_top.mpr u.isUnit, pow_zero, one_eq_top]
    have := ord_ofMul_of_mem A hmem hspan
    simpa using this

end ValuationOrd

end M4aLocalCFT

end Fold_ValuationOrd

section Fold_LocalHaarModulus

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open scoped NNReal ENNReal Pointwise

namespace M4aLocalCFT

namespace LocalHaarModulus

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

section CosetStep

variable {F v}

private theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (Y : v.adicCompletionIntegers F) :
    ∃ z : v.adicCompletionIntegers F,
      Y = Quotient.out (residue (v.adicCompletionIntegers F) Y) + ϖ * z := by
  have hout : residue (v.adicCompletionIntegers F)
      (Quotient.out (residue (v.adicCompletionIntegers F) Y))
      = residue (v.adicCompletionIntegers F) Y := Quotient.out_eq _
  have hzero : residue (v.adicCompletionIntegers F)
      (Y - Quotient.out (residue (v.adicCompletionIntegers F) Y)) = 0 := by
    rw [map_sub, hout, sub_self]
  set w : v.adicCompletionIntegers F
      := Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) with hw
  have hmem : w ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hsub : Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) = ϖ * z := by
    rw [← hw]; exact hz
  exact sub_eq_iff_eq_add'.mp hsub

private theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

private abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

private theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers F)
    refine mem_iUnion.mpr ⟨residue (v.adicCompletionIntegers F) ⟨y, hy⟩, ?_⟩
    refine ⟨(z : v.adicCompletion F), z.2, ?_⟩
    have hco := congrArg
      (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := hk
    obtain ⟨X, hXy⟩ : ∃ X : v.adicCompletionIntegers F, (X : v.adicCompletion F) = y :=
      ⟨Quotient.out k + ϖ * ⟨z, hz⟩, by push_cast; exact hzy⟩
    rw [← hXy]
    exact X.2

private theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint fun k : ResidueField (v.adicCompletionIntegers F) =>
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hKeq : ((Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F) :
      v.adicCompletion F)
      = ((Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :
          v.adicCompletion F) := by
    push_cast
    rw [show ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z = y from hzy,
        show ((Quotient.out k' : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z' = y from hzy']
  have hAeq : (Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F)
      = (Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :=
    Subtype.coe_injective hKeq
  have := congrArg (residue (v.adicCompletionIntegers F)) hAeq
  rwa [residue_out_add_mul hϖ, residue_out_add_mul hϖ] at this

private theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
    (k : ResidueField (v.adicCompletionIntegers F)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
          (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

end CosetStep

section Measure

variable {F v}

private theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  have hTopen : IsOpen (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (NumberField.isOpenAdicCompletionIntegers F v).smul₀ hϖ0
  have hTmeas := hTopen.measurableSet
  have hbridge : ∀ k : ResidueField (v.adicCompletionIntegers F),
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun k => cosetMap_image_eq k
  calc μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = μ (⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        rw [← integers_eq_iUnion_image hϖ]
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine measure_iUnion ?_ fun k => ?_
        · intro k k' hkk'
          exact pairwise_disjoint_image hϖ hkk'
        · rw [hbridge k]
          exact hTmeas.const_vadd _
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := by
        exact tsum_congr fun k => by rw [hbridge k]
    _ = ∑' _ : ResidueField (v.adicCompletionIntegers F),
          μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine tsum_congr fun k => ?_
        exact measure_vadd _ _ _
    _ = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]

end Measure

section MainTheorem

variable {F v}

private theorem distribHaarChar_eq_one_of_mem_range (x : (v.adicCompletion F)ˣ)
    (hx : x ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range) :
    distribHaarChar (v.adicCompletion F) x = 1 := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  obtain ⟨u, rfl⟩ := hx
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨μ⟩ : Nonempty {μ : Measure (v.adicCompletion F) // μ.IsAddHaarMeasure ∧ μ.Regular} :=
    ⟨⟨(MeasureTheory.Measure.addHaarMeasure
        ⟨⟨S, hK⟩, by
          rw [interior_eq_iff_isOpen.mpr hO]
          exact ⟨0, Subring.zero_mem _⟩⟩),
      inferInstance, inferInstance⟩⟩
  obtain ⟨μ, hHaar, hReg⟩ := μ
  haveI := hHaar; haveI := hReg
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S)
    (hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩) (hK.measure_lt_top.ne) ?_
  have hset : ((Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)) u : _) • S = S := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact mul_mem ((u : v.adicCompletionIntegers F).2) hz
    · intro hy
      set w : v.adicCompletionIntegers F := ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
        v.adicCompletionIntegers F) with hw
      refine ⟨(w : v.adicCompletion F) * y, mul_mem w.2 hy, ?_⟩
      have hcancel : ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * (w : v.adicCompletion F) = 1 := by
        have : ((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F)
            = (1 : v.adicCompletionIntegers F) := by
          rw [hw]
          exact_mod_cast u.mul_inv
        calc ((u : v.adicCompletionIntegers F) : v.adicCompletion F) * (w : v.adicCompletion F)
            = (((u : v.adicCompletionIntegers F) * w : v.adicCompletionIntegers F) :
                v.adicCompletion F) := by rw [Subring.coe_mul]
          _ = 1 := by rw [this]; rfl
      show ((u : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((w : v.adicCompletion F) * y) = y
      rw [← mul_assoc, hcancel, one_mul]
  rw [hset, ENNReal.coe_one, one_mul]

private theorem distribHaarChar_mk0_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0) :
    distribHaarChar (v.adicCompletion F) (Units.mk0 _ h0)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ := by
  letI : MeasurableSpace (v.adicCompletion F) := borel _
  haveI : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
  set S := (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hS
  have hK : IsCompact S := NumberField.isCompactAdicCompletionIntegers F v
  have hO : IsOpen S := NumberField.isOpenAdicCompletionIntegers F v
  set μ : Measure (v.adicCompletion F) := MeasureTheory.Measure.addHaarMeasure
    ⟨⟨S, hK⟩, by
      rw [interior_eq_iff_isOpen.mpr hO]
      exact ⟨0, Subring.zero_mem _⟩⟩ with hμ
  have hq0 : (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos
  have hS0 : μ S ≠ 0 := hO.measure_ne_zero μ ⟨0, Subring.zero_mem _⟩
  have hSfin : μ S ≠ ⊤ := hK.measure_lt_top.ne
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := S) hS0 hSfin ?_
  have hcount := measure_integers_eq_card_mul μ hϖ
  show μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) • S)
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ * μ S
  rw [ENNReal.coe_inv (by exact_mod_cast Nat.pos_iff_ne_zero.mp Nat.card_pos), ENNReal.coe_natCast]
  rw [hcount]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 (ENNReal.natCast_ne_top _), one_mul]

private theorem distribHaarChar_adicCompletion (x : (v.adicCompletion F)ˣ) :
    distribHaarChar (v.adicCompletion F) x
      = ((Ideal.absNorm v.asIdeal : ℝ≥0))
          ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have h0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  set w : (v.adicCompletion F)ˣ := Units.mk0 _ h0 with hw
  set k : ℤ := ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) with hk
  set y : (v.adicCompletion F)ˣ := x * w ^ (-k) with hy
  have hordw : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 1 :=
    ValuationOrd.ord_ofMul_mk0_of_irreducible (v.adicCompletionIntegers F) hϖ h0
  have hordy : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul y) = 0 := by
    have hmul : Additive.ofMul y = Additive.ofMul x + (-k) • Additive.ofMul w := rfl
    rw [hmul, map_add, map_zsmul, hordw, smul_eq_mul, mul_one, ← hk, add_neg_cancel]
  have hyunit : distribHaarChar (v.adicCompletion F) y = 1 :=
    distribHaarChar_eq_one_of_mem_range y
      ((ValuationOrd.ord_eq_zero_iff (v.adicCompletionIntegers F) y).mp hordy)
  have hxy : x = y * w ^ k := by
    rw [hy, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hqw : distribHaarChar (v.adicCompletion F) w
      = ((Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0))⁻¹ :=
    distribHaarChar_mk0_irreducible hϖ h0
  rw [hxy, map_mul, map_zpow, hyunit, one_mul, hqw, inv_zpow, ← zpow_neg,
    card_residueField_eq_absNorm]

private theorem measure_smul_integers [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] [μ.Regular] (x : (v.adicCompletion F)ˣ) :
    μ ((x : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (((Ideal.absNorm v.asIdeal : ℝ≥0))
          ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) : ℝ≥0)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [← distribHaarChar_adicCompletion, distribHaarChar_mul]
  rfl

end MainTheorem

end

end LocalHaarModulus

end M4aLocalCFT

end Fold_LocalHaarModulus

section Fold_LocalZetaUnramified

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private abbrev normQ (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 := (Ideal.absNorm v.asIdeal : ℝ≥0)

private theorem modulus_coe_units_adicCompletion (u : (v.adicCompletion F)ˣ) :
    modulus (u : v.adicCompletion F) = normQ v ^ (-(ValuationOrd.ord (v.adicCompletionIntegers F)
      (Additive.ofMul u))) := by
  rw [modulus_coe_units]
  exact LocalHaarModulus.distribHaarChar_adicCompletion u

section Shells

variable {ϖ : v.adicCompletionIntegers F}

private theorem coe_ne_zero_of_irreducible (hϖ : Irreducible ϖ) :
    ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
  fun h => hϖ.ne_zero (Subtype.ext h)

private def piUnit (hϖ : Irreducible ϖ) : (v.adicCompletion F)ˣ := Units.mk0 _ (coe_ne_zero_of_irreducible hϖ)

@[scoped simp] private theorem piUnit_val (hϖ : Irreducible ϖ) :
    ((piUnit hϖ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) := rfl

private theorem ord_piUnit (hϖ : Irreducible ϖ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ)) = 1 :=
  ValuationOrd.ord_ofMul_mk0_of_irreducible _ hϖ _

end Shells

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Measures

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

end Integrand

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

end Zeta

end LocalZetaUnramified
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end Fold_LocalZetaUnramified
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Fold_MulHaarFromAdditive

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open LanglandsTunnell.TateLocal

open scoped NNReal ENNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace MulHaarFromAdditive

open LocalZetaUnramified

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

variable {ϖ : v.adicCompletionIntegers F}

private theorem ord_ofMul_mul (u w : (v.adicCompletion F)ˣ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (u * w))
      = ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u)
        + ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul w) := by
  have h : Additive.ofMul (u * w) = Additive.ofMul u + Additive.ofMul w := rfl
  rw [h, map_add]

private theorem ord_ofMul_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (piUnit hϖ ^ k)) = k := by
  have h : Additive.ofMul (piUnit hϖ ^ k) = k • Additive.ofMul (piUnit hϖ) := rfl
  rw [h, map_zsmul, ord_piUnit hϖ, smul_eq_mul, mul_one]

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

variable [MeasurableSpace ((v.adicCompletion F)ˣ)] [BorelSpace ((v.adicCompletion F)ˣ)]

end MulHaarFromAdditive
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end Fold_MulHaarFromAdditive
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Fold_TateSDecomp2

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel IsDedekindDomain"

open scoped NNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

private def unitAtHom (w : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* (w.adicCompletion F)ˣ :=
  Units.map (((finAdeleEval (𝓞 F) F w).comp (adeleFin (𝓞 F) F)).toMonoidHom)

private def embUnit (v : HeightOneSpectrum (𝓞 F)) : (v.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (Units.map (finIncl (𝓞 F) F)).comp (localUnit (𝓞 F) F v)

private theorem embUnit_val_fst (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl

private theorem unitAtHom_embUnit_self (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    unitAtHom v (embUnit v t) = t :=
  Units.ext (localUnit_apply_self (𝓞 F) F v t)

private theorem unitAtHom_embUnit_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (t : (v.adicCompletion F)ˣ) :
    unitAtHom w (embUnit v t) = 1 :=
  Units.ext (localUnit_apply_of_ne (𝓞 F) F v t hw)

private def ordAt (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ℤ :=
  M4aLocalCFT.ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul t)

private theorem ordAt_mul (v : HeightOneSpectrum (𝓞 F)) (s t : (v.adicCompletion F)ˣ) :
    ordAt v (s * t) = ordAt v s + ordAt v t := by
  simp [ordAt, ofMul_mul, map_add]

private theorem ordAt_inv (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) : ordAt v t⁻¹ = -ordAt v t := by
  simp [ordAt, ofMul_inv, map_neg]

private theorem ordAt_zpow (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) (n : ℤ) :
    ordAt v (t ^ n) = n * ordAt v t := by
  simp [ordAt, ofMul_zpow, map_zsmul]

private theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    ordAt v t = 0 ↔ (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  rw [ordAt, M4aLocalCFT.ValuationOrd.ord_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu]
    exact ⟨(u : v.adicCompletionIntegers F).2, ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨⟨_, h⟩, ⟨_, h'⟩, Subtype.ext t.mul_inv, Subtype.ext t.inv_mul⟩, Units.ext rfl⟩

private structure Uniformizers (F : Type) [Field F] [NumberField F] where
  ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ
  ordAt_eq_one : ∀ v, ordAt v (ϖ v) = 1

private def archUnits : (AdeleRing (𝓞 F) F)ˣ →* (InfiniteAdeleRing F)ˣ := Units.map (adeleArch (𝓞 F) F).toMonoidHom

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end Fold_TateSDecomp2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Fold_LocalGlobalModulus

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

section LG

variable (v : HeightOneSpectrum (𝓞 F))

private def coordAt (x : AdeleRing (𝓞 F) F) : v.adicCompletion F := (x.2 : FiniteAdeleRing (𝓞 F) F) v

private theorem continuous_coordAt : Continuous (coordAt (F := F) v) :=
  (continuous_finAdeleEval (𝓞 F) F v).comp (continuous_adeleFin (𝓞 F) F)

open scoped Classical in
private def finSingle (c : v.adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  ⟨Function.update 0 v c,
    Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset fun w hw => by
      by_contra hwv
      exact hw (by rw [Function.update_of_ne hwv]; exact zero_mem _))⟩

open scoped Classical in
private theorem finSingle_apply_self (c : v.adicCompletion F) : (finSingle v c : FiniteAdeleRing (𝓞 F) F) v = c := by
  show Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v c v = c
  simp

open scoped Classical in
private theorem finSingle_apply_of_ne (c : v.adicCompletion F) {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (finSingle v c : FiniteAdeleRing (𝓞 F) F) w = 0 := by
  show Function.update (0 : ∀ w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v c w = 0
  simp [Function.update_of_ne hw]

private def adeleSingle (c : v.adicCompletion F) : AdeleRing (𝓞 F) F := ((0 : InfiniteAdeleRing F), finSingle v c)

private theorem coordAt_adeleSingle_add (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F) :
    coordAt v (adeleSingle v c + x) = c + coordAt v x := by
  show (finSingle v c : FiniteAdeleRing (𝓞 F) F) v + (x.2 : FiniteAdeleRing (𝓞 F) F) v = c + _
  rw [finSingle_apply_self]
  rfl

private theorem adeleSingle_add_fst (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F) :
    (adeleSingle v c + x).1 = x.1 := by
  show (0 : InfiniteAdeleRing F) + x.1 = x.1
  rw [zero_add]

private theorem adeleSingle_add_snd_apply_of_ne (c : v.adicCompletion F) (x : AdeleRing (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    ((adeleSingle v c + x).2 : FiniteAdeleRing (𝓞 F) F) w = (x.2 : FiniteAdeleRing (𝓞 F) F) w := by
  show (finSingle v c : FiniteAdeleRing (𝓞 F) F) w + (x.2 : FiniteAdeleRing (𝓞 F) F) w = _
  rw [finSingle_apply_of_ne v c hw, zero_add]

private def slab (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

private def box (B : Set (InfiniteAdeleRing F)) : Set (AdeleRing (𝓞 F) F) :=
  {x | x.1 ∈ B ∧ ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}

private theorem preimage_adeleSingle_add_slab (B : Set (InfiniteAdeleRing F)) (c : v.adicCompletion F) :
    (fun x => adeleSingle v c + x) ⁻¹' slab v B = slab v B := by
  ext x
  simp only [Set.mem_preimage, slab, Set.mem_setOf_eq, adeleSingle_add_fst]
  refine and_congr Iff.rfl (forall₂_congr fun w hw => ?_)
  rw [adeleSingle_add_snd_apply_of_ne v c x hw]

private theorem preimage_adeleSingle_add_coordAt (c : v.adicCompletion F) (E : Set (v.adicCompletion F)) :
    (fun x => adeleSingle v c + x) ⁻¹' (coordAt v ⁻¹' E) = coordAt v ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, coordAt_adeleSingle_add]

private theorem coordAt_preimage_integers_inter_slab (B : Set (InfiniteAdeleRing F)) :
    coordAt v ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ∩ slab v B = box B := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_preimage, slab, box, Set.mem_setOf_eq, coordAt]
  constructor
  · rintro ⟨hv, hB, hw⟩
    refine ⟨hB, fun w => ?_⟩
    by_cases h : w = v
    · subst h; exact hv
    · exact hw w h
  · rintro ⟨hB, hw⟩
    exact ⟨hw v, hB, fun w _ => hw w⟩

private theorem isCompact_box {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) : IsCompact (box (F := F) B) := by
  have h := hB.prod (isCompact_integralFiniteAdeles (𝓞 F) F)
  exact h

private theorem isOpen_openBox (B : Set (InfiniteAdeleRing F)) :
    IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
      ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B} :=
    isOpen_interior.preimage (continuous_adeleArch (𝓞 F) F)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

private theorem isOpen_openSlab (B : Set (InfiniteAdeleRing F)) :
    IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B} :=
    isOpen_interior.preimage (continuous_adeleArch (𝓞 F) F)
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
      (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F} := by
    have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (A := fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      Fact.out (p := fun w => w ≠ v)
    exact h.preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

private def slabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : Set (InfiniteAdeleRing F)) : Measure (v.adicCompletion F) :=
  Measure.map (coordAt v) (μ.restrict (slab v B))

private theorem slabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : Set (InfiniteAdeleRing F))
    {E : Set (v.adicCompletion F)} (hE : MeasurableSet E) :
    slabPush v μ B E = μ (coordAt v ⁻¹' E ∩ slab v B) := by
  rw [slabPush, Measure.map_apply (continuous_coordAt v).measurable hE,
    Measure.restrict_apply ((continuous_coordAt v).measurable hE)]

private theorem isAddLeftInvariant_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : Set (InfiniteAdeleRing F)) : (slabPush v μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [slabPush_apply v μ B hE, slabPush_apply v μ B (measurable_const_add c hE),
    ← preimage_adeleSingle_add_coordAt v c E]
  conv_lhs => rw [← preimage_adeleSingle_add_slab v B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (adeleSingle v c) _

private theorem slabPush_integers_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) :
    slabPush v μ B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ := by
  rw [slabPush_apply v μ B (isClosed_adicCompletionIntegers v).measurableSet,
    coordAt_preimage_integers_inter_slab]
  exact (isCompact_box hB).measure_lt_top

private theorem isFiniteMeasureOnCompacts_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : Set (InfiniteAdeleRing F)} (hB : IsCompact B) :
    IsFiniteMeasureOnCompacts (slabPush v μ B) := by
  haveI := isAddLeftInvariant_slabPush v μ B
  refine ⟨fun K hK => ?_⟩
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := NumberField.isOpenAdicCompletionIntegers F v
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : v.adicCompletion F => c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun c => hO.vadd c)
    (fun c hc => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨0, zero_mem _, by simp⟩⟩)
  calc slabPush v μ B K
      ≤ slabPush v μ B (⋃ c ∈ t, c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := measure_mono ht
    _ ≤ ∑ c ∈ t, slabPush v μ B (c +ᵥ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
        measure_biUnion_finset_le t _
    _ = ∑ _c ∈ t, slabPush v μ B (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ c _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (slabPush_integers_lt_top v μ hB)

private theorem isOpenPosMeasure_slabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : Set (InfiniteAdeleRing F)} (hB : (interior B).Nonempty) : IsOpenPosMeasure (slabPush v μ B) := by
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  obtain ⟨b, hb⟩ := hB
  rw [slabPush_apply v μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U ⊆ coordAt v ⁻¹' U ∩ slab v B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, interior_subset h1, h2⟩
  have hopen : IsOpen ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U) :=
    (isOpen_openSlab v B).inter (hU.preimage (continuous_coordAt v))
  have hne' : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior B ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
      ∩ coordAt v ⁻¹' U).Nonempty := by
    refine ⟨((b, finSingle v c) : AdeleRing (𝓞 F) F), ⟨hb, fun w hw => ?_⟩, ?_⟩
    · show (finSingle v c : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F
      rw [finSingle_apply_of_ne v c hw]
      exact zero_mem _
    · show (finSingle v c : FiniteAdeleRing (𝓞 F) F) v ∈ U
      rw [finSingle_apply_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

private theorem embUnit_val_mul_fst (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 = x.1 := by
  show ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 * x.1 = x.1
  rw [embUnit_val_fst, one_mul]

private theorem embUnit_val_mul_snd_apply_self (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) v
      = (t : v.adicCompletion F) * (x.2 : FiniteAdeleRing (𝓞 F) F) v := by
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v
      * (x.2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [localUnit_apply_self]

private theorem embUnit_val_mul_snd_apply_of_ne (t : (v.adicCompletion F)ˣ) (x : AdeleRing (𝓞 F) F)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) w
      = (x.2 : FiniteAdeleRing (𝓞 F) F) w := by
  show ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w
      * (x.2 : FiniteAdeleRing (𝓞 F) F) w = _
  rw [localUnit_apply_of_ne (𝓞 F) F v t hw, one_mul]

private theorem embUnit_smul_box (t : (v.adicCompletion F)ˣ) (B : Set (InfiniteAdeleRing F)) :
    (embUnit v t) • box (F := F) B
      = coordAt v ⁻¹' ((t : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∩ slab v B := by
  ext y
  constructor
  · rintro ⟨x, ⟨hxB, hxint⟩, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · show (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) v
        ∈ (t : v.adicCompletion F) • (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      rw [embUnit_val_mul_snd_apply_self]
      exact Set.smul_mem_smul_set (hxint v)
    · show (((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 ∈ B
      rw [embUnit_val_mul_fst]; exact hxB
    · show (((((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 : FiniteAdeleRing (𝓞 F) F)) w
        ∈ w.adicCompletionIntegers F
      rw [embUnit_val_mul_snd_apply_of_ne v t x hw]; exact hxint w
  · rintro ⟨hv, hB, hw⟩
    obtain ⟨z, hz, hvz⟩ := Set.mem_smul_set.mp hv
    refine ⟨(embUnit v t⁻¹) • y, ⟨?_, fun w => ?_⟩, ?_⟩
    · show (((embUnit v t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 ∈ B
      rw [embUnit_val_mul_fst]; exact hB
    · by_cases hwv : w = v
      · subst hwv
        show (((((embUnit w t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 : FiniteAdeleRing (𝓞 F) F)) w
          ∈ w.adicCompletionIntegers F
        rw [embUnit_val_mul_snd_apply_self]
        have hyv : (y.2 : FiniteAdeleRing (𝓞 F) F) w = (t : w.adicCompletion F) * z := by
          show coordAt w y = (t : w.adicCompletion F) * z
          rw [← hvz]; rfl
        rw [hyv, ← mul_assoc, Units.inv_mul, one_mul]
        exact hz
      · show (((((embUnit v t⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 : FiniteAdeleRing (𝓞 F) F)) w
          ∈ w.adicCompletionIntegers F
        rw [embUnit_val_mul_snd_apply_of_ne v t⁻¹ y hwv]; exact hw w hwv
    · show (embUnit v t) • ((embUnit v t⁻¹) • y) = y
      rw [map_inv, smul_inv_smul]

private theorem distribHaarChar_embUnit (t : (v.adicCompletion F)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (embUnit v t)
      = ((Ideal.absNorm v.asIdeal : ℝ≥0)) ^ (-(ordAt v t)) := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (v.adicCompletion F)
  obtain ⟨B⟩ : Nonempty (PositiveCompacts (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  have hBc : IsCompact (B : Set (InfiniteAdeleRing F)) := B.isCompact
  have hBi : (interior (B : Set (InfiniteAdeleRing F))).Nonempty := B.interior_nonempty
  have hs_top : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ ∞ := (isCompact_box hBc).measure_lt_top.ne
  have hs0 : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ 0 := by
    obtain ⟨b, hb⟩ := hBi
    have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
        ⊆ box (F := F) (B : Set (InfiniteAdeleRing F)) := fun x hx => ⟨interior_subset hx.1, hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), hb, fun w => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openBox (F := F) _).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_slabPush v μ (B : Set (InfiniteAdeleRing F))
  haveI := isFiniteMeasureOnCompacts_slabPush v μ hBc
  haveI := isOpenPosMeasure_slabPush v μ hBi
  haveI : (slabPush v μ (B : Set (InfiniteAdeleRing F))).IsAddHaarMeasure := {}
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := NumberField.isOpenAdicCompletionIntegers F v
  haveI : (slabPush v μ (B : Set (InfiniteAdeleRing F))).Regular :=
    Measure.regular_of_isAddLeftInvariant (NumberField.isCompactAdicCompletionIntegers F v)
      (by rw [hO.interior_eq]; exact ⟨0, zero_mem _⟩) (slabPush_integers_lt_top v μ hBc).ne
  have hlam := M4aLocalCFT.LocalHaarModulus.measure_smul_integers (slabPush v μ (B : Set (InfiniteAdeleRing F))) t
  rw [slabPush_apply v μ _ ((hO.smul₀ t.ne_zero).measurableSet),
    slabPush_apply v μ _ (isClosed_adicCompletionIntegers v).measurableSet,
    coordAt_preimage_integers_inter_slab] at hlam
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [embUnit_smul_box]
  exact hlam

private theorem distribHaarChar_embUnit_eq_local (t : (v.adicCompletion F)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (embUnit v t) = distribHaarChar (v.adicCompletion F) t := by
  rw [distribHaarChar_embUnit, M4aLocalCFT.LocalHaarModulus.distribHaarChar_adicCompletion]
  rfl

private theorem distribHaarChar_eq_one_of_integral {g : (AdeleRing (𝓞 F) F)ˣ} (h1 : ((g : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1)
    (hint : ∀ w : HeightOneSpectrum (𝓞 F), ((g : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F)
    (hint' : ∀ w : HeightOneSpectrum (𝓞 F), (((g⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w
      ∈ w.adicCompletionIntegers F) :
    distribHaarChar (AdeleRing (𝓞 F) F) g = 1 := by
  borelize (AdeleRing (𝓞 F) F)
  obtain ⟨B⟩ : Nonempty (PositiveCompacts (InfiniteAdeleRing F)) := inferInstance
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  have hBc : IsCompact (B : Set (InfiniteAdeleRing F)) := B.isCompact
  have hs_top : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ ∞ := (isCompact_box hBc).measure_lt_top.ne
  have hs0 : μ (box (F := F) (B : Set (InfiniteAdeleRing F))) ≠ 0 := by
    obtain ⟨b, hb⟩ := B.interior_nonempty
    have hsub : {x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}
        ⊆ box (F := F) (B : Set (InfiniteAdeleRing F)) := fun x hx => ⟨interior_subset hx.1, hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | x.1 ∈ interior (B : Set (InfiniteAdeleRing F)) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), hb, fun w => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openBox (F := F) _).measure_pos μ hne) (measure_mono hsub))
  have h1' : (((g⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).1 = 1 := inv_val_fst_eq_one g h1
  have hfix : ∀ (k : (AdeleRing (𝓞 F) F)ˣ), ((k : AdeleRing (𝓞 F) F).1 = 1) →
      (∀ w : HeightOneSpectrum (𝓞 F), ((k : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w ∈ w.adicCompletionIntegers F) →
      ∀ x ∈ box (F := F) (B : Set (InfiniteAdeleRing F)), k • x ∈ box (F := F) (B : Set (InfiniteAdeleRing F)) := by
    intro k hk1 hkint x hx
    refine ⟨?_, fun w => ?_⟩
    · show ((k : AdeleRing (𝓞 F) F).1 * x.1) ∈ (B : Set (InfiniteAdeleRing F))
      rw [hk1, one_mul]; exact hx.1
    · show ((k : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) w * (x.2 : FiniteAdeleRing (𝓞 F) F) w ∈ _
      exact mul_mem (hkint w) (hx.2 w)
  have hset : g • box (F := F) (B : Set (InfiniteAdeleRing F)) = box (F := F) (B : Set (InfiniteAdeleRing F)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hfix g h1 hint x hx
    · intro hy
      exact ⟨g⁻¹ • y, hfix g⁻¹ h1' hint' y hy, smul_inv_smul g y⟩
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [hset, ENNReal.coe_one, one_mul]

end LG
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end Fold_LocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Fold_ShellBound

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT

namespace ShellBound

variable {F : Type} [Field F] [NumberField F]

private theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := TateGlobal.absNorm_ne_zero v
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    intro h
    exact v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

private def baseFam (F : Type) [Field F] [NumberField F] (σ : ℝ) :
    HeightOneSpectrum (𝓞 F) → ℂ :=
  fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) : ℝ) : ℂ)

private theorem norm_baseFam (σ : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    ‖baseFam F σ v‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-σ) := by
  rw [baseFam, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]

private theorem summable_norm_baseFam {σ : ℝ} (hσ : 1 < σ) :
    Summable fun v : HeightOneSpectrum (𝓞 F) => ‖baseFam F σ v‖ := by
  refine (TateGlobal.summable_absNorm_rpow_neg hσ).congr fun v => ?_
  rw [norm_baseFam]

end ShellBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end Fold_ShellBound
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

section Fold_TateAssembly

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel IsDedekindDomain Topology TopologicalSpace Set"

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

private scoped instance instSecondCountableCompletion (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

section Assembly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private abbrev DeepUnits : Type := (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) → (v.1.adicCompletionIntegers F)ˣ

private abbrev SUnits : Type := (v : S) → (v.1.adicCompletion F)ˣ

open scoped Classical in
private def extendUnits : DeepUnits (F := F) S →* ((v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ) where
  toFun o v := if h : v ∈ S then 1 else o ⟨v, h⟩
  map_one' := by
    funext v
    by_cases h : v ∈ S
    · rw [dif_pos h]; rfl
    · rw [dif_neg h]; rfl
  map_mul' o o' := by
    funext v
    by_cases h : v ∈ S
    · rw [Pi.mul_apply, dif_pos h, dif_pos h, dif_pos h, one_mul]
    · rw [Pi.mul_apply, dif_neg h, dif_neg h, dif_neg h]; rfl

open scoped Classical in
private theorem extendUnits_apply_of_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    extendUnits S o v = 1 := by
  show (if h : v ∈ S then (1 : (v.adicCompletionIntegers F)ˣ) else o ⟨v, h⟩) = 1
  rw [dif_pos hv]

open scoped Classical in
private theorem extendUnits_apply_of_not_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    extendUnits S o v = o ⟨v, hv⟩ := by
  show (if h : v ∈ S then (1 : (v.adicCompletionIntegers F)ˣ) else o ⟨v, h⟩) = o ⟨v, hv⟩
  rw [dif_neg hv]

private def structureRingHom : ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun x := RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x
  map_one' := RestrictedProduct.ext _ _ fun _ => rfl
  map_mul' _ _ := RestrictedProduct.ext _ _ fun _ => rfl
  map_zero' := RestrictedProduct.ext _ _ fun _ => rfl
  map_add' _ _ := RestrictedProduct.ext _ _ fun _ => rfl

private def piUnitsInv : ((v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ)
    →* ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F)ˣ :=
  MulEquiv.piUnits.symm.toMonoidHom

private def deepAsm : DeepUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  ((Units.map ((finIncl (𝓞 F) F).comp (structureRingHom (F := F)).toMonoidHom)).comp piUnitsInv).comp (extendUnits S)

private theorem deepAsm_val_fst (o : DeepUnits (F := F) S) : ((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
  rfl

private theorem deepAsm_val_snd_apply (o : DeepUnits (F := F) S) (v : HeightOneSpectrum (𝓞 F)) :
    (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((extendUnits S o v : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :=
  rfl

private theorem unitAtHom_deepAsm_of_not_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (deepAsm S o) = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (o ⟨v, hv⟩) := by
  ext
  show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [deepAsm_val_snd_apply, extendUnits_apply_of_not_mem S o hv]
  rfl

private theorem unitAtHom_deepAsm_of_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (deepAsm S o) = 1 := by
  ext
  show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [deepAsm_val_snd_apply, extendUnits_apply_of_mem S o hv]
  rfl

end Assembly
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_TateAssembly
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_ArchLocalGlobalModulus

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel NumberField.AdelicVolume IsDedekindDomain MeasureTheory MeasureTheory.Measure Set Filter TopologicalSpace"

open scoped NNReal ENNReal Pointwise Topology

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

section LGArch

variable (w : InfinitePlace F)

private def archCoord (x : AdeleRing (𝓞 F) F) : w.Completion := x.1 w

private theorem continuous_archCoord : Continuous (archCoord (F := F) w) := by
  show Continuous fun x : AdeleRing (𝓞 F) F => (fun y : InfiniteAdeleRing F => y w) (adeleArch (𝓞 F) F x)
  exact (continuous_apply w).comp (continuous_adeleArch (𝓞 F) F)

open scoped Classical in
private def archSingle (c : w.Completion) : AdeleRing (𝓞 F) F :=
  ((Function.update (0 : InfiniteAdeleRing F) w c), (0 : FiniteAdeleRing (𝓞 F) F))

open scoped Classical in
private theorem archCoord_archSingle_add (c : w.Completion) (x : AdeleRing (𝓞 F) F) :
    archCoord w (archSingle w c + x) = c + archCoord w x := by
  show Function.update (0 : InfiniteAdeleRing F) w c w + x.1 w = c + x.1 w
  rw [Function.update_self]

open scoped Classical in
private theorem archSingle_add_fst_of_ne (c : w.Completion) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) : (archSingle w c + x).1 w' = x.1 w' := by
  show Function.update (0 : InfiniteAdeleRing F) w c w' + x.1 w' = x.1 w'
  rw [Function.update_of_ne hw]
  exact zero_add _

private theorem archSingle_add_snd (c : w.Completion) (x : AdeleRing (𝓞 F) F) : (archSingle w c + x).2 = x.2 := by
  show (0 : FiniteAdeleRing (𝓞 F) F) + x.2 = x.2
  exact zero_add _

private def archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  {x | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ B w') ∧
    ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}

private def archBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) : Set (AdeleRing (𝓞 F) F) :=
  box (F := F) (Set.pi Set.univ B)

private theorem mem_archBox_iff (B : (w' : InfinitePlace F) → Set (w'.Completion)) (x : AdeleRing (𝓞 F) F) :
    x ∈ archBox B ↔ (∀ w' : InfinitePlace F, x.1 w' ∈ B w') ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' => h1 w' (Set.mem_univ _), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun w' _ => h1 w', h2⟩

private theorem preimage_archSingle_add_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) (c : w.Completion) :
    (fun x => archSingle w c + x) ⁻¹' archSlab w B = archSlab w B := by
  ext x
  simp only [Set.mem_preimage, archSlab, Set.mem_setOf_eq, archSingle_add_snd]
  refine and_congr (forall₂_congr fun w' hw => ?_) Iff.rfl
  rw [archSingle_add_fst_of_ne w c x hw]

private theorem preimage_archSingle_add_archCoord (c : w.Completion) (E : Set (w.Completion)) :
    (fun x => archSingle w c + x) ⁻¹' (archCoord w ⁻¹' E) = archCoord w ⁻¹' ((fun y => c + y) ⁻¹' E) := by
  ext x
  simp only [Set.mem_preimage, archCoord_archSingle_add]

private theorem archCoord_preimage_inter_archSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    archCoord w ⁻¹' (B w) ∩ archSlab w B = archBox B := by
  ext x
  rw [mem_archBox_iff]
  simp only [Set.mem_inter_iff, Set.mem_preimage, archSlab, Set.mem_setOf_eq, archCoord]
  constructor
  · rintro ⟨hw, hB, hv⟩
    refine ⟨fun w' => ?_, hv⟩
    by_cases h : w' = w
    · subst h; exact hw
    · exact hB w' h
  · rintro ⟨hB, hv⟩
    exact ⟨hB w, fun w' _ => hB w', hv⟩

private theorem isCompact_archBox {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    IsCompact (archBox (F := F) B) :=
  isCompact_box (isCompact_univ_pi hB)

private theorem isOpen_openArchSlab (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, ⋂ (_ : w' ≠ w), archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_iInter_of_finite fun _ =>
      isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

private theorem isOpen_openArchBox (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    IsOpen {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} := by
  have h1 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')} := by
    have : {x : AdeleRing (𝓞 F) F | ∀ w' : InfinitePlace F, x.1 w' ∈ interior (B w')}
        = ⋂ w' : InfinitePlace F, archCoord w' ⁻¹' interior (B w') := by
      ext x; simp [archCoord]
    rw [this]
    exact isOpen_iInter_of_finite fun w' => isOpen_interior.preimage (continuous_archCoord w')
  have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F} :=
    (isOpen_integralFiniteAdeles (𝓞 F) F).preimage (continuous_adeleFin (𝓞 F) F)
  exact h1.inter h2

section Measure

variable [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
  [MeasurableSpace (w.Completion)] [BorelSpace (w.Completion)]

private def archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    Measure (w.Completion) :=
  Measure.map (archCoord w) (μ.restrict (archSlab w B))

private theorem archSlabPush_apply (μ : Measure (AdeleRing (𝓞 F) F)) (B : (w' : InfinitePlace F) → Set (w'.Completion))
    {E : Set (w.Completion)} (hE : MeasurableSet E) :
    archSlabPush w μ B E = μ (archCoord w ⁻¹' E ∩ archSlab w B) := by
  rw [archSlabPush, Measure.map_apply (continuous_archCoord w).measurable hE,
    Measure.restrict_apply ((continuous_archCoord w).measurable hE)]

private theorem isAddLeftInvariant_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddLeftInvariant]
    (B : (w' : InfinitePlace F) → Set (w'.Completion)) : (archSlabPush w μ B).IsAddLeftInvariant := by
  refine (forall_measure_preimage_add_iff _).mp fun c E hE => ?_
  rw [archSlabPush_apply w μ B hE, archSlabPush_apply w μ B (measurable_const_add c hE),
    ← preimage_archSingle_add_archCoord w c E]
  conv_lhs => rw [← preimage_archSingle_add_archSlab w B c]
  rw [← Set.preimage_inter]
  exact measure_preimage_add μ (archSingle w c) _

private theorem archSlabPush_self_lt_top (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w')) :
    archSlabPush w μ B (B w) < ∞ := by
  rw [archSlabPush_apply w μ B (hB w).measurableSet, archCoord_preimage_inter_archSlab]
  exact (isCompact_archBox hB).measure_lt_top

private theorem isFiniteMeasureOnCompacts_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsFiniteMeasureOnCompacts μ]
    [μ.IsAddLeftInvariant] {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hB : ∀ w', IsCompact (B w'))
    (hBi : (interior (B w)).Nonempty) :
    IsFiniteMeasureOnCompacts (archSlabPush w μ B) := by
  haveI := isAddLeftInvariant_archSlabPush w μ B
  obtain ⟨b₀, hb₀⟩ := hBi
  refine ⟨fun K hK => ?_⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover
    (fun c : w.Completion => (c - b₀) +ᵥ interior (B w))
    (fun c => isOpen_interior.vadd (c - b₀))
    (fun c _ => Set.mem_iUnion.mpr ⟨c, Set.mem_vadd_set.mpr ⟨b₀, hb₀, by simp⟩⟩)
  calc archSlabPush w μ B K
      ≤ archSlabPush w μ B (⋃ c ∈ t, (c - b₀) +ᵥ interior (B w)) := measure_mono ht
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ interior (B w)) := measure_biUnion_finset_le t _
    _ ≤ ∑ c ∈ t, archSlabPush w μ B ((c - b₀) +ᵥ B w) :=
        Finset.sum_le_sum fun c _ => measure_mono (Set.vadd_set_mono interior_subset)
    _ = ∑ _c ∈ t, archSlabPush w μ B (B w) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        exact measure_vadd _ (c - b₀) _
    _ < ∞ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (archSlabPush_self_lt_top w μ hB)

private theorem isOpenPosMeasure_archSlabPush (μ : Measure (AdeleRing (𝓞 F) F)) [IsOpenPosMeasure μ]
    {B : (w' : InfinitePlace F) → Set (w'.Completion)} (hBi : ∀ w', (interior (B w')).Nonempty) :
    IsOpenPosMeasure (archSlabPush w μ B) := by
  classical
  refine ⟨fun U hU hne => ?_⟩
  obtain ⟨c, hc⟩ := hne
  choose b hb using hBi
  rw [archSlabPush_apply w μ B hU.measurableSet]
  have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U ⊆ archCoord w ⁻¹' U ∩ archSlab w B := by
    rintro x ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h3, fun w' hw => interior_subset (h1 w' hw), h2⟩
  have hopen := (isOpen_openArchSlab w B).inter (hU.preimage (continuous_archCoord w))
  have hne' : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, w' ≠ w → x.1 w' ∈ interior (B w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
      ∩ archCoord w ⁻¹' U).Nonempty := by
    refine ⟨((Function.update b w c, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F),
      ⟨fun w' hw => ?_, fun v => zero_mem _⟩, ?_⟩
    · show Function.update b w c w' ∈ interior (B w')
      rw [Function.update_of_ne hw]
      exact hb w'
    · show Function.update b w c w ∈ U
      rw [Function.update_self]
      exact hc
  exact ne_of_gt (lt_of_lt_of_le (hopen.measure_pos μ hne') (measure_mono hsub))

end Measure
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

private theorem archCentralUnit_val_mul_fst_self (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w = (a : w.Completion) * x.1 w := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w * x.1 w = _
  rw [archCentralUnit_fst_self]

private theorem archCentralUnit_val_mul_fst_of_ne (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) {w' : InfinitePlace F}
    (hw : w' ≠ w) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' = x.1 w' := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w' * x.1 w' = _
  rw [archCentralUnit_fst_of_ne w a hw, one_mul]

private theorem archCentralUnit_val_mul_snd (a : (w.Completion)ˣ) (x : AdeleRing (𝓞 F) F) :
    (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 = x.2 := by
  show ((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 * x.2 = _
  rw [archCentralUnit_snd, one_mul]

private theorem archCentralUnit_smul_archBox (a : (w.Completion)ˣ) (B : (w' : InfinitePlace F) → Set (w'.Completion)) :
    (archCentralUnit F w a) • archBox (F := F) B = archCoord w ⁻¹' (a • B w) ∩ archSlab w B := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [mem_archBox_iff] at hy
    obtain ⟨hB, hv⟩ := hy
    refine ⟨?_, fun w' hw => ?_, fun v => ?_⟩
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w ∈ a • B w
      rw [archCentralUnit_val_mul_fst_self]
      exact Set.smul_mem_smul_set (hB w)
    · show (((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).1 w' ∈ B w'
      rw [archCentralUnit_val_mul_fst_of_ne w a y hw]
      exact hB w'
    · show ((((archCentralUnit F w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * y).2 :
          FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
      rw [archCentralUnit_val_mul_snd]
      exact hv v
  · rintro ⟨hw, hB, hv⟩
    refine ⟨(archUnitHom w a⁻¹) • x, ?_, ?_⟩
    · rw [mem_archBox_iff]
      refine ⟨fun w' => ?_, fun v => ?_⟩
      · by_cases h : w' = w
        · subst h
          show (((archCentralUnit F w' a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_self]
          obtain ⟨b, hb, hbx⟩ := Set.mem_smul_set.mp hw
          have : x.1 w' = (a : w'.Completion) * b := hbx.symm
          rw [this, ← mul_assoc, Units.inv_mul, one_mul]
          exact hb
        · show (((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).1 w' ∈ B w'
          rw [archCentralUnit_val_mul_fst_of_ne w a⁻¹ x h]
          exact hB w' h
      · show ((((archCentralUnit F w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) * x).2 :
            FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F
        rw [archCentralUnit_val_mul_snd]
        exact hv v
    · show (archUnitHom w a) • ((archUnitHom w a⁻¹) • x) = x
      rw [map_inv, smul_inv_smul]

private theorem distribHaarChar_archCentralUnit (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archCentralUnit F w a) = distribHaarChar (w.Completion) a := by
  borelize (AdeleRing (𝓞 F) F)
  borelize (w.Completion)
  set B : (w' : InfinitePlace F) → PositiveCompacts (w'.Completion) := fun w' => Classical.arbitrary _ with hBdef
  obtain ⟨K₀⟩ : Nonempty (PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀ with hμ
  set Bs : (w' : InfinitePlace F) → Set (w'.Completion) := fun w' => (B w' : Set (w'.Completion)) with hBs
  have hBc : ∀ w', IsCompact (Bs w') := fun w' => (B w').isCompact
  have hBi : ∀ w', (interior (Bs w')).Nonempty := fun w' => (B w').interior_nonempty
  have hs_top : μ (archBox (F := F) Bs) ≠ ∞ := (isCompact_archBox hBc).measure_lt_top.ne
  have hs0 : μ (archBox (F := F) Bs) ≠ 0 := by
    classical
    choose b hb using hBi
    have hsub : {x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}
        ⊆ archBox (F := F) Bs := by
      intro x hx
      rw [mem_archBox_iff]
      exact ⟨fun w' => interior_subset (hx.1 w'), hx.2⟩
    have hne : ({x : AdeleRing (𝓞 F) F | (∀ w' : InfinitePlace F, x.1 w' ∈ interior (Bs w')) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F}).Nonempty :=
      ⟨((b, (0 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F), fun w' => hb w', fun v => zero_mem _⟩
    exact ne_of_gt (lt_of_lt_of_le ((isOpen_openArchBox (F := F) Bs).measure_pos μ hne) (measure_mono hsub))
  haveI := isAddLeftInvariant_archSlabPush w μ Bs
  haveI := isFiniteMeasureOnCompacts_archSlabPush w μ hBc (hBi w)
  haveI := isOpenPosMeasure_archSlabPush w μ hBi
  haveI : (archSlabPush w μ Bs).IsAddHaarMeasure := {}
  haveI : (archSlabPush w μ Bs).Regular :=
    Measure.regular_of_isAddLeftInvariant (hBc w) (hBi w) (archSlabPush_self_lt_top w μ hBc).ne
  have key := distribHaarChar_mul (archSlabPush w μ Bs) a (Bs w)
  rw [archSlabPush_apply w μ Bs ((hBc w).smul (a : (w.Completion)ˣ)).measurableSet,
    archSlabPush_apply w μ Bs (hBc w).measurableSet, archCoord_preimage_inter_archSlab] at key
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) hs0 hs_top ?_
  rw [archCentralUnit_smul_archBox]
  exact key.symm

private theorem distribHaarChar_archUnitHom (a : (w.Completion)ˣ) :
    distribHaarChar (AdeleRing (𝓞 F) F) (archUnitHom w a) = distribHaarChar (w.Completion) a :=
  distribHaarChar_archCentralUnit w a

end LGArch
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_ArchLocalGlobalModulus
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_FujisakiC3

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable (F : Type) [Field F] [NumberField F]

private theorem ideleNorm_archCentralUnit (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (NumberField.AdelicVolume.archCentralUnit F w a) =
      ((distribHaarChar (w.Completion) a : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [distribHaarChar_archCentralUnit]

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_FujisakiC3b

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in
private theorem distribHaarChar_completion_eq_pow_mult (w : InfinitePlace F)
    [MeasurableSpace w.Completion] [BorelSpace w.Completion] (t : (w.Completion)ˣ) :
    distribHaarChar w.Completion t = ‖(t : w.Completion)‖₊ ^ w.mult := by
  rcases isReal_or_isComplex w with hv | hv
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isReal w hv, mult_isReal ⟨w, hv⟩]
  · rw [ArchMulHaarCompletion.distribHaarChar_completion_of_isComplex w hv, mult_isComplex ⟨w, hv⟩]

private theorem ideleNorm_archUnitHom (w : InfinitePlace F) (a : (w.Completion)ˣ) :
    ideleNorm F (archUnitHom w a) = ‖(a : w.Completion)‖ ^ w.mult := by
  borelize (w.Completion)
  rw [archUnitHom_apply, ideleNorm_archCentralUnit, distribHaarChar_completion_eq_pow_mult]
  push_cast
  rfl

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_FujisakiC3b
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_FujisakiC3c

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
private theorem continuous_archUnitHom_val (w : InfinitePlace F) :
    Continuous (fun a : (w.Completion)ˣ =>
      ((archUnitHom w a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
  refine continuous_prodMk.mpr ⟨?_, continuous_const⟩
  show Continuous fun a : (w.Completion)ˣ =>
    Function.update (1 : InfiniteAdeleRing F) w (a : w.Completion)
  exact continuous_const.update w Units.continuous_val

private theorem continuous_archUnitHom (w : InfinitePlace F) :
    Continuous (archUnitHom (F := F) w) := by
  classical
  refine Units.continuous_iff.mpr ⟨continuous_archUnitHom_val w, ?_⟩
  have key : (fun a : (w.Completion)ˣ => ↑(archUnitHom w a)⁻¹) =
      (fun a => ((archUnitHom w a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) := by
    funext a; rw [← map_inv]
  rw [key]
  exact (continuous_archUnitHom_val w).comp continuous_inv

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_FujisakiC3c
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_TateAssembly2

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel IsDedekindDomain Topology TopologicalSpace Set Filter"

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

private theorem idele_ext {x y : (AdeleRing (𝓞 F) F)ˣ} (harch : archUnits x = archUnits y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), unitAtHom v x = unitAtHom v y) : x = y := by
  refine Units.ext (Prod.ext ?_ ?_)
  · exact congrArg Units.val harch
  · refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    exact congrArg Units.val (hfin v)

section EmbUnitContinuity

variable (v : HeightOneSpectrum (𝓞 F))

open scoped Classical in
private def finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

end EmbUnitContinuity
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Assembly2

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private def archAsm : (InfiniteAdeleRing F)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun a :=
    { val := ((a : InfiniteAdeleRing F), 1)
      inv := (((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F), 1)
      val_inv := Prod.ext a.mul_inv (one_mul 1)
      inv_val := Prod.ext a.inv_mul (one_mul 1) }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext (Prod.ext rfl (one_mul 1).symm)

private theorem archUnits_archAsm (a : (InfiniteAdeleRing F)ˣ) : archUnits (archAsm (F := F) a) = a := Units.ext rfl

private theorem unitAtHom_archAsm (a : (InfiniteAdeleRing F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtHom v (archAsm (F := F) a) = 1 :=
  Units.ext rfl

private def sAsm : SUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ where
  toFun t := ∏ v : S, embUnit v.1 (t v)
  map_one' := by simp only [Pi.one_apply, map_one, Finset.prod_const_one]
  map_mul' t t' := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

private theorem sAsm_apply (t : SUnits (F := F) S) : sAsm S t = ∏ v : S, embUnit v.1 (t v) := rfl

private theorem archUnits_sAsm (t : SUnits (F := F) S) : archUnits (sAsm S t) = 1 := by
  rw [sAsm_apply, map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  exact Units.ext (embUnit_val_fst v.1 (t v))

private theorem unitAtHom_sAsm_of_mem (t : SUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (sAsm S t) = t ⟨v, hv⟩ := by
  rw [sAsm_apply, map_prod]
  rw [Finset.prod_eq_single (⟨v, hv⟩ : S)]
  · exact unitAtHom_embUnit_self v (t ⟨v, hv⟩)
  · intro w _ hw
    have hwv : (w.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun h => hw (Subtype.ext h)
    exact unitAtHom_embUnit_of_ne (Ne.symm hwv) (t w)
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem unitAtHom_sAsm_of_not_mem (t : SUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (sAsm S t) = 1 := by
  rw [sAsm_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have hwv : (w.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun h => hv (h ▸ w.2)
  exact unitAtHom_embUnit_of_ne (Ne.symm hwv) (t w)

private abbrev Q : Type := (InfiniteAdeleRing F)ˣ × (SUnits (F := F) S × DeepUnits (F := F) S)

private def asm : Q (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  MonoidHom.coprod archAsm (MonoidHom.coprod (sAsm S) (deepAsm S))

private theorem asm_apply (q : Q (F := F) S) : asm S q = archAsm q.1 * (sAsm S q.2.1 * deepAsm S q.2.2) := rfl

private theorem archUnits_deepAsm (o : DeepUnits (F := F) S) : archUnits (deepAsm S o) = 1 :=
  Units.ext (deepAsm_val_fst S o)

private theorem archUnits_asm (q : Q (F := F) S) : archUnits (asm S q) = q.1 := by
  rw [asm_apply, map_mul, map_mul, archUnits_archAsm, archUnits_sAsm, archUnits_deepAsm, mul_one, mul_one]

private theorem unitAtHom_asm_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (asm S q) = q.2.1 ⟨v, hv⟩ := by
  rw [asm_apply, map_mul, map_mul, unitAtHom_archAsm, unitAtHom_sAsm_of_mem S q.2.1 hv,
    unitAtHom_deepAsm_of_mem S q.2.2 hv, one_mul, mul_one]

private theorem unitAtHom_asm_of_not_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (asm S q) = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (q.2.2 ⟨v, hv⟩) := by
  rw [asm_apply, map_mul, map_mul, unitAtHom_archAsm, unitAtHom_sAsm_of_not_mem S q.2.1 hv,
    unitAtHom_deepAsm_of_not_mem S q.2.2 hv, one_mul, one_mul]

open scoped Classical in
private def deepCoordAt (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) : (v.adicCompletionIntegers F)ˣ :=
  if h : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F then
    { val := ⟨(unitAtHom v x : v.adicCompletion F), h.1⟩
      inv := ⟨(((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), h.2⟩
      val_inv := Subtype.ext (unitAtHom v x).mul_inv
      inv_val := Subtype.ext (unitAtHom v x).inv_mul }
  else 1

open scoped Classical in
private theorem deepCoordAt_spec (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ)
    (h : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (deepCoordAt v x) = unitAtHom v x := by
  refine Units.ext ?_
  show (((deepCoordAt v x : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = _
  rw [deepCoordAt, dif_pos h]

private def coord (x : (AdeleRing (𝓞 F) F)ˣ) : Q (F := F) S :=
  (archUnits x, (fun v => unitAtHom v.1 x, fun v => deepCoordAt v.1 x))

private theorem asm_coord {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) : asm S (coord S u) = u := by
  refine idele_ext (archUnits_asm S _) fun v => ?_
  by_cases hv : v ∈ S
  · exact (unitAtHom_asm_of_mem S (coord S u) hv).trans rfl
  · rw [unitAtHom_asm_of_not_mem S _ hv]
    show Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (deepCoordAt v u) = unitAtHom v u
    rw [mem_unitsOutside_iff] at hu
    refine deepCoordAt_spec v u ⟨?_, ?_⟩
    · exact hu.1 v hv
    · rw [← map_inv]; exact hu.2 v hv

private theorem continuous_unitAtHom (v : HeightOneSpectrum (𝓞 F)) : Continuous (unitAtHom (F := F) v) :=
  Units.continuous_map ((continuous_finAdeleEval (𝓞 F) F v).comp (continuous_adeleFin (𝓞 F) F))

private theorem continuous_archUnits : Continuous (archUnits (F := F)) :=
  Units.continuous_map (continuous_adeleArch (𝓞 F) F)

private theorem continuousOn_deepCoordAt {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ContinuousOn (deepCoordAt (F := F) v) (unitsOutside S) := by
  classical
  have key : ∀ u ∈ (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
      (unitAtHom v u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
        (((unitAtHom v u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro u hu
    have hu' := (mem_unitsOutside_iff S u).mp hu
    refine ⟨hu'.1 v hv, ?_⟩
    rw [← map_inv]; exact hu'.2 v hv
  rw [continuousOn_iff_continuous_restrict]
  have c1 : Continuous fun u : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) =>
      (⟨(unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F), (key u u.2).1⟩ : v.adicCompletionIntegers F) :=
    (Units.continuous_val.comp ((continuous_unitAtHom v).comp continuous_subtype_val)).subtype_mk _
  have c2 : Continuous fun u : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) =>
      (⟨(((unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), (key u u.2).2⟩ :
        v.adicCompletionIntegers F) :=
    (Units.continuous_coe_inv.comp ((continuous_unitAtHom v).comp continuous_subtype_val)).subtype_mk _
  refine Units.continuous_iff.mpr ⟨c1.congr fun u => ?_, c2.congr fun u => ?_⟩
  · refine Subtype.ext ?_
    show (unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F)
      = (((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ) : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
    rw [deepCoordAt, dif_pos (key u u.2)]
  · refine Subtype.ext ?_
    have e : ((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletionIntegers F)ˣ)
        = (deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ := rfl
    show (((unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
    rw [deepCoordAt, dif_pos (key u u.2)]
    rfl

private theorem continuousOn_coord : ContinuousOn (coord (F := F) S) (unitsOutside S) := by
  have h1 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => archUnits x) (unitsOutside S) :=
    continuous_archUnits.continuousOn
  have h2 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => fun v : S => unitAtHom v.1 x) (unitsOutside S) :=
    (continuous_pi fun v : S => continuous_unitAtHom (F := F) v.1).continuousOn
  have h3 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      deepCoordAt v.1 x) (unitsOutside S) :=
    continuousOn_pi.mpr fun v => continuousOn_deepCoordAt S v.2
  exact h1.prodMk (h2.prodMk h3)

end Assembly2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_TateAssembly2
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_TateSDecomp4

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicLevel IsDedekindDomain MeasureTheory Set"

open scoped NNReal Pointwise

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

set_option synthInstance.maxHeartbeats 1600000 in
private theorem ordAt_nonneg_of_mem (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ)
    (ht : (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F) : 0 ≤ ordAt v t := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  have ha : (⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F) ≠ 0 := by
    intro h
    exact t.ne_zero (congrArg Subtype.val h)
  have hbot : Ideal.span {(⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact ha
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  have hspan : Ideal.span {(⟨(t : v.adicCompletion F), ht⟩ : v.adicCompletionIntegers F)}
      = IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) ^ n := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have h := M4aLocalCFT.ValuationOrd.ord_ofMul_of_mem (v.adicCompletionIntegers F) ht hspan
  rw [ordAt, h]
  exact Int.natCast_nonneg n

private theorem mem_integers_iff_ordAt_nonneg (v : HeightOneSpectrum (𝓞 F)) (t : (v.adicCompletion F)ˣ) :
    (t : v.adicCompletion F) ∈ v.adicCompletionIntegers F ↔ 0 ≤ ordAt v t := by
  refine ⟨ordAt_nonneg_of_mem v t, fun h => ?_⟩
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (t : v.adicCompletion F) with ht | ht
  · exact ht
  · have ht' : ((t⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
      rwa [Units.val_inv_eq_inv_val]
    have h1 := ordAt_nonneg_of_mem v t⁻¹ ht'
    rw [ordAt_inv] at h1
    have h0 : ordAt v t = 0 := le_antisymm (by omega) h
    exact ((ordAt_eq_zero_iff v t).mp h0).1

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_TateSDecomp4
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_ShellSupport

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField MeasureTheory"

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

noncomputable section

namespace M4aLocalCFT
namespace ShellSupport

variable {F : Type} [Field F] [NumberField F]

private def integralOff (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}

private theorem isOpen_integralOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOff (F := F) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => (Valued.isOpen_integer (v.adicCompletion F)))
    (p := fun v => v ∉ S)
  exact h

private def boxAt (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    Set (v.adicCompletion F) :=
  {y | ((ϖ.ϖ v ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y ∈ v.adicCompletionIntegers F}

private theorem isOpen_boxAt (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    IsOpen (boxAt ϖ v m) :=
  (Valued.isOpen_integer (v.adicCompletion F)).preimage
    (continuous_const.mul continuous_id)

private theorem boxAt_mono (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ}
    (hmm : m ≤ m') : boxAt ϖ v m ⊆ boxAt ϖ v m' := by
  intro y hy
  simp only [boxAt, Set.mem_setOf_eq] at hy ⊢
  have hfac : ((ϖ.ϖ v ^ m' : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
      = ((ϖ.ϖ v ^ (m' - m) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        * (((ϖ.ϖ v ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) := by
    rw [← mul_assoc, ← Units.val_mul, ← pow_add, Nat.sub_add_cancel hmm]
  rw [hfac]
  have hint : ((ϖ.ϖ v ^ (m' - m) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      ∈ v.adicCompletionIntegers F := by
    rw [mem_integers_iff_ordAt_nonneg]
    have h1 : ordAt v (ϖ.ϖ v ^ ((m' - m : ℕ) : ℤ)) = ((m' - m : ℕ) : ℤ) * 1 := by
      rw [ordAt_zpow, ϖ.ordAt_eq_one v]
    rw [zpow_natCast] at h1
    rw [h1]
    positivity
  exact mul_mem hint hy

private theorem mem_boxAt_exists (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) : ∃ m : ℕ, y ∈ boxAt ϖ v m := by
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨0, ?_⟩
    simp only [boxAt, Set.mem_setOf_eq, mul_zero]
    exact zero_mem _
  · set u : (v.adicCompletion F)ˣ := Units.mk0 y hy0 with hu
    refine ⟨(-ordAt v u).toNat, ?_⟩
    have hcoe : ((ϖ.ϖ v ^ (-ordAt v u).toNat : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
        = ((ϖ.ϖ v ^ (-ordAt v u).toNat * u : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      rw [Units.val_mul, hu, Units.val_mk0]
    simp only [boxAt, Set.mem_setOf_eq]
    rw [hcoe, mem_integers_iff_ordAt_nonneg, ordAt_mul]
    have h1 : ordAt v (ϖ.ϖ v ^ (((-ordAt v u).toNat : ℕ) : ℤ)) = (((-ordAt v u).toNat : ℕ) : ℤ) * 1 := by
      rw [ordAt_zpow, ϖ.ordAt_eq_one v]
    rw [zpow_natCast] at h1
    rw [h1]
    omega

end M4aLocalCFT.ShellSupport
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_ShellSupport
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_ValuedOrdBridge

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set"

open WithZero Multiplicative

open scoped NNReal ENNReal

noncomputable section

namespace M4aLocalCFT

namespace ValuedOrdBridge

open LocalZetaUnramified MulHaarFromAdditive

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem valued_ne_zero_of_ne_zero {x : v.adicCompletion F} (hx : x ≠ 0) :
    Valued.v x ≠ 0 := by
  intro h0
  have h1 : Valued.v x * Valued.v x⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hx, map_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

private theorem valued_le_one_of_mem {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v x ≤ 1 :=
  hx

private theorem integers_adicCompletionIntegers :
    (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).Integers (v.adicCompletionIntegers F) :=
  Valuation.valuationSubring.integers _

private theorem exists_irreducible_valued :
    ∃ ϖ : v.adicCompletionIntegers F, Irreducible ϖ ∧
      Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
        = WithZero.exp (-1 : ℤ) := by
  obtain ⟨y, hy⟩ := valuedAdicCompletion_surjective (K := F) (v := v) (WithZero.exp (-1 : ℤ))
  have hy1 : y ∈ v.adicCompletionIntegers F := by
    rw [mem_adicCompletionIntegers, hy, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by norm_num)
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  refine ⟨⟨y, hy1⟩, ⟨?_, ?_⟩, hy⟩
  ·
    intro hu
    have h1 := (integers_adicCompletionIntegers (v := v)).one_of_isUnit hu
    rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) ⟨y, hy1⟩ = y
      from rfl, hy] at h1
    exact absurd ((WithZero.exp_eq_one).mp h1) (by norm_num)
  ·
    rintro a b hab
    have hane : (a : v.adicCompletion F) ≠ 0 := by
      intro h0
      apply hy0
      have : y = (a : v.adicCompletion F) * (b : v.adicCompletion F) := by
        simpa using congrArg Subtype.val hab
      rw [this, h0, zero_mul]
    have hbne : (b : v.adicCompletion F) ≠ 0 := by
      intro h0
      apply hy0
      have : y = (a : v.adicCompletion F) * (b : v.adicCompletion F) := by
        simpa using congrArg Subtype.val hab
      rw [this, h0, mul_zero]
    have hmul : Valued.v ((a : v.adicCompletion F)) * Valued.v ((b : v.adicCompletion F))
        = WithZero.exp (-1 : ℤ) := by
      rw [← map_mul]
      have : (a : v.adicCompletion F) * (b : v.adicCompletion F) = y := by
        simpa using (congrArg Subtype.val hab).symm
      rw [this, hy]
    have hva0 : Valued.v ((a : v.adicCompletion F)) ≠ 0 := by
      exact valued_ne_zero_of_ne_zero hane
    have hvb0 : Valued.v ((b : v.adicCompletion F)) ≠ 0 := by
      exact valued_ne_zero_of_ne_zero hbne
    set s : ℤ := WithZero.log (Valued.v ((a : v.adicCompletion F))) with hs
    set t : ℤ := WithZero.log (Valued.v ((b : v.adicCompletion F))) with ht
    have hexps : Valued.v ((a : v.adicCompletion F)) = WithZero.exp s :=
      (WithZero.exp_log hva0).symm
    have hexpt : Valued.v ((b : v.adicCompletion F)) = WithZero.exp t :=
      (WithZero.exp_log hvb0).symm
    have hsum : s + t = -1 := by
      have := hmul
      rw [hexps, hexpt, ← WithZero.exp_add] at this
      exact WithZero.exp_inj.mp this
    have hsle : s ≤ 0 := by
      have := valued_le_one_of_mem a.2
      rw [hexps, ← WithZero.exp_zero] at this
      exact WithZero.exp_le_exp.mp this
    have htle : t ≤ 0 := by
      have := valued_le_one_of_mem b.2
      rw [hexpt, ← WithZero.exp_zero] at this
      exact WithZero.exp_le_exp.mp this
    rcases (by omega : s = 0 ∨ t = 0) with h0 | h0
    · left
      refine (integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := a) ?_
      rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) a
        = (a : v.adicCompletion F) from rfl, hexps, h0, WithZero.exp_zero]
    · right
      refine (integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := b) ?_
      rw [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) b
        = (b : v.adicCompletion F) from rfl, hexpt, h0, WithZero.exp_zero]

variable {ϖ : v.adicCompletionIntegers F}

private theorem valued_coe_of_irreducible (hϖ : Irreducible ϖ) :
    Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π₀, hπ₀, hv₀⟩ := exists_irreducible_valued (v := v)
  have hϖK : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 :=
    coe_ne_zero_of_irreducible hϖ
  have hϖv0 : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    exact valued_ne_zero_of_ne_zero hϖK
  have hle : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≤ 1 :=
    valued_le_one_of_mem ϖ.2
  have hne1 : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 1 := by
    intro h1
    exact hϖ.not_isUnit ((integers_adicCompletionIntegers (v := v)).isUnit_of_one' (x := ϖ) h1)
  set s : ℤ := WithZero.log
    (Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)) with hs
  have hexps : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      = WithZero.exp s := (WithZero.exp_log hϖv0).symm
  have hsle : s ≤ 0 := by
    have := hle
    rw [hexps, ← WithZero.exp_zero] at this
    exact WithZero.exp_le_exp.mp this
  have hsne : s ≠ 0 := by
    intro h0
    exact hne1 (by rw [hexps, h0, WithZero.exp_zero])
  have hlev : Valued.v ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
      ≤ Valued.v ((π₀ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
    rw [hexps, hv₀]
    exact WithZero.exp_le_exp.mpr (by omega)
  have hdvd : π₀ ∣ ϖ :=
    ((integers_adicCompletionIntegers (v := v)).le_iff_dvd (x := ϖ) (y := π₀)).mp hlev
  obtain ⟨c, hc⟩ := hdvd
  rcases hϖ.isUnit_or_isUnit hc with hu | hu
  · exact absurd hu hπ₀.not_isUnit
  · have h1 : Valued.v ((c : v.adicCompletionIntegers F) : v.adicCompletion F) = 1 := by
      have := (integers_adicCompletionIntegers (v := v)).one_of_isUnit hu
      rwa [show (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) c
        = (c : v.adicCompletion F) from rfl] at this
    have hcoe : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)
        = ((π₀ : v.adicCompletionIntegers F) : v.adicCompletion F)
          * ((c : v.adicCompletionIntegers F) : v.adicCompletion F) := by
      simpa using congrArg Subtype.val hc
    rw [hcoe, map_mul, hv₀, h1, mul_one]

private theorem valued_coe_units_eq_exp_neg_ord (x : (v.adicCompletion F)ˣ) :
    Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x))) := by
  obtain ⟨π₀, hπ₀, hv₀⟩ := exists_irreducible_valued (v := v)
  set n : ℤ := ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul x) with hn
  set u : (v.adicCompletion F)ˣ := (piUnit hπ₀ ^ n)⁻¹ * x with hu
  have hordu : ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul u) = 0 := by
    rw [hu, ord_ofMul_mul,
      show ((piUnit hπ₀ ^ n)⁻¹ : (v.adicCompletion F)ˣ) = piUnit hπ₀ ^ (-n) from
        (zpow_neg _ _).symm,
      ord_ofMul_zpow_piUnit hπ₀, ← hn]
    omega
  obtain ⟨w, hw⟩ := (ValuationOrd.ord_eq_zero_iff (v.adicCompletionIntegers F) u).mp hordu
  have hvu : Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    have hiso : ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)) (w : _) := by
      rw [← hw]; rfl
    rw [hiso]
    exact (integers_adicCompletionIntegers (v := v)).one_of_isUnit w.isUnit
  have hx : (x : (v.adicCompletion F)ˣ) = piUnit hπ₀ ^ n * u := by
    rw [hu, mul_inv_cancel_left]
  have hvpi : Valued.v (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
      = WithZero.exp (-n) := by
    have hzpow : (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
        = (((piUnit hπ₀ : (v.adicCompletion F)ˣ)) : v.adicCompletion F) ^ n := by
      push_cast
      rfl
    rw [hzpow, map_zpow₀, piUnit_val, valued_coe_of_irreducible hπ₀,
      ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]
  calc Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = Valued.v ((((piUnit hπ₀ ^ n * u : (v.adicCompletion F)ˣ)) : v.adicCompletion F)) := by
        rw [← hx]
    _ = Valued.v (((piUnit hπ₀ ^ n : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
        * Valued.v ((u : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
        rw [Units.val_mul, map_mul]
    _ = WithZero.exp (-n) := by rw [hvpi, hvu, mul_one]

end ValuedOrdBridge
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_ValuedOrdBridge
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_TateReference

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set"

open M4aLocalCFT LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

section RangeVal

variable {K : Type*} [GroupWithZero K]

end RangeVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K]

variable [MeasurableSpace Kˣ]

end CompVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

variable {F : Type} [Field F] [NumberField F]

section Instances

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

end Instances
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Deep

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

end Deep
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section SFactor

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

end SFactor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Arch

private def archPiUnits : (InfiniteAdeleRing F)ˣ ≃ₜ* ((w : InfinitePlace F) → (w.Completion)ˣ) :=
  ContinuousMulEquiv.piUnits

omit [NumberField F] in
private theorem archPiUnits_apply (a : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    ((archPiUnits a w : (w.Completion)ˣ) : w.Completion) = (a : InfiniteAdeleRing F) w := rfl

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]

variable [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

end Arch
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Reference

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

end Reference
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Factorwise

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

section DeepConst

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]

end DeepConst
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section SProd

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]

end SProd
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section ArchProd

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]

end ArchProd
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Factorwise
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_TateReference
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_TateFubini

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter"

open M4aLocalCFT LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F]

open scoped Classical in
private theorem archPiUnits_archUnits_archUnitHom (w : InfinitePlace F) (u : (w.Completion)ˣ) :
    archPiUnits (archUnits (archUnitHom w u)) = Pi.mulSingle w u := by
  funext w'
  refine Units.ext ?_
  rw [archPiUnits_apply]
  show Function.update (1 : InfiniteAdeleRing F) w (u : w.Completion) w'
    = ((Pi.mulSingle w u : (w' : InfinitePlace F) → (w'.Completion)ˣ) w' : w'.Completion)
  by_cases h : w' = w
  · subst h
    rw [Function.update_self, Pi.mulSingle_eq_same]
  · rw [Function.update_of_ne h, Pi.mulSingle_eq_of_ne h]
    rfl

open scoped Classical in
private theorem archAsm_eq_prod_archUnitHom (a : (InfiniteAdeleRing F)ˣ) :
    archAsm a = ∏ w, archUnitHom w (archPiUnits a w) := by
  refine idele_ext ?_ (fun v => ?_)
  · apply (archPiUnits (F := F)).injective
    rw [archUnits_archAsm, map_prod, map_prod]
    simp_rw [archPiUnits_archUnits_archUnitHom]
    exact (Finset.univ_prod_mulSingle _).symm
  · rw [unitAtHom_archAsm, map_prod]
    exact (Finset.prod_eq_one fun w _ => Units.ext rfl).symm

section AlongAsm

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private theorem distribHaarChar_deepAsm (o : DeepUnits (F := F) S) :
    distribHaarChar (AdeleRing (𝓞 F) F) (deepAsm S o) = 1 := by
  refine distribHaarChar_eq_one_of_integral (deepAsm_val_fst S o) (fun w => ?_) (fun w => ?_)
  · rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _
  · rw [← map_inv, deepAsm_val_snd_apply]
    exact SetLike.coe_mem _

private theorem ideleNorm_asm (q : Q (F := F) S) :
    ideleNorm F (asm S q) = (∏ w, ((distribHaarChar (w.Completion) (archPiUnits q.1 w) : ℝ≥0) : ℝ))
      * ∏ v : S, ((distribHaarChar (v.1.adicCompletion F) (q.2.1 v) : ℝ≥0) : ℝ) := by
  unfold ideleNorm
  rw [asm_apply, map_mul, map_mul, archAsm_eq_prod_archUnitHom, map_prod, sAsm_apply, map_prod,
    distribHaarChar_deepAsm, mul_one]
  simp_rw [distribHaarChar_archUnitHom, distribHaarChar_embUnit_eq_local]
  push_cast
  rfl

end AlongAsm
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section DeepTrivial

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

end DeepTrivial
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Integrands

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

end Integrands
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section LocalIntegrals

section ArchLocal

variable [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion))

end ArchLocal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section FinLocal

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F))

end FinLocal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end LocalIntegrals
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Master

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletionIntegers F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)]
  [∀ v : HeightOneSpectrum (𝓞 F), MeasurableSpace (v.adicCompletion F)ˣ]
  [∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (v.adicCompletion F)ˣ]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)] [∀ w : InfinitePlace F, BorelSpace (w.Completion)]
  [∀ w : InfinitePlace F, MeasurableSpace (w.Completion)ˣ] [∀ w : InfinitePlace F, BorelSpace (w.Completion)ˣ]
  [MeasurableSpace (InfiniteAdeleRing F)ˣ] [BorelSpace (InfiniteAdeleRing F)ˣ]
  (μa : (w : InfinitePlace F) → Measure (w.Completion)) [∀ w, (μa w).IsAddHaarMeasure]
  (μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F)) [∀ v, (μf v).IsAddHaarMeasure]

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
  (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]

end Master
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_TateFubini
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_G2Proof

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume"

open AutomorphicForm IsDedekindDomain M4aLocalCFT

p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

open scoped NNReal Pointwise

noncomputable section

namespace M4aLocalCFT

namespace G2Proof

variable {F : Type} [Field F] [NumberField F]

private def unifOf (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ)) : Uniformizers F where
  ϖ := ϖ
  ordAt_eq_one v := by
    have h : WithZero.exp (-(ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ v))))
        = WithZero.exp (-1 : ℤ) := by
      rw [← ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord]
      exact hϖ v
    have h' := WithZero.exp_injective h
    show ValuationOrd.ord (v.adicCompletionIntegers F) (Additive.ofMul (ϖ v)) = 1
    omega

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

section TestFunction

variable {S}

variable {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

end TestFunction
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section PerShell

variable {S}

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable {f : AdeleRing (𝓞 F) F → ℂ} {g : (w : InfinitePlace F) → w.Completion → ℂ}
  {h : (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F → ℂ}

end PerShell
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Reindex

end Reindex
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end G2Proof
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end M4aLocalCFT
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_G2Proof
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_LocalBoxIntegrable

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain MeasureTheory MeasureTheory.Measure Topology TopologicalSpace Set Filter"

open M4aLocalCFT LanglandsTunnell.TateLocal

open scoped NNReal ENNReal

noncomputable section

namespace NumberField
p2m_export "NumberField" "FinitePlace InfiniteAdeleRing mk place InfinitePlace.Completion mixedEmbedding mixedEmbedding.mixedSpace InfiniteAdeleRing.ringEquiv_mixedSpace InfinitePlace.Completion.isometry_extensionEmbedding InfinitePlace AdeleRing FinitePlace.norm_def TateGlobal.zetaIntegral_meromorphic_continuation_fe TateGlobal.localChar TateGlobal.IsUnramifiedCharAt AdelicFourier.pureTensorSet AdelicFourier.schwartzBruhat AdelicFourier.tensor_mem_pureTensorSet AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet AdelicVolume.archCentralUnit AdelicLevel.finIncl AdelicLevel.localUnit AdelicBox.adelicBox AdelicBox.measure_adelicBox_lt_top AdelicBox.measure_adelicBox_pos TateGlobal.zetaIntegral_mul_eulerFactors_eq StandardAddChar.isGlobalAddChar_stdAddChar AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar isCompactAdicCompletionIntegers isOpenAdicCompletionIntegers"
namespace TateGlobal
p2m_export "NumberField.TateGlobal" "zetaIntegral_meromorphic_continuation_fe normOneIdeles ideleNorm zetaIntegral localChar archUnitHom archLocalChar IsUnramifiedCharAt integralOutside IsFactorizableStandardOutside mem_normOneIdeles_iff localChar_apply archUnitHom_apply zetaIntegral_mul_eulerFactors_eq"
p2m_open "NumberField.TateGlobal NumberField"

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

private theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (a : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp a) = e ^ a := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]
  congr 1

private theorem coe_distribHaarChar_adicCompletion_eq_norm (t : (v.adicCompletion F)ˣ) :
    ((distribHaarChar (v.adicCompletion F) t : ℝ≥0) : ℝ) = ‖(t : v.adicCompletion F)‖ := by
  rw [NumberField.FinitePlace.norm_def, ValuedOrdBridge.valued_coe_units_eq_exp_neg_ord, toNNReal_exp,
    LocalHaarModulus.distribHaarChar_adicCompletion]

section CompVal

variable {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K]
  [MeasurableSpace K] [MeasurableSingletonClass K] [MeasurableSpace Kˣ]

end CompVal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section FinLeg

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
  (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]

variable [MeasurableSpace (v.adicCompletion F)ˣ] [BorelSpace (v.adicCompletion F)ˣ]

end FinLeg
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end NumberField.TateGlobal
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Foot

end Foot
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_LocalBoxIntegrable
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_FujisakiC3d

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal NumberField.InfinitePlace IsDedekindDomain MeasureTheory Topology"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

private theorem exists_mem_unitsOutside (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), x ∈ unitsOutside (F := F) S := by
  classical
  have h1 : {v : HeightOneSpectrum (𝓞 F) |
      ¬ ((((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp (((x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  have h2 : {v : HeightOneSpectrum (𝓞 F) |
      ¬ ((((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
        ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  refine ⟨h1.toFinset ∪ h2.toFinset, (mem_unitsOutside_iff _ x).mpr ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · by_contra hnot
    exact hv (Finset.mem_union_left _ (h1.mem_toFinset.mpr hnot))
  · by_contra hnot
    exact hv (Finset.mem_union_right _ (h2.mem_toFinset.mpr hnot))

section NormQ

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private def normQ (q : Q (F := F) S) : ℝ :=
  (∏ w : InfinitePlace F, ‖((q.1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ ^ w.mult) *
    ∏ v : S, ‖((q.2.1 v : (v.1.adicCompletion F)ˣ) : v.1.adicCompletion F)‖

private theorem continuous_normQ : Continuous (normQ (F := F) S) := by
  refine Continuous.mul ?_ ?_
  · refine continuous_finsetProd _ fun w _ => ?_
    exact (((continuous_apply w).comp (Units.continuous_val.comp continuous_fst)).norm).pow _
  · refine continuous_finsetProd _ fun v _ => ?_
    exact (Units.continuous_val.comp ((continuous_apply v).comp (continuous_fst.comp continuous_snd))).norm

private theorem ideleNorm_asm_eq_normQ (q : Q (F := F) S) : ideleNorm F (asm S q) = normQ S q := by
  rw [ideleNorm_asm]
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun w _ => ?_) (Finset.prod_congr rfl fun v _ => ?_)
  · borelize (w.Completion)
    rw [FujisakiC3.distribHaarChar_completion_eq_pow_mult]
    push_cast
    rfl
  · exact coe_distribHaarChar_adicCompletion_eq_norm (q.2.1 v)

private theorem continuousOn_ideleNorm : ContinuousOn (ideleNorm F) (unitsOutside (F := F) S) := by
  have h : Set.EqOn (ideleNorm F) (normQ S ∘ coord S) (unitsOutside (F := F) S) := fun x hx => by
    show ideleNorm F x = normQ S (coord S x)
    rw [← ideleNorm_asm_eq_normQ, asm_coord S hx]
  exact ((continuous_normQ S).comp_continuousOn (continuousOn_coord S)).congr h

end NormQ
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

private theorem continuous_ideleNorm : Continuous (ideleNorm F) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  obtain ⟨S, hS⟩ := exists_mem_unitsOutside x
  exact (continuousOn_ideleNorm S).continuousAt ((isOpen_unitsOutside S).mem_nhds hS)

private theorem isClosed_normOneIdeles : IsClosed (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) := by
  have h : (normOneIdeles F : Set (AdeleRing (𝓞 F) F)ˣ) = ideleNorm F ⁻¹' {1} := by
    ext x
    exact mem_normOneIdeles_iff x
  rw [h]
  exact isClosed_singleton.preimage continuous_ideleNorm

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_FujisakiC3d
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_FujisakiC3e

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal NumberField.InfinitePlace NumberField.InfinitePlace.Completion P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

open scoped NNReal

noncomputable section

namespace M4aLocalCFT
namespace FujisakiC3

variable {F : Type} [Field F] [NumberField F]

variable (F) in

private def ideleNormU : (AdeleRing (𝓞 F) F)ˣ →* ℝ≥0ˣ :=
  (distribHaarChar (AdeleRing (𝓞 F) F)).toHomUnits

private theorem val_ideleNormU (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((ideleNormU F x : ℝ≥0ˣ) : ℝ≥0) = distribHaarChar (AdeleRing (𝓞 F) F) x := rfl

private theorem ideleNormU_eq_one_iff (x : (AdeleRing (𝓞 F) F)ˣ) : ideleNormU F x = 1 ↔ x ∈ normOneIdeles F := by
  rw [← Units.val_eq_one, val_ideleNormU, normOneIdeles, MonoidHom.mem_ker]

private theorem ideleNormU_of_mem {x : (AdeleRing (𝓞 F) F)ˣ} (hx : x ∈ normOneIdeles F) : ideleNormU F x = 1 :=
  (ideleNormU_eq_one_iff x).mpr hx

private theorem continuous_distribHaarChar_idele :
    Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => distribHaarChar (AdeleRing (𝓞 F) F) x :=
  continuous_induced_rng.2 continuous_ideleNorm

private theorem continuous_ideleNormU : Continuous (ideleNormU F) := by
  refine Units.continuous_iff.mpr ⟨continuous_distribHaarChar_idele, ?_⟩
  show Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => distribHaarChar (AdeleRing (𝓞 F) F) x⁻¹
  exact continuous_distribHaarChar_idele.comp continuous_inv

section LocalSection

variable {w : InfinitePlace F}

omit [NumberField F] in
private theorem norm_ringEquivRealOfIsReal_symm (hv : IsReal w) (t : ℝ) : ‖(ringEquivRealOfIsReal hv).symm t‖ = ‖t‖ := by
  have h := ArchMulHaarCompletion.nnnorm_ringEquivReal hv ((ringEquivRealOfIsReal hv).symm t)
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [coe_nnnorm] using congrArg NNReal.toReal h.symm

omit [NumberField F] in
private theorem norm_ringEquivComplexOfIsComplex_symm (hv : IsComplex w) (z : ℂ) :
    ‖(ringEquivComplexOfIsComplex hv).symm z‖ = ‖z‖ := by
  have h := ArchMulHaarCompletion.nnnorm_ringEquivComplex hv ((ringEquivComplexOfIsComplex hv).symm z)
  rw [RingEquiv.apply_symm_apply] at h
  simpa only [coe_nnnorm] using congrArg NNReal.toReal h.symm

omit [NumberField F] in
private theorem continuous_ringEquivRealOfIsReal_symm (hv : IsReal w) : Continuous (ringEquivRealOfIsReal hv).symm :=
  (isometryEquivRealOfIsReal hv).symm.continuous

omit [NumberField F] in
private theorem continuous_ringEquivComplexOfIsComplex_symm (hv : IsComplex w) :
    Continuous (ringEquivComplexOfIsComplex hv).symm :=
  (isometryEquivComplexOfIsComplex hv).symm.continuous

private def realSectionOfIsReal (hv : IsReal w) : ℝ≥0ˣ →* (w.Completion)ˣ :=
  (Units.map (ringEquivRealOfIsReal hv).symm.toRingHom.toMonoidHom).comp (Units.map NNReal.toRealHom.toMonoidHom)

private def realSectionOfIsComplex (hv : IsComplex w) : ℝ≥0ˣ →* (w.Completion)ˣ :=
  (Units.map (ringEquivComplexOfIsComplex hv).symm.toRingHom.toMonoidHom).comp <|
    (Units.map Complex.ofRealHom.toMonoidHom).comp <|
      (Units.map NNReal.toRealHom.toMonoidHom).comp (Units.map NNReal.sqrtHom.toMonoidHom)

omit [NumberField F] in
private theorem val_realSectionOfIsReal (hv : IsReal w) (r : ℝ≥0ˣ) :
    ((realSectionOfIsReal hv r : (w.Completion)ˣ) : w.Completion) =
      (ringEquivRealOfIsReal hv).symm ((r : ℝ≥0) : ℝ) := rfl

omit [NumberField F] in
private theorem val_realSectionOfIsComplex (hv : IsComplex w) (r : ℝ≥0ˣ) :
    ((realSectionOfIsComplex hv r : (w.Completion)ˣ) : w.Completion) =
      (ringEquivComplexOfIsComplex hv).symm (((NNReal.sqrt (r : ℝ≥0) : ℝ≥0) : ℝ) : ℂ) := rfl

omit [NumberField F] in
private theorem continuous_realSectionOfIsReal (hv : IsReal w) : Continuous (realSectionOfIsReal hv) :=
  (Continuous.units_map _ (continuous_ringEquivRealOfIsReal_symm hv)).comp
    (Continuous.units_map _ NNReal.continuous_coe)

omit [NumberField F] in
private theorem continuous_realSectionOfIsComplex (hv : IsComplex w) : Continuous (realSectionOfIsComplex hv) :=
  (Continuous.units_map _ (continuous_ringEquivComplexOfIsComplex_symm hv)).comp <|
    (Continuous.units_map _ Complex.continuous_ofReal).comp <|
      (Continuous.units_map _ NNReal.continuous_coe).comp (Continuous.units_map _ NNReal.continuous_sqrt)

variable (w)

open scoped Classical in
private def localSection : ℝ≥0ˣ →* (w.Completion)ˣ :=
  if hv : IsReal w then realSectionOfIsReal hv else realSectionOfIsComplex (not_isReal_iff_isComplex.mp hv)

omit [NumberField F] in
private theorem continuous_localSection : Continuous (localSection w) := by
  by_cases hv : IsReal w
  · rw [localSection, dif_pos hv]; exact continuous_realSectionOfIsReal hv
  · rw [localSection, dif_neg hv]; exact continuous_realSectionOfIsComplex _

omit [NumberField F] in
private theorem norm_localSection_pow_mult (r : ℝ≥0ˣ) :
    ‖((localSection w r : (w.Completion)ˣ) : w.Completion)‖ ^ w.mult = ((r : ℝ≥0) : ℝ) := by
  by_cases hv : IsReal w
  · rw [localSection, dif_pos hv, val_realSectionOfIsReal, norm_ringEquivRealOfIsReal_symm, mult_isReal ⟨w, hv⟩,
      pow_one, NNReal.norm_eq]
  · rw [localSection, dif_neg hv, val_realSectionOfIsComplex, norm_ringEquivComplexOfIsComplex_symm,
      mult_isComplex ⟨w, not_isReal_iff_isComplex.mp hv⟩, Complex.norm_real, NNReal.norm_eq, ← NNReal.coe_pow,
      NNReal.sq_sqrt]

private def normSectionAt : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ :=
  (archUnitHom w).comp (localSection w)

private theorem normSectionAt_apply (r : ℝ≥0ˣ) : normSectionAt w r = archUnitHom w (localSection w r) := rfl

private theorem continuous_normSectionAt : Continuous (normSectionAt (F := F) w) :=
  (continuous_archUnitHom w).comp (continuous_localSection w)

private theorem ideleNorm_normSectionAt (r : ℝ≥0ˣ) : ideleNorm F (normSectionAt w r) = ((r : ℝ≥0) : ℝ) := by
  rw [normSectionAt_apply, ideleNorm_archUnitHom, norm_localSection_pow_mult]

private theorem ideleNormU_normSectionAt (r : ℝ≥0ˣ) : ideleNormU F (normSectionAt w r) = r :=
  Units.ext (NNReal.coe_injective (ideleNorm_normSectionAt w r))

end LocalSection
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Split

variable (w : InfinitePlace F)

private def normOnePart (x : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  x * (normSectionAt w (ideleNormU F x))⁻¹

private theorem normOnePart_mem (x : (AdeleRing (𝓞 F) F)ˣ) : normOnePart w x ∈ normOneIdeles F := by
  rw [← ideleNormU_eq_one_iff, normOnePart, map_mul, map_inv, ideleNormU_normSectionAt, mul_inv_cancel]

private theorem normOnePart_mul (x y : (AdeleRing (𝓞 F) F)ˣ) :
    normOnePart w (x * y) = normOnePart w x * normOnePart w y := by
  simp only [normOnePart, map_mul, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

private theorem continuous_normOnePart : Continuous (normOnePart (F := F) w) :=
  continuous_id.mul ((continuous_normSectionAt w).comp continuous_ideleNormU).inv

private def splitFun (x : (AdeleRing (𝓞 F) F)ˣ) : ↥(normOneIdeles F) × ℝ≥0ˣ :=
  (⟨normOnePart w x, normOnePart_mem w x⟩, ideleNormU F x)

private def splitInv (p : ↥(normOneIdeles F) × ℝ≥0ˣ) : (AdeleRing (𝓞 F) F)ˣ :=
  (p.1 : (AdeleRing (𝓞 F) F)ˣ) * normSectionAt w p.2

private theorem splitInv_splitFun (x : (AdeleRing (𝓞 F) F)ˣ) : splitInv w (splitFun w x) = x := by
  show x * (normSectionAt w (ideleNormU F x))⁻¹ * normSectionAt w (ideleNormU F x) = x
  rw [inv_mul_cancel_right]

private theorem ideleNormU_splitInv (p : ↥(normOneIdeles F) × ℝ≥0ˣ) : ideleNormU F (splitInv w p) = p.2 := by
  rw [splitInv, map_mul, ideleNormU_of_mem p.1.2, ideleNormU_normSectionAt, one_mul]

private theorem splitFun_splitInv (p : ↥(normOneIdeles F) × ℝ≥0ˣ) : splitFun w (splitInv w p) = p := by
  refine Prod.ext (Subtype.ext ?_) (ideleNormU_splitInv w p)
  show splitInv w p * (normSectionAt w (ideleNormU F (splitInv w p)))⁻¹ = p.1
  rw [ideleNormU_splitInv, splitInv, mul_inv_cancel_right]

private def idelesSplitAt : (AdeleRing (𝓞 F) F)ˣ ≃ₜ* ↥(normOneIdeles F) × ℝ≥0ˣ where
  toFun := splitFun w
  invFun := splitInv w
  left_inv := splitInv_splitFun w
  right_inv := splitFun_splitInv w
  map_mul' x y := Prod.ext (Subtype.ext (normOnePart_mul w x y)) (map_mul (ideleNormU F) x y)
  continuous_toFun := ((continuous_normOnePart w).subtype_mk _).prodMk continuous_ideleNormU
  continuous_invFun :=
    (continuous_subtype_val.comp continuous_fst).mul ((continuous_normSectionAt w).comp continuous_snd)

end Split
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

variable (F) in

private def idelesSplit : (AdeleRing (𝓞 F) F)ˣ ≃ₜ* ↥(normOneIdeles F) × ℝ≥0ˣ :=
  idelesSplitAt (Classical.arbitrary (InfinitePlace F))

end M4aLocalCFT.FujisakiC3
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end Fold_FujisakiC3e
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

section Fold_W2aGauss

open Real

open scoped SchwartzMap RealInnerProductSpace

noncomputable section

namespace M4aD3Glue

private theorem gauss_poly_bound (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → (1 + t) ^ m * Real.exp (-(π * t ^ 2)) ≤ M := by
  refine ⟨Real.exp ((m : ℝ) ^ 2 / (4 * π)), (Real.exp_pos _).le, fun t ht => ?_⟩
  have h1t : 1 + t ≤ Real.exp t := by
    simpa [add_comm] using Real.add_one_le_exp t
  have h1 : (1 + t) ^ m ≤ Real.exp t ^ m := pow_le_pow_left₀ (by linarith) h1t m
  have h2 : Real.exp t ^ m = Real.exp ((m : ℝ) * t) := (Real.exp_nat_mul t m).symm
  have h4 : (m : ℝ) * t - π * t ^ 2 ≤ (m : ℝ) ^ 2 / (4 * π) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * π)]
    nlinarith [sq_nonneg (2 * π * t - (m : ℝ)), Real.pi_pos, sq_nonneg t]
  calc (1 + t) ^ m * Real.exp (-(π * t ^ 2))
      ≤ Real.exp ((m : ℝ) * t) * Real.exp (-(π * t ^ 2)) :=
        mul_le_mul_of_nonneg_right (h1.trans_eq h2) (Real.exp_pos _).le
    _ = Real.exp ((m : ℝ) * t - π * t ^ 2) := by rw [← Real.exp_add]; ring_nf
    _ ≤ Real.exp ((m : ℝ) ^ 2 / (4 * π)) := Real.exp_le_exp.mpr h4

section Exponent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def gaussExponent (y : E) : ℝ := -(π * ‖y‖ ^ 2)

private theorem contDiff_gaussExponent : ContDiff ℝ (⊤ : ℕ∞) (gaussExponent (E := E)) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun y : E => ‖y‖ ^ 2 := contDiff_norm_sq ℝ
  unfold gaussExponent
  simpa using (contDiff_const.mul h).neg

private def gaussProfile (y : E) : ℝ := Real.exp (gaussExponent y)

private theorem contDiff_gaussProfile : ContDiff ℝ (⊤ : ℕ∞) (gaussProfile (E := E)) :=
  Real.contDiff_exp.comp contDiff_gaussExponent

end Exponent
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

private theorem iteratedDeriv_real_exp (i : ℕ) : iteratedDeriv i Real.exp = Real.exp := by
  induction i with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, ih, Real.deriv_exp]

section Main

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

variable (E) in

private def gaussInnerCLM : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (((LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ) :
        (E →ₗ[ℝ] ℝ) →ₗ[ℝ] E →L[ℝ] ℝ).comp (innerₗ E))

@[scoped simp] private theorem gaussInnerCLM_apply (y z : E) : gaussInnerCLM E y z = ⟪y, z⟫ := rfl

omit [FiniteDimensional ℝ E] in
private theorem norm_iteratedFDeriv_clm_apply_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E →L[ℝ] F) (j : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ j (fun v : E => c v) y‖ ≤ ‖c‖ * (1 + ‖y‖) := by
  have hy : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hc : (0 : ℝ) ≤ ‖c‖ := c.opNorm_nonneg
  match j with
  | 0 =>
    rw [norm_iteratedFDeriv_zero]
    calc ‖c y‖ ≤ ‖c‖ * ‖y‖ := c.le_opNorm y
      _ ≤ ‖c‖ * (1 + ‖y‖) := by nlinarith
  | 1 =>
    rw [norm_iteratedFDeriv_one, c.fderiv]
    nlinarith
  | (m + 2) =>
    have h1 : ‖iteratedFDeriv ℝ (m + 2) (fun v : E => c v) y‖
        = ‖iteratedFDeriv ℝ (m + 1) (fderiv ℝ fun v : E => c v) y‖ :=
      (norm_iteratedFDeriv_fderiv).symm
    have h2 : (fderiv ℝ fun v : E => c v) = fun _ : E => c := funext fun v => c.fderiv
    rw [h1, h2, iteratedFDeriv_const_of_ne (Nat.succ_ne_zero m)]
    simp only [Pi.zero_apply, norm_zero]
    positivity

private theorem hasFDerivAt_gaussExponent (y : E) :
    HasFDerivAt (gaussExponent (E := E)) (((-(2 * π)) • gaussInnerCLM E) y) y := by
  have hd : DifferentiableAt ℝ (fun v : E => ‖v‖ ^ 2) y :=
    ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero).differentiableAt
  have hfd : HasFDerivAt (fun v : E => ‖v‖ ^ 2) (2 • innerSL ℝ y) y := by
    have h := hd.hasFDerivAt
    rwa [fderiv_norm_sq_apply] at h
  have h2 : HasFDerivAt (fun v : E => -(π * ‖v‖ ^ 2)) (-(π • (2 • innerSL ℝ y))) y :=
    (hfd.const_mul π).neg
  have h2' : HasFDerivAt (gaussExponent (E := E)) (-(π • (2 • innerSL ℝ y))) y := h2
  have hCLM : ((-(2 * π)) • gaussInnerCLM E) y = -(π • (2 • innerSL ℝ y)) := by
    ext z
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
      gaussInnerCLM_apply, smul_eq_mul, nsmul_eq_mul]
    have hSL : innerSL ℝ y z = ⟪y, z⟫ := rfl
    rw [hSL]
    ring
  rw [hCLM]
  exact h2'

private theorem fderiv_gaussExponent_eq :
    fderiv ℝ (gaussExponent (E := E)) = fun y => ((-(2 * π)) • gaussInnerCLM E) y :=
  funext fun y => (hasFDerivAt_gaussExponent y).fderiv

private theorem norm_iteratedFDeriv_gaussExponent_le (i : ℕ) (hi : 1 ≤ i) (y : E) :
    ‖iteratedFDeriv ℝ i (gaussExponent (E := E)) y‖
      ≤ ‖(-(2 * π)) • gaussInnerCLM E‖ * (1 + ‖y‖) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have h1 : ‖iteratedFDeriv ℝ (j + 1) (gaussExponent (E := E)) y‖
      = ‖iteratedFDeriv ℝ j (fderiv ℝ (gaussExponent (E := E))) y‖ :=
    (norm_iteratedFDeriv_fderiv).symm
  rw [h1, fderiv_gaussExponent_eq]
  exact norm_iteratedFDeriv_clm_apply_le _ j y

private theorem norm_iteratedFDeriv_gaussProfile_le (n : ℕ) (y : E) :
    ‖iteratedFDeriv ℝ n (gaussProfile (E := E)) y‖
      ≤ (n.factorial : ℝ) * Real.exp (gaussExponent y)
        * ((1 + ‖(-(2 * π)) • gaussInnerCLM E‖) * (1 + ‖y‖)) ^ n := by
  have hA : (0 : ℝ) ≤ ‖(-(2 * π)) • gaussInnerCLM E‖ := ContinuousLinearMap.opNorm_nonneg _
  have hy : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hD1 : (1 : ℝ) ≤ (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) * (1 + ‖y‖) := by nlinarith
  have hcomp : gaussProfile (E := E) = Real.exp ∘ gaussExponent (E := E) := rfl
  rw [hcomp]
  refine norm_iteratedFDeriv_comp_le (𝕜 := ℝ) Real.contDiff_exp contDiff_gaussExponent
    (by exact_mod_cast le_top) y ?_ ?_
  · intro i _
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_real_exp,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · intro i hi _
    refine (norm_iteratedFDeriv_gaussExponent_le i hi y).trans ?_
    calc ‖(-(2 * π)) • gaussInnerCLM E‖ * (1 + ‖y‖)
        ≤ (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) * (1 + ‖y‖) := by nlinarith
      _ = ((1 + ‖(-(2 * π)) • gaussInnerCLM E‖) * (1 + ‖y‖)) ^ 1 := (pow_one _).symm
      _ ≤ ((1 + ‖(-(2 * π)) • gaussInnerCLM E‖) * (1 + ‖y‖)) ^ i :=
          pow_le_pow_right₀ hD1 hi

variable (E) in

private def gaussSchwartzMap : 𝓢(E, ℂ) where
  toFun y := (gaussProfile y : ℂ)
  smooth' := Complex.ofRealCLM.contDiff.comp contDiff_gaussProfile
  decay' := by
    intro k n
    obtain ⟨M, hM0, hM⟩ := gauss_poly_bound (k + n)
    refine ⟨‖Complex.ofRealCLM‖ * ((n.factorial : ℝ)
      * (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) ^ n * M), fun y => ?_⟩
    have hy : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    have hA : (0 : ℝ) ≤ ‖(-(2 * π)) • gaussInnerCLM E‖ := ContinuousLinearMap.opNorm_nonneg _
    have hcoe : (fun v : E => (gaussProfile v : ℂ))
        = ⇑Complex.ofRealCLM ∘ gaussProfile (E := E) := rfl
    have h1 : ‖iteratedFDeriv ℝ n (fun v : E => (gaussProfile v : ℂ)) y‖
        ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ n (gaussProfile (E := E)) y‖ := by
      rw [hcoe]
      exact Complex.ofRealCLM.norm_iteratedFDeriv_comp_left
        (contDiff_gaussProfile (E := E)).contDiffAt (by exact_mod_cast le_top)
    have h2 := norm_iteratedFDeriv_gaussProfile_le (E := E) n y
    have hexp : Real.exp (gaussExponent y) = Real.exp (-(π * ‖y‖ ^ 2)) := rfl
    calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (fun v : E => (gaussProfile v : ℂ)) y‖
        ≤ ‖y‖ ^ k * (‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ n (gaussProfile (E := E)) y‖) := by
          gcongr
      _ ≤ ‖y‖ ^ k * (‖Complex.ofRealCLM‖ * ((n.factorial : ℝ) * Real.exp (gaussExponent y)
            * ((1 + ‖(-(2 * π)) • gaussInnerCLM E‖) * (1 + ‖y‖)) ^ n)) := by
          gcongr
      _ = ‖Complex.ofRealCLM‖ * ((n.factorial : ℝ)
            * (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) ^ n)
            * (‖y‖ ^ k * (1 + ‖y‖) ^ n * Real.exp (-(π * ‖y‖ ^ 2))) := by
          rw [hexp, mul_pow]; ring
      _ ≤ ‖Complex.ofRealCLM‖ * ((n.factorial : ℝ)
            * (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) ^ n)
            * ((1 + ‖y‖) ^ (k + n) * Real.exp (-(π * ‖y‖ ^ 2))) := by
          have hkn : ‖y‖ ^ k * (1 + ‖y‖) ^ n ≤ (1 + ‖y‖) ^ (k + n) := by
            rw [pow_add]
            exact mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hy (by linarith) k) (by positivity)
          have hstep : ‖y‖ ^ k * (1 + ‖y‖) ^ n * Real.exp (-(π * ‖y‖ ^ 2))
              ≤ (1 + ‖y‖) ^ (k + n) * Real.exp (-(π * ‖y‖ ^ 2)) :=
            mul_le_mul_of_nonneg_right hkn (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ ‖Complex.ofRealCLM‖ * ((n.factorial : ℝ)
            * (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) ^ n) * M := by
          gcongr
          exact hM ‖y‖ hy
      _ = ‖Complex.ofRealCLM‖ * ((n.factorial : ℝ)
            * (1 + ‖(-(2 * π)) • gaussInnerCLM E‖) ^ n * M) := by ring

@[scoped simp] private theorem gaussSchwartzMap_apply (y : E) :
    gaussSchwartzMap E y = Complex.exp (-((π : ℂ) * (‖y‖ : ℂ) ^ 2)) := by
  show ((Real.exp (-(π * ‖y‖ ^ 2)) : ℝ) : ℂ) = _
  rw [Complex.ofReal_exp]
  push_cast
  ring_nf

end Main
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end Fold_W2aGauss
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section Fold_W2bArchTensor

p2m_open "Real NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.mixedEmbedding NumberField.InfinitePlace"

open LanglandsTunnell.ArchPlace

open scoped SchwartzMap

open Classical

noncomputable section

namespace M4aD3Glue

variable (K : Type) [Field K] [NumberField K]

private def cxDil : mixedSpace K ≃L[ℝ] mixedSpace K :=
  ((LinearEquiv.refl ℝ ({w : InfinitePlace K // IsReal w} → ℝ)).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ({w : InfinitePlace K // IsComplex w} → ℂ) (Real.sqrt 2)
      (ne_of_gt (by positivity)))).toContinuousLinearEquiv

@[scoped simp] private theorem cxDil_apply (v : mixedSpace K) :
    cxDil K v = (v.1, Real.sqrt 2 • v.2) := rfl

private def toEuclidGauss : mixedSpace K ≃L[ℝ] euclidean.mixedSpace K :=
  (cxDil K).trans (euclidean.toMixed K).symm

private theorem norm_sq_toEuclidGauss (v : mixedSpace K) :
    ‖toEuclidGauss K v‖ ^ 2
      = (∑ w : {w : InfinitePlace K // IsReal w}, (v.1 w) ^ 2)
        + 2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖v.2 w‖ ^ 2 := by
  have happ : toEuclidGauss K v = (euclidean.toMixed K).symm (v.1, Real.sqrt 2 • v.2) := rfl
  have hfst : ((euclidean.toMixed K).symm (v.1, Real.sqrt 2 • v.2)).fst
      = WithLp.toLp 2 (v.1) := rfl
  have hsnd : ((euclidean.toMixed K).symm (v.1, Real.sqrt 2 • v.2)).snd
      = WithLp.toLp 2 (Real.sqrt 2 • v.2) := rfl
  rw [happ, WithLp.prod_norm_sq_eq_of_L2, hfst, hsnd]
  have h1 : ‖(WithLp.toLp 2 (v.1) : EuclideanSpace ℝ {w : InfinitePlace K // IsReal w})‖ ^ 2
      = ∑ w : {w : InfinitePlace K // IsReal w}, (v.1 w) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have h2 : ‖(WithLp.toLp 2 (Real.sqrt 2 • v.2) :
        EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w})‖ ^ 2
      = 2 * ∑ w : {w : InfinitePlace K // IsComplex w}, ‖v.2 w‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have : (WithLp.toLp 2 (Real.sqrt 2 • v.2) :
        EuclideanSpace ℂ {w : InfinitePlace K // IsComplex w}) w = Real.sqrt 2 • v.2 w := rfl
    rw [this, _root_.norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  rw [h1, h2]

private def archGaussBase : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclidGauss K)
    (gaussSchwartzMap (euclidean.mixedSpace K))

private theorem archGaussBase_apply (v : mixedSpace K) :
    archGaussBase K v
      = Complex.exp (-((π : ℂ) * ((‖toEuclidGauss K v‖ : ℝ) : ℂ) ^ 2)) := by
  show gaussSchwartzMap (euclidean.mixedSpace K) (toEuclidGauss K v) = _
  rw [gaussSchwartzMap_apply]

variable {K}

private theorem htg_mul' {f g : mixedSpace K → ℂ} (hf : Function.HasTemperateGrowth f)
    (hg : Function.HasTemperateGrowth g) :
    Function.HasTemperateGrowth fun v => f v * g v := by
  exact hf.mul hg

private theorem htg_pow_clm (c : mixedSpace K →L[ℝ] ℂ) (n : ℕ) :
    Function.HasTemperateGrowth fun v => c v ^ n := by
  exact c.hasTemperateGrowth.pow n

private theorem htg_finset_prod {ι : Type*} (s : Finset ι) (f : ι → mixedSpace K → ℂ)
    (h : ∀ i ∈ s, Function.HasTemperateGrowth (f i)) :
    Function.HasTemperateGrowth fun v => ∏ i ∈ s, f i v := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    simp only [Finset.prod_cons]
    exact htg_mul' (h i (Finset.mem_cons_self _ _))
      (ih fun j hj => h j (Finset.mem_cons_of_mem hj))

private def realCoordCLM (w : {w : InfinitePlace K // IsReal w}) : mixedSpace K →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w).comp
    (ContinuousLinearMap.fst ℝ ({w : InfinitePlace K // IsReal w} → ℝ)
      ({w : InfinitePlace K // IsComplex w} → ℂ)))

omit [NumberField K] in
@[scoped simp] private theorem realCoordCLM_apply (w : {w : InfinitePlace K // IsReal w}) (v : mixedSpace K) :
    realCoordCLM w v = ((v.1 w : ℝ) : ℂ) := rfl

private def cxCoordCLM (w : {w : InfinitePlace K // IsComplex w}) : mixedSpace K →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj w).comp
    (ContinuousLinearMap.snd ℝ ({w : InfinitePlace K // IsReal w} → ℝ)
      ({w : InfinitePlace K // IsComplex w} → ℂ))

omit [NumberField K] in
@[scoped simp] private theorem cxCoordCLM_apply (w : {w : InfinitePlace K // IsComplex w}) (v : mixedSpace K) :
    cxCoordCLM w v = v.2 w := rfl

private def cxConjCoordCLM (w : {w : InfinitePlace K // IsComplex w}) : mixedSpace K →L[ℝ] ℂ :=
  (Complex.conjCLE.toContinuousLinearMap).comp (cxCoordCLM w)

omit [NumberField K] in
@[scoped simp] private theorem cxConjCoordCLM_apply (w : {w : InfinitePlace K // IsComplex w})
    (v : mixedSpace K) : cxConjCoordCLM w v = starRingEnd ℂ (v.2 w) := rfl

private def archMonomial (a : {w : InfinitePlace K // IsReal w} → ZMod 2)
    (k : {w : InfinitePlace K // IsComplex w} → ℤ) : mixedSpace K → ℂ := fun v =>
  (∏ w : {w : InfinitePlace K // IsReal w}, ((v.1 w : ℝ) : ℂ) ^ ((a w).val)) *
    ∏ w : {w : InfinitePlace K // IsComplex w},
      (starRingEnd ℂ (v.2 w)) ^ (k w).toNat * (v.2 w) ^ (-(k w)).toNat

private theorem hasTemperateGrowth_archMonomial (a : {w : InfinitePlace K // IsReal w} → ZMod 2)
    (k : {w : InfinitePlace K // IsComplex w} → ℤ) :
    Function.HasTemperateGrowth (archMonomial a k) := by
  refine htg_mul' (htg_finset_prod _ _ fun w _ => ?_) (htg_finset_prod _ _ fun w _ => ?_)
  · simpa using htg_pow_clm (realCoordCLM w) ((a w).val)
  · exact htg_mul' (by simpa using htg_pow_clm (cxConjCoordCLM w) (k w).toNat)
      (by simpa using htg_pow_clm (cxCoordCLM w) (-(k w)).toNat)

variable (K) in

private def archGaussTensor (a : {w : InfinitePlace K // IsReal w} → ZMod 2)
    (k : {w : InfinitePlace K // IsComplex w} → ℤ) : 𝓢(mixedSpace K, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (archMonomial a k) (archGaussBase K)

private theorem archGaussTensor_apply (a : {w : InfinitePlace K // IsReal w} → ZMod 2)
    (k : {w : InfinitePlace K // IsComplex w} → ℤ) (v : mixedSpace K) :
    archGaussTensor K a k v = archMonomial a k v * archGaussBase K v := by
  have h := SchwartzMap.smulLeftCLM_apply_apply (F := ℂ)
    (hasTemperateGrowth_archMonomial a k) (archGaussBase K) v
  simpa [smul_eq_mul, archGaussTensor] using h

private theorem cexp_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.exp (∑ i ∈ s, f i) = ∏ i ∈ s, Complex.exp (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.prod_cons, Complex.exp_add, ih]

private theorem finset_sum_neg {ι M : Type*} [AddCommGroup M] (s : Finset ι) (f : ι → M) :
    ∑ i ∈ s, -f i = -∑ i ∈ s, f i := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih => rw [Finset.sum_cons, Finset.sum_cons, ih, neg_add]

private theorem exp_neg_weighted_split (v : mixedSpace K) :
    Complex.exp (-((π : ℂ) * ((‖toEuclidGauss K v‖ : ℝ) : ℂ) ^ 2))
      = (∏ w : {w : InfinitePlace K // IsReal w},
          Complex.exp (-(π * ((v.1 w : ℝ) : ℂ) ^ 2))) *
        ∏ w : {w : InfinitePlace K // IsComplex w},
          Complex.exp (-(2 * π * ((‖v.2 w‖ : ℝ) : ℂ) ^ 2)) := by
  have h0 : -((π : ℂ) * ((‖toEuclidGauss K v‖ : ℝ) : ℂ) ^ 2)
      = ((-(π * ‖toEuclidGauss K v‖ ^ 2) : ℝ) : ℂ) := by push_cast; ring
  have h1 : (-(π * ‖toEuclidGauss K v‖ ^ 2) : ℝ)
      = (∑ w : {w : InfinitePlace K // IsReal w}, -(π * (v.1 w) ^ 2))
        + ∑ w : {w : InfinitePlace K // IsComplex w}, -(2 * π * ‖v.2 w‖ ^ 2) := by
    rw [norm_sq_toEuclidGauss, finset_sum_neg, finset_sum_neg, ← Finset.mul_sum,
      ← Finset.mul_sum]
    ring
  rw [h0, h1]
  push_cast
  rw [Complex.exp_add, cexp_sum, cexp_sum]

private theorem archGaussTensor_eq_prod (a : {w : InfinitePlace K // IsReal w} → ZMod 2)
    (k : {w : InfinitePlace K // IsComplex w} → ℤ) (v : mixedSpace K) :
    archGaussTensor K a k v
      = (∏ w : {w : InfinitePlace K // IsReal w}, realTestFun (a w) (v.1 w)) *
        ∏ w : {w : InfinitePlace K // IsComplex w}, complexTestFun (k w) (v.2 w) := by
  rw [archGaussTensor_apply, archGaussBase_apply, exp_neg_weighted_split]
  unfold archMonomial realTestFun complexTestFun
  simp only [Finset.prod_mul_distrib]
  ring

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end Fold_W2bArchTensor
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section Fold_WeilDomain1

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal NumberField.InfinitePlace P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"

noncomputable section

namespace M4aLocalCFT
namespace WeilDomain

variable (F : Type) [Field F] [NumberField F]

private theorem locallyCompactSpace_normOneIdeles : LocallyCompactSpace ↥(normOneIdeles F) :=
  (FujisakiC3.isClosed_normOneIdeles (F := F)).locallyCompactSpace

end M4aLocalCFT.WeilDomain
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section Prints

end Prints
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end Fold_WeilDomain1
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section Fold_Witness

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain MeasureTheory NumberField.AdelicFourier"

open scoped SchwartzMap

noncomputable section

namespace M4aTate
namespace Witness

section ClopenIndicator

variable {X : Type*} [TopologicalSpace X] {M : Type*} [Zero M]

private theorem isLocallyConstant_indicator_of_isClopen {U : Set X} (hU : IsClopen U) (c : M) :
    IsLocallyConstant (U.indicator fun _ => c) := by
  classical
  intro s
  have hpre : (U.indicator fun _ => c) ⁻¹' s
      = (if c ∈ s then U else ∅) ∪ (if (0 : M) ∈ s then Uᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ U <;> by_cases hcs : c ∈ s <;> by_cases h0s : (0 : M) ∈ s <;>
      simp [hx, hcs, h0s]
  rw [hpre]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact hU.2
    · exact isOpen_empty
  · split_ifs
    · exact hU.1.isOpen_compl
    · exact isOpen_empty

private theorem hasCompactSupport_indicator_of_isCompact {U : Set X} (hUc : IsCompact U)
    (hUcl : IsClosed U) (c : M) :
    HasCompactSupport (U.indicator fun _ => c) := by
  have hsupp : Function.support (U.indicator fun _ => c) ⊆ U := by
    intro x hx
    by_contra hxU
    exact hx (Set.indicator_of_notMem hxU _)
  have hsub : tsupport (U.indicator fun _ => c) ⊆ U := closure_minimal hsupp hUcl
  exact IsCompact.of_isClosed_subset hUc (isClosed_tsupport _) hsub

end ClopenIndicator
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

variable (F : Type*) [Field F] [NumberField F]

end M4aTate.Witness
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end Fold_Witness
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section Fold_W2cFinSide

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField MeasureTheory"

p2m_open "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.ShellSupport NumberField.AdelicBox NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal"

open Classical

noncomputable section

namespace M4aD3Glue

variable {F : Type} [Field F] [NumberField F]

private def finBox (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)) :
    Set (FiniteAdeleRing (𝓞 F) F) :=
  {y | (∀ v ∈ S, y v ∈ B v) ∧ ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

private theorem finBox_eq (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)) :
    finBox S B
      = (⋂ v ∈ S, (fun y : FiniteAdeleRing (𝓞 F) F => y v) ⁻¹' B v) ∩ integralOff S := by
  ext y
  simp only [finBox, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    integralOff]

private theorem isOpen_finBox {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)}
    (hB : ∀ v ∈ S, IsOpen (B v)) : IsOpen (finBox S B) := by
  rw [finBox_eq]
  refine IsOpen.inter ?_ (isOpen_integralOff S)
  exact isOpen_biInter_finset fun v hv =>
    (hB v hv).preimage (RestrictedProduct.continuous_eval v)

private theorem isClosed_integralOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsClosed (integralOff (F := F) S) := by
  have h : integralOff (F := F) S
      = ⋂ v, ⋂ (_ : v ∉ S), (fun y : FiniteAdeleRing (𝓞 F) F => y v) ⁻¹'
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext y
    simp only [integralOff, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
  rw [h]
  exact isClosed_iInter fun v => isClosed_iInter fun _ =>
    IsClosed.preimage (RestrictedProduct.continuous_eval v) (Valued.isClosed_valuationSubring _)

private theorem isClosed_finBox {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)}
    (hB : ∀ v ∈ S, IsClosed (B v)) : IsClosed (finBox S B) := by
  rw [finBox_eq]
  refine IsClosed.inter ?_ (isClosed_integralOff S)
  exact isClosed_biInter fun v hv =>
    IsClosed.preimage (RestrictedProduct.continuous_eval v) (hB v hv)

private theorem exists_subset_boxAt_of_isCompact (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F))
    {B : Set (v.adicCompletion F)} (hB : IsCompact B) : ∃ m : ℕ, B ⊆ boxAt ϖ v m := by
  have hcover : B ⊆ ⋃ m : ℕ, boxAt ϖ v m := fun y _ =>
    Set.mem_iUnion.mpr (mem_boxAt_exists ϖ v y)
  obtain ⟨t, ht⟩ := hB.elim_finite_subcover (boxAt ϖ v) (isOpen_boxAt ϖ v) hcover
  rcases t.eq_empty_or_nonempty with rfl | htne
  · refine ⟨0, fun y hy => ?_⟩
    have h := ht hy
    simp at h
  · refine ⟨t.max' htne, fun y hy => ?_⟩
    obtain ⟨m, hm, hym⟩ := Set.mem_iUnion₂.mp (ht hy)
    exact boxAt_mono ϖ v (t.le_max' m hm) hym

open scoped Classical in
private def scaleAdele (S : Finset (HeightOneSpectrum (𝓞 F))) (ϖ : Uniformizers F)
    (m : HeightOneSpectrum (𝓞 F) → ℕ) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ S then ((ϖ.ϖ v ^ m v : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1,
    Filter.eventually_cofinite.mpr (Set.Finite.subset S.finite_toSet fun v hv => by
      by_contra hvS
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      exact hv (show (if v ∈ S then ((ϖ.ϖ v ^ m v : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          else 1) ∈ v.adicCompletionIntegers F by rw [if_neg hvS']; exact one_mem _))⟩

open scoped Classical in
private def scaleAdeleInv (S : Finset (HeightOneSpectrum (𝓞 F))) (ϖ : Uniformizers F)
    (m : HeightOneSpectrum (𝓞 F) → ℕ) : FiniteAdeleRing (𝓞 F) F :=
  ⟨fun v => if v ∈ S then (((ϖ.ϖ v ^ m v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1,
    Filter.eventually_cofinite.mpr (Set.Finite.subset S.finite_toSet fun v hv => by
      by_contra hvS
      have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
      exact hv (show (if v ∈ S then (((ϖ.ϖ v ^ m v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
          else 1) ∈ v.adicCompletionIntegers F by rw [if_neg hvS']; exact one_mem _))⟩

open scoped Classical in
private theorem scaleAdeleInv_mul_scaleAdele (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : Uniformizers F) (m : HeightOneSpectrum (𝓞 F) → ℕ) :
    scaleAdeleInv S ϖ m * scaleAdele S ϖ m = 1 := by
  refine RestrictedProduct.ext _ _ fun v => ?_
  show (scaleAdeleInv S ϖ m) v * (scaleAdele S ϖ m) v = 1
  by_cases hv : v ∈ S
  · show (if v ∈ S then (((ϖ.ϖ v ^ m v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1)
        * (if v ∈ S then ((ϖ.ϖ v ^ m v : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1) = 1
    rw [if_pos hv, if_pos hv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  · show (if v ∈ S then (((ϖ.ϖ v ^ m v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1)
        * (if v ∈ S then ((ϖ.ϖ v ^ m v : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1) = 1
    rw [if_neg hv, if_neg hv, one_mul]

open scoped Classical in
private theorem finBox_subset_image (S : Finset (HeightOneSpectrum (𝓞 F))) (ϖ : Uniformizers F)
    (m : HeightOneSpectrum (𝓞 F) → ℕ)
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)}
    (hm : ∀ v ∈ S, B v ⊆ boxAt ϖ v (m v)) :
    finBox S B
      ⊆ (fun z => scaleAdeleInv S ϖ m * z) '' integralFiniteAdeles (𝓞 F) F := by
  intro y hy
  refine ⟨scaleAdele S ϖ m * y, fun v => ?_, ?_⟩
  · show (scaleAdele S ϖ m) v * y v ∈ v.adicCompletionIntegers F
    by_cases hv : v ∈ S
    · have hbox : y v ∈ boxAt ϖ v (m v) := hm v hv (hy.1 v hv)
      show (if v ∈ S then ((ϖ.ϖ v ^ m v : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1)
          * y v ∈ v.adicCompletionIntegers F
      rw [if_pos hv]
      exact hbox
    · show (if v ∈ S then ((ϖ.ϖ v ^ m v : (v.adicCompletion F)ˣ) : v.adicCompletion F) else 1)
          * y v ∈ v.adicCompletionIntegers F
      rw [if_neg hv, one_mul]
      exact hy.2 v hv
  · show scaleAdeleInv S ϖ m * (scaleAdele S ϖ m * y) = y
    rw [← mul_assoc, scaleAdeleInv_mul_scaleAdele, one_mul]

private theorem isCompact_finBox {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)} (ϖ : Uniformizers F)
    (hBcl : ∀ v ∈ S, IsClosed (B v)) (hBcp : ∀ v ∈ S, IsCompact (B v)) :
    IsCompact (finBox S B) := by
  classical
  choose! m hm using fun v (hv : v ∈ S) => exists_subset_boxAt_of_isCompact ϖ v (hBcp v hv)
  have himg : IsCompact ((fun z => scaleAdeleInv S ϖ m * z) ''
      integralFiniteAdeles (𝓞 F) F) :=
    (isCompact_integralFiniteAdeles F).image (continuous_const_mul _)
  exact himg.of_isClosed_subset (isClosed_finBox hBcl) (finBox_subset_image S ϖ m hm)

private def finBoxIndicator (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)) :
    FiniteAdeleRing (𝓞 F) F → ℂ :=
  (finBox S B).indicator fun _ => 1

private theorem isLocallyConstant_finBoxIndicator {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)}
    (hBo : ∀ v ∈ S, IsOpen (B v)) (hBc : ∀ v ∈ S, IsClosed (B v)) :
    IsLocallyConstant (finBoxIndicator S B) :=
  M4aTate.Witness.isLocallyConstant_indicator_of_isClopen
    ⟨isClosed_finBox hBc, isOpen_finBox hBo⟩ 1

private theorem hasCompactSupport_finBoxIndicator {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)} (ϖ : Uniformizers F)
    (hBc : ∀ v ∈ S, IsClosed (B v)) (hBcp : ∀ v ∈ S, IsCompact (B v)) :
    HasCompactSupport (finBoxIndicator S B) :=
  M4aTate.Witness.hasCompactSupport_indicator_of_isCompact
    (isCompact_finBox ϖ hBc hBcp) (isClosed_finBox hBc) 1

private def d3Witness (S : Finset (HeightOneSpectrum (𝓞 F)))
    (B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) : AdeleRing (𝓞 F) F → ℂ :=
  fun x => archGaussTensor F a k (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
    * finBoxIndicator S B x.2

private theorem d3Witness_mem_pureTensorSet {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)} (ϖ : Uniformizers F)
    (hBo : ∀ v ∈ S, IsOpen (B v)) (hBc : ∀ v ∈ S, IsClosed (B v))
    (hBcp : ∀ v ∈ S, IsCompact (B v))
    (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) :
    d3Witness S B a k ∈ NumberField.AdelicFourier.pureTensorSet F :=
  NumberField.AdelicFourier.tensor_mem_pureTensorSet (archGaussTensor F a k)
    (finBoxIndicator S B) (isLocallyConstant_finBoxIndicator hBo hBc)
    (hasCompactSupport_finBoxIndicator ϖ hBc hBcp)

private theorem d3Witness_mem_schwartzBruhat {S : Finset (HeightOneSpectrum (𝓞 F))}
    {B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)} (ϖ : Uniformizers F)
    (hBo : ∀ v ∈ S, IsOpen (B v)) (hBc : ∀ v ∈ S, IsClosed (B v))
    (hBcp : ∀ v ∈ S, IsCompact (B v))
    (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) :
    d3Witness S B a k ∈ NumberField.AdelicFourier.schwartzBruhat F :=
  NumberField.AdelicFourier.mem_schwartzBruhat_of_mem_pureTensorSet
    (d3Witness_mem_pureTensorSet ϖ hBo hBc hBcp a k)

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end Fold_W2cFinSide
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma1b

namespace M4aD3Glue

private theorem circleHom_eq_exp (u : ℝ → Circle) (hadd : ∀ a b : ℝ, u (a + b) = u a * u b)
    (hc : Continuous u) :
    ∃ τ : ℝ, ∀ t : ℝ, (u t : ℂ) = Complex.exp (Complex.I * (τ * t)) := by
  set v : ℝ → ℂ := fun t => ((u t : Circle) : ℂ) with hv
  have hvc : Continuous v := continuous_subtype_val.comp hc
  have hvmul : ∀ a b : ℝ, v (a + b) = v a * v b := by
    intro a b
    simp only [hv]
    rw [hadd a b]
    exact Circle.coe_mul _ _
  have hvnorm : ∀ t : ℝ, ‖v t‖ = 1 := fun t => Circle.norm_coe (u t)
  have hvne : ∀ t : ℝ, v t ≠ 0 := fun t => Circle.coe_ne_zero (u t)
  have hv0 : v 0 = 1 := by
    have h := hvmul 0 0
    rw [add_zero] at h
    exact (mul_left_cancel₀ (hvne 0) (by rw [mul_one, ← h])).symm
  set F : ℝ → ℂ := fun x => ∫ t in (0:ℝ)..x, v t with hF
  have hFint : ∀ a b : ℝ, IntervalIntegrable v MeasureTheory.volume a b := fun a b =>
    hvc.intervalIntegrable a b
  have hFderiv : ∀ x : ℝ, HasDerivAt F (v x) x := by
    intro x
    exact intervalIntegral.integral_hasDerivAt_right (hFint 0 x)
      (hvc.stronglyMeasurableAtFilter _ _) hvc.continuousAt
  have hF0 : F 0 = 0 := intervalIntegral.integral_same
  obtain ⟨δ, hFδ⟩ : ∃ δ : ℝ, F δ ≠ 0 := by
    have h0 : HasDerivAt F 1 0 := by
      have := hFderiv 0
      rw [hv0] at this
      exact this
    have hs := hasDerivAt_iff_tendsto_slope.mp h0
    have hne : ∀ᶠ x in nhdsWithin 0 {(0:ℝ)}ᶜ, slope F 0 x ≠ 0 :=
      hs.eventually_ne one_ne_zero
    obtain ⟨δ, hδ2⟩ := hne.exists
    refine ⟨δ, fun h0' => hδ2 ?_⟩
    simp [slope, h0', hF0]
  have hkey : ∀ x : ℝ, v x * F δ = F (x + δ) - F x := by
    intro x
    have hadj : F x + (∫ t in x..(x + δ), v t) = F (x + δ) :=
      intervalIntegral.integral_add_adjacent_intervals (hFint 0 x) (hFint x (x + δ))
    have hshift : (∫ t in (0:ℝ)..δ, v (t + x)) = ∫ t in x..(x + δ), v t := by
      have h := intervalIntegral.integral_comp_add_right (a := (0:ℝ)) (b := δ) v x
      rw [h, zero_add, add_comm δ x]
    have hmulstep : (∫ t in (0:ℝ)..δ, v (t + x)) = v x * F δ := by
      have hpt : ∀ t : ℝ, v (t + x) = v x * v t := by
        intro t
        rw [add_comm, hvmul]
      simp only [hpt]
      rw [intervalIntegral.integral_const_mul]
    rw [← hmulstep, hshift, ← hadj]
    ring
  set c : ℂ := (v δ - 1) / F δ with hcdef
  have hvderiv : ∀ x : ℝ, HasDerivAt v (c * v x) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => F (y + δ)) (v (x + δ)) x := by
      simpa using (hFderiv (x + δ)).comp_add_const x δ
    have h2 : HasDerivAt (fun y : ℝ => (F (y + δ) - F y) / F δ)
        ((v (x + δ) - v x) / F δ) x := (h1.sub (hFderiv x)).div_const _
    have h3 : (fun y : ℝ => (F (y + δ) - F y) / F δ) = v := by
      funext y
      rw [eq_comm, eq_div_iff hFδ]
      exact hkey y
    rw [h3] at h2
    convert h2 using 1
    rw [hcdef, hvmul x δ]
    field_simp [hFδ]
  have hconst : ∀ x : ℝ, v x = Complex.exp (c * (x : ℂ)) := by
    have hg : ∀ y : ℝ, HasDerivAt (fun z : ℝ => v z * Complex.exp (-c * (z : ℂ))) (0 : ℂ) y := by
      intro y
      have hlin : HasDerivAt (fun z : ℝ => -c * (z : ℂ)) (-c) y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul (-c)
      have he : HasDerivAt (fun z : ℝ => Complex.exp (-c * (z : ℂ)))
          (Complex.exp (-c * (y : ℂ)) * -c) y := by simpa using hlin.cexp
      have hprod := (hvderiv y).mul he
      have hfeq : (fun z : ℝ => v z * Complex.exp (-c * (z : ℂ)))
          = v * fun z : ℝ => Complex.exp (-c * (z : ℂ)) := rfl
      rw [hfeq]
      convert hprod using 1
      all_goals first | rfl | ring
    have hdiff : Differentiable ℝ (fun z : ℝ => v z * Complex.exp (-c * (z : ℂ))) :=
      fun y => (hg y).differentiableAt
    have hz : ∀ y : ℝ, deriv (fun z : ℝ => v z * Complex.exp (-c * (z : ℂ))) y = 0 :=
      fun y => (hg y).deriv
    intro x
    have hcx := is_const_of_deriv_eq_zero hdiff hz x 0
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hv0] at hcx
    rw [neg_mul, Complex.exp_neg] at hcx
    exact (mul_inv_eq_one₀ (Complex.exp_ne_zero _)).mp hcx
  have hre : c.re = 0 := by
    have h1 := hvnorm 1
    rw [hconst 1, Complex.norm_exp] at h1
    have h2 := (Real.exp_eq_one_iff _).mp h1
    simpa using h2
  refine ⟨c.im, fun t => ?_⟩
  have hct : c = Complex.I * (c.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  show v t = _
  rw [hconst t]
  congr 1
  conv_lhs => rw [hct]
  ring

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma1b
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma1c

namespace M4aD3Glue

private theorem realUnits_char_classification_of_gamma1b
    (γ1b : ∀ (u : ℝ → Circle), (∀ a b : ℝ, u (a + b) = u a * u b) → Continuous u →
      ∃ τ : ℝ, ∀ t : ℝ, (u t : ℂ) = Complex.exp (Complex.I * (τ * t)))
    (χ : ℝˣ →* ℂˣ)
    (hc : Continuous χ) (hu : ∀ x : ℝˣ, ‖((χ x : ℂˣ) : ℂ)‖ = 1) :
    ∃ (ε : Bool) (τ : ℝ), ∀ x : ℝˣ,
      ((χ x : ℂˣ) : ℂ)
        = (if ε then (Real.sign (x : ℝ) : ℂ) else 1)
          * Complex.exp (Complex.I * (τ * Real.log |(x : ℝ)|)) := by
  set P : ℝ → ℝˣ := fun t => Units.mk0 (Real.exp t) (Real.exp_ne_zero t) with hP
  have hPadd : ∀ a b : ℝ, P (a + b) = P a * P b := by
    intro a b
    apply Units.ext
    simp [hP, Real.exp_add]
  have hPcont : Continuous P := by
    rw [Units.continuous_iff]
    constructor
    · exact Real.continuous_exp.congr fun t => by simp [hP]
    · exact (Real.continuous_exp.comp continuous_neg).congr fun t => by
        simp [hP, Real.exp_neg]
  set u : ℝ → Circle := fun t =>
    ⟨((χ (P t) : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu (P t)]⟩ with hudef
  have huadd : ∀ a b : ℝ, u (a + b) = u a * u b := by
    intro a b
    apply Subtype.ext
    rw [Circle.coe_mul]
    simp only [hudef]
    rw [hPadd, map_mul]
    exact Units.val_mul _ _
  have hucont : Continuous u := by
    apply Continuous.subtype_mk
    have h1 : Continuous fun t : ℝ => χ (P t) := hc.comp hPcont
    exact (Units.continuous_iff.mp h1).1
  obtain ⟨τ, hτ⟩ := γ1b u huadd hucont
  have hpos : ∀ x : ℝˣ, 0 < (x : ℝ) →
      ((χ x : ℂˣ) : ℂ) = Complex.exp (Complex.I * (τ * Real.log |(x : ℝ)|)) := by
    intro x hx
    have hxP : x = P (Real.log (x : ℝ)) := by
      apply Units.ext
      simp [hP, Real.exp_log hx]
    rw [hxP]
    have habs : |((P (Real.log (x : ℝ)) : ℝˣ) : ℝ)| = Real.exp (Real.log (x : ℝ)) := by
      simp [hP, abs_of_pos (Real.exp_pos _)]
    rw [habs, Real.log_exp]
    simpa [hudef] using hτ (Real.log (x : ℝ))
  have hν : ((χ (-1 : ℝˣ) : ℂˣ) : ℂ) = 1 ∨ ((χ (-1 : ℝˣ) : ℂˣ) : ℂ) = -1 := by
    have hm : (-1 : ℝˣ) * (-1 : ℝˣ) = 1 := by
      apply Units.ext
      simp
    have h2 : ((χ (-1 : ℝˣ) : ℂˣ) : ℂ) * ((χ (-1 : ℝˣ) : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, ← map_mul, hm, map_one, Units.val_one]
    exact mul_self_eq_one_iff.mp h2
  have hnegdec : ∀ x : ℝˣ, (x : ℝ) < 0 → x = (-1 : ℝˣ) * P (Real.log |(x : ℝ)|) := by
    intro x hx
    apply Units.ext
    have habs : (0 : ℝ) < |(x : ℝ)| := abs_pos.mpr (Units.ne_zero x)
    rw [Units.val_mul]
    simp only [hP, Units.val_mk0]
    rw [Real.exp_log habs, abs_of_neg hx]
    simp
  have hχneg : ∀ x : ℝˣ, (x : ℝ) < 0 →
      ((χ x : ℂˣ) : ℂ) = ((χ (-1 : ℝˣ) : ℂˣ) : ℂ)
        * Complex.exp (Complex.I * (τ * Real.log |(x : ℝ)|)) := by
    intro x hx
    have hPpos : (0 : ℝ) < ((P (Real.log |(x : ℝ)|) : ℝˣ) : ℝ) := by
      simp [hP, Real.exp_pos]
    have habs2 : |((P (Real.log |(x : ℝ)|) : ℝˣ) : ℝ)| = |(x : ℝ)| := by
      simp only [hP, Units.val_mk0]
      rw [abs_of_pos (Real.exp_pos _), Real.exp_log (abs_pos.mpr (Units.ne_zero x))]
    have hPv := hpos _ hPpos
    rw [habs2] at hPv
    calc ((χ x : ℂˣ) : ℂ)
        = ((χ ((-1 : ℝˣ) * P (Real.log |(x : ℝ)|)) : ℂˣ) : ℂ) := by
          rw [← hnegdec x hx]
      _ = ((χ (-1 : ℝˣ) : ℂˣ) : ℂ) * ((χ (P (Real.log |(x : ℝ)|)) : ℂˣ) : ℂ) := by
          rw [map_mul, Units.val_mul]
      _ = ((χ (-1 : ℝˣ) : ℂˣ) : ℂ)
          * Complex.exp (Complex.I * (τ * Real.log |(x : ℝ)|)) := by
          rw [hPv]
  rcases hν with h1 | h1
  · refine ⟨false, τ, fun x => ?_⟩
    rcases lt_or_gt_of_ne (Units.ne_zero x : (x : ℝ) ≠ 0) with hx | hx
    · rw [hχneg x hx, h1]
      simp
    · rw [hpos x hx]
      simp
  · refine ⟨true, τ, fun x => ?_⟩
    rcases lt_or_gt_of_ne (Units.ne_zero x : (x : ℝ) ≠ 0) with hx | hx
    · rw [hχneg x hx, h1, Real.sign_of_neg hx]
      simp
    · rw [hpos x hx, Real.sign_of_pos hx]
      simp

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma1c
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma1d

namespace M4aD3Glue

private theorem complexUnits_char_classification_of_gamma1b
    (γ1b : ∀ (u : ℝ → Circle), (∀ a b : ℝ, u (a + b) = u a * u b) → Continuous u →
      ∃ τ : ℝ, ∀ t : ℝ, (u t : ℂ) = Complex.exp (Complex.I * (τ * t)))
    (χ : ℂˣ →* ℂˣ)
    (hc : Continuous χ) (hu : ∀ z : ℂˣ, ‖((χ z : ℂˣ) : ℂ)‖ = 1) :
    ∃ (k : ℤ) (τ : ℝ), ∀ z : ℂˣ,
      ((χ z : ℂˣ) : ℂ)
        = (((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k)
          * Complex.exp (Complex.I * (τ * Real.log ‖(z : ℂ)‖)) := by
  set Pc : ℝ → ℂˣ := fun t =>
    Units.mk0 ((Real.exp t : ℝ) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)) with hPc
  have hPcadd : ∀ a b : ℝ, Pc (a + b) = Pc a * Pc b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul]
    simp only [hPc, Units.val_mk0]
    push_cast [Real.exp_add]
    ring
  have hPccont : Continuous Pc := by
    rw [Units.continuous_iff]
    constructor
    · exact (Complex.continuous_ofReal.comp Real.continuous_exp).congr fun t => by simp [hPc]
    · exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_neg)).congr
        fun t => by simp [hPc, Real.exp_neg, Complex.ofReal_inv]
  set C1 : ℝ → ℂˣ := fun t =>
    Units.mk0 (Complex.exp ((t : ℂ) * Complex.I)) (Complex.exp_ne_zero _) with hC1
  have hC1add : ∀ a b : ℝ, C1 (a + b) = C1 a * C1 b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul]
    simp only [hC1, Units.val_mk0]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hC1cont : Continuous C1 := by
    have hinner : Continuous fun t : ℝ => (t : ℂ) * Complex.I :=
      Complex.continuous_ofReal.mul continuous_const
    rw [Units.continuous_iff]
    constructor
    · exact (Complex.continuous_exp.comp hinner).congr fun t => by simp [hC1]
    · exact (Complex.continuous_exp.comp hinner.neg).congr fun t => by
        simp [hC1, Complex.exp_neg]
  set u₁ : ℝ → Circle := fun t =>
    ⟨((χ (C1 t) : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu (C1 t)]⟩ with hu1def
  have hu1add : ∀ a b : ℝ, u₁ (a + b) = u₁ a * u₁ b := by
    intro a b
    apply Subtype.ext
    rw [Circle.coe_mul]
    simp only [hu1def]
    rw [hC1add, map_mul]
    exact Units.val_mul _ _
  have hu1cont : Continuous u₁ := by
    apply Continuous.subtype_mk
    have h1 : Continuous fun t : ℝ => χ (C1 t) := hc.comp hC1cont
    exact (Units.continuous_iff.mp h1).1
  set u₂ : ℝ → Circle := fun t =>
    ⟨((χ (Pc t) : ℂˣ) : ℂ), by simp [Submonoid.unitSphere, hu (Pc t)]⟩ with hu2def
  have hu2add : ∀ a b : ℝ, u₂ (a + b) = u₂ a * u₂ b := by
    intro a b
    apply Subtype.ext
    rw [Circle.coe_mul]
    simp only [hu2def]
    rw [hPcadd, map_mul]
    exact Units.val_mul _ _
  have hu2cont : Continuous u₂ := by
    apply Continuous.subtype_mk
    have h1 : Continuous fun t : ℝ => χ (Pc t) := hc.comp hPccont
    exact (Units.continuous_iff.mp h1).1
  obtain ⟨α, hα⟩ := γ1b u₁ hu1add hu1cont
  obtain ⟨τ, hτ2⟩ := γ1b u₂ hu2add hu2cont
  have h2πC : C1 (2 * Real.pi) = 1 := by
    apply Units.ext
    simp only [hC1, Units.val_mk0, Units.val_one]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I = 2 * (Real.pi : ℂ) * Complex.I by
      push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  have hper : Complex.exp (Complex.I * ((α : ℂ) * ((2 * Real.pi : ℝ) : ℂ))) = 1 := by
    have h : ((χ (C1 (2 * Real.pi)) : ℂˣ) : ℂ)
        = Complex.exp (Complex.I * ((α : ℂ) * ((2 * Real.pi : ℝ) : ℂ))) := hα (2 * Real.pi)
    rw [h2πC, map_one, Units.val_one] at h
    exact h.symm
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hper
  have hα_eq : α = (n : ℝ) := by
    have h3 : Complex.I * ((α : ℂ) * ((2 * Real.pi : ℝ) : ℂ))
        = Complex.I * ((n : ℂ) * (2 * (Real.pi : ℂ))) := by
      rw [hn]
      ring
    have h2 : ((α : ℂ) * ((2 * Real.pi : ℝ) : ℂ)) = (n : ℂ) * (2 * (Real.pi : ℂ)) :=
      mul_left_cancel₀ Complex.I_ne_zero h3
    have h5 : α * (2 * Real.pi) = (n : ℝ) * (2 * Real.pi) := by exact_mod_cast h2
    exact mul_right_cancel₀ (ne_of_gt Real.two_pi_pos) h5
  have hz_norm_pos : ∀ z : ℂˣ, (0 : ℝ) < ‖(z : ℂ)‖ := fun z =>
    norm_pos_iff.mpr (Units.ne_zero z)
  have hdec : ∀ z : ℂˣ, z = C1 (Complex.arg (z : ℂ)) * Pc (Real.log ‖(z : ℂ)‖) := by
    intro z
    apply Units.ext
    rw [Units.val_mul]
    simp only [hC1, hPc, Units.val_mk0]
    rw [Real.exp_log (hz_norm_pos z), mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm
  refine ⟨n, τ, fun z => ?_⟩
  have hsplit : ((χ z : ℂˣ) : ℂ)
      = ((χ (C1 (Complex.arg (z : ℂ))) : ℂˣ) : ℂ)
        * ((χ (Pc (Real.log ‖(z : ℂ)‖)) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, ← hdec z]
  have hC1val : ((χ (C1 (Complex.arg (z : ℂ))) : ℂˣ) : ℂ)
      = Complex.exp (Complex.I * (α * Complex.arg (z : ℂ))) := hα (Complex.arg (z : ℂ))
  have hPcval : ((χ (Pc (Real.log ‖(z : ℂ)‖)) : ℂˣ) : ℂ)
      = Complex.exp (Complex.I * (τ * Real.log ‖(z : ℂ)‖)) := hτ2 (Real.log ‖(z : ℂ)‖)
  have hfrac : (z : ℂ) / (‖(z : ℂ)‖ : ℂ)
      = Complex.exp ((Complex.arg (z : ℂ) : ℂ) * Complex.I) := by
    rw [div_eq_iff (by exact_mod_cast (hz_norm_pos z).ne' : ((‖(z : ℂ)‖ : ℝ) : ℂ) ≠ 0),
      mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I (z : ℂ)).symm
  have hpow : (((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ (n : ℤ))
      = Complex.exp ((n : ℂ) * ((Complex.arg (z : ℂ) : ℂ) * Complex.I)) := by
    rw [hfrac]
    exact (Complex.exp_int_mul _ n).symm
  rw [hsplit, hC1val, hPcval, hpow]
  congr 1
  rw [hα_eq]
  push_cast
  ring

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma1d
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma2RHelp

open MeasureTheory Set LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped Real

namespace M4aD3Glue

private theorem integral_comp_abs_cx {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

private theorem exp_I_mul_log {τ t : ℝ} (ht : 0 < t) :
    Complex.exp (Complex.I * (τ * Real.log t)) = (t : ℂ) ^ (Complex.I * τ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
  rw [← Complex.ofReal_log ht.le]
  ring_nf

private theorem mellin_gaussian {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z
      = (2 : ℂ)⁻¹ * (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2) := by
  have h1 : (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ))
      = fun t : ℝ => (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) (t ^ (2 : ℝ)) := by
    funext t
    have hp : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t 2]
      norm_num
    rw [hp]
  have h2 := mellin_comp_rpow (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) z (2 : ℝ)
  have h3 := mellin_comp_mul_left (fun u : ℝ => (Real.exp (-u) : ℂ)) (z / 2) Real.pi_pos
  have h4 : (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ))
      = fun u : ℝ => (fun v : ℝ => (Real.exp (-v) : ℂ)) (Real.pi * u) := by
    funext u; rfl
  have h5 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    have h6 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2)
        = Complex.GammaIntegral (z / 2) := by
      rw [Complex.GammaIntegral_eq_mellin]
    rw [h6, ← Complex.Gamma_eq_integral (by simpa using hz)]
  have hcast : z / ((2 : ℝ) : ℂ) = z / 2 := by norm_num
  rw [h1, h2, hcast, h4, h3, h5]
  rw [Complex.real_smul, smul_eq_mul]
  have habs : |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [habs]
  push_cast
  ring

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma2RHelp
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma2REval

open MeasureTheory Set LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped Real

namespace M4aD3Glue

private theorem integral_comp_abs_cx' {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Ioi 0, f |x| = ∫ (x : ℝ) in Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Iic 0, f |x|) + ∫ x in Ioi 0, f |x| := by
        rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

private theorem exp_I_mul_log' {τ t : ℝ} (ht : 0 < t) :
    Complex.exp (Complex.I * (τ * Real.log t)) = (t : ℂ) ^ (Complex.I * τ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
  rw [← Complex.ofReal_log ht.le]
  ring_nf

private theorem mellin_gaussian' {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z
      = (2 : ℂ)⁻¹ * (Real.pi : ℂ) ^ (-(z / 2)) * Complex.Gamma (z / 2) := by
  have h1 : (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ))
      = fun t : ℝ => (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) (t ^ (2 : ℝ)) := by
    funext t
    have hp : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t 2]
      norm_num
    rw [hp]
  have h2 := mellin_comp_rpow (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ)) z (2 : ℝ)
  have h3 := mellin_comp_mul_left (fun u : ℝ => (Real.exp (-u) : ℂ)) (z / 2) Real.pi_pos
  have h4 : (fun u : ℝ => (Real.exp (-(Real.pi * u)) : ℂ))
      = fun u : ℝ => (fun v : ℝ => (Real.exp (-v) : ℂ)) (Real.pi * u) := by
    funext u; rfl
  have h5 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    have h6 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2)
        = Complex.GammaIntegral (z / 2) := by
      rw [Complex.GammaIntegral_eq_mellin]
    rw [h6, ← Complex.Gamma_eq_integral (by simpa using hz)]
  have hcast : z / ((2 : ℝ) : ℂ) = z / 2 := by norm_num
  rw [h1, h2, hcast, h4, h3, h5]
  rw [Complex.real_smul, smul_eq_mul]
  have habs : |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [habs]
  push_cast
  ring

private theorem realZeta_classified_eval (ε : Bool) (τ : ℝ) (χ : ℝˣ →* ℂˣ)
    (hχ : ∀ u : ℝˣ, ((χ u : ℂˣ) : ℂ)
      = (if ε then (Real.sign (u : ℝ) : ℂ) else 1)
        * Complex.exp (Complex.I * (τ * Real.log |(u : ℝ)|)))
    (s : ℂ) (hs : 0 < (s + Complex.I * τ + (if ε then 1 else 0)).re) :
    realZeta volume (realTestFun (if ε then 1 else 0)) χ s
      = Complex.Gammaℝ (s + Complex.I * τ + (if ε then 1 else 0)) := by
  set z : ℂ := s + Complex.I * τ + (if ε then 1 else 0) with hzdef
  set a : ZMod 2 := if ε then 1 else 0 with hadef
  have havN : a.val = if ε then 1 else 0 := by
    cases ε <;> simp [hadef] <;> decide
  have hav : (a.val : ℂ) = if ε then 1 else 0 := by
    rw [havN]; cases ε <;> simp
  have hpt : ∀ x : ℝ, x ≠ 0 →
      realTestFun a x * charExt χ x * ((‖x‖ : ℂ) ^ (s - 1))
        = (((|x| : ℝ) : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
    intro x hx
    have habs0 : (0 : ℝ) < |x| := abs_pos.mpr hx
    have habsC : ((|x| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habs0.ne'
    rw [charExt_of_ne_zero χ hx, hχ (Units.mk0 x hx)]
    simp only [realTestFun, Units.val_mk0]
    have hexp : Complex.exp (-(↑Real.pi * (x : ℂ) ^ 2))
        = (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
      rw [Complex.ofReal_exp]
      push_cast [sq_abs]
      ring_nf
    have hpow : ((x : ℂ) ^ (a.val : ℕ)) * (if ε then ((Real.sign x : ℝ) : ℂ) else 1)
        = ((|x| : ℝ) : ℂ) ^ (a.val : ℕ) := by
      cases ε
      · simp [hadef]
      · simp only [hadef, if_true, Bool.cond_true]
        have h1 : ((1 : ZMod 2)).val = 1 := by decide
        rw [h1]
        rcases lt_or_gt_of_ne hx with hneg | hpos
        · rw [Real.sign_of_neg hneg, abs_of_neg hneg]
          push_cast
          ring
        · rw [Real.sign_of_pos hpos, abs_of_pos hpos]
          push_cast
          ring
    have hIτ : Complex.exp (Complex.I * (τ * Real.log |x|))
        = ((|x| : ℝ) : ℂ) ^ (Complex.I * τ) := exp_I_mul_log' habs0
    have hnorm : ((‖x‖ : ℝ) : ℂ) = ((|x| : ℝ) : ℂ) := by
      norm_cast
    calc (↑x ^ a.val * Complex.exp (-(↑Real.pi * (x:ℂ) ^ 2)))
          * ((if ε then ((Real.sign x : ℝ) : ℂ) else 1)
              * Complex.exp (Complex.I * (τ * Real.log |↑(Units.mk0 x hx)|)))
          * ((‖x‖ : ℂ) ^ (s - 1))
        = (↑x ^ a.val * (if ε then ((Real.sign x : ℝ) : ℂ) else 1))
          * Complex.exp (Complex.I * (τ * Real.log |x|))
          * ((|x| : ℝ) : ℂ) ^ (s - 1)
          * Complex.exp (-(↑Real.pi * (x:ℂ) ^ 2)) := by
          rw [hnorm]
          simp only [Units.val_mk0]
          ring
      _ = (((|x| : ℝ) : ℂ) ^ (a.val : ℕ)) * (((|x| : ℝ) : ℂ) ^ (Complex.I * τ))
          * (((|x| : ℝ) : ℂ) ^ (s - 1)) * (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
          rw [hpow, hIτ, hexp]
      _ = ((|x| : ℝ) : ℂ) ^ (z - 1) * (Real.exp (-(Real.pi * |x| ^ 2)) : ℂ) := by
          rw [← Complex.cpow_natCast ((|x| : ℝ) : ℂ) a.val]
          rw [← Complex.cpow_add _ _ habsC, ← Complex.cpow_add _ _ habsC]
          congr 2
          rw [hav, hzdef]
          ring
  have h0ae : ∀ᵐ (x : ℝ) ∂volume, x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using Real.volume_singleton (a := 0)
  have hcongr : realZeta volume (realTestFun a) χ s
      = ∫ x : ℝ, (fun t : ℝ => ((t : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) |x| := by
    simp only [realZeta]
    refine integral_congr_ae (h0ae.mono fun x hx => ?_)
    exact hpt x hx
  rw [hadef] at hcongr
  rw [hcongr, integral_comp_abs_cx'
    (f := fun t : ℝ => ((t : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ))]
  have hmel : (∫ x in Ioi (0:ℝ),
        (fun t : ℝ => ((t : ℂ) ^ (z - 1)) * (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) x)
      = mellin (fun t : ℝ => (Real.exp (-(Real.pi * t ^ 2)) : ℂ)) z := by
    simp only [mellin, smul_eq_mul]
  rw [hmel, mellin_gaussian' hs]
  rw [Complex.Gammaℝ_def, neg_div]
  ring

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma2REval
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma2CEval

open Real Set MeasureTheory MeasureTheory.Measure
open LanglandsTunnell LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open scoped ENNReal

namespace M4aD3Glue

private theorem exp_I_mul_log₂ {τ t : ℝ} (ht : 0 < t) :
    Complex.exp (Complex.I * (τ * Real.log t)) = (t : ℂ) ^ (Complex.I * τ) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast ht.ne')]
  rw [← Complex.ofReal_log ht.le]
  ring_nf

private theorem mellin_gaussian₂ {z : ℂ} (hz : 0 < z.re) :
    mellin (fun t : ℝ => (Real.exp (-(2 * Real.pi * t ^ 2)) : ℂ)) z
      = (2 : ℂ)⁻¹ * (2 * (Real.pi : ℂ)) ^ (-(z / 2)) * Complex.Gamma (z / 2) := by
  have h1 : (fun t : ℝ => (Real.exp (-(2 * Real.pi * t ^ 2)) : ℂ))
      = fun t : ℝ => (fun u : ℝ => (Real.exp (-(2 * Real.pi * u)) : ℂ)) (t ^ (2 : ℝ)) := by
    funext t
    have hp : t ^ (2 : ℝ) = t ^ (2 : ℕ) := by
      rw [← Real.rpow_natCast t 2]
      norm_num
    rw [hp]
  have h2 := mellin_comp_rpow (fun u : ℝ => (Real.exp (-(2 * Real.pi * u)) : ℂ)) z (2 : ℝ)
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have h3 := mellin_comp_mul_left (fun u : ℝ => (Real.exp (-u) : ℂ)) (z / 2) h2pi
  have h4 : (fun u : ℝ => (Real.exp (-(2 * Real.pi * u)) : ℂ))
      = fun u : ℝ => (fun v : ℝ => (Real.exp (-v) : ℂ)) (2 * Real.pi * u) := by
    funext u; rfl
  have h5 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2) = Complex.Gamma (z / 2) := by
    have h6 : mellin (fun v : ℝ => (Real.exp (-v) : ℂ)) (z / 2)
        = Complex.GammaIntegral (z / 2) := by
      rw [Complex.GammaIntegral_eq_mellin]
    rw [h6, ← Complex.Gamma_eq_integral (by simpa using hz)]
  have hcast : z / ((2 : ℝ) : ℂ) = z / 2 := by norm_num
  rw [h1, h2, hcast, h4, h3, h5]
  rw [Complex.real_smul, smul_eq_mul]
  have habs : |(2 : ℝ)|⁻¹ = (2 : ℝ)⁻¹ := by norm_num
  rw [habs]
  push_cast
  ring

private theorem conj_pow_mul_pow_mul_phase_zpow {k : ℤ} {z : ℂ} (hz : z ≠ 0) :
    (starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat * ((z / ((‖z‖ : ℝ) : ℂ)) ^ k)
      = ((‖z‖ : ℝ) : ℂ) ^ k.natAbs := by
  have hr0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
  have hrC : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  by_cases hk : 0 ≤ k
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = (n : ℤ) := ⟨k.toNat, by omega⟩
    have e1 : ((n : ℤ)).toNat = n := by omega
    have e2 : (-(n : ℤ)).toNat = 0 := by omega
    have e3 : ((n : ℤ)).natAbs = n := by omega
    rw [e1, e2, e3, pow_zero, mul_one, zpow_natCast, ← mul_pow]
    congr 1
    rw [← mul_div_assoc, mul_comm (starRingEnd ℂ z) z, Complex.mul_conj']
    push_cast
    rw [pow_two, mul_div_assoc, div_self hrC, mul_one]
  · obtain ⟨n, rfl⟩ : ∃ n : ℕ, k = -((n : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    have e1 : ((-((n : ℤ) + 1))).toNat = 0 := by omega
    have e2 : ((-(-((n : ℤ) + 1)))).toNat = n + 1 := by omega
    have e3 : ((-((n : ℤ) + 1))).natAbs = n + 1 := by omega
    have e4 : (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
    rw [e1, e2, e3, pow_zero, one_mul, e4, zpow_neg, zpow_natCast]
    rw [← inv_pow, inv_div, ← mul_pow]
    congr 1
    rw [← mul_div_assoc, mul_comm z ((‖z‖ : ℝ) : ℂ), mul_div_assoc, div_self hz, mul_one]

private theorem complexZeta_classified_eval (k : ℤ) (τ : ℝ) (χ : ℂˣ →* ℂˣ)
    (hχ : ∀ z : ℂˣ, ((χ z : ℂˣ) : ℂ)
      = (((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k)
        * Complex.exp (Complex.I * (τ * Real.log ‖(z : ℂ)‖)))
    (s : ℂ) (hs : 0 < (s + (Complex.I * τ + (k.natAbs : ℂ)) / 2).re) :
    complexZeta ((2 : ℝ≥0∞) • volume) (complexTestFun k) χ s
      = (Real.pi : ℂ) * Complex.Gammaℂ (s + (Complex.I * τ + (k.natAbs : ℂ)) / 2) := by
  set ζ : ℂ := s + (Complex.I * τ + (k.natAbs : ℂ)) / 2 with hζ
  set w : ℂ := 2 * ζ with hw
  have hhalf : w / 2 = ζ := by rw [hw]; ring
  have hw_re : 0 < w.re := by
    rw [hw]
    have h2re : (2 * ζ).re = 2 * ζ.re := by
      simp [Complex.mul_re]
    rw [h2re]
    linarith [hs]
  have hpt : ∀ z : ℂ, z ≠ 0 →
      complexTestFun k z * charExt χ z * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2))
        = (((‖z‖ : ℝ) : ℂ) ^ (w - 2)) * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ) := by
    intro z hz
    have hr0 : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz
    have hrC : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have hexp : Complex.exp (-(2 * (Real.pi : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2))
        = (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ) := by
      rw [Complex.ofReal_exp]
      push_cast
      ring_nf
    have hIτ : Complex.exp (Complex.I * ((τ : ℝ) * Real.log ‖z‖))
        = ((‖z‖ : ℝ) : ℂ) ^ (Complex.I * (τ : ℂ)) := exp_I_mul_log₂ hr0
    have hphase := conj_pow_mul_pow_mul_phase_zpow (k := k) hz
    rw [charExt_of_ne_zero χ hz, hχ (Units.mk0 z hz)]
    simp only [complexTestFun, Units.val_mk0]
    calc (starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat
          * Complex.exp (-(2 * (Real.pi : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2))
          * (((z / ((‖z‖ : ℝ) : ℂ)) ^ k)
              * Complex.exp (Complex.I * ((τ : ℝ) * Real.log ‖z‖)))
          * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2))
        = ((starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat * ((z / ((‖z‖ : ℝ) : ℂ)) ^ k))
          * Complex.exp (Complex.I * ((τ : ℝ) * Real.log ‖z‖))
          * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2))
          * Complex.exp (-(2 * (Real.pi : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2)) := by
          ring
      _ = (((‖z‖ : ℝ) : ℂ) ^ k.natAbs) * (((‖z‖ : ℝ) : ℂ) ^ (Complex.I * (τ : ℂ)))
          * (((‖z‖ : ℝ) : ℂ) ^ ((2 : ℂ) * s - 2))
          * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ) := by
          rw [hphase, hIτ, hexp]
      _ = (((‖z‖ : ℝ) : ℂ) ^ (w - 2)) * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ) := by
          rw [← Complex.cpow_natCast (((‖z‖ : ℝ) : ℂ)) k.natAbs]
          rw [← Complex.cpow_add _ _ hrC, ← Complex.cpow_add _ _ hrC]
          have hexps : (k.natAbs : ℂ) + Complex.I * (τ : ℂ) + ((2 : ℂ) * s - 2) = w - 2 := by
            rw [hw, hζ]
            push_cast
            ring
          rw [hexps]
  have h0ae : ∀ᵐ (z : ℂ) ∂volume, z ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simpa using measure_singleton (0 : ℂ)
  simp only [complexZeta]
  rw [integral_smul_measure]
  simp only [ENNReal.toReal_ofNat]
  have hcongr : (∫ z : ℂ, complexTestFun k z * charExt χ z * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2)))
      = ∫ z : ℂ, (((‖z‖ : ℝ) : ℂ) ^ (w - 2)) * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ) := by
    refine integral_congr_ae (h0ae.mono fun z hz => ?_)
    exact hpt z hz
  rw [hcongr]
  have hpolar : (∫ z : ℂ, (((‖z‖ : ℝ) : ℂ) ^ (w - 2)) * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ))
      = ((2 * Real.pi : ℝ) : ℂ)
        * mellin (fun t : ℝ => (Real.exp (-(2 * Real.pi * t ^ 2)) : ℂ)) w := by
    calc ∫ z : ℂ, (((‖z‖ : ℝ) : ℂ) ^ (w - 2)) * (Real.exp (-(2 * Real.pi * ‖z‖ ^ 2)) : ℂ)
        = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
            (p.1 : ℂ) * (((|p.1| : ℝ) : ℂ) ^ (w - 2)
              * (Real.exp (-(2 * Real.pi * |p.1| ^ 2)) : ℂ)) := by
          rw [← Complex.integral_comp_polarCoord_symm, _root_.polarCoord_target]
          simp_rw [Complex.norm_polarCoord_symm, Complex.real_smul]
      _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * (((|r| : ℝ) : ℂ) ^ (w - 2)
            * (Real.exp (-(2 * Real.pi * |r| ^ 2)) : ℂ)))
            * ∫ _ in Ioo (-Real.pi) Real.pi, (1 : ℂ) := by
          rw [← setIntegral_prod_mul, volume_eq_prod]
          simp_rw [mul_one]
      _ = (∫ r in Ioi (0 : ℝ), (r : ℂ) * (((|r| : ℝ) : ℂ) ^ (w - 2)
            * (Real.exp (-(2 * Real.pi * |r| ^ 2)) : ℂ)))
            * ((2 * Real.pi : ℝ) : ℂ) := by
          congr 1
          simp_rw [integral_const, measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter,
            volume_real_Ioo_of_le (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_nonneg]),
            sub_neg_eq_add, ← two_mul, Complex.real_smul, mul_one]
      _ = ((2 * Real.pi : ℝ) : ℂ)
            * mellin (fun t : ℝ => (Real.exp (-(2 * Real.pi * t ^ 2)) : ℂ)) w := by
          rw [mul_comm]
          congr 1
          simp only [mellin, smul_eq_mul]
          refine setIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
          rw [Set.mem_Ioi] at hr
          have hrne : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
          rw [abs_of_pos hr]
          have h1 : ((r : ℝ) : ℂ) ^ (w - 1) = (r : ℂ) * ((r : ℝ) : ℂ) ^ (w - 2) := by
            rw [show w - 1 = 1 + (w - 2) by ring, Complex.cpow_add _ _ hrne, Complex.cpow_one]
          rw [h1]
          ring
  rw [hpolar, mellin_gaussian₂ hw_re, hhalf, Complex.Gammaℂ_def]
  rw [Complex.real_smul]
  push_cast
  ring

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma2CEval
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldGamma2aLegs

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion"
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal

noncomputable section

namespace M4aD3Glue

section Transport

variable {K L : Type*} [Field K] [Field L]
  [TopologicalSpace K] [IsTopologicalRing K] [LocallyCompactSpace K] [MeasurableSpace K]
  [TopologicalSpace L] [IsTopologicalRing L] [LocallyCompactSpace L] [MeasurableSpace L]

private theorem mulMeasure_map' (e : L ≃ᵐ K) (h0 : e 0 = 0)
    (hmod : ∀ y : L, modulus (e y) = modulus y) (μ : Measure L) :
    mulMeasure (Measure.map e μ) = Measure.map e (mulMeasure μ) := by
  have hpre : (e : L → K) ⁻¹' {0}ᶜ = ({0}ᶜ : Set L) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · intro h hx
      exact h (hx ▸ h0)
    · intro h he
      exact h (e.injective (he.trans h0.symm))
  unfold mulMeasure
  rw [MeasurableEquiv.restrict_map, hpre]
  set ν : Measure L := μ.restrict {0}ᶜ with hν
  ext A hA
  calc ((Measure.map e ν).withDensity fun x => ((modulus x : ℝ≥0∞))⁻¹) A
      = ∫⁻ x in A, ((modulus x : ℝ≥0∞))⁻¹ ∂(Measure.map e ν) := withDensity_apply _ hA
    _ = ∫⁻ x, ((modulus x : ℝ≥0∞))⁻¹ ∂(Measure.map e (ν.restrict ((e : L → K) ⁻¹' A))) := by
        rw [MeasurableEquiv.restrict_map]
    _ = ∫⁻ y, ((modulus (e y) : ℝ≥0∞))⁻¹ ∂(ν.restrict ((e : L → K) ⁻¹' A)) := by
        rw [lintegral_map_equiv]
    _ = ∫⁻ y, ((modulus y : ℝ≥0∞))⁻¹ ∂(ν.restrict ((e : L → K) ⁻¹' A)) := by
        refine lintegral_congr fun y => ?_
        rw [hmod]
    _ = (ν.withDensity fun y => ((modulus y : ℝ≥0∞))⁻¹) ((e : L → K) ⁻¹' A) :=
        (withDensity_apply _ (hA.preimage e.measurable)).symm
    _ = (Measure.map e (ν.withDensity fun y => ((modulus y : ℝ≥0∞))⁻¹)) A :=
        (MeasurableEquiv.map_apply e A).symm

private theorem localZeta_map' (e : L ≃ᵐ K) (h0 : e 0 = 0)
    (hmod : ∀ y : L, modulus (e y) = modulus y)
    (μ : Measure L) (f : K → ℂ) (χK : Kˣ →* ℂˣ) (χL : Lˣ →* ℂˣ)
    (hχ : ∀ y : L, charExt χK (e y) = charExt χL y) (s : ℂ) :
    localZeta (Measure.map e μ) f χK s = localZeta μ (fun y => f (e y)) χL s := by
  unfold localZeta
  rw [mulMeasure_map' e h0 hmod, integral_map_equiv]
  congr 1
  funext y
  rw [hχ y, hmod y]

end Transport
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

variable {F : Type} [Field F] [NumberField F]
variable {w : InfinitePlace F} [MeasurableSpace w.Completion] [BorelSpace w.Completion]

private def realPlaceMeasurableEquiv (hv : w.IsReal) : ℝ ≃ᵐ w.Completion :=
  Homeomorph.toMeasurableEquiv
    { toEquiv := (ringEquivRealOfIsReal hv).symm.toEquiv
      continuous_toFun := by
        have h : Isometry (isometryEquivRealOfIsReal hv).symm :=
          (isometryEquivRealOfIsReal hv).symm.isometry
        exact h.continuous
      continuous_invFun := (isometry_extensionEmbeddingOfIsReal hv).continuous }

@[scoped simp] private theorem realPlaceMeasurableEquiv_apply (hv : w.IsReal) (y : ℝ) :
    realPlaceMeasurableEquiv hv y = (ringEquivRealOfIsReal hv).symm y := rfl

private theorem realPlace_h0 (hv : w.IsReal) : realPlaceMeasurableEquiv hv 0 = 0 := by
  rw [realPlaceMeasurableEquiv_apply]
  exact map_zero _

private theorem realPlace_ne_zero (hv : w.IsReal) {y : ℝ} (hy : y ≠ 0) :
    (ringEquivRealOfIsReal hv).symm y ≠ 0 := fun h =>
  hy (by simpa using congrArg (ringEquivRealOfIsReal hv) h)

private theorem realPlace_hmod (hv : w.IsReal) (y : ℝ) :
    modulus (realPlaceMeasurableEquiv hv y) = modulus y := by
  rw [realPlaceMeasurableEquiv_apply]
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, modulus_zero, modulus_zero]
  · have hy' := realPlace_ne_zero hv hy
    rw [modulus_of_ne_zero hy', modulus_of_ne_zero hy]
    rw [M4aLocalCFT.ArchMulHaarCompletion.distribHaarChar_completion_of_isReal w hv, pow_one]
    rw [M4aLocalCFT.ArchMulHaarReal.distribHaarChar_real]
    have hn := M4aLocalCFT.ArchMulHaarCompletion.nnnorm_ringEquivReal hv
      ((ringEquivRealOfIsReal hv).symm y)
    simp only [RingEquiv.apply_symm_apply] at hn
    simp only [Units.val_mk0]
    exact hn.symm

private theorem realPlace_hχ (hv : w.IsReal) (χK : (w.Completion)ˣ →* ℂˣ) (y : ℝ) :
    charExt χK (realPlaceMeasurableEquiv hv y)
      = charExt (χK.comp (Units.map
          ((ringEquivRealOfIsReal hv).symm : ℝ →+* w.Completion).toMonoidHom)) y := by
  rw [realPlaceMeasurableEquiv_apply]
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, charExt_zero, charExt_zero]
  · have hy' := realPlace_ne_zero hv hy
    rw [charExt_of_ne_zero _ hy', charExt_of_ne_zero _ hy]
    have harg : Units.mk0 ((ringEquivRealOfIsReal hv).symm y) hy'
        = Units.map ((ringEquivRealOfIsReal hv).symm : ℝ →+* w.Completion).toMonoidHom
            (Units.mk0 y hy) := by
      ext
      simp
    rw [harg]
    rfl

private theorem localZeta_realPlace (hv : w.IsReal) (μ : Measure ℝ) (f : w.Completion → ℂ)
    (χK : (w.Completion)ˣ →* ℂˣ) (s : ℂ) :
    localZeta (Measure.map (realPlaceMeasurableEquiv hv) μ) f χK s
      = localZeta μ (fun y => f (realPlaceMeasurableEquiv hv y))
          (χK.comp (Units.map
            ((ringEquivRealOfIsReal hv).symm : ℝ →+* w.Completion).toMonoidHom)) s :=
  localZeta_map' (realPlaceMeasurableEquiv hv) (realPlace_h0 hv) (realPlace_hmod hv) μ f χK _
    (realPlace_hχ hv χK) s

private def complexPlaceMeasurableEquiv (hv : w.IsComplex) : ℂ ≃ᵐ w.Completion :=
  Homeomorph.toMeasurableEquiv
    { toEquiv := (ringEquivComplexOfIsComplex hv).symm.toEquiv
      continuous_toFun := by
        have h : Isometry (isometryEquivComplexOfIsComplex hv).symm :=
          (isometryEquivComplexOfIsComplex hv).symm.isometry
        exact h.continuous
      continuous_invFun := (isometry_extensionEmbedding w).continuous }

@[scoped simp] private theorem complexPlaceMeasurableEquiv_apply (hv : w.IsComplex) (y : ℂ) :
    complexPlaceMeasurableEquiv hv y = (ringEquivComplexOfIsComplex hv).symm y := rfl

private theorem complexPlace_h0 (hv : w.IsComplex) : complexPlaceMeasurableEquiv hv 0 = 0 := by
  rw [complexPlaceMeasurableEquiv_apply]
  exact map_zero _

private theorem complexPlace_ne_zero (hv : w.IsComplex) {y : ℂ} (hy : y ≠ 0) :
    (ringEquivComplexOfIsComplex hv).symm y ≠ 0 := fun h =>
  hy (by simpa using congrArg (ringEquivComplexOfIsComplex hv) h)

private theorem complexPlace_hmod (hv : w.IsComplex) (y : ℂ) :
    modulus (complexPlaceMeasurableEquiv hv y) = modulus y := by
  rw [complexPlaceMeasurableEquiv_apply]
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, modulus_zero, modulus_zero]
  · have hy' := complexPlace_ne_zero hv hy
    rw [modulus_of_ne_zero hy', modulus_of_ne_zero hy]
    rw [M4aLocalCFT.ArchMulHaarCompletion.distribHaarChar_completion_of_isComplex w hv]
    rw [M4aLocalCFT.ArchMulHaarComplex.distribHaarChar_complex]
    have hn := M4aLocalCFT.ArchMulHaarCompletion.nnnorm_ringEquivComplex hv
      ((ringEquivComplexOfIsComplex hv).symm y)
    simp only [RingEquiv.apply_symm_apply] at hn
    simp only [Units.val_mk0]
    rw [hn]

private theorem complexPlace_hχ (hv : w.IsComplex) (χK : (w.Completion)ˣ →* ℂˣ) (y : ℂ) :
    charExt χK (complexPlaceMeasurableEquiv hv y)
      = charExt (χK.comp (Units.map
          ((ringEquivComplexOfIsComplex hv).symm : ℂ →+* w.Completion).toMonoidHom)) y := by
  rw [complexPlaceMeasurableEquiv_apply]
  by_cases hy : y = 0
  · subst hy
    rw [map_zero, charExt_zero, charExt_zero]
  · have hy' := complexPlace_ne_zero hv hy
    rw [charExt_of_ne_zero _ hy', charExt_of_ne_zero _ hy]
    have harg : Units.mk0 ((ringEquivComplexOfIsComplex hv).symm y) hy'
        = Units.map ((ringEquivComplexOfIsComplex hv).symm : ℂ →+* w.Completion).toMonoidHom
            (Units.mk0 y hy) := by
      ext
      simp
    rw [harg]
    rfl

private theorem localZeta_complexPlace (hv : w.IsComplex) (μ : Measure ℂ) (f : w.Completion → ℂ)
    (χK : (w.Completion)ˣ →* ℂˣ) (s : ℂ) :
    localZeta (Measure.map (complexPlaceMeasurableEquiv hv) μ) f χK s
      = localZeta μ (fun y => f (complexPlaceMeasurableEquiv hv y))
          (χK.comp (Units.map
            ((ringEquivComplexOfIsComplex hv).symm : ℂ →+* w.Completion).toMonoidHom)) s :=
  localZeta_map' (complexPlaceMeasurableEquiv hv) (complexPlace_h0 hv) (complexPlace_hmod hv) μ f
    χK _ (complexPlace_hχ hv χK) s

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"
end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldGamma2aLegs
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldAlphaKappa

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField AutomorphicForm IsDedekindDomain Topology"

namespace M4aD3Glue

private lemma sq_dist_ge {w : ℂ} (hw : ‖w‖ = 1) (hlt : ‖w - 1‖ < 1) :
    Real.sqrt 3 * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have hfact : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have hpar := parallelogram_law_with_norm ℝ w 1
  have h3 : Real.sqrt 3 ≤ ‖w + 1‖ := by
    have h3' : 3 ≤ ‖w + 1‖ * ‖w + 1‖ := by
      have hn1 : ‖(1 : ℂ)‖ = 1 := norm_one
      nlinarith [norm_nonneg (w - 1), norm_nonneg (w + 1)]
    have : Real.sqrt 3 ≤ Real.sqrt (‖w + 1‖ * ‖w + 1‖) := Real.sqrt_le_sqrt h3'
    rwa [Real.sqrt_mul_self (norm_nonneg _)] at this
  rw [hfact, norm_mul]
  exact mul_le_mul_of_nonneg_right h3 (norm_nonneg _)

private lemma escape_radial {z : ℂˣ} (hgt : 1 < ‖(z : ℂ)‖) :
    ∃ n : ℤ, 1 ≤ ‖((z ^ n : ℂˣ) : ℂ) - 1‖ := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hgt
  refine ⟨(n : ℤ), ?_⟩
  have hz : ((z ^ (n : ℤ) : ℂˣ) : ℂ) = (z : ℂ) ^ n := by
    rw [zpow_natCast]; exact Units.val_pow_eq_pow_val z n
  have h1 : (1 : ℝ) ≤ ‖(z : ℂ)‖ ^ n - 1 := by
    have : (2 : ℝ) < ‖(z : ℂ)‖ ^ n := hn
    linarith
  calc (1 : ℝ) ≤ ‖(z : ℂ)‖ ^ n - 1 := h1
    _ = ‖(z : ℂ) ^ n‖ - ‖(1 : ℂ)‖ := by rw [norm_pow, norm_one]
    _ ≤ ‖(z : ℂ) ^ n - 1‖ := norm_sub_norm_le _ _
    _ = ‖((z ^ (n : ℤ) : ℂˣ) : ℂ) - 1‖ := by rw [hz]

private theorem eq_one_of_forall_zpow_dist_lt {z : ℂˣ}
    (h : ∀ n : ℤ, ‖((z ^ n : ℂˣ) : ℂ) - 1‖ < 1) : z = 1 := by
  rcases lt_trichotomy ‖(z : ℂ)‖ 1 with hlt | heq | hgt
  · have h0 : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
    have hgt' : 1 < ‖((z⁻¹ : ℂˣ) : ℂ)‖ := by
      rw [Units.val_inv_eq_inv_val, norm_inv]
      exact (one_lt_inv₀ h0).mpr hlt
    obtain ⟨n, hn⟩ := escape_radial hgt'
    have hcast : ((z⁻¹ ^ n : ℂˣ) : ℂ) = ((z ^ (-n) : ℂˣ) : ℂ) := by
      rw [inv_zpow, ← zpow_neg]
    rw [hcast] at hn
    exact absurd (h (-n)) (not_lt.mpr hn)
  · by_contra hne
    have hd : 0 < ‖(z : ℂ) - 1‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact fun hh => hne (Units.ext (by simpa using hh))
    have hnpow : ∀ m : ℕ, ‖(z : ℂ) ^ m‖ = 1 := fun m => by rw [norm_pow, heq, one_pow]
    have hlt1 : ∀ m : ℕ, ‖(z : ℂ) ^ m - 1‖ < 1 := by
      intro m
      have hm := h ((m : ℕ) : ℤ)
      rwa [zpow_natCast, Units.val_pow_eq_pow_val] at hm
    have key : ∀ k : ℕ, Real.sqrt 3 ^ k * ‖(z : ℂ) - 1‖ ≤ ‖(z : ℂ) ^ (2 ^ k) - 1‖ := by
      intro k
      induction k with
      | zero => simpa using le_refl _
      | succ k ih =>
          have step := sq_dist_ge (w := (z : ℂ) ^ (2 ^ k)) (hnpow _) (hlt1 _)
          have hsq : ((z : ℂ) ^ (2 ^ k)) ^ 2 = (z : ℂ) ^ (2 ^ (k + 1)) := by
            rw [← pow_mul, pow_succ]
          calc Real.sqrt 3 ^ (k + 1) * ‖(z : ℂ) - 1‖
              = Real.sqrt 3 * (Real.sqrt 3 ^ k * ‖(z : ℂ) - 1‖) := by ring
            _ ≤ Real.sqrt 3 * ‖(z : ℂ) ^ (2 ^ k) - 1‖ :=
                mul_le_mul_of_nonneg_left ih (Real.sqrt_nonneg 3)
            _ ≤ ‖((z : ℂ) ^ (2 ^ k)) ^ 2 - 1‖ := step
            _ = ‖(z : ℂ) ^ (2 ^ (k + 1)) - 1‖ := by rw [hsq]
    have hsqrt3 : (1 : ℝ) < Real.sqrt 3 := by
      have h1 : (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
      rw [h1]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / ‖(z : ℂ) - 1‖) hsqrt3
    have h1 : 1 < Real.sqrt 3 ^ k * ‖(z : ℂ) - 1‖ := by
      rw [div_lt_iff₀ hd] at hk
      linarith
    have h2 := hlt1 (2 ^ k)
    have := key k
    linarith
  · obtain ⟨n, hn⟩ := escape_radial hgt
    exact absurd (h n) (not_lt.mpr hn)

private theorem unramified_cofinite_of_continuous (F : Type) [Field F] [NumberField F]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) :
    {v : HeightOneSpectrum (𝓞 F) | ¬ NumberField.TateGlobal.IsUnramifiedCharAt χ v}.Finite := by
  classical
  set V : Set ℂˣ := {u : ℂˣ | ‖(u : ℂ) - 1‖ < 1} with hVdef
  have hball : IsOpen {w : ℂ | ‖w - 1‖ < 1} := by
    have hbeq : {w : ℂ | ‖w - 1‖ < 1} = Metric.ball (1 : ℂ) 1 := by
      ext w; simp [Metric.mem_ball, dist_eq_norm]
    rw [hbeq]; exact Metric.isOpen_ball
  have hVopen : IsOpen V := hball.preimage Units.continuous_val
  have h1V : (1 : ℂˣ) ∈ V := by simp [hVdef]
  have hW : (⇑χ) ⁻¹' V ∈ 𝓝 (1 : (AdeleRing (𝓞 F) F)ˣ) := by
    have := hχc.continuousAt (x := (1 : (AdeleRing (𝓞 F) F)ˣ))
    exact this.preimage_mem_nhds (by rw [map_one]; exact hVopen.mem_nhds h1V)
  rw [(Units.isEmbedding_embedProduct).isInducing.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨O, hO, hOsub⟩ := hW
  have hembed1 : Units.embedProduct (AdeleRing (𝓞 F) F) 1
      = ((1 : AdeleRing (𝓞 F) F), MulOpposite.op (1 : AdeleRing (𝓞 F) F)) := by
    simp [Units.embedProduct]
  rw [hembed1, mem_nhds_prod_iff] at hO
  obtain ⟨P, hP, Q', hQ', hPQ⟩ := hO
  have hQ : MulOpposite.op ⁻¹' Q' ∈ 𝓝 (1 : AdeleRing (𝓞 F) F) := by
    have hcont : Continuous (MulOpposite.op (α := AdeleRing (𝓞 F) F)) :=
      MulOpposite.opHomeomorph.continuous
    exact hcont.continuousAt.preimage_mem_nhds (by simpa using hQ')
  set Q : Set (AdeleRing (𝓞 F) F) := MulOpposite.op ⁻¹' Q' with hQdef
  have hPp : P ∈ 𝓝 (((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := hP
  have hQp : Q ∈ 𝓝 (((1 : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) :
      InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := hQ
  obtain ⟨Pi, hPi, Pf, hPf, hPsub⟩ := mem_nhds_prod_iff.mp hPp
  obtain ⟨Qi, hQi, Qf, hQf, hQsub⟩ := mem_nhds_prod_iff.mp hQp
  have hOopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) := fun v =>
    Valued.isOpen_integer _
  have h1sm : (1 : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.structureMap _ _ Filter.cofinite
          (1 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) := rfl
  rw [h1sm] at hPf hQf
  have hmapP : (RestrictedProduct.structureMap _ _ Filter.cofinite) ⁻¹' Pf
      ∈ 𝓝 (1 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :=
    Filter.mem_map.mp ((Filter.ext_iff.mp
      (RestrictedProduct.nhds_eq_map_structureMap hOopen
        (1 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)) Pf).mp hPf)
  have hmapQ : (RestrictedProduct.structureMap _ _ Filter.cofinite) ⁻¹' Qf
      ∈ 𝓝 (1 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) :=
    Filter.mem_map.mp ((Filter.ext_iff.mp
      (RestrictedProduct.nhds_eq_map_structureMap hOopen
        (1 : Π v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)) Qf).mp hQf)
  rw [nhds_pi, Filter.mem_pi] at hmapP hmapQ
  obtain ⟨IP, hIPfin, tP, htP, hIPsub⟩ := hmapP
  obtain ⟨IQ, hIQfin, tQ, htQ, hIQsub⟩ := hmapQ
  refine Set.Finite.subset (Set.Finite.union hIPfin hIQfin) ?_
  intro v hv
  by_contra hvT
  apply hv
  intro t htval htinv
  apply eq_one_of_forall_zpow_dist_lt
  intro n
  rw [← map_zpow (NumberField.TateGlobal.localChar χ v) t n]
  have hzpow_mem : ∀ a : (v.adicCompletion F)ˣ,
      ((a : v.adicCompletion F) ∈ v.adicCompletionIntegers F) →
      (((a⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) →
      ∀ k : ℤ, ((a ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        ∈ v.adicCompletionIntegers F := by
    intro a ha hai k
    rcases k with m | m
    · simpa [zpow_natCast, Units.val_pow_eq_pow_val] using pow_mem ha m
    · simpa [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val] using pow_mem hai (m + 1)
  have hval' : ((t ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      ∈ v.adicCompletionIntegers F := hzpow_mem t htval htinv n
  have hinv' : (((t ^ n)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      ∈ v.adicCompletionIntegers F := by
    rw [← inv_zpow]
    exact hzpow_mem t⁻¹ htinv (by simpa using htval) n
  set s : (v.adicCompletion F)ˣ := t ^ n with hsdef
  set u : (AdeleRing (𝓞 F) F)ˣ :=
    Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
      (NumberField.AdelicLevel.localUnit (𝓞 F) F v s) with hudef
  set yP : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F :=
    Function.update (1 : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F) v
      ⟨(s : v.adicCompletion F), hval'⟩ with hyP
  set yQ : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F :=
    Function.update (1 : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F) v
      ⟨((s⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hinv'⟩ with hyQ
  have hvIP : v ∉ IP := fun hmem => hvT (Set.mem_union_left _ hmem)
  have hvIQ : v ∉ IQ := fun hmem => hvT (Set.mem_union_right _ hmem)
  have hcoordP : ((u : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.structureMap _ _ Filter.cofinite yP := by
    ext w
    show Function.update (1 : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v
        (s : v.adicCompletion F) w = ((yP w : w.adicCompletion F))
    by_cases hw : w = v
    · subst hw; simp [hyP]
    · simp [hyP, Function.update_of_ne hw]
  have hcoordQ : ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
      = RestrictedProduct.structureMap _ _ Filter.cofinite yQ := by
    have hmapinv : (u⁻¹ : (AdeleRing (𝓞 F) F)ˣ)
        = Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)
            (NumberField.AdelicLevel.localUnit (𝓞 F) F v s⁻¹) := by
      rw [hudef, ← map_inv, ← map_inv]
    rw [hmapinv]
    ext w
    show Function.update (1 : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletion F) v
        ((s⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) w = ((yQ w : w.adicCompletion F))
    by_cases hw : w = v
    · subst hw; simp [hyQ]
    · simp [hyQ, Function.update_of_ne hw]
  have hboxP : yP ∈ IP.pi tP := by
    intro w hw
    have hwv : w ≠ v := fun hh => hvIP (hh ▸ hw)
    have h1w : (1 : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F) w ∈ tP w :=
      mem_of_mem_nhds (htP w)
    simpa [hyP, Function.update_of_ne hwv] using h1w
  have hboxQ : yQ ∈ IQ.pi tQ := by
    intro w hw
    have hwv : w ≠ v := fun hh => hvIQ (hh ▸ hw)
    have h1w : (1 : Π w : HeightOneSpectrum (𝓞 F), w.adicCompletionIntegers F) w ∈ tQ w :=
      mem_of_mem_nhds (htQ w)
    simpa [hyQ, Function.update_of_ne hwv] using h1w
  have hmemP : (u : AdeleRing (𝓞 F) F) ∈ P := by
    apply hPsub
    refine ⟨mem_of_mem_nhds hPi, ?_⟩
    have : (u : AdeleRing (𝓞 F) F).2 ∈ Pf := by
      rw [hcoordP]
      exact hIPsub hboxP
    exact this
  have hmemQ : ((u⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) ∈ Q := by
    apply hQsub
    refine ⟨mem_of_mem_nhds hQi, ?_⟩
    rw [hcoordQ]
    exact hIQsub hboxQ
  have huW : u ∈ (⇑χ) ⁻¹' V := by
    apply hOsub
    show Units.embedProduct _ u ∈ O
    apply hPQ
    refine Set.mem_prod.mpr ⟨hmemP, ?_⟩
    exact hmemQ
  have hloc : NumberField.TateGlobal.localChar χ v s = χ u := by
    simp [NumberField.TateGlobal.localChar, MonoidHom.comp_apply, hudef]
  show ‖((NumberField.TateGlobal.localChar χ v s : ℂˣ) : ℂ) - 1‖ < 1
  rw [hloc]
  exact huW

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldAlphaKappa
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldBeta

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField AutomorphicForm IsDedekindDomain Topology"
open scoped ENNReal NNReal

namespace M4aD3Glue

section Beta

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

private lemma continuous_localChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) :
    Continuous (NumberField.TateGlobal.localChar χ v) := by
  letI : DecidableEq (HeightOneSpectrum (𝓞 F)) := Classical.decEq _
  have hj : Continuous (fun x : v.adicCompletion F =>
      (RestrictedProduct.inclusion
        (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
        (fun w => w.adicCompletionIntegers F)
        (Filter.le_principal_iff.mpr
          ((Set.finite_singleton v).compl_mem_cofinite))
        (⟨Function.update 1 v x, by
            rw [Filter.eventually_principal]
            intro w hw
            have hwv : w ≠ v := by simpa [Set.mem_compl_iff] using hw
            rw [Function.update_of_ne hwv]
            exact one_mem _⟩ :
          RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
            (fun w => w.adicCompletionIntegers F)
            (Filter.principal ({v} : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) :
        FiniteAdeleRing (𝓞 F) F)) := by
    exact Continuous.comp
      ((RestrictedProduct.isOpenEmbedding_inclusion_principal
        (fun w => Valued.isOpen_integer _) _).continuous)
      ((RestrictedProduct.isEmbedding_coe_of_principal.continuous_iff).mpr
        ((continuous_update v).comp (continuous_const.prodMk continuous_id)))
  have hlU : Continuous (NumberField.AdelicLevel.localUnit (𝓞 F) F v) := by
    rw [Units.continuous_iff]
    constructor
    · exact hj.comp Units.continuous_val
    · exact hj.comp Units.continuous_coe_inv
  have hfI : Continuous (NumberField.AdelicLevel.finIncl (𝓞 F) F) := by
    show Continuous (fun x : FiniteAdeleRing (𝓞 F) F => ((1 : NumberField.InfiniteAdeleRing F), x))
    exact continuous_const.prodMk continuous_id
  have hmap : Continuous (Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)) := hfI.units_map _
  show Continuous (⇑χ ∘ ⇑(Units.map (NumberField.AdelicLevel.finIncl (𝓞 F) F)) ∘
    ⇑(NumberField.AdelicLevel.localUnit (𝓞 F) F v))
  exact hχc.comp (hmap.comp hlU)

private theorem exists_localZeta_indicator_const
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    (hmod : ∀ u : (v.adicCompletion F)ˣ,
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F →
      LanglandsTunnell.TateLocal.modulus ((u : v.adicCompletion F)) = 1)
    (hcomp : IsCompact (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :
    ∃ B : Set (v.adicCompletion F), IsClopen B ∧ IsCompact B ∧
      ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ,
        LanglandsTunnell.TateLocal.localZeta μ (B.indicator 1)
          (NumberField.TateGlobal.localChar χ v) s = C := by
  classical
  have hcont := continuous_localChar F v χ hχc
  set χloc := NumberField.TateGlobal.localChar χ v with hχldef
  set V : Set ℂˣ := {u : ℂˣ | ‖(u : ℂ) - 1‖ < 1} with hVdef
  have hball : IsOpen {w : ℂ | ‖w - 1‖ < 1} := by
    have hbeq : {w : ℂ | ‖w - 1‖ < 1} = Metric.ball (1 : ℂ) 1 := by
      ext w; simp [Metric.mem_ball, dist_eq_norm]
    rw [hbeq]; exact Metric.isOpen_ball
  have hVopen : IsOpen V := hball.preimage Units.continuous_val
  have h1V : (1 : ℂˣ) ∈ V := by simp [hVdef]
  have hW : (⇑χloc) ⁻¹' V ∈ 𝓝 (1 : (v.adicCompletion F)ˣ) := by
    have := hcont.continuousAt (x := (1 : (v.adicCompletion F)ˣ))
    exact this.preimage_mem_nhds (by rw [map_one]; exact hVopen.mem_nhds h1V)
  rw [(Units.isEmbedding_embedProduct).isInducing.nhds_eq_comap, Filter.mem_comap] at hW
  obtain ⟨O, hO, hOsub⟩ := hW
  have hembed1 : Units.embedProduct (v.adicCompletion F) 1
      = ((1 : v.adicCompletion F), MulOpposite.op (1 : v.adicCompletion F)) := by
    simp [Units.embedProduct]
  rw [hembed1, mem_nhds_prod_iff] at hO
  obtain ⟨P, hP, Q', hQ', hPQ⟩ := hO
  have hQn : MulOpposite.op ⁻¹' Q' ∈ 𝓝 (1 : v.adicCompletion F) := by
    have hcop : Continuous (MulOpposite.op (α := v.adicCompletion F)) :=
      MulOpposite.opHomeomorph.continuous
    exact hcop.continuousAt.preimage_mem_nhds (by simpa using hQ')
  obtain ⟨γP, hγP⟩ := Valued.mem_nhds.mp hP
  obtain ⟨γQ, hγQ⟩ := Valued.mem_nhds.mp hQn
  set γ₀ := min (min γP.val γQ.val) 1 with hγdef
  have hγ₀pos : 0 < γ₀ :=
    lt_min (lt_min (Units.zero_lt γP) (Units.zero_lt γQ)) zero_lt_one
  set B : Set (v.adicCompletion F) := {y | Valued.v.restrict (y - 1) < γ₀} with hBdef
  have hγ₀P : γ₀ ≤ ↑γP := (min_le_left _ _).trans (min_le_left _ _)
  have hγ₀Q : γ₀ ≤ ↑γQ := (min_le_left _ _).trans (min_le_right _ _)
  have hγ₀1 : γ₀ ≤ 1 := min_le_right _ _
  have h1B : (1 : v.adicCompletion F) ∈ B := by
    simp only [hBdef, Set.mem_setOf_eq, sub_self, map_zero]
    exact hγ₀pos
  have hvone : ∀ {a : v.adicCompletion F}, a ∈ B → Valued.v.restrict a = 1 := by
    intro a ha
    have hlt : Valued.v.restrict (a - 1) < 1 := lt_of_lt_of_le ha hγ₀1
    have hrw : a = 1 + (a - 1) := by ring
    rw [hrw]
    exact Valuation.map_one_add_of_lt _ hlt
  have hvone' : ∀ {a : v.adicCompletion F}, a ∈ B → Valued.v a = 1 := by
    intro a ha
    exact (Valuation.restrict_eq_one_iff _).mp (hvone ha)
  have hne0 : ∀ {a : v.adicCompletion F}, a ∈ B → a ≠ 0 := by
    intro a ha h0
    have := hvone ha
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hBmul : ∀ {a b : v.adicCompletion F}, a ∈ B → b ∈ B → a * b ∈ B := by
    intro a b ha hb
    have key : a * b - 1 = a * (b - 1) + (a - 1) := by ring
    simp only [hBdef, Set.mem_setOf_eq] at ha hb ⊢
    rw [key]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ha)
    rw [map_mul, hvone (show a ∈ B from ha), one_mul]
    exact hb
  have hBinv : ∀ {a : v.adicCompletion F}, a ∈ B → a⁻¹ ∈ B := by
    intro a ha
    have ha0 := hne0 ha
    have key : a⁻¹ - 1 = -(a⁻¹ * (a - 1)) := by
      field_simp
      ring
    simp only [hBdef, Set.mem_setOf_eq] at ha ⊢
    rw [key, Valuation.map_neg, map_mul, map_inv₀,
      hvone (show a ∈ B from ha), inv_one, one_mul]
    exact ha
  have hBopen : IsOpen B := by
    rw [isOpen_iff_mem_nhds]
    intro y₀ hy₀
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 γ₀ (ne_of_gt hγ₀pos), fun y hy => ?_⟩
    simp only [Units.val_mk0] at hy
    simp only [Set.mem_setOf_eq] at hy
    simp only [hBdef, Set.mem_setOf_eq] at hy₀ ⊢
    have key : y - 1 = (y - y₀) + (y₀ - 1) := by ring
    rw [key]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hy hy₀)
  have hBclosed : IsClosed B := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y₀ hy₀
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 γ₀ (ne_of_gt hγ₀pos), fun y hy => ?_⟩
    simp only [Units.val_mk0] at hy
    simp only [Set.mem_setOf_eq] at hy
    simp only [hBdef, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hy₀ ⊢
    have hneq : Valued.v.restrict (y₀ - 1) ≠ Valued.v.restrict (y - y₀) :=
      ne_of_gt (lt_of_lt_of_le hy hy₀)
    have key : y - 1 = (y₀ - 1) + (y - y₀) := by ring
    rw [key, Valuation.map_add_of_distinct_val _ hneq]
    exact le_max_of_le_left hy₀
  have hBsubO : B ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro a ha
    rw [SetLike.mem_coe, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    rw [hvone' (show a ∈ B from ha)]
  have hBcompact : IsCompact B := hcomp.of_isClosed_subset hBclosed hBsubO
  have hzpow : ∀ (y : v.adicCompletion F) (hy : y ∈ B) (hy0 : y ≠ 0) (n : ℤ),
      ((Units.mk0 y hy0 ^ n : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ B := by
    intro y hy hy0 n
    have hpow : ∀ k : ℕ, ((Units.mk0 y hy0 ^ (k : ℤ) : (v.adicCompletion F)ˣ) :
        v.adicCompletion F) ∈ B := by
      intro k
      induction k with
      | zero => simpa using h1B
      | succ k ih =>
        have hstep : ((Units.mk0 y hy0 ^ ((k + 1 : ℕ) : ℤ) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F)
            = ((Units.mk0 y hy0 ^ (k : ℤ) : (v.adicCompletion F)ˣ) :
              v.adicCompletion F) * y := by
          push_cast
          rw [zpow_add_one₀ (Units.ne_zero _)]
          simp
        rw [hstep]
        exact hBmul ih hy
    cases n with
    | ofNat k => exact hpow k
    | negSucc k =>
      have hinv : ((Units.mk0 y hy0 ^ (Int.negSucc k) : (v.adicCompletion F)ˣ) :
          v.adicCompletion F)
          = (((Units.mk0 y hy0 ^ ((k + 1 : ℕ) : ℤ) : (v.adicCompletion F)ˣ) :
            v.adicCompletion F))⁻¹ := by
        rw [Int.negSucc_eq, zpow_neg]
        push_cast
        simp
      rw [hinv]
      exact hBinv (hpow (k + 1))
  have htriv : ∀ (y : v.adicCompletion F) (hy : y ∈ B) (hy0 : y ≠ 0),
      χloc (Units.mk0 y hy0) = 1 := by
    intro y hy hy0
    refine eq_one_of_forall_zpow_dist_lt (z := χloc (Units.mk0 y hy0)) ?_
    intro n
    rw [← map_zpow]
    have hun : (Units.mk0 y hy0 ^ n) ∈ (⇑χloc) ⁻¹' V := by
      apply hOsub
      apply hPQ
      refine Set.mem_prod.mpr ⟨?_, ?_⟩
      · apply hγP
        simp only [Set.mem_setOf_eq]
        exact lt_of_lt_of_le (hzpow y hy hy0 n) hγ₀P
      · show MulOpposite.op (((Units.mk0 y hy0 ^ n)⁻¹ : (v.adicCompletion F)ˣ) :
          v.adicCompletion F) ∈ Q'
        have hmem : (((Units.mk0 y hy0 ^ n)⁻¹ : (v.adicCompletion F)ˣ) :
            v.adicCompletion F) ∈ MulOpposite.op ⁻¹' Q' := by
          apply hγQ
          simp only [Set.mem_setOf_eq]
          rw [← zpow_neg]
          exact lt_of_lt_of_le (hzpow y hy hy0 (-n)) hγ₀Q
        exact hmem
    simpa [hVdef] using hun
  refine ⟨B, ⟨hBclosed, hBopen⟩, hBcompact, (((μ B).toReal : ℝ) : ℂ), ?_, ?_⟩
  · have hpos : 0 < μ B := hBopen.measure_pos μ ⟨1, h1B⟩
    have hfin : μ B < ⊤ := hBcompact.measure_lt_top
    exact_mod_cast ne_of_gt (ENNReal.toReal_pos (ne_of_gt hpos) (ne_of_lt hfin))
  · intro s
    unfold LanglandsTunnell.TateLocal.localZeta
    have hBmeas : MeasurableSet B := hBopen.measurableSet
    have hptw : ∀ x : v.adicCompletion F,
        B.indicator 1 x * LanglandsTunnell.TateLocal.charExt χloc x
          * ((LanglandsTunnell.TateLocal.modulus x : ℝ) : ℂ) ^ s
        = B.indicator (fun _ => (1 : ℂ)) x := by
      intro x
      by_cases hx : x ∈ B
      · have hx0 := hne0 hx
        have hvx := hvone' (show x ∈ B from hx)
        have hmem1 : ((Units.mk0 x hx0 : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            ∈ v.adicCompletionIntegers F := by
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
          simp [hvx]
        have hmem2 : (((Units.mk0 x hx0)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            ∈ v.adicCompletionIntegers F := by
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
          simp [map_inv₀, hvx]
        have hmodx := hmod (Units.mk0 x hx0) hmem1 hmem2
        simp only [Units.val_mk0] at hmodx
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
          LanglandsTunnell.TateLocal.charExt_of_ne_zero χloc hx0, htriv x hx hx0, hmodx]
        norm_num
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
        ring
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hptw)]
    rw [MeasureTheory.integral_indicator hBmeas, MeasureTheory.setIntegral_const]
    have hB0 : B ⊆ ({0}ᶜ : Set (v.adicCompletion F)) := fun a ha => hne0 ha
    have hν : LanglandsTunnell.TateLocal.mulMeasure μ B = μ B := by
      unfold LanglandsTunnell.TateLocal.mulMeasure
      rw [MeasureTheory.withDensity_apply _ hBmeas]
      have hcongr : ∀ x ∈ B,
          ((LanglandsTunnell.TateLocal.modulus x : ℝ≥0∞))⁻¹ = 1 := by
        intro x hx
        have hx0 := hne0 hx
        have hvx := hvone' (show x ∈ B from hx)
        have hmem1 : ((Units.mk0 x hx0 : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            ∈ v.adicCompletionIntegers F := by
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
          simp [hvx]
        have hmem2 : (((Units.mk0 x hx0)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
            ∈ v.adicCompletionIntegers F := by
          rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
          simp [map_inv₀, hvx]
        have hmodx := hmod (Units.mk0 x hx0) hmem1 hmem2
        simp only [Units.val_mk0] at hmodx
        rw [hmodx]
        simp
      rw [MeasureTheory.setLIntegral_congr_fun hBmeas
        (fun x hx => hcongr x hx)]
      rw [MeasureTheory.setLIntegral_one, MeasureTheory.Measure.restrict_apply hBmeas]
      rw [Set.inter_eq_self_of_subset_left hB0]
    have hνr : (LanglandsTunnell.TateLocal.mulMeasure μ).real B = (μ B).toReal := by
      unfold MeasureTheory.Measure.real
      rw [hν]
    rw [hνr]
    simp [Complex.real_smul]

end Beta
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldBeta
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldDelta

namespace M4aD3Glue

section Delta
variable {ι : Type*}

private theorem mulIndicator_one_add (U : Set ι) (a : ι → ℂ) :
    Set.mulIndicator U (fun i => 1 + a i) = fun i => 1 + Set.indicator U a i := by
  funext i
  by_cases h : i ∈ U
  · simp [Set.mulIndicator_of_mem h, Set.indicator_of_mem h]
  · simp [Set.mulIndicator_of_notMem h, Set.indicator_of_notMem h]

private theorem summable_norm_indicator {a : ι → ℂ} (hsum : Summable fun i => ‖a i‖) (U : Set ι) :
    Summable fun i => ‖Set.indicator U a i‖ := by
  have h1 : (fun i => ‖Set.indicator U a i‖) = Set.indicator U fun i => ‖a i‖ := by
    funext i
    by_cases h : i ∈ U
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [h1]
  exact hsum.indicator U

private theorem tprod_subtype_peel (a : ι → ℂ) (hsum : Summable fun i => ‖a i‖)
    (S T : Set ι) (hST : S ⊆ T) (hfin : (T \ S).Finite) :
    ∏' i : {i // i ∉ S}, (1 + a i)
      = (∏ i ∈ hfin.toFinset, (1 + a i)) * ∏' i : {i // i ∉ T}, (1 + a i) := by
  have hsplit : Set.mulIndicator {i | i ∉ S} (fun i => 1 + a i)
      = fun i => Set.mulIndicator (T \ S) (fun i => 1 + a i) i
          * Set.mulIndicator {i | i ∉ T} (fun i => 1 + a i) i := by
    funext i
    by_cases hiT : i ∈ T
    · by_cases hiS : i ∈ S
      · have h1 : i ∉ {i | i ∉ S} := by simp [hiS]
        have h2 : i ∉ T \ S := by simp [hiS]
        have h3 : i ∉ {i | i ∉ T} := by simp [hiT]
        simp [Set.mulIndicator_of_notMem, h1, h2, h3]
      · have h1 : i ∈ {i | i ∉ S} := by simp [hiS]
        have h2 : i ∈ T \ S := ⟨hiT, hiS⟩
        have h3 : i ∉ {i | i ∉ T} := by simp [hiT]
        simp [Set.mulIndicator_of_mem, Set.mulIndicator_of_notMem, h1, h2, h3]
    · have hiS : i ∉ S := fun h => hiT (hST h)
      have h1 : i ∈ {i | i ∉ S} := by simp [hiS]
      have h2 : i ∉ T \ S := by simp [hiT]
      have h3 : i ∈ {i | i ∉ T} := by simp [hiT]
      simp [Set.mulIndicator_of_mem, Set.mulIndicator_of_notMem, h1, h2, h3]
  have hm1 : Multipliable (Set.mulIndicator (T \ S) fun i => 1 + a i) := by
    rw [mulIndicator_one_add]
    exact multipliable_one_add_of_summable (summable_norm_indicator hsum _)
  have hm2 : Multipliable (Set.mulIndicator {i | i ∉ T} fun i => 1 + a i) := by
    rw [mulIndicator_one_add]
    exact multipliable_one_add_of_summable (summable_norm_indicator hsum _)
  have h0 : (∏' i : {i // i ∉ S}, (1 + a i))
      = ∏' i : ι, Set.mulIndicator {i | i ∉ S} (fun i => 1 + a i) i :=
    tprod_subtype {i | i ∉ S} fun i => 1 + a i
  rw [h0]
  simp only [hsplit]
  rw [hm1.tprod_mul hm2]
  congr 1
  · have h1 : ∀ b ∉ hfin.toFinset, Set.mulIndicator (T \ S) (fun i => 1 + a i) b = 1 := by
      intro b hb
      exact Set.mulIndicator_of_notMem (fun hmem => hb (hfin.mem_toFinset.mpr hmem)) _
    rw [tprod_eq_prod h1]
    exact Finset.prod_congr rfl fun i hi =>
      Set.mulIndicator_of_mem (hfin.mem_toFinset.mp hi) _
  · exact (tprod_subtype {i | i ∉ T} fun i => 1 + a i).symm

end Delta
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldDelta
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldW1Witness

p2m_open "NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField IsDedekindDomain MeasureTheory AutomorphicForm P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT"
open NumberField.AdelicFourier NumberField.StandardAddChar
open MeasureTheory.Measure
open scoped NNReal

namespace M4aD3Glue

section Instances
variable (F : Type) [Field F] [NumberField F]

private scoped instance : LocallyCompactSpace ℝ≥0ˣ := inferInstance

private scoped instance : LocallyCompactSpace (AdeleRing (𝓞 F) F)ˣ := by
  haveI := WeilDomain.locallyCompactSpace_normOneIdeles F
  exact (FujisakiC3.idelesSplit F).toHomeomorph.locallyCompactSpace_iff.mpr inferInstance

end Instances
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section Witnesses
variable (F : Type) [Field F] [NumberField F]

private theorem w1_mu :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
    haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
    ∃ μ : Measure (AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure ∧ μ (AdelicBox.adelicBox F) = 1 := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
  obtain ⟨K₀⟩ : Nonempty (TopologicalSpace.PositiveCompacts (AdeleRing (𝓞 F) F)) := inferInstance
  set μ₀ : Measure (AdeleRing (𝓞 F) F) := addHaarMeasure K₀
  have htop : μ₀ (AdelicBox.adelicBox F) < ⊤ := AdelicBox.measure_adelicBox_lt_top F μ₀
  have hpos : 0 < μ₀ (AdelicBox.adelicBox F) := AdelicBox.measure_adelicBox_pos F μ₀
  refine ⟨(μ₀ (AdelicBox.adelicBox F))⁻¹ • μ₀, ?_, ?_⟩
  · exact Measure.IsAddHaarMeasure.smul (μ := μ₀)
      (cpos := ENNReal.inv_ne_zero.mpr htop.ne) (ctop := ENNReal.inv_ne_top.mpr hpos.ne')
  · rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos.ne' htop.ne]

private theorem w1_nu :
    letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := borel _
    haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := ⟨rfl⟩
    ∃ ν : Measure (AdeleRing (𝓞 F) F)ˣ, ν.IsHaarMeasure := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := borel _
  haveI : BorelSpace (AdeleRing (𝓞 F) F)ˣ := ⟨rfl⟩
  obtain ⟨K₁⟩ : Nonempty (TopologicalSpace.PositiveCompacts (AdeleRing (𝓞 F) F)ˣ) := inferInstance
  exact ⟨Measure.haarMeasure K₁, inferInstance⟩

private theorem w1_psi :
    ∃ ψ : AddChar (AdeleRing (𝓞 F) F) ℂ, IsGlobalAddChar F ψ ∧
      ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
  have hstd := NumberField.StandardAddChar.isGlobalAddChar_stdAddChar F
  obtain ⟨a, ha0, hatr⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hstd
  refine ⟨(stdAddChar F).compAddMonoidHom
    (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a)), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro α
    show stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) a
      * algebraMap F (AdeleRing (𝓞 F) F) α) = 1
    rw [← map_mul]
    exact hstd.principalInvariant (a * α)
  · exact hstd.continuous.comp (continuous_const_mul _)
  · intro h1
    apply hstd.nontrivial
    ext y
    have h2 : stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) a
        * (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * y)) = 1 := by
      have h3 := DFunLike.congr_fun h1 (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * y)
      rwa [AddChar.one_apply] at h3
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul] at h2
    simpa using h2
  · intro x
    have h1 : (stdAddChar F).compAddMonoidHom
        (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a)) (x, 0)
        = stdAddChar F (algebraMap F (InfiniteAdeleRing F) a * x, 0) :=
      congrArg (stdAddChar F) (Prod.ext rfl (mul_zero _))
    exact h1.trans (hatr x)

end Witnesses
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end M4aD3Glue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

end FoldW1Witness
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue"

section FoldSpine

p2m_open "MeasureTheory NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField AutomorphicForm IsDedekindDomain"
p2m_open "NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal NumberField.AdelicFourier NumberField.AdelicBox"
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open LanglandsTunnell.TateLocal LanglandsTunnell.ArchPlace
open M4aD3Glue M4aLocalCFT
open Classical
open scoped NNReal ENNReal

noncomputable section

namespace TateGlobal
namespace IdeleCharGlue

variable {F : Type} [Field F] [NumberField F]

private local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
private local instance (v : HeightOneSpectrum (𝓞 F)) : BorelSpace (v.adicCompletion F) := ⟨rfl⟩
private local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
private local instance (w : InfinitePlace F) : BorelSpace w.Completion := ⟨rfl⟩
private local instance : MeasurableSpace (AdeleRing (𝓞 F) F) := borel _
private local instance : BorelSpace (AdeleRing (𝓞 F) F) := ⟨rfl⟩
private local instance : MeasurableSpace (AdeleRing (𝓞 F) F)ˣ := borel _
private local instance : BorelSpace (AdeleRing (𝓞 F) F)ˣ := ⟨rfl⟩

private noncomputable abbrev archRealEquiv {w : InfinitePlace F} (hv : w.IsReal) : ℝ ≃ᵐ w.Completion :=
  M4aD3Glue.realPlaceMeasurableEquiv hv

private noncomputable abbrev archCxEquiv {w : InfinitePlace F} (hv : w.IsComplex) : ℂ ≃ᵐ w.Completion :=
  M4aD3Glue.complexPlaceMeasurableEquiv hv

private def archMeas (w : InfinitePlace F) : Measure w.Completion :=
  if hw : w.IsReal then Measure.map (archRealEquiv hw) volume
  else Measure.map (archCxEquiv (not_isReal_iff_isComplex.mp hw)) ((2 : ℝ≥0∞) • volume)

private theorem archMeas_real {w : InfinitePlace F} (hw : w.IsReal) :
    archMeas w = Measure.map (archRealEquiv hw) volume := by
  rw [archMeas, dif_pos hw]

private theorem archMeas_cx {w : InfinitePlace F} (hw : w.IsComplex) :
    archMeas w = Measure.map (archCxEquiv hw) ((2 : ℝ≥0∞) • volume) := by
  have hnr : ¬ w.IsReal := not_isReal_iff_isComplex.mpr hw
  rw [archMeas, dif_neg hnr]

private scoped instance (w : InfinitePlace F) : (archMeas w).IsAddHaarMeasure := by
  by_cases hw : w.IsReal
  · rw [archMeas_real hw]
    show (Measure.map ((ringEquivRealOfIsReal hw).symm.toAddEquiv) volume).IsAddHaarMeasure
    exact ((ringEquivRealOfIsReal hw).symm.toAddEquiv).isAddHaarMeasure_map volume
      ((isometryEquivRealOfIsReal hw).symm.isometry.continuous)
      ((isometry_extensionEmbeddingOfIsReal hw).continuous)
  · have hwc : w.IsComplex := not_isReal_iff_isComplex.mp hw
    rw [archMeas_cx hwc]
    haveI h2 : ((2 : ℝ≥0∞) • (volume : Measure ℂ)).IsAddHaarMeasure :=
      Measure.IsAddHaarMeasure.smul _ (by norm_num) (by norm_num)
    show (Measure.map ((ringEquivComplexOfIsComplex hwc).symm.toAddEquiv)
      ((2 : ℝ≥0∞) • volume)).IsAddHaarMeasure
    exact ((ringEquivComplexOfIsComplex hwc).symm.toAddEquiv).isAddHaarMeasure_map _
      ((isometryEquivComplexOfIsComplex hwc).symm.isometry.continuous)
      ((isometry_extensionEmbedding w).continuous)

private def archFactor (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) (w : InfinitePlace F) :
    w.Completion → ℂ :=
  if hw : w.IsReal then
    fun z => realTestFun (a ⟨w, hw⟩) (ringEquivRealOfIsReal hw z)
  else
    fun z => complexTestFun (k ⟨w, not_isReal_iff_isComplex.mp hw⟩)
      (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw) z)

private theorem archFactor_real (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) {w : InfinitePlace F} (hw : w.IsReal) :
    archFactor a k w = fun z => realTestFun (a ⟨w, hw⟩) (ringEquivRealOfIsReal hw z) := by
  rw [archFactor, dif_pos hw]

private theorem archFactor_cx (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) {w : InfinitePlace F} (hw : w.IsComplex) :
    archFactor a k w
      = fun z => complexTestFun (k ⟨w, hw⟩) (ringEquivComplexOfIsComplex hw z) := by
  have hnr : ¬ w.IsReal := not_isReal_iff_isComplex.mpr hw
  rw [archFactor, dif_neg hnr]

private theorem prod_places_split (f : InfinitePlace F → ℂ) :
    ∏ w, f w
      = (∏ w : {w : InfinitePlace F // w.IsReal}, f w.1)
        * ∏ w : {w : InfinitePlace F // w.IsComplex}, f w.1 := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace F => w.IsReal) f]
  congr 1
  exact Fintype.prod_equiv
    (Equiv.subtypeEquivRight fun w => (not_isReal_iff_isComplex (w := w)))
    (fun w => f w.1) (fun w => f w.1) (fun w => rfl)

private theorem archGauss_coord (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) (x : InfiniteAdeleRing F) :
    archGaussTensor F a k (InfiniteAdeleRing.ringEquiv_mixedSpace F x)
      = ∏ w, archFactor a k w (x w) := by
  rw [archGaussTensor_eq_prod, prod_places_split (fun w => archFactor a k w (x w))]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [archFactor_real a k w.2]
    rfl
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [archFactor_cx a k w.2]
    rfl

private theorem isFactorizable_d3Witness
    (T : Finset (HeightOneSpectrum (𝓞 F)))
    (B : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (a : {w : InfinitePlace F // w.IsReal} → ZMod 2)
    (k : {w : InfinitePlace F // w.IsComplex} → ℤ) :
    IsFactorizableStandardOutside (d3Witness T B a k) T (archFactor a k)
      (fun v => (B v).indicator 1) := by
  intro x
  by_cases hx : x ∈ integralOutside T
  · rw [Set.indicator_of_mem hx]
    show archGaussTensor F a k (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
        * finBoxIndicator T B x.2
      = (∏ w, archFactor a k w (x.1 w))
        * ∏ v ∈ T, (B v).indicator 1 ((x.2 : FiniteAdeleRing (𝓞 F) F) v)
    rw [archGauss_coord]
    congr 1
    by_cases hall : ∀ v ∈ T, (x.2 : FiniteAdeleRing (𝓞 F) F) v ∈ B v
    · have hmem : (x.2 : FiniteAdeleRing (𝓞 F) F) ∈ finBox T B :=
        ⟨hall, fun v hv => hx v hv⟩
      rw [finBoxIndicator, Set.indicator_of_mem hmem]
      exact (Finset.prod_eq_one fun v hv => by
        rw [Set.indicator_of_mem (hall v hv)]; rfl).symm
    · push Not at hall
      obtain ⟨v0, hv0T, hv0B⟩ := hall
      have hnmem : (x.2 : FiniteAdeleRing (𝓞 F) F) ∉ finBox T B := fun hmem =>
        hv0B (hmem.1 v0 hv0T)
      rw [finBoxIndicator, Set.indicator_of_notMem hnmem]
      exact (Finset.prod_eq_zero hv0T (by
        rw [Set.indicator_of_notMem hv0B])).symm
  · rw [Set.indicator_of_notMem hx]
    have hnmem : (x.2 : FiniteAdeleRing (𝓞 F) F) ∉ finBox T B := by
      intro hmem
      exact hx fun v hv => hmem.2 v hv
    show archGaussTensor F a k (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1)
        * finBoxIndicator T B x.2 = 0
    rw [finBoxIndicator, Set.indicator_of_notMem hnmem, mul_zero]

private theorem continuous_unitsMap {M N : Type} [Monoid M] [Monoid N]
    [TopologicalSpace M] [TopologicalSpace N] (f : M →* N) (hf : Continuous f) :
    Continuous (Units.map f) :=
  Units.continuous_iff.mpr ⟨hf.comp Units.continuous_val, hf.comp Units.continuous_coe_inv⟩

private def pulledRealChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F} (hw : w.IsReal) :
    ℝˣ →* ℂˣ :=
  (archLocalChar χ w).comp (Units.map
    ((ringEquivRealOfIsReal hw).symm : ℝ →+* w.Completion).toMonoidHom)

private def pulledCxChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) {w : InfinitePlace F} (hw : w.IsComplex) :
    ℂˣ →* ℂˣ :=
  (archLocalChar χ w).comp (Units.map
    ((ringEquivComplexOfIsComplex hw).symm : ℂ →+* w.Completion).toMonoidHom)

private theorem continuous_pulledRealChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    {w : InfinitePlace F} (hw : w.IsReal) : Continuous (pulledRealChar χ hw) := by
  refine ((hχc.comp (M4aLocalCFT.FujisakiC3.continuous_archUnitHom w)).comp
    (continuous_unitsMap _ ?_))
  exact (isometryEquivRealOfIsReal hw).symm.isometry.continuous

private theorem continuous_pulledCxChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ)
    {w : InfinitePlace F} (hw : w.IsComplex) : Continuous (pulledCxChar χ hw) := by
  refine ((hχc.comp (M4aLocalCFT.FujisakiC3.continuous_archUnitHom w)).comp
    (continuous_unitsMap _ ?_))
  exact (isometryEquivComplexOfIsComplex hw).symm.isometry.continuous

private theorem norm_pulledRealChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχu : IsUnitaryChar (𝓞 F) F χ) {w : InfinitePlace F} (hw : w.IsReal) (x : ℝˣ) :
    ‖((pulledRealChar χ hw x : ℂˣ) : ℂ)‖ = 1 :=
  hχu _

private theorem norm_pulledCxChar (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχu : IsUnitaryChar (𝓞 F) F χ) {w : InfinitePlace F} (hw : w.IsComplex) (z : ℂˣ) :
    ‖((pulledCxChar χ hw z : ℂˣ) : ℂ)‖ = 1 :=
  hχu _

private def invGR (r : ℂ) : ℂ → ℂ := fun s =>
  (Real.pi : ℂ) ^ ((s + r) / 2) * (Complex.Gamma ((s + r) / 2))⁻¹

private def invGC (r : ℂ) : ℂ → ℂ := fun s =>
  (Real.pi : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (2 * (Real.pi : ℂ)) ^ (s + r) * (Complex.Gamma (s + r))⁻¹)

private theorem pi_cx_ne_zero : (Real.pi : ℂ) ≠ 0 := by
  exact_mod_cast Real.pi_ne_zero

private theorem two_pi_cx_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 :=
  mul_ne_zero two_ne_zero pi_cx_ne_zero

private theorem gamma_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) : Complex.Gamma z ≠ 0 := by
  refine Complex.Gamma_ne_zero fun m => ?_
  intro h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

private theorem differentiable_invGR (r : ℂ) : Differentiable ℂ (invGR r) := by
  refine Differentiable.mul ?_ ?_
  · exact Differentiable.const_cpow ((differentiable_id.add_const r).div_const 2)
      (Or.inl pi_cx_ne_zero)
  · exact Complex.differentiable_one_div_Gamma.comp
      ((differentiable_id.add_const r).div_const 2)

private theorem differentiable_invGC (r : ℂ) : Differentiable ℂ (invGC r) := by
  refine Differentiable.const_mul (Differentiable.mul ?_ ?_) _
  · exact Differentiable.const_mul
      (Differentiable.const_cpow (differentiable_id.add_const r) (Or.inl two_pi_cx_ne_zero)) _
  · exact Complex.differentiable_one_div_Gamma.comp (differentiable_id.add_const r)

private theorem Gammaℝ_mul_invGR (r s : ℂ) (hre : 0 < (s + r).re) :
    Complex.Gammaℝ (s + r) * invGR r s = 1 := by
  have hΓ : Complex.Gamma ((s + r) / 2) ≠ 0 := by
    refine gamma_ne_zero_of_re_pos ?_
    rw [show (s + r) / 2 = (s + r) * (2⁻¹ : ℂ) by ring, Complex.mul_re]
    have h1 : ((2⁻¹ : ℂ)).re = 2⁻¹ := by norm_num
    have h2 : ((2⁻¹ : ℂ)).im = 0 := by norm_num
    rw [h1, h2, mul_zero, sub_zero]
    positivity
  have hpow : (Real.pi : ℂ) ^ (-(s + r) / 2) * (Real.pi : ℂ) ^ ((s + r) / 2) = 1 := by
    rw [← Complex.cpow_add _ _ pi_cx_ne_zero,
      show -(s + r) / 2 + (s + r) / 2 = 0 by ring, Complex.cpow_zero]
  have hΓc : Complex.Gamma ((s + r) / 2) * (Complex.Gamma ((s + r) / 2))⁻¹ = 1 :=
    mul_inv_cancel₀ hΓ
  show (Real.pi : ℂ) ^ (-(s + r) / 2) * Complex.Gamma ((s + r) / 2)
      * ((Real.pi : ℂ) ^ ((s + r) / 2) * (Complex.Gamma ((s + r) / 2))⁻¹) = 1
  calc (Real.pi : ℂ) ^ (-(s + r) / 2) * Complex.Gamma ((s + r) / 2)
        * ((Real.pi : ℂ) ^ ((s + r) / 2) * (Complex.Gamma ((s + r) / 2))⁻¹)
      = ((Real.pi : ℂ) ^ (-(s + r) / 2) * (Real.pi : ℂ) ^ ((s + r) / 2))
        * (Complex.Gamma ((s + r) / 2) * (Complex.Gamma ((s + r) / 2))⁻¹) := by ring
    _ = 1 := by rw [hpow, hΓc, one_mul]

private theorem piGammaℂ_mul_invGC (r s : ℂ) (hre : 0 < (s + r).re) :
    ((Real.pi : ℂ) * Complex.Gammaℂ (s + r)) * invGC r s = 1 := by
  have hΓ : Complex.Gamma (s + r) ≠ 0 := gamma_ne_zero_of_re_pos hre
  have h2ne : (2 : ℂ) ≠ 0 := by norm_num
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(s + r)) * (2 * (Real.pi : ℂ)) ^ (s + r) = 1 := by
    rw [← Complex.cpow_add _ _ two_pi_cx_ne_zero,
      show -(s + r) + (s + r) = 0 by ring, Complex.cpow_zero]
  have hΓc : Complex.Gamma (s + r) * (Complex.Gamma (s + r))⁻¹ = 1 :=
    mul_inv_cancel₀ hΓ
  show ((Real.pi : ℂ) * (2 * (2 * (Real.pi : ℂ)) ^ (-(s + r)) * Complex.Gamma (s + r)))
      * ((Real.pi : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (2 * (Real.pi : ℂ)) ^ (s + r)
        * (Complex.Gamma (s + r))⁻¹)) = 1
  calc ((Real.pi : ℂ) * (2 * (2 * (Real.pi : ℂ)) ^ (-(s + r)) * Complex.Gamma (s + r)))
        * ((Real.pi : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (2 * (Real.pi : ℂ)) ^ (s + r)
          * (Complex.Gamma (s + r))⁻¹))
      = ((Real.pi : ℂ) * (Real.pi : ℂ)⁻¹) * ((2 : ℂ) * (2 : ℂ)⁻¹)
        * ((2 * (Real.pi : ℂ)) ^ (-(s + r)) * (2 * (Real.pi : ℂ)) ^ (s + r))
        * (Complex.Gamma (s + r) * (Complex.Gamma (s + r))⁻¹) := by ring
    _ = 1 := by
        rw [mul_inv_cancel₀ pi_cx_ne_zero, mul_inv_cancel₀ h2ne, hpow, hΓc]
        norm_num

private theorem differentiable_finset_prod {ι : Type} (t : Finset ι) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ t, Differentiable ℂ (g i)) :
    Differentiable ℂ (fun s => ∏ i ∈ t, g i s) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
      have h1 : (fun s => ∏ i ∈ insert a t, g i s)
          = fun s => g a s * ∏ i ∈ t, g i s := by
        funext s
        rw [Finset.prod_insert ha]
      rw [h1]
      exact (hg a (Finset.mem_insert_self a t)).mul
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

private theorem norm_eulerTerm (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    ‖((localChar χ v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)‖
      = ‖ShellBound.baseFam F s.re v‖ := by
  rw [norm_mul]
  have h1 : ‖((localChar χ v (ϖ v) : ℂˣ) : ℂ)‖ = 1 := by
    rw [localChar_apply]
    exact hχu _
  have hN : 0 < Ideal.absNorm v.asIdeal :=
    lt_trans Nat.zero_lt_one (ShellBound.one_lt_absNorm v)
  rw [h1, one_mul, Complex.norm_natCast_cpow_of_pos hN, Complex.neg_re,
    ShellBound.norm_baseFam]

private theorem summable_norm_eulerTerm (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (hχu : IsUnitaryChar (𝓞 F) F χ)
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    {s : ℂ} (hs : 1 < s.re) :
    Summable fun v : HeightOneSpectrum (𝓞 F) =>
      ‖-(((localChar χ v (ϖ v) : ℂˣ) : ℂ) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))‖ := by
  refine (ShellBound.summable_norm_baseFam hs).congr fun v => ?_
  rw [norm_neg, norm_eulerTerm χ hχu ϖ v s]

private theorem tprod_conv (W : Finset (HeightOneSpectrum (𝓞 F)))
    (t : HeightOneSpectrum (𝓞 F) → ℂ) :
    (∏' v : {v // v ∉ W}, (1 - t v.1))
      = ∏' v : {v : HeightOneSpectrum (𝓞 F) // v ∉ (↑W : Set (HeightOneSpectrum (𝓞 F)))},
          (1 + -(t v.1)) :=
  tprod_congr fun v => sub_eq_add_neg _ _

private theorem exists_meromorphicOn_eq_partialEulerProduct_core
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ)
    (hα : {v : HeightOneSpectrum (𝓞 F) | ¬ IsUnramifiedCharAt χ v}.Finite)
    (hclassR : ∀ (w : InfinitePlace F) (hw : w.IsReal), ∃ (ε : Bool) (τ : ℝ), ∀ x : ℝˣ,
      ((pulledRealChar χ hw x : ℂˣ) : ℂ)
        = (if ε then (Real.sign (x : ℝ) : ℂ) else 1)
          * Complex.exp (Complex.I * (τ * Real.log |(x : ℝ)|)))
    (hclassC : ∀ (w : InfinitePlace F) (hw : w.IsComplex), ∃ (k : ℤ) (τ : ℝ), ∀ z : ℂˣ,
      ((pulledCxChar χ hw z : ℂˣ) : ℂ)
        = (((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k)
          * Complex.exp (Complex.I * (τ * Real.log ‖(z : ℂ)‖)))
    (hβ : ∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (v.adicCompletion F)),
      μ.IsAddHaarMeasure →
      ∃ B : Set (v.adicCompletion F), IsClopen B ∧ IsCompact B ∧
        ∃ C : ℂ, C ≠ 0 ∧ ∀ s : ℂ,
          localZeta μ (B.indicator 1) (localChar χ v) s = C)
    (hevalR : ∀ {w : InfinitePlace F} (hw : w.IsReal) (ε : Bool) (τ : ℝ)
      (χw : (w.Completion)ˣ →* ℂˣ),
      (∀ x : ℝˣ,
        ((χw.comp (Units.map
            ((ringEquivRealOfIsReal hw).symm : ℝ →+* w.Completion).toMonoidHom) x : ℂˣ) : ℂ)
          = (if ε then (Real.sign (x : ℝ) : ℂ) else 1)
            * Complex.exp (Complex.I * (τ * Real.log |(x : ℝ)|))) →
      ∀ s : ℂ, 0 < (s + Complex.I * τ + (if ε then 1 else 0)).re →
      localZeta (Measure.map (archRealEquiv hw) volume)
          (fun z => realTestFun (if ε then (1 : ZMod 2) else 0) (ringEquivRealOfIsReal hw z))
          χw s
        = Complex.Gammaℝ (s + Complex.I * τ + (if ε then 1 else 0)))
    (hevalC : ∀ {w : InfinitePlace F} (hw : w.IsComplex) (k : ℤ) (τ : ℝ)
      (χw : (w.Completion)ˣ →* ℂˣ),
      (∀ z : ℂˣ,
        ((χw.comp (Units.map
            ((ringEquivComplexOfIsComplex hw).symm : ℂ →+* w.Completion).toMonoidHom) z : ℂˣ) : ℂ)
          = (((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ k)
            * Complex.exp (Complex.I * (τ * Real.log ‖(z : ℂ)‖))) →
      ∀ s : ℂ, 0 < (s + (Complex.I * τ + (k.natAbs : ℂ)) / 2).re →
      localZeta (Measure.map (archCxEquiv hw) ((2 : ℝ≥0∞) • volume))
          (fun z => complexTestFun k (ringEquivComplexOfIsComplex hw z))
          χw s
        = (Real.pi : ℂ) * Complex.Gammaℂ (s + (Complex.I * τ + (k.natAbs : ℂ)) / 2))
    (hδpeel : ∀ (a : HeightOneSpectrum (𝓞 F) → ℂ),
      (Summable fun v => ‖a v‖) → ∀ (U W : Set (HeightOneSpectrum (𝓞 F))), U ⊆ W →
      ∀ (hfin : (W \ U).Finite),
      (∏' v : {v // v ∉ U}, (1 + a v))
        = (∏ v ∈ hfin.toFinset, (1 + a v)) * ∏' v : {v // v ∉ W}, (1 + a v))
    (hw1mu : ∃ μAd : Measure (AdeleRing (𝓞 F) F),
      μAd.IsAddHaarMeasure ∧ μAd (adelicBox F) = 1)
    (hw1nu : ∃ ν : Measure (AdeleRing (𝓞 F) F)ˣ, ν.IsHaarMeasure)
    (hw1psi : ∃ ψ : AddChar (AdeleRing (𝓞 F) F) ℂ, IsGlobalAddChar F ψ ∧
      ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        L s = (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  classical
  set T : Finset (HeightOneSpectrum (𝓞 F)) := S ∪ hα.toFinset with hT
  have hST : (↑S : Set (HeightOneSpectrum (𝓞 F))) ⊆ ↑T := by
    intro v hv
    simp only [hT, Finset.coe_union, Set.mem_union]
    exact Or.inl hv
  have hunramT : ∀ v ∉ T, IsUnramifiedCharAt χ v := by
    intro v hvT
    by_contra hram
    refine hvT ?_
    simp only [hT, Finset.mem_union]
    exact Or.inr (hα.mem_toFinset.mpr hram)
  obtain ⟨μAd, hμAdH, hμAdBox⟩ := hw1mu
  obtain ⟨ν, hνH⟩ := hw1nu
  obtain ⟨ψ, hψG, hψinf⟩ := hw1psi
  haveI := hμAdH
  haveI := hνH
  set μf : (v : HeightOneSpectrum (𝓞 F)) → Measure (v.adicCompletion F) := fun v =>
    Measure.addHaarMeasure (Classical.choice
      (inferInstance : Nonempty (TopologicalSpace.PositiveCompacts (v.adicCompletion F))))
    with hμf
  haveI hμfH : ∀ v, (μf v).IsAddHaarMeasure := fun v =>
    Measure.isAddHaarMeasure_addHaarMeasure _
  choose εR τR hclR using hclassR
  choose kC τC hclC using hclassC
  set aM : {w : InfinitePlace F // w.IsReal} → ZMod 2 := fun wR =>
    if εR wR.1 wR.2 then 1 else 0 with haM
  set kM : {w : InfinitePlace F // w.IsComplex} → ℤ := fun wC => kC wC.1 wC.2 with hkM
  choose Bv hBclopen hBcpt Cv hCne hCval using fun v => hβ v (μf v) (hμfH v)
  have hBo : ∀ v ∈ T, IsOpen (Bv v) := fun v _ => (hBclopen v).2
  have hBc : ∀ v ∈ T, IsClosed (Bv v) := fun v _ => (hBclopen v).1
  have hBcp : ∀ v ∈ T, IsCompact (Bv v) := fun v _ => hBcpt v
  have hfact := isFactorizable_d3Witness T Bv aM kM
  have hfSB : d3Witness T Bv aM kM ∈ schwartzBruhat F :=
    d3Witness_mem_schwartzBruhat (M4aLocalCFT.G2Proof.unifOf ϖ hϖ) hBo hBc hBcp aM kM
  obtain ⟨c, hc0, hG2⟩ :=
    NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq F ν T μf archMeas ϖ hϖ
  obtain ⟨Z, hZmero, hZeq, _hZfe⟩ :=
    NumberField.TateGlobal.zetaIntegral_meromorphic_continuation_fe F ν μAd hμAdBox
      ψ hψG hψinf hfSB hχc hχu hχF
  set rR : {w : InfinitePlace F // w.IsReal} → ℂ := fun wR =>
    Complex.I * ((τR wR.1 wR.2 : ℝ) : ℂ) + (if εR wR.1 wR.2 then 1 else 0) with hrR
  set rC : {w : InfinitePlace F // w.IsComplex} → ℂ := fun wC =>
    (Complex.I * ((τC wC.1 wC.2 : ℝ) : ℂ) + ((kC wC.1 wC.2).natAbs : ℂ)) / 2 with hrC
  have hrR_re : ∀ wR, 0 ≤ (rR wR).re := by
    intro wR
    show (0:ℝ) ≤ (Complex.I * ((τR wR.1 wR.2 : ℝ) : ℂ)
      + (if εR wR.1 wR.2 then 1 else 0)).re
    rw [Complex.add_re]
    have hIτ : (Complex.I * ((τR wR.1 wR.2 : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hIτ, zero_add]
    by_cases hε : εR wR.1 wR.2 <;> simp [hε]
  have hrC_re : ∀ wC, 0 ≤ (rC wC).re := by
    intro wC
    show (0:ℝ) ≤ ((Complex.I * ((τC wC.1 wC.2 : ℝ) : ℂ)
      + ((kC wC.1 wC.2).natAbs : ℂ)) / 2).re
    have h2 : ((Complex.I * ((τC wC.1 wC.2 : ℝ) : ℂ) + ((kC wC.1 wC.2).natAbs : ℂ)) / 2)
        = (Complex.I * ((τC wC.1 wC.2 : ℝ) : ℂ) + ((kC wC.1 wC.2).natAbs : ℂ)) * (2⁻¹ : ℂ) := by
      ring
    rw [h2, Complex.mul_re]
    have hIτ : (Complex.I * ((τC wC.1 wC.2 : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    have h2inv : ((2⁻¹ : ℂ)).im = 0 := by
      norm_num
    rw [Complex.add_re, hIτ, zero_add, h2inv, mul_zero, sub_zero]
    have hk : (((kC wC.1 wC.2).natAbs : ℂ)).re = ((kC wC.1 wC.2).natAbs : ℝ) := by
      simp
    have h2r : ((2⁻¹ : ℂ)).re = (2⁻¹ : ℝ) := by
      norm_num
    rw [hk, h2r]
    positivity
  have hreR : ∀ (s : ℂ), 1 < s.re → ∀ wR, 0 < (s + rR wR).re := by
    intro s hs wR
    rw [Complex.add_re]
    have := hrR_re wR
    linarith
  have hreC : ∀ (s : ℂ), 1 < s.re → ∀ wC, 0 < (s + rC wC).re := by
    intro s hs wC
    rw [Complex.add_re]
    have := hrC_re wC
    linarith
  have harchR : ∀ (s : ℂ), 1 < s.re → ∀ (wR : {w : InfinitePlace F // w.IsReal}),
      localZeta (archMeas wR.1) (archFactor aM kM wR.1) (archLocalChar χ wR.1) s
        = Complex.Gammaℝ (s + rR wR) := by
    intro s hs wR
    have hre0 : 0 < (s + Complex.I * ((τR wR.1 wR.2 : ℝ) : ℂ)
        + (if εR wR.1 wR.2 then 1 else 0)).re := by
      rw [add_assoc]
      exact hreR s hs wR
    have h := hevalR wR.2 (εR wR.1 wR.2) (τR wR.1 wR.2) (archLocalChar χ wR.1)
      (hclR wR.1 wR.2) s hre0
    rw [add_assoc] at h
    rw [archMeas_real wR.2, archFactor_real aM kM wR.2]
    exact h
  have harchC : ∀ (s : ℂ), 1 < s.re → ∀ (wC : {w : InfinitePlace F // w.IsComplex}),
      localZeta (archMeas wC.1) (archFactor aM kM wC.1) (archLocalChar χ wC.1) s
        = (Real.pi : ℂ) * Complex.Gammaℂ (s + rC wC) := by
    intro s hs wC
    have hre0 : 0 < (s + (Complex.I * ((τC wC.1 wC.2 : ℝ) : ℂ)
        + ((kC wC.1 wC.2).natAbs : ℂ)) / 2).re := hreC s hs wC
    have h := hevalC wC.2 (kC wC.1 wC.2) (τC wC.1 wC.2) (archLocalChar χ wC.1)
      (hclC wC.1 wC.2) s hre0
    rw [archMeas_cx wC.2, archFactor_cx aM kM wC.2]
    exact h
  have harchprod : ∀ (s : ℂ), 1 < s.re →
      (∏ w, localZeta (archMeas w) (archFactor aM kM w) (archLocalChar χ w) s)
        = (∏ wR : {w : InfinitePlace F // w.IsReal}, Complex.Gammaℝ (s + rR wR))
          * ∏ wC : {w : InfinitePlace F // w.IsComplex},
              (Real.pi : ℂ) * Complex.Gammaℂ (s + rC wC) := by
    intro s hs
    rw [prod_places_split
      (fun w => localZeta (archMeas w) (archFactor aM kM w) (archLocalChar χ w) s)]
    congr 1
    · exact Finset.prod_congr rfl fun wR _ => harchR s hs wR
    · exact Finset.prod_congr rfl fun wC _ => harchC s hs wC
  set CT : ℂ := ∏ v ∈ T, Cv v with hCT
  have hCTne : CT ≠ 0 := by
    rw [hCT]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => hCne v
  set Dinv : ℂ → ℂ := fun s =>
    (((c : ℝ) : ℂ) * CT)⁻¹
      * ((∏ wR : {w : InfinitePlace F // w.IsReal}, invGR (rR wR) s)
        * ∏ wC : {w : InfinitePlace F // w.IsComplex}, invGC (rC wC) s) with hDinv
  set TScorr : ℂ → ℂ := fun s =>
    ∏ v ∈ T \ S, (1 - ((localChar χ v (ϖ v) : ℂˣ) : ℂ)
      * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)) with hTS
  set L : ℂ → ℂ := fun s => Z s * Dinv s * (TScorr s)⁻¹ with hL
  have hNne : ∀ v : HeightOneSpectrum (𝓞 F), ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 :=
    fun v => Nat.cast_ne_zero.mpr
      (lt_trans Nat.zero_lt_one (ShellBound.one_lt_absNorm v)).ne'
  refine ⟨L, ?_, ?_⟩
  ·
    have hDdiff : Differentiable ℂ Dinv := by
      rw [hDinv]
      refine Differentiable.const_mul (Differentiable.mul ?_ ?_) _
      · exact differentiable_finset_prod _ _ fun wR _ => differentiable_invGR (rR wR)
      · exact differentiable_finset_prod _ _ fun wC _ => differentiable_invGC (rC wC)
    have hTSdiff : Differentiable ℂ TScorr := by
      rw [hTS]
      refine differentiable_finset_prod _ _ fun v _ => ?_
      refine (differentiable_const (1 : ℂ)).sub ?_
      exact Differentiable.const_mul
        (Differentiable.const_cpow differentiable_neg (Or.inl (hNne v))) _
    rw [hL]
    exact (hZmero.mul
        ((hDdiff.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn)).mul
      (((hTSdiff.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn).inv)
  ·
    intro s hs
    have hkey := hG2 (d3Witness T Bv aM kM) (archFactor aM kM)
      (fun v => (Bv v).indicator 1) hfact χ hχc hχu hunramT s hs
    rw [harchprod s hs] at hkey
    have hfinprod : (∏ v ∈ T, localZeta (μf v) ((Bv v).indicator 1) (localChar χ v) s)
        = CT := by
      rw [hCT]
      exact Finset.prod_congr rfl fun v _ => hCval v s
    rw [hfinprod] at hkey
    set PR : ℂ := ∏ wR : {w : InfinitePlace F // w.IsReal},
      Complex.Gammaℝ (s + rR wR) with hPR
    set PC : ℂ := ∏ wC : {w : InfinitePlace F // w.IsComplex},
      (Real.pi : ℂ) * Complex.Gammaℂ (s + rC wC) with hPC
    set PRi : ℂ := ∏ wR : {w : InfinitePlace F // w.IsReal}, invGR (rR wR) s with hPRi
    set PCi : ℂ := ∏ wC : {w : InfinitePlace F // w.IsComplex}, invGC (rC wC) s with hPCi
    have hPRcancel : PR * PRi = 1 := by
      rw [hPR, hPRi, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun wR _ => Gammaℝ_mul_invGR (rR wR) s (hreR s hs wR)
    have hPCcancel : PC * PCi = 1 := by
      rw [hPC, hPCi, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun wC _ => piGammaℂ_mul_invGC (rC wC) s (hreC s hs wC)
    have hcne : ((c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hc0.ne'
    have hDR : Dinv s * (((c : ℝ) : ℂ) * (PR * PC) * CT) = 1 := by
      rw [hDinv]
      calc (((c : ℝ) : ℂ) * CT)⁻¹ * (PRi * PCi) * (((c : ℝ) : ℂ) * (PR * PC) * CT)
          = ((((c : ℝ) : ℂ) * CT)⁻¹ * (((c : ℝ) : ℂ) * CT))
            * ((PR * PRi) * (PC * PCi)) := by ring
        _ = 1 := by
            rw [inv_mul_cancel₀ (mul_ne_zero hcne hCTne), hPRcancel, hPCcancel]
            norm_num
    have hsum := summable_norm_eulerTerm χ hχu ϖ hs
    have hTSfin : ((↑T : Set (HeightOneSpectrum (𝓞 F))) \ ↑S).Finite :=
      Set.Finite.subset T.finite_toSet Set.diff_subset
    have hpeel := hδpeel (fun v => -(((localChar χ v (ϖ v) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))) hsum ↑S ↑T hST hTSfin
    have hconvS := tprod_conv S (fun v => ((localChar χ v (ϖ v) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
    have hconvT := tprod_conv T (fun v => ((localChar χ v (ϖ v) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s))
    have htofin : hTSfin.toFinset = T \ S := by
      ext v
      simp [Finset.mem_sdiff]
    have hTSeq : (∏ v ∈ hTSfin.toFinset, (1 + -(((localChar χ v (ϖ v) : ℂˣ) : ℂ)
        * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-s)))) = TScorr s := by
      rw [htofin, hTS]
      exact Finset.prod_congr rfl fun v _ => by rw [← sub_eq_add_neg]
    have hsplit : (∏' v : {v // v ∉ S},
        (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
          * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
        = TScorr s * (∏' v : {v // v ∉ T},
            (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
      rw [hconvS, hpeel, hTSeq, hconvT]
    have hzD : zetaIntegral ν (d3Witness T Bv aM kM) χ s * Dinv s
        = (∏' v : {v // v ∉ T},
            (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
              * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
      have h1 : zetaIntegral ν (d3Witness T Bv aM kM) χ s * Dinv s
          * (∏' v : {v // v ∉ T},
              (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) = 1 := by
        calc zetaIntegral ν (d3Witness T Bv aM kM) χ s * Dinv s
              * (∏' v : {v // v ∉ T},
                  (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))
            = Dinv s * (zetaIntegral ν (d3Witness T Bv aM kM) χ s
              * ∏' v : {v // v ∉ T},
                  (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
                    * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by ring
          _ = Dinv s * (((c : ℝ) : ℂ) * (PR * PC) * CT) := by rw [hkey]
          _ = 1 := hDR
      exact eq_inv_of_mul_eq_one_left h1
    rw [hL]
    show Z s * Dinv s * (TScorr s)⁻¹ = _
    rw [hZeq s hs, hzD, hsplit, mul_inv]
    ring

private theorem d3_solution_preview
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        L s = (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ)
            * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ := by
  refine exists_meromorphicOn_eq_partialEulerProduct_core S ϖ hϖ χ hχc hχu hχF
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  ·
    exact M4aD3Glue.unramified_cofinite_of_continuous F χ hχc
  ·
    exact fun w hw => M4aD3Glue.realUnits_char_classification_of_gamma1b
      (fun u hadd hcont => M4aD3Glue.circleHom_eq_exp u hadd hcont)
      (pulledRealChar χ hw) (continuous_pulledRealChar χ hχc hw)
      (norm_pulledRealChar χ hχu hw)
  ·
    exact fun w hw => M4aD3Glue.complexUnits_char_classification_of_gamma1b
      (fun u hadd hcont => M4aD3Glue.circleHom_eq_exp u hadd hcont)
      (pulledCxChar χ hw) (continuous_pulledCxChar χ hχc hw)
      (norm_pulledCxChar χ hχu hw)
  ·
    intro v μ hμ
    haveI := hμ
    refine M4aD3Glue.exists_localZeta_indicator_const F v μ χ hχc ?_ ?_
    ·
      intro u hu hui
      rw [M4aLocalCFT.LocalZetaUnramified.modulus_coe_units_adicCompletion]
      have hzero : M4aLocalCFT.ValuationOrd.ord (v.adicCompletionIntegers F)
          (Additive.ofMul u) = 0 := by
        rw [M4aLocalCFT.ValuationOrd.ord_eq_zero_iff]
        refine ⟨Units.mk ⟨(u : v.adicCompletion F), hu⟩
          ⟨((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), hui⟩
          (Subtype.ext (by simp)) (Subtype.ext (by simp)), Units.ext rfl⟩
      rw [hzero]
      simp
    ·
      exact NumberField.isCompactAdicCompletionIntegers F v
  ·
    intro w hw ε τ χw hχw s hs
    have h1 := M4aD3Glue.localZeta_realPlace hw volume
      (fun z => realTestFun (if ε then (1 : ZMod 2) else 0) (ringEquivRealOfIsReal hw z)) χw s
    have h2 : (fun y : ℝ => realTestFun (if ε then (1 : ZMod 2) else 0)
        (ringEquivRealOfIsReal hw (M4aD3Glue.realPlaceMeasurableEquiv hw y)))
        = realTestFun (if ε then (1 : ZMod 2) else 0) := by
      funext y
      rw [show (M4aD3Glue.realPlaceMeasurableEquiv hw y : w.Completion)
        = (ringEquivRealOfIsReal hw).symm y from rfl, RingEquiv.apply_symm_apply]
    rw [h2] at h1
    rw [← LanglandsTunnell.TateLocal.realZeta_eq_localZeta] at h1
    rw [M4aD3Glue.realZeta_classified_eval ε τ _ hχw s hs] at h1
    exact h1
  ·
    intro w hw k τ χw hχw s hs
    have h1 := M4aD3Glue.localZeta_complexPlace hw ((2 : ℝ≥0∞) • volume)
      (fun z => complexTestFun k (ringEquivComplexOfIsComplex hw z)) χw s
    have h2 : (fun y : ℂ => complexTestFun k
        (ringEquivComplexOfIsComplex hw (M4aD3Glue.complexPlaceMeasurableEquiv hw y)))
        = complexTestFun k := by
      funext y
      rw [show (M4aD3Glue.complexPlaceMeasurableEquiv hw y : w.Completion)
        = (ringEquivComplexOfIsComplex hw).symm y from rfl, RingEquiv.apply_symm_apply]
    rw [h2] at h1
    rw [← LanglandsTunnell.TateLocal.complexZeta_eq_localZeta] at h1
    rw [M4aD3Glue.complexZeta_classified_eval k τ _ hχw s hs] at h1
    exact h1
  ·
    exact fun a hsum U W hsub hfin => M4aD3Glue.tprod_subtype_peel a hsum U W hsub hfin
  ·
    exact M4aD3Glue.w1_mu F
  ·
    exact M4aD3Glue.w1_nu F
  ·
    exact M4aD3Glue.w1_psi F

end TateGlobal.IdeleCharGlue
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal.IdeleCharGlue"
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal"

end
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal.IdeleCharGlue"

end FoldSpine
p2m_reactivate "P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT.LocalZetaUnramified P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aLocalCFT P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.M4aD3Glue P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.TateGlobal.IdeleCharGlue"

open _root_.NumberField _root_.P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField AutomorphicForm IsDedekindDomain _root_.NumberField.TateGlobal _root_.P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct.NumberField.TateGlobal in

theorem solution (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (ϖ : (v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletion F)ˣ)
    (hϖ : ∀ v, Valued.v (ϖ v : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ))
    (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    (hχF : IsIdeleClassChar (𝓞 F) F χ) :
    ∃ L : ℂ → ℂ, MeromorphicOn L Set.univ ∧
      ∀ s : ℂ, 1 < s.re →
        L s = (∏' v : {v // v ∉ S},
          (1 - ((localChar χ v.1 (ϖ v.1) : ℂˣ) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)))⁻¹ :=
  TateGlobal.IdeleCharGlue.d3_solution_preview (F := F) S ϖ hϖ χ hχc hχu hχF

end S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct (solution)
