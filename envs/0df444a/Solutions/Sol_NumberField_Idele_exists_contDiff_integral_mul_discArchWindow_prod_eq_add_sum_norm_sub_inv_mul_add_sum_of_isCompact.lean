-- Prove2me | solution 1 for NumberField.Idele.exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/49fd7a5a-2912-5081-81ea-fbf37c49b142

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_NumberField_AdelicLevel

import Theorems.Thm_NumberField_mixedEmbedding_contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units
import Theorems.Thm_NumberField_Idele_integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
import Theorems.Thm_NumberField_Idele_contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
import Theorems.Thm_NumberField_Idele_integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_Idele_exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain

set_option linter.unusedSectionVars false

namespace NumCore

theorem norm_sub_one_mul_inv_kink {F : Type*} [NormedField F] (x : F) (hx0 : x ≠ 0) (hx1 : x ≠ 1) :
    ‖x - 1‖ * (‖1 - x⁻¹‖ / Real.sqrt ‖x⁻¹‖)⁻¹ = Real.sqrt ‖x‖ := by
  have h1 : 1 - x⁻¹ = x⁻¹ * (x - 1) := by field_simp
  have hn : ‖x - 1‖ ≠ 0 := by rw [norm_ne_zero_iff]; exact sub_ne_zero.2 hx1
  have hxn : 0 < ‖x‖ := norm_pos_iff.2 hx0
  rw [h1, norm_mul, norm_inv, Real.sqrt_inv]
  have hs : Real.sqrt ‖x‖ ≠ 0 := (Real.sqrt_pos.2 hxn).ne'
  have hsq : Real.sqrt ‖x‖ * Real.sqrt ‖x‖ = ‖x‖ := Real.mul_self_sqrt hxn.le
  field_simp
  nlinarith [hsq, hs, hn, hxn]

theorem arch_kink_ratio (K : Type) [Field K] [NumberField K] (u : Kˣ) (hu : (u : K) ≠ 1) :
    (((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) *
      ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) -
          AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ /
          Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K
            (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ =
    (((∏ w : InfinitePlace K, (Real.sqrt ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w‖) ^ w.mult : ℝ)) : ℂ) := by
  have hcomp : ∀ (x : K) (w : InfinitePlace K),
      AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) x) w = algebraMap K w.Completion x := fun x w => rfl
  have hev : ∀ (w : InfinitePlace K) (y : InfiniteAdeleRing K), NumberField.AdelicLevel.archEval K w y = y w := fun w y => rfl
  have hsub : ∀ (y y' : InfiniteAdeleRing K) (w : InfinitePlace K), (y - y') w = y w - y' w := fun _ _ _ => rfl
  have hone : ∀ w : InfinitePlace K, (1 : InfiniteAdeleRing K) w = 1 := fun _ => rfl
  simp only [hev, hsub, hone, hcomp, Units.val_inv_eq_inv_val, map_inv₀]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul]
  congr 1
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hx0 : algebraMap K w.Completion (u : K) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap K w.Completion).injective]; exact u.ne_zero
  have hx1 : algebraMap K w.Completion (u : K) ≠ 1 := by
    rw [Ne, ← (algebraMap K w.Completion).map_one, (algebraMap K w.Completion).injective.eq_iff]; exact hu
  rw [← inv_pow, ← mul_pow, NumCore.norm_sub_one_mul_inv_kink _ hx0 hx1]

end NumCore

namespace ArchFold

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

section Scalar

variable (K : Type) [Field K] [NumberField K]

theorem normAtPlace_ringEquiv (x : InfiniteAdeleRing K) (w : InfinitePlace K) :
    normAtPlace w (InfiniteAdeleRing.ringEquiv_mixedSpace K x) = ‖x w‖ := by
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  by_cases hw : IsReal w
  · rw [normAtPlace_apply_of_isReal hw]
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) _
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

noncomputable def cT (y : mixedSpace K) : ℂ :=
  ((∏ w : InfinitePlace K, (Real.sqrt (normAtPlace w y)) ^ w.mult : ℝ) : ℂ)

theorem cT_ringEquiv (x : InfiniteAdeleRing K) :
    cT K (InfiniteAdeleRing.ringEquiv_mixedSpace K x) = ((∏ w : InfinitePlace K, (Real.sqrt ‖x w‖) ^ w.mult : ℝ) : ℂ) := by
  simp only [cT, normAtPlace_ringEquiv]

theorem fst_ne_zero_of_isUnit {y : mixedSpace K} (hy : IsUnit y) (i : {w : InfinitePlace K // IsReal w}) : y.1 i ≠ 0 :=
  ((hy.map (RingHom.fst _ _)).map (Pi.evalRingHom _ i)).ne_zero

theorem snd_ne_zero_of_isUnit {y : mixedSpace K} (hy : IsUnit y) (i : {w : InfinitePlace K // IsComplex w}) : y.2 i ≠ 0 :=
  ((hy.map (RingHom.snd _ _)).map (Pi.evalRingHom _ i)).ne_zero

theorem contDiffAt_normAtPlace (w : InfinitePlace K) {y : mixedSpace K} (hy : IsUnit y) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => normAtPlace w y) y := by
  by_cases hw : IsReal w
  · have h : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.1 ⟨w, hw⟩‖ :=
      funext fun y => normAtPlace_apply_of_isReal hw y
    rw [h]
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => y.1 ⟨w, hw⟩) y :=
      ((contDiffAt_apply ℝ ℝ (⟨w, hw⟩ : {w : InfinitePlace K // IsReal w}) y.1).comp y contDiffAt_fst)
    exact (contDiffAt_norm ℝ (fst_ne_zero_of_isUnit K hy ⟨w, hw⟩)).comp y h1
  · have hw' : IsComplex w := not_isReal_iff_isComplex.mp hw
    have h : (fun y : mixedSpace K => normAtPlace w y) = fun y => ‖y.2 ⟨w, hw'⟩‖ :=
      funext fun y => normAtPlace_apply_of_isComplex hw' y
    rw [h]
    have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => y.2 ⟨w, hw'⟩) y :=
      ((contDiffAt_apply ℝ ℂ (⟨w, hw'⟩ : {w : InfinitePlace K // IsComplex w}) y.2).comp y contDiffAt_snd)
    exact (contDiffAt_norm ℝ (snd_ne_zero_of_isUnit K hy ⟨w, hw'⟩)).comp y h1

theorem normAtPlace_pos_of_isUnit (w : InfinitePlace K) {y : mixedSpace K} (hy : IsUnit y) : 0 < normAtPlace w y := by
  by_cases hw : IsReal w
  · rw [normAtPlace_apply_of_isReal hw]; exact norm_pos_iff.2 (fst_ne_zero_of_isUnit K hy ⟨w, hw⟩)
  · rw [normAtPlace_apply_of_isComplex (not_isReal_iff_isComplex.mp hw)]
    exact norm_pos_iff.2 (snd_ne_zero_of_isUnit K hy ⟨w, _⟩)

theorem contDiffAt_cT {y : mixedSpace K} (hy : IsUnit y) : ContDiffAt ℝ (⊤ : ℕ∞) (cT K) y := by
  unfold cT
  refine (Complex.ofRealCLM.contDiff.contDiffAt).comp y ?_
  refine contDiffAt_prod fun w _ => ?_
  refine ContDiffAt.pow ?_ _
  exact (Real.contDiffAt_sqrt (normAtPlace_pos_of_isUnit K w hy).ne').comp y (contDiffAt_normAtPlace K w hy)

end Scalar

end ArchFold

namespace ArchFold

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

section Piece

variable (K : Type) [Field K] [NumberField K]
  [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
  (ν : Measure (AdeleRing (𝓞 K) K)ˣ) [ν.IsHaarMeasure]
  (S : Finset (HeightOneSpectrum (𝓞 K)))
  (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
  (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
  (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
  (hΦf : ∀ v ∈ S, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧ ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0)

noncomputable def FI (Φa : (Fin 2 → mixedSpace K) → ℂ) (x : mixedSpace K)
    (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) : ℂ :=
  ∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
      (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
        ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
    ∂(Measure.map (NumberField.Idele.partAt K S)
        (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))

omit hξc hΦf in
theorem continuous_ringEquiv_units :
    Continuous fun q : (InfiniteAdeleRing K)ˣ => InfiniteAdeleRing.ringEquiv_mixedSpace K (q : InfiniteAdeleRing K) := by
  have h : (fun x : InfiniteAdeleRing K => InfiniteAdeleRing.ringEquiv_mixedSpace K x) =
      fun x => ((fun (v : {w : InfinitePlace K // IsReal w}) => Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun (v : {w : InfinitePlace K // IsComplex w}) => Completion.extensionEmbedding v.1 (x v))) := by
    funext x; exact InfiniteAdeleRing.ringEquiv_mixedSpace_apply K x
  have hc : Continuous fun x : InfiniteAdeleRing K => InfiniteAdeleRing.ringEquiv_mixedSpace K x := by
    rw [h]
    exact (continuous_pi fun v => (Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
        (continuous_apply v.1)).prodMk
      (continuous_pi fun v => (Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply v.1))
  exact hc.comp Units.continuous_val

include hξc hΦf in

theorem piece (Φa : (Fin 2 → mixedSpace K) → ℂ) (hΦa : ContDiff ℝ (⊤ : ℕ∞) Φa) (hΦac : HasCompactSupport Φa)
    (Cp : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCp : IsCompact Cp)
    (hsupp : ∀ p ∈ tsupport Φa, ∃ q ∈ Cp,
      p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K),
            InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) :
    (∀ b, ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedSpace K => cT K y * FI K ν S ξ Φf Φa (Ring.inverse y) b)) ∧
    (∀ (y : mixedSpace K) b, y ∉ Ring.inverse '' ((fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
        InfiniteAdeleRing.ringEquiv_mixedSpace K ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) '' Cp) →
      cT K y * FI K ν S ξ Φf Φa (Ring.inverse y) b = 0) ∧
    (∀ y : mixedSpace K, IsLocallyConstant (fun b => cT K y * FI K ν S ξ Φf Φa (Ring.inverse y) b)) ∧
    (∃ Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K),
      (∀ v ∈ S, IsCompact (Cf v) ∧ (0 : v.adicCompletion K) ∉ Cf v) ∧
      ∀ (y : mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K), (∃ v ∈ S, b v ∉ Cf v) →
        cT K y * FI K ν S ξ Φf Φa (Ring.inverse y) b = 0) ∧
    (∀ (x : mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K),
      Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
        (Φa ![x, InfiniteAdeleRing.ringEquiv_mixedSpace K ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
          ∏ v ∈ S, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))
        (Measure.map (NumberField.Idele.partAt K S)
          (ν.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S) : Set (AdeleRing (𝓞 K) K)ˣ)))) := by
  set RE := InfiniteAdeleRing.ringEquiv_mixedSpace K with hRE

  set Ca : Set (InfiniteAdeleRing K)ˣ := Prod.snd '' Cp with hCa
  have hCac : IsCompact Ca := hCp.image continuous_snd
  have hΦa0 : ∀ p : Fin 2 → mixedSpace K, Φa p ≠ 0 → RE.symm (p 1) ∈ Units.val '' Ca := by
    intro p hp
    obtain ⟨q, hq, hpq⟩ := hsupp p (subset_tsupport _ (Function.mem_support.2 hp))
    refine ⟨q.2, ⟨q, hq, rfl⟩, ?_⟩
    have h1 : p 1 = RE q.2 := by rw [hpq]; rfl
    rw [h1, RingEquiv.symm_apply_apply]

  obtain ⟨h1, -, h3, Cf, hCf, h4⟩ :=
    NumberField.Idele.contDiff_and_exists_isCompact_and_isLocallyConstant_integral_mul_window_prod_map_partAt_of_isCompact
      K ν S ξ hξc Φa hΦa hΦac Ca hCac hΦa0 Φf hΦf

  set C₀ : Set (mixedSpace K) := (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      RE ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) '' Cp with hC₀
  have hC₀c : IsCompact C₀ := hCp.image ((continuous_ringEquiv_units K).comp continuous_fst)
  have hC₀u : ∀ y ∈ C₀, IsUnit y := by
    rintro _ ⟨q, -, rfl⟩
    exact q.1.isUnit.map RE
  have hF0 : ∀ (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) (x : mixedSpace K),
      FI K ν S ξ Φf Φa x b ≠ 0 → x ∈ C₀ := by
    intro b x hx
    by_contra hxC
    apply hx
    have hz : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        Φa ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] = 0 := by
      intro zS
      by_contra hne
      obtain ⟨q, hq, hpq⟩ := hsupp _ (subset_tsupport _ (Function.mem_support.2 hne))
      have : x = RE q.1 := by have := congr_fun hpq 0; simpa using this
      exact hxC ⟨q, hq, this.symm⟩
    simp only [FI, hRE ▸ hz, zero_mul, mul_zero, integral_zero]

  have hIW := (NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units K).1
  refine ⟨fun b => ?_, fun y b hy => ?_, fun y => ?_, ⟨Cf, hCf, fun y b hb => ?_⟩, fun x b => ?_⟩
  ·
    obtain ⟨hcd, hKc, hKu, hvan⟩ := hIW (fun x => FI K ν S ξ Φf Φa x b) (h1 b) C₀ hC₀c hC₀u (hF0 b)
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : IsUnit y
    · exact (contDiffAt_cT K hy).mul hcd.contDiffAt
    · have hyK : y ∉ Ring.inverse '' C₀ := fun h => hy (hKu y h)
      have hev : (fun y : mixedSpace K => cT K y * FI K ν S ξ Φf Φa (Ring.inverse y) b) =ᶠ[nhds y] fun _ => 0 := by
        filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hyK] with y' hy'
        have : FI K ν S ξ Φf Φa (Ring.inverse y') b = 0 := by
          by_contra h; exact hy' (hvan y' h)
        rw [this, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  ·
    obtain ⟨-, -, -, hvan⟩ := hIW (fun x => FI K ν S ξ Φf Φa x b) (h1 b) C₀ hC₀c hC₀u (hF0 b)
    have : FI K ν S ξ Φf Φa (Ring.inverse y) b = 0 := by
      by_contra h; exact hy (hvan y h)
    rw [this, mul_zero]
  ·
    exact (h3 (Ring.inverse y)).comp (fun t => cT K y * t)
  ·
    have : FI K ν S ξ Φf Φa (Ring.inverse y) b = 0 := h4 (Ring.inverse y) b hb
    rw [this, mul_zero]
  ·
    have hG : ContDiff ℝ (⊤ : ℕ∞) (fun p : mixedSpace K × mixedSpace K => Φa ![p.1, p.2]) := by
      refine hΦa.comp ?_
      refine contDiff_pi.2 fun i => ?_
      fin_cases i
      · simpa using contDiff_fst
      · simpa using contDiff_snd
    have hGc : HasCompactSupport (fun p : mixedSpace K × mixedSpace K => Φa ![p.1, p.2]) := by
      have h := hΦac.comp_homeomorph (Homeomorph.piFinTwo (fun _ : Fin 2 => mixedSpace K)).symm
      have heq : (fun p : mixedSpace K × mixedSpace K => Φa ![p.1, p.2]) =
          Φa ∘ ⇑(Homeomorph.piFinTwo (fun _ : Fin 2 => mixedSpace K)).symm := by
        funext p
        simp only [Function.comp_apply]
        exact congrArg Φa (funext fun i => by fin_cases i <;> rfl)
      rw [heq]; exact h
    have hG0 : ∀ (x : mixedSpace K) (y : InfiniteAdeleRing K),
        (fun p : mixedSpace K × mixedSpace K => Φa ![p.1, p.2]) (x, RE y) ≠ 0 → y ∈ Units.val '' Ca := by
      intro x y h
      have := hΦa0 _ h
      simpa using this
    exact (NumberField.Idele.integrable_and_contDiff_integral_mul_comp_ringEquiv_mixedSpace_mul_prod_map_partAt K ν S
      (fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) hξc
      (fun p : mixedSpace K × mixedSpace K => Φa ![p.1, p.2]) hG hGc Ca hCac hG0 Φf hΦf b).1 x

end Piece

end ArchFold

namespace ArchFold

open NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical

section Main

theorem ringInverse_RE_inv (K : Type) [Field K] [NumberField K] (u : Kˣ) :
    Ring.inverse (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))) := by
  have h : InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))) *
      InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K))) = 1 := by
    rw [← map_mul, ← map_mul, ← map_mul, Units.inv_mul, map_one, map_one, map_one]
  rw [show InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))) =
      ((Units.mkOfMulEqOne _ _ h : (mixedSpace K)ˣ) : mixedSpace K) from rfl, Ring.inverse_unit]
  rfl

theorem ringInverse_RE (K : Type) [Field K] [NumberField K] (u : Kˣ) :
    Ring.inverse (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) =
      InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))) := by
  have := ringInverse_RE_inv K u⁻¹
  rw [inv_inv] at this
  exact this

end Main

end ArchFold

open ArchFold NumberField.InfinitePlace NumberField.mixedEmbedding in
open scoped Classical in
set_option maxHeartbeats 6400000 in
theorem solution
    (K : Type) [Field K] [NumberField K]
    [MeasurableSpace (AdeleRing (𝓞 K) K)ˣ] [BorelSpace (AdeleRing (𝓞 K) K)ˣ]
    (νZK : Measure (AdeleRing (𝓞 K) K)ˣ) [νZK.IsHaarMeasure]
    (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ)
    (hξc : Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ))
    (Bd : (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (Cd Ed : NumberField.InfinitePlace K → (Fin 2 → mixedEmbedding.mixedSpace K) → ℂ)
    (hBd_smooth : ContDiff ℝ (⊤ : ℕ∞) Bd) (hCd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Cd w))
    (hEd_smooth : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ed w))
    (hBd_cs : HasCompactSupport Bd) (hCd_cs : ∀ w, HasCompactSupport (Cd w)) (hEd_cs : ∀ w, HasCompactSupport (Ed w))
    (CaD : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ)) (hCaD : IsCompact CaD)
    (hBCE_Ca : ∀ p ∈ tsupport Bd ∪ ⋃ w, (tsupport (Cd w) ∪ tsupport (Ed w)),
      ∃ q ∈ CaD, p = ![InfiniteAdeleRing.ringEquiv_mixedSpace K (q.1 : InfiniteAdeleRing K),
        InfiniteAdeleRing.ringEquiv_mixedSpace K (q.2 : InfiniteAdeleRing K)])
    (Φf : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K) × (v.adicCompletion K) → ℂ)
    (hΦf : ∀ v ∈ SK, IsLocallyConstant (Φf v) ∧ HasCompactSupport (Φf v) ∧ ∀ p, Φf v p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0) :
    ∃ (Bt : mixedEmbedding.mixedSpace K → ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) → ℂ)
      (Ct Et : NumberField.InfinitePlace K → mixedEmbedding.mixedSpace K → ((v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K) → ℂ),
      (∀ b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K, ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedEmbedding.mixedSpace K => Bt y b) ∧
        ∀ w, ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedEmbedding.mixedSpace K => Ct w y b) ∧ ContDiff ℝ (⊤ : ℕ∞) (fun y : mixedEmbedding.mixedSpace K => Et w y b)) ∧
      (∃ C₁ : Set (mixedEmbedding.mixedSpace K), IsCompact C₁ ∧ (∀ y ∈ C₁, IsUnit y) ∧
        ∀ (y : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K), y ∉ C₁ → Bt y b = 0 ∧ ∀ w, Ct w y b = 0 ∧ Et w y b = 0) ∧
      (∀ y : mixedEmbedding.mixedSpace K, IsLocallyConstant (Bt y) ∧ ∀ w, IsLocallyConstant (Ct w y) ∧ IsLocallyConstant (Et w y)) ∧
      (∃ Cf : ∀ v : HeightOneSpectrum (𝓞 K), Set (v.adicCompletion K),
        (∀ v ∈ SK, IsCompact (Cf v) ∧ (0 : v.adicCompletion K) ∉ Cf v) ∧
        ∀ (y : mixedEmbedding.mixedSpace K) (b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K), (∃ v ∈ SK, b v ∉ Cf v) →
          Bt y b = 0 ∧ ∀ w, Ct w y b = 0 ∧ Et w y b = 0) ∧
      ∀ (u : Kˣ), (u : K) ≠ 1 → ∀ b : (v : HeightOneSpectrum (𝓞 K)) → v.adicCompletion K,
        Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))
          (Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) ∧
        (∫ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))
          ∂(Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ)))) =
        Bt (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) b +
          ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ct w (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) b +
          ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Et w (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) b := by
  set RE := InfiniteAdeleRing.ringEquiv_mixedSpace K with hRE
  have hIW2 := (NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units K).2
    (fun _ => (1 : ℂ)) contDiffOn_const

  set Bw : (Fin 2 → mixedSpace K) → ℂ := fun p => (fun _ : mixedSpace K => (1 : ℂ)) (p 0) * Bd ![p 0, p 1 * Ring.inverse (p 0)] with hBw
  set Cw : InfinitePlace K → (Fin 2 → mixedSpace K) → ℂ :=
    fun w p => (fun _ : mixedSpace K => (1 : ℂ)) (p 0) * Cd w ![p 0, p 1 * Ring.inverse (p 0)] with hCw
  set Ew : InfinitePlace K → (Fin 2 → mixedSpace K) → ℂ :=
    fun w p => (fun _ : mixedSpace K => (1 : ℂ)) (p 0) * Ed w ![p 0, p 1 * Ring.inverse (p 0)] with hEw
  set Cp : Set ((InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ) :=
    (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ => (q.1, q.2 * q.1)) '' CaD with hCp
  have hCpc : IsCompact Cp := hCaD.image (continuous_fst.prodMk (continuous_snd.mul continuous_fst))
  have hB := hIW2 Bd hBd_smooth hBd_cs CaD hCaD (fun p hp => hBCE_Ca p (Set.mem_union_left _ hp))
  have hC : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Cw w) ∧ HasCompactSupport (Cw w) ∧ ∀ p ∈ tsupport (Cw w), ∃ q ∈ Cp,
      p = ![RE ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), RE ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] :=
    fun w => hIW2 (Cd w) (hCd_smooth w) (hCd_cs w) CaD hCaD
      (fun p hp => hBCE_Ca p (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨w, Set.mem_union_left _ hp⟩)))
  have hE : ∀ w, ContDiff ℝ (⊤ : ℕ∞) (Ew w) ∧ HasCompactSupport (Ew w) ∧ ∀ p ∈ tsupport (Ew w), ∃ q ∈ Cp,
      p = ![RE ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), RE ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)] :=
    fun w => hIW2 (Ed w) (hEd_smooth w) (hEd_cs w) CaD hCaD
      (fun p hp => hBCE_Ca p (Set.mem_union_right _ (Set.mem_iUnion.2 ⟨w, Set.mem_union_right _ hp⟩)))

  have hPB := piece K νZK SK ξ hξc Φf hΦf Bw hB.1 hB.2.1 Cp hCpc hB.2.2
  have hPC := fun w => piece K νZK SK ξ hξc Φf hΦf (Cw w) (hC w).1 (hC w).2.1 Cp hCpc (hC w).2.2
  have hPE := fun w => piece K νZK SK ξ hξc Φf hΦf (Ew w) (hE w).1 (hE w).2.1 Cp hCpc (hE w).2.2
  obtain ⟨CfB, hCfB, hCfB'⟩ := hPB.2.2.2.1
  choose CfC hCfC hCfC' using fun w => (hPC w).2.2.2.1
  choose CfE hCfE hCfE' using fun w => (hPE w).2.2.2.1

  set C₀ : Set (mixedSpace K) := (fun q : (InfiniteAdeleRing K)ˣ × (InfiniteAdeleRing K)ˣ =>
      RE ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)) '' Cp with hC₀
  have hC₀c : IsCompact C₀ := hCpc.image ((continuous_ringEquiv_units K).comp continuous_fst)
  have hC₀u : ∀ y ∈ C₀, IsUnit y := by
    rintro _ ⟨q, -, rfl⟩
    exact q.1.isUnit.map RE
  obtain ⟨-, hC₁c, hC₁u, -⟩ :=
    (NumberField.mixedEmbedding.contDiff_comp_ringInverse_and_contDiff_mul_twist_of_tsupport_subset_units K).1
      (fun _ => (0 : ℂ)) contDiff_const C₀ hC₀c hC₀u (fun y h => absurd rfl h)
  refine ⟨fun y b => cT K y * FI K νZK SK ξ Φf Bw (Ring.inverse y) b,
    fun w y b => cT K y * FI K νZK SK ξ Φf (Cw w) (Ring.inverse y) b,
    fun w y b => cT K y * FI K νZK SK ξ Φf (Ew w) (Ring.inverse y) b, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact fun b => ⟨hPB.1 b, fun w => ⟨(hPC w).1 b, (hPE w).1 b⟩⟩
  ·
    exact ⟨Ring.inverse '' C₀, hC₁c, hC₁u, fun y b hy => ⟨hPB.2.1 y b hy, fun w => ⟨(hPC w).2.1 y b hy, (hPE w).2.1 y b hy⟩⟩⟩
  ·
    exact fun y => ⟨hPB.2.2.1 y, fun w => ⟨(hPC w).2.2.1 y, (hPE w).2.2.1 y⟩⟩
  ·
    refine ⟨fun v => CfB v ∪ ⋃ w, (CfC w v ∪ CfE w v), fun v hv => ⟨?_, ?_⟩, fun y b hb => ?_⟩
    · exact (hCfB v hv).1.union (isCompact_iUnion fun w => ((hCfC w v hv).1.union (hCfE w v hv).1))
    · simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists]
      exact ⟨(hCfB v hv).2, fun w => ⟨(hCfC w v hv).2, (hCfE w v hv).2⟩⟩
    · obtain ⟨v, hv, hbv⟩ := hb
      simp only [Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hbv
      exact ⟨hCfB' y b ⟨v, hv, hbv.1⟩, fun w => ⟨hCfC' w y b ⟨v, hv, (hbv.2 w).1⟩, hCfE' w y b ⟨v, hv, (hbv.2 w).2⟩⟩⟩
  ·
    intro u hu b
    set x : mixedSpace K := RE (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))) with hx
    have hsymm : RE.symm x = AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)) := by
      rw [hx, RingEquiv.symm_apply_apply]
    have hsymm' : (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x = AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)) := hsymm

    have hCa' : IsCompact (Prod.snd '' Cp) := hCpc.image continuous_snd
    have key : ∀ (Φa : (Fin 2 → mixedSpace K) → ℂ), (∀ p ∈ tsupport Φa, ∃ q ∈ Cp,
        p = ![RE ((q.1 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K), RE ((q.2 : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K)]) →
        ∀ p, Φa p ≠ 0 → RE.symm (p 1) ∈ Units.val '' (Prod.snd '' Cp) := by
      intro Φa hs p hne
      obtain ⟨q, hq, hpq⟩ := hs p (subset_tsupport _ (Function.mem_support.2 hne))
      refine ⟨q.2, ⟨q, hq, rfl⟩, ?_⟩
      have : p 1 = RE q.2 := by rw [hpq]; rfl
      rw [this, RingEquiv.symm_apply_apply]
    have h0 : ∀ p : Fin 2 → mixedSpace K, (Bw p ≠ 0 ∨ ∃ w, Cw w p ≠ 0 ∨ Ew w p ≠ 0) →
        (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 1) ∈ Units.val '' (Prod.snd '' Cp) := by
      intro p hp
      rcases hp with h | ⟨w, h | h⟩
      · exact key Bw hB.2.2 p h
      · exact key (Cw w) (hC w).2.2 p h
      · exact key (Ew w) (hE w).2.2 p h
    have hfold := NumberField.Idele.integral_mul_kinkWindow_prod_map_partAt_eq_add_sum_real_add_sum_complex_of_isCompact
      K νZK SK ξ hξc Bw Cw Ew ⟨hB.1, hB.2.1⟩ (fun w => ⟨(hC w).1, (hC w).2.1⟩) (fun w => ⟨(hE w).1, (hE w).2.1⟩)
      (Prod.snd '' Cp) hCa' h0 Φf hΦf x b

    have hratio := NumCore.arch_kink_ratio K u hu
    have hcT : cT K (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) = (((∏ w : InfinitePlace K, (Real.sqrt ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w‖) ^ w.mult : ℝ)) : ℂ) := cT_ringEquiv K _
    have hinvRE : Ring.inverse (InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) = x := ringInverse_RE K u
    have hP : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        RE (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K)))) =
          RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1 * Ring.inverse x := by
      intro zS
      rw [hx, ringInverse_RE_inv, map_mul, map_mul]
      rfl

    have hpt : ∀ zS : (AdeleRing (𝓞 K) K)ˣ,
        ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
            (((((∏ w : InfinitePlace K, ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w - 1‖ ^ w.mult : ℝ)) : ℂ) * ((((∏ w : InfinitePlace K, (‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ / Real.sqrt ‖NumberField.AdelicLevel.archEval K w (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖) ^ w.mult : ℝ)) : ℂ))⁻¹ * (Bd ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Cd w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))] +
                  ∑ w ∈ Finset.univ.filter (fun w : InfinitePlace K => w.IsComplex),
                    ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ ^ 2 * Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K)))‖ : ℝ) : ℂ) * Ed w ![InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) ((u⁻¹ : Kˣ) : K))), InfiniteAdeleRing.ringEquiv_mixedSpace K (AdelicLevel.adeleArch (𝓞 K) K (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) * (algebraMap K (AdeleRing (𝓞 K) K) (u : K))))])) *
                ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) =
        (((∏ w : InfinitePlace K, (Real.sqrt ‖AdelicLevel.adeleArch (𝓞 K) K (algebraMap K (AdeleRing (𝓞 K) K) (u : K)) w‖) ^ w.mult : ℝ)) : ℂ) * (((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((fun p : Fin 2 → mixedSpace K =>
            Bw p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * Cw w p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * Ew w p) ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))) := by
      intro zS
      rw [hratio, hP zS]
      simp only [hBw, hCw, hEw, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul, hsymm, hsymm']
      rw [← hx]
      ring

    have hexp : ∀ zS : (AdeleRing (𝓞 K) K)ˣ, ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((fun p : Fin 2 → mixedSpace K =>
            Bw p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * Cw w p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * Ew w p) ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) =
        ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * (Bw ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] * ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)) +
        (∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal),
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ) * (((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * (Cw w ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] * ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))) +
         ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex),
            ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ ^ 2 *
              Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm x)‖ : ℝ) : ℂ) * (((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) * (Ew w ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] * ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v)))) := by
      intro zS
      simp only [Matrix.cons_val_zero]
      rw [add_mul, add_mul, mul_add, mul_add, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, add_assoc]
      congr 1
      congr 1
      · exact Finset.sum_congr rfl fun w _ => by ring
      · exact Finset.sum_congr rfl fun w _ => by ring
    have hIB := hPB.2.2.2.2 x b
    have hkint : Integrable (fun zS : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨zS, Subgroup.mem_top zS⟩ : ℂˣ) : ℂ) *
          ((fun p : Fin 2 → mixedSpace K =>
            Bw p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsReal), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * Cw w p +
            ∑ w ∈ Finset.univ.filter (fun w : NumberField.InfinitePlace K => w.IsComplex), ((‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ ^ 2 *
                Real.log ‖NumberField.AdelicLevel.archEval K w ((1 : InfiniteAdeleRing K) - (InfiniteAdeleRing.ringEquiv_mixedSpace K).symm (p 0))‖ : ℝ) : ℂ) * Ew w p) ![x, RE ((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).1] *
            ∏ v ∈ SK, Φf v (b v, (((zS : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 : FiniteAdeleRing (𝓞 K) K) v))) (Measure.map (NumberField.Idele.partAt K SK)
            (νZK.restrict (NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑SK) : Set (AdeleRing (𝓞 K) K)ˣ))) := by
      rw [funext hexp]
      exact (hIB.add ((integrable_finset_sum _ fun w _ => ((hPC w).2.2.2.2 x b).const_mul _).add
        (integrable_finset_sum _ fun w _ => ((hPE w).2.2.2.2 x b).const_mul _)))
    refine ⟨?_, ?_⟩
    · rw [funext hpt]
      exact hkint.const_mul _
    · rw [funext hpt, integral_const_mul, hfold]
      beta_reduce
      rw [hcT, hinvRE]
      simp only [FI, hsymm', mul_add, Finset.mul_sum]
      congr 1
      · congr 1
        exact Finset.sum_congr rfl fun w _ => by ring
      · exact Finset.sum_congr rfl fun w _ => by ring

end S_NumberField_Idele_exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact
end P2MW
export P2MW.S_NumberField_Idele_exists_contDiff_integral_mul_discArchWindow_prod_eq_add_sum_norm_sub_inv_mul_add_sum_of_isCompact (solution)
