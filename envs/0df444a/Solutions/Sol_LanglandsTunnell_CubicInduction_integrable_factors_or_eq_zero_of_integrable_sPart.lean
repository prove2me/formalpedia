-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.integrable_factors_or_eq_zero_of_integrable_sPart
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/017ae219-8c2e-544b-a994-4001eedd8cdf

import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt
import Theorems.Thm_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
import Theorems.Thm_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
import Theorems.Thm_NumberField_Idele_measurePreserving_mul_right_sPartMeasure
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open LanglandsTunnell

private theorem ae_zero_left_or_right_of_mul_ae_zero {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (g : X → ℂ) (h : Y → ℂ) (H : (fun p : X × Y => g p.1 * h p.2) =ᵐ[μ.prod ν] 0) :
    g =ᵐ[μ] 0 ∨ h =ᵐ[ν] 0 := by
  have H' : (μ.prod ν) {p : X × Y | ¬ g p.1 * h p.2 = 0} = 0 := by
    have := ae_iff.mp H
    simpa using this
  have hrect : (μ.prod ν) ({x | ¬ g x = 0} ×ˢ {y | ¬ h y = 0}) = 0 := by
    refine measure_mono_null ?_ H'
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact mul_ne_zero hx hy
  rw [Measure.prod_prod, mul_eq_zero] at hrect
  rcases hrect with hx | hy
  · exact Or.inl (ae_iff.mpr (by simpa using hx))
  · exact Or.inr (ae_iff.mpr (by simpa using hy))

private theorem integrable_mul_prod_or_ae_zero_left_or_right {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (g : X → ℂ) (h : Y → ℂ) (H : Integrable (fun p : X × Y => g p.1 * h p.2) (μ.prod ν)) :
    (Integrable g μ ∧ Integrable h ν) ∨ g =ᵐ[μ] 0 ∨ h =ᵐ[ν] 0 := by
  by_cases hg : g =ᵐ[μ] 0
  · exact Or.inr (Or.inl hg)
  by_cases hh : h =ᵐ[ν] 0
  · exact Or.inr (Or.inr hh)
  left
  have hm : AEStronglyMeasurable (fun p : X × Y => g p.1 * h p.2) (μ.prod ν) := H.aestronglyMeasurable
  obtain ⟨H1, H2⟩ := (integrable_prod_iff hm).mp H

  have hxg : ∃ x, g x ≠ 0 ∧ Integrable (fun y => g x * h y) ν := by
    by_contra hcon
    push Not at hcon
    apply hg
    filter_upwards [H1] with x hx
    by_contra hgx
    exact hcon x hgx hx
  obtain ⟨x₀, hgx₀, hx₀⟩ := hxg
  have hh_int : Integrable h ν := by
    refine (hx₀.const_mul (g x₀)⁻¹).congr (Filter.Eventually.of_forall fun y => ?_)
    simp [hgx₀]
  refine ⟨?_, hh_int⟩

  have hsec : ∀ᵐ y ∂ν, AEStronglyMeasurable (fun x => g x * h y) μ := hm.prodMk_right
  have hyh : ∃ y, h y ≠ 0 ∧ AEStronglyMeasurable (fun x => g x * h y) μ := by
    by_contra hcon
    push Not at hcon
    apply hh
    filter_upwards [hsec] with y hy
    by_contra hhy
    exact hcon y hhy hy
  obtain ⟨y₀, hhy₀, hy₀⟩ := hyh
  have hgm : AEStronglyMeasurable g μ := by
    refine (hy₀.mul_const (h y₀)⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [hhy₀]

  have hpos : 0 < ∫ y, ‖h y‖ ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun y => norm_nonneg (h y)) hh_int.norm]
    refine pos_iff_ne_zero.mpr fun h0 => hh ?_
    refine ae_iff.mpr ?_
    convert h0 using 2
    ext y
    simp [Function.mem_support]
  have H2' : Integrable (fun x => ‖g x‖ * ∫ y, ‖h y‖ ∂ν) μ := by
    refine H2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [norm_mul, integral_const_mul]
  have hgn : Integrable (fun x => ‖g x‖) μ := by
    refine (H2'.mul_const (∫ y, ‖h y‖ ∂ν)⁻¹).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [hpos.ne']
  exact (integrable_norm_iff hgm).mp hgn

private noncomputable def ideleAt (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (AdelicLevel.localUnit (𝓞 ℚ) ℚ v t)

private theorem ideleAt_fst (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = 1 :=
  AdelicLevel.finIncl_apply_fst (𝓞 ℚ) ℚ _

private theorem ideleAt_snd_self (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v = t := by
  show ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = t
  exact AdelicLevel.localUnit_apply_self (𝓞 ℚ) ℚ v t

private theorem ideleAt_snd_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w = 1 := by
  show ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) w = 1
  exact AdelicLevel.localUnit_apply_of_ne (𝓞 ℚ) ℚ v t hw

open scoped Classical in

private noncomputable def glueAt (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × v.adicCompletion ℚ) : (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  if hx : p.2 = 0 then Idele.partAt ℚ T p.1 else Idele.partAt ℚ T p.1 * ideleAt v (Units.mk0 p.2 hx)

private theorem glueAt_of_ne_zero (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    glueAt T v (b, x) = Idele.partAt ℚ T b * ideleAt v (Units.mk0 x hx) := by
  simp [glueAt, hx]

private theorem glueAt_fst (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ((glueAt T v (b, x) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = (b : AdeleRing (𝓞 ℚ) ℚ).1 := by
  rw [glueAt_of_ne_zero T v b hx]
  have h1 : (((Idele.partAt ℚ T b * ideleAt v (Units.mk0 x hx) : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) : AdeleRing (𝓞 ℚ) ℚ).1 =
      ((Idele.partAt ℚ T b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 *
        ((ideleAt v (Units.mk0 x hx) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 := rfl
  rw [h1, ideleAt_fst, mul_one, Idele.partAt_fst]

private theorem glueAt_snd_of_mem (T : Finset (HeightOneSpectrum (𝓞 ℚ))) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ T) (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0)
    {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ∈ T) :
    ((glueAt T v (b, x) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w = (b : AdeleRing (𝓞 ℚ) ℚ).2 w := by
  have hwv : w ≠ v := fun h => hv (h ▸ hw)
  rw [glueAt_of_ne_zero T v b hx]
  have h1 : (((Idele.partAt ℚ T b * ideleAt v (Units.mk0 x hx) : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((Idele.partAt ℚ T b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w *
        ((ideleAt v (Units.mk0 x hx) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w := rfl
  rw [h1, ideleAt_snd_of_ne v _ hwv, mul_one, Idele.partAt_snd_of_mem ℚ T b hw]

private theorem glueAt_snd_self (T : Finset (HeightOneSpectrum (𝓞 ℚ))) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ T) (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    ((glueAt T v (b, x) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v = x := by
  rw [glueAt_of_ne_zero T v b hx]
  have h1 : (((Idele.partAt ℚ T b * ideleAt v (Units.mk0 x hx) : (AdeleRing (𝓞 ℚ) ℚ)ˣ)) : AdeleRing (𝓞 ℚ) ℚ).2 v =
      ((Idele.partAt ℚ T b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v *
        ((ideleAt v (Units.mk0 x hx) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v := rfl
  rw [h1, Idele.partAt_snd_of_not_mem ℚ T b hv, one_mul, ideleAt_snd_self]
  rfl

private theorem continuous_localUnit_val (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun t : (v.adicCompletion ℚ)ˣ =>
      ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 ℚ))) ≤
      Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 ℚ))) :=
    Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite
  let g : (v.adicCompletion ℚ)ˣ → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 ℚ) => w.adicCompletion ℚ)
      (fun w => (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)))
      (Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 ℚ)))) := fun t =>
    ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 ℚ)) → w.adicCompletion ℚ) v (t : v.adicCompletion ℚ),
      Filter.eventually_principal.mpr fun w hw => by
        rw [Function.update_of_ne hw]
        exact one_mem _⟩
  have hg : Continuous g := by
    refine RestrictedProduct.continuous_rng_of_principal.mpr (continuous_pi fun w => ?_)
    by_cases hw : w = v
    · subst hw
      show Continuous fun t : (w.adicCompletion ℚ)ˣ => Function.update (1 : (u : HeightOneSpectrum (𝓞 ℚ)) →
        u.adicCompletion ℚ) w (t : w.adicCompletion ℚ) w
      simpa using Units.continuous_val
    · show Continuous fun t : (v.adicCompletion ℚ)ˣ => Function.update (1 : (u : HeightOneSpectrum (𝓞 ℚ)) →
        u.adicCompletion ℚ) v (t : v.adicCompletion ℚ) w
      simp only [Function.update_of_ne hw]
      exact continuous_const
  have heq : (fun t : (v.adicCompletion ℚ)ˣ =>
      ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      fun t => RestrictedProduct.inclusion _ _ hle (g t) := by
    funext t
    exact Subtype.ext (funext fun _ => rfl)
  rw [heq]
  exact (RestrictedProduct.continuous_inclusion hle).comp hg

private theorem continuous_ideleAt_val (v : HeightOneSpectrum (𝓞 ℚ)) :
    Continuous fun t : (v.adicCompletion ℚ)ˣ => ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ) := by
  show Continuous fun t : (v.adicCompletion ℚ)ˣ => ((1 : InfiniteAdeleRing ℚ),
    ((AdelicLevel.localUnit (𝓞 ℚ) ℚ v t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ))
  exact continuous_const.prodMk (continuous_localUnit_val v)

private theorem ideleAt_inv (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ) :
    (ideleAt v t)⁻¹ = ideleAt v t⁻¹ := by
  simp only [ideleAt, map_inv]

private theorem continuous_ideleAt (v : HeightOneSpectrum (𝓞 ℚ)) : Continuous (ideleAt v) := by
  refine Units.continuous_iff.mpr ⟨continuous_ideleAt_val v, ?_⟩
  simp only [ideleAt_inv]
  exact (continuous_ideleAt_val v).comp continuous_inv

open scoped Classical in

private noncomputable def unitOf (v : HeightOneSpectrum (𝓞 ℚ)) (x : v.adicCompletion ℚ) : (v.adicCompletion ℚ)ˣ :=
  if hx : x = 0 then 1 else Units.mk0 x hx

private theorem continuousOn_unitOf (v : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousOn (unitOf v) {x : v.adicCompletion ℚ | x ≠ 0} := by
  rw [Units.isEmbedding_val₀.continuousOn_iff]
  refine continuousOn_id.congr fun x hx => ?_
  have hx' : x ≠ 0 := hx
  simp [unitOf, hx']

open scoped Classical in
private theorem glueAt_eq_piecewise (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) :
    glueAt T v = {p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × v.adicCompletion ℚ | p.2 = 0}.piecewise
      (fun p => Idele.partAt ℚ T p.1) (fun p => Idele.partAt ℚ T p.1 * ideleAt v (unitOf v p.2)) := by
  funext p
  by_cases hx : p.2 = 0
  · simp [glueAt, Set.piecewise, hx]
  · simp [glueAt, Set.piecewise, unitOf, hx]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

private theorem measurable_glueAt (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    Measurable (glueAt T v) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := Idele.borelSpace_ideleBorel ℚ
  rw [glueAt_eq_piecewise]
  refine ContinuousOn.measurable_piecewise ?_ ?_ ?_
  · exact ((Idele.continuous_partAt ℚ T).comp continuous_fst).continuousOn
  · refine ContinuousOn.mul ((Idele.continuous_partAt ℚ T).comp continuous_fst).continuousOn ?_
    refine (continuous_ideleAt v).comp_continuousOn ?_
    refine (continuousOn_unitOf v).comp continuous_snd.continuousOn ?_
    intro p hp
    exact hp
  · exact measurable_snd (measurableSet_singleton (0 : v.adicCompletion ℚ))

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

private theorem measurePreserving_mul_right_sPartMeasure' (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (hu : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ S → ((u : AdeleRing (𝓞 ℚ) ℚ)).2 w = 1) :
    MeasurePreserving (fun t : (AdeleRing (𝓞 ℚ) ℚ)ˣ => t * u) (Idele.sPartMeasure ℚ S) (Idele.sPartMeasure ℚ S) :=
  Idele.measurePreserving_mul_right_sPartMeasure ℚ S u hu

private theorem idele_ext' {a b : (AdeleRing (𝓞 ℚ) ℚ)ˣ}
    (h₁ : ((a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 = ((b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 ℚ), ((a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w) : a = b :=
  Units.ext (Prod.ext h₁ (Subtype.ext (funext h₂)))

private theorem partAt_empty_glueAt (T : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (b : (AdeleRing (𝓞 ℚ) ℚ)ˣ) {x : v.adicCompletion ℚ} (hx : x ≠ 0) :
    Idele.partAt ℚ ∅ (glueAt T v (b, x)) = Idele.partAt ℚ ∅ b := by
  refine idele_ext' ?_ fun w => ?_
  · rw [Idele.partAt_fst, Idele.partAt_fst, glueAt_fst T v b hx]
  · rw [Idele.partAt_snd_of_not_mem ℚ ∅ _ (by simp), Idele.partAt_snd_of_not_mem ℚ ∅ _ (by simp)]

private theorem mem_unitIdelesOutside_iff_ord' (T : Set (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    a ∈ AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ T ↔ ∀ w, w ∉ T → Idele.ord ℚ w a = 0 := by
  rw [AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [Idele.ord_eq_zero_iff]
  rfl

private theorem setOf_ord_eq_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Idele.ord ℚ v a = 0} =
      (AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ ({v}ᶜ : Set (HeightOneSpectrum (𝓞 ℚ))) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) := by
  ext a
  simp only [Set.mem_setOf_eq, SetLike.mem_coe, mem_unitIdelesOutside_iff_ord', Set.notMem_compl_iff,
    Set.mem_singleton_iff, forall_eq]

private noncomputable def ordHom' (v : HeightOneSpectrum (𝓞 ℚ)) : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (Idele.ord ℚ v a)
  map_one' := by rw [Idele.ord_one]; rfl
  map_mul' a b := by rw [Idele.ord_mul]; rfl

private theorem ord_zpow' (v : HeightOneSpectrum (𝓞 ℚ)) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (n : ℤ) :
    Idele.ord ℚ v (a ^ n) = n * Idele.ord ℚ v a := by
  have h := map_zpow (ordHom' v) a n
  have h' := congrArg Multiplicative.toAdd h
  simpa [ordHom'] using h'

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem measurableSet_ord_eq (v : HeightOneSpectrum (𝓞 ℚ)) (m : ℤ) :
    MeasurableSet {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Idele.ord ℚ v a = m} := by
  haveI := Idele.borelSpace_ideleBorel ℚ
  have hset : {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Idele.ord ℚ v a = m} =
      (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => AutomorphicForm.uniformizerIdele ℚ v ^ (-m) * a) ⁻¹'
        {a : (AdeleRing (𝓞 ℚ) ℚ)ˣ | Idele.ord ℚ v a = 0} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Idele.ord_mul, ord_zpow', Idele.ord_uniformizerIdele_self,
      mul_one]
    omega
  rw [hset, setOf_ord_eq_zero]
  exact (continuous_const.mul continuous_id).measurable (Idele.isOpen_unitIdelesOutside ℚ _).measurableSet

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem measurable_ord (v : HeightOneSpectrum (𝓞 ℚ)) : Measurable (Idele.ord ℚ v) :=
  measurable_to_countable' fun m => measurableSet_ord_eq v m

private theorem continuous_archNorm (w : InfinitePlace ℚ) :
    Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖ :=
  continuous_norm.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

private def archBox (n : ℕ) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {a | ∀ w : InfinitePlace ℚ, ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖ ∈ Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)}

private def box (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ :=
  archBox n ∩ {a | ∀ v ∈ S, Idele.ord ℚ v a ∈ Finset.Icc (-(n : ℤ)) n}

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem measurableSet_archBox (n : ℕ) : MeasurableSet (archBox n) := by
  haveI := Idele.borelSpace_ideleBorel ℚ
  unfold archBox
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter fun w => (continuous_archNorm w).measurable measurableSet_Icc

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem measurableSet_box (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) : MeasurableSet (box S n) := by
  refine (measurableSet_archBox n).inter ?_
  simp only [Set.setOf_forall]
  exact S.measurableSet_biInter fun v _ => measurable_ord v MeasurableSet.of_discrete

private theorem archNorm_pos (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (w : InfinitePlace ℚ) :
    0 < ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖ := by
  refine norm_pos_iff.mpr fun h0 => ?_
  have h : ((a : AdeleRing (𝓞 ℚ) ℚ).1 w) * (((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 w) = 1 :=
    congrArg (fun x : AdeleRing (𝓞 ℚ) ℚ => x.1 w) (Units.mul_inv a)
  rw [h0, zero_mul] at h
  exact zero_ne_one h

private theorem exists_mem_box (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ∃ n : ℕ, a ∈ box S n := by
  classical

  have harch : ∀ w : InfinitePlace ℚ, ∃ k : ℕ,
      ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖⁻¹ ≤ k ∧ ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖ ≤ k := fun w => by
    obtain ⟨k, hk⟩ := exists_nat_ge (max ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖⁻¹ ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖)
    exact ⟨k, (le_max_left _ _).trans hk, (le_max_right _ _).trans hk⟩
  choose k hk using harch
  refine ⟨Finset.univ.sup k + S.sup fun v => (Idele.ord ℚ v a).natAbs, ?_, ?_⟩
  · intro w
    have hkw : k w ≤ Finset.univ.sup k + S.sup fun v => (Idele.ord ℚ v a).natAbs :=
      (Finset.le_sup (Finset.mem_univ w)).trans (Nat.le_add_right _ _)
    have hkw' : (k w : ℝ) ≤ ((Finset.univ.sup k + S.sup fun v => (Idele.ord ℚ v a).natAbs : ℕ) : ℝ) + 1 := by
      exact_mod_cast Nat.le_succ_of_le hkw
    have hpos := archNorm_pos a w
    refine ⟨?_, (hk w).2.trans hkw'⟩
    rw [inv_le_comm₀ (by positivity) hpos]
    exact (hk w).1.trans hkw'
  · intro v hv
    have h1 : (Idele.ord ℚ v a).natAbs ≤ Finset.univ.sup k + S.sup fun v => (Idele.ord ℚ v a).natAbs :=
      (Finset.le_sup (f := fun v => (Idele.ord ℚ v a).natAbs) hv).trans (Nat.le_add_left _ _)
    rw [Finset.mem_Icc]
    omega

private theorem prod_indicator_archBox (n : ℕ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (∏ w : InfinitePlace ℚ, (Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)).indicator (fun _ => (1 : ENNReal))
        ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖) = (archBox n).indicator (fun _ => (1 : ENNReal)) a := by
  by_cases ha : a ∈ archBox n
  · rw [Set.indicator_of_mem ha]
    exact Finset.prod_eq_one fun w _ => Set.indicator_of_mem (ha w) _
  · rw [Set.indicator_of_notMem ha]
    obtain ⟨w, hw⟩ : ∃ w : InfinitePlace ℚ, ‖((a : AdeleRing (𝓞 ℚ) ℚ).1 w)‖ ∉ Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1) := by
      by_contra h
      push Not at h
      exact ha h
    exact Finset.prod_eq_zero (Finset.mem_univ w) (Set.indicator_of_notMem hw _)

private theorem lintegral_indicator_inv_lt_top (n : ℕ) :
    (∫⁻ t in Set.Ioi (0 : ℝ), (Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)).indicator (fun _ => (1 : ENNReal)) t *
        (ENNReal.ofReal t)⁻¹) < ⊤ := by
  have hpt : ∀ t : ℝ, (Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)).indicator (fun _ => (1 : ENNReal)) t *
      (ENNReal.ofReal t)⁻¹ ≤ (Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)).indicator (fun _ => ENNReal.ofReal (n + 1)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht, one_mul]
      have h1 : ENNReal.ofReal ((n + 1 : ℝ)⁻¹) ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal ht.1
      rw [ENNReal.ofReal_inv_of_pos (by positivity)] at h1
      exact ENNReal.inv_le_iff_inv_le.mpr h1
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
  refine (lintegral_mono hpt).trans_lt ?_
  rw [lintegral_indicator measurableSet_Icc, setLIntegral_const]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine lt_of_le_of_lt (Measure.le_iff'.mp Measure.restrict_le_self _) ?_
  rw [Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem sPartMeasure_empty_archBox_lt_top (n : ℕ) : Idele.sPartMeasure ℚ ∅ (archBox n) < ⊤ := by
  obtain ⟨C, -, hCtop, hC⟩ := Idele.exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral ℚ
  have h := hC (fun _ t => (Set.Icc ((n + 1 : ℝ)⁻¹) (n + 1)).indicator (fun _ => (1 : ENNReal)) t)
    fun _ => measurable_const.indicator measurableSet_Icc
  simp only [prod_indicator_archBox] at h
  rw [lintegral_indicator_const (measurableSet_archBox n), one_mul] at h
  rw [h]
  exact ENNReal.mul_lt_top hCtop.lt_top (ENNReal.prod_lt_top fun w _ => lintegral_indicator_inv_lt_top n)

private theorem indicator_box (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    (archBox n).indicator (fun _ => (1 : ENNReal)) a *
        ∏ v ∈ S, (↑(Finset.Icc (-(n : ℤ)) n) : Set ℤ).indicator (fun _ => (1 : ENNReal)) (Idele.ord ℚ v a) =
      (box S n).indicator (fun _ => (1 : ENNReal)) a := by
  by_cases ha : a ∈ box S n
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha.1, one_mul]
    exact Finset.prod_eq_one fun v hv => Set.indicator_of_mem (Finset.mem_coe.mpr (ha.2 v hv)) _
  · rw [Set.indicator_of_notMem ha]
    by_cases h1 : a ∈ archBox n
    · obtain ⟨v, hv, hord⟩ : ∃ v ∈ S, Idele.ord ℚ v a ∉ Finset.Icc (-(n : ℤ)) n := by
        by_contra h
        push Not at h
        exact ha ⟨h1, h⟩
      rw [Finset.prod_eq_zero hv (Set.indicator_of_notMem (fun h => hord (Finset.mem_coe.mp h)) _), mul_zero]
    · rw [Set.indicator_of_notMem h1, zero_mul]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem sPartMeasure_box_lt_top (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (n : ℕ) :
    Idele.sPartMeasure ℚ S (box S n) < ⊤ := by
  have hf1 : ∀ a b : (AdeleRing (𝓞 ℚ) ℚ)ˣ, ((a : AdeleRing (𝓞 ℚ) ℚ)).1 = ((b : AdeleRing (𝓞 ℚ) ℚ)).1 →
      (archBox n).indicator (fun _ => (1 : ENNReal)) a = (archBox n).indicator (fun _ => (1 : ENNReal)) b := by
    intro a b hab
    simp only [Set.indicator_apply, archBox, Set.mem_setOf_eq, hab]
  have h := Idele.lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum ℚ S
    ((archBox n).indicator fun _ => (1 : ENNReal)) (measurable_const.indicator (measurableSet_archBox n)) hf1
    fun _ m => (↑(Finset.Icc (-(n : ℤ)) n) : Set ℤ).indicator (fun _ => (1 : ENNReal)) m
  simp only [indicator_box] at h
  rw [lintegral_indicator_const (measurableSet_box S n), one_mul, lintegral_indicator_const (measurableSet_archBox n),
    one_mul] at h
  rw [h]
  refine ENNReal.mul_lt_top (sPartMeasure_empty_archBox_lt_top n) (ENNReal.prod_lt_top fun v _ => ?_)
  rw [tsum_eq_sum (s := Finset.Icc (-(n : ℤ)) n) fun m hm =>
    Set.indicator_of_notMem (fun h => hm (Finset.mem_coe.mp h)) _]
  refine ENNReal.sum_lt_top.mpr fun m _ => ?_
  classical
  rw [Set.indicator_apply]
  split_ifs <;> simp

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

private theorem sigmaFinite_sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    SigmaFinite (Idele.sPartMeasure ℚ S) := by
  refine Measure.sigmaFinite_of_countable (Set.countable_range (box S)) ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact sPartMeasure_box_lt_top S n
  · refine Set.eq_univ_of_forall fun a => ?_
    obtain ⟨n, hn⟩ := exists_mem_box S a
    exact Set.mem_sUnion.mpr ⟨box S n, ⟨n, rfl⟩, hn⟩

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
private theorem sfinite_sPartMeasure (S : Finset (HeightOneSpectrum (𝓞 ℚ))) : SFinite (Idele.sPartMeasure ℚ S) := by
  haveI := sigmaFinite_sPartMeasure S
  infer_instance

private theorem sfinite_mulMeasure (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    SFinite (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  rw [LanglandsTunnell.TateLocal.mulMeasure, LanglandsTunnell.TateLocal.selfDualHaarAt]
  infer_instance

private theorem mulMeasure_singleton_zero (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) {0} = 0 := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  rw [LanglandsTunnell.TateLocal.mulMeasure, withDensity_apply _ (measurableSet_singleton 0),
    Measure.restrict_restrict (measurableSet_singleton 0), Set.inter_compl_self, Measure.restrict_empty,
    lintegral_zero_measure]

private theorem selfDualHaarAt_isAddHaarMeasure (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).IsAddHaarMeasure := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hc : (Ideal.absNorm v.asIdeal : NNReal) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal ℚ v) : ℝ) / 2) ≠ 0 :=
    (NNReal.rpow_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN))).ne'
  show (((Ideal.absNorm v.asIdeal : NNReal) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) •
    Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v)).IsAddHaarMeasure
  exact Measure.IsAddHaarMeasure.nnreal_smul _ hc

private theorem selfDualHaarAt_regular (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v).Regular := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  show (((Ideal.absNorm v.asIdeal : NNReal) ^
      (-(LanglandsTunnell.TateLocal.addCharLevel (StandardAddChar.psiLocal ℚ v) : ℝ) / 2)) •
    Measure.addHaarMeasure (LanglandsTunnell.TateLocal.integersPositiveCompacts ℚ v)).Regular
  infer_instance

private theorem selfDualHaarAt_integers_ne_zero_and_ne_top (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ≠ 0 ∧
      LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v
        (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ≠ ⊤ := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := selfDualHaarAt_isAddHaarMeasure v
  exact ⟨(Valued.isOpen_valuationSubring _).measure_ne_zero _ ⟨0, zero_mem _⟩,
    (isCompact_iff_compactSpace.mpr
      (show CompactSpace (v.adicCompletionIntegers ℚ) from inferInstance)).measure_lt_top.ne⟩

open scoped Pointwise in

private theorem map_mul_left_eq_smul_selfDualHaarAt (v : HeightOneSpectrum (𝓞 ℚ)) {x : v.adicCompletion ℚ}
    (hx : x ≠ 0) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    Measure.map (fun y : v.adicCompletion ℚ => x * y) (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) =
      ((LanglandsTunnell.TateLocal.modulus x : ENNReal))⁻¹ • LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := selfDualHaarAt_isAddHaarMeasure v
  haveI := selfDualHaarAt_regular v
  refine Measure.ext fun s hs => ?_
  have hpre : (fun y : v.adicCompletion ℚ => x * y) ⁻¹' s = (Units.mk0 x hx)⁻¹ • s := by
    ext y
    rw [Set.mem_preimage, Set.mem_inv_smul_set_iff, Units.smul_def, Units.val_mk0, smul_eq_mul]
  rw [Measure.map_apply (continuous_const_mul x).measurable hs, Measure.smul_apply, smul_eq_mul, hpre,
    ← distribHaarChar_mul (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) (Units.mk0 x hx)⁻¹ s, map_inv,
    LanglandsTunnell.TateLocal.modulus_of_ne_zero hx, ENNReal.coe_inv (distribHaarChar_pos).ne']

private theorem modulus_eq_one_of_valuation_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) {u : v.adicCompletion ℚ}
    (hu : Valued.v u = 1) : LanglandsTunnell.TateLocal.modulus u = 1 := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := selfDualHaarAt_isAddHaarMeasure v
  haveI := selfDualHaarAt_regular v
  have hu0 : u ≠ 0 := fun h => by
    rw [h, map_zero] at hu
    exact zero_ne_one hu
  obtain ⟨h0, htop⟩ := selfDualHaarAt_integers_ne_zero_and_ne_top v
  rw [LanglandsTunnell.TateLocal.modulus_of_ne_zero hu0]
  refine distribHaarChar_eq_of_measure_smul_eq_mul (μ := LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) h0 htop ?_
  rw [ENNReal.coe_one, one_mul]
  congr 1
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem, Units.smul_def, smul_eq_mul, SetLike.mem_coe, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, map_mul,
    Units.val_inv_eq_inv_val, Units.val_mk0, map_inv₀, hu, inv_one, one_mul]

private theorem map_mul_left_mulMeasure (v : HeightOneSpectrum (𝓞 ℚ)) (x : (v.adicCompletion ℚ)ˣ) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    Measure.map (fun y : v.adicCompletion ℚ => (x : v.adicCompletion ℚ) * y)
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) =
      LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  set μ := LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v with hμdef
  set m : ENNReal := (LanglandsTunnell.TateLocal.modulus (x : v.adicCompletion ℚ) : ENNReal) with hmdef
  have hm0 : m ≠ 0 := ENNReal.coe_ne_zero.mpr (LanglandsTunnell.TateLocal.modulus_ne_zero x.ne_zero)
  have hmt : m ≠ ⊤ := ENNReal.coe_ne_top
  set e : v.adicCompletion ℚ ≃ᵐ v.adicCompletion ℚ := MeasurableEquiv.mulLeft₀ (x : v.adicCompletion ℚ) x.ne_zero
  have he : (e : v.adicCompletion ℚ → v.adicCompletion ℚ) = fun y => (x : v.adicCompletion ℚ) * y := rfl
  have hmeas : Measurable fun y : v.adicCompletion ℚ => (x : v.adicCompletion ℚ) * y := by
    rw [← he]
    exact e.measurable

  have hμ : μ = m • Measure.map (e : v.adicCompletion ℚ → v.adicCompletion ℚ) μ := by
    rw [he, map_mul_left_eq_smul_selfDualHaarAt v x.ne_zero, smul_smul, ENNReal.mul_inv_cancel hm0 hmt, one_smul]
  set d : v.adicCompletion ℚ → ENNReal := fun y => ((LanglandsTunnell.TateLocal.modulus y : ENNReal))⁻¹ with hddef
  have h0 : MeasurableSet ({0}ᶜ : Set (v.adicCompletion ℚ)) := (measurableSet_singleton 0).compl
  have key : ∀ s : Set (v.adicCompletion ℚ), MeasurableSet s →
      ∫⁻ y, (s ∩ {0}ᶜ).indicator d y ∂μ =
        ∫⁻ y, ((fun y => (x : v.adicCompletion ℚ) * y) ⁻¹' s ∩ {0}ᶜ).indicator d y ∂μ := by
    intro s hs
    calc ∫⁻ y, (s ∩ {0}ᶜ).indicator d y ∂μ
        = ∫⁻ y, (s ∩ {0}ᶜ).indicator d y ∂(m • Measure.map (e : v.adicCompletion ℚ → v.adicCompletion ℚ) μ) := by
          rw [← hμ]
      _ = m * ∫⁻ y, (s ∩ {0}ᶜ).indicator d (e y) ∂μ := by
          rw [lintegral_smul_measure, lintegral_map_equiv, smul_eq_mul]
      _ = m * ∫⁻ y, m⁻¹ * ((fun y => (x : v.adicCompletion ℚ) * y) ⁻¹' s ∩ {0}ᶜ).indicator d y ∂μ := by
          congr 1
          refine lintegral_congr fun y => ?_
          by_cases hy : y ∈ (fun y => (x : v.adicCompletion ℚ) * y) ⁻¹' s ∩ {0}ᶜ
          · have hxy : e y ∈ s ∩ {0}ᶜ := ⟨hy.1, mul_ne_zero x.ne_zero hy.2⟩
            rw [Set.indicator_of_mem hxy, Set.indicator_of_mem hy, hddef]
            show ((LanglandsTunnell.TateLocal.modulus ((x : v.adicCompletion ℚ) * y) : ENNReal))⁻¹ = _
            rw [LanglandsTunnell.TateLocal.modulus_mul, ENNReal.coe_mul,
              ENNReal.mul_inv (Or.inl hm0) (Or.inl hmt)]
          · have hxy : e y ∉ s ∩ {0}ᶜ := fun h =>
              hy ⟨h.1, fun h0 => h.2 (show (x : v.adicCompletion ℚ) * y = 0 by
                rw [show y = 0 from h0, mul_zero])⟩
            rw [Set.indicator_of_notMem hxy, Set.indicator_of_notMem hy, mul_zero]
      _ = _ := by
          rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hm0), ← mul_assoc,
            ENNReal.mul_inv_cancel hm0 hmt, one_mul]
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hmeas hs, LanglandsTunnell.TateLocal.mulMeasure, withDensity_apply _ (hs.preimage hmeas),
    withDensity_apply _ hs, Measure.restrict_restrict (hs.preimage hmeas), Measure.restrict_restrict hs,
    ← lintegral_indicator (hs.inter h0), ← lintegral_indicator ((hs.preimage hmeas).inter h0)]
  exact (key s hs).symm

private theorem mulMeasure_preimage_mul_left (v : HeightOneSpectrum (𝓞 ℚ)) (x : (v.adicCompletion ℚ)ˣ)
    {B : Set (v.adicCompletion ℚ)} (hB : MeasurableSet[LanglandsTunnell.TateLocal.localBorel ℚ v] B) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
        ((fun y : v.adicCompletion ℚ => (x : v.adicCompletion ℚ) * y) ⁻¹' B) =
      LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) B := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  have h := map_mul_left_mulMeasure v x
  rw [← Measure.map_apply (continuous_const_mul (x : v.adicCompletion ℚ)).measurable hB, h]

private theorem isOpen_setOf_valued_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    IsOpen {y : v.adicCompletion ℚ | Valued.v y = 1} := by
  have hϖ : ((AdelicLevel.uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≠ 0 := Units.ne_zero _
  have h : {y : v.adicCompletion ℚ | Valued.v y = 1} =
      {y | Valued.v y ≤ Valued.v (1 : v.adicCompletion ℚ)} \
        {y | Valued.v y ≤ Valued.v ((AdelicLevel.uniformizerUnit ℚ v : (v.adicCompletion ℚ)ˣ) :
          v.adicCompletion ℚ)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_diff, map_one, AdelicLevel.valued_uniformizerUnit, not_le]
    constructor
    · intro hy
      rw [hy, ← WithZero.exp_zero, WithZero.exp_lt_exp]
      exact ⟨le_rfl, by omega⟩
    · rintro ⟨h1, h2⟩
      by_cases hy0 : Valued.v y = 0
      · rw [hy0] at h2
        exact absurd h2 (not_lt.mpr _root_.zero_le)
      obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hy0).symm⟩
      rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      rw [hm, WithZero.exp_lt_exp] at h2
      rw [hm, ← WithZero.exp_zero]
      congr 1
      omega
  rw [h]
  exact (AdelicLevel.isOpen_setOf_valued_le v (1 : v.adicCompletion ℚ) isUnit_one.ne_zero).sdiff
    (AdelicLevel.isClosed_setOf_valued_le v _ hϖ)

private theorem measurableSet_setOf_valued_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    MeasurableSet[LanglandsTunnell.TateLocal.localBorel ℚ v] {y : v.adicCompletion ℚ | Valued.v y = 1} := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  exact (isOpen_setOf_valued_eq_one v).measurableSet

private theorem exists_setOf_valued_eq_exp_eq_preimage (v : HeightOneSpectrum (𝓞 ℚ)) (n : ℤ) :
    ∃ u : (v.adicCompletion ℚ)ˣ, {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n} =
      (fun y : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * y) ⁻¹' {y | Valued.v y = 1} := by
  refine ⟨AdelicLevel.uniformizerUnit ℚ v ^ n, Set.ext fun y => ?_⟩
  have hu : Valued.v ((AdelicLevel.uniformizerUnit ℚ v ^ n : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) =
      WithZero.exp (-n) := by
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, AdelicLevel.valued_uniformizerUnit, ← WithZero.exp_zsmul]
    congr 1
    simp
  rw [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_setOf_eq, map_mul, hu, ← WithZero.exp_zero]
  constructor
  · intro hy
    rw [hy, ← WithZero.exp_add]
    congr 1
    omega
  · intro hy
    by_cases hy0 : Valued.v y = 0
    · rw [hy0, mul_zero] at hy
      exact absurd hy (WithZero.exp_ne_zero).symm
    obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v y = WithZero.exp m := ⟨_, (WithZero.exp_log hy0).symm⟩
    rw [hm, ← WithZero.exp_add] at hy
    rw [hm]
    have h := WithZero.exp_injective hy
    congr 1
    omega

private theorem mulMeasure_setOf_valued_eq_one (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
        {y : v.adicCompletion ℚ | Valued.v y = 1} =
      LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v {y : v.adicCompletion ℚ | Valued.v y = 1} := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  have hU := measurableSet_setOf_valued_eq_one v
  have hU0 : {y : v.adicCompletion ℚ | Valued.v y = 1} ∩ {0}ᶜ = {y | Valued.v y = 1} := by
    refine Set.inter_eq_left.mpr fun y hy h0 => ?_
    rw [Set.mem_singleton_iff] at h0
    rw [Set.mem_setOf_eq, h0, map_zero] at hy
    exact zero_ne_one hy
  rw [LanglandsTunnell.TateLocal.mulMeasure, withDensity_apply _ hU, Measure.restrict_restrict hU, hU0]
  refine (setLIntegral_congr_fun hU fun y hy => ?_).trans (setLIntegral_one _)
  show ((LanglandsTunnell.TateLocal.modulus y : ENNReal))⁻¹ = 1
  rw [modulus_eq_one_of_valuation_eq_one v hy, ENNReal.coe_one, inv_one]

private theorem mulMeasure_setOf_valued_eq_one_ne_zero_and_ne_top (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
        {y : v.adicCompletion ℚ | Valued.v y = 1} ≠ 0 ∧
      LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
        {y : v.adicCompletion ℚ | Valued.v y = 1} ≠ ⊤ := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := selfDualHaarAt_isAddHaarMeasure v
  rw [mulMeasure_setOf_valued_eq_one v]
  refine ⟨(isOpen_setOf_valued_eq_one v).measure_ne_zero _ ⟨1, by simp⟩, ?_⟩
  refine (lt_of_le_of_lt (measure_mono fun y hy => ?_) (selfDualHaarAt_integers_ne_zero_and_ne_top v).2.lt_top).ne
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  exact le_of_eq hy

private theorem sigmaFinite_mulMeasure (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    SigmaFinite (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  refine Measure.sigmaFinite_of_countable (S := insert {0} (Set.range fun n : ℤ =>
    {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n})) ((Set.countable_range _).insert _) ?_ ?_
  · rintro s (rfl | ⟨n, rfl⟩)
    · rw [mulMeasure_singleton_zero v]
      exact ENNReal.zero_lt_top
    · beta_reduce
      obtain ⟨u, hu⟩ := exists_setOf_valued_eq_exp_eq_preimage v n
      rw [hu, mulMeasure_preimage_mul_left v u (measurableSet_setOf_valued_eq_one v)]
      exact (mulMeasure_setOf_valued_eq_one_ne_zero_and_ne_top v).2.lt_top
  · refine Set.eq_univ_of_forall fun y => ?_
    rw [Set.sUnion_insert, Set.mem_union, Set.mem_singleton_iff, Set.sUnion_range, Set.mem_iUnion]
    by_cases hy : y = 0
    · exact Or.inl hy
    · refine Or.inr ⟨WithZero.log (Valued.v y), ?_⟩
      beta_reduce
      rw [Set.mem_setOf_eq, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr hy)]

private theorem snd_ideleAt_mul_self (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ((ideleAt v t * a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v =
      (t : v.adicCompletion ℚ) * (a : AdeleRing (𝓞 ℚ) ℚ).2 v := by
  have h : ((ideleAt v t * a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v =
      ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v * (a : AdeleRing (𝓞 ℚ) ℚ).2 v := rfl
  rw [h, ideleAt_snd_self]

private theorem snd_ideleAt_mul_of_ne (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((ideleAt v t * a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w = (a : AdeleRing (𝓞 ℚ) ℚ).2 w := by
  have h : ((ideleAt v t * a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w =
      ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w * (a : AdeleRing (𝓞 ℚ) ℚ).2 w := rfl
  rw [h, ideleAt_snd_of_ne v t hw, one_mul]

private theorem ideleAt_mem_unitIdelesOutside (v : HeightOneSpectrum (𝓞 ℚ)) (t : (v.adicCompletion ℚ)ˣ)
    {S : Set (HeightOneSpectrum (𝓞 ℚ))} (hv : v ∈ S) :
    ideleAt v t ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ S := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro w hw
  have hwv : w ≠ v := fun h => hw (h ▸ hv)
  constructor
  · show ((ideleAt v t : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w ∈ w.adicCompletionIntegers ℚ
    rw [ideleAt_snd_of_ne v t hwv]
    exact one_mem _
  · show (((ideleAt v t)⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w ∈ w.adicCompletionIntegers ℚ
    rw [ideleAt_inv, ideleAt_snd_of_ne v t⁻¹ hwv]
    exact one_mem _

private theorem partAt_ideleAt_eq_one (T : Finset (HeightOneSpectrum (𝓞 ℚ))) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ T) (t : (v.adicCompletion ℚ)ˣ) : Idele.partAt ℚ T (ideleAt v t) = 1 := by
  refine idele_ext' ?_ fun w => ?_
  · rw [Idele.partAt_fst, ideleAt_fst]
    rfl
  · by_cases hw : w ∈ T
    · rw [Idele.partAt_snd_of_mem ℚ T _ hw, ideleAt_snd_of_ne v t (fun h => hv (h ▸ hw))]
      rfl
    · rw [Idele.partAt_snd_of_not_mem ℚ T _ hw]
      rfl

private theorem partAt_ideleAt_mul (T : Finset (HeightOneSpectrum (𝓞 ℚ))) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ T) (t : (v.adicCompletion ℚ)ˣ) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Idele.partAt ℚ T (ideleAt v t * a) = Idele.partAt ℚ T a := by
  rw [map_mul, partAt_ideleAt_eq_one T hv t, one_mul]

private theorem partAt_eq_glueAt (T S : Finset (HeightOneSpectrum (𝓞 ℚ))) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∉ T) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ S ↔ w = v ∨ w ∈ T) (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Idele.partAt ℚ S a = glueAt T v (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v) := by
  have ha : (a : AdeleRing (𝓞 ℚ) ℚ).2 v ≠ 0 := fun h =>
    Idele.valued_snd_ne_zero ℚ v a (by rw [h, map_zero])
  rw [glueAt_of_ne_zero T v _ ha]
  refine idele_ext' ?_ fun w => ?_
  · have h : ((Idele.partAt ℚ T (Idele.partAt ℚ T a) * ideleAt v (Units.mk0 _ ha) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
          AdeleRing (𝓞 ℚ) ℚ).1 =
        ((Idele.partAt ℚ T (Idele.partAt ℚ T a) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 *
          ((ideleAt v (Units.mk0 _ ha) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).1 := rfl
    rw [h, Idele.partAt_fst, Idele.partAt_fst, Idele.partAt_fst, ideleAt_fst, mul_one]
  · have h : ((Idele.partAt ℚ T (Idele.partAt ℚ T a) * ideleAt v (Units.mk0 _ ha) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
          AdeleRing (𝓞 ℚ) ℚ).2 w =
        ((Idele.partAt ℚ T (Idele.partAt ℚ T a) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w *
          ((ideleAt v (Units.mk0 _ ha) : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 w := rfl
    rw [h]
    by_cases hwv : w = v
    · subst hwv
      rw [Idele.partAt_snd_of_mem ℚ S a ((hS w).mpr (Or.inl rfl)), Idele.partAt_snd_of_not_mem ℚ T _ hv,
        ideleAt_snd_self, one_mul, Units.val_mk0]
    · rw [ideleAt_snd_of_ne v _ hwv, mul_one]
      by_cases hwT : w ∈ T
      · rw [Idele.partAt_snd_of_mem ℚ S a ((hS w).mpr (Or.inr hwT)), Idele.partAt_snd_of_mem ℚ T _ hwT,
          Idele.partAt_snd_of_mem ℚ T _ hwT]
      · rw [Idele.partAt_snd_of_not_mem ℚ S a (fun h => ((hS w).mp h).elim hwv hwT),
          Idele.partAt_snd_of_not_mem ℚ T _ hwT]

private theorem mem_unitIdelesOutside_iff_and_valued_eq_one (T S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ T) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ S ↔ w = v ∨ w ∈ T)
    (a : (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑T : Set (HeightOneSpectrum (𝓞 ℚ))) ↔
      a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S : Set (HeightOneSpectrum (𝓞 ℚ))) ∧
        Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 := by
  simp only [NumberField.AdeleRing.mem_unitIdelesOutside_iff, FiniteAdeleRing.mem_unitIdelesOutside_iff,
    Finset.mem_coe]

  have hval : ((Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom a :
      (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) = (a : AdeleRing (𝓞 ℚ) ℚ).2 := rfl
  have hinv : (((Units.map (RingHom.snd (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom a)⁻¹ :
        (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) =
      ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 := by
    rw [← map_inv]
    rfl
  simp only [hval, hinv]
  have h₁ : (a : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ ↔ 0 ≤ Idele.ord ℚ v a := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Idele.valued_snd_eq_exp_neg_ord, ← WithZero.exp_zero,
      WithZero.exp_le_exp]
    exact ⟨fun h => by omega, fun h => by omega⟩
  have h₂ : ((a⁻¹ : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ).2 v ∈ v.adicCompletionIntegers ℚ ↔
      Idele.ord ℚ v a ≤ 0 := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Idele.valued_snd_eq_exp_neg_ord, Idele.ord_inv, neg_neg,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
  have h₃ : Valued.v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v) = 1 ↔ Idele.ord ℚ v a = 0 := by
    rw [Idele.valued_snd_eq_exp_neg_ord, ← WithZero.exp_zero, WithZero.exp_injective.eq_iff]
    exact ⟨fun h => by omega, fun h => by omega⟩
  constructor
  · intro h
    refine ⟨fun w hw => h w fun hwT => hw ((hS w).mpr (Or.inr hwT)), ?_⟩
    obtain ⟨ha, ha'⟩ := h v hv
    rw [h₃]
    have := h₁.mp ha
    have := h₂.mp ha'
    omega
  · rintro ⟨h, h1⟩ w hw
    by_cases hwv : w = v
    · subst hwv
      rw [h₃] at h1
      exact ⟨h₁.mpr h1.ge, h₂.mpr h1.le⟩
    · exact h w fun hwS => ((hS w).mp hwS).elim hwv hw

attribute [local instance] NumberField.Idele.ideleBorel in

private theorem measurable_sndAt (v : HeightOneSpectrum (𝓞 ℚ)) :
    @Measurable (AdeleRing (𝓞 ℚ) ℚ)ˣ (v.adicCompletion ℚ) (Idele.ideleBorel ℚ)
      (LanglandsTunnell.TateLocal.localBorel ℚ v) fun a => (a : AdeleRing (𝓞 ℚ) ℚ).2 v := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := Idele.ideleBorel ℚ
  haveI : BorelSpace (AdeleRing (𝓞 ℚ) ℚ)ˣ := Idele.borelSpace_ideleBorel ℚ
  have hc : Continuous fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (a : AdeleRing (𝓞 ℚ) ℚ).2 v :=
    (RestrictedProduct.continuous_eval v).comp (continuous_snd.comp Units.continuous_val)
  exact hc.measurable

private theorem eq_smul_of_forall_preimage_mul_eq (v : HeightOneSpectrum (𝓞 ℚ)) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    ∀ ν₁ ν₂ : Measure (v.adicCompletion ℚ), ν₁ {0} = 0 → ν₂ {0} = 0 →
      (∀ (u : (v.adicCompletion ℚ)ˣ) (B : Set (v.adicCompletion ℚ)), MeasurableSet B →
        ν₁ ((fun y : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * y) ⁻¹' B) = ν₁ B) →
      (∀ (u : (v.adicCompletion ℚ)ˣ) (B : Set (v.adicCompletion ℚ)), MeasurableSet B →
        ν₂ ((fun y : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * y) ⁻¹' B) = ν₂ B) →
      (∀ n : ℤ, ν₁ {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n} ≠ ⊤) →
      (∀ n : ℤ, ν₂ {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n} ≠ ⊤) →
      ν₂ {y : v.adicCompletion ℚ | Valued.v y = 1} ≠ 0 → ν₂ {y : v.adicCompletion ℚ | Valued.v y = 1} ≠ ⊤ →
      ν₁ = (ν₁ {y : v.adicCompletion ℚ | Valued.v y = 1} / ν₂ {y : v.adicCompletion ℚ | Valued.v y = 1}) • ν₂ := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  intro ν₁ ν₂ h0₁ h0₂ h₁ h₂ hfin₁ hfin₂ hs0 hst
  letI : MeasurableSpace (v.adicCompletion ℚ)ˣ := borel _
  haveI : BorelSpace (v.adicCompletion ℚ)ˣ := ⟨rfl⟩
  haveI : SecondCountableTopology (v.adicCompletion ℚ)ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have he : Measurable (unitOf v) := measurable_of_continuousOn_compl_singleton 0 (continuousOn_unitOf v)
  have hval : Measurable (Units.val : (v.adicCompletion ℚ)ˣ → v.adicCompletion ℚ) := Units.continuous_val.measurable
  have hU := measurableSet_setOf_valued_eq_one v
  have he_of_ne : ∀ {x : v.adicCompletion ℚ} (hx : x ≠ 0), unitOf v x = Units.mk0 x hx := fun hx => dif_neg hx

  have hT₂ : ∀ B : Set (v.adicCompletion ℚ), unitOf v ⁻¹' (Units.val ⁻¹' B) \ {0} = B \ {0} := by
    intro B
    ext x
    simp only [Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx0⟩
      rw [he_of_ne hx0, Units.val_mk0] at hx
      exact ⟨hx, hx0⟩
    · rintro ⟨hx, hx0⟩
      rw [he_of_ne hx0, Units.val_mk0]
      exact ⟨hx, hx0⟩
  have hT₃ : ∀ (g : (v.adicCompletion ℚ)ˣ) (B' : Set (v.adicCompletion ℚ)ˣ),
      unitOf v ⁻¹' ((fun h => g * h) ⁻¹' B') \ {0} =
        (fun y : v.adicCompletion ℚ => (g : v.adicCompletion ℚ) * y) ⁻¹' (unitOf v ⁻¹' B' \ {0}) := by
    intro g B'
    ext x
    simp only [Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hx0⟩
      have hgx : (g : v.adicCompletion ℚ) * x ≠ 0 := mul_ne_zero g.ne_zero hx0
      refine ⟨?_, hgx⟩
      rwa [he_of_ne hgx, show Units.mk0 _ hgx = g * unitOf v x from
        Units.ext (by rw [Units.val_mk0, Units.val_mul, he_of_ne hx0, Units.val_mk0])]
    · rintro ⟨hx, hgx⟩
      have hx0 : x ≠ 0 := fun h => hgx (by rw [h, mul_zero])
      refine ⟨?_, hx0⟩
      rwa [he_of_ne hgx, show Units.mk0 _ hgx = g * unitOf v x from
        Units.ext (by rw [Units.val_mk0, Units.val_mul, he_of_ne hx0, Units.val_mk0])] at hx

  have hT₁ : ∀ ν : Measure (v.adicCompletion ℚ), ν {0} = 0 → ∀ B' : Set (v.adicCompletion ℚ)ˣ,
      MeasurableSet B' → Measure.map (unitOf v) ν B' = ν (unitOf v ⁻¹' B' \ {0}) := by
    intro ν h0 B' hB'
    rw [Measure.map_apply he hB', measure_diff_null h0]
  have hT : ∀ ν : Measure (v.adicCompletion ℚ), ν {0} = 0 → ∀ B : Set (v.adicCompletion ℚ),
      MeasurableSet B → ν B = Measure.map (unitOf v) ν (Units.val ⁻¹' B) := by
    intro ν h0 B hB
    rw [hT₁ ν h0 _ (hval hB), hT₂, measure_diff_null h0]

  have hinv : ∀ ν : Measure (v.adicCompletion ℚ), ν {0} = 0 →
      (∀ (u : (v.adicCompletion ℚ)ˣ) (B : Set (v.adicCompletion ℚ)), MeasurableSet B →
        ν ((fun y : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * y) ⁻¹' B) = ν B) →
      (Measure.map (unitOf v) ν).IsMulLeftInvariant := by
    intro ν h0 h
    refine ⟨fun g => Measure.ext fun B' hB' => ?_⟩
    have hg : Measurable fun h : (v.adicCompletion ℚ)ˣ => g * h := (continuous_const_mul g).measurable
    rw [Measure.map_apply hg hB', hT₁ ν h0 _ (hg hB'), hT₃, h g _ ((he hB').diff (measurableSet_singleton 0)),
      hT₁ ν h0 _ hB']

  have hsf : ∀ ν : Measure (v.adicCompletion ℚ), ν {0} = 0 →
      (∀ n : ℤ, ν {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n} ≠ ⊤) →
      SigmaFinite (Measure.map (unitOf v) ν) := by
    intro ν h0 hfin
    refine Measure.sigmaFinite_of_countable (Set.countable_range fun n : ℤ =>
      Units.val ⁻¹' {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n}) ?_ ?_
    · rintro _ ⟨n, rfl⟩
      beta_reduce
      obtain ⟨u, hu⟩ := exists_setOf_valued_eq_exp_eq_preimage v n
      have hmeas : MeasurableSet {y : v.adicCompletion ℚ | Valued.v y = WithZero.exp n} := by
        rw [hu]
        exact hU.preimage (continuous_const_mul (u : v.adicCompletion ℚ)).measurable
      rw [← hT ν h0 _ hmeas]
      exact (hfin n).lt_top
    · refine Set.eq_univ_of_forall fun g => ?_
      rw [Set.sUnion_range, Set.mem_iUnion]
      refine ⟨WithZero.log (Valued.v (g : v.adicCompletion ℚ)), ?_⟩
      beta_reduce
      rw [Set.mem_preimage, Set.mem_setOf_eq, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr g.ne_zero)]
  haveI := hinv ν₁ h0₁ h₁
  haveI := hinv ν₂ h0₂ h₂
  haveI := hsf ν₁ h0₁ hfin₁
  haveI := hsf ν₂ h0₂ hfin₂
  have h2s : Measure.map (unitOf v) ν₂ (Units.val ⁻¹' {y : v.adicCompletion ℚ | Valued.v y = 1}) ≠ 0 := by
    rwa [← hT ν₂ h0₂ _ hU]
  have h3s : Measure.map (unitOf v) ν₂ (Units.val ⁻¹' {y : v.adicCompletion ℚ | Valued.v y = 1}) ≠ ⊤ := by
    rwa [← hT ν₂ h0₂ _ hU]
  have key := measure_eq_div_smul (Measure.map (unitOf v) ν₁) (Measure.map (unitOf v) ν₂) h2s h3s
  rw [← hT ν₁ h0₁ _ hU, ← hT ν₂ h0₂ _ hU] at key
  refine Measure.ext fun B hB => ?_
  rw [hT ν₁ h0₁ B hB, key, Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul, ← hT ν₂ h0₂ B hB]

attribute [local instance] NumberField.Idele.ideleBorel in

private noncomputable def sliceMeasure (T S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) :
    @Measure (v.adicCompletion ℚ) (LanglandsTunnell.TateLocal.localBorel ℚ v) := by
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  exact Measure.map (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (a : AdeleRing (𝓞 ℚ) ℚ).2 v)
    ((Idele.idelicHaar ℚ).restrict
      ((NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S : Set (HeightOneSpectrum (𝓞 ℚ))) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) ∩ Idele.partAt ℚ T ⁻¹' A))

attribute [local instance] NumberField.Idele.ideleBorel in

private theorem sliceMeasure_apply (T S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) {B : Set (v.adicCompletion ℚ)}
    (hB : MeasurableSet[LanglandsTunnell.TateLocal.localBorel ℚ v] B) :
    sliceMeasure T S v A B = Idele.idelicHaar ℚ
      ((fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (a : AdeleRing (𝓞 ℚ) ℚ).2 v) ⁻¹' B ∩
        ((NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S : Set (HeightOneSpectrum (𝓞 ℚ))) :
            Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) ∩ Idele.partAt ℚ T ⁻¹' A)) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  rw [sliceMeasure, Measure.map_apply (measurable_sndAt v) hB,
    Measure.restrict_apply (hB.preimage (measurable_sndAt v))]

attribute [local instance] NumberField.Idele.ideleBorel in

private theorem sliceMeasure_singleton_zero (T S : Finset (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) : sliceMeasure T S v A {0} = 0 := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  rw [sliceMeasure_apply T S v A (measurableSet_singleton 0)]
  convert measure_empty (μ := Idele.idelicHaar ℚ) using 2
  refine Set.eq_empty_of_forall_notMem fun a ha => Idele.valued_snd_ne_zero ℚ v a ?_
  rw [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at ha
  rw [ha.1, map_zero]

attribute [local instance] NumberField.Idele.ideleBorel in

private theorem sliceMeasure_setOf_valued_eq_one (T S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ T) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ S ↔ w = v ∨ w ∈ T)
    {A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ} (hA : MeasurableSet A) :
    sliceMeasure T S v A {y : v.adicCompletion ℚ | Valued.v y = 1} = Idele.sPartMeasure ℚ T A := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  rw [sliceMeasure_apply T S v A (measurableSet_setOf_valued_eq_one v), Idele.sPartMeasure,
    Measure.map_apply (Idele.measurable_partAt ℚ T) hA,
    Measure.restrict_apply (hA.preimage (Idele.measurable_partAt ℚ T))]
  congr 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, SetLike.mem_coe,
    mem_unitIdelesOutside_iff_and_valued_eq_one T S hv hS a]
  tauto

attribute [local instance] NumberField.Idele.ideleBorel in

private theorem sliceMeasure_preimage_mul_left (T S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ T) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ S ↔ w = v ∨ w ∈ T)
    (A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ) (u : (v.adicCompletion ℚ)ˣ) {B : Set (v.adicCompletion ℚ)}
    (hB : MeasurableSet[LanglandsTunnell.TateLocal.localBorel ℚ v] B) :
    sliceMeasure T S v A ((fun y : v.adicCompletion ℚ => (u : v.adicCompletion ℚ) * y) ⁻¹' B) =
      sliceMeasure T S v A B := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := Idele.borelSpace_ideleBorel ℚ
  haveI := Idele.isHaarMeasure_idelicHaar ℚ
  rw [sliceMeasure_apply T S v A (hB.preimage (continuous_const_mul (u : v.adicCompletion ℚ)).measurable),
    sliceMeasure_apply T S v A hB]
  conv_rhs => rw [← measure_preimage_mul (Idele.idelicHaar ℚ) (ideleAt v u)]
  congr 1
  ext a
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe, snd_ideleAt_mul_self, partAt_ideleAt_mul T hv,
    Subgroup.mul_mem_cancel_left _ (ideleAt_mem_unitIdelesOutside v u (S := ↑S)
      (Finset.mem_coe.mpr ((hS v).mpr (Or.inl rfl))))]

attribute [local instance] NumberField.Idele.ideleBorel in

private theorem prod_sPartMeasure_mulMeasure_eq_smul_map (T S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ T) (hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ S ↔ w = v ∨ w ∈ T) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    (Idele.sPartMeasure ℚ T).prod
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) =
      LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
          {y : v.adicCompletion ℚ | Valued.v y = 1} •
        Measure.map (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v))
          ((Idele.idelicHaar ℚ).restrict
            (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S : Set (HeightOneSpectrum (𝓞 ℚ))) :
              Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := Idele.borelSpace_ideleBorel ℚ
  haveI := sigmaFinite_sPartMeasure T
  haveI := sigmaFinite_mulMeasure v
  obtain ⟨hk0, hkt⟩ := mulMeasure_setOf_valued_eq_one_ne_zero_and_ne_top v
  set μv := LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v) with hμv
  set k := μv {y : v.adicCompletion ℚ | Valued.v y = 1} with hk
  have hΦ : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v) :=
    (Idele.measurable_partAt ℚ T).prodMk (measurable_sndAt v)
  have hU := measurableSet_setOf_valued_eq_one v

  have hCgen : MeasurableSpace.generateFrom
      {A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ | MeasurableSet A ∧ Idele.sPartMeasure ℚ T A ≠ ⊤} = Idele.ideleBorel ℚ := by
    refine le_antisymm (MeasurableSpace.generateFrom_le fun A hA => hA.1) ?_
    intro A hA
    have hAU : A = ⋃ n, A ∩ spanningSets (Idele.sPartMeasure ℚ T) n := by
      rw [← Set.inter_iUnion, iUnion_spanningSets, Set.inter_univ]
    rw [hAU]
    refine MeasurableSet.iUnion fun n => MeasurableSpace.measurableSet_generateFrom ⟨?_, ?_⟩
    · exact hA.inter (measurableSet_spanningSets _ n)
    · exact ((measure_mono Set.inter_subset_right).trans_lt (measure_spanningSets_lt_top _ n)).ne
  have hCpi : IsPiSystem {A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ | MeasurableSet A ∧ Idele.sPartMeasure ℚ T A ≠ ⊤} :=
    fun A hA A' hA' _ => ⟨hA.1.inter hA'.1, ((measure_mono Set.inter_subset_left).trans_lt hA.2.lt_top).ne⟩
  have hCspan : (Idele.sPartMeasure ℚ T).FiniteSpanningSetsIn
      {A : Set (AdeleRing (𝓞 ℚ) ℚ)ˣ | MeasurableSet A ∧ Idele.sPartMeasure ℚ T A ≠ ⊤} :=
    ⟨spanningSets _, fun n => ⟨measurableSet_spanningSets _ n, (measure_spanningSets_lt_top _ n).ne⟩,
      measure_spanningSets_lt_top _, iUnion_spanningSets _⟩
  refine Measure.prod_eq_generateFrom hCgen MeasurableSpace.generateFrom_measurableSet hCpi
    MeasurableSpace.isPiSystem_measurableSet hCspan μv.toFiniteSpanningSetsIn ?_
  rintro A ⟨hAm, hAt⟩ B (hB : MeasurableSet B)

  have hrect : (Measure.map (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v))
      ((Idele.idelicHaar ℚ).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑S : Set (HeightOneSpectrum (𝓞 ℚ))) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ))) (A ×ˢ B) = sliceMeasure T S v A B := by
    rw [Measure.map_apply hΦ (hAm.prod hB), Measure.restrict_apply ((hAm.prod hB).preimage hΦ),
      sliceMeasure_apply T S v A hB, Set.mk_preimage_prod]
    congr 1
    ext a
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    tauto
  have hslice := eq_smul_of_forall_preimage_mul_eq v (sliceMeasure T S v A) μv (sliceMeasure_singleton_zero T S v A)
    (mulMeasure_singleton_zero v) (fun u B' hB' => sliceMeasure_preimage_mul_left T S hv hS A u hB')
    (fun u B' hB' => mulMeasure_preimage_mul_left v u hB') (fun n => ?_) (fun n => ?_) hk0 hkt
  · rw [Measure.smul_apply, smul_eq_mul, hrect, hslice, Measure.smul_apply, smul_eq_mul,
      sliceMeasure_setOf_valued_eq_one T S hv hS hAm, ← hk, ENNReal.div_eq_inv_mul, ← mul_assoc, ← mul_assoc,
      ENNReal.mul_inv_cancel hk0 hkt, one_mul]
  · obtain ⟨u, hu⟩ := exists_setOf_valued_eq_exp_eq_preimage v n
    rw [hu, sliceMeasure_preimage_mul_left T S hv hS A u hU, sliceMeasure_setOf_valued_eq_one T S hv hS hAm]
    exact hAt
  · obtain ⟨u, hu⟩ := exists_setOf_valued_eq_exp_eq_preimage v n
    rw [hu, mulMeasure_preimage_mul_left v u hU]
    exact hkt

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in
open scoped Classical in

private theorem sPartMeasure_insert_eq_smul_map_prod (T : Finset (HeightOneSpectrum (𝓞 ℚ)))
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ T) :
    letI := LanglandsTunnell.TateLocal.localBorel ℚ v
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      Idele.sPartMeasure ℚ (insert v T) =
        c • Measure.map (glueAt T v) ((Idele.sPartMeasure ℚ T).prod
          (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) := by
  letI : MeasurableSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : BorelSpace (v.adicCompletion ℚ) := LanglandsTunnell.TateLocal.borelSpace_localBorel ℚ v
  haveI := Idele.borelSpace_ideleBorel ℚ
  have hS : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∈ insert v T ↔ w = v ∨ w ∈ T := fun w => Finset.mem_insert
  obtain ⟨hk0, hkt⟩ := mulMeasure_setOf_valued_eq_one_ne_zero_and_ne_top v
  set k := LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)
    {y : v.adicCompletion ℚ | Valued.v y = 1} with hk
  refine ⟨k⁻¹, ENNReal.inv_ne_zero.mpr hkt, ENNReal.inv_ne_top.mpr hk0, ?_⟩
  have hΦ : Measurable fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v) :=
    (Idele.measurable_partAt ℚ T).prodMk (measurable_sndAt v)

  have hP : (Idele.partAt ℚ (insert v T) : (AdeleRing (𝓞 ℚ) ℚ)ˣ → (AdeleRing (𝓞 ℚ) ℚ)ˣ) =
      glueAt T v ∘ fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v) :=
    funext fun a => partAt_eq_glueAt T (insert v T) hv hS a

  have hρ : Measure.map (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => (Idele.partAt ℚ T a, (a : AdeleRing (𝓞 ℚ) ℚ).2 v))
      ((Idele.idelicHaar ℚ).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(insert v T) : Set (HeightOneSpectrum (𝓞 ℚ))) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) =
      k⁻¹ • (Idele.sPartMeasure ℚ T).prod
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) := by
    rw [prod_sPartMeasure_mulMeasure_eq_smul_map T (insert v T) hv hS, smul_smul, ENNReal.inv_mul_cancel hk0 hkt,
      one_smul]
  rw [show Idele.sPartMeasure ℚ (insert v T) = Measure.map (Idele.partAt ℚ (insert v T))
      ((Idele.idelicHaar ℚ).restrict
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 ℚ) ℚ (↑(insert v T) : Set (HeightOneSpectrum (𝓞 ℚ))) :
          Set (AdeleRing (𝓞 ℚ) ℚ)ˣ)) from rfl,
    hP, ← Measure.map_map (measurable_glueAt T v) hΦ, hρ, Measure.map_smul]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

private theorem trichotomy_and_ae_zero_aux (finf : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ)
    (f : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ → ℂ)
    (hinf : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, finf a = finf (Idele.partAt ℚ ∅ a)) (S : Finset (HeightOneSpectrum (𝓞 ℚ))) :
    (Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => finf a * ∏ v ∈ S, f v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v))
        (Idele.sPartMeasure ℚ S) →
      (Integrable finf (Idele.sPartMeasure ℚ ∅) ∧
          ∀ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v
            Integrable (f v) (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) ∨
        finf =ᵐ[Idele.sPartMeasure ℚ ∅] 0 ∨
        ∃ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v;
          f v =ᵐ[LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)] 0) ∧
    ((fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => finf a * ∏ v ∈ S, f v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v)) =ᵐ[
        Idele.sPartMeasure ℚ S] 0 →
      finf =ᵐ[Idele.sPartMeasure ℚ ∅] 0 ∨
        ∃ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v;
          f v =ᵐ[LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)] 0) := by
  classical
  refine Finset.induction_on S ?_ ?_
  · refine ⟨fun h => Or.inl ⟨?_, ?_⟩, fun h => Or.inl ?_⟩
    · simpa using h
    · simp
    · simpa using h
  intro v T hv ih
  letI := LanglandsTunnell.TateLocal.localBorel ℚ v
  haveI : SFinite (Idele.sPartMeasure ℚ T) := sfinite_sPartMeasure T
  haveI : SFinite (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)) :=
    sfinite_mulMeasure v
  obtain ⟨c, hc0, hctop, hQ⟩ := sPartMeasure_insert_eq_smul_map_prod T hv
  have hglue : AEMeasurable (glueAt T v) ((Idele.sPartMeasure ℚ T).prod
      (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) :=
    (measurable_glueAt T v).aemeasurable

  have hfibre : ∀ᵐ p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × v.adicCompletion ℚ ∂((Idele.sPartMeasure ℚ T).prod
      (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))), p.2 ≠ 0 := by
    rw [ae_iff]
    have h0 : {p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × v.adicCompletion ℚ | ¬ p.2 ≠ 0} = Set.univ ×ˢ {0} := by
      ext p; simp
    rw [h0, Measure.prod_prod, mulMeasure_singleton_zero v, mul_zero]

  have hae : (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × v.adicCompletion ℚ =>
        finf (glueAt T v p) * ∏ w ∈ insert v T, f w ((glueAt T v p : AdeleRing (𝓞 ℚ) ℚ).2 w)) =ᵐ[
      (Idele.sPartMeasure ℚ T).prod
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))]
      fun p => (finf p.1 * ∏ w ∈ T, f w ((p.1 : AdeleRing (𝓞 ℚ) ℚ).2 w)) * f v p.2 := by
    filter_upwards [hfibre] with p hp
    obtain ⟨b, x⟩ := p
    have hx : x ≠ 0 := hp
    have h1 : finf (glueAt T v (b, x)) = finf b := by
      rw [hinf (glueAt T v (b, x)), partAt_empty_glueAt T v b hx, ← hinf b]
    rw [Finset.prod_insert hv, h1, glueAt_snd_self T hv b hx]
    rw [Finset.prod_congr rfl fun w hw => by rw [glueAt_snd_of_mem T hv b hx hw]]
    ring
  refine ⟨fun hprod => ?_, fun hzero => ?_⟩
  · rw [hQ, integrable_smul_measure hc0 hctop] at hprod
    have hpull := (integrable_map_measure hprod.aestronglyMeasurable hglue).mp hprod
    have hsplit := integrable_mul_prod_or_ae_zero_left_or_right (Idele.sPartMeasure ℚ T)
      (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))
      (fun b => finf b * ∏ w ∈ T, f w ((b : AdeleRing (𝓞 ℚ) ℚ).2 w)) (f v) (hpull.congr hae)
    rcases hsplit with ⟨hG, hfv⟩ | hG0 | hfv0
    · rcases ih.1 hG with ⟨hF, hT⟩ | hF0 | ⟨w, hw, hw0⟩
      · refine Or.inl ⟨hF, fun w hw => ?_⟩
        rcases Finset.mem_insert.mp hw with rfl | hw'
        · exact hfv
        · exact hT w hw'
      · exact Or.inr (Or.inl hF0)
      · exact Or.inr (Or.inr ⟨w, Finset.mem_insert_of_mem hw, hw0⟩)
    · rcases ih.2 hG0 with hF0 | ⟨w, hw, hw0⟩
      · exact Or.inr (Or.inl hF0)
      · exact Or.inr (Or.inr ⟨w, Finset.mem_insert_of_mem hw, hw0⟩)
    · exact Or.inr (Or.inr ⟨v, Finset.mem_insert_self v T, hfv0⟩)
  · rw [hQ] at hzero
    have hbad := ae_iff.mp hzero
    rw [Measure.smul_apply, smul_eq_mul] at hbad
    have hzero' := ae_iff.mpr ((mul_eq_zero.mp hbad).resolve_left hc0)
    have hpull := ae_of_ae_map hglue hzero'
    have hprodzero : (fun p : (AdeleRing (𝓞 ℚ) ℚ)ˣ × v.adicCompletion ℚ =>
        (finf p.1 * ∏ w ∈ T, f w ((p.1 : AdeleRing (𝓞 ℚ) ℚ).2 w)) * f v p.2) =ᵐ[
      (Idele.sPartMeasure ℚ T).prod
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))] 0 :=
      hae.symm.trans hpull
    rcases ae_zero_left_or_right_of_mul_ae_zero (Idele.sPartMeasure ℚ T)
        (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))
        (fun b => finf b * ∏ w ∈ T, f w ((b : AdeleRing (𝓞 ℚ) ℚ).2 w)) (f v) hprodzero with hG0 | hfv0
    · rcases ih.2 hG0 with hF0 | ⟨w, hw, hw0⟩
      · exact Or.inl hF0
      · exact Or.inr ⟨w, Finset.mem_insert_of_mem hw, hw0⟩
    · exact Or.inr ⟨v, Finset.mem_insert_self v T, hfv0⟩

attribute [local instance] NumberField.Idele.ideleBorel NumberField.AdelicHaar.adeleBorel in

theorem solution
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (finf : (AdeleRing (𝓞 ℚ) ℚ)ˣ → ℂ) (f : (v : HeightOneSpectrum (𝓞 ℚ)) → v.adicCompletion ℚ → ℂ)
    (hinf : ∀ a : (AdeleRing (𝓞 ℚ) ℚ)ˣ, finf a = finf (NumberField.Idele.partAt ℚ ∅ a))
    (hprod : Integrable (fun a : (AdeleRing (𝓞 ℚ) ℚ)ˣ => finf a * ∏ v ∈ S, f v ((a : AdeleRing (𝓞 ℚ) ℚ).2 v))
      (NumberField.Idele.sPartMeasure ℚ S)) :
    (Integrable finf (NumberField.Idele.sPartMeasure ℚ ∅) ∧
        ∀ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v
          Integrable (f v) (LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v))) ∨
      finf =ᵐ[NumberField.Idele.sPartMeasure ℚ ∅] 0 ∨
      ∃ v ∈ S, letI := LanglandsTunnell.TateLocal.localBorel ℚ v;
        f v =ᵐ[LanglandsTunnell.TateLocal.mulMeasure (LanglandsTunnell.TateLocal.selfDualHaarAt ℚ v)] 0 := by
  exact (trichotomy_and_ae_zero_aux finf f hinf S).1 hprod

end S_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_integrable_factors_or_eq_zero_of_integrable_sPart (solution)
