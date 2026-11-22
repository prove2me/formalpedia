-- Prove2me | solution 1 for MasulloGRH.tamagawaAdelic_selfDual_stdAdelicCharacter
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:57:10.640809+00:00
-- url     : https://prove2.me/submissions/ad36e200-5684-497b-9e47-7e9477b3201f

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_SLocalStandardCharacter
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure
import Theorems.Thm_MasulloGRH_sAdele_addHaar_image_mul
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_MasulloGRH_tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa
import Theorems.Thm_MasulloGRH_tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain
import Theorems.Thm_NumberField_AdeleRing_secondCountableTopology

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal WithZero

set_option autoImplicit false

namespace Sol_MasulloGRH_tamagawaAdelic_selfDual_stdAdelicCharacter

open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

section Part1

/-- The archimedean trace `Tr_∞ : F_∞ → ℝ`. -/
noncomputable def trInf (u : InfiniteAdeleRing F) : ℝ :=
  ∑ w : InfinitePlace F,
    (w.mult : ℝ) * (InfinitePlace.Completion.extensionEmbedding w (u w)).re

lemma trInf_add (u u' : InfiniteAdeleRing F) : trInf (u + u') = trInf u + trInf u' := by
  unfold trInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (u + u') w = u w + u' w := rfl
  rw [h, map_add, Complex.add_re, mul_add]

lemma trInf_zero : trInf (0 : InfiniteAdeleRing F) = 0 := by
  unfold trInf
  refine Finset.sum_eq_zero fun w _ => ?_
  have h : (0 : InfiniteAdeleRing F) w = 0 := rfl
  rw [h, map_zero, Complex.zero_re, mul_zero]

lemma trInf_neg (u : InfiniteAdeleRing F) : trInf (-u) = -trInf u := by
  unfold trInf
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (-u) w = -(u w) := rfl
  rw [h, map_neg, Complex.neg_re, mul_neg]

lemma trInf_sub (u u' : InfiniteAdeleRing F) : trInf (u - u') = trInf u - trInf u' := by
  rw [sub_eq_add_neg, trInf_add, trInf_neg, sub_eq_add_neg]

/-- `∑_w mult(w) Re(σ_w(a)) = Tr_{F/ℚ}(a)`. -/
lemma sum_mult_re_embedding (a : F) :
    ∑ w : InfinitePlace F, (w.mult : ℝ) * (w.embedding a).re =
      ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  classical
  have h1 : ((Algebra.trace ℚ F a : ℚ) : ℂ) = ∑ φ : F →+* ℂ, φ a := by
    have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := a)
    rw [eq_ratCast] at h
    rw [h]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ) (fun φ => φ a) (fun σ => σ a)
      (fun _ => rfl)).symm
  have h2 : ((Algebra.trace ℚ F a : ℚ) : ℝ) = ∑ φ : F →+* ℂ, (φ a).re := by
    have h := congrArg Complex.re h1
    rw [Complex.re_sum] at h
    simpa using h
  rw [h2, ← Finset.sum_fiberwise Finset.univ InfinitePlace.mk (fun φ : F →+* ℂ => (φ a).re)]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h3 : ∀ φ ∈ (Finset.univ.filter fun φ : F →+* ℂ => InfinitePlace.mk φ = w),
      (φ a).re = (w.embedding a).re := by
    intro φ hφ
    have hφ' := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff] at hφ'
    rcases hφ' with h | h
    · rw [h]
    · rw [← h]; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [Finset.sum_congr rfl h3, Finset.sum_const, InfinitePlace.card_filter_mk_eq, nsmul_eq_mul]

lemma trInf_algebraMap (a : F) :
    trInf (algebraMap F (InfiniteAdeleRing F) a) = ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  rw [← sum_mult_re_embedding]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [InfiniteAdeleRing.algebraMap_apply]
  congr 2
  simp

lemma trace_int (a : 𝓞 F) : ∃ n : ℤ, ((Algebra.trace ℚ F (a : F) : ℚ) : ℝ) = n := by
  refine ⟨Algebra.intTrace ℤ (𝓞 F) a, ?_⟩
  have h := Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := F) (B := 𝓞 F) a
  rw [← h]
  simp

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma sDiagonal_fst (ξ : F) : (sDiagonal Sf ξ).1 = algebraMap F (InfiniteAdeleRing F) ξ := rfl

lemma sDiagonal_snd (ξ : F) (v : Sf) :
    (sDiagonal Sf ξ).2 v =
      algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ := rfl

lemma valued_algebraMap (v : HeightOneSpectrum (𝓞 F)) (ξ : F) :
    Valued.v (algebraMap F (v.adicCompletion F) ξ) = v.valuation F ξ :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ξ

/-- `ξ` is an `S`-integer approximating `x` modulo `∏_{v ∈ S_f} 𝒪_v`. -/
def IsApprox (x : SAdeleRing F Sf) (ξ : F) : Prop :=
  ξ ∈ SIntegers (F := F) Sf ∧
    ∀ v : Sf, (x - sDiagonal Sf ξ).2 v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F

/-- An element of `𝒪_{F,S}` that is integral at all places of `S_f` is in `𝒪_F`. -/
lemma mem_range_of_forall (δ : F) (h1 : δ ∈ SIntegers (F := F) Sf)
    (h2 : ∀ v ∈ Sf, v.valuation F δ ≤ 1) : δ ∈ (algebraMap (𝓞 F) F).range := by
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F δ fun v => ?_
  by_cases hv : v ∈ Sf
  · exact h2 v hv
  · exact h1 v hv

/-- Well-definedness of the standard character. -/
lemma sStdCharacter_eq (x : SAdeleRing F Sf) (ξ : F) (h : IsApprox Sf x ξ) :
    sStdCharacter Sf x =
      Complex.exp (-(2 * Real.pi * Complex.I) * (trInf ((x - sDiagonal Sf ξ).1) : ℂ)) := by
  have hex : ∃ ξ : F, ξ ∈ SIntegers (F := F) Sf ∧
      ∀ v : Sf, (x - sDiagonal Sf ξ).2 v ∈
        (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F := ⟨ξ, h⟩
  unfold sStdCharacter
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  set ξ' := hex.choose with hξ'
  have hsum : (∑ w : InfinitePlace F, (w.mult : ℂ) *
      ((InfinitePlace.Completion.extensionEmbedding w ((x - sDiagonal Sf ξ').1 w)).re : ℂ)) =
      ((trInf ((x - sDiagonal Sf ξ').1) : ℝ) : ℂ) := by
    simp [trInf]
  rw [hsum]
  -- δ = ξ' - ξ is in 𝓞 F
  have hδ : ξ' - ξ ∈ (algebraMap (𝓞 F) F).range := by
    refine mem_range_of_forall Sf _ (Subalgebra.sub_mem _ h1 h.1) fun v hv => ?_
    have e1 := h.2 ⟨v, hv⟩
    have e2 := h2 ⟨v, hv⟩
    have e3 : (x - sDiagonal Sf ξ).2 ⟨v, hv⟩ - (x - sDiagonal Sf ξ').2 ⟨v, hv⟩ ∈
        v.adicCompletionIntegers F := sub_mem e1 e2
    have e4 : (x - sDiagonal Sf ξ).2 ⟨v, hv⟩ - (x - sDiagonal Sf ξ').2 ⟨v, hv⟩ =
        algebraMap F (v.adicCompletion F) (ξ' - ξ) := by
      simp only [Prod.snd_sub, Pi.sub_apply, sDiagonal_snd, map_sub]
      ring
    rw [e4, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap] at e3
    exact e3
  obtain ⟨a, ha⟩ := hδ
  obtain ⟨n, hn⟩ := trace_int a
  have e5 : (x - sDiagonal Sf ξ').1 = (x - sDiagonal Sf ξ).1 -
      algebraMap F (InfiniteAdeleRing F) (ξ' - ξ) := by
    simp only [Prod.fst_sub, sDiagonal_fst, map_sub]
    ring
  have ha' : (algebraMap (𝓞 F) F) a = ξ' - ξ := ha
  rw [e5, trInf_sub, trInf_algebraMap, ← ha', hn, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨n, ?_⟩
  push_cast
  ring

end Part1

section Part5

lemma exists_local_approx (v : HeightOneSpectrum (𝓞 F)) (t : v.adicCompletion F) :
    ∃ a : F, t - algebraMap F (v.adicCompletion F) a ∈ v.adicCompletionIntegers F := by
  have hopen : IsOpen {y : v.adicCompletion F | t - y ∈ v.adicCompletionIntegers F} :=
    (Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage
      (continuous_const.sub continuous_id)
  have hne : {y : v.adicCompletion F | t - y ∈ v.adicCompletionIntegers F}.Nonempty := by
    refine ⟨t, ?_⟩
    show t - t ∈ v.adicCompletionIntegers F
    rw [sub_self]
    exact zero_mem _
  exact (HeightOneSpectrum.denseRange_algebraMap (v := v) (K := F)).exists_mem_open hopen hne

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- Strong approximation: every `S`-adele is congruent to an `S`-integer modulo
`∏_{v ∈ S_f} 𝒪_v`. -/
lemma strong_approx (x : SAdeleRing F Sf) : ∃ ξ, IsApprox Sf x ξ := by
  classical
  choose a ha using fun v : Sf => exists_local_approx (v : HeightOneSpectrum (𝓞 F)) (x.2 v)
  obtain ⟨⟨d, hdmem⟩, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 F))
    (Finset.univ : Finset Sf) a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hdmem
  choose r hr using fun v : Sf => hd v (Finset.mem_univ v)
  have hr' : ∀ v : Sf, algebraMap (𝓞 F) F (r v) = algebraMap (𝓞 F) F d * a v := fun v => by
    rw [hr v, Algebra.smul_def]
  choose n hn using fun w : HeightOneSpectrum (𝓞 F) =>
    (⟨_, w.intValuation_if_neg hd0⟩ : ∃ n : ℕ, w.intValuation d = WithZero.exp (-(n : ℤ)))
  have hfin : {w : HeightOneSpectrum (𝓞 F) | w.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa using hd0)
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Sf ∪ hfin.toFinset)
    (fun w => w.asIdeal) n
    (fun w _ => w.prime) (fun w _ w' _ hww' h => hww' (HeightOneSpectrum.ext h))
    (fun w => if h : (w : HeightOneSpectrum (𝓞 F)) ∈ Sf then r ⟨w, h⟩ else 0)
  have hcS : ∀ v : Sf, (v : HeightOneSpectrum (𝓞 F)).intValuation (c - r v) ≤
      (v : HeightOneSpectrum (𝓞 F)).intValuation d := by
    intro v
    have h := hc v (Finset.mem_union_left _ v.2)
    dsimp only at h
    rw [dif_pos v.2] at h
    rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact h
  have hcT : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ Sf → w.intValuation c ≤ w.intValuation d := by
    intro w hw
    by_cases hwT : w ∈ Sf ∪ hfin.toFinset
    · have h := hc w hwT
      dsimp only at h
      rw [dif_neg hw, sub_zero] at h
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact h
    · have hwd : ¬ w.asIdeal ∣ Ideal.span {d} := fun hdiv =>
        hwT (Finset.mem_union_right _ (hfin.mem_toFinset.2 hdiv))
      have h1 : w.intValuation d = 1 := by
        rw [Ideal.dvd_span_singleton, ← HeightOneSpectrum.intValuation_lt_one_iff_mem,
          not_lt] at hwd
        exact le_antisymm (w.intValuation_le_one d) hwd
      rw [h1]
      exact w.intValuation_le_one c
  have hdF : algebraMap (𝓞 F) F d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
    exact hd0
  have hpos : ∀ w : HeightOneSpectrum (𝓞 F), 0 < w.intValuation d := fun w =>
    zero_lt_iff.2 (w.intValuation_ne_zero d hd0)
  refine ⟨algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d, ?_, ?_⟩
  · intro w hw
    rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (div_le_one₀ (hpos w)).2 (hcT w hw)
  · intro v
    have e : (x - sDiagonal Sf (algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d)).2 v =
        (x.2 v - algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (a v)) +
          algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
            (algebraMap (𝓞 F) F (r v - c) / algebraMap (𝓞 F) F d) := by
      have h1 : algebraMap (𝓞 F) F (r v - c) / algebraMap (𝓞 F) F d =
          a v - algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F d := by
        rw [map_sub, hr' v]
        field_simp
      rw [h1]
      simp only [Prod.snd_sub, Pi.sub_apply, sDiagonal_snd, map_sub]
      ring
    rw [e]
    refine add_mem (ha v) ?_
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_div₀,
      HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
      Valuation.map_sub_swap]
    exact (div_le_one₀ (hpos _)).2 (hcS v)

end Part5

section Char

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma isApprox_add {x y : SAdeleRing F Sf} {ξ η : F} (hx : IsApprox Sf x ξ)
    (hy : IsApprox Sf y η) : IsApprox Sf (x + y) (ξ + η) := by
  refine ⟨Subalgebra.add_mem _ hx.1 hy.1, fun v => ?_⟩
  have e : (x + y - sDiagonal Sf (ξ + η)).2 v = (x - sDiagonal Sf ξ).2 v + (y - sDiagonal Sf η).2 v := by
    simp only [map_add, Prod.snd_sub, Prod.snd_add, Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  exact add_mem (hx.2 v) (hy.2 v)

lemma char_add (x y : SAdeleRing F Sf) :
    sStdCharacter Sf (x + y) = sStdCharacter Sf x * sStdCharacter Sf y := by
  obtain ⟨ξ, hξ⟩ := strong_approx Sf x
  obtain ⟨η, hη⟩ := strong_approx Sf y
  rw [sStdCharacter_eq Sf _ _ (isApprox_add Sf hξ hη), sStdCharacter_eq Sf _ _ hξ,
    sStdCharacter_eq Sf _ _ hη, ← Complex.exp_add]
  congr 1
  have e : (x + y - sDiagonal Sf (ξ + η)).1 = (x - sDiagonal Sf ξ).1 + (y - sDiagonal Sf η).1 := by
    simp only [map_add, Prod.fst_sub, Prod.fst_add]
    ring
  rw [e, trInf_add]
  push_cast
  ring

lemma norm_exp_trInf (t : ℝ) : ‖Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ))‖ = 1 := by
  have e : -(2 * Real.pi * Complex.I) * (t : ℂ) = ((-(2 * Real.pi * t) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

lemma char_norm (x : SAdeleRing F Sf) : ‖sStdCharacter Sf x‖ = 1 := by
  obtain ⟨ξ, hξ⟩ := strong_approx Sf x
  rw [sStdCharacter_eq Sf _ _ hξ]
  exact norm_exp_trInf _

lemma continuous_trInf : Continuous (trInf : InfiniteAdeleRing F → ℝ) := by
  unfold trInf
  refine continuous_finset_sum _ fun w _ => continuous_const.mul ?_
  exact Complex.continuous_re.comp
    ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply w))

lemma char_continuous : Continuous (sStdCharacter Sf : SAdeleRing F Sf → ℂ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨ξ, hξ⟩ := strong_approx Sf x₀
  have hU : IsOpen {x : SAdeleRing F Sf | ∀ v : Sf, (x - sDiagonal Sf ξ).2 v ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F} := by
    rw [Set.ofPred_forall]
    refine isOpen_iInter_of_finite fun v => ?_
    exact (Valued.isOpen_valuationSubring _).preimage
      ((continuous_apply v).comp (continuous_snd.comp (continuous_id.sub continuous_const)))
  have hev : sStdCharacter Sf =ᶠ[nhds x₀] fun x =>
      Complex.exp (-(2 * Real.pi * Complex.I) * (trInf ((x - sDiagonal Sf ξ).1) : ℂ)) := by
    filter_upwards [hU.mem_nhds hξ.2] with x hx
    exact sStdCharacter_eq Sf x ξ ⟨hξ.1, hx⟩
  refine ContinuousAt.congr ?_ hev.symm
  refine Continuous.continuousAt ?_
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp
    (continuous_trInf.comp (continuous_fst.comp (continuous_id.sub continuous_const)))

/-- The archimedean component of the standard character. -/
noncomputable def charInf (a : InfiniteAdeleRing F) : ℂ :=
  Complex.exp (-(2 * Real.pi * Complex.I) *
    ∑ w : InfinitePlace F, (w.mult : ℂ) *
      ((InfinitePlace.Completion.extensionEmbedding w (a w)).re : ℂ))

lemma charInf_eq (a : InfiniteAdeleRing F) :
    charInf a = Complex.exp (-(2 * Real.pi * Complex.I) * (trInf a : ℂ)) := by
  unfold charInf trInf
  push_cast
  rfl

/-- The finite component of the standard character. -/
noncomputable def charFin
    (b : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) : ℂ :=
  sStdCharacter Sf ((0, b) : SAdeleRing F Sf)

lemma char_fst (a : InfiniteAdeleRing F) :
    sStdCharacter Sf ((a, 0) : SAdeleRing F Sf) = charInf a := by
  have h : IsApprox Sf ((a, 0) : SAdeleRing F Sf) 0 := by
    refine ⟨Subalgebra.zero_mem _, fun v => ?_⟩
    rw [map_zero, sub_zero]
    exact zero_mem _
  rw [sStdCharacter_eq Sf _ _ h, charInf_eq, map_zero, sub_zero]

lemma char_split (x : SAdeleRing F Sf) :
    sStdCharacter Sf x = charInf x.1 * charFin Sf x.2 := by
  have e : x = ((x.1, 0) : SAdeleRing F Sf) + ((0, x.2) : SAdeleRing F Sf) := by
    ext <;> simp
  conv_lhs => rw [e]
  rw [char_add, char_fst]
  rfl

lemma char_mul_split (x y : SAdeleRing F Sf) :
    sStdCharacter Sf (x * y) = charInf (x.1 * y.1) * charFin Sf (x.2 * y.2) :=
  char_split Sf (x * y)

lemma charFin_add (b b' : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    charFin Sf (b + b') = charFin Sf b * charFin Sf b' := by
  unfold charFin
  rw [← char_add]
  congr 1
  ext <;> simp

lemma charFin_norm (b : (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    ‖charFin Sf b‖ = 1 := char_norm Sf _

lemma charFin_continuous : Continuous (charFin Sf) :=
  (char_continuous Sf).comp (continuous_const.prodMk continuous_id)

lemma charInf_norm (a : InfiniteAdeleRing F) : ‖charInf a‖ = 1 := by
  rw [charInf_eq]; exact norm_exp_trInf _

lemma charInf_continuous : Continuous (charInf : InfiniteAdeleRing F → ℂ) := by
  have h : (charInf : InfiniteAdeleRing F → ℂ) =
      fun a => Complex.exp (-(2 * Real.pi * Complex.I) * (trInf a : ℂ)) := funext charInf_eq
  rw [h]
  exact Complex.continuous_exp.comp (continuous_const.mul
    (Complex.continuous_ofReal.comp continuous_trInf))

end Char


section Finite

instance secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

instance finHaar (v : HeightOneSpectrum (𝓞 F)) :
    (RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v).IsAddHaarMeasure :=
  RiemannMasullo.finiteLocalAdditiveTamagawaMeasure_isAddHaar F v

instance infAdeleBorel : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

instance infAdeleT2 : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))

instance infAdeleSecondCountable : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- The finite part `∏_{v ∈ S_f} F_v` of the `S`-adeles. -/
abbrev FinPart := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F

/-- The product measure on the finite part. -/
noncomputable abbrev muFin : Measure (FinPart Sf) :=
  Measure.pi fun v : Sf =>
    RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F (v : HeightOneSpectrum (𝓞 F))

/-- The box `∏_{v ∈ S_f} 𝔭_v^{m_v}`. -/
def box (m : Sf → ℤ) : Set (FinPart Sf) :=
  {b | ∀ v : Sf, Valued.v (b v) ≤ WithZero.exp (-(m v))}

lemma exp_mul_le_iff (a b : ℤ) (x : ℤᵐ⁰) :
    WithZero.exp a * x ≤ WithZero.exp b ↔ x ≤ WithZero.exp (b - a) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨c, rfl⟩ : ∃ c : ℤ, x = WithZero.exp c := ⟨WithZero.log x, (WithZero.exp_log hx).symm⟩
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

lemma exists_unif (v : HeightOneSpectrum (𝓞 F)) :
    ∃ ϖ : v.adicCompletion F, ϖ ≠ 0 ∧ Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hval : Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1 : ℤ) := by
    rw [valued_algebraMap, hπ]
  refine ⟨_, fun h => ?_, hval⟩
  rw [h, map_zero] at hval
  exact WithZero.exp_ne_zero hval.symm

/-- A uniformizer of `F_v`. -/
noncomputable def unif (v : HeightOneSpectrum (𝓞 F)) : v.adicCompletion F :=
  (exists_unif v).choose

lemma unif_ne_zero (v : HeightOneSpectrum (𝓞 F)) : unif v ≠ 0 := (exists_unif v).choose_spec.1

lemma valued_unif (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (unif v) = WithZero.exp (-1 : ℤ) := (exists_unif v).choose_spec.2

lemma valued_unif_zpow_mul (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) (t : v.adicCompletion F) :
    Valued.v (unif v ^ j * t) = WithZero.exp (-j) * Valued.v t := by
  rw [map_mul, map_zpow₀, valued_unif, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]

/-- The vector `(ϖ_v^{m_v})_v`. -/
noncomputable def gv (m : Sf → ℤ) : FinPart Sf := fun v => unif (v : HeightOneSpectrum (𝓞 F)) ^ (m v)

lemma gv_mul_gv_neg (m : Sf → ℤ) : gv Sf m * gv Sf (-m) = 1 := by
  funext v
  show unif (v : HeightOneSpectrum (𝓞 F)) ^ (m v) * unif (v : HeightOneSpectrum (𝓞 F)) ^ (-(m v)) = 1
  rw [← zpow_add₀ (unif_ne_zero _), add_neg_cancel, zpow_zero]

lemma box_eq_image (m : Sf → ℤ) : box Sf m = (fun b => gv Sf m * b) '' box Sf 0 := by
  ext b
  constructor
  · intro hb
    refine ⟨gv Sf (-m) * b, fun v => ?_, ?_⟩
    · show Valued.v (unif (v : HeightOneSpectrum (𝓞 F)) ^ (-(m v)) * b v) ≤ WithZero.exp (-(0 : Sf → ℤ) v)
      rw [valued_unif_zpow_mul, exp_mul_le_iff]
      have h := hb v
      have e : -((0 : Sf → ℤ) v) - -(-(m v)) = -(m v) := by simp
      rw [e]; exact h
    · show gv Sf m * (gv Sf (-m) * b) = b
      rw [← mul_assoc, gv_mul_gv_neg, one_mul]
  · rintro ⟨c, hc, rfl⟩ v
    show Valued.v (unif (v : HeightOneSpectrum (𝓞 F)) ^ (m v) * c v) ≤ WithZero.exp (-(m v))
    rw [valued_unif_zpow_mul, exp_mul_le_iff]
    have h := hc v
    have e : -(m v) - -(m v) = -((0 : Sf → ℤ) v) := by simp
    rw [e]; exact h

lemma box_zero_eq : box Sf 0 = Set.univ.pi fun v : Sf =>
    ((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F : Set _) := by
  ext b
  simp only [box, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies, SetLike.mem_coe,
    HeightOneSpectrum.mem_adicCompletionIntegers, Pi.zero_apply, neg_zero, WithZero.exp_zero]

lemma isCompact_box (m : Sf → ℤ) : IsCompact (box Sf m) := by
  rw [box_eq_image]
  refine IsCompact.image ?_ (continuous_const.mul continuous_id)
  rw [box_zero_eq]
  exact isCompact_univ_pi fun v => NumberField.isCompactAdicCompletionIntegers F _

lemma isOpen_box_zero : IsOpen (box Sf 0) := by
  rw [box_zero_eq]
  exact isOpen_set_pi Set.finite_univ fun v _ => NumberField.isOpenAdicCompletionIntegers F _

lemma measurableSet_box (m : Sf → ℤ) : MeasurableSet (box Sf m) :=
  (isCompact_box Sf m).isClosed.measurableSet

theorem finite_mass (v : HeightOneSpectrum (𝓞 F)) :
    RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hne : (v.adicCompletionIntegers F : Set (v.adicCompletion F)).Nonempty :=
    ⟨0, zero_mem _⟩
  have hpos : 0 < RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hO.measure_pos _ hne
  have hμpos : 0 < Measure.addHaar (G := v.adicCompletion F)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := hO.measure_pos _ hne
  have hval : RiemannMasullo.finiteLocalAdditiveTamagawaMeasure F v
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) =
      ((ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ /
        Measure.addHaar (G := v.adicCompletion F)
          (v.adicCompletionIntegers F : Set (v.adicCompletion F))) *
        Measure.addHaar (G := v.adicCompletion F)
          (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := rfl
  have hμtop : Measure.addHaar (G := v.adicCompletion F)
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) ≠ ⊤ := by
    intro htop
    rw [hval, htop, ENNReal.div_top, zero_mul] at hpos
    exact lt_irrefl _ hpos
  rw [hval]
  exact ENNReal.div_mul_cancel hμpos.ne' hμtop

lemma muFin_box_zero : muFin Sf (box Sf 0) = ∏ v : Sf,
    (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
      multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  rw [box_zero_eq, Measure.pi_pi]
  exact Finset.prod_congr rfl fun v _ => finite_mass _

end Finite


section FiniteMeasure

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

theorem toNNReal_exp {e : ℝ≥0} (he : e ≠ 0) (n : ℤ) :
    WithZeroMulInt.toNNReal he (WithZero.exp n) = e ^ n := by
  have h : WithZero.unzero (WithZero.exp_ne_zero : WithZero.exp n ≠ 0) = Multiplicative.ofAdd n :=
    WithZero.unzero_coe _
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero, h, toAdd_ofAdd]

lemma norm_unif_zpow (v : HeightOneSpectrum (𝓞 F)) (j : ℤ) :
    ‖unif v ^ j‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-j) := by
  rw [NumberField.FinitePlace.norm_def, map_zpow₀, valued_unif, ← WithZero.exp_zsmul,
    smul_eq_mul, mul_neg, mul_one, toNNReal_exp, NNReal.coe_zpow, NNReal.coe_natCast]

/-- The `S`-idele `(1, (ϖ_v^{m_v})_v)`. -/
noncomputable def gIdele (m : Sf → ℤ) : SIdeleGroup F Sf where
  val := (1, gv Sf m)
  inv := (1, gv Sf (-m))
  val_inv := by
    ext1
    · exact mul_one _
    · exact gv_mul_gv_neg Sf m
  inv_val := by
    ext1
    · exact mul_one _
    · rw [Prod.snd_mul, mul_comm]; exact gv_mul_gv_neg Sf m

lemma sIdeleNorm_gIdele (m : Sf → ℤ) :
    sIdeleNorm Sf (gIdele Sf m) = ∏ v : Sf, (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^ (-(m v)) := by
  unfold sIdeleNorm
  have h1 : ∀ w : InfinitePlace F, ‖((gIdele Sf m : SIdeleGroup F Sf) : SAdeleRing F Sf).1 w‖ ^ w.mult = 1 := by
    intro w
    have e : ((1 : InfiniteAdeleRing F) w) = (1 : w.Completion) := rfl
    show ‖(1 : InfiniteAdeleRing F) w‖ ^ w.mult = 1
    rw [e, norm_one, one_pow]
  rw [Finset.prod_congr rfl fun w _ => h1 w, Finset.prod_const_one, one_mul]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact norm_unif_zpow _ (m v)

lemma image_gIdele (m : Sf → ℤ) (K : Set (InfiniteAdeleRing F)) :
    (fun x : SAdeleRing F Sf => ((gIdele Sf m : SIdeleGroup F Sf) : SAdeleRing F Sf) * x) ''
      (K ×ˢ box Sf 0) = K ×ˢ box Sf m := by
  rw [box_eq_image Sf m]
  ext ⟨a, b⟩
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨ha', hb'⟩, h⟩
    have h1 : (1 : InfiniteAdeleRing F) * a' = a := congrArg Prod.fst h
    have h2 : gv Sf m * b' = b := congrArg Prod.snd h
    rw [one_mul] at h1
    subst h1
    exact ⟨ha', b', hb', h2⟩
  · rintro ⟨ha, b', hb', h2⟩
    refine ⟨(a, b'), ⟨ha, hb'⟩, ?_⟩
    show ((1 : InfiniteAdeleRing F) * a, gv Sf m * b') = (a, b)
    rw [one_mul]
    exact Prod.ext rfl h2

lemma muFin_box (m : Sf → ℤ) :
    muFin Sf (box Sf m) = ENNReal.ofReal (∏ v : Sf,
      (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^ (-(m v))) *
        muFin Sf (box Sf 0) := by
  have := sAdditiveTamagawa_isAddHaarMeasure F Sf
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : InfiniteAdeleRing F)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hB : MeasurableSet (K ×ˢ box Sf 0) := hKm.prod (measurableSet_box Sf 0)
  have himg := sAdele_addHaar_image_mul F Sf (sAdditiveTamagawa F Sf) (gIdele Sf m)
    (K ×ˢ box Sf 0) hB
  rw [image_gIdele, sIdeleNorm_gIdele] at himg
  have hprod : ∀ X : Set (FinPart Sf), sAdditiveTamagawa F Sf (K ×ˢ X) =
      infiniteAdditiveTamagawa F K * muFin Sf X := fun X => Measure.prod_prod _ _
  rw [hprod, hprod] at himg
  have hpos : 0 < sAdditiveTamagawa F Sf (K ×ˢ box Sf 0) := by
    refine MeasureTheory.Measure.measure_pos_of_mem_nhds (x := (0 : SAdeleRing F Sf)) _ ?_
    have h0 : (0 : SAdeleRing F Sf) = ((0 : InfiniteAdeleRing F), (0 : FinPart Sf)) := rfl
    rw [h0]
    exact prod_mem_nhds hK0 ((isOpen_box_zero Sf).mem_nhds fun v => by simp)
  have hfin : sAdditiveTamagawa F Sf (K ×ˢ box Sf 0) < ⊤ :=
    (hKc.prod (isCompact_box Sf 0)).measure_lt_top
  rw [hprod] at hpos hfin
  have hK0' : infiniteAdditiveTamagawa F K ≠ 0 := by
    intro h; rw [h, zero_mul] at hpos; exact lt_irrefl _ hpos
  have hB0 : muFin Sf (box Sf 0) ≠ 0 := by
    intro h; rw [h, mul_zero] at hpos; exact lt_irrefl _ hpos
  have hKt : infiniteAdditiveTamagawa F K ≠ ⊤ := by
    intro h; rw [h, ENNReal.top_mul hB0] at hfin; exact lt_irrefl _ hfin
  rw [mul_left_comm] at himg
  exact (ENNReal.mul_right_inj hK0' hKt).1 himg

lemma muFin_box_toReal (m : Sf → ℤ) :
    (muFin Sf (box Sf m)).toReal = ∏ v : Sf,
      ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^ (-(m v)) /
        Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)))) := by
  rw [muFin_box, muFin_box_zero, ENNReal.toReal_mul, ENNReal.toReal_prod,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun v _ => zpow_nonneg (Nat.cast_nonneg _) _),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), div_eq_mul_inv]

end FiniteMeasure


section BoxAnnihilator

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma exists_int_of_exp_eq_one (t : ℝ)
    (h : Complex.exp (-(2 * Real.pi * Complex.I) * (t : ℂ)) = 1) : ∃ n : ℤ, t = n := by
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  refine ⟨-n, ?_⟩
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have h3 : (t : ℂ) = ((-n : ℤ) : ℂ) := by
    have h4 : (2 * Real.pi * Complex.I) * (t : ℂ) =
        (2 * Real.pi * Complex.I) * ((-n : ℤ) : ℂ) := by
      push_cast; linear_combination -hn
    exact mul_left_cancel₀ h2 h4
  exact_mod_cast h3

lemma mul_mem_range_of_dual (ζ : F)
    (hζ : ∀ a : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a * ζ) = n)
    (d : 𝓞 F) (hd : d ∈ differentIdeal ℤ (𝓞 F)) :
    algebraMap (𝓞 F) F d * ζ ∈ (algebraMap (𝓞 F) F).range := by
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := one_ne_zero
  have h1 : ζ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [FractionalIdeal.mem_dual h10]
    intro a ha
    rw [FractionalIdeal.mem_one_iff] at ha
    obtain ⟨a', rfl⟩ := ha
    obtain ⟨n, hn⟩ := hζ a'
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, mul_comm, hn]
    simp
  have h2 : algebraMap (𝓞 F) F d ∈
      (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F))⁻¹ := by
    rw [← coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)]
    exact (FractionalIdeal.mem_coeIdeal _).2 ⟨d, hd, rfl⟩
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [inv_mul_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ h10),
    FractionalIdeal.mem_one_iff] at h3
  obtain ⟨c, hc⟩ := h3
  exact ⟨c, hc⟩

/-- `Tr(ξ) ∈ ℤ` as soon as `ξ 𝔡 ⊆ 𝒪_F`. -/
lemma trace_int_of_mul_mem (ξ : F)
    (h : ∀ a ∈ differentIdeal ℤ (𝓞 F), algebraMap (𝓞 F) F a * ξ ∈ (algebraMap (𝓞 F) F).range) :
    ∃ n : ℤ, ((Algebra.trace ℚ F ξ : ℚ) : ℝ) = n := by
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := one_ne_zero
  have hD0 : ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
  have hdual : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
      ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (nonZeroDivisors (𝓞 F)) F)⁻¹ := by
    rw [coeIdeal_differentIdeal ℤ ℚ F (𝓞 F), inv_inv]
  have hξ : ξ ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) := by
    rw [hdual, FractionalIdeal.mem_inv_iff hD0]
    intro y hy
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    rw [FractionalIdeal.mem_one_iff]
    obtain ⟨c, hc⟩ := h a ha
    exact ⟨c, by rw [hc, mul_comm]⟩
  rw [FractionalIdeal.mem_dual h10] at hξ
  obtain ⟨n, hn⟩ := hξ 1 (FractionalIdeal.one_mem_one _)
  refine ⟨n, ?_⟩
  rw [Algebra.traceForm_apply, mul_one] at hn
  rw [← hn]
  simp

lemma intValuation_le_of_mem_different (w : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F)
    (ha : a ∈ differentIdeal ℤ (𝓞 F)) :
    w.intValuation a ≤
      WithZero.exp (-(multiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  rw [HeightOneSpectrum.intValuation_le_pow_iff_mem]
  exact Ideal.le_of_dvd (pow_multiplicity_dvd _ _) ha

/-- An `S`-integer with `v(ξ) ≤ q_v^{d_v}` at the places of `S_f` has integral trace. -/
lemma trace_int_of_valuation (ξ : F) (hS : ξ ∈ SIntegers (F := F) Sf)
    (hv : ∀ v : Sf, (v : HeightOneSpectrum (𝓞 F)).valuation F ξ ≤
      WithZero.exp (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
        (differentIdeal ℤ (𝓞 F)) : ℤ)) :
    ∃ n : ℤ, ((Algebra.trace ℚ F ξ : ℚ) : ℝ) = n := by
  refine trace_int_of_mul_mem ξ fun a ha => ?_
  refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun w => ?_
  rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hw : w ∈ Sf
  · calc w.intValuation a * w.valuation F ξ
        ≤ WithZero.exp (-(multiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) *
            WithZero.exp (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ) :=
          mul_le_mul' (intValuation_le_of_mem_different w a ha) (hv ⟨w, hw⟩)
      _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
  · calc w.intValuation a * w.valuation F ξ ≤ 1 * 1 :=
          mul_le_mul' (w.intValuation_le_one a) (hS w hw)
      _ = 1 := one_mul 1

lemma charFin_eq_of_approx (t : FinPart Sf) (ξ : F) (hξ : ξ ∈ SIntegers (F := F) Sf)
    (h : ∀ v : Sf, t v - algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ ∈
      (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F) :
    charFin Sf t =
      Complex.exp (-(2 * Real.pi * Complex.I) * ((0 - ((Algebra.trace ℚ F ξ : ℚ) : ℝ) : ℝ) : ℂ)) := by
  have hA : IsApprox Sf ((0, t) : SAdeleRing F Sf) ξ := ⟨hξ, fun v => h v⟩
  unfold charFin
  rw [sStdCharacter_eq Sf _ _ hA]
  have e : (((0, t) : SAdeleRing F Sf) - sDiagonal Sf ξ).1 =
      0 - algebraMap F (InfiniteAdeleRing F) ξ := rfl
  rw [e, trInf_sub, trInf_zero, trInf_algebraMap]

lemma one_le_exp_nat (d : ℕ) : (1 : ℤᵐ⁰) ≤ WithZero.exp (d : ℤ) := by
  rw [← WithZero.exp_zero, WithZero.exp_le_exp]; exact_mod_cast Nat.zero_le d

lemma annihilates (k : Sf → ℤ) (u y : FinPart Sf)
    (hu : ∀ v : Sf, Valued.v (u v) ≤ WithZero.exp (k v +
      (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)))
    (hy : ∀ v : Sf, Valued.v (y v) ≤ WithZero.exp (-(k v))) :
    sStdCharacter Sf ((0, y * u) : SAdeleRing F Sf) = 1 := by
  obtain ⟨ξ, hξS, hξ2⟩ := strong_approx Sf ((0, y * u) : SAdeleRing F Sf)
  have hv : ∀ v : Sf, (v : HeightOneSpectrum (𝓞 F)).valuation F ξ ≤
      WithZero.exp (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
        (differentIdeal ℤ (𝓞 F)) : ℤ) := by
    intro v
    have h1 : Valued.v ((y * u) v) ≤ WithZero.exp (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
        (differentIdeal ℤ (𝓞 F)) : ℤ) := by
      have e : (y * u) v = y v * u v := rfl
      rw [e, map_mul]
      calc Valued.v (y v) * Valued.v (u v) ≤ WithZero.exp (-(k v)) * WithZero.exp (k v +
          (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) :=
            mul_le_mul' (hy v) (hu v)
        _ = _ := by rw [← WithZero.exp_add]; congr 1; ring
    have h2 : Valued.v ((y * u) v - algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ)
        ≤ 1 := hξ2 v
    rw [← valued_algebraMap]
    have e2 : algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ =
        (y * u) v - ((y * u) v - algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ) := by
      ring
    rw [e2]
    exact Valuation.map_sub_le _ h1 (h2.trans (one_le_exp_nat _))
  obtain ⟨n, hn⟩ := trace_int_of_valuation Sf ξ hξS hv
  have hc := charFin_eq_of_approx Sf (y * u) ξ hξS (fun v => hξ2 v)
  unfold charFin at hc
  rw [hc, hn]
  have e : -(2 * Real.pi * Complex.I) * ((0 - (n : ℝ) : ℝ) : ℂ) = (n : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_int_mul_two_pi_mul_I]

end BoxAnnihilator


section BoxAnnihilator2

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

lemma not_dvd_different_succ (w : HeightOneSpectrum (𝓞 F)) :
    ¬ w.asIdeal ^ (multiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)) + 1) ∣
      differentIdeal ℤ (𝓞 F) := by
  have hfin : FiniteMultiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)) := by
    refine FiniteMultiplicity.of_not_isUnit ?_ ?_
    · rw [Ideal.isUnit_iff]; exact w.isPrime.ne_top
    · rw [Ne, Ideal.zero_eq_bot]
      exact differentIdeal_ne_bot
  exact hfin.not_pow_dvd_of_multiplicity_lt (Nat.lt_succ_self _)

lemma exists_different_val (w : HeightOneSpectrum (𝓞 F)) :
    ∃ a ∈ differentIdeal ℤ (𝓞 F),
      WithZero.exp (-((multiplicity w.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ) + 1)) <
        w.intValuation a := by
  have h := not_dvd_different_succ w
  rw [Ideal.dvd_iff_le] at h
  obtain ⟨a, ha, hna⟩ := SetLike.not_le_iff_exists.1 h
  refine ⟨a, ha, ?_⟩
  rw [← not_le]
  intro hle
  apply hna
  rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem]
  convert hle using 2
  push_cast
  ring

lemma exp_div_le {x : ℤᵐ⁰} {a c : ℤ} (hx : x ≤ WithZero.exp a) :
    x / WithZero.exp c ≤ WithZero.exp (a - c) := by
  rw [div_eq_mul_inv, ← WithZero.exp_neg, sub_eq_add_neg, WithZero.exp_add]
  exact mul_le_mul_left hx _

lemma forward (k : Sf → ℤ) (u : FinPart Sf)
    (h : ∀ y : FinPart Sf, (∀ v : Sf, Valued.v (y v) ≤ WithZero.exp (-(k v))) →
      sStdCharacter Sf ((0, y * u) : SAdeleRing F Sf) = 1) (v₀ : Sf) :
    Valued.v (u v₀) ≤ WithZero.exp (k v₀ +
      (multiplicity (v₀ : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  classical
  obtain ⟨a, ha, hlta⟩ := exists_different_val (v₀ : HeightOneSpectrum (𝓞 F))
  obtain ⟨d, hd⟩ : ∃ d : ℕ, multiplicity (v₀ : HeightOneSpectrum (𝓞 F)).asIdeal
      (differentIdeal ℤ (𝓞 F)) = d := ⟨_, rfl⟩
  rw [hd] at hlta ⊢
  by_contra hlt
  push Not at hlt
  -- a global element with valuation `q^{d+1}` at `v₀`, integral elsewhere
  obtain ⟨ξ, hξS, hξ2⟩ := strong_approx Sf
    ((0, Pi.single v₀ (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1)))) : SAdeleRing F Sf)
  have hother : ∀ v : Sf, v₀ ≠ v →
      Valued.v (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ) ≤ 1 := by
    intro v hv
    have h2 := hξ2 v
    have e : (((0, Pi.single v₀ (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1)))) :
        SAdeleRing F Sf) - sDiagonal Sf ξ).2 v =
        -(algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ) := by
      show (Pi.single v₀ (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1))) : FinPart Sf) v -
        algebraMap F _ ξ = _
      rw [Pi.single_eq_of_ne (Ne.symm hv), zero_sub]
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_neg] at h2
    exact h2
  have hv₀ : Valued.v (algebraMap F ((v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ) =
      WithZero.exp ((d : ℤ) + 1) := by
    have h2 := hξ2 v₀
    have e : (((0, Pi.single v₀ (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1)))) :
        SAdeleRing F Sf) - sDiagonal Sf ξ).2 v₀ =
        unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1)) - algebraMap F _ ξ := by
      show (Pi.single v₀ (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1))) : FinPart Sf) v₀ -
        algebraMap F _ ξ = _
      rw [Pi.single_eq_same]
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers] at h2
    have hg : Valued.v (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1))) =
        WithZero.exp ((d : ℤ) + 1) := by
      rw [map_zpow₀, valued_unif, ← WithZero.exp_zsmul, smul_eq_mul]
      congr 1; ring
    have hlt1 : Valued.v (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1)) -
        algebraMap F _ ξ) < Valued.v (unif (v₀ : HeightOneSpectrum (𝓞 F)) ^ (-((d : ℤ) + 1))) := by
      rw [hg]
      refine lt_of_le_of_lt h2 ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have h5 := Valuation.map_sub_eq_of_lt_left Valued.v hlt1
    rw [sub_sub_cancel] at h5
    rw [h5, hg]
  -- some `a' ∈ 𝒪_F` with `Tr(a' ξ) ∉ ℤ`
  have hex : ∃ a' : 𝓞 F, ∀ n : ℤ, Algebra.trace ℚ F (algebraMap (𝓞 F) F a' * ξ) ≠ n := by
    by_contra hall
    push Not at hall
    obtain ⟨c, hc⟩ := mul_mem_range_of_dual ξ hall a ha
    have h1 : (v₀ : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a * ξ) ≤ 1 := by
      rw [← hc]; exact HeightOneSpectrum.valuation_le_one _ c
    rw [map_mul, HeightOneSpectrum.valuation_of_algebraMap, ← valued_algebraMap, hv₀] at h1
    have ha0 : (v₀ : HeightOneSpectrum (𝓞 F)).intValuation a ≠ 0 := ne_of_gt
      (lt_of_le_of_lt (zero_le') hlta)
    obtain ⟨e, he⟩ : ∃ e : ℤ, (v₀ : HeightOneSpectrum (𝓞 F)).intValuation a = WithZero.exp e :=
      ⟨WithZero.log _, (WithZero.exp_log ha0).symm⟩
    rw [he, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    rw [he, WithZero.exp_lt_exp] at hlta
    omega
  obtain ⟨a', ha'⟩ := hex
  have hu0 : u v₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hlt
    exact not_lt_zero' hlt
  obtain ⟨t0, ht0⟩ : ∃ t0 : (v₀ : HeightOneSpectrum (𝓞 F)).adicCompletion F,
      t0 = algebraMap F _ (algebraMap (𝓞 F) F a' * ξ) := ⟨_, rfl⟩
  have hint : ∀ v : Sf, v₀ ≠ v → Valued.v (algebraMap F
      ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) (algebraMap (𝓞 F) F a' * ξ)) ≤ 1 := by
    intro v hv
    rw [map_mul, map_mul]
    calc Valued.v (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
          (algebraMap (𝓞 F) F a')) *
          Valued.v (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F) ξ) ≤ 1 * 1 := by
          refine mul_le_mul' ?_ (hother v hv)
          rw [valued_algebraMap]; exact HeightOneSpectrum.valuation_le_one _ a'
      _ = 1 := one_mul 1
  have hyu : ∀ v : Sf, ((Pi.single v₀ (t0 / u v₀) : FinPart Sf) * u) v =
      (Pi.single v₀ t0 : FinPart Sf) v := by
    intro v
    by_cases hv : v₀ = v
    · subst hv
      show (Pi.single v₀ (t0 / u v₀) : FinPart Sf) v₀ * u v₀ = (Pi.single v₀ t0 : FinPart Sf) v₀
      rw [Pi.single_eq_same, Pi.single_eq_same, div_mul_cancel₀ _ hu0]
    · show (Pi.single v₀ (t0 / u v₀) : FinPart Sf) v * u v = (Pi.single v₀ t0 : FinPart Sf) v
      rw [Pi.single_eq_of_ne (Ne.symm hv), Pi.single_eq_of_ne (Ne.symm hv), zero_mul]
  have hybox : ∀ v : Sf, Valued.v ((Pi.single v₀ (t0 / u v₀) : FinPart Sf) v) ≤
      WithZero.exp (-(k v)) := by
    intro v
    by_cases hv : v₀ = v
    · subst hv
      rw [Pi.single_eq_same, map_div₀]
      obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (u v₀) = WithZero.exp c :=
        ⟨WithZero.log _, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hu0)).symm⟩
      have ht : Valued.v t0 ≤ WithZero.exp ((d : ℤ) + 1) := by
        rw [ht0, map_mul, map_mul, hv₀, valued_algebraMap]
        calc (v₀ : HeightOneSpectrum (𝓞 F)).valuation F (algebraMap (𝓞 F) F a') *
            WithZero.exp ((d : ℤ) + 1) ≤ 1 * WithZero.exp ((d : ℤ) + 1) :=
              mul_le_mul_left (HeightOneSpectrum.valuation_le_one _ a') _
          _ = _ := one_mul _
      rw [hc]
      refine (exp_div_le ht).trans ?_
      rw [hc, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      omega
    · rw [Pi.single_eq_of_ne (Ne.symm hv), map_zero]
      exact zero_le'
  have hval := h _ hybox
  have hyu' : (Pi.single v₀ (t0 / u v₀) : FinPart Sf) * u = (Pi.single v₀ t0 : FinPart Sf) :=
    funext hyu
  rw [hyu'] at hval
  have hA := charFin_eq_of_approx Sf (Pi.single v₀ t0 : FinPart Sf) (algebraMap (𝓞 F) F a' * ξ)
    (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ a') hξS) (fun v => by
      by_cases hv : v₀ = v
      · subst hv
        rw [Pi.single_eq_same, ht0, sub_self]
        exact zero_mem _
      · rw [Pi.single_eq_of_ne (Ne.symm hv), zero_sub, HeightOneSpectrum.mem_adicCompletionIntegers,
          Valuation.map_neg]
        exact hint v hv)
  unfold charFin at hA
  rw [hA] at hval
  obtain ⟨n, hn⟩ := exists_int_of_exp_eq_one _ hval
  apply ha' (-n)
  have : ((Algebra.trace ℚ F (algebraMap (𝓞 F) F a' * ξ) : ℚ) : ℝ) = ((-n : ℤ) : ℝ) := by
    push_cast; linarith
  exact_mod_cast this

theorem box_annihilator (k : Sf → ℤ) (u : FinPart Sf) :
    (∀ y : FinPart Sf, (∀ v : Sf, Valued.v (y v) ≤ WithZero.exp (-(k v))) →
        sStdCharacter Sf ((0, y * u) : SAdeleRing F Sf) = 1) ↔
      ∀ v : Sf, Valued.v (u v) ≤ WithZero.exp (k v +
        (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) :=
  ⟨fun h v => forward Sf k u h v, fun hu y hy => annihilates Sf k u y hu hy⟩

end BoxAnnihilator2


section Lattices

open Filter Topology

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- The exponent `d_v` of `𝔭_v` in the different. -/
noncomputable def dExp (v : Sf) : ℤ :=
  (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)

/-- `L n = ∏_v 𝔭_v^{-n}`. -/
def Lset (n : ℕ) : Set (FinPart Sf) := box Sf (fun _ => -(n : ℤ))

/-- `M n = ∏_v 𝔭_v^{n - d_v}`, the annihilator of `L n`. -/
def Mset (n : ℕ) : Set (FinPart Sf) := box Sf (fun v => (n : ℤ) - dExp Sf v)

/-- `c n = ν(L n)`. -/
noncomputable def cfun (n : ℕ) : ℝ := (muFin Sf (Lset Sf n)).toReal

lemma mem_Mset (n : ℕ) (u : FinPart Sf) :
    u ∈ Mset Sf n ↔ ∀ v : Sf, Valued.v (u v) ≤ WithZero.exp (-(n : ℤ) +
      (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  unfold Mset box dExp
  simp only [Set.mem_setOf_eq, neg_sub]
  refine forall_congr' fun v => ?_
  rw [sub_eq_neg_add]

lemma box_add_mem {m : Sf → ℤ} {y y' : FinPart Sf} (hy : y ∈ box Sf m) (hy' : y' ∈ box Sf m) :
    y + y' ∈ box Sf m := fun v => Valuation.map_add_le _ (hy v) (hy' v)

lemma box_neg_mem {m : Sf → ℤ} {y : FinPart Sf} (hy : y ∈ box Sf m) : -y ∈ box Sf m := by
  intro v
  have h : (-y) v = -(y v) := rfl
  rw [h, Valuation.map_neg]
  exact hy v

lemma box_mono {m m' : Sf → ℤ} (h : ∀ v, m' v ≤ m v) : box Sf m ⊆ box Sf m' := by
  intro b hb v
  refine (hb v).trans ?_
  rw [WithZero.exp_le_exp]
  linarith [h v]

lemma Lset_mono : Monotone (Lset Sf) := by
  intro n n' hnn'
  refine box_mono Sf fun v => ?_
  have : (n : ℤ) ≤ n' := by exact_mod_cast hnn'
  linarith

lemma Mset_anti : Antitone (Mset Sf) := by
  intro n n' hnn'
  refine box_mono Sf fun v => ?_
  have : (n : ℤ) ≤ n' := by exact_mod_cast hnn'
  linarith

lemma Lset_iUnion : ⋃ n, Lset Sf n = Set.univ := by
  refine Set.eq_univ_of_forall fun b => ?_
  have h : ∀ v : Sf, ∀ᶠ n : ℕ in atTop, Valued.v (b v) ≤ WithZero.exp (-(-(n : ℤ))) := by
    intro v
    rcases eq_or_ne (b v) 0 with h0 | h0
    · refine Eventually.of_forall fun n => ?_
      rw [h0, map_zero]
      exact zero_le'
    · have hv : Valued.v (b v) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
      obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (b v) = WithZero.exp c :=
        ⟨WithZero.log _, (WithZero.exp_log hv).symm⟩
      refine eventually_atTop.2 ⟨c.toNat, fun n hn => ?_⟩
      rw [hc, WithZero.exp_le_exp]
      have : (c.toNat : ℤ) ≤ n := by exact_mod_cast hn
      omega
  obtain ⟨n, hn⟩ := (eventually_all.2 h).exists
  exact Set.mem_iUnion.2 ⟨n, hn⟩

lemma Mset_iInter (x : FinPart Sf) (hx : x ∈ ⋂ n, Mset Sf n) : x = 0 := by
  funext v
  by_contra h0
  have hv : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
  obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (x v) = WithZero.exp c :=
    ⟨WithZero.log _, (WithZero.exp_log hv).symm⟩
  have h1 : Valued.v (x v) ≤ WithZero.exp (-(((dExp Sf v - c + 1).toNat : ℤ) - dExp Sf v)) :=
    (Set.mem_iInter.1 hx (dExp Sf v - c + 1).toNat) v
  rw [hc, WithZero.exp_le_exp] at h1
  have h2 : ((dExp Sf v - c + 1).toNat : ℤ) ≥ dExp Sf v - c + 1 := Int.self_le_toNat _
  omega

lemma Mset_small (U : Set (FinPart Sf)) (hU : U ∈ 𝓝 (0 : FinPart Sf)) :
    ∀ᶠ n in atTop, Mset Sf n ⊆ U := by
  have hdir : Directed (· ⊇ ·) (Mset Sf) := fun i j =>
    ⟨max i j, Mset_anti Sf (le_max_left i j), Mset_anti Sf (le_max_right i j)⟩
  obtain ⟨n₀, hn₀⟩ := exists_subset_nhds_of_isCompact' hdir (fun n => isCompact_box Sf _)
    (fun n => (isCompact_box Sf _).isClosed) (U := U) (fun x hx => by
      rw [Mset_iInter Sf x hx]; exact hU)
  exact eventually_atTop.2 ⟨n₀, fun n hn => (Mset_anti Sf hn).trans hn₀⟩

lemma absNorm_pos (v : HeightOneSpectrum (𝓞 F)) : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  have h : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  exact_mod_cast Nat.pos_of_ne_zero h

lemma cfun_mul (n : ℕ) : cfun Sf n * (muFin Sf (Mset Sf n)).toReal = 1 := by
  unfold cfun Lset Mset
  rw [muFin_box_toReal, muFin_box_toReal, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hq := absNorm_pos (v : HeightOneSpectrum (𝓞 F))
  set q : ℝ := (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) with hqdef
  have hs : Real.sqrt (q ^ multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
      (differentIdeal ℤ (𝓞 F))) * Real.sqrt (q ^ multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
      (differentIdeal ℤ (𝓞 F))) = q ^ multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
      (differentIdeal ℤ (𝓞 F)) := Real.mul_self_sqrt (pow_nonneg hq.le _)
  have hpos : 0 < q ^ multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
      (differentIdeal ℤ (𝓞 F)) := pow_pos hq _
  rw [div_mul_div_comm, hs, ← zpow_add₀ hq.ne']
  have e : -(-(n : ℤ)) + -((n : ℤ) - dExp Sf v) = ((multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal
      (differentIdeal ℤ (𝓞 F)) : ℕ) : ℤ) := by unfold dExp; ring
  rw [e, zpow_natCast, div_self hpos.ne']

lemma integral_char_Lset (n : ℕ) (b : FinPart Sf) :
    ∫ y in Lset Sf n, charFin Sf (y * b) ∂(muFin Sf) =
      Set.indicator (Mset Sf n) (fun _ => (cfun Sf n : ℂ)) b := by
  have hL : MeasurableSet (Lset Sf n) := measurableSet_box Sf _
  have hann := box_annihilator Sf (fun _ => -(n : ℤ)) b
  by_cases hb : ∀ y ∈ Lset Sf n, charFin Sf (y * b) = 1
  · have hbM : b ∈ Mset Sf n := (mem_Mset Sf n b).2 (hann.1 fun y hy => hb y hy)
    rw [Set.indicator_of_mem hbM, setIntegral_congr_fun hL (fun y hy => hb y hy),
      setIntegral_const, Complex.real_smul, mul_one]
    rfl
  · push Not at hb
    obtain ⟨y₀, hy₀, hne⟩ := hb
    have hbM : b ∉ Mset Sf n := by
      intro h
      exact hne (hann.2 ((mem_Mset Sf n b).1 h) y₀ hy₀)
    rw [Set.indicator_of_notMem hbM]
    set I := ∫ y in Lset Sf n, charFin Sf (y * b) ∂(muFin Sf) with hI
    have hshift : I = charFin Sf (y₀ * b) * I := by
      have h1 : I = ∫ y, (Lset Sf n).indicator (fun y => charFin Sf (y * b)) (y₀ + y) ∂(muFin Sf) := by
        rw [integral_add_left_eq_self, integral_indicator hL]
      have h2 : (fun y => (Lset Sf n).indicator (fun y => charFin Sf (y * b)) (y₀ + y)) =
          (Lset Sf n).indicator (fun y => charFin Sf (y₀ * b) * charFin Sf (y * b)) := by
        funext y
        by_cases hy : y ∈ Lset Sf n
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y₀ + y ∈ Lset Sf n from box_add_mem Sf hy₀ hy), add_mul,
            charFin_add]
        · have hy' : y₀ + y ∉ Lset Sf n := fun h => hy (by
            have := box_add_mem Sf (box_neg_mem Sf (show y₀ ∈ box Sf (fun _ => -(n : ℤ)) from hy₀)) h
            rwa [neg_add_cancel_left] at this)
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
      refine h1.trans ?_
      rw [h2, integral_indicator hL, integral_const_mul, hI]
    have h3 : (1 - charFin Sf (y₀ * b)) * I = 0 := by linear_combination hshift
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

end Lattices


section Partial

open Filter Topology

/-- Partial Fourier inversion.  `V` carries a character `E` for which Fourier inversion holds;
`N` carries a character `χ` and two sequences of sets `L n ↑ N`, `M n ↓ 0` with
`∫_{L n} χ(y b) dy = c n · 1_{M n}(b)` and `c n · μ(M n) = 1`.  Then Fourier inversion holds on
`V × N` for the product character and the product measure. -/
theorem partial_inversion
    {V N : Type*} [CommRing V] [TopologicalSpace V] [IsTopologicalRing V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [LocallyCompactSpace V]
    [CommRing N] [TopologicalSpace N] [IsTopologicalRing N] [T2Space N]
    [MeasurableSpace N] [BorelSpace N] [SecondCountableTopology N]
    (μV : Measure V) (μN : Measure N) [SigmaFinite μV] [SigmaFinite μN]
    [IsFiniteMeasureOnCompacts μN] [IsLocallyFiniteMeasure μN] [μN.IsAddLeftInvariant]
    (E : V → ℂ) (χ : N → ℂ)
    (hE : Continuous E) (hE1 : ∀ a, ‖E a‖ = 1)
    (hχ : Continuous χ) (hχ1 : ∀ b, ‖χ b‖ = 1) (hχadd : ∀ b b', χ (b + b') = χ b * χ b')
    (hV : ∀ g : V → ℂ, Continuous g → Integrable g μV →
        Integrable (fun y => ∫ x, g x * E (x * y) ∂μV) μV →
        ∀ z, ∫ y, (∫ x, g x * E (x * y) ∂μV) * E (y * z) ∂μV = g (-z))
    (L M : ℕ → Set N) (c : ℕ → ℝ)
    (hLm : ∀ n, MeasurableSet (L n)) (hLmono : Monotone L) (hLU : ⋃ n, L n = Set.univ)
    (hLfin : ∀ n, μN (L n) ≠ ⊤)
    (hMc : ∀ n, IsCompact (M n))
    (hMs : ∀ U ∈ 𝓝 (0 : N), ∀ᶠ n in atTop, M n ⊆ U)
    (hLM : ∀ n b, ∫ y in L n, χ (y * b) ∂μN = Set.indicator (M n) (fun _ => (c n : ℂ)) b)
    (hc : ∀ n, c n * (μN (M n)).toReal = 1)
    (f : V × N → ℂ) (hf : Continuous f) (hfi : Integrable f (μV.prod μN))
    (hfh : Integrable (fun y : V × N =>
      ∫ x, f x * (E (x.1 * y.1) * χ (x.2 * y.2)) ∂(μV.prod μN)) (μV.prod μN))
    (z : V × N) :
    ∫ y, (∫ x, f x * (E (x.1 * y.1) * χ (x.2 * y.2)) ∂(μV.prod μN)) *
        (E (y.1 * z.1) * χ (y.2 * z.2)) ∂(μV.prod μN) = f (-z) := by
  obtain ⟨G, hGdef⟩ : ∃ G : V × N → ℂ, G = fun y =>
      (∫ x, f x * (E (x.1 * y.1) * χ (x.2 * y.2)) ∂(μV.prod μN)) *
        (E (y.1 * z.1) * χ (y.2 * z.2)) := ⟨_, rfl⟩
  have hKz : Continuous (fun y : V × N => E (y.1 * z.1) * χ (y.2 * z.2)) :=
    (hE.comp (continuous_fst.mul continuous_const)).mul
      (hχ.comp (continuous_snd.mul continuous_const))
  have hG : Integrable G (μV.prod μN) := by
    rw [hGdef]
    refine hfh.mul_bdd (c := 1) hKz.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [norm_mul, hE1, hχ1, one_mul]
  have hEne : ∀ a, E a ≠ 0 := fun a h => by
    have h1 := hE1 a
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hcpos : ∀ n, 0 < c n := by
    intro n
    have h := hc n
    have h2 : 0 ≤ (μN (M n)).toReal := ENNReal.toReal_nonneg
    by_contra hneg
    push Not at hneg
    have h3 : c n * (μN (M n)).toReal ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg h2
    linarith
  -- Step A: exhaustion
  have hA : Tendsto (fun n => ∫ y in (Set.univ : Set V) ×ˢ L n, G y ∂(μV.prod μN)) atTop
      (𝓝 (∫ y, G y ∂(μV.prod μN))) := by
    have h := tendsto_setIntegral_of_monotone (μ := μV.prod μN) (f := G)
      (s := fun n => (Set.univ : Set V) ×ˢ L n) (fun n => MeasurableSet.univ.prod (hLm n))
      (fun i j hij => Set.prod_mono (le_refl _) (hLmono hij)) hG.integrableOn
    have hU : ⋃ n, (Set.univ : Set V) ×ˢ L n = Set.univ := by
      rw [← Set.prod_iUnion, hLU, Set.univ_prod_univ]
    rwa [hU, setIntegral_univ] at h
  -- Step B: the truncated integral
  have hB : ∀ n, ∫ y in (Set.univ : Set V) ×ˢ L n, G y ∂(μV.prod μN) =
      (c n : ℂ) * ∫ b in (fun b => z.2 + b) ⁻¹' M n, f (-z.1, b) ∂μN := by
    intro n
    obtain ⟨M', hM'⟩ : ∃ M' : Set N, M' = (fun b => z.2 + b) ⁻¹' M n := ⟨_, rfl⟩
    have hM'c : IsCompact M' := by
      rw [hM']
      exact (Homeomorph.addLeft z.2).isCompact_preimage.mpr (hMc n)
    have hM'm : MeasurableSet M' := hM'c.measurableSet
    have : IsFiniteMeasure (μN.restrict (L n)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr (hLfin n)⟩
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : V × N → ℂ, Φ = Set.indicator (Prod.snd ⁻¹' M') f := ⟨_, rfl⟩
    have hΦi : Integrable Φ (μV.prod μN) := by
      rw [hΦ]; exact hfi.indicator (measurable_snd hM'm)
    obtain ⟨Fn, hFn⟩ : ∃ Fn : V → ℂ, Fn = fun x₁ => ∫ x₂ in M', f (x₁, x₂) ∂μN := ⟨_, rfl⟩
    have hFnΦ : ∀ x₁, ∫ x₂, Φ (x₁, x₂) ∂μN = Fn x₁ := by
      intro x₁
      have h1 : (fun x₂ => Φ (x₁, x₂)) = Set.indicator M' (fun x₂ => f (x₁, x₂)) := by
        funext x₂
        rw [hΦ]
        by_cases hx : x₂ ∈ M'
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show (x₁, x₂) ∈ Prod.snd ⁻¹' M' from hx)]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (show (x₁, x₂) ∉ Prod.snd ⁻¹' M' from hx)]
      rw [h1, integral_indicator hM'm, hFn]
    -- the inner integral
    have hinner : ∀ a : V, ∫ b in L n, G (a, b) ∂μN =
        (c n : ℂ) * (∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) * E (a * z.1) := by
      intro a
      obtain ⟨T, hT⟩ : ∃ T : N → V × N → ℂ,
          T = fun b x => f x * E (x.1 * a) * χ (b * (z.2 + x.2)) := ⟨_, rfl⟩
      have h1 : ∀ b, G (a, b) = E (a * z.1) * ∫ x, T b x ∂(μV.prod μN) := by
        intro b
        rw [hGdef, hT]
        simp only
        rw [← integral_mul_const, ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only
        rw [mul_add, hχadd, mul_comm b x.2]
        ring
      have hTint : Integrable (Function.uncurry T) ((μN.restrict (L n)).prod (μV.prod μN)) := by
        have h0 : Integrable (fun p : N × (V × N) => f p.2)
            ((μN.restrict (L n)).prod (μV.prod μN)) := hfi.comp_snd _
        have hcont : Continuous (Function.uncurry T) := by
          rw [hT]
          show Continuous fun p : N × (V × N) =>
            f p.2 * E (p.2.1 * a) * χ (p.1 * (z.2 + p.2.2))
          exact ((hf.comp continuous_snd).mul
            (hE.comp ((continuous_fst.comp continuous_snd).mul continuous_const))).mul
            (hχ.comp (continuous_fst.mul
              (continuous_const.add (continuous_snd.comp continuous_snd))))
        refine h0.mono hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
        rw [hT]
        show ‖f p.2 * E (p.2.1 * a) * χ (p.1 * (z.2 + p.2.2))‖ ≤ ‖f p.2‖
        rw [norm_mul, norm_mul, hE1, hχ1, mul_one, mul_one]
      have h2 : ∀ x : V × N, ∫ b in L n, T b x ∂μN = (c n : ℂ) * (Φ x * E (x.1 * a)) := by
        intro x
        rw [hT]
        simp only
        rw [integral_const_mul, hLM n (z.2 + x.2), hΦ]
        by_cases hx : z.2 + x.2 ∈ M n
        · have hx' : x ∈ Prod.snd ⁻¹' M' := by rw [hM']; exact hx
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx']
          ring
        · have hx' : x ∉ Prod.snd ⁻¹' M' := by rw [hM']; exact hx
          rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx']
          ring
      have hΦE : Integrable (fun x : V × N => Φ x * E (x.1 * a)) (μV.prod μN) := by
        refine hΦi.mul_bdd (c := 1)
          (hE.comp (continuous_fst.mul continuous_const)).aestronglyMeasurable
          (Eventually.of_forall fun x => (hE1 _).le)
      calc ∫ b in L n, G (a, b) ∂μN
          = ∫ b in L n, E (a * z.1) * ∫ x, T b x ∂(μV.prod μN) ∂μN := by
            simp_rw [h1]
        _ = E (a * z.1) * ∫ b in L n, ∫ x, T b x ∂(μV.prod μN) ∂μN := by
            rw [integral_const_mul]
        _ = E (a * z.1) * ∫ x, ∫ b in L n, T b x ∂μN ∂(μV.prod μN) := by
            rw [integral_integral_swap hTint]
        _ = E (a * z.1) * ∫ x, (c n : ℂ) * (Φ x * E (x.1 * a)) ∂(μV.prod μN) := by
            simp_rw [h2]
        _ = E (a * z.1) * ((c n : ℂ) * ∫ x, Φ x * E (x.1 * a) ∂(μV.prod μN)) := by
            rw [integral_const_mul]
        _ = E (a * z.1) * ((c n : ℂ) * ∫ x₁, ∫ x₂, Φ (x₁, x₂) * E (x₁ * a) ∂μN ∂μV) := by
            rw [integral_prod _ hΦE]
        _ = E (a * z.1) * ((c n : ℂ) * ∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) := by
            congr 2
            refine integral_congr_ae (Eventually.of_forall fun x₁ => ?_)
            simp only
            rw [integral_mul_const, hFnΦ]
        _ = (c n : ℂ) * (∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) * E (a * z.1) := by ring
    -- regularity of `Fn`
    have hFc : Continuous Fn := by
      have hcu : Continuous (Function.uncurry fun (x₁ : V) (x₂ : N) => f (x₁, x₂)) := by
        have h1 : (Function.uncurry fun (x₁ : V) (x₂ : N) => f (x₁, x₂)) = f := by
          funext p; rfl
        rw [h1]; exact hf
      rw [hFn]
      exact continuous_parametric_integral_of_continuous hcu hM'c
    have hFi : Integrable Fn μV := by
      have h1 := hΦi.integral_prod_left
      have h2 : (fun x₁ => ∫ x₂, Φ (x₁, x₂) ∂μN) = Fn := funext hFnΦ
      rwa [h2] at h1
    have hHn : Integrable (fun a => ∫ b in L n, G (a, b) ∂μN) μV := by
      have hres : μV.prod (μN.restrict (L n)) =
          (μV.prod μN).restrict ((Set.univ : Set V) ×ˢ L n) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      have hG' : Integrable G (μV.prod (μN.restrict (L n))) := by
        rw [hres]; exact hG.integrableOn
      exact hG'.integral_prod_left
    have hcn : (c n : ℂ) ≠ 0 := by exact_mod_cast (hcpos n).ne'
    have hFh : Integrable (fun a => ∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) μV := by
      have heq : (fun a => ∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) =
          fun a => ((c n : ℂ)⁻¹ * (E (a * z.1))⁻¹) * ∫ b in L n, G (a, b) ∂μN := by
        funext a
        rw [hinner a]
        have := hEne (a * z.1)
        field_simp
      rw [heq]
      refine hHn.bdd_mul (c := |c n|⁻¹) (Continuous.aestronglyMeasurable ?_)
        (Eventually.of_forall fun a => ?_)
      · exact continuous_const.mul
          ((hE.comp (continuous_id.mul continuous_const)).inv₀ fun a => hEne _)
      · rw [norm_mul, norm_inv, norm_inv, hE1, inv_one, mul_one, Complex.norm_real,
          Real.norm_eq_abs]
    have hinv := hV Fn hFc hFi hFh z.1
    rw [setIntegral_prod G hG.integrableOn]
    simp only [Measure.restrict_univ]
    simp_rw [hinner]
    have h3 : (fun a => (c n : ℂ) * (∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) * E (a * z.1)) =
        fun a => (c n : ℂ) * ((∫ x₁, Fn x₁ * E (x₁ * a) ∂μV) * E (a * z.1)) := by
      funext a; ring
    rw [h3, integral_const_mul, hinv, hFn, hM']
  -- Step C: the averages converge
  have hC : Tendsto (fun n => (c n : ℂ) * ∫ b in (fun b => z.2 + b) ⁻¹' M n, f (-z.1, b) ∂μN)
      atTop (𝓝 (f (-z))) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hgc : Continuous (fun b : N => f (-z.1, b)) :=
      hf.comp (continuous_const.prodMk continuous_id)
    have hW : {b : N | ‖f (-z.1, b) - f (-z)‖ < ε / 2} ∈ 𝓝 (-z.2) := by
      have hopen : IsOpen {b : N | ‖f (-z.1, b) - f (-z)‖ < ε / 2} :=
        isOpen_lt (hgc.sub continuous_const).norm continuous_const
      refine hopen.mem_nhds ?_
      show ‖f (-z.1, -z.2) - f (-z)‖ < ε / 2
      have h1 : ((-z.1, -z.2) : V × N) = -z := rfl
      rw [h1, sub_self, norm_zero]
      linarith
    have hU : (fun u : N => -z.2 + u) ⁻¹' {b : N | ‖f (-z.1, b) - f (-z)‖ < ε / 2} ∈
        𝓝 (0 : N) := by
      have hct : ContinuousAt (fun u : N => -z.2 + u) 0 :=
        (continuous_const.add continuous_id).continuousAt
      refine hct.preimage_mem_nhds ?_
      rw [add_zero]
      exact hW
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hMs _ hU)
    refine ⟨n₀, fun n hn => ?_⟩
    have hsub := hn₀ n hn
    obtain ⟨M', hM'⟩ : ∃ M' : Set N, M' = (fun b => z.2 + b) ⁻¹' M n := ⟨_, rfl⟩
    rw [← hM']
    have hM'c : IsCompact M' := by
      rw [hM']
      exact (Homeomorph.addLeft z.2).isCompact_preimage.mpr (hMc n)
    have hμM' : μN M' = μN (M n) := by
      rw [hM']; exact measure_preimage_add μN z.2 (M n)
    have hfin : μN M' < ⊤ := hM'c.measure_lt_top
    have hbound : ∀ b ∈ M', ‖f (-z.1, b) - f (-z)‖ ≤ ε / 2 := by
      intro b hb
      have h1 : z.2 + b ∈ M n := by rw [hM'] at hb; exact hb
      have h2 : ‖f (-z.1, -z.2 + (z.2 + b)) - f (-z)‖ < ε / 2 := hsub h1
      rw [neg_add_cancel_left] at h2
      exact h2.le
    have hint1 : IntegrableOn (fun b : N => f (-z.1, b)) M' μN :=
      hgc.continuousOn.integrableOn_compact hM'c
    have hint2 : IntegrableOn (fun _ : N => f (-z)) M' μN := integrableOn_const hfin.ne
    have hsplit : (c n : ℂ) * ∫ b in M', f (-z.1, b) ∂μN - f (-z) =
        (c n : ℂ) * ∫ b in M', (f (-z.1, b) - f (-z)) ∂μN := by
      rw [integral_sub hint1 hint2, setIntegral_const, mul_sub]
      congr 1
      rw [Measure.real, hμM', Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, hc n,
        Complex.ofReal_one, one_mul]
    rw [dist_eq_norm, hsplit, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (hcpos n)]
    calc c n * ‖∫ b in M', (f (-z.1, b) - f (-z)) ∂μN‖
        ≤ c n * (ε / 2 * μN.real M') :=
          mul_le_mul_of_nonneg_left (norm_setIntegral_le_of_norm_le_const hfin hbound)
            (hcpos n).le
      _ = ε / 2 * (c n * (μN (M n)).toReal) := by rw [Measure.real, hμM']; ring
      _ = ε / 2 := by rw [hc n, mul_one]
      _ < ε := by linarith
  have hlim := tendsto_nhds_unique hA (hC.congr fun n => (hB n).symm)
  rw [hGdef] at hlim
  exact hlim


end Partial


section Assembly0

open InfinitePlace.Completion

instance infinite_haar (w : InfinitePlace F) :
    (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := by
  by_cases h : w.IsReal
  · rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
    exact (ringEquivRealOfIsReal h).symm.toAddEquiv.isAddHaarMeasure_map volume
      (isometryEquivRealOfIsReal h).symm.continuous (isometryEquivRealOfIsReal h).continuous
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp h
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
    have : (2 • (volume : Measure ℂ)).IsAddHaarMeasure := by
      rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0∞) • volume by simp [two_smul]]
      exact Measure.IsAddHaarMeasure.smul (μ := (volume : Measure ℂ)) (by norm_num) (by simp)
    exact (ringEquivComplexOfIsComplex hc).symm.toAddEquiv.isAddHaarMeasure_map _
      (isometryEquivComplexOfIsComplex hc).symm.continuous
      (isometryEquivComplexOfIsComplex hc).continuous

instance sigmaFinite_infinite : SigmaFinite (infiniteAdditiveTamagawa F) := by
  have hhaar : ∀ w : InfinitePlace F,
      (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := infinite_haar
  have hsf : ∀ w : InfinitePlace F,
      SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := fun w => inferInstance
  unfold infiniteAdditiveTamagawa
  exact Measure.pi.sigmaFinite _

end Assembly0


section Arch

open InfinitePlace.Completion
open scoped RealInnerProductSpace FourierTransform


open scoped Classical in
/-- In mixed real and complex coordinates, the archimedean product measure is Lebesgue
measure multiplied by two for each complex place. -/
theorem map_mixedSpace :
    (Measure.pi (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F)).map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      ((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F) •
        (volume : Measure (mixedEmbedding.mixedSpace F)) := by
  let μ := RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F
  have hsc : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion :=
    fun v => secondCountable_infinite v
  have hhaar : ∀ v : InfinitePlace F, (μ v).IsAddHaarMeasure := fun v => infinite_haar v
  have hsf : ∀ v : InfinitePlace F, SigmaFinite (μ v) := fun v => inferInstance
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ (fun v ↦ v.IsReal)
  let reindex : {v : InfinitePlace F // ¬ v.IsReal} ≃ {v : InfinitePlace F // v.IsComplex} :=
    Equiv.subtypeEquivRight fun _ ↦ InfinitePlace.not_isReal_iff_isComplex
  have hr (v : {v : InfinitePlace F // v.IsReal}) :
      MeasurePreserving (ringEquivRealOfIsReal v.2) (μ v) volume := by
    let e := (isometryEquivRealOfIsReal v.2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_pos v.2]
    change (volume.map e.symm).map e = _
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hc (v : {v : InfinitePlace F // ¬ v.IsReal}) :
      MeasurePreserving (ringEquivComplexOfIsComplex (reindex v).2)
        (μ v) ((2 : ℝ≥0) • (volume : Measure ℂ)) := by
    let e := (isometryEquivComplexOfIsComplex (reindex v).2).toHomeomorph.toMeasurableEquiv
    refine ⟨e.measurable, ?_⟩
    change (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F v).map e = _
    rw [RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure, dif_neg v.2]
    change (Measure.map e.symm (2 • (volume : Measure ℂ))).map e = _
    rw [show 2 • (volume : Measure ℂ) = (2 : ℝ≥0) • volume by simp [two_smul]]
    rw [Measure.map_map e.measurable e.symm.measurable, e.self_comp_symm, Measure.map_id]
  have hright := (measurePreserving_piCongrLeft
    (fun _ : {v : InfinitePlace F // v.IsComplex} ↦ (2 : ℝ≥0) • (volume : Measure ℂ)) reindex).comp
      (measurePreserving_pi (ι := {v : InfinitePlace F // ¬ v.IsReal}) _ _ hc)
  let μreal := fun v : {v : InfinitePlace F // v.IsReal} ↦ μ v
  let μcomplex := fun v : {v : InfinitePlace F // ¬ v.IsReal} ↦ μ v
  have hsfr : ∀ v : {v : InfinitePlace F // v.IsReal}, SigmaFinite (μreal v) :=
    fun v => hsf v.val
  have hsfc : ∀ v : {v : InfinitePlace F // ¬ v.IsReal}, SigmaFinite (μcomplex v) :=
    fun v => hsf v.val
  have hpr : SigmaFinite (Measure.pi μreal) := Measure.pi.sigmaFinite μreal
  have hpc : SigmaFinite (Measure.pi μcomplex) := Measure.pi.sigmaFinite μcomplex
  have hleft := measurePreserving_pi μreal (fun _ ↦ volume) hr
  have hmap := (hleft.prod (μc := Measure.pi μcomplex) hright).comp hsplit
  let μr : Measure ({v : InfinitePlace F // v.IsReal} → ℝ) := volume
  let μc : Measure ({v : InfinitePlace F // v.IsComplex} → ℂ) := volume
  let k : ℝ≥0 := 2 ^ InfinitePlace.nrComplexPlaces F
  have hpow : (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
      (2 : ℝ≥0) • (volume : Measure ℂ)) = k • μc := by
    apply Measure.pi_eq
    intro T hT
    rw [Measure.coe_nnreal_smul_apply, show μc = Measure.pi (fun _ ↦ volume) from volume_pi,
      Measure.pi_pi]
    simp only [Measure.coe_nnreal_smul_apply, k, ENNReal.coe_pow, ENNReal.coe_ofNat,
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, InfinitePlace.nrComplexPlaces]
  have hmap' : (Measure.pi μ).map (InfiniteAdeleRing.ringEquiv_mixedSpace F) =
      μr.prod (Measure.pi fun _ : {v : InfinitePlace F // v.IsComplex} ↦
        (2 : ℝ≥0) • (volume : Measure ℂ)) := by
    rw [show μr = Measure.pi (fun _ ↦ volume) from volume_pi]
    exact hmap.map_eq
  rw [hmap', hpow]
  have hk : (k : ℝ≥0∞) = (2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F := by simp [k]
  rw [← hk, ← ENNReal.smul_def]
  change μr.prod (k • μc) = k • μr.prod μc
  refine Measure.prod_eq fun U V _ _ ↦ ?_
  rw [Measure.coe_nnreal_smul_apply, Measure.prod_prod, Measure.coe_nnreal_smul_apply,
    mul_left_comm]



open scoped Classical in
/-- The coordinates of `F_∞` as a homeomorphism onto the mixed space. -/
noncomputable def phiH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toFun x := (fun w => isometryEquivRealOfIsReal w.2 (x w),
    fun w => isometryEquivComplexOfIsComplex w.2 (x w))
  invFun p := (fun w => if h : w.IsReal then (isometryEquivRealOfIsReal h).symm (p.1 ⟨w, h⟩)
    else (isometryEquivComplexOfIsComplex (InfinitePlace.not_isReal_iff_isComplex.1 h)).symm
      (p.2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.1 h⟩) : (w : InfinitePlace F) → w.Completion)
  left_inv x := by
    refine funext fun w => ?_
    by_cases h : w.IsReal
    · simp [h]
    · simp [h]
  right_inv p := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp [w.2]
    · have h : ¬ (w : InfinitePlace F).IsReal := InfinitePlace.not_isReal_iff_isComplex.2 w.2
      simp [h]
  continuous_toFun :=
    (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  continuous_invFun := by
    refine continuous_pi fun w => ?_
    by_cases h : w.IsReal
    · simp only [h, ↓reduceDIte]
      exact (isometryEquivRealOfIsReal h).symm.continuous.comp
        ((continuous_apply _).comp continuous_fst)
    · simp only [h, ↓reduceDIte]
      exact (isometryEquivComplexOfIsComplex _).symm.continuous.comp
        ((continuous_apply _).comp continuous_snd)

lemma sqrt_two_ne_zero : Real.sqrt 2 ≠ 0 := by positivity

/-- Multiplication by `√2` in the complex coordinates. -/
noncomputable def sH : mixedEmbedding.mixedSpace F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.refl _).prodCongr (Homeomorph.smulOfNeZero (Real.sqrt 2) sqrt_two_ne_zero)

/-- Complex conjugation in the complex coordinates. -/
noncomputable def cH : mixedEmbedding.mixedSpace F ≃ₜ mixedEmbedding.mixedSpace F :=
  (Homeomorph.refl _).prodCongr (Homeomorph.piCongrRight fun _ => Complex.conjLIE.toHomeomorph)

/-- The two coordinate maps `P, Q : F_∞ → ℝ^{r₁} × ℂ^{r₂}` (Euclidean). -/
noncomputable def pH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.euclidean.mixedSpace F :=
  (phiH.trans sH).trans (mixedEmbedding.euclidean.toMixed F).symm.toHomeomorph

noncomputable def qH : InfiniteAdeleRing F ≃ₜ mixedEmbedding.euclidean.mixedSpace F :=
  ((phiH.trans cH).trans sH).trans (mixedEmbedding.euclidean.toMixed F).symm.toHomeomorph



open scoped Classical

omit [NumberField F] in
lemma phiH_eq : (phiH : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F := by
  funext x; rfl

lemma mp_phiH : MeasurePreserving phiH (infiniteAdditiveTamagawa F)
    (((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F) •
      (volume : Measure (mixedEmbedding.mixedSpace F))) := by
  refine ⟨phiH.continuous.measurable, ?_⟩
  rw [phiH_eq]
  exact map_mixedSpace

lemma mp_smul_complex : MeasurePreserving
    (fun b : ({w : InfinitePlace F // w.IsComplex} → ℂ) => Real.sqrt 2 • b) volume
    (((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F)⁻¹ • volume) := by
  refine ⟨(continuous_const_smul _).measurable, ?_⟩
  rw [Measure.map_addHaar_smul volume sqrt_two_ne_zero]
  congr 1
  rw [Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [mul_comm, pow_mul, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
    abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]

lemma mp_sH : MeasurePreserving sH (((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F) •
    (volume : Measure (mixedEmbedding.mixedSpace F))) volume := by
  have h1 : MeasurePreserving sH (volume : Measure (mixedEmbedding.mixedSpace F))
      (((2 : ℝ≥0∞) ^ InfinitePlace.nrComplexPlaces F)⁻¹ • volume) := by
    have := (MeasurePreserving.id (volume : Measure ({w : InfinitePlace F // w.IsReal} → ℝ))).prod
      (mp_smul_complex (F := F))
    rw [Measure.prod_smul_right] at this
    exact this
  refine ⟨sH.continuous.measurable, ?_⟩
  rw [Measure.map_smul, h1.map_eq, smul_smul,
    ENNReal.mul_inv_cancel (pow_ne_zero _ two_ne_zero) (by simp), one_smul]

lemma mp_cH : MeasurePreserving cH (volume : Measure (mixedEmbedding.mixedSpace F)) volume :=
  (MeasurePreserving.id _).prod
    (measurePreserving_pi (fun _ => volume) (fun _ => volume)
      fun _ => Complex.conjLIE.measurePreserving)

lemma mp_cH' (c : ℝ≥0∞) : MeasurePreserving cH (c • (volume : Measure (mixedEmbedding.mixedSpace F)))
    (c • volume) :=
  ⟨cH.continuous.measurable, by rw [Measure.map_smul, (mp_cH (F := F)).map_eq]⟩

lemma mp_pH : MeasurePreserving pH (infiniteAdditiveTamagawa F) volume :=
  (mixedEmbedding.euclidean.volumePreserving_toMixed_symm F).comp (mp_sH.comp mp_phiH)

lemma mp_qH : MeasurePreserving qH (infiniteAdditiveTamagawa F) volume :=
  (mixedEmbedding.euclidean.volumePreserving_toMixed_symm F).comp
    (mp_sH.comp ((mp_cH' _).comp mp_phiH))

lemma inner_formula (p q : mixedEmbedding.mixedSpace F) :
    inner ℝ ((mixedEmbedding.euclidean.toMixed F).symm p) ((mixedEmbedding.euclidean.toMixed F).symm q) =
      ∑ w, p.1 w * q.1 w + ∑ w, ((starRingEnd ℂ) (p.2 w) * q.2 w).re := by
  simp [mixedEmbedding.euclidean.toMixed, WithLp.prod_inner_apply, PiLp.inner_apply, mul_comm]



lemma trInf_split (u : InfiniteAdeleRing F) :
    trInf u = ∑ w : {w : InfinitePlace F // w.IsReal},
        (w.1.mult : ℝ) * (extensionEmbedding w.1 (u w.1)).re +
      ∑ w : {w : InfinitePlace F // w.IsComplex},
        (w.1.mult : ℝ) * (extensionEmbedding w.1 (u w.1)).re := by
  unfold trInf
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace F => w.IsReal)]
  congr 1
  exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex)
    _ _ (fun _ => rfl)

lemma trInf_mul_eq_inner (x y : InfiniteAdeleRing F) :
    trInf (x * y) = inner ℝ (pH x) (qH y) := by
  have hP : pH x = (mixedEmbedding.euclidean.toMixed F).symm (sH (phiH x)) := rfl
  have hQ : qH y = (mixedEmbedding.euclidean.toMixed F).symm (sH (cH (phiH y))) := rfl
  rw [hP, hQ, inner_formula, trInf_split]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    have e1 : (sH (phiH x)).1 w = extensionEmbeddingOfIsReal w.2 (x w.1) := rfl
    have e2 : (sH (cH (phiH y))).1 w = extensionEmbeddingOfIsReal w.2 (y w.1) := rfl
    have e3 : (x * y) w.1 = x w.1 * y w.1 := rfl
    rw [e1, e2, e3, map_mul, ← extensionEmbeddingOfIsReal_apply w.2,
      ← extensionEmbeddingOfIsReal_apply w.2, ← Complex.ofReal_mul, Complex.ofReal_re]
    have hm : (w.1.mult : ℝ) = 1 := by simp [InfinitePlace.mult, w.2]
    rw [hm, one_mul]
  · refine Finset.sum_congr rfl fun w _ => ?_
    have e1 : (sH (phiH x)).2 w = (Real.sqrt 2 : ℂ) * extensionEmbedding w.1 (x w.1) := by
      show (Real.sqrt 2) • extensionEmbedding w.1 (x w.1) = _
      rw [Complex.real_smul]
    have e2 : (sH (cH (phiH y))).2 w =
        (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (extensionEmbedding w.1 (y w.1)) := by
      show (Real.sqrt 2) • (Complex.conjLIE (extensionEmbedding w.1 (y w.1))) = _
      rw [Complex.real_smul, Complex.conjLIE_apply]
    have e3 : (x * y) w.1 = x w.1 * y w.1 := rfl
    have hm : (w.1.mult : ℝ) = 2 := by
      simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.2 w.2]
    rw [e1, e2, e3, map_mul, hm]
    have hs : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
    have key : (starRingEnd ℂ) ((Real.sqrt 2 : ℂ) * extensionEmbedding w.1 (x w.1)) *
        ((Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (extensionEmbedding w.1 (y w.1))) =
        2 * (starRingEnd ℂ) (extensionEmbedding w.1 (x w.1) * extensionEmbedding w.1 (y w.1)) := by
      rw [map_mul, map_mul, Complex.conj_ofReal]
      linear_combination ((starRingEnd ℂ) (extensionEmbedding w.1 (x w.1)) *
        (starRingEnd ℂ) (extensionEmbedding w.1 (y w.1))) * hs
    rw [key]
    simp

lemma charInf_mul_eq (x y : InfiniteAdeleRing F) :
    charInf (x * y) = Complex.exp (↑(-2 * Real.pi * inner ℝ (pH x) (qH y)) * Complex.I) := by
  rw [charInf_eq, trInf_mul_eq_inner]
  congr 1
  push_cast
  ring

lemma pH_neg (z : InfiniteAdeleRing F) : pH (-z) = -pH z := by
  have hP : ∀ x, pH x = (mixedEmbedding.euclidean.toMixed F).symm (sH (phiH x)) := fun x => rfl
  have h1 : phiH (-z) = -phiH z := by
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · show ringEquivRealOfIsReal w.2 ((-z) w.1) = -(ringEquivRealOfIsReal w.2 (z w.1))
      exact map_neg (ringEquivRealOfIsReal w.2) (z w.1)
    · show ringEquivComplexOfIsComplex w.2 ((-z) w.1) = -(ringEquivComplexOfIsComplex w.2 (z w.1))
      exact map_neg (ringEquivComplexOfIsComplex w.2) (z w.1)
  have h2 : ∀ p : mixedEmbedding.mixedSpace F, sH (-p) = -sH p := fun p =>
    Prod.ext rfl (smul_neg (Real.sqrt 2) p.2)
  rw [hP, hP, h1, h2, map_neg]

theorem arch_inversion (g : InfiniteAdeleRing F → ℂ) (hg : Continuous g)
    (hg1 : Integrable g (infiniteAdditiveTamagawa F))
    (hg2 : Integrable (fun y => ∫ x, g x * charInf (x * y) ∂(infiniteAdditiveTamagawa F))
      (infiniteAdditiveTamagawa F))
    (z : InfiniteAdeleRing F) :
    ∫ y, (∫ x, g x * charInf (x * y) ∂(infiniteAdditiveTamagawa F)) * charInf (y * z)
      ∂(infiniteAdditiveTamagawa F) = g (-z) := by
  have hP : MeasurePreserving (pH (F := F)).toMeasurableEquiv (infiniteAdditiveTamagawa F) volume :=
    mp_pH
  have hQ : MeasurePreserving (qH (F := F)).toMeasurableEquiv (infiniteAdditiveTamagawa F) volume :=
    mp_qH
  obtain ⟨h, hh⟩ : ∃ h : mixedEmbedding.euclidean.mixedSpace F → ℂ,
      h = fun a => g ((pH (F := F)).symm a) := ⟨_, rfl⟩
  have hcont : Continuous h := by rw [hh]; exact hg.comp (pH (F := F)).symm.continuous
  have hgh : ∀ x, g x = h (pH x) := fun x => by rw [hh]; simp
  have hint : Integrable h := by
    have e : h ∘ (pH (F := F)).toMeasurableEquiv = g := funext fun x => (hgh x).symm
    rw [← (hP.integrable_comp_emb (pH (F := F)).toMeasurableEquiv.measurableEmbedding), e]
    exact hg1
  have hF : ∀ y, ∫ x, g x * charInf (x * y) ∂(infiniteAdditiveTamagawa F) = 𝓕 h (qH y) := by
    intro y
    rw [Real.fourier_eq', ← hP.integral_comp'
      (fun v => Complex.exp (↑(-2 * Real.pi * inner ℝ v (qH y)) * Complex.I) • h v)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show g x * charInf (x * y) = Complex.exp (↑(-2 * Real.pi * inner ℝ (pH x) (qH y)) * Complex.I) •
      h (pH x)
    rw [smul_eq_mul, hgh x, charInf_mul_eq, mul_comm]
  have hFint : Integrable (𝓕 h) := by
    have e : (𝓕 h) ∘ (qH (F := F)).toMeasurableEquiv =
        fun y => ∫ x, g x * charInf (x * y) ∂(infiniteAdditiveTamagawa F) :=
      funext fun y => (hF y).symm
    rw [← (hQ.integrable_comp_emb (qH (F := F)).toMeasurableEquiv.measurableEmbedding), e]
    exact hg2
  calc ∫ y, (∫ x, g x * charInf (x * y) ∂(infiniteAdditiveTamagawa F)) * charInf (y * z)
        ∂(infiniteAdditiveTamagawa F)
      = ∫ y, (fun b => 𝓕 h b * Complex.exp (↑(-2 * Real.pi * inner ℝ (pH z) b) * Complex.I))
          ((qH (F := F)).toMeasurableEquiv y) ∂(infiniteAdditiveTamagawa F) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        show (∫ x, g x * charInf (x * y) ∂(infiniteAdditiveTamagawa F)) * charInf (y * z) =
          𝓕 h (qH y) * Complex.exp (↑(-2 * Real.pi * inner ℝ (pH z) (qH y)) * Complex.I)
        rw [hF y, mul_comm y z, charInf_mul_eq]
    _ = ∫ b, 𝓕 h b * Complex.exp (↑(-2 * Real.pi * inner ℝ (pH z) b) * Complex.I) :=
        hQ.integral_comp'
          (fun b => 𝓕 h b * Complex.exp (↑(-2 * Real.pi * inner ℝ (pH z) b) * Complex.I))
    _ = 𝓕 (𝓕 h) (pH z) := by
        rw [Real.fourier_eq']
        refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
        show 𝓕 h b * Complex.exp (↑(-2 * Real.pi * inner ℝ (pH z) b) * Complex.I) =
          Complex.exp (↑(-2 * Real.pi * inner ℝ b (pH z)) * Complex.I) • 𝓕 h b
        rw [smul_eq_mul, real_inner_comm, mul_comm]
    _ = 𝓕⁻ (𝓕 h) (-(pH z)) := by rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    _ = h (-(pH z)) := by rw [hcont.fourierInv_fourier_eq hint hFint]
    _ = g (-z) := by rw [← pH_neg, hh]; simp

end Arch

section GChar

/-- An adele from its infinite and finite components. -/
noncomputable def mkA (a : InfiniteAdeleRing F) (b : FiniteAdeleRing (𝓞 F) F) : AdeleRing (𝓞 F) F := (a, b)

/-- Every adele is an integral adele plus an element of `F`. -/
lemma exists_decomp (x : AdeleRing (𝓞 F) F) :
    ∃ ξ : F, IsIntegralAdele (x - algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  obtain ⟨k, hk⟩ :=
    NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F x.2
  refine ⟨-k, fun v => ?_⟩
  have e : x - algebraMap F (AdeleRing (𝓞 F) F) (-k) =
      x + algebraMap F (AdeleRing (𝓞 F) F) k := by
    rw [map_neg, sub_neg_eq_add]
  rw [e]
  have h := hk v
  have e2 : (x + algebraMap F (AdeleRing (𝓞 F) F) k).2 v =
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) k + x.2) v := by
    rw [add_comm]; rfl
  rw [e2]
  exact h

/-- Well-definedness of the global standard character. -/
lemma stdChar_eq (x y : AdeleRing (𝓞 F) F) (ξ : F) (hy : IsIntegralAdele y)
    (hx : x = y + algebraMap F (AdeleRing (𝓞 F) F) ξ) :
    stdAdelicCharacter x = Complex.exp (-(2 * Real.pi * Complex.I) * (trInf y.1 : ℂ)) := by
  have hex : ∃ y : AdeleRing (𝓞 F) F, IsIntegralAdele y ∧
      ∃ ξ : F, x = y + algebraMap F (AdeleRing (𝓞 F) F) ξ := ⟨y, hy, ξ, hx⟩
  unfold stdAdelicCharacter
  rw [dif_pos hex]
  obtain ⟨h1, ξ', h2⟩ := hex.choose_spec
  set y' := hex.choose with hy'
  have hsum : (∑ w : InfinitePlace F, (w.mult : ℂ) *
      ((InfinitePlace.Completion.extensionEmbedding w (y'.1 w)).re : ℂ)) =
      ((trInf y'.1 : ℝ) : ℂ) := by
    simp [trInf]
  rw [hsum]
  have hyy : y' = y - algebraMap F (AdeleRing (𝓞 F) F) (ξ' - ξ) := by
    have h3 : y + algebraMap F (AdeleRing (𝓞 F) F) ξ =
        y' + algebraMap F (AdeleRing (𝓞 F) F) ξ' := hx.symm.trans h2
    rw [map_sub]
    linear_combination h3.symm
  have hδ : ξ' - ξ ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F _ fun v => ?_
    have e3 : y.2 v - y'.2 v ∈ v.adicCompletionIntegers F := sub_mem (hy v) (h1 v)
    have e4 : y.2 v - y'.2 v = algebraMap F (v.adicCompletion F) (ξ' - ξ) := by
      rw [hyy]
      show y.2 v - (y.2 v - ((ξ' - ξ : F) : v.adicCompletion F)) = _
      rw [sub_sub_cancel]
      rfl
    rw [e4, HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap] at e3
    exact e3
  obtain ⟨a, ha⟩ := hδ
  obtain ⟨n, hn⟩ := trace_int a
  have e5 : y'.1 = y.1 - algebraMap F (InfiniteAdeleRing F) (ξ' - ξ) := by
    rw [hyy]; rfl
  have ha' : (algebraMap (𝓞 F) F) a = ξ' - ξ := ha
  rw [e5, trInf_sub, trInf_algebraMap, ← ha', hn, Complex.exp_eq_exp_iff_exists_int]
  refine ⟨n, ?_⟩
  push_cast
  ring

lemma gchar_add (x y : AdeleRing (𝓞 F) F) :
    stdAdelicCharacter (x + y) = stdAdelicCharacter x * stdAdelicCharacter y := by
  obtain ⟨ξ, hξ⟩ := exists_decomp x
  obtain ⟨η, hη⟩ := exists_decomp y
  have e0 : (x + y) - algebraMap F (AdeleRing (𝓞 F) F) (ξ + η) =
      (x - algebraMap F (AdeleRing (𝓞 F) F) ξ) + (y - algebraMap F (AdeleRing (𝓞 F) F) η) := by
    rw [map_add]; abel
  have hxy : IsIntegralAdele ((x + y) - algebraMap F (AdeleRing (𝓞 F) F) (ξ + η)) := by
    intro v
    rw [e0]
    exact add_mem (hξ v) (hη v)
  rw [stdChar_eq (x + y) _ (ξ + η) hxy (sub_add_cancel _ _).symm,
    stdChar_eq x _ ξ hξ (sub_add_cancel _ _).symm,
    stdChar_eq y _ η hη (sub_add_cancel _ _).symm, ← Complex.exp_add, e0]
  congr 1
  have e : ((x - algebraMap F (AdeleRing (𝓞 F) F) ξ) +
      (y - algebraMap F (AdeleRing (𝓞 F) F) η)).1 =
      (x - algebraMap F (AdeleRing (𝓞 F) F) ξ).1 + (y - algebraMap F (AdeleRing (𝓞 F) F) η).1 :=
    rfl
  rw [e, trInf_add]
  push_cast
  ring

lemma gchar_norm (x : AdeleRing (𝓞 F) F) : ‖stdAdelicCharacter x‖ = 1 := by
  obtain ⟨ξ, hξ⟩ := exists_decomp x
  rw [stdChar_eq x _ ξ hξ (sub_add_cancel _ _).symm]
  exact norm_exp_trInf _

lemma gchar_continuous : Continuous (stdAdelicCharacter : AdeleRing (𝓞 F) F → ℂ) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨ξ, hξ⟩ := exists_decomp x₀
  have hU : IsOpen {x : AdeleRing (𝓞 F) F |
      IsIntegralAdele (x - algebraMap F (AdeleRing (𝓞 F) F) ξ)} := by
    have h : {x : AdeleRing (𝓞 F) F |
        IsIntegralAdele (x - algebraMap F (AdeleRing (𝓞 F) F) ξ)} =
        (fun x : AdeleRing (𝓞 F) F => (x - algebraMap F (AdeleRing (𝓞 F) F) ξ).2) ⁻¹'
          NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F := rfl
    rw [h]
    exact (NumberField.AdelicBox.isOpen_integralFiniteAdeles F).preimage
      (continuous_snd.comp (continuous_id.sub continuous_const))
  have hev : stdAdelicCharacter =ᶠ[nhds x₀] fun x =>
      Complex.exp (-(2 * Real.pi * Complex.I) *
        (trInf ((x - algebraMap F (AdeleRing (𝓞 F) F) ξ).1) : ℂ)) := by
    filter_upwards [hU.mem_nhds hξ] with x hx
    exact stdChar_eq x _ ξ hx (sub_add_cancel _ _).symm
  refine ContinuousAt.congr ?_ hev.symm
  refine Continuous.continuousAt ?_
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp
    (continuous_trInf.comp (continuous_fst.comp (continuous_id.sub continuous_const)))

lemma gchar_algebraMap (ξ : F) :
    stdAdelicCharacter (algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1 := by
  rw [stdChar_eq _ 0 ξ (fun v => zero_mem _) (zero_add _).symm]
  have h : (0 : AdeleRing (𝓞 F) F).1 = 0 := rfl
  rw [h, trInf_zero]
  simp

lemma gchar_nontriv : ∃ x : AdeleRing (𝓞 F) F, stdAdelicCharacter x ≠ 1 := by
  set d : ℕ := Module.finrank ℚ F with hd
  have hdpos : 0 < d := Module.finrank_pos
  set q : ℚ := 1 / (2 * d) with hq
  set t : InfiniteAdeleRing F := algebraMap F (InfiniteAdeleRing F) (algebraMap ℚ F q)
  refine ⟨(mkA t 0), ?_⟩
  rw [stdChar_eq _ (mkA t 0) 0 (fun v => zero_mem _)
    (by rw [map_zero, add_zero])]
  show Complex.exp (-(2 * Real.pi * Complex.I) * (trInf t : ℂ)) ≠ 1
  rw [trInf_algebraMap, Algebra.trace_algebraMap]
  have hq2 : (((d • q : ℚ) : ℝ) : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    have : (d • q : ℚ) = 1 / 2 := by
      rw [hq, nsmul_eq_mul]
      have : (d : ℚ) ≠ 0 := by exact_mod_cast hdpos.ne'
      field_simp
    rw [this]; push_cast; ring
  rw [hq2]
  have e : -(2 * Real.pi * Complex.I) * ((1 / 2 : ℝ) : ℂ) = -(Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- The finite component of the global standard character. -/
noncomputable def chiF (b : FiniteAdeleRing (𝓞 F) F) : ℂ :=
  stdAdelicCharacter (mkA 0 b)

lemma gchar_fst (a : InfiniteAdeleRing F) :
    stdAdelicCharacter (mkA a 0) = charInf a := by
  rw [stdChar_eq _ (mkA a 0) 0 (fun v => zero_mem _)
    (by rw [map_zero, add_zero]), charInf_eq]
  rfl

lemma gchar_split (x : AdeleRing (𝓞 F) F) :
    stdAdelicCharacter x = charInf x.1 * chiF x.2 := by
  have e : x = mkA x.1 0 + mkA 0 x.2 :=
    Prod.ext (add_zero _).symm (zero_add _).symm
  conv_lhs => rw [e]
  rw [gchar_add, gchar_fst]
  rfl

lemma chiF_add (b b' : FiniteAdeleRing (𝓞 F) F) : chiF (b + b') = chiF b * chiF b' := by
  unfold chiF
  rw [← gchar_add]
  congr 1
  exact Prod.ext (add_zero _).symm rfl

lemma chiF_norm (b : FiniteAdeleRing (𝓞 F) F) : ‖chiF b‖ = 1 := gchar_norm _

lemma chiF_continuous : Continuous (chiF : FiniteAdeleRing (𝓞 F) F → ℂ) :=
  gchar_continuous.comp (continuous_const.prodMk continuous_id)

/-- On adeles integral outside `S`, the finite global character is the `S`-local one. -/
lemma chiF_eq_charFin (S : Finset (HeightOneSpectrum (𝓞 F))) (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ v, v ∉ S → b v ∈ v.adicCompletionIntegers F) :
    chiF b = charFin S (fun v : S => b v) := by
  obtain ⟨ξ, hξ⟩ := exists_decomp (mkA 0 b)
  have hS : ξ ∈ SIntegers (F := F) S := by
    intro v hv
    have h1 : b v - algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F := hξ v
    have h2 : algebraMap F (v.adicCompletion F) ξ ∈ v.adicCompletionIntegers F := by
      have : algebraMap F (v.adicCompletion F) ξ =
          b v - (b v - algebraMap F (v.adicCompletion F) ξ) := by ring
      rw [this]
      exact sub_mem (hb v hv) h1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap] at h2
    exact h2
  have hA : IsApprox S ((0, fun v : S => b v) : SAdeleRing F S) ξ := ⟨hS, fun v => hξ v⟩
  unfold chiF charFin
  rw [stdChar_eq _ _ ξ hξ (sub_add_cancel _ _).symm, sStdCharacter_eq S _ ξ hA]
  rfl

end GChar

section GProd

open scoped RestrictedProduct Topology

instance gSecondCountable_finAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  have h0 := NumberField.AdeleRing.secondCountableTopology F
  have h : SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) := h0
  exact (isEmbedding_prodMkRight (0 : InfiniteAdeleRing F)).secondCountableTopology

lemma gLocallyCompact_finite (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v

lemma gCompact_integers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  RiemannMasullo.compactSpace_adicCompletionIntegers v

lemma gFact_isOpen : Fact (∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

attribute [local instance] gLocallyCompact_finite gCompact_integers gFact_isOpen

instance gLocallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  change LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
  infer_instance

instance gT2_finiteAdele : T2Space (FiniteAdeleRing (𝓞 F) F) := by
  change T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
  infer_instance

noncomputable instance gFinAdeleMeasurableSpace : MeasurableSpace (FiniteAdeleRing (𝓞 F) F) := borel _

instance gFinAdeleBorel : BorelSpace (FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩

instance gInfHaar : (infiniteAdditiveTamagawa F).IsAddHaarMeasure := by
  have h1 : ∀ w : InfinitePlace F,
      (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w).IsAddHaarMeasure := infinite_haar
  have h2 : ∀ w : InfinitePlace F,
      SigmaFinite (RiemannMasullo.infiniteLocalAdditiveTamagawaMeasure F w) := fun w => inferInstance
  unfold infiniteAdditiveTamagawa
  exact Measure.pi.isAddHaarMeasure _

/-- The identification `𝔸_F = F_∞ × 𝔸_f` as a measurable equivalence. -/
def eAd : (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) ≃ᵐ AdeleRing (𝓞 F) F where
  toEquiv := Equiv.refl _
  measurable_toFun := Continuous.measurable (by exact continuous_id)
  measurable_invFun := Continuous.measurable (by exact continuous_id)

lemma eAd_apply (p : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :
    (eAd (F := F)) p = mkA p.1 p.2 := rfl

/-- The Tamagawa measure is a product `ν_∞ ⊗ ν_f`. -/
theorem exists_prod_decomp : ∃ νf : Measure (FiniteAdeleRing (𝓞 F) F), νf.IsAddHaarMeasure ∧
    MeasurePreserving (eAd (F := F)) ((infiniteAdditiveTamagawa F).prod νf)
      (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)) := by
  have hν := (tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain F).1
  let φ : AdeleRing (𝓞 F) F ≃+ (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    AddEquiv.refl _
  have hφc : Continuous φ := continuous_id
  have hφsc : Continuous φ.symm := continuous_id
  let ν' : Measure (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) :=
    Measure.map φ (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F))
  have hν' : ν'.IsAddHaarMeasure := φ.isAddHaarMeasure_map _ hφc hφsc
  let μf : Measure (FiniteAdeleRing (𝓞 F) F) := Measure.addHaar
  let P := (infiniteAdditiveTamagawa F).prod μf
  have hP : P.IsAddHaarMeasure := inferInstance
  have h := Measure.isAddLeftInvariant_eq_smul ν' P
  set c := Measure.addHaarScalarFactor ν' P with hcdef
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν' P
  refine ⟨(c : ℝ≥0∞) • μf, ?_, ⟨(eAd (F := F)).measurable, ?_⟩⟩
  · exact Measure.IsAddHaarMeasure.smul _ (by exact_mod_cast hc.ne') ENNReal.coe_ne_top
  · rw [Measure.prod_smul_right]
    have h2 : (c : ℝ≥0∞) • P = ν' := by rw [h]; rfl
    rw [h2]
    have hφm : Measurable φ := hφc.measurable
    rw [Measure.map_map (eAd (F := F)).measurable hφm]
    have h3 : (eAd (F := F)) ∘ φ = id := rfl
    rw [h3, Measure.map_id]

end GProd

section GSBox

open scoped RestrictedProduct Topology

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- Restriction of a finite adele to the places of `S`. -/
def resS (b : FiniteAdeleRing (𝓞 F) F) : FinPart S := fun v => b (v : HeightOneSpectrum (𝓞 F))

lemma continuous_resS : Continuous (resS (F := F) S) :=
  continuous_pi fun v => RestrictedProduct.continuous_eval _

/-- Finite adeles integral outside `S`. -/
def intOutF : Set (FiniteAdeleRing (𝓞 F) F) :=
  {y | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

lemma isOpen_intOutF : IsOpen (intOutF (F := F) S) :=
  RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ S)

/-- Finite adeles integral outside `S` whose `S`-components lie in `B`. -/
def gS (B : Set (FinPart S)) : Set (FiniteAdeleRing (𝓞 F) F) :=
  intOutF S ∩ resS S ⁻¹' B

lemma measurableSet_gS {B : Set (FinPart S)} (hB : MeasurableSet B) :
    MeasurableSet (gS (F := F) S B) :=
  (isOpen_intOutF S).measurableSet.inter ((continuous_resS S).measurable hB)

/-- The constant `|d_F|^{-1/2} ∏_{v ∈ S} N(𝔡_v)^{1/2}`. -/
noncomputable def CS : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
    ∏ v ∈ S, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))

theorem nuf_gS (νf : Measure (FiniteAdeleRing (𝓞 F) F)) [νf.IsAddHaarMeasure]
    (hνf : MeasurePreserving (eAd (F := F)) ((infiniteAdditiveTamagawa F).prod νf)
      (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)))
    (B : Set (FinPart S)) (hB : MeasurableSet B) :
    νf (gS S B) = muFin S B * CS (F := F) S := by
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : InfiniteAdeleRing F)
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have h := tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa F S (K ×ˢ B) (hKm.prod hB)
  have hpre : (eAd (F := F)) ⁻¹' {x : AdeleRing (𝓞 F) F |
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → x.2 v ∈ v.adicCompletionIntegers F) ∧
      ((x.1, fun v : S => x.2 (v : HeightOneSpectrum (𝓞 F))) : SAdeleRing F S) ∈ K ×ˢ B} =
      K ×ˢ gS S B := by
    ext p
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h2, h1, h3⟩ => ⟨h1, h2, h3⟩⟩
  rw [← hνf.measure_preimage_equiv, hpre, Measure.prod_prod] at h
  have h2 : sAdditiveTamagawa F S (K ×ˢ B) = infiniteAdditiveTamagawa F K * muFin S B :=
    Measure.prod_prod _ _
  unfold CS
  rw [h2, mul_assoc] at h
  have hpos : 0 < infiniteAdditiveTamagawa F K := Measure.measure_pos_of_mem_nhds _ hK0
  have hfin : infiniteAdditiveTamagawa F K < ⊤ := hKc.measure_lt_top
  exact (ENNReal.mul_right_inj hpos.ne' hfin.ne).1 h

end GSBox

section GLat1

open scoped RestrictedProduct Topology
open Filter

/-- `Lat a = a⁻¹ 𝒪̂ ⊆ 𝔸_f`. -/
def Lat (a : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {y | algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a * y ∈
    NumberField.AdelicBox.integralFiniteAdeles (𝓞 F) F}

lemma mem_Lat (a : 𝓞 F) (y : FiniteAdeleRing (𝓞 F) F) :
    y ∈ Lat a ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * y v ∈
        v.adicCompletionIntegers F := Iff.rfl

lemma Lat_add {a : 𝓞 F} {y y' : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ Lat a) (hy' : y' ∈ Lat a) :
    y + y' ∈ Lat a := by
  rw [mem_Lat] at *
  intro v
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * (y + y') v =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * y v +
        algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * y' v := mul_add _ _ _
  rw [e]
  exact add_mem (hy v) (hy' v)

lemma Lat_neg {a : 𝓞 F} {y : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ Lat a) : -y ∈ Lat a := by
  rw [mem_Lat] at *
  intro v
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * (-y) v =
      -(algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * y v) := mul_neg _ _
  rw [e]
  exact neg_mem (hy v)

lemma isOpen_Lat (a : 𝓞 F) : IsOpen (Lat a) :=
  (NumberField.AdelicBox.isOpen_integralFiniteAdeles F).preimage
    (continuous_const.mul continuous_id)

lemma isClosed_Lat (a : 𝓞 F) : IsClosed (Lat a) :=
  (NumberField.AdelicBox.isClosed_integralFiniteAdeles F).preimage
    (continuous_const.mul continuous_id)

lemma algebraMap_ne_zero {a : 𝓞 F} (ha : a ≠ 0) : algebraMap (𝓞 F) F a ≠ 0 := by
  rw [Ne, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 F) F)]
  exact ha

lemma isCompact_Lat {a : 𝓞 F} (ha : a ≠ 0) : IsCompact (Lat a) := by
  have hc : Continuous fun y : FiniteAdeleRing (𝓞 F) F =>
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)⁻¹ * y :=
    continuous_const.mul continuous_id
  have hK := (NumberField.AdelicBox.isCompact_integralFiniteAdeles F).image hc
  refine hK.of_isClosed_subset (isClosed_Lat a) fun y hy => ?_
  refine ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a * y, hy, ?_⟩
  have e : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a) :=
    IsScalarTower.algebraMap_apply _ _ _ _
  show algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F a)⁻¹ *
    (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a * y) = y
  rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (algebraMap_ne_zero ha), map_one, one_mul]

lemma Lat_mono {a a' : 𝓞 F} (h : a ∣ a') : Lat a ⊆ Lat a' := by
  obtain ⟨c, rfl⟩ := h
  intro y hy
  rw [mem_Lat] at *
  intro v
  have e : algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (a * c)) * y v =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F c) *
        (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a) * y v) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem (NumberField.AdelicBox.algebraMap_mem_adicCompletionIntegers (𝓞 F) F v c) (hy v)

/-- The exhausting sequence `a_n = (n!)^n`. -/
noncomputable def aSeq (n : ℕ) : 𝓞 F := ((n.factorial : ℕ) : 𝓞 F) ^ n

lemma aSeq_ne_zero (n : ℕ) : aSeq (F := F) n ≠ 0 := by
  unfold aSeq
  refine pow_ne_zero _ ?_
  exact_mod_cast (Nat.factorial_pos n).ne'

lemma aSeq_dvd {n m : ℕ} (h : n ≤ m) : aSeq (F := F) n ∣ aSeq m := by
  unfold aSeq
  have h1 : ((n.factorial : ℕ) : 𝓞 F) ∣ ((m.factorial : ℕ) : 𝓞 F) :=
    Nat.cast_dvd_cast (Nat.factorial_dvd_factorial h)
  exact (pow_dvd_pow_of_dvd h1 n).trans (pow_dvd_pow _ h)

lemma dvd_aSeq {s : 𝓞 F} (hs : s ≠ 0) : ∃ N : ℕ, ∀ n, N ≤ n → s ∣ aSeq (F := F) n := by
  set N : ℕ := Ideal.absNorm (Ideal.span {s}) with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hs
  have hsN : s ∣ (N : 𝓞 F) := Ideal.mem_span_singleton.1 (Ideal.absNorm_mem _)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (N : 𝓞 F) ∣ ((n.factorial : ℕ) : 𝓞 F) :=
    Nat.cast_dvd_cast (Nat.dvd_factorial (Nat.pos_of_ne_zero hN0) hn)
  have h2 : ((n.factorial : ℕ) : 𝓞 F) ∣ aSeq n := by
    unfold aSeq
    exact dvd_pow_self _ (by omega)
  exact hsN.trans (h1.trans h2)

lemma iUnion_Lat_aSeq : ⋃ n, Lat (aSeq (F := F) n) = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨s, hs, hsy⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles (𝓞 F) F y
  obtain ⟨N, hN⟩ := dvd_aSeq hs
  exact Set.mem_iUnion.2 ⟨N, Lat_mono (hN N le_rfl) hsy⟩

/-- The exponent `ℓ_v(a) = log v(a)`. -/
noncomputable def ell (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ℤ := WithZero.log (v.intValuation a)

lemma intValuation_eq_exp_ell {a : 𝓞 F} (ha : a ≠ 0) (v : HeightOneSpectrum (𝓞 F)) :
    v.intValuation a = WithZero.exp (ell a v) :=
  (WithZero.exp_log (v.intValuation_ne_zero a ha)).symm

lemma valued_coe_eq (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) = v.intValuation a := by
  rw [valued_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]

lemma mem_Lat_iff {a : 𝓞 F} (ha : a ≠ 0) (y : FiniteAdeleRing (𝓞 F) F) :
    y ∈ Lat a ↔ ∀ v, Valued.v (y v) ≤ WithZero.exp (-(ell a v)) := by
  rw [mem_Lat]
  refine forall_congr' fun v => ?_
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_coe_eq,
    intValuation_eq_exp_ell ha, ← WithZero.exp_zero, exp_mul_le_iff, zero_sub]

/-- The finite set of places dividing `a`. -/
noncomputable def supp (a : 𝓞 F) (ha : a ≠ 0) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)).toFinset

lemma ell_eq_zero {a : 𝓞 F} (ha : a ≠ 0) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ supp a ha) :
    ell a v = 0 := by
  have hwd : ¬ v.asIdeal ∣ Ideal.span {a} := fun hdiv =>
    hv ((Ideal.finite_factors (I := Ideal.span {a}) (by simpa using ha)).mem_toFinset.2 hdiv)
  have h1 : v.intValuation a = 1 := by
    rw [Ideal.dvd_span_singleton, ← HeightOneSpectrum.intValuation_lt_one_iff_mem,
      not_lt] at hwd
    exact le_antisymm (v.intValuation_le_one a) hwd
  unfold ell
  rw [h1]
  rfl

lemma ell_nonpos (a : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) : ell a v ≤ 0 := by
  unfold ell
  by_cases ha : a = 0
  · subst ha; simp
  · have h := v.intValuation_le_one a
    rw [intValuation_eq_exp_ell ha v, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    exact h

lemma Lat_eq_gS {a : 𝓞 F} (ha : a ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS : supp a ha ⊆ S) :
    Lat a = gS S (box S fun v => ell a (v : HeightOneSpectrum (𝓞 F))) := by
  ext y
  rw [mem_Lat_iff ha]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v => h v⟩
    have h1 := h v
    rw [ell_eq_zero ha (fun h' => hv (hS h')), neg_zero, WithZero.exp_zero] at h1
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · exact h2 ⟨v, hv⟩
    · have h3 := h1 v hv
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h3
      rw [ell_eq_zero ha (fun h' => hv (hS h')), neg_zero, WithZero.exp_zero]
      exact h3

end GLat1

section GLat2

open scoped RestrictedProduct Topology
open Filter

/-- The annihilator of a set of finite adeles for the pairing `chiF (y b)`. -/
def Ann (L : Set (FiniteAdeleRing (𝓞 F) F)) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {b | ∀ y ∈ L, chiF (y * b) = 1}

lemma Ann_anti {L L' : Set (FiniteAdeleRing (𝓞 F) F)} (h : L ⊆ L') : Ann L' ⊆ Ann L :=
  fun _ hb y hy => hb y (h hy)

lemma isClosed_Ann (L : Set (FiniteAdeleRing (𝓞 F) F)) : IsClosed (Ann L) := by
  have : Ann L = ⋂ y ∈ L, (fun b => chiF (y * b)) ⁻¹' {1} := by
    ext b; simp [Ann]
  rw [this]
  exact isClosed_biInter fun y _ => isClosed_singleton.preimage
    (chiF_continuous.comp (continuous_const.mul continuous_id))

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

open Classical in
/-- Extension by zero of an `S`-adele to a finite adele. -/
noncomputable def glueF (u : FinPart S) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.mk (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (𝓕 := Filter.cofinite)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      if h : v ∈ S then u ⟨v, h⟩ else (0 : v.adicCompletion F)) (by
    refine Filter.eventually_cofinite.2 (S.finite_toSet.subset fun v hv => ?_)
    by_contra h
    apply hv
    simp only [dif_neg (show v ∉ S from h)]
    exact zero_mem _)

lemma glueF_apply_mem (u : FinPart S) (v : S) : glueF S u v = u v := by
  classical
  show (if h : (v : HeightOneSpectrum (𝓞 F)) ∈ S then u ⟨v, h⟩
    else (0 : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) = u v
  rw [dif_pos v.2]

lemma glueF_apply_not_mem (u : FinPart S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    glueF S u v = 0 := by
  classical
  show (if h : v ∈ S then u ⟨v, h⟩ else (0 : v.adicCompletion F)) = 0
  rw [dif_neg hv]

lemma resS_glueF (u : FinPart S) : resS S (glueF S u) = u :=
  funext fun v => glueF_apply_mem S u v

lemma glueF_mem_intOutF (u : FinPart S) : glueF S u ∈ intOutF S := fun v hv => by
  rw [glueF_apply_not_mem S u hv]; exact zero_mem _

lemma mul_mem_intOutF {y b : FiniteAdeleRing (𝓞 F) F} (hy : y ∈ intOutF S)
    (hb : b ∈ intOutF S) : y * b ∈ intOutF S :=
  fun v hv => mul_mem (hy v hv) (hb v hv)

lemma resS_mul (y b : FiniteAdeleRing (𝓞 F) F) : resS S (y * b) = resS S y * resS S b := rfl

lemma chiF_eq_charFin' (b : FiniteAdeleRing (𝓞 F) F) (hb : b ∈ intOutF S) :
    chiF b = charFin S (resS S b) := chiF_eq_charFin S b hb

theorem ann_gS (k : S → ℤ) (b : FiniteAdeleRing (𝓞 F) F) (hb : b ∈ intOutF S) :
    b ∈ Ann (gS S (box S k)) ↔ ∀ v : S, Valued.v (b v) ≤ WithZero.exp (k v +
        (multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)) := by
  refine Iff.trans ?_ (box_annihilator S k (resS S b))
  constructor
  · intro h y hy
    have h1 := h (glueF S y) ⟨glueF_mem_intOutF S y, by
      rw [Set.mem_preimage, resS_glueF]; exact hy⟩
    rw [chiF_eq_charFin' S _ (mul_mem_intOutF S (glueF_mem_intOutF S y) hb), resS_mul,
      resS_glueF] at h1
    exact h1
  · intro h y hy
    rw [chiF_eq_charFin' S _ (mul_mem_intOutF S hy.1 hb), resS_mul]
    exact h (resS S y) hy.2

end GLat2

section GLat3

open scoped RestrictedProduct Topology
open Filter

lemma finite_nonint (b : FiniteAdeleRing (𝓞 F) F) :
    {v : HeightOneSpectrum (𝓞 F) | b v ∉ v.adicCompletionIntegers F}.Finite :=
  Filter.eventually_cofinite.1 b.2

/-- The exponent `d_v` of `𝔭_v` in the different. -/
noncomputable def dE (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) : ℤ)

/-- The places dividing the different. -/
noncomputable def S0 : Finset (HeightOneSpectrum (𝓞 F)) :=
  (Ideal.finite_factors (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot).toFinset

lemma dE_eq_zero {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S0 (F := F)) : dE v = 0 := by
  have hwd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h => hv
    ((Ideal.finite_factors (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot).mem_toFinset.2 h)
  unfold dE
  rw [multiplicity_eq_zero.2 hwd]
  rfl

lemma dE_nonneg (v : HeightOneSpectrum (𝓞 F)) : 0 ≤ dE v := Nat.cast_nonneg _

theorem ann_Lat {a : 𝓞 F} (ha : a ≠ 0) (b : FiniteAdeleRing (𝓞 F) F) :
    b ∈ Ann (Lat a) ↔ ∀ v, Valued.v (b v) ≤ WithZero.exp (ell a v + dE v) := by
  classical
  constructor
  · intro h v
    set T := (finite_nonint b).toFinset
    set S := supp a ha ∪ T
    have hbS : b ∈ intOutF S := fun w hw => by
      by_contra h'
      exact hw (Finset.mem_union_right _ ((finite_nonint b).mem_toFinset.2 h'))
    rw [Lat_eq_gS ha S Finset.subset_union_left, ann_gS S _ b hbS] at h
    by_cases hv : v ∈ S
    · exact h ⟨v, hv⟩
    · have h1 := hbS v hv
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
      refine h1.trans ?_
      rw [ell_eq_zero ha (fun h' => hv (Finset.mem_union_left _ h')), zero_add,
        ← WithZero.exp_zero, WithZero.exp_le_exp]
      exact dE_nonneg v
  · intro h
    set S := supp a ha ∪ S0
    have hbS : b ∈ intOutF S := fun w hw => by
      have h1 := h w
      rw [ell_eq_zero ha (fun h' => hw (Finset.mem_union_left _ h')),
        dE_eq_zero (fun h' => hw (Finset.mem_union_right _ h')), zero_add,
        WithZero.exp_zero] at h1
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1
    rw [Lat_eq_gS ha S Finset.subset_union_left, ann_gS S _ b hbS]
    intro v
    exact h v

lemma Ann_eq_gS {a : 𝓞 F} (ha : a ≠ 0) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hS1 : supp a ha ⊆ S) (hS2 : S0 ⊆ S) :
    Ann (Lat a) = gS S (box S fun v =>
      -(ell a (v : HeightOneSpectrum (𝓞 F)) + dE (v : HeightOneSpectrum (𝓞 F)))) := by
  ext b
  rw [ann_Lat ha]
  constructor
  · intro h
    refine ⟨fun v hv => ?_, fun v => by rw [neg_neg]; exact h v⟩
    have h1 := h v
    rw [ell_eq_zero ha (fun h' => hv (hS1 h')),
      dE_eq_zero (fun h' => hv (hS2 h')), zero_add,
      WithZero.exp_zero] at h1
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 h1
  · rintro ⟨h1, h2⟩ v
    by_cases hv : v ∈ S
    · have := h2 ⟨v, hv⟩
      rw [neg_neg] at this
      exact this
    · have h3 := h1 v hv
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h3
      rw [ell_eq_zero ha (fun h' => hv (hS1 h')),
        dE_eq_zero (fun h' => hv (hS2 h')), zero_add,
        WithZero.exp_zero]
      exact h3

/-- `D = N(𝔡) ∈ 𝔡`. -/
noncomputable def Dd : 𝓞 F := (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : 𝓞 F)

lemma Dd_ne_zero : Dd (F := F) ≠ 0 := by
  unfold Dd
  have h : Ideal.absNorm (differentIdeal ℤ (𝓞 F)) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact differentIdeal_ne_bot
  exact_mod_cast h

lemma Ann_subset_Lat_Dd {a : 𝓞 F} (ha : a ≠ 0) : Ann (Lat a) ⊆ Lat (Dd (F := F)) := by
  intro b hb
  rw [ann_Lat ha] at hb
  rw [mem_Lat]
  intro v
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, valued_coe_eq]
  have h1 : v.intValuation (Dd (F := F)) ≤ WithZero.exp (-(dE v)) :=
    intValuation_le_of_mem_different v _ (Ideal.absNorm_mem _)
  have h2 : Valued.v (b v) ≤ WithZero.exp (dE v) := (hb v).trans (by
    rw [WithZero.exp_le_exp]; linarith [ell_nonpos a v])
  calc v.intValuation (Dd (F := F)) * Valued.v (b v)
      ≤ WithZero.exp (-(dE v)) * WithZero.exp (dE v) := mul_le_mul' h1 h2
    _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]

lemma isCompact_Ann_Lat {a : 𝓞 F} (ha : a ≠ 0) : IsCompact (Ann (Lat a)) :=
  (isCompact_Lat Dd_ne_zero).of_isClosed_subset (isClosed_Ann _) (Ann_subset_Lat_Dd ha)

lemma iInter_Ann_Lat (b : FiniteAdeleRing (𝓞 F) F)
    (hb : ∀ n, b ∈ Ann (Lat (aSeq (F := F) n))) : b = 0 := by
  refine FiniteAdeleRing.ext _ fun v => ?_
  by_contra h0
  have h0' : b v ≠ 0 := h0
  have hv : Valued.v (b v) ≠ 0 := (Valuation.ne_zero_iff _).2 h0'
  obtain ⟨c, hc⟩ : ∃ c : ℤ, Valued.v (b v) = WithZero.exp c :=
    ⟨WithZero.log _, (WithZero.exp_log hv).symm⟩
  set m : ℕ := (dE v - c + 1).toNat with hm
  set Nv : 𝓞 F := (Ideal.absNorm v.asIdeal : 𝓞 F)
  have hNv0 : Nv ≠ 0 := by
    have h : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact Nat.cast_ne_zero.2 h
  have ha0 : Nv ^ m ≠ 0 := pow_ne_zero _ hNv0
  obtain ⟨N, hN⟩ := dvd_aSeq ha0
  have hb' : b ∈ Ann (Lat (Nv ^ m)) := Ann_anti (Lat_mono (hN N le_rfl)) (hb N)
  rw [ann_Lat ha0] at hb'
  have h1 := hb' v
  have hNv : v.intValuation Nv ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, pow_one]
    exact Ideal.absNorm_mem _
  have h2 : v.intValuation (Nv ^ m) ≤ WithZero.exp (-(m : ℤ)) := by
    rw [map_pow]
    calc v.intValuation Nv ^ m ≤ WithZero.exp (-((1 : ℕ) : ℤ)) ^ m := pow_le_pow_left' hNv m
      _ = WithZero.exp (-(m : ℤ)) := by rw [← WithZero.exp_nsmul]; congr 1; simp
  rw [intValuation_eq_exp_ell ha0, WithZero.exp_le_exp] at h2
  rw [hc, WithZero.exp_le_exp] at h1
  have h3 : ((dE v - c + 1).toNat : ℤ) ≥ dE v - c + 1 := Int.self_le_toNat _
  omega

end GLat3

section GLat4

open scoped RestrictedProduct Topology
open Filter

/-- `∏_{v ∈ S} N(𝔭_v)^{d_v} = N(𝔡) = |d_F|` when `S` contains the places dividing `𝔡`. -/
lemma prod_absNorm_pow (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : S0 ⊆ S) :
    ∏ v ∈ S, (Ideal.absNorm v.asIdeal) ^ (multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))) =
      (discr F).natAbs := by
  rw [← NumberField.absNorm_differentIdeal F (𝓞 F)]
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization
    (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot]
  rw [finprod_eq_prod_of_mulSupport_subset (s := S) _ ?_]
  · rw [map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity differentIdeal_ne_bot, map_pow]
  · intro v hv
    by_contra h
    apply hv
    have hwd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := fun h' => h (hS
      ((Ideal.finite_factors (I := differentIdeal ℤ (𝓞 F)) differentIdeal_ne_bot).mem_toFinset.2 h'))
    show v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = 1
    rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity differentIdeal_ne_bot,
      multiplicity_eq_zero.2 hwd, pow_zero, Ideal.one_eq_top]

lemma CS_sq (S : Finset (HeightOneSpectrum (𝓞 F))) (hS : S0 ⊆ S) :
    (CS (F := F) S).toReal * (CS (F := F) S).toReal = 1 := by
  unfold CS
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_prod]
  simp_rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  have h1 : (∏ v ∈ S, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) *
      (∏ v ∈ S, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) =
      ∏ v ∈ S, (Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => Real.mul_self_sqrt (pow_nonneg (Nat.cast_nonneg _) _)
  have h2 : ∏ v ∈ S, (Ideal.absNorm v.asIdeal : ℝ) ^
      multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)) = |(discr F : ℝ)| := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (prod_absNorm_pow S hS)
    simp only [Nat.cast_prod, Nat.cast_pow] at h
    rw [h, Nat.cast_natAbs, Int.cast_abs]
  have h3 : Real.sqrt |(discr F : ℝ)| * Real.sqrt |(discr F : ℝ)| = |(discr F : ℝ)| :=
    Real.mul_self_sqrt (abs_nonneg _)
  have hd : |(discr F : ℝ)| ≠ 0 := abs_ne_zero.2 (Int.cast_ne_zero.2 (discr_ne_zero F))
  calc (Real.sqrt |(discr F : ℝ)|)⁻¹ * (∏ v ∈ S, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) *
      ((Real.sqrt |(discr F : ℝ)|)⁻¹ * (∏ v ∈ S, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))
      = (Real.sqrt |(discr F : ℝ)| * Real.sqrt |(discr F : ℝ)|)⁻¹ *
        ((∏ v ∈ S, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) *
        (∏ v ∈ S, Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
        multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) := by rw [mul_inv]; ring
    _ = |(discr F : ℝ)|⁻¹ * |(discr F : ℝ)| := by rw [h3, h1, h2]
    _ = 1 := inv_mul_cancel₀ hd

lemma loc_prod_one (S : Finset (HeightOneSpectrum (𝓞 F))) (k : S → ℤ) :
    (∏ v : S, ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^ (-(k v)) /
        Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F))))) *
    (∏ v : S, ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
        (-(-(k v + dE (v : HeightOneSpectrum (𝓞 F))))) /
        Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F))))) = 1 := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hq := absNorm_pos (v : HeightOneSpectrum (𝓞 F))
  set q : ℝ := (Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) with hqdef
  set d : ℕ := multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F))
  have hs : Real.sqrt (q ^ d) * Real.sqrt (q ^ d) = q ^ d := Real.mul_self_sqrt (pow_nonneg hq.le _)
  have hpos : 0 < q ^ d := pow_pos hq _
  rw [div_mul_div_comm, hs, ← zpow_add₀ hq.ne']
  have e : -(k v) + -(-(k v + dE (v : HeightOneSpectrum (𝓞 F)))) = ((d : ℕ) : ℤ) := by
    unfold dE; ring
  rw [e, zpow_natCast, div_self hpos.ne']

theorem prod_meas_eq_one (νf : Measure (FiniteAdeleRing (𝓞 F) F)) [νf.IsAddHaarMeasure]
    (hνf : MeasurePreserving (eAd (F := F)) ((infiniteAdditiveTamagawa F).prod νf)
      (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)))
    {a : 𝓞 F} (ha : a ≠ 0) :
    (νf (Lat a)).toReal * (νf (Ann (Lat a))).toReal = 1 := by
  classical
  set S := supp a ha ∪ S0
  rw [Ann_eq_gS ha S Finset.subset_union_left Finset.subset_union_right,
    Lat_eq_gS ha S Finset.subset_union_left,
    nuf_gS S νf hνf _ (measurableSet_box S _), nuf_gS S νf hνf _ (measurableSet_box S _),
    ENNReal.toReal_mul, ENNReal.toReal_mul, muFin_box_toReal, muFin_box_toReal]
  have h1 := loc_prod_one S (fun v => ell a (v : HeightOneSpectrum (𝓞 F)))
  have h2 := CS_sq (F := F) S Finset.subset_union_right
  calc _ = ((∏ v : S, ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          (-(ell a (v : HeightOneSpectrum (𝓞 F)))) /
        Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F))))) *
      (∏ v : S, ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
        (-(-(ell a (v : HeightOneSpectrum (𝓞 F)) + dE (v : HeightOneSpectrum (𝓞 F))))) /
        Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)))))) *
      ((CS (F := F) S).toReal * (CS (F := F) S).toReal) := by ring
    _ = 1 := by rw [h1, h2, one_mul]

lemma integral_chiF_Lat (νf : Measure (FiniteAdeleRing (𝓞 F) F)) [νf.IsAddHaarMeasure]
    (a : 𝓞 F) (b : FiniteAdeleRing (𝓞 F) F) :
    ∫ y in Lat a, chiF (y * b) ∂νf =
      Set.indicator (Ann (Lat a)) (fun _ => ((νf (Lat a)).toReal : ℂ)) b := by
  have hL : MeasurableSet (Lat a) := (isClosed_Lat a).measurableSet
  by_cases hb : b ∈ Ann (Lat a)
  · rw [Set.indicator_of_mem hb, setIntegral_congr_fun hL (fun y hy => hb y hy),
      setIntegral_const, Complex.real_smul, mul_one]
    rfl
  · have hb' : ¬ ∀ y ∈ Lat a, chiF (y * b) = 1 := hb
    push Not at hb'
    obtain ⟨y₀, hy₀, hne⟩ := hb'
    rw [Set.indicator_of_notMem hb]
    set I := ∫ y in Lat a, chiF (y * b) ∂νf with hI
    have hshift : I = chiF (y₀ * b) * I := by
      have h1 : I = ∫ y, (Lat a).indicator (fun y => chiF (y * b)) (y₀ + y) ∂νf := by
        rw [integral_add_left_eq_self, integral_indicator hL]
      have h2 : (fun y => (Lat a).indicator (fun y => chiF (y * b)) (y₀ + y)) =
          (Lat a).indicator (fun y => chiF (y₀ * b) * chiF (y * b)) := by
        funext y
        by_cases hy : y ∈ Lat a
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (Lat_add hy₀ hy), add_mul, chiF_add]
        · have hy' : y₀ + y ∉ Lat a := fun h => hy (by
            have := Lat_add (Lat_neg hy₀) h
            rwa [neg_add_cancel_left] at this)
          rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy']
      refine h1.trans ?_
      rw [h2, integral_indicator hL, integral_const_mul, hI]
    have h3 : (1 - chiF (y₀ * b)) * I = 0 := by linear_combination hshift
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

lemma Ann_small (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : FiniteAdeleRing (𝓞 F) F)) :
    ∀ᶠ n in atTop, Ann (Lat (aSeq (F := F) n)) ⊆ U := by
  have hanti : Antitone fun n => Ann (Lat (aSeq (F := F) n)) :=
    fun n m h => Ann_anti (Lat_mono (aSeq_dvd h))
  have hdir : Directed (· ⊇ ·) fun n => Ann (Lat (aSeq (F := F) n)) := fun i j =>
    ⟨max i j, hanti (le_max_left i j), hanti (le_max_right i j)⟩
  obtain ⟨n₀, hn₀⟩ := exists_subset_nhds_of_isCompact' hdir
    (fun n => isCompact_Ann_Lat (aSeq_ne_zero n)) (fun n => isClosed_Ann _) (U := U)
    (fun x hx => by
      rw [iInter_Ann_Lat x (Set.mem_iInter.1 hx)]; exact hU)
  exact eventually_atTop.2 ⟨n₀, fun n hn => (hanti hn).trans hn₀⟩

end GLat4

section GAssem

open Filter Topology

theorem selfDual (f : AdeleRing (𝓞 F) F → ℂ) (hf : Continuous f)
    (hfi : Integrable f tamagawaAdelic)
    (hfh : Integrable (adelicFourierFun f) tamagawaAdelic) (z : AdeleRing (𝓞 F) F) :
    adelicFourierFun (adelicFourierFun f) z = f (-z) := by
  obtain ⟨νf, hνH, hνf⟩ := exists_prod_decomp (F := F)
  set P := (infiniteAdditiveTamagawa F).prod νf with hP
  have hT : ∀ g : AdeleRing (𝓞 F) F → ℂ,
      ∫ x, g x ∂(tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)) = ∫ p, g (eAd p) ∂P :=
    fun g => (hνf.integral_comp' g).symm
  have hFT : ∀ (φ : AdeleRing (𝓞 F) F → ℂ) (y : AdeleRing (𝓞 F) F),
      adelicFourierFun φ y =
        ∫ p, φ (eAd p) * (charInf (p.1 * y.1) * chiF (p.2 * y.2)) ∂P := by
    intro φ y
    unfold adelicFourierFun
    rw [hT]
    congr 1
    funext p
    rw [gchar_split]
    rfl
  set g : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F → ℂ := fun p => f (eAd p) with hgdef
  have hg : Continuous g := hf.comp (by exact continuous_id)
  have hgi : Integrable g P := (hνf.integrable_comp_emb (eAd (F := F)).measurableEmbedding).2 hfi
  have hgh : Integrable (fun y : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F =>
      ∫ x, g x * (charInf (x.1 * y.1) * chiF (x.2 * y.2)) ∂P) P := by
    have h : (fun y : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F =>
        ∫ x, g x * (charInf (x.1 * y.1) * chiF (x.2 * y.2)) ∂P) =
        (adelicFourierFun f) ∘ (eAd (F := F)) := by
      funext y
      rw [Function.comp_apply, hFT]
      rfl
    rw [h]
    exact (hνf.integrable_comp_emb (eAd (F := F)).measurableEmbedding).2 hfh
  have key := partial_inversion (infiniteAdditiveTamagawa F) νf charInf chiF
    charInf_continuous charInf_norm chiF_continuous chiF_norm chiF_add
    (fun g hg hg1 hg2 z => arch_inversion g hg hg1 hg2 z)
    (fun n => Lat (aSeq (F := F) n)) (fun n => Ann (Lat (aSeq (F := F) n)))
    (fun n => (νf (Lat (aSeq (F := F) n))).toReal)
    (fun n => (isClosed_Lat _).measurableSet)
    (fun n m h => Lat_mono (aSeq_dvd h)) iUnion_Lat_aSeq
    (fun n => (isCompact_Lat (aSeq_ne_zero n)).measure_lt_top.ne)
    (fun n => isCompact_Ann_Lat (aSeq_ne_zero n)) Ann_small
    (fun n b => integral_chiF_Lat νf _ b)
    (fun n => prod_meas_eq_one νf hνf (aSeq_ne_zero n))
    g hg hgi hgh ((eAd (F := F)).symm z)
  rw [hFT]
  simp_rw [hFT f]
  exact key

end GAssem

end Sol_MasulloGRH_tamagawaAdelic_selfDual_stdAdelicCharacter

open MasulloGRH Sol_MasulloGRH_tamagawaAdelic_selfDual_stdAdelicCharacter in
theorem solution
    (F : Type*) [Field F] [NumberField F] :
    (∀ x y : AdeleRing (𝓞 F) F,
      stdAdelicCharacter (x + y) = stdAdelicCharacter x * stdAdelicCharacter y) ∧
    (∀ x : AdeleRing (𝓞 F) F, ‖stdAdelicCharacter x‖ = 1) ∧
    Continuous (stdAdelicCharacter : AdeleRing (𝓞 F) F → ℂ) ∧
    (∀ ξ : F, stdAdelicCharacter (algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1) ∧
    (∃ x : AdeleRing (𝓞 F) F, stdAdelicCharacter x ≠ 1) ∧
    ∀ f : AdeleRing (𝓞 F) F → ℂ, Continuous f → Integrable f tamagawaAdelic →
      Integrable (adelicFourierFun f) tamagawaAdelic →
      ∀ z : AdeleRing (𝓞 F) F, adelicFourierFun (adelicFourierFun f) z = f (-z) :=
  ⟨gchar_add, gchar_norm, gchar_continuous, gchar_algebraMap, gchar_nontriv,
    fun f hf hfi hfh z => selfDual f hf hfi hfh z⟩

