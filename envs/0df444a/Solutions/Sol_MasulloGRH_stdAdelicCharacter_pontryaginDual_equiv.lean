-- Prove2me | solution 1 for MasulloGRH.stdAdelicCharacter_pontryaginDual_equiv
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T18:50:06.45892+00:00
-- url     : https://prove2.me/submissions/3d6c062d-9f70-48a0-80bb-550e8a7c07f6

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_SLocalStandardCharacter
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_NumberField_AdelicBox
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_LCAGroup_pontryagin_duality
import Theorems.Thm_MasulloGRH_pontryaginDual_separates_of_locallyCompact

open NumberField IsDedekindDomain

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal NNReal WithZero

namespace Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

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

instance infAdeleBorel : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((w : InfinitePlace F) → w.Completion))

instance infAdeleT2 : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))

instance infAdeleSecondCountable : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

variable (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- The finite part `∏_{v ∈ S_f} F_v` of the `S`-adeles. -/
abbrev FinPart := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F

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

end Finite




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








section Arch

open InfinitePlace.Completion
open scoped RealInnerProductSpace FourierTransform


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

end Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

namespace Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

open MasulloGRH Filter Topology

variable {F : Type*} [Field F] [NumberField F]

section Dual

instance adeleLC : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance adeleT2 : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

instance mulAdeleLC : LocallyCompactSpace (Multiplicative (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (LocallyCompactSpace (AdeleRing (𝓞 F) F))

instance mulAdeleT2 : T2Space (Multiplicative (AdeleRing (𝓞 F) F)) :=
  inferInstanceAs (T2Space (AdeleRing (𝓞 F) F))

/-! ### No small subgroups in `ℂ` -/

lemma norm_sq_sub_one_ge (u : ℂ) (hu : ‖u - 1‖ < 1 / 2) :
    3 / 2 * ‖u - 1‖ ≤ ‖u ^ 2 - 1‖ := by
  have e : u ^ 2 - 1 = (u - 1) * ((u - 1) + 2) := by ring
  have h2 : 3 / 2 ≤ ‖(u - 1) + 2‖ := by
    have h := norm_sub_norm_le (2 : ℂ) (-(u - 1))
    have e2 : (2 : ℂ) - -(u - 1) = (u - 1) + 2 := by ring
    rw [e2, norm_neg] at h
    have : ‖(2 : ℂ)‖ = 2 := by simp
    linarith
  rw [e, norm_mul]
  nlinarith [norm_nonneg (u - 1)]

lemma eq_one_of_forall_pow (w : ℂ) (h : ∀ m : ℕ, ‖w ^ m - 1‖ < 1 / 2) : w = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖w - 1‖ ≤ ‖w ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 := norm_sq_sub_one_ge (w ^ (2 ^ k)) (h _)
      have e : (w ^ (2 ^ k)) ^ 2 = w ^ (2 ^ (k + 1)) := by
        rw [← pow_mul, pow_succ]
      rw [e] at h1
      rw [pow_succ]
      nlinarith
  by_contra hne
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 2 / ‖w - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  have h3 := key k
  have h4 := h (2 ^ k)
  rw [div_lt_iff₀ hpos] at hk
  linarith

/-! ### The character `ψ` with values in the circle -/

/-- `ψ_{F,std}` as a map to the circle. -/
noncomputable def psiC (x : AdeleRing (𝓞 F) F) : Circle :=
  ⟨stdAdelicCharacter x, mem_sphere_zero_iff_norm.2 (gchar_norm x)⟩

lemma coe_psiC (x : AdeleRing (𝓞 F) F) : ((psiC x : Circle) : ℂ) = stdAdelicCharacter x := rfl

lemma gchar_zero : stdAdelicCharacter (0 : AdeleRing (𝓞 F) F) = 1 := by
  have h := gchar_algebraMap (F := F) 0
  rwa [map_zero] at h

lemma continuous_psiC : Continuous (psiC (F := F)) :=
  Continuous.subtype_mk gchar_continuous _

/-- The character `x ↦ ψ(x y)`. -/
noncomputable def chi (y : AdeleRing (𝓞 F) F) :
    ContinuousMonoidHom (Multiplicative (AdeleRing (𝓞 F) F)) Circle where
  toFun x := psiC (Multiplicative.toAdd x * y)
  map_one' := by
    apply Circle.ext
    rw [coe_psiC, toAdd_one, zero_mul, gchar_zero, Circle.coe_one]
  map_mul' x x' := by
    apply Circle.ext
    rw [Circle.coe_mul, coe_psiC, coe_psiC, coe_psiC, toAdd_mul, add_mul, gchar_add]
  continuous_toFun :=
    continuous_psiC.comp ((continuous_toAdd).mul continuous_const)

lemma chi_apply (y x : AdeleRing (𝓞 F) F) :
    ((chi y (Multiplicative.ofAdd x) : Circle) : ℂ) = stdAdelicCharacter (x * y) := rfl

/-- The homomorphism `y ↦ χ_y`. -/
noncomputable def phi : Multiplicative (AdeleRing (𝓞 F) F) →*
    PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)) where
  toFun y := chi (Multiplicative.toAdd y)
  map_one' := by
    refine ContinuousMonoidHom.ext fun x => Circle.ext ?_
    show stdAdelicCharacter (Multiplicative.toAdd x * Multiplicative.toAdd (1 : Multiplicative _))
      = ((1 : Circle) : ℂ)
    rw [toAdd_one, mul_zero, gchar_zero, Circle.coe_one]
  map_mul' y y' := by
    refine ContinuousMonoidHom.ext fun x => Circle.ext ?_
    show stdAdelicCharacter (Multiplicative.toAdd x * Multiplicative.toAdd (y * y')) =
      stdAdelicCharacter (Multiplicative.toAdd x * Multiplicative.toAdd y) *
        stdAdelicCharacter (Multiplicative.toAdd x * Multiplicative.toAdd y')
    rw [toAdd_mul, mul_add, gchar_add]

lemma phi_apply (y x : AdeleRing (𝓞 F) F) :
    ((phi (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
      stdAdelicCharacter (x * y) := rfl

lemma continuous_phi : Continuous (phi (F := F)) := by
  refine ContinuousMonoidHom.continuous_of_continuous_uncurry _ ?_
  exact continuous_psiC.comp ((continuous_toAdd.comp continuous_snd).mul
    (continuous_toAdd.comp continuous_fst))

end Dual

end Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

namespace Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

open MasulloGRH Filter Topology
open scoped Classical

variable {F : Type*} [Field F] [NumberField F]

section Inj

lemma charInf_zero : charInf (0 : InfiniteAdeleRing F) = 1 := by
  rw [charInf_eq, trInf_zero]
  simp

lemma chiF_zero : chiF (0 : FiniteAdeleRing (𝓞 F) F) = 1 := gchar_zero

lemma qH_zero : qH (0 : InfiniteAdeleRing F) = 0 := by
  have h : ∀ x : InfiniteAdeleRing F, inner ℝ (pH x) (qH (0 : InfiniteAdeleRing F)) = 0 := by
    intro x
    rw [← trInf_mul_eq_inner, mul_zero, trInf_zero]
  have h1 := h (pH.symm (qH 0))
  rw [Homeomorph.apply_symm_apply] at h1
  exact inner_self_eq_zero.1 h1

lemma pH_zero : pH (0 : InfiniteAdeleRing F) = 0 := by
  have h : ∀ y : InfiniteAdeleRing F, inner ℝ (pH (0 : InfiniteAdeleRing F)) (qH y) = 0 := by
    intro y
    rw [← trInf_mul_eq_inner, zero_mul, trInf_zero]
  have h1 := h (qH.symm (pH 0))
  rw [Homeomorph.apply_symm_apply] at h1
  exact inner_self_eq_zero.1 h1

lemma pH_symm_zero : (pH (F := F)).symm 0 = 0 := by
  rw [← pH_zero, Homeomorph.symm_apply_apply]

lemma qH_symm_zero : (qH (F := F)).symm 0 = 0 := by
  rw [← qH_zero, Homeomorph.symm_apply_apply]

/-- The test vector `p = z / (2 ‖z‖²)`, with `⟪p, z⟫ = 1/2`. -/
lemma test_vector (z : mixedEmbedding.euclidean.mixedSpace F) (hz : z ≠ 0) :
    inner ℝ ((1 / (2 * ‖z‖ ^ 2)) • z) z = 1 / 2 ∧
      ‖(1 / (2 * ‖z‖ ^ 2)) • z‖ = 1 / (2 * ‖z‖) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  constructor
  · rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    field_simp
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp

lemma exp_half : Complex.exp (↑(-2 * Real.pi * (1 / 2 : ℝ)) * Complex.I) = -1 := by
  have e : (↑(-2 * Real.pi * (1 / 2 : ℝ)) * Complex.I : ℂ) = -(Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- `ψ(x y) = 1` for all `x` forces `y = 0`. -/
lemma eq_zero_of_forall (y : AdeleRing (𝓞 F) F)
    (h : ∀ x : AdeleRing (𝓞 F) F, stdAdelicCharacter (x * y) = 1) : y = 0 := by
  have h2 : y.2 = 0 := by
    apply iInter_Ann_Lat
    intro n b _
    have h1 := h (mkA 0 b)
    rw [gchar_split] at h1
    have e1 : charInf ((mkA 0 b * y).1) = 1 := by
      show charInf (0 * y.1) = 1
      rw [zero_mul, charInf_zero]
    rw [e1, one_mul] at h1
    exact h1
  have h1 : y.1 = 0 := by
    by_contra hne
    set z := qH y.1 with hzdef
    have hz : z ≠ 0 := fun hz => hne (qH.injective (hz.trans qH_zero.symm))
    obtain ⟨hin, -⟩ := test_vector z hz
    set p : mixedEmbedding.euclidean.mixedSpace F := (1 / (2 * ‖z‖ ^ 2)) • z with hp
    have h1 := h (mkA (pH.symm p) 0)
    rw [gchar_split] at h1
    have e1 : charInf ((mkA (pH.symm p) 0 * y).1) = -1 := by
      show charInf (pH.symm p * y.1) = -1
      rw [charInf_mul_eq, Homeomorph.apply_symm_apply, ← hzdef, hin]
      exact exp_half
    have e2 : chiF ((mkA (pH.symm p) 0 * y).2) = 1 := by
      show chiF (0 * y.2) = 1
      rw [zero_mul, chiF_zero]
    rw [e1, e2] at h1
    norm_num at h1
  exact Prod.ext h1 h2

end Inj

section Estimate

lemma zero_mem_Lat (a : 𝓞 F) : (0 : FiniteAdeleRing (𝓞 F) F) ∈ Lat a := by
  rw [mem_Lat]
  intro v
  have e : (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := rfl
  rw [e, mul_zero]
  exact zero_mem _

lemma nsmul_mem_Lat {a : 𝓞 F} {b : FiniteAdeleRing (𝓞 F) F} (hb : b ∈ Lat a) (m : ℕ) :
    m • b ∈ Lat a := by
  induction m with
  | zero => rw [zero_smul]; exact zero_mem_Lat a
  | succ m ih => rw [succ_nsmul]; exact Lat_add ih hb

lemma chiF_nsmul (b : FiniteAdeleRing (𝓞 F) F) (m : ℕ) : chiF (m • b) = chiF b ^ m := by
  induction m with
  | zero => rw [zero_smul, pow_zero]; exact chiF_zero
  | succ m ih => rw [succ_nsmul, chiF_add, ih, pow_succ]

/-- The key estimate: characters `χ_y` uniformly close to `1` on a suitable compact set have
`y` in a given neighbourhood of `0`. -/
lemma estimate (U : Set (AdeleRing (𝓞 F) F)) (hU : U ∈ 𝓝 (0 : AdeleRing (𝓞 F) F)) :
    ∃ K : Set (AdeleRing (𝓞 F) F), IsCompact K ∧ ∀ y : AdeleRing (𝓞 F) F,
      (∀ x ∈ K, ‖stdAdelicCharacter (x * y) - 1‖ < 1 / 2) → y ∈ U := by
  obtain ⟨U1, hU1, U2, hU2, hsub⟩ := mem_nhds_prod_iff.1
    (show (U : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) ∈
      𝓝 ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F)) from hU)
  obtain ⟨n, hn⟩ := (Ann_small U2 hU2).exists
  have hU1' : (qH (F := F)).symm ⁻¹' U1 ∈ 𝓝 (0 : mixedEmbedding.euclidean.mixedSpace F) := by
    apply (qH (F := F)).symm.continuous.continuousAt
    rw [qH_symm_zero]
    exact hU1
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hU1'
  set R : ℝ := 1 / (2 * δ) with hR
  have hR0 : 0 ≤ R := by positivity
  set K1 : Set (InfiniteAdeleRing F) := pH.symm '' Metric.closedBall 0 R
  set K2 : Set (FiniteAdeleRing (𝓞 F) F) := Lat (aSeq (F := F) n)
  have hK : IsCompact (K1 ×ˢ K2 : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) :=
    ((isCompact_closedBall 0 R).image pH.symm.continuous).prod (isCompact_Lat (aSeq_ne_zero n))
  have h0K1 : (0 : InfiniteAdeleRing F) ∈ K1 :=
    ⟨0, Metric.mem_closedBall_self hR0, pH_symm_zero⟩
  refine ⟨K1 ×ˢ K2, hK, ?_⟩
  intro y hy
  apply hsub
  refine ⟨?_, ?_⟩
  · by_contra hy1
    have hz : δ ≤ ‖qH y.1‖ := by
      by_contra hlt
      push Not at hlt
      apply hy1
      have h3 : qH y.1 ∈ Metric.ball (0 : mixedEmbedding.euclidean.mixedSpace F) δ :=
        mem_ball_zero_iff.2 hlt
      have h4 := hball h3
      rw [Set.mem_preimage, Homeomorph.symm_apply_apply] at h4
      exact h4
    set z := qH y.1 with hzdef
    have hz0 : z ≠ 0 := fun h0 => by
      rw [h0, norm_zero] at hz
      linarith
    obtain ⟨hin, hnorm⟩ := test_vector z hz0
    set p : mixedEmbedding.euclidean.mixedSpace F := (1 / (2 * ‖z‖ ^ 2)) • z with hp
    have hpR : ‖p‖ ≤ R := by
      rw [hnorm, hR]
      gcongr
    have hmem : mkA (pH.symm p) 0 ∈ (K1 ×ˢ K2 : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) :=
      ⟨⟨p, mem_closedBall_zero_iff.2 hpR, rfl⟩, zero_mem_Lat _⟩
    have h1 := hy _ hmem
    rw [gchar_split] at h1
    have e1 : charInf ((mkA (pH.symm p) 0 * y).1) = -1 := by
      show charInf (pH.symm p * y.1) = -1
      rw [charInf_mul_eq, Homeomorph.apply_symm_apply, ← hzdef, hin]
      exact exp_half
    have e2 : chiF ((mkA (pH.symm p) 0 * y).2) = 1 := by
      show chiF (0 * y.2) = 1
      rw [zero_mul, chiF_zero]
    rw [e1, e2] at h1
    norm_num at h1
  · apply hn
    intro b hb
    apply eq_one_of_forall_pow
    intro m
    rw [← chiF_nsmul, ← smul_mul_assoc]
    have hmem : mkA 0 (m • b) ∈ (K1 ×ˢ K2 : Set (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)) :=
      ⟨h0K1, nsmul_mem_Lat hb m⟩
    have h1 := hy _ hmem
    rw [gchar_split] at h1
    have e1 : charInf ((mkA 0 (m • b) * y).1) = 1 := by
      show charInf (0 * y.1) = 1
      rw [zero_mul, charInf_zero]
    rw [e1, one_mul] at h1
    exact h1

end Estimate

end Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

namespace Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

open MasulloGRH Filter Topology

variable {F : Type*} [Field F] [NumberField F]

section Main

/-- The basic neighbourhood `{χ : |χ(x) - 1| < 1/2 on K}` of `1` in the dual. -/
def Wset (K : Set (AdeleRing (𝓞 F) F)) :
    Set (PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F))) :=
  {χ | ∀ x ∈ K, ‖((χ (Multiplicative.ofAdd x) : Circle) : ℂ) - 1‖ < 1 / 2}

lemma isOpen_Wset {K : Set (AdeleRing (𝓞 F) F)} (hK : IsCompact K) : IsOpen (Wset K) := by
  have hV : IsOpen {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2} :=
    isOpen_lt (continuous_norm.comp (continuous_subtype_val.sub continuous_const))
      continuous_const
  have hK' : IsCompact (Multiplicative.ofAdd '' K) := hK.image continuous_ofAdd
  have h := (ContinuousMap.isOpen_setOfPred_mapsTo hK' hV).preimage
    (ContinuousMonoidHom.isInducing_toContinuousMap
      (Multiplicative (AdeleRing (𝓞 F) F)) Circle).continuous
  have e : Wset K = ((ContinuousMonoidHom.toContinuousMap :
      ContinuousMonoidHom (Multiplicative (AdeleRing (𝓞 F) F)) Circle →
        C(Multiplicative (AdeleRing (𝓞 F) F), Circle)) ⁻¹'
      {f | Set.MapsTo f (Multiplicative.ofAdd '' K) {z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2}}) := by
    ext χ
    constructor
    · intro hχ x hx
      obtain ⟨x', hx', rfl⟩ := hx
      exact hχ x' hx'
    · intro hχ x hx
      exact hχ ⟨x, hx, rfl⟩
  rw [e]
  exact h

lemma one_mem_Wset (K : Set (AdeleRing (𝓞 F) F)) : (1 : PontryaginDual _) ∈ Wset K := by
  intro x _
  have e : (((1 : PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)))
      (Multiplicative.ofAdd x) : Circle) : ℂ) = 1 := rfl
  rw [e, sub_self, norm_zero]
  norm_num

lemma dense_range_phi : Dense (Set.range (phi (F := F))) := by
  set G := Multiplicative (AdeleRing (𝓞 F) F)
  set H : Subgroup (PontryaginDual G) := (phi (F := F)).range.topologicalClosure with hHdef
  have hH : ∀ χ, χ ∈ H := by
    intro χ0
    by_contra hχ0
    obtain ⟨X, hX1, hX2⟩ := MasulloGRH.pontryaginDual_separates_of_locallyCompact
      (PontryaginDual G) H (phi (F := F)).range.isClosed_topologicalClosure χ0 hχ0
    obtain ⟨e, he⟩ := LCAGroup.pontryagin_duality G
    set x := e.symm X
    have hXe : ∀ χ, X χ = χ x := fun χ => by rw [← he x χ, e.apply_symm_apply]
    have hx : Multiplicative.toAdd x = 0 := by
      apply eq_zero_of_forall
      intro y
      have h1 := hX1 (phi (Multiplicative.ofAdd y))
        (Subgroup.le_topologicalClosure _ (MonoidHom.mem_range.2 ⟨Multiplicative.ofAdd y, rfl⟩))
      rw [hXe] at h1
      have h2 := congrArg (fun z : Circle => (z : ℂ)) h1
      simp only [Circle.coe_one] at h2
      rw [mul_comm]
      exact h2
    apply hX2
    rw [hXe]
    have hx1 : x = 1 := hx
    rw [hx1, map_one]
  rw [dense_iff_closure_eq, ← MonoidHom.coe_range, ← Subgroup.topologicalClosure_coe]
  exact Set.eq_univ_of_forall hH

lemma surjective_phi : Function.Surjective (phi (F := F)) := by
  obtain ⟨C, hC, hCn⟩ := exists_compact_mem_nhds (0 : AdeleRing (𝓞 F) F)
  obtain ⟨K, hK, hKC⟩ := estimate C hCn
  set R := (phi (F := F)).range with hRdef
  have hW : Wset K ⊆ (R : Set _) := by
    intro χ hχ
    have hcl : χ ∈ closure (Wset K ∩ Set.range (phi (F := F))) :=
      (isOpen_Wset hK).inter_closure ⟨hχ, by rw [dense_range_phi.closure_eq]; trivial⟩
    have hsub : Wset K ∩ Set.range (phi (F := F)) ⊆
        phi '' (Multiplicative.ofAdd '' C) := by
      rintro _ ⟨hy, ⟨y, rfl⟩⟩
      exact ⟨y, ⟨Multiplicative.toAdd y, hKC _ (fun x hx => hy x hx), rfl⟩, rfl⟩
    have hcomp : IsCompact (phi '' (Multiplicative.ofAdd '' C)) :=
      (hC.image continuous_ofAdd).image continuous_phi
    obtain ⟨y, _, hy⟩ := closure_minimal hsub hcomp.isClosed hcl
    exact ⟨y, hy⟩
  have hRo : IsOpen (R : Set (PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)))) :=
    R.isOpen_of_mem_nhds (g := 1)
      (Filter.mem_of_superset ((isOpen_Wset hK).mem_nhds (one_mem_Wset K)) hW)
  have hRc : IsClosed (R : Set (PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)))) :=
    R.isClosed_of_isOpen hRo
  intro χ
  have h1 : χ ∈ closure (R : Set (PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)))) := by
    rw [MonoidHom.coe_range, dense_range_phi.closure_eq]
    trivial
  rw [hRc.closure_eq] at h1
  exact h1

lemma injective_phi : Function.Injective (phi (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have h : Multiplicative.toAdd y = 0 := by
    apply eq_zero_of_forall
    intro x
    have h1 := congrArg
      (fun χ : PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)) =>
        ((χ (Multiplicative.ofAdd x) : Circle) : ℂ)) hy
    exact h1
  exact h

theorem main : ∃ e : Multiplicative (AdeleRing (𝓞 F) F) ≃ₜ*
        PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)),
      ∀ x y : AdeleRing (𝓞 F) F,
        ((e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
          stdAdelicCharacter (x * y) := by
  set e0 := MulEquiv.ofBijective (phi (F := F)) ⟨injective_phi, surjective_phi⟩ with he0
  have hcont : Continuous e0.symm := by
    refine continuous_of_continuousAt_one e0.symm ?_
    rw [ContinuousAt, map_one]
    intro U hU
    refine Filter.mem_map.2 ?_
    have hU' : Multiplicative.ofAdd ⁻¹' U ∈ 𝓝 (0 : AdeleRing (𝓞 F) F) :=
      continuous_ofAdd.continuousAt.preimage_mem_nhds hU
    obtain ⟨K, hK, hKU⟩ := estimate _ hU'
    refine Filter.mem_of_superset ((isOpen_Wset hK).mem_nhds (one_mem_Wset K)) ?_
    intro χ hχ
    have hχ' : phi (e0.symm χ) = χ := e0.apply_symm_apply χ
    rw [← hχ'] at hχ
    exact hKU (Multiplicative.toAdd (e0.symm χ)) (fun x hx => hχ x hx)
  exact ⟨{ e0 with
    continuous_toFun := continuous_phi
    continuous_invFun := hcont }, fun x y => rfl⟩

end Main

end Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv

open MasulloGRH Sol_MasulloGRH_stdAdelicCharacter_pontryaginDual_equiv in
theorem solution
    (F : Type*) [Field F] [NumberField F] :
    ∃ e : Multiplicative (AdeleRing (𝓞 F) F) ≃ₜ*
        PontryaginDual (Multiplicative (AdeleRing (𝓞 F) F)),
      ∀ x y : AdeleRing (𝓞 F) F,
        ((e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x) : Circle) : ℂ) =
          stdAdelicCharacter (x * y) :=
  main
