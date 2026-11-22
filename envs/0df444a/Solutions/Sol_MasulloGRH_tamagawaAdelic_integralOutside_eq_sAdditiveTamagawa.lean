-- Prove2me | solution 1 for MasulloGRH.tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T14:41:44.865462+00:00
-- url     : https://prove2.me/submissions/59ab8173-c01f-41e2-acd7-42b51e5550ad

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_SIntegerFundamentalDomain
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_precompact
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_cover
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_disjoint
import Theorems.Thm_MasulloGRH_sAdditiveTamagawa_isAddHaarMeasure
import Theorems.Thm_MasulloGRH_sIntegerLattice_covolume_sAdditiveTamagawa
import Theorems.Thm_MasulloGRH_sIntegerFundamentalDomain_existsUnique

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The additive Tamagawa measure is the restricted product of the local measures

Let `ν` be the Haar measure on `𝔸_F` for which a measurable strict fundamental domain of `F`
has mass one, and `U_S = 𝔸_{F,S} × ∏_{v ∉ S} 𝒪_v` the open subring of adeles integral outside
`S`, with projection `p : 𝔸_F → 𝔸_{F,S}`.

* `ν` is well defined: `D = D_{F,∞} × ∏_v 𝒪_v` is a measurable strict fundamental domain
  (platform theorems `RiemannMasullo.adeleFundamentalDomain_cover` and `_disjoint`) of finite
  positive Haar measure (`RiemannMasullo.adeleFundamentalDomain_precompact`), so a rescaled
  Haar measure of `𝔸_F` (locally compact: restricted product of locally compact fields with
  compact open subrings) gives it mass one; all strict fundamental domains of the countable
  group `F` have the same measure.
* `μ = p_*(ν|_{U_S})` is translation invariant on `𝔸_{F,S}` (translate by the adele `(a, 0)`)
  and finite on compact sets (`U_S ∩ p⁻¹ K` is the continuous image of `K × ∏_{v ∉ S} 𝒪_v`), so
  by uniqueness of Haar measure `μ = c • ν_S`.
* Evaluating on `D_{F,S} = D_{F,∞} × ∏_{v ∈ S_f} 𝒪_v`, with `U_S ∩ p⁻¹ D_{F,S} = D`, gives
  `1 = c · ν_S(D_{F,S}) = c · √|d_F| ∏_{v ∈ S_f} N(𝔡_v)^{-1/2}`
  (platform theorem `MasulloGRH.sIntegerLattice_covolume_sAdditiveTamagawa`).

The argument follows the proof in the open formalization mccorvie/riemann-masullo.
-/

namespace Sol_MasulloGRH_tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa

open MasulloGRH InfinitePlace.Completion
open scoped RestrictedProduct Pointwise

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-- The projection `𝔸_F → 𝔸_{F,S}` onto the coordinates at the places of `S`. -/
def proj (x : AdeleRing (𝓞 F) F) : SAdeleRing F Sf :=
  (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F)))

/-- The open subring of adeles integral outside `S`. -/
def intOut : Set (AdeleRing (𝓞 F) F) :=
  {x | ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F}

/-- The product of the local integers at the finite places outside `S`. -/
abbrev Tail : Type _ :=
  (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf}) → v.1.adicCompletionIntegers F

open Classical in
/-- Gluing an `S`-adele and a family of local integers outside `S`, as an element of the
restricted product with respect to the principal filter of the complement of `S`. -/
def glueP (p : SAdeleRing F Sf × Tail F Sf) :
    Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]_[
      Filter.principal ((Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ)] :=
  ⟨fun v => if h : v ∈ Sf then p.1.2 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : v.adicCompletion F),
    Filter.eventually_principal.mpr fun v hv => by
      have hv' : v ∉ Sf := hv
      simp only [dif_neg hv']
      exact (p.2 ⟨v, hv'⟩).2⟩

open Classical in
theorem glueP_apply (p : SAdeleRing F Sf × Tail F Sf) (v : HeightOneSpectrum (𝓞 F)) :
    (glueP F Sf p) v =
      if h : v ∈ Sf then p.1.2 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : v.adicCompletion F) := rfl

omit [NumberField F] in
theorem cofinite_le : Filter.cofinite ≤
    Filter.principal ((Sf : Set (HeightOneSpectrum (𝓞 F)))ᶜ) := by
  rw [Filter.le_principal_iff, Filter.mem_cofinite, compl_compl]
  exact Sf.finite_toSet

/-- Gluing an `S`-adele and a family of local integers outside `S` into an adele. -/
def glue (p : SAdeleRing F Sf × Tail F Sf) : AdeleRing (𝓞 F) F :=
  (p.1.1, RestrictedProduct.inclusion _ _ (cofinite_le F Sf) (glueP F Sf p))

open Classical in
theorem glue_snd_apply (p : SAdeleRing F Sf × Tail F Sf) (v : HeightOneSpectrum (𝓞 F)) :
    (glue F Sf p).2 v =
      if h : v ∈ Sf then p.1.2 ⟨v, h⟩ else (p.2 ⟨v, h⟩ : v.adicCompletion F) := rfl

theorem continuous_glue : Continuous (glue F Sf) := by
  have h2 : Continuous (glueP F Sf) := by
    apply RestrictedProduct.continuous_rng_of_principal.mpr
    apply continuous_pi
    intro v
    by_cases h : v ∈ Sf
    · have : (fun p : SAdeleRing F Sf × Tail F Sf => ((glueP F Sf p : _) :
          (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v) =
          fun p => p.1.2 ⟨v, h⟩ := by
        funext p
        exact (glueP_apply F Sf p v).trans (dif_pos h)
      change Continuous (fun p : SAdeleRing F Sf × Tail F Sf => ((glueP F Sf p : _) :
          (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v)
      rw [this]
      exact (continuous_apply _).comp (continuous_snd.comp continuous_fst)
    · have : (fun p : SAdeleRing F Sf × Tail F Sf => ((glueP F Sf p : _) :
          (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v) =
          fun p => ((p.2 ⟨v, h⟩ : v.adicCompletionIntegers F) : v.adicCompletion F) := by
        funext p
        exact (glueP_apply F Sf p v).trans (dif_neg h)
      change Continuous (fun p : SAdeleRing F Sf × Tail F Sf => ((glueP F Sf p : _) :
          (v : HeightOneSpectrum (𝓞 F)) → v.adicCompletion F) v)
      rw [this]
      exact continuous_subtype_val.comp ((continuous_apply _).comp continuous_snd)
  exact (continuous_fst.comp continuous_fst).prodMk
    ((RestrictedProduct.continuous_inclusion _).comp h2)


/-! ### Topology of the factors -/

omit [NumberField F] in
theorem secondCountable_infinite (w : InfinitePlace F) :
    SecondCountableTopology w.Completion :=
  (isometry_extensionEmbedding w).isEmbedding.secondCountableTopology

/-- A number field is countable: all its elements are algebraic over `ℚ`. -/
theorem countable_numberField : Countable F := by
  have h : ({x : F | IsAlgebraic ℚ x}).Countable := Algebraic.countable ℚ F
  have huniv : {x : F | IsAlgebraic ℚ x} = Set.univ :=
    Set.eq_univ_of_forall fun x => Algebra.IsAlgebraic.isAlgebraic x
  rw [huniv] at h
  exact Set.countable_univ_iff.mp h

theorem secondCountable_finite (v : HeightOneSpectrum (𝓞 F)) :
    SecondCountableTopology (v.adicCompletion F) := by
  have : Countable F := countable_numberField F
  have : TopologicalSpace.SeparableSpace (v.adicCompletion F) :=
    ⟨⟨Set.range (algebraMap F (v.adicCompletion F)), Set.countable_range _,
      v.denseRange_algebraMap F⟩⟩
  exact UniformSpace.secondCountable_of_separable _

theorem locallyCompact_finite (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v

theorem compact_integers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  RiemannMasullo.compactSpace_adicCompletionIntegers v

theorem fact_isOpen : Fact (∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

attribute [local instance] secondCountable_infinite secondCountable_finite locallyCompact_finite
  compact_integers fact_isOpen

theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  change LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
  infer_instance

theorem t2_finiteAdele : T2Space (FiniteAdeleRing (𝓞 F) F) := by
  change T2Space
    (Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
  infer_instance

attribute [local instance] locallyCompact_finiteAdele t2_finiteAdele

omit [NumberField F] in
theorem t2_infinite : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

attribute [local instance] t2_infinite secondCountable_infiniteAdele

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem t2_adele : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem borel_infinite : BorelSpace (InfiniteAdeleRing F) :=
  inferInstanceAs (BorelSpace ((v : InfinitePlace F) → v.Completion))

attribute [local instance] locallyCompact_adele t2_adele borel_infinite

theorem borel_sAdele : BorelSpace (SAdeleRing F Sf) := inferInstance

theorem secondCountable_sAdele : SecondCountableTopology (SAdeleRing F Sf) := inferInstance

theorem locallyCompact_sAdele : LocallyCompactSpace (SAdeleRing F Sf) := inferInstance

theorem t2_sAdele : T2Space (SAdeleRing F Sf) := inferInstance

attribute [local instance] borel_sAdele secondCountable_sAdele locallyCompact_sAdele t2_sAdele

/-! ### The projection and the integral subring -/

theorem measurable_proj : Measurable (proj F Sf) := by
  apply Measurable.prodMk
  · have hc : ∀ w : InfinitePlace F, Continuous (fun x : AdeleRing (𝓞 F) F => x.1 w) :=
      fun w => (continuous_apply w).comp continuous_fst
    have : Measurable (fun x : AdeleRing (𝓞 F) F => (x.1 : (w : InfinitePlace F) → w.Completion)) :=
      measurable_pi_iff.mpr fun w => (hc w).measurable
    exact this
  · have hc : ∀ v : Sf, Continuous
        (fun x : AdeleRing (𝓞 F) F => x.2 (v : HeightOneSpectrum (𝓞 F))) :=
      fun v => (RestrictedProduct.continuous_eval (v : HeightOneSpectrum (𝓞 F))).comp
        continuous_snd
    exact measurable_pi_iff.mpr fun v => (hc v).measurable

theorem isOpen_intOut : IsOpen (intOut F Sf) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun v => v ∉ Sf)
  exact h.preimage continuous_snd

theorem glue_mem_intOut (p : SAdeleRing F Sf × Tail F Sf) : glue F Sf p ∈ intOut F Sf := by
  intro v hv
  rw [glue_snd_apply, dif_neg hv]
  exact (p.2 ⟨v, hv⟩).2

theorem proj_glue (p : SAdeleRing F Sf × Tail F Sf) : proj F Sf (glue F Sf p) = p.1 := by
  refine Prod.ext rfl (funext fun v => ?_)
  change (glue F Sf p).2 (v : HeightOneSpectrum (𝓞 F)) = p.1.2 v
  rw [glue_snd_apply, dif_pos v.2]

theorem subset_image_glue (K : Set (SAdeleRing F Sf)) :
    {x | x ∈ intOut F Sf ∧ proj F Sf x ∈ K} ⊆ glue F Sf '' (K ×ˢ Set.univ) := by
  rintro x ⟨hx, hK⟩
  refine ⟨(proj F Sf x, fun v => ⟨x.2 v.1, hx v.1 v.2⟩), ⟨hK, Set.mem_univ _⟩, ?_⟩
  refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
  rw [glue_snd_apply]
  by_cases h : v ∈ Sf
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]

theorem proj_add (x y : AdeleRing (𝓞 F) F) :
    proj F Sf (x + y) = proj F Sf x + proj F Sf y := rfl

theorem add_mem_intOut_iff (a : SAdeleRing F Sf) (x : AdeleRing (𝓞 F) F) :
    glue F Sf (a, 0) + x ∈ intOut F Sf ↔ x ∈ intOut F Sf := by
  have h0 : ∀ v, v ∉ Sf → (glue F Sf (a, 0) + x).2 v = x.2 v := by
    intro v hv
    change (glue F Sf (a, 0)).2 v + x.2 v = x.2 v
    rw [glue_snd_apply, dif_neg hv]
    simp
  constructor
  · intro h v hv
    rw [← h0 v hv]
    exact h v hv
  · intro h v hv
    rw [h0 v hv]
    exact h v hv

/-! ### The projected measure -/

variable {F Sf}

/-- The image in `𝔸_{F,S}` of the restriction of a measure on `𝔸_F` to the adeles integral
outside `S`. -/
def pushMeasure (ν : Measure (AdeleRing (𝓞 F) F)) : Measure (SAdeleRing F Sf) :=
  (ν.restrict (intOut F Sf)).map (proj F Sf)

theorem pushMeasure_apply (ν : Measure (AdeleRing (𝓞 F) F)) {B : Set (SAdeleRing F Sf)}
    (hB : MeasurableSet B) :
    pushMeasure ν B = ν {x | x ∈ intOut F Sf ∧ proj F Sf x ∈ B} := by
  rw [pushMeasure, Measure.map_apply (measurable_proj F Sf) hB,
    Measure.restrict_apply' (isOpen_intOut F Sf).measurableSet]
  congr 1
  ext x
  exact and_comm

theorem pushMeasure_isAddLeftInvariant (ν : Measure (AdeleRing (𝓞 F) F))
    [ν.IsAddHaarMeasure] : (pushMeasure (Sf := Sf) ν).IsAddLeftInvariant := by
  constructor
  intro a
  ext E hE
  rw [Measure.map_apply (measurable_const_add a) hE,
    pushMeasure_apply ν (measurable_const_add a hE), pushMeasure_apply ν hE]
  have hset : {x | x ∈ intOut F Sf ∧ proj F Sf x ∈ (fun y => a + y) ⁻¹' E} =
      (fun y => glue F Sf (a, 0) + y) ⁻¹' {x | x ∈ intOut F Sf ∧ proj F Sf x ∈ E} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [add_mem_intOut_iff, proj_add, proj_glue]
  rw [hset, measure_preimage_add]

theorem pushMeasure_finite (ν : Measure (AdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] :
    IsFiniteMeasureOnCompacts (pushMeasure (Sf := Sf) ν) := by
  constructor
  intro K hK
  rw [pushMeasure_apply ν hK.isClosed.measurableSet]
  refine (measure_mono (subset_image_glue F Sf K)).trans_lt ?_
  exact ((hK.prod isCompact_univ).image (continuous_glue F Sf)).measure_lt_top

theorem pushMeasure_eq (ν : Measure (AdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, pushMeasure (Sf := Sf) ν = c • sAdditiveTamagawa F Sf := by
  have := sAdditiveTamagawa_isAddHaarMeasure F Sf
  have := pushMeasure_isAddLeftInvariant (Sf := Sf) ν
  have := pushMeasure_finite (Sf := Sf) ν
  exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩


/-! ### Fundamental domains -/

variable (F Sf)

theorem measurableSet_infFD :
    MeasurableSet (RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)) := by
  classical
  have he : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  unfold RiemannMasullo.infiniteAdeleFundamentalDomain
  exact (ZSpan.fundamentalDomain_measurableSet _).preimage he.measurable

theorem measurableSet_sFD :
    MeasurableSet (sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf) := by
  have hprod : sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf =
      (RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F)) ×ˢ
        (Set.univ.pi fun v : Sf =>
          (((v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F : Set
            ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)))) := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v _ => h2 v⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun v => h2 v (Set.mem_univ v)⟩
  rw [hprod]
  exact (measurableSet_infFD F).prod (MeasurableSet.univ_pi fun v =>
    (Valued.isOpen_valuationSubring _).measurableSet)

/-- The adelic fundamental domain `D_{F,∞} × ∏_v 𝒪_v` is the set of adeles integral outside `S`
whose `S`-component lies in `D_{F,S} = D_{F,∞} × ∏_{v ∈ S_f} 𝒪_v`. -/
theorem adeleFD_eq : RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F) =
    {x | x ∈ intOut F Sf ∧
      proj F Sf x ∈ sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf} := by
  ext a
  change (_ ∧ a ∈ RiemannMasullo.integralAdelesOutside F ∅) ↔
    ((∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → a.2 v ∈ v.adicCompletionIntegers F) ∧
      (a.1 ∈ RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F) ∧
        ∀ v : Sf, a.2 (v : HeightOneSpectrum (𝓞 F)) ∈
          (v : HeightOneSpectrum (𝓞 F)).adicCompletionIntegers F))
  simp only [RiemannMasullo.integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, true_implies]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun v _ => h2 v, h1, fun v => h2 v⟩
  · rintro ⟨hout, h1, hin⟩
    refine ⟨h1, fun v => ?_⟩
    by_cases hv : v ∈ Sf
    · exact hin ⟨v, hv⟩
    · exact hout v hv

theorem adeleFD_existsUnique (x : AdeleRing (𝓞 F) F) :
    ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈
      RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F) := by
  set D := RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F)
  have hcov := RiemannMasullo.adeleFundamentalDomain_cover F (RingOfIntegers.basis F)
  have hx : x ∈ ⋃ q : F, algebraMap F (AdeleRing (𝓞 F) F) q +ᵥ D := by
    rw [hcov]
    trivial
  obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hx
  obtain ⟨y, hy, hyx⟩ := Set.mem_vadd_set.mp hq
  have hfirst : x + algebraMap F (AdeleRing (𝓞 F) F) (-q) ∈ D := by
    have : x + algebraMap F (AdeleRing (𝓞 F) F) (-q) = y := by
      rw [← hyx, vadd_eq_add, map_neg]
      abel
    rw [this]
    exact hy
  refine ⟨-q, hfirst, ?_⟩
  intro η hη
  by_contra hne
  have hne' : η - -q ≠ 0 := sub_ne_zero.mpr hne
  have hd := RiemannMasullo.adeleFundamentalDomain_disjoint F (RingOfIntegers.basis F) (η - -q) hne'
  have hmem1 : x + algebraMap F (AdeleRing (𝓞 F) F) η ∈
      algebraMap F (AdeleRing (𝓞 F) F) (η - -q) +ᵥ D := by
    refine Set.mem_vadd_set.mpr ⟨x + algebraMap F (AdeleRing (𝓞 F) F) (-q), hfirst, ?_⟩
    rw [vadd_eq_add, map_sub]
    abel
  exact Set.disjoint_left.mp hd hmem1 hη

theorem countable_principal : Countable (AdeleRing.principalSubgroup (𝓞 F) F) := by
  have : Countable F := countable_numberField F
  have h : ((AdeleRing.principalSubgroup (𝓞 F) F : AddSubgroup (AdeleRing (𝓞 F) F)) :
      Set (AdeleRing (𝓞 F) F)).Countable := by
    have : ((AdeleRing.principalSubgroup (𝓞 F) F : AddSubgroup (AdeleRing (𝓞 F) F)) :
        Set (AdeleRing (𝓞 F) F)) = Set.range (algebraMap F (AdeleRing (𝓞 F) F)) := by
      ext a
      exact RingHom.mem_range
    rw [this]
    exact Set.countable_range _
  exact h.to_subtype

theorem measurableConstVAdd_principal :
    MeasurableConstVAdd (AdeleRing.principalSubgroup (𝓞 F) F) (AdeleRing (𝓞 F) F) := by
  refine ⟨fun c => ?_⟩
  change Measurable fun x : AdeleRing (𝓞 F) F => (c : AdeleRing (𝓞 F) F) + x
  exact (continuous_const_add (c : AdeleRing (𝓞 F) F)).measurable

theorem isAddFundamentalDomain_principal (ν : Measure (AdeleRing (𝓞 F) F))
    {D : Set (AdeleRing (𝓞 F) F)} (hD : MeasurableSet D)
    (h : ∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) :
    IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) D ν := by
  refine IsAddFundamentalDomain.mk' hD.nullMeasurableSet fun x => ?_
  obtain ⟨ξ, hξ, huniq⟩ := h x
  refine ⟨⟨algebraMap F _ ξ, RingHom.mem_range_self _ ξ⟩, ?_, ?_⟩
  · change algebraMap F _ ξ + x ∈ D
    rwa [add_comm]
  · rintro ⟨g, hg⟩ hgx
    obtain ⟨η, rfl⟩ := RingHom.mem_range.mp hg
    have hgx' : x + algebraMap F _ η ∈ D := by
      change algebraMap F _ η + x ∈ D at hgx
      rwa [add_comm] at hgx
    have := huniq η hgx'
    subst this
    rfl

/-- The diagonal image of the `S`-integers is a countable group. -/
theorem countable_sIntegerLattice : Countable (sIntegerLattice Sf) := by
  have : Countable F := countable_numberField F
  have h : (sIntegerLattice Sf : Set (SAdeleRing F Sf)).Countable := by
    rw [sIntegerLattice, AddSubgroup.coe_map]
    exact (Set.to_countable _).image _
  exact h.to_subtype

theorem existsUnique_vadd_mem (x : SAdeleRing F Sf) :
    ∃! g : sIntegerLattice Sf, g +ᵥ x ∈ sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf := by
  obtain ⟨ξ, ⟨hξ, hx⟩, huniq⟩ :=
    sIntegerFundamentalDomain_existsUnique F (RingOfIntegers.basis F) Sf x
  have hmem : ∀ η : F, η ∈ SIntegers (F := F) Sf → sDiagonal Sf η ∈ sIntegerLattice Sf :=
    fun η hη => ⟨η, hη, rfl⟩
  refine ⟨⟨-sDiagonal Sf ξ, neg_mem (hmem ξ hξ)⟩, ?_, ?_⟩
  · change -sDiagonal Sf ξ + x ∈ sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf
    rw [neg_add_eq_sub]
    exact hx
  · rintro ⟨g, η, hη, rfl⟩ hgx
    have hgx' : sDiagonal Sf η + x ∈ sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf :=
      hgx
    have h1 : -η = ξ := by
      refine huniq (-η) ⟨neg_mem hη, ?_⟩
      rw [map_neg, sub_neg_eq_add, add_comm]
      exact hgx'
    apply Subtype.ext
    change sDiagonal Sf η = -sDiagonal Sf ξ
    rw [← h1, map_neg, neg_neg]

/-- `ν_S(D_{F,S}) = √|d_F| ∏_{v ∈ S_f} N(𝔡_v)^{-1/2}`. -/
theorem sAdditiveTamagawa_sFD :
    sAdditiveTamagawa F Sf (sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf) =
      ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) *
        ∏ v ∈ Sf, (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
          multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  have hhaar : (sAdditiveTamagawa F Sf).IsAddHaarMeasure := sAdditiveTamagawa_isAddHaarMeasure F Sf
  have hm1 : MeasurableAdd (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableAdd ((w : InfinitePlace F) → w.Completion))
  have hmeasadd : MeasurableConstVAdd (sIntegerLattice Sf) (SAdeleRing F Sf) := by
    refine ⟨fun c => ?_⟩
    change Measurable fun x : SAdeleRing F Sf =>
      ((c : SAdeleRing F Sf).1 + x.1, (c : SAdeleRing F Sf).2 + x.2)
    exact ((measurable_const_add _).comp measurable_fst).prodMk
      ((measurable_const_add _).comp measurable_snd)
  have hD0 : IsAddFundamentalDomain (sIntegerLattice Sf)
      (sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf) (sAdditiveTamagawa F Sf) :=
    IsAddFundamentalDomain.mk' (measurableSet_sFD F Sf).nullMeasurableSet
      (existsUnique_vadd_mem F Sf)
  exact sIntegerLattice_covolume_sAdditiveTamagawa F Sf _ hD0


/-! ### The main computation -/

theorem main (B : Set (SAdeleRing F Sf)) (hB : MeasurableSet B) :
    tamagawaAdelic (F := F)
        {x : AdeleRing (𝓞 F) F |
          (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F) ∧
          ((x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) : SAdeleRing F Sf) ∈ B} =
      sAdditiveTamagawa F Sf B *
        ((ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
          ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) := by
  set D₀ := RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F) with hD₀def
  set B₀ := sIntegerFundamentalDomain F (RingOfIntegers.basis F) Sf with hB₀def
  have hB₀ : MeasurableSet B₀ := measurableSet_sFD F Sf
  have hD₀ : MeasurableSet D₀ := by
    rw [hD₀def, adeleFD_eq F Sf]
    exact (isOpen_intOut F Sf).measurableSet.inter (measurable_proj F Sf hB₀)
  have hfd := adeleFD_existsUnique F
  have hcount := countable_principal F
  have hmc := measurableConstVAdd_principal F
  -- a Haar measure for which the fundamental domain `D₀` has mass one
  have hex : ∃ ν : Measure (AdeleRing (𝓞 F) F), ν.IsAddHaarMeasure ∧
      ∃ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D ∧
        (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) ∧
        ν D = 1 := by
    let ν₁ : Measure (AdeleRing (𝓞 F) F) := Measure.addHaar
    have h0 : ν₁ D₀ ≠ 0 :=
      (isAddFundamentalDomain_principal F ν₁ hD₀ hfd).measure_ne_zero (NeZero.ne ν₁)
    have htop : ν₁ D₀ ≠ ⊤ :=
      ((measure_mono subset_closure).trans_lt
        (RiemannMasullo.adeleFundamentalDomain_precompact F
          (RingOfIntegers.basis F)).measure_lt_top).ne
    refine ⟨(ν₁ D₀)⁻¹ • ν₁, Measure.IsAddHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr h0), D₀, hD₀, hfd, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]
  have hν : tamagawaAdelic (F := F) = hex.choose := by
    rw [tamagawaAdelic, dif_pos hex]
  obtain ⟨hH, D, hDm, hDfd, hD1⟩ := hex.choose_spec
  rw [hν]
  set ν := hex.choose
  have hνD₀ : ν D₀ = 1 := by
    rw [← hD1]
    exact (isAddFundamentalDomain_principal F ν hD₀ hfd).measure_eq
      (isAddFundamentalDomain_principal F ν hDm hDfd)
  obtain ⟨c, hc⟩ := pushMeasure_eq (Sf := Sf) ν
  have happly : ∀ E : Set (SAdeleRing F Sf), MeasurableSet E →
      ν {x | x ∈ intOut F Sf ∧ proj F Sf x ∈ E} = c * sAdditiveTamagawa F Sf E := by
    intro E hE
    rw [← pushMeasure_apply ν hE, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have h1 : (c : ℝ≥0∞) * sAdditiveTamagawa F Sf B₀ = 1 := by
    rw [← happly B₀ hB₀, ← adeleFD_eq F Sf]
    exact hνD₀
  rw [sAdditiveTamagawa_sFD F Sf] at h1
  set a := ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) with ha
  set bv := fun v : HeightOneSpectrum (𝓞 F) => ENNReal.ofReal (Real.sqrt
    ((Ideal.absNorm v.asIdeal : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) with hbv
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr
    (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F))))).ne'
  have hb0 : ∀ v : HeightOneSpectrum (𝓞 F), bv v ≠ 0 := by
    intro v
    have hN : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
      Nat.cast_pos.mpr (HeightOneSpectrum.one_lt_absNorm v).pos
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (pow_pos hN _))).ne'
  have h1' : (c : ℝ≥0∞) * (a * ∏ v ∈ Sf, (bv v)⁻¹) = 1 := h1
  have hK : (a * ∏ v ∈ Sf, (bv v)⁻¹) * (a⁻¹ * ∏ v ∈ Sf, bv v) = 1 := by
    rw [mul_mul_mul_comm, ENNReal.mul_inv_cancel ha0 ENNReal.ofReal_ne_top,
      ← Finset.prod_mul_distrib,
      Finset.prod_eq_one fun v _ => ENNReal.inv_mul_cancel (hb0 v) ENNReal.ofReal_ne_top, one_mul]
  have hcK : (c : ℝ≥0∞) = a⁻¹ * ∏ v ∈ Sf, bv v := by
    calc (c : ℝ≥0∞) = c * ((a * ∏ v ∈ Sf, (bv v)⁻¹) * (a⁻¹ * ∏ v ∈ Sf, bv v)) := by
          rw [hK, mul_one]
      _ = (c * (a * ∏ v ∈ Sf, (bv v)⁻¹)) * (a⁻¹ * ∏ v ∈ Sf, bv v) := by rw [← mul_assoc]
      _ = a⁻¹ * ∏ v ∈ Sf, bv v := by rw [h1', one_mul]
  change ν {x | x ∈ intOut F Sf ∧ proj F Sf x ∈ B} = _
  rw [happly B hB, hcK, mul_comm]

end

end Sol_MasulloGRH_tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa

open MasulloGRH Sol_MasulloGRH_tamagawaAdelic_integralOutside_eq_sAdditiveTamagawa in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Set (SAdeleRing F Sf)) (hB : MeasurableSet B) :
    tamagawaAdelic (F := F)
        {x : AdeleRing (𝓞 F) F |
          (∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → x.2 v ∈ v.adicCompletionIntegers F) ∧
          ((x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F))) : SAdeleRing F Sf) ∈ B} =
      sAdditiveTamagawa F Sf B *
        ((ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
          ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) :=
  main F Sf B hB
