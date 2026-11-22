-- Prove2me | solution 1 for MasulloGRH.tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:23:00.802314+00:00
-- url     : https://prove2.me/submissions/5da85455-b9fc-4845-a7f5-2b71a6de3672

import Mathlib
import Definitions.Def_MasulloGRH_AdelicTheta
import Definitions.Def_RiemannMasullo_AdeleFundamentalDomain
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_precompact
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_cover
import Theorems.Thm_RiemannMasullo_adeleFundamentalDomain_disjoint

open MeasureTheory NumberField IsDedekindDomain

set_option autoImplicit false

/-!
# The additive Tamagawa measure is a Haar measure giving every fundamental domain mass one

* `D₀ = D_{F,∞} × ∏_v 𝒪_v` is a measurable strict fundamental domain of `F` in `𝔸_F`
  (platform theorems `RiemannMasullo.adeleFundamentalDomain_cover` and `_disjoint`) with
  compact closure (`RiemannMasullo.adeleFundamentalDomain_precompact`).
* `𝔸_F` is locally compact (restricted product of locally compact fields with respect to
  compact open subrings), so it carries a Haar measure `μ`; `0 < μ(D₀) < ∞`, and
  `μ(D₀)⁻¹ • μ` is a Haar measure giving `D₀` mass one. Hence `tamagawaAdelic` is the chosen
  Haar measure of its definition.
* All measurable strict fundamental domains of the countable group `F` have the same measure
  for a translation invariant measure (`IsAddFundamentalDomain.measure_eq`).
-/

namespace Sol_MasulloGRH_tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain

open MasulloGRH InfinitePlace.Completion
open scoped RestrictedProduct Pointwise

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

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

theorem locallyCompact_finite (v : HeightOneSpectrum (𝓞 F)) :
    LocallyCompactSpace (v.adicCompletion F) :=
  RiemannMasullo.locallyCompactSpace_adicCompletion v

theorem compact_integers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  RiemannMasullo.compactSpace_adicCompletionIntegers v

theorem fact_isOpen : Fact (∀ v : HeightOneSpectrum (𝓞 F),
    IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

attribute [local instance] secondCountable_infinite locallyCompact_finite
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

attribute [local instance] t2_infinite

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem t2_adele : T2Space (AdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

attribute [local instance] locallyCompact_adele t2_adele

/-! ### The fundamental domain `D_{F,∞} × ∏_v 𝒪_v` -/

theorem continuous_mixed :
    Continuous (fun x : AdeleRing (𝓞 F) F => InfiniteAdeleRing.ringEquiv_mixedSpace F x.1) := by
  classical
  have he : Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
    change Continuous (fun x : InfiniteAdeleRing F ↦ InfiniteAdeleRing.ringEquiv_mixedSpace F x)
    simp only [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (continuous_pi fun v ↦ (isometryEquivRealOfIsReal v.2).continuous.comp
      (continuous_apply v.1)).prodMk
      (continuous_pi fun v ↦ (isometryEquivComplexOfIsComplex v.2).continuous.comp
        (continuous_apply v.1))
  exact he.comp continuous_fst

theorem measurableSet_infFD :
    MeasurableSet (Prod.fst ⁻¹'
      RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F) :
        Set (AdeleRing (𝓞 F) F)) := by
  classical
  unfold RiemannMasullo.infiniteAdeleFundamentalDomain
  exact (continuous_mixed F).measurable (ZSpan.fundamentalDomain_measurableSet _)

theorem isOpen_integral :
    IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
      x.2 v ∈ v.adicCompletionIntegers F} := by
  have h := RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _)
  exact h.preimage continuous_snd

theorem adeleFD_eq : RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F) =
    Prod.fst ⁻¹' RiemannMasullo.infiniteAdeleFundamentalDomain F (RingOfIntegers.basis F) ∩
      {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F),
        x.2 v ∈ v.adicCompletionIntegers F} := by
  ext a
  change (_ ∧ a ∈ RiemannMasullo.integralAdelesOutside F ∅) ↔ _
  simp only [RiemannMasullo.integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, true_implies]
  rfl

theorem measurableSet_adeleFD :
    MeasurableSet (RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F)) := by
  rw [adeleFD_eq F]
  exact (measurableSet_infFD F).inter (isOpen_integral F).measurableSet

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

/-- A Haar measure of `𝔸_F` for which some measurable strict fundamental domain of `F` has
mass one. -/
theorem exists_haar :
    ∃ ν : Measure (AdeleRing (𝓞 F) F), ν.IsAddHaarMeasure ∧
      ∃ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D ∧
        (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) ∧
        ν D = 1 := by
  set D₀ := RiemannMasullo.adeleFundamentalDomain F (RingOfIntegers.basis F) with hD₀def
  have hD₀ : MeasurableSet D₀ := measurableSet_adeleFD F
  have hfd := adeleFD_existsUnique F
  have hcount := countable_principal F
  have hmc := measurableConstVAdd_principal F
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

theorem main :
    (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)).IsAddHaarMeasure ∧
    ∀ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D →
      (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) →
      (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)) D = 1 := by
  have hex := exists_haar F
  have hν : tamagawaAdelic (F := F) = hex.choose := by
    rw [tamagawaAdelic, dif_pos hex]
  obtain ⟨hH, D₁, hD₁m, hD₁fd, hD₁⟩ := hex.choose_spec
  rw [hν]
  refine ⟨hH, fun D hDm hDfd => ?_⟩
  have hcount := countable_principal F
  have hmc := measurableConstVAdd_principal F
  exact ((isAddFundamentalDomain_principal F _ hDm hDfd).measure_eq
    (isAddFundamentalDomain_principal F _ hD₁m hD₁fd)).trans hD₁

end

end Sol_MasulloGRH_tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain

open MasulloGRH Sol_MasulloGRH_tamagawaAdelic_isAddHaarMeasure_and_fundamentalDomain in
theorem solution
    (F : Type*) [Field F] [NumberField F] :
    (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)).IsAddHaarMeasure ∧
    ∀ D : Set (AdeleRing (𝓞 F) F), MeasurableSet D →
      (∀ x : AdeleRing (𝓞 F) F, ∃! ξ : F, x + algebraMap F (AdeleRing (𝓞 F) F) ξ ∈ D) →
      (tamagawaAdelic : Measure (AdeleRing (𝓞 F) F)) D = 1 :=
  main F
