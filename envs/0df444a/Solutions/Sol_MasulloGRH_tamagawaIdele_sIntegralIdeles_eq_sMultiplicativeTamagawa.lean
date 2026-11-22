-- Prove2me | solution 1 for MasulloGRH.tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:17:50.821417+00:00
-- url     : https://prove2.me/submissions/059a6056-aaf4-4868-91a6-75dfa050cd41

import Mathlib
import Definitions.Def_MasulloGRH_ZetaIntegrals
import Definitions.Def_MasulloGRH_SLocalTamagawaMeasures
import Definitions.Def_MasulloGRH_TateArchimedeanDomain
import Definitions.Def_MasulloGRH_TateIdeleDomain
import Theorems.Thm_RiemannMasullo_locallyCompactSpace_adicCompletion
import Theorems.Thm_RiemannMasullo_compactSpace_adicCompletionIntegers
import Theorems.Thm_RiemannMasullo_finiteLocalAdditiveTamagawaMeasure_isAddHaar
import Theorems.Thm_MasulloGRH_infiniteLocalMulTamagawa_isHaarMeasure
import Theorems.Thm_MasulloGRH_finiteLocalMulTamagawa_isHaarMeasure_and_units
import Theorems.Thm_MasulloGRH_sMultiplicativeTamagawa_isHaarMeasure_and_rectangle
import Theorems.Thm_MasulloGRH_tamagawa_measures_wellDefined
import Theorems.Thm_MasulloGRH_tateArchimedeanDomain_torsion_translates
import Theorems.Thm_MasulloGRH_tateArchimedeanDomain_existsUnique_unit_mul
import Theorems.Thm_MasulloGRH_tateIdeleDomain_existsUnique_principal_mul
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

/-!
# The idelic Tamagawa measure is the restricted product of the local ones

Let `μ` be the Tamagawa measure of `GL₁(𝔸_F)`, `U_S = GL₁(𝔸_{F,S}) × ∏_{v ∉ S} 𝒪_vˣ` and
`p : U_S → GL₁(𝔸_{F,S})` the projection.

* Step A (`stepA`): `B ↦ μ(U_S ∩ p⁻¹ B)` is a left invariant measure on `GL₁(𝔸_{F,S})`, finite on
  compact sets (the fibres of `p` are the compact group `∏_{v ∉ S} 𝒪_vˣ`), hence `c_S • μ_S`.
* Archimedean volume (`arch_strip`, `muInf_omega`): the archimedean regulator strip has
  `⊗_w μ_w`-measure `2^{r₁} (2π)^{r₂} R_F`; it is the disjoint union of the `w_F` torsion
  translates of the set `Ω₀` built from Tate's archimedean domain `E₀`
  (platform theorems `MasulloGRH.tateArchimedeanDomain_torsion_translates` and
  `MasulloGRH.tateArchimedeanDomain_existsUnique_unit_mul`).
* Global count (`count`): with norm-one ideles `r_c` of ideal class `c`, the set
  `D = ⋃_c r_c (Ω₀ × ∏_v 𝒪_vˣ)` maps bijectively onto the classes of norm in `[1, e)`
  (platform theorem `MasulloGRH.tateIdeleDomain_existsUnique_principal_mul`), so
  `Res ζ_F = μ̄ = μ(D) = h_F · μ(Ω₀ × ∏_v 𝒪_vˣ)`.
* Solving for `c_S` with `μ_v(𝒪_vˣ) = N(𝔡_v)^{-1/2}` gives `c_S = |d_F|^{-1/2} ∏_{v ∈ S_f} N(𝔡_v)^{1/2}`.

The archimedean volume computation follows the proof in the open formalization
mccorvie/riemann-masullo.
-/


-- ===== part A =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH InfinitePlace.Completion
open scoped RestrictedProduct Pointwise

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))

/-! ### Gluing -/

/-- The product of the local integers at the finite places outside `S`. -/
abbrev Tail : Type _ :=
  (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf}) → v.1.adicCompletionIntegers F

open Classical in
/-- Gluing an `S`-adele and a family of local integers outside `S` (restricted product with
respect to the principal filter of the complement of `S`). -/
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

/-! ### Topology -/

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

attribute [local instance] secondCountable_infinite secondCountable_finite locallyCompact_finite
  compact_integers

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

omit [NumberField F] in
theorem t2_infinite : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

attribute [local instance] secondCountable_infiniteAdele t2_infinite

theorem secondCountable_sIdele : SecondCountableTopology (SIdeleGroup F Sf) := by
  have : SecondCountableTopology (SAdeleRing F Sf)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := SAdeleRing F Sf)).symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompact_sIdele : LocallyCompactSpace (SIdeleGroup F Sf) := inferInstance

attribute [local instance] secondCountable_sIdele locallyCompact_sIdele

/-! ### The projection to the `S`-ideles and the gluing of units -/

/-- The restriction `𝔸_F → 𝔸_{F,S}` as a monoid homomorphism. -/
def projHom : AdeleRing (𝓞 F) F →* SAdeleRing F Sf where
  toFun x := (x.1, fun v : Sf => x.2 (v : HeightOneSpectrum (𝓞 F)))
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_projHom : Continuous (projHom F Sf) :=
  continuous_fst.prodMk (continuous_pi fun v =>
    (RestrictedProduct.continuous_eval (v : HeightOneSpectrum (𝓞 F))).comp continuous_snd)

/-- The projection `GL₁(𝔸_F) → GL₁(𝔸_{F,S})`. -/
def pU : IdeleGroup F →* SIdeleGroup F Sf := Units.map (projHom F Sf)

theorem continuous_pU : Continuous (pU F Sf) := Units.continuous_map (continuous_projHom F Sf)

theorem measurable_pU : Measurable (pU F Sf) := (continuous_pU F Sf).measurable

/-- The local units outside `S`. -/
abbrev TailU : Type _ :=
  (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf}) → (v.1.adicCompletionIntegers F)ˣ

theorem glue_mul (a b : SAdeleRing F Sf) (s t : Tail F Sf) :
    glue F Sf (a, s) * glue F Sf (b, t) = glue F Sf (a * b, s * t) := by
  refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
  change (glue F Sf (a, s)).2 v * (glue F Sf (b, t)).2 v = (glue F Sf (a * b, s * t)).2 v
  rw [glue_snd_apply, glue_snd_apply, glue_snd_apply]
  by_cases h : v ∈ Sf
  · simp only [dif_pos h]
    rfl
  · simp only [dif_neg h]
    rfl

theorem glue_one : glue F Sf (1, 1) = 1 := by
  refine Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_)
  change (glue F Sf (1, 1)).2 v = 1
  rw [glue_snd_apply]
  by_cases h : v ∈ Sf
  · simp only [dif_pos h]
    rfl
  · simp only [dif_neg h]
    rfl

/-- Gluing an `S`-idele and local units outside `S` into an idele. -/
def glueU (p : SIdeleGroup F Sf × TailU F Sf) : IdeleGroup F where
  val := glue F Sf ((p.1 : SAdeleRing F Sf), fun v => ((p.2 v : (v.1.adicCompletionIntegers F)ˣ) :
    v.1.adicCompletionIntegers F))
  inv := glue F Sf (((p.1⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf),
    fun v => (((p.2 v)⁻¹ : (v.1.adicCompletionIntegers F)ˣ) : v.1.adicCompletionIntegers F))
  val_inv := by
    rw [glue_mul, ← glue_one F Sf]
    congr 2
    · exact p.1.mul_inv
    · funext v
      exact (p.2 v).mul_inv
  inv_val := by
    rw [glue_mul, ← glue_one F Sf]
    congr 2
    · exact p.1.inv_mul
    · funext v
      exact (p.2 v).inv_mul

theorem continuous_glueU : Continuous (glueU F Sf) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · change Continuous fun p : SIdeleGroup F Sf × TailU F Sf =>
      glue F Sf ((p.1 : SAdeleRing F Sf), fun v => ((p.2 v : (v.1.adicCompletionIntegers F)ˣ) :
        v.1.adicCompletionIntegers F))
    refine (continuous_glue F Sf).comp ((Units.continuous_val.comp continuous_fst).prodMk ?_)
    exact continuous_pi fun v => Units.continuous_val.comp ((continuous_apply v).comp continuous_snd)
  · change Continuous fun p : SIdeleGroup F Sf × TailU F Sf =>
      glue F Sf (((p.1⁻¹ : SIdeleGroup F Sf) : SAdeleRing F Sf),
        fun v => (((p.2 v)⁻¹ : (v.1.adicCompletionIntegers F)ˣ) : v.1.adicCompletionIntegers F))
    refine (continuous_glue F Sf).comp
      ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).prodMk ?_)
    exact continuous_pi fun v => Units.continuous_val.comp
      (continuous_inv.comp ((continuous_apply v).comp continuous_snd))

theorem valued_unit (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletionIntegers F)ˣ) :
    Valued.v (((u : v.adicCompletionIntegers F) : v.adicCompletion F)) = 1 := by
  have h1 : Valued.v (((u : v.adicCompletionIntegers F) : v.adicCompletion F)) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (u : v.adicCompletionIntegers F).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
      v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp
      ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
  have h3 : Valued.v (((u : v.adicCompletionIntegers F) : v.adicCompletion F)) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
        v.adicCompletion F) = 1 := by
    rw [← map_mul]
    have : (((u : v.adicCompletionIntegers F) : v.adicCompletion F)) *
        (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
          v.adicCompletion F) = 1 := by
      exact congrArg (Subtype.val : v.adicCompletionIntegers F → v.adicCompletion F) u.mul_inv
    rw [this, map_one]
  by_contra hne
  have hlt : Valued.v (((u : v.adicCompletionIntegers F) : v.adicCompletion F)) < 1 :=
    lt_of_le_of_ne h1 hne
  have : Valued.v (((u : v.adicCompletionIntegers F) : v.adicCompletion F)) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :
        v.adicCompletion F) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at this
  exact lt_irrefl _ this

theorem glueU_mem (p : SIdeleGroup F Sf × TailU F Sf) : glueU F Sf p ∈ sIntegralIdeles Sf := by
  intro v hv
  change Valued.v ((glue F Sf _).2 v) = 1
  rw [glue_snd_apply, dif_neg hv]
  exact valued_unit F v (p.2 ⟨v, hv⟩)

theorem pU_glueU (p : SIdeleGroup F Sf × TailU F Sf) : pU F Sf (glueU F Sf p) = p.1 := by
  refine Units.ext (Prod.ext rfl (funext fun v => ?_))
  change (glue F Sf _).2 (v : HeightOneSpectrum (𝓞 F)) = (p.1 : SAdeleRing F Sf).2 v
  rw [glue_snd_apply, dif_pos v.2]

theorem fin_inv_mul (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v * (g : AdeleRing (𝓞 F) F).2 v = 1 := by
  have : ((g⁻¹ * g : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    rw [inv_mul_cancel]; rfl
  exact this

theorem subset_image_glueU (K : Set (SIdeleGroup F Sf)) :
    {g | g ∈ sIntegralIdeles Sf ∧ pU F Sf g ∈ K} ⊆ glueU F Sf '' (K ×ˢ Set.univ) := by
  rintro g ⟨hg, hK⟩
  have hmem : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf},
      (g : AdeleRing (𝓞 F) F).2 v.1 ∈ v.1.adicCompletionIntegers F := fun v =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hg v.1 v.2).le
  have hmem' : ∀ v : {v : HeightOneSpectrum (𝓞 F) // v ∉ Sf},
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v.1 ∈ v.1.adicCompletionIntegers F := by
    intro v
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (le_of_eq ?_)
    have h := congrArg Valued.v (fin_inv_mul F g v.1)
    rw [map_mul, map_one, hg v.1 v.2, mul_one] at h
    exact h
  let t : TailU F Sf := fun v =>
    { val := ⟨(g : AdeleRing (𝓞 F) F).2 v.1, hmem v⟩
      inv := ⟨((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v.1, hmem' v⟩
      val_inv := by
        apply Subtype.ext
        have : ((g * g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v.1 = 1 := by
          rw [mul_inv_cancel]; rfl
        exact this
      inv_val := by
        apply Subtype.ext
        exact fin_inv_mul F g v.1 }
  refine ⟨(pU F Sf g, t), ⟨hK, Set.mem_univ _⟩, ?_⟩
  refine Units.ext (Prod.ext rfl (FiniteAdeleRing.ext _ fun v => ?_))
  change (glue F Sf _).2 v = (g : AdeleRing (𝓞 F) F).2 v
  rw [glue_snd_apply]
  by_cases h : v ∈ Sf
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]

theorem mul_mem_iff (x : SIdeleGroup F Sf) (g : IdeleGroup F) :
    glueU F Sf (x, 1) * g ∈ sIntegralIdeles Sf ↔ g ∈ sIntegralIdeles Sf := by
  have h0 : ∀ v, v ∉ Sf → Valued.v (((glueU F Sf (x, 1) * g : IdeleGroup F) :
      AdeleRing (𝓞 F) F).2 v) = Valued.v ((g : AdeleRing (𝓞 F) F).2 v) := by
    intro v hv
    have h1 := glueU_mem F Sf (x, 1) v hv
    change Valued.v ((glueU F Sf (x, 1) : AdeleRing (𝓞 F) F).2 v * (g : AdeleRing (𝓞 F) F).2 v) = _
    rw [map_mul, h1, one_mul]
  constructor
  · intro h v hv
    rw [← h0 v hv]
    exact h v hv
  · intro h v hv
    rw [h0 v hv]
    exact h v hv

/-! ### The projected measure -/

variable {F Sf}

/-- The image in `GL₁(𝔸_{F,S})` of the restriction of a measure on `GL₁(𝔸_F)` to the ideles that
are units outside `S`. -/
def pushMeasure (μ : Measure (IdeleGroup F)) : Measure (SIdeleGroup F Sf) :=
  (μ.restrict (sIntegralIdeles Sf)).map (pU F Sf)

theorem pushMeasure_apply (μ : Measure (IdeleGroup F)) {B : Set (SIdeleGroup F Sf)}
    (hB : MeasurableSet B) :
    pushMeasure μ B = μ {g | g ∈ sIntegralIdeles Sf ∧ pU F Sf g ∈ B} := by
  rw [pushMeasure, Measure.map_apply (measurable_pU F Sf) hB,
    Measure.restrict_apply (measurable_pU F Sf hB)]
  congr 1
  ext x
  exact and_comm

theorem pushMeasure_isMulLeftInvariant (μ : Measure (IdeleGroup F)) [μ.IsHaarMeasure] :
    (pushMeasure (Sf := Sf) μ).IsMulLeftInvariant := by
  constructor
  intro a
  ext E hE
  rw [Measure.map_apply (measurable_const_mul a) hE,
    pushMeasure_apply μ (measurable_const_mul a hE), pushMeasure_apply μ hE]
  have hset : {g | g ∈ sIntegralIdeles Sf ∧ pU F Sf g ∈ (fun y => a * y) ⁻¹' E} =
      (fun y => glueU F Sf (a, 1) * y) ⁻¹' {g | g ∈ sIntegralIdeles Sf ∧ pU F Sf g ∈ E} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [mul_mem_iff, map_mul, pU_glueU]
  rw [hset, measure_preimage_mul]

theorem pushMeasure_finite (μ : Measure (IdeleGroup F)) [μ.IsHaarMeasure] :
    IsFiniteMeasureOnCompacts (pushMeasure (Sf := Sf) μ) := by
  constructor
  intro K hK
  rw [pushMeasure_apply μ hK.isClosed.measurableSet]
  refine (measure_mono (subset_image_glueU F Sf K)).trans_lt ?_
  exact ((hK.prod isCompact_univ).image (continuous_glueU F Sf)).measure_lt_top

theorem pushMeasure_eq (μ : Measure (IdeleGroup F)) [μ.IsHaarMeasure] :
    ∃ c : ℝ≥0, pushMeasure (Sf := Sf) μ = c • sMultiplicativeTamagawa F Sf := by
  have := (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).1
  have := pushMeasure_isMulLeftInvariant (Sf := Sf) μ
  have := pushMeasure_finite (Sf := Sf) μ
  exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ _⟩

variable (F Sf)

/-- The set of the target, in terms of the projection. -/
theorem targetSet_eq (B : Set (SIdeleGroup F Sf)) :
    {g : IdeleGroup F | g ∈ sIntegralIdeles Sf ∧
          ∃ b ∈ B, (b : SAdeleRing F Sf) =
            ((g : AdeleRing (𝓞 F) F).1,
              fun v : Sf => (g : AdeleRing (𝓞 F) F).2 (v : HeightOneSpectrum (𝓞 F)))} =
      {g | g ∈ sIntegralIdeles Sf ∧ pU F Sf g ∈ B} := by
  ext g
  simp only [Set.mem_ofPred_eq]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, rfl⟩⟩
  rintro ⟨b, hb, hbg⟩
  have : b = pU F Sf g := Units.ext hbg
  exact this ▸ hb

/-- Step A: the restriction of the Tamagawa measure to the ideles that are units outside `S` is a
constant multiple of `μ_S`. -/
theorem stepA : ∃ c : ℝ≥0, ∀ B : Set (SIdeleGroup F Sf), MeasurableSet B →
    tamagawaIdele F {g : IdeleGroup F | g ∈ sIntegralIdeles Sf ∧
          ∃ b ∈ B, (b : SAdeleRing F Sf) =
            ((g : AdeleRing (𝓞 F) F).1,
              fun v : Sf => (g : AdeleRing (𝓞 F) F).2 (v : HeightOneSpectrum (𝓞 F)))} =
      (c : ℝ≥0∞) * sMultiplicativeTamagawa F Sf B := by
  have hH : (tamagawaIdele F).IsHaarMeasure := (tamagawa_measures_wellDefined F).2.1.1
  obtain ⟨c, hc⟩ := pushMeasure_eq (Sf := Sf) (tamagawaIdele F)
  refine ⟨c, fun B hB => ?_⟩
  rw [targetSet_eq, ← pushMeasure_apply _ hB, hc]
  rfl

end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part B =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH InfinitePlace.Completion Set RiemannMasullo
open scoped Classical

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

set_option linter.unusedSectionVars false

local notation "archRegulatorMass(" F ")" =>
  ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Units.regulator F)

/-- The archimedean regulator strip: total normalized log norm in `[0, 1)` and the log
coordinates away from `w₀` in the regulator parallelotope. -/
def archStrip : Set ((w : InfinitePlace F) → w.Completionˣ) :=
  {a | (∑ w, (w.mult : ℝ) * Real.log ‖(a w).val‖) ∈ Ico 0 1 ∧
    (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀ (K := F)} ↦
      (w.val.mult : ℝ) * Real.log ‖(a w.val).val‖) ∈
      regulatorParallelotope F (Units.basisModTorsion F)}

theorem archStrip_measurableSet : MeasurableSet (archStrip F) := by
  have hlog (w : InfinitePlace F) : Measurable
      (fun a : (w : InfinitePlace F) → w.Completionˣ ↦ (w.mult : ℝ) * Real.log ‖(a w).val‖) :=
    measurable_const.mul
      (Real.measurable_log.comp ((continuous_norm.comp Units.continuous_val).measurable.comp
        (measurable_pi_apply w)))
  have hP : MeasurableSet (regulatorParallelotope F (Units.basisModTorsion F)) :=
    ZSpan.fundamentalDomain_measurableSet _
  exact (measurableSet_Ico.preimage (Finset.measurable_sum Finset.univ fun w _ ↦ hlog w)).inter
    (hP.preimage (measurable_pi_lambda _ fun w ↦ hlog w.val))

/-- The integral of `dt / t` over `(e^a, e^b]` is `b - a`. -/
theorem arch_Ioc_exp {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ t in Ioc (Real.exp a) (Real.exp b), ENNReal.ofReal t⁻¹ = ENNReal.ofReal (b - a) := by
  have hpos {t : ℝ} (ht : t ∈ Ioc (Real.exp a) (Real.exp b)) : 0 < t :=
    (Real.exp_pos a).trans ht.1
  have hint : IntegrableOn (fun t : ℝ ↦ t⁻¹) (Ioc (Real.exp a) (Real.exp b)) :=
    (ContinuousOn.integrableOn_Icc (f := fun t : ℝ ↦ t⁻¹) (continuousOn_inv₀.mono
      fun t ht ↦ ((Real.exp_pos a).trans_le ht.1).ne')).mono_set Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
        fun _ ht ↦ inv_nonneg.mpr (hpos ht).le)),
    ← intervalIntegral.integral_of_le (Real.exp_le_exp.mpr hab),
    integral_inv_of_pos (Real.exp_pos a) (Real.exp_pos b), ← Real.exp_sub, Real.log_exp]

/-- On the real line, `dt / |t|` gives the band `log |t| ∈ (a, b]` mass `2 (b - a)`. -/
theorem arch_lintegral_real {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ t in {t : ℝ | t ≠ 0 ∧ Real.log ‖t‖ ∈ Ioc a b}, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ =
      2 * ENNReal.ofReal (b - a) := by
  set A := Ioc (Real.exp a) (Real.exp b)
  have hS : {t : ℝ | t ≠ 0 ∧ Real.log ‖t‖ ∈ Ioc a b} = A ∪ Neg.neg ⁻¹' A := by
    ext t
    simp only [mem_ofPred_eq, mem_union, mem_preimage, A, mem_Ioc, Real.norm_eq_abs]
    constructor
    · rintro ⟨ht, h1, h2⟩
      have h1' := Real.exp_lt_exp.mpr h1
      have h2' := Real.exp_le_exp.mpr h2
      rw [Real.exp_log (abs_pos.mpr ht)] at h1' h2'
      rcases lt_or_gt_of_ne ht with h | h
      · right; rw [abs_of_neg h] at h1' h2'; exact ⟨h1', h2'⟩
      · left; rw [abs_of_pos h] at h1' h2'; exact ⟨h1', h2'⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have ht : 0 < t := (Real.exp_pos a).trans h1
        refine ⟨ht.ne', ?_, ?_⟩ <;> rw [abs_of_pos ht]
        · exact (Real.lt_log_iff_exp_lt ht).mpr h1
        · exact (Real.log_le_iff_le_exp ht).mpr h2
      · have ht : 0 < -t := (Real.exp_pos a).trans h1
        refine ⟨by linarith, ?_, ?_⟩ <;> rw [abs_of_neg (by linarith)]
        · exact (Real.lt_log_iff_exp_lt ht).mpr h1
        · exact (Real.log_le_iff_le_exp ht).mpr h2
  have hdisj : Disjoint A (Neg.neg ⁻¹' A) := by
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 : 0 < t := (Real.exp_pos a).trans ht.1
    have h2 : 0 < -t := (Real.exp_pos a).trans ht'.1
    linarith
  have hf (t : ℝ) (ht : 0 < t) : (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ = ENNReal.ofReal t⁻¹ := by
    rw [pow_one, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Real.norm_eq_abs, abs_of_pos ht,
      ENNReal.ofReal_inv_of_pos ht]
  have hA : ∫⁻ t in A, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (b - a) := by
    rw [setLIntegral_congr_fun measurableSet_Ioc
      (fun t ht ↦ hf t ((Real.exp_pos a).trans ht.1)), arch_Ioc_exp hab]
  have hneg : ∫⁻ t in Neg.neg ⁻¹' A, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ =
      ∫⁻ t in A, (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹ := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).setLIntegral_comp_preimage
      (s := A) measurableSet_Ioc (f := fun t : ℝ ↦ (↑(‖t‖₊ ^ 1) : ℝ≥0∞)⁻¹) (by fun_prop)
    simpa only [nnnorm_neg] using h
  rw [hS, lintegral_union (measurableSet_Ioc.preimage measurable_neg) hdisj, hneg, hA, two_mul]

/-- On the plane, `2 dA / |z|²` gives the band `2 log |z| ∈ (a, b]` mass `2π (b - a)`. -/
theorem arch_lintegral_complex {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ z in {z : ℂ | z ≠ 0 ∧ 2 * Real.log ‖z‖ ∈ Ioc a b}, (↑(‖z‖₊ ^ 2) : ℝ≥0∞)⁻¹
        ∂(2 • (volume : Measure ℂ)) =
      ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (b - a) := by
  set S := {z : ℂ | z ≠ 0 ∧ 2 * Real.log ‖z‖ ∈ Ioc a b}
  set A := Ioc (Real.exp (a / 2)) (Real.exp (b / 2))
  have hSm : MeasurableSet S :=
    show MeasurableSet ({(0 : ℂ)}ᶜ ∩ (fun z : ℂ ↦ 2 * Real.log ‖z‖) ⁻¹' Ioc a b) from
      (measurableSet_singleton 0).compl.inter (measurableSet_Ioc.preimage
        (measurable_const.mul (Real.measurable_log.comp measurable_norm)))
  have hmemS (r θ : ℝ) (hr : 0 < r) : Complex.polarCoord.symm (r, θ) ∈ S ↔ r ∈ A := by
    have hn : ‖Complex.polarCoord.symm (r, θ)‖ = r := by
      rw [Complex.norm_polarCoord_symm, abs_of_pos hr]
    have hz : Complex.polarCoord.symm (r, θ) ≠ 0 := by
      rw [← norm_ne_zero_iff, hn]
      exact hr.ne'
    simp only [S, A, mem_ofPred_eq, mem_Ioc, hn]
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨(Real.lt_log_iff_exp_lt hr).mp (by linarith), (Real.log_le_iff_le_exp hr).mp (by linarith)⟩
    · rintro ⟨h1, h2⟩
      have := (Real.lt_log_iff_exp_lt hr).mpr h1
      have := (Real.log_le_iff_le_exp hr).mpr h2
      exact ⟨hz, by linarith, by linarith⟩
  rw [Measure.restrict_smul, lintegral_smul_measure, ← lintegral_indicator hSm,
    ← Complex.lintegral_comp_polarCoord_symm]
  have hcongr : ∀ p ∈ polarCoord.target, ENNReal.ofReal p.1 •
      S.indicator (fun z : ℂ ↦ (↑(‖z‖₊ ^ 2) : ℝ≥0∞)⁻¹) (Complex.polarCoord.symm p) =
      A.indicator (fun r ↦ ENNReal.ofReal r⁻¹) p.1 * (Ioo (-Real.pi) Real.pi).indicator 1 p.2 := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    simp only [mem_Ioi] at hr
    dsimp only
    rw [indicator_of_mem (show θ ∈ Ioo (-Real.pi) Real.pi from hθ), Pi.one_apply, mul_one]
    by_cases hA : r ∈ A
    · rw [indicator_of_mem ((hmemS r θ hr).mpr hA), indicator_of_mem hA, smul_eq_mul]
      have hn : ‖Complex.polarCoord.symm (r, θ)‖₊ = r.toNNReal := by
        ext
        simp only [coe_nnnorm, Complex.norm_polarCoord_symm, abs_of_pos hr,
          Real.coe_toNNReal _ hr.le]
      have hx : (((r.toNNReal ^ 2 : ℝ≥0) : ℝ≥0∞))⁻¹ = ENNReal.ofReal ((r ^ 2)⁻¹) := by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_coe_nnreal]
        congr 2
        simp [hr.le]
      rw [hn, hx, ← ENNReal.ofReal_mul hr.le]
      congr 1
      field_simp
    · rw [indicator_of_notMem (fun h ↦ hA ((hmemS r θ hr).mp h)), indicator_of_notMem hA, smul_zero]
  have htarget : MeasurableSet polarCoord.target := measurableSet_Ioi.prod measurableSet_Ioo
  rw [setLIntegral_congr_fun htarget hcongr, show polarCoord.target =
      Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi from rfl, Measure.volume_eq_prod,
    ← Measure.prod_restrict,
    lintegral_prod_mul (f := A.indicator (fun r ↦ ENNReal.ofReal r⁻¹))
      (g := (Ioo (-Real.pi) Real.pi).indicator 1)
      ((Measurable.ennreal_ofReal measurable_inv).indicator measurableSet_Ioc).aemeasurable
      (measurable_one.indicator measurableSet_Ioo).aemeasurable,
    lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_self_of_subset_left (fun r (hr : r ∈ A) ↦ mem_Ioi.mpr ((Real.exp_pos _).trans hr.1)),
    arch_Ioc_exp (by linarith), lintegral_indicator_one measurableSet_Ioo,
    Measure.restrict_apply_self, Real.volume_Ioo, nsmul_eq_mul, Nat.cast_ofNat,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_mul zero_le_two,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

/-- The regulator parallelotope has volume equal to the regulator. -/
theorem arch_parallelotope :
    volume (regulatorParallelotope F (Units.basisModTorsion F)) =
      ENNReal.ofReal (Units.regulator F) := by
  set B := ((Units.basisModTorsion F).map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ
    (Units.unitLattice F)
  have hspan : Submodule.span ℤ (Set.range B) = Units.unitLattice F :=
    Module.Basis.ofZLatticeBasis_span ℝ (Units.unitLattice F) _
  have hfd := ZSpan.isAddFundamentalDomain B (volume : Measure ({w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} → ℝ))
  rw [hspan] at hfd
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain (Units.unitLattice F) volume hfd
  have hfin : volume (ZSpan.fundamentalDomain B) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded B).measure_lt_top.ne
  change volume (ZSpan.fundamentalDomain B) = _
  rw [Units.regulator, hcov, Measure.real, ENNReal.ofReal_toReal hfin]


/-- At a real place, the band `log ‖x‖ ∈ (a, b]` has multiplicative mass `2 (b - a)`. -/
theorem arch_real (w : InfinitePlace F) (h : w.IsReal) {a b : ℝ} (hab : a ≤ b) :
    infiniteLocalMulTamagawa F w
      {x | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} = 2 * ENNReal.ofReal (b - a) := by
  let e := (isometryEquivRealOfIsReal h).toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hnorm (t : ℝ) : ‖e.symm t‖ = ‖t‖ :=
    (isometryEquivRealOfIsReal h).symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivRealOfIsReal h).symm) t
  set S : Set w.Completion := {x | x ≠ 0 ∧ (w.mult : ℝ) * Real.log ‖x‖ ∈ Ioc a b}
  have hSm : MeasurableSet S :=
    show MeasurableSet ({(0 : w.Completion)}ᶜ ∩ (fun x : w.Completion ↦ (w.mult : ℝ) * Real.log ‖x‖) ⁻¹' Ioc a b) from
      (measurableSet_singleton 0).compl.inter (measurableSet_Ioc.preimage
        (measurable_const.mul (Real.measurable_log.comp measurable_norm)))
  have hsub : S ⊆ range (Units.val : w.Completionˣ → w.Completion) :=
    fun x hx ↦ ⟨Units.mk0 x hx.1, rfl⟩
  have hset : {x : w.Completionˣ | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} =
      Units.val ⁻¹' S := by
    ext x
    simp [S]
  rw [hset]
  rw [infiniteLocalMulTamagawa, hval.comap_preimage,
    inter_eq_self_of_subset_left hsub, withDensity_apply _ hSm,
    infiniteLocalAdditiveTamagawaMeasure, dif_pos h]
  change (∫⁻ x in S, (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹ ∂volume.map e.symm) = _
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map]
  have hz (t : ℝ) : e.symm t ≠ 0 ↔ t ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm, norm_ne_zero_iff]
  have hpre : e.symm ⁻¹' S = {t : ℝ | t ≠ 0 ∧ Real.log ‖t‖ ∈ Ioc a b} := by
    ext t
    simp only [S, mem_preimage, mem_ofPred_eq, hnorm, h.mult_eq_one, Nat.cast_one, one_mul, hz]
  have hnn (t : ℝ) : ‖e.symm t‖₊ = ‖t‖₊ := NNReal.eq (hnorm t)
  rw [hpre]
  simp only [hnn, h.mult_eq_one]
  exact arch_lintegral_real hab

/-- At a complex place, the band `2 log ‖x‖ ∈ (a, b]` has multiplicative mass `2π (b - a)`. -/
theorem arch_complex (w : InfinitePlace F) (h : ¬ w.IsReal) {a b : ℝ} (hab : a ≤ b) :
    infiniteLocalMulTamagawa F w
      {x | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} =
        ENNReal.ofReal (2 * Real.pi) * ENNReal.ofReal (b - a) := by
  have h' := InfinitePlace.not_isReal_iff_isComplex.mp h
  let e := (isometryEquivComplexOfIsComplex h').toHomeomorph.toMeasurableEquiv
  have hval := (IsOpenUnits.isOpenEmbedding_unitsVal (M := w.Completion)).measurableEmbedding
  have hnorm (z : ℂ) : ‖e.symm z‖ = ‖z‖ :=
    (isometryEquivComplexOfIsComplex h').symm.isometry.norm_map_of_map_zero
      (map_zero (ringEquivComplexOfIsComplex h').symm) z
  set S : Set w.Completion := {x | x ≠ 0 ∧ (w.mult : ℝ) * Real.log ‖x‖ ∈ Ioc a b}
  have hSm : MeasurableSet S :=
    show MeasurableSet ({(0 : w.Completion)}ᶜ ∩ (fun x : w.Completion ↦ (w.mult : ℝ) * Real.log ‖x‖) ⁻¹' Ioc a b) from
      (measurableSet_singleton 0).compl.inter (measurableSet_Ioc.preimage
        (measurable_const.mul (Real.measurable_log.comp measurable_norm)))
  have hsub : S ⊆ range (Units.val : w.Completionˣ → w.Completion) :=
    fun x hx ↦ ⟨Units.mk0 x hx.1, rfl⟩
  have hset : {x : w.Completionˣ | (w.mult : ℝ) * Real.log ‖x.val‖ ∈ Ioc a b} =
      Units.val ⁻¹' S := by
    ext x
    simp [S]
  rw [hset]
  rw [infiniteLocalMulTamagawa, hval.comap_preimage,
    inter_eq_self_of_subset_left hsub, withDensity_apply _ hSm,
    infiniteLocalAdditiveTamagawaMeasure, dif_neg h]
  change (∫⁻ x in S, (↑(‖x‖₊ ^ w.mult) : ℝ≥0∞)⁻¹ ∂(2 • (volume : Measure ℂ)).map e.symm) = _
  rw [e.symm.restrict_map, e.symm.measurableEmbedding.lintegral_map]
  have hz (z : ℂ) : e.symm z ≠ 0 ↔ z ≠ 0 := by
    rw [← norm_ne_zero_iff, hnorm, norm_ne_zero_iff]
  have hpre : e.symm ⁻¹' S = {z : ℂ | z ≠ 0 ∧ 2 * Real.log ‖z‖ ∈ Ioc a b} := by
    ext z
    simp only [S, mem_preimage, mem_ofPred_eq, hnorm, h'.mult_eq_two, Nat.cast_ofNat, hz]
  have hnn (z : ℂ) : ‖e.symm z‖₊ = ‖z‖₊ := NNReal.eq (hnorm z)
  rw [hpre]
  simp only [hnn, h'.mult_eq_two]
  exact arch_lintegral_complex hab

/-- The local multiplicative measure pushed forward by the normalized log norm is
`2` or `2π` times Lebesgue measure. -/
theorem arch_map (w : InfinitePlace F) :
    (infiniteLocalMulTamagawa F w).map
      (fun x : w.Completionˣ ↦ (w.mult : ℝ) * Real.log ‖x.val‖) =
        (if w.IsReal then (2 : ℝ≥0) else Real.toNNReal (2 * Real.pi)) • volume := by
  have hmeas : Measurable (fun x : w.Completionˣ ↦ (w.mult : ℝ) * Real.log ‖x.val‖) :=
    measurable_const.mul (Real.measurable_log.comp
      (continuous_norm.comp Units.continuous_val).measurable)
  symm
  refine Measure.ext_of_Ioc' (α := ℝ) _ _ (fun a b _ ↦ ?_) (fun a b hab ↦ ?_)
  · rw [Measure.smul_apply, Real.volume_Ioc, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  · rw [Measure.map_apply hmeas measurableSet_Ioc, Measure.smul_apply, Real.volume_Ioc,
      ENNReal.smul_def, smul_eq_mul]
    split_ifs with h
    · rw [ENNReal.coe_ofNat]
      exact (arch_real F w h hab.le).symm
    · exact (arch_complex F w h hab.le).symm

/-- Splitting off the omitted place: the strip over a set of log coordinates has the
volume of that set. -/
theorem arch_volume (P : Set ({w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} → ℝ))
    (hP : MeasurableSet P) :
    volume {y : InfinitePlace F → ℝ | ∑ w, y w ∈ Ico 0 1 ∧
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ∈ P} =
      volume P := by
  let p : InfinitePlace F → Prop := (· ≠ Units.dirichletUnitTheorem.w₀)
  have he := measurePreserving_piEquivPiSubtypeProd (fun _ : InfinitePlace F ↦ (volume : Measure ℝ)) p
  let : Unique {w // ¬ p w} := ⟨⟨⟨Units.dirichletUnitTheorem.w₀ (K := F), not_not.mpr rfl⟩⟩, fun w ↦ Subtype.ext (not_not.mp w.2)⟩
  set T : Set (({w // p w} → ℝ) × ({w // ¬ p w} → ℝ)) :=
    {z | z.1 ∈ P ∧ ∑ w, z.1 w + ∑ w, z.2 w ∈ Ico 0 1}
  have h1 : Measurable
      (fun z : ({w // p w} → ℝ) × ({w // ¬ p w} → ℝ) ↦ ∑ w, z.1 w + ∑ w, z.2 w) :=
    (Finset.measurable_sum Finset.univ fun (w : {w // p w}) _ ↦
      (measurable_pi_apply w).comp measurable_fst).add
    (Finset.measurable_sum Finset.univ fun (w : {w // ¬ p w}) _ ↦
      (measurable_pi_apply w).comp measurable_snd)
  have hT : MeasurableSet T := (hP.preimage measurable_fst).inter (measurableSet_Ico.preimage h1)
  have hpre : {y : InfinitePlace F → ℝ | ∑ w, y w ∈ Ico 0 1 ∧
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ∈ P} =
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ ℝ) p ⁻¹' T := by
    ext y
    simp only [T, mem_preimage, mem_ofPred_eq, MeasurableEquiv.piEquivPiSubtypeProd,
      MeasurableEquiv.coe_mk, Equiv.piEquivPiSubtypeProd_apply]
    rw [Fintype.sum_subtype_add_sum_subtype p y]
    exact and_comm
  have hslice (z : {w // p w} → ℝ) :
      Measure.pi (fun _ : {w // ¬ p w} ↦ (volume : Measure ℝ)) (Prod.mk z ⁻¹' T) =
        P.indicator 1 z := by
    by_cases hz : z ∈ P
    · rw [indicator_of_mem hz, Pi.one_apply]
      have hset : Prod.mk z ⁻¹' T = Set.univ.pi fun _ ↦ Ico (-∑ w, z w) (1 - ∑ w, z w) := by
        ext u
        simp only [T, mem_preimage, mem_ofPred_eq, mem_Ico, hz, true_and, mem_univ_pi,
          Fintype.sum_unique, Unique.forall_iff]
        constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
      rw [hset, Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one,
        Real.volume_Ico]
      norm_num
    · rw [indicator_of_notMem hz]
      have : Prod.mk z ⁻¹' T = ∅ := by
        ext u
        simp [T, hz]
      rw [this, measure_empty]
  rw [hpre, volume_pi, he.measure_preimage hT.nullMeasurableSet, Measure.prod_apply hT]
  simp_rw [hslice]
  exact lintegral_indicator_one hP

/-- The archimedean product measure of the regulator strip is the regulator times the
full sign and angular masses. In normalized radial logarithms each real place
contributes `2 dx` and each complex place contributes `2π dx`. Splitting off the
sum coordinate has Jacobian of absolute value one. -/
theorem arch_strip :
    Measure.pi (infiniteLocalMulTamagawa F)
      (archStrip F) = archRegulatorMass(F) := by
  set f : (w : InfinitePlace F) → w.Completionˣ → ℝ :=
    fun w x ↦ (w.mult : ℝ) * Real.log ‖x.val‖
  set c : InfinitePlace F → ℝ≥0 :=
    fun w ↦ if w.IsReal then (2 : ℝ≥0) else Real.toNNReal (2 * Real.pi)
  have hf (w : InfinitePlace F) : Measurable (f w) :=
    measurable_const.mul (Real.measurable_log.comp
      (continuous_norm.comp Units.continuous_val).measurable)
  have hmap (w : InfinitePlace F) :
      (infiniteLocalMulTamagawa F w).map (f w) = c w • volume :=
    arch_map F w
  have : ∀ w, SigmaFinite ((infiniteLocalMulTamagawa F w).map (f w)) :=
    fun w ↦ by rw [hmap w]; infer_instance
  set P := regulatorParallelotope F (Units.basisModTorsion F)
  have hP : MeasurableSet P := ZSpan.fundamentalDomain_measurableSet _
  set T := {y : InfinitePlace F → ℝ | ∑ w, y w ∈ Ico 0 1 ∧
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ∈ P}
  have hT : MeasurableSet T :=
    show MeasurableSet ((fun y : InfinitePlace F → ℝ ↦ ∑ w, y w) ⁻¹' Ico 0 1 ∩
        (fun y : InfinitePlace F → ℝ ↦
          fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} ↦ y w.val) ⁻¹' P) from
      (measurableSet_Ico.preimage (Finset.measurable_sum _ fun w _ ↦ measurable_pi_apply w)).inter
        (hP.preimage (measurable_pi_lambda _
          fun (w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀}) ↦
            measurable_pi_apply w.val))
  have hstrip : archStrip F = (fun x w ↦ f w (x w)) ⁻¹' T := rfl
  have hpi : Measure.pi (fun w ↦ (infiniteLocalMulTamagawa F w).map (f w)) =
      (∏ w, c w) • volume := by
    refine Measure.pi_eq fun s hs ↦ ?_
    rw [Measure.smul_apply, volume_pi_pi, ENNReal.smul_def, smul_eq_mul]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ ↦ ?_
    rw [hmap w, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hL : Measurable (fun (x : (w : InfinitePlace F) → w.Completionˣ) (w : InfinitePlace F) ↦
      f w (x w)) := measurable_pi_lambda _ fun w ↦ (hf w).comp (measurable_pi_apply w)
  rw [hstrip, ← Measure.map_apply hL hT,
    Measure.pi_map_pi (fun w ↦ (hf w).aemeasurable), hpi, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, arch_volume F P hP, arch_parallelotope F]
  have hc : ((∏ w, c w : ℝ≥0) : ℝ) = (2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F := by
    rw [NNReal.coe_prod]
    simp only [c, apply_ite NNReal.toReal, NNReal.coe_ofNat, Real.coe_toNNReal _ (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
    rw [Finset.prod_ite]
    simp only [Finset.prod_const, ← Fintype.card_subtype, InfinitePlace.not_isReal_iff_isComplex]
  rw [← ENNReal.ofReal_coe_nnreal, hc, ← ENNReal.ofReal_mul (by positivity)]


end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part C =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH InfinitePlace.Completion Set RiemannMasullo
open scoped Classical

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

/-! ### Archimedean ideles: logarithms, norms, a section of the norm -/

/-- The normalized logarithm `log |x_w|_w` of an archimedean idele at the place `w`. -/
def Lg (x : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) : ℝ :=
  (w.mult : ℝ) * Real.log ‖(x : InfiniteAdeleRing F) w‖

/-- The archimedean norm `∏_w |x_w|_w`. -/
def normInf (x : (InfiniteAdeleRing F)ˣ) : ℝ :=
  ∏ w : InfinitePlace F, ‖(x : InfiniteAdeleRing F) w‖ ^ w.mult

variable {F}

omit [NumberField F] in
theorem coord_mul_inv (x : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (x : InfiniteAdeleRing F) w * ((x⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1 :=
  congrArg (fun a : InfiniteAdeleRing F => a w) x.mul_inv

omit [NumberField F] in
theorem coord_ne_zero (x : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    (x : InfiniteAdeleRing F) w ≠ 0 := by
  intro h
  have := coord_mul_inv x w
  rw [h, zero_mul] at this
  exact zero_ne_one this

omit [NumberField F] in
theorem coord_inv (x : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    ((x⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = ((x : InfiniteAdeleRing F) w)⁻¹ :=
  (eq_inv_of_mul_eq_one_right (coord_mul_inv x w))

omit [NumberField F] in
theorem coord_mul (x y : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    ((x * y : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
      (x : InfiniteAdeleRing F) w * (y : InfiniteAdeleRing F) w := rfl

omit [NumberField F] in
theorem norm_coord_pos (x : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    0 < ‖(x : InfiniteAdeleRing F) w‖ := norm_pos_iff.mpr (coord_ne_zero x w)

omit [NumberField F] in
theorem Lg_mul (x y : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    Lg F (x * y) w = Lg F x w + Lg F y w := by
  unfold Lg
  rw [coord_mul, norm_mul, Real.log_mul (norm_coord_pos x w).ne' (norm_coord_pos y w).ne']
  ring

omit [NumberField F] in
theorem Lg_inv (x : (InfiniteAdeleRing F)ˣ) (w : InfinitePlace F) :
    Lg F x⁻¹ w = -Lg F x w := by
  unfold Lg
  rw [coord_inv, norm_inv, Real.log_inv]
  ring

theorem normInf_pos (x : (InfiniteAdeleRing F)ˣ) : 0 < normInf F x :=
  Finset.prod_pos fun w _ => pow_pos (norm_coord_pos x w) _

theorem sum_Lg (x : (InfiniteAdeleRing F)ˣ) :
    ∑ w, Lg F x w = Real.log (normInf F x) := by
  unfold normInf Lg
  rw [Real.log_prod (fun w _ => (pow_pos (norm_coord_pos x w) _).ne')]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Real.log_pow]

theorem normInf_mul (x y : (InfiniteAdeleRing F)ˣ) :
    normInf F (x * y) = normInf F x * normInf F y := by
  unfold normInf
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [coord_mul, norm_mul, mul_pow]

theorem normInf_inv (x : (InfiniteAdeleRing F)ˣ) : normInf F x⁻¹ = (normInf F x)⁻¹ := by
  unfold normInf
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [coord_inv, norm_inv, inv_pow]

theorem sum_Lg_mem_iff (x : (InfiniteAdeleRing F)ˣ) :
    (∑ w, Lg F x w) ∈ Ico (0 : ℝ) 1 ↔ normInf F x ∈ Ico 1 (Real.exp 1) := by
  rw [sum_Lg]
  have hp := normInf_pos x
  simp only [mem_Ico]
  rw [Real.log_nonneg_iff hp, Real.log_lt_iff_lt_exp hp]

/-- The real archimedean idele norm is the archimedean norm. -/
theorem coe_infiniteIdeleNorm (g : (InfiniteAdeleRing F)ˣ) :
    (((infiniteIdeleNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = normInf F g := by
  simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val, NNReal.coe_prod,
    NNReal.coe_pow]
  rfl

theorem mem_ker_iff (g : (InfiniteAdeleRing F)ˣ) :
    g ∈ MonoidHom.ker (infiniteIdeleNorm F) ↔ normInf F g = 1 := by
  rw [MonoidHom.mem_ker, ← coe_infiniteIdeleNorm, ← Units.val_eq_one, ← NNReal.coe_eq_one]

omit [NumberField F] in
theorem exists_ext_eq (w : InfinitePlace F) (r : ℝ) :
    ∃ z : w.Completion, extensionEmbedding w z = (r : ℂ) := by
  by_cases hw : w.IsReal
  · obtain ⟨z, hz⟩ := surjective_extensionEmbeddingOfIsReal hw r
    exact ⟨z, by rw [← extensionEmbeddingOfIsReal_apply hw, hz]⟩
  · exact surjective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) (r : ℂ)

variable (F)

/-- The distinguished infinite place. -/
abbrev w0 : InfinitePlace F := Units.dirichletUnitTheorem.w₀ (K := F)

/-- The radius of the section at `w₀`. -/
def rsec (t : ℝ) : ℝ := if 0 < t then t ^ (1 / ((w0 F).mult : ℝ)) else 1

/-- The coordinate of the section at `w₀`: a positive real number. -/
def zsec (t : ℝ) : (w0 F).Completion := Classical.choose (exists_ext_eq (w0 F) (rsec F t))

variable {F}

theorem rsec_pos (t : ℝ) : 0 < rsec F t := by
  unfold rsec
  split_ifs with h
  · exact Real.rpow_pos_of_pos h _
  · exact one_pos

theorem ext_zsec (t : ℝ) : extensionEmbedding (w0 F) (zsec F t) = (rsec F t : ℂ) :=
  Classical.choose_spec (exists_ext_eq (w0 F) (rsec F t))

theorem norm_zsec (t : ℝ) : ‖zsec F t‖ = rsec F t := by
  rw [← (isometry_extensionEmbedding (w0 F)).norm_map_of_map_zero (map_zero _), ext_zsec,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (rsec_pos t)]

theorem zsec_ne_zero (t : ℝ) : zsec F t ≠ 0 := by
  intro h
  have := norm_zsec (F := F) t
  rw [h, norm_zero] at this
  exact (rsec_pos t).ne' this.symm

variable (F)

/-- The section `t ↦ s(t)` of the archimedean norm: `s(t)` is the positive real number
`t ^ (1 / m_{w₀})` at `w₀` and `1` at the other infinite places. -/
def secI (t : ℝ) : (InfiniteAdeleRing F)ˣ :=
  (MulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).symm
    (Pi.mulSingle (w0 F) (Units.mk0 (zsec F t) (zsec_ne_zero t)))

variable {F}

theorem secI_ne (t : ℝ) (w : InfinitePlace F) (hw : w ≠ w0 F) :
    ((secI F t : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1 := by
  change (((Pi.mulSingle (w0 F) (Units.mk0 (zsec F t) (zsec_ne_zero t)) :
    (w : InfinitePlace F) → (w.Completion)ˣ) w : w.Completionˣ) : w.Completion) = 1
  rw [Pi.mulSingle_eq_of_ne hw, Units.val_one]

theorem secI_w0 (t : ℝ) :
    ((secI F t : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) (w0 F) = zsec F t := by
  change (((Pi.mulSingle (w0 F) (Units.mk0 (zsec F t) (zsec_ne_zero t)) :
    (w : InfinitePlace F) → (w.Completion)ˣ) (w0 F) : (w0 F).Completionˣ) : (w0 F).Completion) = _
  rw [Pi.mulSingle_eq_same, Units.val_mk0]

theorem normInf_secI (t : ℝ) (ht : 0 < t) : normInf F (secI F t) = t := by
  unfold normInf
  rw [Finset.prod_eq_single (w0 F)]
  · rw [secI_w0, norm_zsec]
    unfold rsec
    rw [if_pos ht, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, one_div,
      inv_mul_cancel₀ (by exact_mod_cast (InfinitePlace.mult_pos (w := w0 F)).ne'), Real.rpow_one]
  · intro w _ hw
    rw [secI_ne t w hw, norm_one, one_pow]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Lg_secI_ne (t : ℝ) (w : InfinitePlace F) (hw : w ≠ w0 F) : Lg F (secI F t) w = 0 := by
  unfold Lg
  rw [secI_ne t w hw, norm_one, Real.log_one, mul_zero]

/-- The torsion sector condition at `w₀` (with `σ = id`). -/
def sector (x : (InfiniteAdeleRing F)ˣ) : Prop :=
  inTorsionSector F (w0 F) (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)
    (Units.map (Pi.evalRingHom (fun w : InfinitePlace F ↦ w.Completion) (w0 F)).toMonoidHom x)

theorem sector_iff (x : (InfiniteAdeleRing F)ˣ) :
    sector x ↔ (extensionEmbedding (w0 F) ((x : InfiniteAdeleRing F) (w0 F))).arg ∈
      Ico 0 (2 * Real.pi / Units.torsionOrder F) := Iff.rfl

theorem sector_mul_secI (x : (InfiniteAdeleRing F)ˣ) (t : ℝ) :
    sector (x * secI F t) ↔ sector x := by
  rw [sector_iff, sector_iff, coord_mul, map_mul, secI_w0, ext_zsec, Complex.arg_mul_real (rsec_pos t)]

theorem sector_mul_secI_inv (x : (InfiniteAdeleRing F)ˣ) (t : ℝ) :
    sector (x * (secI F t)⁻¹) ↔ sector x := by
  rw [← sector_mul_secI (x * (secI F t)⁻¹) t, inv_mul_cancel_right]

variable (F)

/-- `Ω₀`: the archimedean ideles with norm in `[1, e)` whose log coordinates away from `w₀` lie in
the regulator parallelotope and whose `w₀`-coordinate lies in the torsion sector. -/
def OmegaI : Set (InfiniteAdeleRing F)ˣ :=
  {x | (∑ w, Lg F x w) ∈ Ico (0 : ℝ) 1 ∧
    (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} => Lg F x w.val) ∈
      regulatorParallelotope F (Units.basisModTorsion F) ∧ sector x}

/-- The archimedean regulator strip, in `GL₁(𝔸_{F,∞})`. -/
def StripI : Set (InfiniteAdeleRing F)ˣ :=
  {x | (∑ w, Lg F x w) ∈ Ico (0 : ℝ) 1 ∧
    (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} => Lg F x w.val) ∈
      regulatorParallelotope F (Units.basisModTorsion F)}

/-- Tate's archimedean domain for our choice of data. -/
abbrev E0 : Set (MonoidHom.ker (infiniteIdeleNorm F)) :=
  tateArchimedeanDomain F (Units.basisModTorsion F) (w0 F) (AlgEquiv.refl : ℂ ≃ₐ[ℝ] ℂ)

variable {F}

theorem mem_E0_iff (k : MonoidHom.ker (infiniteIdeleNorm F)) :
    k ∈ E0 F ↔ (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
        Lg F (k : (InfiniteAdeleRing F)ˣ) w.val) ∈
      regulatorParallelotope F (Units.basisModTorsion F) ∧ sector (k : (InfiniteAdeleRing F)ˣ) :=
  Iff.rfl

theorem Lg_mul_secI_inv_ne (x : (InfiniteAdeleRing F)ˣ) (t : ℝ) (w : InfinitePlace F)
    (hw : w ≠ w0 F) : Lg F (x * (secI F t)⁻¹) w = Lg F x w := by
  rw [Lg_mul, Lg_inv, Lg_secI_ne t w hw, neg_zero, add_zero]

theorem Lg_mul_secI_ne (x : (InfiniteAdeleRing F)ˣ) (t : ℝ) (w : InfinitePlace F)
    (hw : w ≠ w0 F) : Lg F (x * secI F t) w = Lg F x w := by
  rw [Lg_mul, Lg_secI_ne t w hw, add_zero]

/-- An element of `Ω₀`, divided by the section at its norm, lies in `E₀`. -/
theorem omega_to_E0 (x : (InfiniteAdeleRing F)ˣ) (hx : x ∈ OmegaI F) :
    ∃ k ∈ E0 F, (k : (InfiniteAdeleRing F)ˣ) = x * (secI F (normInf F x))⁻¹ := by
  have hker : x * (secI F (normInf F x))⁻¹ ∈ MonoidHom.ker (infiniteIdeleNorm F) := by
    rw [mem_ker_iff, normInf_mul, normInf_inv, normInf_secI _ (normInf_pos x),
      mul_inv_cancel₀ (normInf_pos x).ne']
  refine ⟨⟨_, hker⟩, ?_, rfl⟩
  rw [mem_E0_iff]
  refine ⟨?_, (sector_mul_secI_inv x _).mpr hx.2.2⟩
  have : (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
      Lg F (x * (secI F (normInf F x))⁻¹) w.val) =
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} => Lg F x w.val) :=
    funext fun w => Lg_mul_secI_inv_ne x _ w.val w.2
  change (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
      Lg F (x * (secI F (normInf F x))⁻¹) w.val) ∈ _
  rw [this]
  exact hx.2.1

/-- An element of `E₀` times the section at `t ∈ [1, e)` lies in `Ω₀`. -/
theorem E0_to_omega (k : MonoidHom.ker (infiniteIdeleNorm F)) (hk : k ∈ E0 F) (t : ℝ)
    (ht : t ∈ Ico 1 (Real.exp 1)) :
    (k : (InfiniteAdeleRing F)ˣ) * secI F t ∈ OmegaI F ∧
      normInf F ((k : (InfiniteAdeleRing F)ˣ) * secI F t) = t := by
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
  have hn : normInf F ((k : (InfiniteAdeleRing F)ˣ) * secI F t) = t := by
    rw [normInf_mul, normInf_secI t ht0, (mem_ker_iff _).mp k.2, one_mul]
  refine ⟨⟨(sum_Lg_mem_iff _).mpr (by rw [hn]; exact ht), ?_, (sector_mul_secI _ t).mpr hk.2⟩, hn⟩
  have : (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
      Lg F ((k : (InfiniteAdeleRing F)ˣ) * secI F t) w.val) =
      (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
        Lg F (k : (InfiniteAdeleRing F)ˣ) w.val) :=
    funext fun w => Lg_mul_secI_ne _ t w.val w.2
  rw [this]
  exact hk.1

end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part D =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH InfinitePlace.Completion Set RiemannMasullo
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-! ### Torsion translates of `Ω₀` -/

theorem norm_unitsToInfiniteIdeles (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    ‖((unitsToInfiniteIdeles F u : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ =
      w ((u : 𝓞 F) : F) :=
  InfinitePlace.Completion.norm_coe w _

theorem Lg_torsion_mul (ζ : (𝓞 F)ˣ) (hζ : ζ ∈ Units.torsion F) (x : (InfiniteAdeleRing F)ˣ)
    (w : InfinitePlace F) : Lg F (unitsToInfiniteIdeles F ζ * x) w = Lg F x w := by
  rw [Lg_mul]
  unfold Lg
  rw [norm_unitsToInfiniteIdeles, (Units.mem_torsion F).mp hζ w, Real.log_one, mul_zero, zero_add]

theorem normInf_torsion (ζ : (𝓞 F)ˣ) (hζ : ζ ∈ Units.torsion F) :
    normInf F (unitsToInfiniteIdeles F ζ) = 1 := by
  unfold normInf
  refine Finset.prod_eq_one fun w _ => ?_
  rw [norm_unitsToInfiniteIdeles, (Units.mem_torsion F).mp hζ w, one_pow]

theorem stripI_eq :
    StripI F = ⋃ ζ : Units.torsion F,
      (fun x => unitsToInfiniteIdeles F (ζ : (𝓞 F)ˣ) * x) '' OmegaI F := by
  ext x
  simp only [mem_iUnion, mem_image]
  constructor
  · intro hx
    set t := normInf F x with ht_def
    have ht : t ∈ Ico 1 (Real.exp 1) := (sum_Lg_mem_iff x).mp hx.1
    have hker : x * (secI F t)⁻¹ ∈ MonoidHom.ker (infiniteIdeleNorm F) := by
      rw [mem_ker_iff, normInf_mul, normInf_inv, normInf_secI _ (normInf_pos x),
        mul_inv_cancel₀ (normInf_pos x).ne']
    have hpar : (⟨_, hker⟩ : MonoidHom.ker (infiniteIdeleNorm F)) ∈
        logParallelotopePreimage F (Units.basisModTorsion F) := by
      have : (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
          Lg F (x * (secI F t)⁻¹) w.val) =
          (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} => Lg F x w.val) :=
        funext fun w => Lg_mul_secI_inv_ne x _ w.val w.2
      show (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
          Lg F (x * (secI F t)⁻¹) w.val) ∈ regulatorParallelotope F (Units.basisModTorsion F)
      rw [this]
      exact hx.2
    obtain ⟨ζ, hζ, e, he, hke⟩ := (tateArchimedeanDomain_torsion_translates F
      (Units.basisModTorsion F) (w0 F) AlgEquiv.refl ⟨_, hker⟩).mp hpar
    obtain ⟨hmem, -⟩ := E0_to_omega e he t ht
    refine ⟨⟨ζ, hζ⟩, (e : (InfiniteAdeleRing F)ˣ) * secI F t, hmem, ?_⟩
    change unitsToInfiniteIdeles F ζ * ((e : (InfiniteAdeleRing F)ˣ) * secI F t) = x
    have hke' : x * (secI F t)⁻¹ = unitsToInfiniteIdeles F ζ * (e : (InfiniteAdeleRing F)ˣ) :=
      hke
    rw [← mul_assoc, ← hke', inv_mul_cancel_right]
  · rintro ⟨ζ, y, hy, rfl⟩
    have hL : ∀ w, Lg F (unitsToInfiniteIdeles F (ζ : (𝓞 F)ˣ) * y) w = Lg F y w :=
      fun w => Lg_torsion_mul _ ζ.2 y w
    refine ⟨?_, ?_⟩
    · simp only [hL]
      exact hy.1
    · have : (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} =>
          Lg F (unitsToInfiniteIdeles F (ζ : (𝓞 F)ˣ) * y) w.val) =
          (fun w : {w : InfinitePlace F // w ≠ Units.dirichletUnitTheorem.w₀} => Lg F y w.val) :=
        funext fun w => hL w.val
      rw [this]
      exact hy.2.1

theorem omega_disjoint : Pairwise (Function.onFun Disjoint fun ζ : Units.torsion F =>
    (fun x => unitsToInfiniteIdeles F (ζ : (𝓞 F)ˣ) * x) '' OmegaI F) := by
  intro ζ ζ' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨y, hy, rfl⟩ ⟨y', hy', hyy⟩
  apply hne
  -- the norms agree
  have hn : normInf F y' = normInf F y := by
    have := congrArg (normInf F) hyy
    rwa [normInf_mul, normInf_mul, normInf_torsion _ ζ.2, normInf_torsion _ ζ'.2, one_mul,
      one_mul] at this
  obtain ⟨k, hk, hk_eq⟩ := omega_to_E0 y hy
  obtain ⟨k', hk', hk'_eq⟩ := omega_to_E0 y' hy'
  rw [hn] at hk'_eq
  -- `k' = (ζ'⁻¹ ζ) k`
  have hrel : (k' : (InfiniteAdeleRing F)ˣ) =
      unitsToInfiniteIdeles F ((ζ' : (𝓞 F)ˣ)⁻¹ * ζ) * (k : (InfiniteAdeleRing F)ˣ) := by
    rw [hk'_eq, hk_eq, map_mul, map_inv]
    have hyy' : unitsToInfiniteIdeles F (ζ' : (𝓞 F)ˣ) * y' =
        unitsToInfiniteIdeles F (ζ : (𝓞 F)ˣ) * y := hyy
    have : y' = (unitsToInfiniteIdeles F (ζ' : (𝓞 F)ˣ))⁻¹ *
        (unitsToInfiniteIdeles F (ζ : (𝓞 F)ˣ) * y) := by
      rw [← hyy', inv_mul_cancel_left]
    rw [this]
    group
  obtain ⟨u, -, huniq⟩ := tateArchimedeanDomain_existsUnique_unit_mul F
    (Units.basisModTorsion F) (w0 F) AlgEquiv.refl k'
  have h1 : (1 : (𝓞 F)ˣ) = u := huniq 1 ⟨k', hk', by rw [map_one, one_mul]⟩
  have h2 : (ζ' : (𝓞 F)ˣ)⁻¹ * ζ = u := huniq _ ⟨k, hk, hrel⟩
  have h3 : (ζ' : (𝓞 F)ˣ)⁻¹ * ζ = 1 := h2.trans h1.symm
  apply Subtype.ext
  rw [inv_mul_eq_one] at h3
  exact h3.symm

/-! ### The measure of `Ω₀` -/

/-- The coordinates `GL₁(𝔸_{F,∞}) ≃ ∏_w F_wˣ`. -/
abbrev eInf : (InfiniteAdeleRing F)ˣ ≃* ((w : InfinitePlace F) → w.Completionˣ) :=
  MulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)

theorem archStrip_eq : archStrip F = (eInf (F := F)).symm ⁻¹' StripI F := rfl

theorem measurable_Lg_comp (w : InfinitePlace F) :
    Measurable (fun p : (w : InfinitePlace F) → w.Completionˣ =>
      Lg F ((eInf (F := F)).symm p) w) :=
  measurable_const.mul (Real.measurable_log.comp
    ((continuous_norm.comp Units.continuous_val).measurable.comp (measurable_pi_apply w)))

theorem measurableSet_omega : MeasurableSet ((eInf (F := F)).symm ⁻¹' OmegaI F) := by
  have hP : MeasurableSet (regulatorParallelotope F (Units.basisModTorsion F)) :=
    ZSpan.fundamentalDomain_measurableSet _
  have hsec : Measurable (fun p : (w : InfinitePlace F) → w.Completionˣ =>
      (extensionEmbedding (w0 F) (((p (w0 F)) : (w0 F).Completionˣ) : (w0 F).Completion)).arg) :=
    Complex.measurable_arg.comp ((isometry_extensionEmbedding (w0 F)).continuous.measurable.comp
      (Units.continuous_val.measurable.comp (measurable_pi_apply (w0 F))))
  refine ((measurableSet_Ico.preimage
      (Finset.measurable_sum Finset.univ fun w _ => measurable_Lg_comp w)).inter
    ((hP.preimage (measurable_pi_lambda _ fun w => measurable_Lg_comp w.val)).inter
      (measurableSet_Ico.preimage hsec)))

theorem measurableSet_strip : MeasurableSet ((eInf (F := F)).symm ⁻¹' StripI F) := by
  rw [← archStrip_eq]
  exact archStrip_measurableSet F

variable (F) in
/-- The archimedean multiplicative Tamagawa measure `⊗_w μ_w`. -/
abbrev muInf : Measure ((w : InfinitePlace F) → w.Completionˣ) :=
  Measure.pi (infiniteLocalMulTamagawa F)

theorem muInf_leftInv : (muInf F).IsMulLeftInvariant := by
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := w.Completion)).isEmbedding.secondCountableTopology
  have : ∀ w, (infiniteLocalMulTamagawa F w).IsHaarMeasure :=
    fun w => infiniteLocalMulTamagawa_isHaarMeasure F w
  have : ∀ w, SigmaFinite (infiniteLocalMulTamagawa F w) := fun w => inferInstance
  infer_instance

theorem preimage_image_mul (a : (InfiniteAdeleRing F)ˣ) (S : Set (InfiniteAdeleRing F)ˣ) :
    (eInf (F := F)).symm ⁻¹' ((fun x => a * x) '' S) =
      (fun p => eInf a⁻¹ * p) ⁻¹' ((eInf (F := F)).symm ⁻¹' S) := by
  ext p
  simp only [mem_preimage, mem_image]
  constructor
  · rintro ⟨x, hx, hxp⟩
    rw [map_mul, MulEquiv.symm_apply_apply, ← hxp, inv_mul_cancel_left]
    exact hx
  · intro h
    refine ⟨_, h, ?_⟩
    rw [map_mul, MulEquiv.symm_apply_apply, mul_inv_cancel_left]

/-- `w_F · (⊗ μ_w)(Ω₀) = 2^{r₁} (2π)^{r₂} R_F`. -/
theorem muInf_omega :
    (Units.torsionOrder F : ℝ≥0∞) * muInf F ((eInf (F := F)).symm ⁻¹' OmegaI F) =
      ENNReal.ofReal ((2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
        (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Units.regulator F) := by
  have := muInf_leftInv (F := F)
  rw [← arch_strip F, archStrip_eq, stripI_eq, preimage_iUnion]
  rw [measure_iUnion]
  · simp_rw [preimage_image_mul, measure_preimage_mul]
    rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe]
    rfl
  · intro ζ ζ' hne
    simp only [Function.onFun]
    exact (omega_disjoint hne).preimage _
  · intro ζ
    rw [preimage_image_mul]
    exact measurableSet_omega.preimage (measurable_const_mul _)

end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part E =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH
open scoped WithZero nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-- The finite component at `v` of an idele times that of its inverse is `1`. -/
lemma fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) h
  exact h2

/-- The component of an idele at a finite place `v` has valuation `1` if and only if it and the
`v`-component of the inverse idele are `v`-integral. -/
lemma valued_eq_one_iff (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1 ↔
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
        ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  have hm : Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
      Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) = 1 := by
    rw [← map_mul, fin_mul_inv, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hm
    exact ⟨h.le, hm.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = Valued.v ((g : AdeleRing (𝓞 F) F).2 v) *
          Valued.v (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) := hm.symm
      _ ≤ Valued.v ((g : AdeleRing (𝓞 F) F).2 v) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _

/-- If the `v`-components of an idele and of its inverse are both `v`-integral, the `v`-component
has norm `1`. -/
lemma norm_fin_eq_one_of_mem (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have a1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1)
  have a2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr
      ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h2)
  have hm : ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
      ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, fin_mul_inv, norm_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ) = ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
        ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ := hm.symm
    _ ≤ ‖(g : AdeleRing (𝓞 F) F).2 v‖ * 1 := mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    _ = _ := mul_one _

/-- An idele is a unit at all but finitely many finite places. -/
lemma finite_valued_ne_one (g : IdeleGroup F) :
    {v : HeightOneSpectrum (𝓞 F) | Valued.v ((g : AdeleRing (𝓞 F) F).2 v) ≠ 1}.Finite := by
  have h1 : ∀ᶠ v in Filter.cofinite,
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := (g : AdeleRing (𝓞 F) F).2.2
  have h2 : ∀ᶠ v in Filter.cofinite,
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2
  have h3 := h1.and h2
  rw [Filter.eventually_cofinite] at h3
  refine h3.subset ?_
  intro v hv h
  exact hv ((valued_eq_one_iff g v).mpr h)

/-- All but finitely many finite components of an idele have norm `1`. -/
lemma finite_mulSupport_fin (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  refine (finite_valued_ne_one g).subset ?_
  intro v hv h
  exact hv (norm_fin_eq_one_of_mem g v ((valued_eq_one_iff g v).mp h).1
    ((valued_eq_one_iff g v).mp h).2)

/-! ### The idelic norm -/

/-- The idelic norm is multiplicative. -/
lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := fun w => rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  simp only [e1, e2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (finite_mulSupport_fin g) (finite_mulSupport_fin h)]
  ring


/-- The component at an infinite place `w` of an idele times that of its inverse is `1`. -/
lemma inf_mul_inv (g : IdeleGroup F) (w : InfinitePlace F) :
    (g : AdeleRing (𝓞 F) F).1 w * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.1 w) h
  exact h2


/-- The idelic norm is positive. -/
lemma ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g := by
  unfold ideleNorm
  apply mul_pos
  · refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr ?_) _
    intro h0
    have := inf_mul_inv g w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · refine finprod_induction (0 < ·) zero_lt_one (fun _ _ => mul_pos) fun v => norm_pos_iff.mpr ?_
    intro h0
    have := fin_mul_inv g v
    rw [h0, zero_mul] at this
    exact zero_ne_one this


/-! ### The archimedean and the finite part of an idele -/

/-- The finite part of an idele. -/
noncomputable def finPart : IdeleGroup F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

/-- The archimedean part of an idele. -/
noncomputable def infPart : IdeleGroup F →* (InfiniteAdeleRing F)ˣ :=
  Units.map (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

lemma finPart_apply (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((finPart g : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v =
      (g : AdeleRing (𝓞 F) F).2 v := rfl

/-! ### Ideles with prescribed archimedean norm and prescribed ideal class -/

omit [NumberField F] in
/-- Every positive real number is the norm of an element of the completion at an infinite
place. -/
lemma exists_norm_eq (w : InfinitePlace F) (s : ℝ) (hs : 0 < s) :
    ∃ z : w.Completion, ‖z‖ = s := by
  by_cases hw : w.IsReal
  · obtain ⟨z, hz⟩ := InfinitePlace.Completion.surjective_extensionEmbeddingOfIsReal hw s
    refine ⟨z, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) z, hz, Real.norm_eq_abs, abs_of_pos hs]
  · obtain ⟨z, hz⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) (s : ℂ)
    refine ⟨z, ?_⟩
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) z, hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]

/-- Every positive real number is the archimedean norm of an archimedean idele. -/
lemma exists_infiniteUnits_norm_eq (t : ℝ) (ht : 0 < t) :
    ∃ a : (InfiniteAdeleRing F)ˣ,
      ∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult = t := by
  classical
  let w₀ : InfinitePlace F := Classical.arbitrary _
  have hm : (0 : ℝ) < (w₀.mult : ℝ) := by
    have := InfinitePlace.mult_pos (w := w₀)
    exact_mod_cast this
  obtain ⟨z, hz⟩ := exists_norm_eq w₀ (t ^ (1 / (w₀.mult : ℝ))) (Real.rpow_pos_of_pos ht _)
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    exact (Real.rpow_pos_of_pos ht (1 / (w₀.mult : ℝ))).ne' hz.symm
  let u : (w : InfinitePlace F) → (w.Completion)ˣ := Pi.mulSingle w₀ (Units.mk0 z hz0)
  let a : (InfiniteAdeleRing F)ˣ :=
    { val := fun w => ((u w : (w.Completion)ˣ) : w.Completion)
      inv := fun w => (((u w)⁻¹ : (w.Completion)ˣ) : w.Completion)
      val_inv := funext fun w => (u w).mul_inv
      inv_val := funext fun w => (u w).inv_mul }
  refine ⟨a, ?_⟩
  have hval : ∀ w, ((a : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w =
      ((u w : (w.Completion)ˣ) : w.Completion) := fun w => rfl
  simp_rw [hval]
  rw [Finset.prod_eq_single w₀]
  · simp only [u, Pi.mulSingle_eq_same, Units.val_mk0]
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul ht.le, one_div, inv_mul_cancel₀ hm.ne',
      Real.rpow_one]
  · intro w _ hw
    simp only [u, Pi.mulSingle_eq_of_ne hw, Units.val_one, norm_one, one_pow]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

/-- The idele with archimedean part `a` and finite part `x`. -/
noncomputable def mkIdele (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    IdeleGroup F :=
  (Homeomorph.prodUnits : (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)ˣ ≃ₜ _).symm (a, x)

lemma mkIdele_fst (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((mkIdele a x : IdeleGroup F) : AdeleRing (𝓞 F) F).1 = (a : InfiniteAdeleRing F) := rfl

lemma mkIdele_snd (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((mkIdele a x : IdeleGroup F) : AdeleRing (𝓞 F) F).2 = (x : FiniteAdeleRing (𝓞 F) F) := rfl

lemma finPart_mkIdele (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    finPart (mkIdele a x) = x := Units.ext rfl

lemma ideleNorm_mkIdele (a : (InfiniteAdeleRing F)ˣ) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ideleNorm (mkIdele a x) = (∏ w : InfinitePlace F, ‖(a : InfiniteAdeleRing F) w‖ ^ w.mult) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := rfl

/-- The ideal class of an idele is the class of the content of its finite part, for a
surjective content homomorphism `φ`. -/
theorem exists_contentHom (F : Type*) [Field F] [NumberField F] :
    ∃ φ : (FiniteAdeleRing (𝓞 F) F)ˣ →* (FractionalIdeal (𝓞 F)⁰ F)ˣ,
      (∀ g : IdeleGroup F, ideleIdealClass F g = ClassGroup.mk F (φ (finPart g))) ∧
      Function.Surjective φ := by
  obtain ⟨φ, hφ, -, hsurj, -, -⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
      (𝓞 F) F
  refine ⟨φ, ?_, hsurj⟩
  intro g
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    -WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))
  let P : HeightOneSpectrum (𝓞 F) → (Ideal (𝓞 F))⁰ := fun v =>
    ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      (FractionalIdeal.mk0 F (P v)) ^ n v).Finite := by
    refine (finite_valued_ne_one g).subset ?_
    intro v hv h
    apply hv
    change (FractionalIdeal.mk0 F (P v)) ^
      (-WithZero.log (Valued.v ((g : AdeleRing (𝓞 F) F).2 v))) = 1
    rw [h, WithZero.log_one, neg_zero, zpow_zero]
  have hu : φ (finPart g) = ∏ᶠ v, (FractionalIdeal.mk0 F (P v)) ^ n v := by
    apply Units.ext
    rw [hφ (finPart g)]
    have h1 := MonoidHom.map_finprod_of_injective (Units.coeHom (FractionalIdeal (𝓞 F)⁰ F))
      (fun _ _ h => Units.ext h) (fun v => (FractionalIdeal.mk0 F (P v)) ^ n v)
    rw [Units.coeHom_apply] at h1
    rw [h1]
    refine finprod_congr fun v => ?_
    rw [Units.coeHom_apply, Units.val_zpow_eq_zpow_val, FractionalIdeal.coe_mk0]
    rfl
  rw [hu, MonoidHom.map_finprod _ hfin]
  unfold ideleIdealClass
  refine finprod_congr fun v => ?_
  rw [map_zpow, ClassGroup.mk_mk0]

/-- The idele `1` has norm `1`. -/
lemma ideleNorm_one : ideleNorm (1 : IdeleGroup F) = 1 := by
  have h := ideleNorm_mul (1 : IdeleGroup F) 1
  rw [one_mul] at h
  have h0 := (ideleNorm_pos (1 : IdeleGroup F)).ne'
  have h2 : ideleNorm (1 : IdeleGroup F) * 1 =
      ideleNorm (1 : IdeleGroup F) * ideleNorm (1 : IdeleGroup F) := by rw [mul_one]; exact h
  exact (mul_left_cancel₀ h0 h2).symm

/-- **Norm-one representatives of the ideal classes**: there is a map `r` from the class group
to the norm-one ideles with `r 1 = 1` and such that `r c` has ideal class `c`. -/
theorem exists_classRep :
    ∃ r : ClassGroup (𝓞 F) → IdeleGroup F, r 1 = 1 ∧ (∀ c, ideleNorm (r c) = 1) ∧
      ∀ c, ideleIdealClass F (r c) = c := by
  classical
  obtain ⟨φ, hcls, hsurj⟩ := exists_contentHom F
  have hrep : ∀ c : ClassGroup (𝓞 F), ∃ g : IdeleGroup F, ideleNorm g = 1 ∧
      ideleIdealClass F g = c := by
    intro c
    obtain ⟨I, hI⟩ : ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ClassGroup.mk F I = c :=
      ClassGroup.induction (R := 𝓞 F) (P := fun c => ∃ I : (FractionalIdeal (𝓞 F)⁰ F)ˣ,
        ClassGroup.mk F I = c) F (fun I => ⟨I, rfl⟩) c
    obtain ⟨x, hx⟩ := hsurj I
    have hpos : 0 < ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖ := by
      have h := ideleNorm_pos (mkIdele 1 x)
      rw [ideleNorm_mkIdele] at h
      have h1 : (∏ w : InfinitePlace F,
          ‖((1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w‖ ^ w.mult) = 1 := by
        refine Finset.prod_eq_one fun w _ => ?_
        have : ((1 : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) w = 1 := rfl
        rw [this, norm_one, one_pow]
      rw [h1, one_mul] at h
      exact h
    obtain ⟨a, ha⟩ := exists_infiniteUnits_norm_eq (F := F)
      (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : FiniteAdeleRing (𝓞 F) F) v‖)⁻¹ (inv_pos.mpr hpos)
    refine ⟨mkIdele a x, ?_, ?_⟩
    · rw [ideleNorm_mkIdele, ha, inv_mul_cancel₀ hpos.ne']
    · rw [hcls, finPart_mkIdele, hx, hI]
  choose r₀ hr₀n hr₀ using hrep
  refine ⟨fun c => if c = 1 then 1 else r₀ c, by simp, fun c => ?_, fun c => ?_⟩
  · by_cases hc : c = 1
    · simp only [hc, if_true]
      exact ideleNorm_one
    · simp only [hc, if_false]
      exact hr₀n c
  · by_cases hc : c = 1
    · simp only [hc, if_true]
      rw [hcls, map_one, map_one, map_one]
    · simp only [hc, if_false]
      exact hr₀ c

/-- On the ideles that are units at every finite place, the idelic norm is the archimedean
norm. -/
lemma ideleNorm_eq_of_units (g : IdeleGroup F)
    (hg : ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1) :
    ideleNorm g = ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
  unfold ideleNorm
  rw [finprod_eq_one_of_forall_eq_one (fun v => norm_fin_eq_one_of_mem g v
    ((valued_eq_one_iff g v).mp (hg v)).1 ((valued_eq_one_iff g v).mp (hg v)).2), mul_one]

/-- The product formula: a principal idele has idelic norm `1`. -/
lemma ideleNorm_principalIdele (k : Fˣ) : ideleNorm (principalIdele F k) = 1 := by
  have h := NumberField.prod_abs_eq_one (K := F) (x := (k : F)) k.ne_zero
  rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h
  rw [← h]
  unfold ideleNorm
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  congr 1
  exact InfinitePlace.Completion.norm_coe w _

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part G =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH InfinitePlace.Completion Set RiemannMasullo
open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

set_option linter.unusedSectionVars false

/-! ### Ideles with prescribed archimedean part -/

/-- The idele with archimedean part `x` and finite part `1`. -/
def ideleOfInf : (InfiniteAdeleRing F)ˣ →* IdeleGroup F :=
  (MulEquiv.prodUnits (M := InfiniteAdeleRing F) (N := FiniteAdeleRing (𝓞 F) F)).symm.toMonoidHom.comp
    (MonoidHom.inl _ _)

lemma ideleOfInf_snd (x : (InfiniteAdeleRing F)ˣ) :
    ((ideleOfInf x : IdeleGroup F) : AdeleRing (𝓞 F) F).2 = 1 := rfl

lemma infPart_ideleOfInf (x : (InfiniteAdeleRing F)ˣ) : infPart (ideleOfInf x) = x := Units.ext rfl

/-- The ideles that are units at every finite place. -/
def UnitFin : Set (IdeleGroup F) :=
  {g | ∀ v : HeightOneSpectrum (𝓞 F), Valued.v ((g : AdeleRing (𝓞 F) F).2 v) = 1}

lemma valued_mul (g a : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v (((g * a : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v) =
      Valued.v ((g : AdeleRing (𝓞 F) F).2 v) * Valued.v ((a : AdeleRing (𝓞 F) F).2 v) :=
  map_mul _ _ _

lemma ideleOfInf_mem (x : (InfiniteAdeleRing F)ˣ) : ideleOfInf x ∈ UnitFin := by
  intro v
  rw [ideleOfInf_snd]
  exact map_one _

lemma unitFin_mul {g a : IdeleGroup F} (hg : g ∈ UnitFin) (ha : a ∈ UnitFin) :
    g * a ∈ UnitFin := by
  intro v
  rw [valued_mul, hg v, ha v, one_mul]

lemma ideleNorm_ideleOfInf (x : (InfiniteAdeleRing F)ˣ) :
    ideleNorm (ideleOfInf x) = normInf F x :=
  ideleNorm_eq_of_units _ (ideleOfInf_mem x)

lemma ideleNorm_eq_normInf (g : IdeleGroup F) (hg : g ∈ UnitFin) :
    ideleNorm g = normInf F (infPart g) :=
  ideleNorm_eq_of_units g hg

lemma ideleIdealClass_mul_unitFin (g a : IdeleGroup F) (ha : a ∈ UnitFin) :
    ideleIdealClass F (g * a) = ideleIdealClass F g := by
  unfold ideleIdealClass
  congr 1
  funext v
  rw [valued_mul, ha v, mul_one]

/-- The set `A = Ω₀ × ∏_v 𝒪_vˣ`. -/
def Aset : Set (IdeleGroup F) := {g | g ∈ UnitFin ∧ infPart g ∈ OmegaI F}

lemma mem_tateUnit_iff (e : IdeleGroup F) :
    e ∈ tateUnitIdeleDomain F (Units.basisModTorsion F) (w0 F) AlgEquiv.refl ↔
      (∃ k ∈ E0 F, infPart e = (k : (InfiniteAdeleRing F)ˣ)) ∧ e ∈ UnitFin := by
  constructor
  · rintro ⟨⟨k, hk, he⟩, hv⟩
    exact ⟨⟨k, hk, Units.ext he⟩, hv⟩
  · rintro ⟨⟨k, hk, he⟩, hv⟩
    exact ⟨⟨k, hk, congrArg Units.val he⟩, hv⟩

lemma A_mul_sec_inv (a : IdeleGroup F) (ha : a ∈ Aset) :
    a * (ideleOfInf (secI F (ideleNorm a)))⁻¹ ∈
      tateUnitIdeleDomain F (Units.basisModTorsion F) (w0 F) AlgEquiv.refl := by
  have hn : ideleNorm a = normInf F (infPart a) := ideleNorm_eq_normInf a ha.1
  obtain ⟨k, hk, hk_eq⟩ := omega_to_E0 (infPart a) ha.2
  refine (mem_tateUnit_iff _).mpr ⟨⟨k, hk, ?_⟩, unitFin_mul ha.1 ?_⟩
  · rw [map_mul, map_inv, infPart_ideleOfInf, hk_eq, hn]
  · rw [← map_inv]
    exact ideleOfInf_mem _

/-- The domain `D = ⋃_c r_c A`. -/
def Dset (r : ClassGroup (𝓞 F) → IdeleGroup F) : Set (IdeleGroup F) :=
  ⋃ c : ClassGroup (𝓞 F), (fun g => r c * g) '' Aset

/-- The ideles of norm in `[1, e)`. -/
def Nset : Set (IdeleGroup F) := {g | 1 ≤ ideleNorm g ∧ ideleNorm g < Real.exp 1}

lemma ideleNorm_inv (g : IdeleGroup F) : ideleNorm g⁻¹ = (ideleNorm g)⁻¹ := by
  have h := ideleNorm_mul g g⁻¹
  rw [mul_inv_cancel, ideleNorm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma D_sub_N (r : ClassGroup (𝓞 F) → IdeleGroup F) (hrn : ∀ c, ideleNorm (r c) = 1) :
    Dset r ⊆ Nset := by
  intro g hg
  simp only [Dset, mem_iUnion, mem_image] at hg
  obtain ⟨c, a, ha, rfl⟩ := hg
  have h := (sum_Lg_mem_iff (infPart a)).mp ha.2.1
  change 1 ≤ ideleNorm (r c * a) ∧ ideleNorm (r c * a) < Real.exp 1
  rw [ideleNorm_mul, hrn, one_mul, ideleNorm_eq_normInf a ha.1]
  exact ⟨h.1, h.2⟩

lemma N_sub (r : ClassGroup (𝓞 F) → IdeleGroup F) (hr₁ : r 1 = 1)
    (hrn : ∀ c, ideleNorm (r c) = 1) (hr : ∀ c, ideleIdealClass F (r c) = c)
    (g : IdeleGroup F) (hg : g ∈ Nset) : ∃ ξ : Fˣ, principalIdele F ξ * g ∈ Dset r := by
  set t := ideleNorm g with ht_def
  have ht : t ∈ Ico 1 (Real.exp 1) := ⟨hg.1, hg.2⟩
  have ht0 : 0 < t := lt_of_lt_of_le one_pos ht.1
  set S := ideleOfInf (secI F t) with hS
  have hnorm : ideleNorm (g * S⁻¹) = 1 := by
    rw [ideleNorm_mul, ideleNorm_inv, hS, ideleNorm_ideleOfInf, normInf_secI t ht0,
      ← ht_def, mul_inv_cancel₀ ht0.ne']
  obtain ⟨ξ, ⟨e, he, hhe⟩, -⟩ := tateIdeleDomain_existsUnique_principal_mul F
    (Units.basisModTorsion F) (w0 F) AlgEquiv.refl r hr₁ hrn hr (g * S⁻¹) hnorm
  obtain ⟨c, e', he', rfl⟩ := he
  obtain ⟨⟨k, hk, hke⟩, hu⟩ := (mem_tateUnit_iff e').mp he'
  refine ⟨ξ⁻¹, ?_⟩
  simp only [Dset, mem_iUnion, mem_image]
  refine ⟨c, e' * S, ⟨unitFin_mul hu (ideleOfInf_mem _), ?_⟩, ?_⟩
  · rw [map_mul, hS, infPart_ideleOfInf, hke]
    exact (E0_to_omega k hk t ht).1
  · have hg' : g = principalIdele F ξ * (r c * e') * S := by
      rw [← hhe, inv_mul_cancel_right]
    rw [hg', map_inv]
    group

lemma D_injOn (r : ClassGroup (𝓞 F) → IdeleGroup F) (hr₁ : r 1 = 1)
    (hrn : ∀ c, ideleNorm (r c) = 1) (hr : ∀ c, ideleIdealClass F (r c) = c) :
    InjOn (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) (Dset r) := by
  intro g hg g' hg' hgg'
  simp only [Dset, mem_iUnion, mem_image] at hg hg'
  obtain ⟨c, a, ha, rfl⟩ := hg
  obtain ⟨c', a', ha', rfl⟩ := hg'
  obtain ⟨ξ, hξ⟩ := QuotientGroup.eq.mp hgg'
  -- `r c' a' = r c a ξ`
  have hrel : r c' * a' = r c * a * principalIdele F ξ := by
    rw [hξ, mul_inv_cancel_left]
  have hna : ideleNorm a' = ideleNorm a := by
    have h := congrArg ideleNorm hrel
    rwa [ideleNorm_mul, ideleNorm_mul, ideleNorm_mul, hrn, hrn, ideleNorm_principalIdele,
      one_mul, one_mul, mul_one] at h
  set t := ideleNorm a with ht_def
  set S := ideleOfInf (secI F t) with hS
  have hnorm : ideleNorm (r c' * a' * S⁻¹) = 1 := by
    have hpos : 0 < t := ideleNorm_pos a
    rw [ideleNorm_mul, ideleNorm_mul, hrn, one_mul, hna, ideleNorm_inv, hS, ideleNorm_ideleOfInf,
      normInf_secI t hpos, mul_inv_cancel₀ hpos.ne']
  obtain ⟨ξ₀, -, huniq⟩ := tateIdeleDomain_existsUnique_principal_mul F
    (Units.basisModTorsion F) (w0 F) AlgEquiv.refl r hr₁ hrn hr (r c' * a' * S⁻¹) hnorm
  have h1 : (1 : Fˣ) = ξ₀ := by
    refine huniq 1 ⟨r c' * (a' * S⁻¹), ⟨c', a' * S⁻¹, ?_, rfl⟩, ?_⟩
    · have := A_mul_sec_inv a' ha'
      rwa [hna] at this
    · rw [map_one, one_mul, mul_assoc]
  have h2 : ξ = ξ₀ := by
    refine huniq ξ ⟨r c * (a * S⁻¹), ⟨c, a * S⁻¹, A_mul_sec_inv a ha, rfl⟩, ?_⟩
    rw [hrel, mul_comm (r c * a) (principalIdele F ξ)]
    group
  have hξ1 : ξ = 1 := h2.trans h1.symm
  rw [hrel, hξ1, map_one, mul_one]

lemma D_disjoint (r : ClassGroup (𝓞 F) → IdeleGroup F) (hr : ∀ c, ideleIdealClass F (r c) = c) :
    Pairwise (Function.onFun Disjoint fun c : ClassGroup (𝓞 F) =>
      (fun g => r c * g) '' (Aset : Set (IdeleGroup F))) := by
  intro c c' hne
  rw [Function.onFun, Set.disjoint_left]
  rintro _ ⟨a, ha, rfl⟩ ⟨a', ha', h⟩
  apply hne
  have := congrArg (ideleIdealClass F) h
  rwa [ideleIdealClass_mul_unitFin _ _ ha.1, ideleIdealClass_mul_unitFin _ _ ha'.1, hr, hr,
    eq_comm] at this

/-! ### Measurability -/

lemma isOpen_unitFin : IsOpen (UnitFin : Set (IdeleGroup F)) := by
  have hO := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => Valued.isOpen_valuationSubring _) (p := fun _ => True)
  have hO' : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), True →
      x.2 v ∈ v.adicCompletionIntegers F} := hO.preimage continuous_snd
  have hset : (UnitFin : Set (IdeleGroup F)) =
      (Units.val ⁻¹' {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), True →
        x.2 v ∈ v.adicCompletionIntegers F}) ∩
      ((fun g : IdeleGroup F => ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F)) ⁻¹'
        {x : AdeleRing (𝓞 F) F | ∀ v : HeightOneSpectrum (𝓞 F), True →
          x.2 v ∈ v.adicCompletionIntegers F}) := by
    ext g
    simp only [UnitFin, mem_ofPred_eq, mem_inter_iff, mem_preimage, forall_const]
    constructor
    · intro h
      exact ⟨fun v => ((valued_eq_one_iff g v).mp (h v)).1,
        fun v => ((valued_eq_one_iff g v).mp (h v)).2⟩
    · rintro ⟨h1, h2⟩ v
      exact (valued_eq_one_iff g v).mpr ⟨h1 v, h2 v⟩
  rw [hset]
  exact (hO'.preimage Units.continuous_val).inter (hO'.preimage Units.continuous_coe_inv)

lemma continuous_eInf : Continuous (eInf (F := F)) :=
  (ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).continuous

lemma continuous_infPart : Continuous (infPart : IdeleGroup F → (InfiniteAdeleRing F)ˣ) :=
  Units.continuous_map (f := (RingHom.fst (InfiniteAdeleRing F)
    (FiniteAdeleRing (𝓞 F) F)).toMonoidHom) continuous_fst

lemma measurableSet_A : MeasurableSet (Aset : Set (IdeleGroup F)) := by
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := w.Completion)).isEmbedding.secondCountableTopology
  have hc : Continuous (fun g : IdeleGroup F => eInf (infPart g)) :=
    continuous_eInf.comp continuous_infPart
  have hset : (Aset : Set (IdeleGroup F)) = UnitFin ∩
      (fun g : IdeleGroup F => eInf (infPart g)) ⁻¹' ((eInf (F := F)).symm ⁻¹' OmegaI F) := by
    ext g
    simp [Aset]
  rw [hset]
  exact isOpen_unitFin.measurableSet.inter (measurableSet_omega.preimage hc.measurable)

/-! ### The global count -/

/-- `μ̄(C_F¹-shell) = h_F · μ(A)`. -/
theorem count (r : ClassGroup (𝓞 F) → IdeleGroup F) (hr₁ : r 1 = 1)
    (hrn : ∀ c, ideleNorm (r c) = 1) (hr : ∀ c, ideleIdealClass F (r c) = c) :
    ENNReal.ofReal (tamagawaClassVolume F) =
      (classNumber F : ℝ≥0∞) * tamagawaIdele F Aset := by
  have WD := tamagawa_measures_wellDefined F
  have hH : (tamagawaIdele F).IsHaarMeasure := WD.2.1.1
  have hinj := WD.2.1.2.1
  have hnorm := WD.1.2.1
  have hmeasD : ∀ c : ClassGroup (𝓞 F),
      MeasurableSet ((fun g => r c * g) '' (Aset : Set (IdeleGroup F))) := by
    intro c
    rw [Set.image_mul_left]
    exact measurableSet_A.preimage (measurable_const_mul _)
  have hDm : MeasurableSet (Dset r) := MeasurableSet.iUnion hmeasD
  have himg : (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' Dset r =
      (QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' Nset := by
    refine subset_antisymm (image_mono (D_sub_N r hrn)) ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨ξ, hξ⟩ := N_sub r hr₁ hrn hr g hg
    refine ⟨_, hξ, QuotientGroup.eq.mpr ?_⟩
    rw [mul_inv_rev, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul, ← map_inv]
    exact ⟨ξ⁻¹, rfl⟩
  rw [← hnorm]
  change tamagawaIdeleClass F ((QuotientGroup.mk : IdeleGroup F → IdeleClassGroup F) '' Nset) = _
  rw [← himg, ← hinj _ hDm (D_injOn r hr₁ hrn hr), Dset,
    measure_iUnion (D_disjoint r hr) hmeasD]
  simp_rw [Set.image_mul_left, measure_preimage_mul]
  rw [ENNReal.tsum_const, ENat.card_eq_coe_natCard, ENat.toENNReal_coe, Nat.card_eq_fintype_card]
  rfl

end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part H =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH InfinitePlace.Completion Set RiemannMasullo
open scoped WithZero

noncomputable section

variable (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))

set_option linter.unusedSectionVars false

/-! ### `μ_S` as a product measure -/

/-- The coordinates of an `S`-idele: `GL₁(𝔸_{F,S}) ≃ ∏_{w ∣ ∞} F_wˣ × ∏_{v ∈ S_f} F_vˣ`. -/
def coordEquiv : SIdeleGroup F Sf ≃*
    ((w : InfinitePlace F) → w.Completionˣ) ×
      ((v : Sf) → ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ) :=
  (MulEquiv.prodUnits (M := (w : InfinitePlace F) → w.Completion)
      (N := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).trans
    (MulEquiv.prodCongr MulEquiv.piUnits MulEquiv.piUnits)

theorem continuous_coordEquiv : Continuous (coordEquiv F Sf) :=
  ((ContinuousMulEquiv.piUnits (M := fun w : InfinitePlace F => w.Completion)).continuous.prodMap
    (ContinuousMulEquiv.piUnits
      (M := fun v : Sf => (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous).comp
    (Homeomorph.prodUnits (α := (w : InfinitePlace F) → w.Completion)
      (β := (v : Sf) → (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)).continuous

/-- `μ_S` is carried by the coordinates to the product of the local multiplicative measures. -/
theorem map_coordEquiv :
    (sMultiplicativeTamagawa F Sf).map (coordEquiv F Sf) =
      (Measure.pi (infiniteLocalMulTamagawa F)).prod
        (Measure.pi fun v : Sf => finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F))) := by
  have hsc_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have hsc_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  have hscu_inf : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := w.Completion)).isEmbedding.secondCountableTopology
  have hscu_fin : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F)ˣ :=
    fun v => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := v.adicCompletion F)).isEmbedding.secondCountableTopology
  have hinf : ∀ w : InfinitePlace F, (infiniteLocalMulTamagawa F w).IsHaarMeasure :=
    fun w => infiniteLocalMulTamagawa_isHaarMeasure F w
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), (finiteLocalMulTamagawa F v).IsHaarMeasure :=
    fun v => (finiteLocalMulTamagawa_isHaarMeasure_and_units F v).1
  have hsf_inf : ∀ w : InfinitePlace F, SigmaFinite (infiniteLocalMulTamagawa F w) :=
    fun w => inferInstance
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (finiteLocalMulTamagawa F v) :=
    fun v => inferInstance
  have hme : Measurable (coordEquiv F Sf) := (continuous_coordEquiv F Sf).measurable
  symm
  refine Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    (Measure.FiniteSpanningSetsIn.pi fun w => (infiniteLocalMulTamagawa F w).toFiniteSpanningSetsIn)
    (Measure.FiniteSpanningSetsIn.pi fun v : Sf =>
      (finiteLocalMulTamagawa F (v : HeightOneSpectrum (𝓞 F))).toFiniteSpanningSetsIn) ?_
  rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
  have hA' : ∀ w, MeasurableSet (A w) := fun w => hA w (Set.mem_univ w)
  have hB' : ∀ v, MeasurableSet (B v) := fun v => hB v (Set.mem_univ v)
  rw [Measure.map_apply hme ((MeasurableSet.univ_pi hA').prod (MeasurableSet.univ_pi hB')),
    Measure.pi_pi, Measure.pi_pi,
    ← (sMultiplicativeTamagawa_isHaarMeasure_and_rectangle F Sf).2 A B hA' hB']
  congr 1
  ext g
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun w => ⟨_, h1 w (Set.mem_univ w), rfl⟩, fun v => ⟨_, h2 v (Set.mem_univ v), rfl⟩⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun w _ => ?_, fun v _ => ?_⟩
    · obtain ⟨a, ha, hag⟩ := h1 w
      have : a = (coordEquiv F Sf g).1 w := Units.ext hag
      exact this ▸ ha
    · obtain ⟨b, hb, hbg⟩ := h2 v
      have : b = (coordEquiv F Sf g).2 v := Units.ext hbg
      exact this ▸ hb

/-- The test set `B_S = Ω₀ × ∏_{v ∈ S_f} 𝒪_vˣ` in `GL₁(𝔸_{F,S})`. -/
def testSet : Set (SIdeleGroup F Sf) :=
  coordEquiv F Sf ⁻¹' (((eInf (F := F)).symm ⁻¹' OmegaI F) ×ˢ
    Set.univ.pi fun v : Sf =>
      {u : ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ |
        Valued.v (u : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) = 1})

theorem valued_units_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ) :
    Valued.v (u : v.adicCompletion F) = 1 ↔
      (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
        ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
  have hm : Valued.v (u : v.adicCompletion F) *
      Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hm
    exact ⟨h.le, hm.le⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    calc (1 : ℤᵐ⁰) = Valued.v (u : v.adicCompletion F) *
          Valued.v ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) := hm.symm
      _ ≤ Valued.v (u : v.adicCompletion F) * 1 := mul_le_mul' le_rfl h2
      _ = _ := mul_one _

theorem measurableSet_units_one (v : HeightOneSpectrum (𝓞 F)) :
    MeasurableSet {u : (v.adicCompletion F)ˣ | Valued.v (u : v.adicCompletion F) = 1} := by
  have hO : IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    Valued.isOpen_valuationSubring _
  have hset : {u : (v.adicCompletion F)ˣ | Valued.v (u : v.adicCompletion F) = 1} =
      (Units.val ⁻¹' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∩
      ((fun u : (v.adicCompletion F)ˣ => ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)) ⁻¹'
        (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
    ext u
    exact valued_units_eq_one_iff F v u
  rw [hset]
  exact ((hO.preimage Units.continuous_val).inter (hO.preimage Units.continuous_coe_inv)).measurableSet

theorem measurableSet_testSet : MeasurableSet (testSet F Sf) := by
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := w.Completion)).isEmbedding.secondCountableTopology
  have : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F)ˣ :=
    fun v => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := v.adicCompletion F)).isEmbedding.secondCountableTopology
  exact (measurableSet_omega.prod (MeasurableSet.univ_pi fun v : Sf =>
    measurableSet_units_one F (v : HeightOneSpectrum (𝓞 F)))).preimage
    (continuous_coordEquiv F Sf).measurable

theorem sMul_testSet :
    sMultiplicativeTamagawa F Sf (testSet F Sf) =
      muInf F ((eInf (F := F)).symm ⁻¹' OmegaI F) *
        ∏ v : Sf, (ENNReal.ofReal (Real.sqrt ((Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal : ℝ) ^
          multiplicity (v : HeightOneSpectrum (𝓞 F)).asIdeal (differentIdeal ℤ (𝓞 F)))))⁻¹ := by
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completion :=
    secondCountable_infinite F
  have : ∀ w : InfinitePlace F, SecondCountableTopology w.Completionˣ :=
    fun w => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := w.Completion)).isEmbedding.secondCountableTopology
  have : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F) :=
    secondCountable_finite F
  have : ∀ v : HeightOneSpectrum (𝓞 F), SecondCountableTopology (v.adicCompletion F)ˣ :=
    fun v => (IsOpenUnits.isOpenEmbedding_unitsVal
      (M := v.adicCompletion F)).isEmbedding.secondCountableTopology
  have hlc_fin : ∀ v : HeightOneSpectrum (𝓞 F), LocallyCompactSpace (v.adicCompletion F) :=
    fun v => RiemannMasullo.locallyCompactSpace_adicCompletion v
  have hfin : ∀ v : HeightOneSpectrum (𝓞 F), (finiteLocalMulTamagawa F v).IsHaarMeasure :=
    fun v => (finiteLocalMulTamagawa_isHaarMeasure_and_units F v).1
  have hsf_fin : ∀ v : HeightOneSpectrum (𝓞 F), SigmaFinite (finiteLocalMulTamagawa F v) :=
    fun v => inferInstance
  have hinf : ∀ w : InfinitePlace F, (infiniteLocalMulTamagawa F w).IsHaarMeasure :=
    fun w => infiniteLocalMulTamagawa_isHaarMeasure F w
  have hsf_inf : ∀ w : InfinitePlace F, SigmaFinite (infiniteLocalMulTamagawa F w) :=
    fun w => inferInstance
  have hm : MeasurableSet (((eInf (F := F)).symm ⁻¹' OmegaI F) ×ˢ
      Set.univ.pi fun v : Sf =>
        {u : ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)ˣ |
          Valued.v (u : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) = 1}) :=
    measurableSet_omega.prod (MeasurableSet.univ_pi fun v =>
      measurableSet_units_one F (v : HeightOneSpectrum (𝓞 F)))
  rw [testSet, ← Measure.map_apply (continuous_coordEquiv F Sf).measurable hm, map_coordEquiv,
    Measure.prod_prod, Measure.pi_pi]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  exact (finiteLocalMulTamagawa_isHaarMeasure_and_units F (v : HeightOneSpectrum (𝓞 F))).2

theorem targetSet_testSet :
    {g : IdeleGroup F | g ∈ sIntegralIdeles Sf ∧
          ∃ b ∈ testSet F Sf, (b : SAdeleRing F Sf) =
            ((g : AdeleRing (𝓞 F) F).1,
              fun v : Sf => (g : AdeleRing (𝓞 F) F).2 (v : HeightOneSpectrum (𝓞 F)))} =
      Aset := by
  rw [targetSet_eq]
  ext g
  have h1 : (eInf (F := F)).symm (coordEquiv F Sf (pU F Sf g)).1 = infPart g := Units.ext rfl
  simp only [mem_ofPred_eq, testSet, mem_preimage, mem_prod, mem_univ_pi, h1]
  constructor
  · rintro ⟨hout, hΩ, hin⟩
    refine ⟨fun v => ?_, hΩ⟩
    by_cases hv : v ∈ Sf
    · exact hin ⟨v, hv⟩
    · exact hout v hv
  · rintro ⟨hall, hΩ⟩
    exact ⟨fun v _ => hall v, hΩ, fun v => hall v⟩

end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa


-- ===== part I =====

open MeasureTheory NumberField IsDedekindDomain
open scoped ENNReal NNReal

set_option autoImplicit false
set_option maxSynthPendingDepth 8

namespace Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH

noncomputable section

theorem final (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Set (SIdeleGroup F Sf)) (hB : MeasurableSet B) :
    tamagawaIdele F
        {g : IdeleGroup F | g ∈ sIntegralIdeles Sf ∧
          ∃ b ∈ B, (b : SAdeleRing F Sf) =
            ((g : AdeleRing (𝓞 F) F).1,
              fun v : Sf => (g : AdeleRing (𝓞 F) F).2 (v : HeightOneSpectrum (𝓞 F)))} =
      sMultiplicativeTamagawa F Sf B *
        ((ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
          ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) := by
  obtain ⟨r, hr₁, hrn, hr⟩ := exists_classRep (F := F)
  have hcount := count r hr₁ hrn hr
  obtain ⟨c, hc⟩ := stepA F Sf
  have hA : tamagawaIdele F Aset = c * sMultiplicativeTamagawa F Sf (testSet F Sf) := by
    rw [← targetSet_testSet F Sf]
    exact hc _ (measurableSet_testSet F Sf)
  rw [sMul_testSet] at hA
  have hM := muInf_omega (F := F)
  set M := muInf F ((eInf (F := F)).symm ⁻¹' OmegaI F) with hM_def
  set q : HeightOneSpectrum (𝓞 F) → ℝ≥0∞ := fun v => ENNReal.ofReal (Real.sqrt
    ((Ideal.absNorm v.asIdeal : ℝ) ^ multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F)))) with hq
  set X := ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|) with hX
  set Q := ∏ v ∈ Sf, q v with hQ
  set W := (Units.torsionOrder F : ℝ≥0∞) with hW
  set H := (classNumber F : ℝ≥0∞) with hH
  set a : ℝ := (2 : ℝ) ^ InfinitePlace.nrRealPlaces F *
    (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F * Units.regulator F with ha
  have hqpos : ∀ v : HeightOneSpectrum (𝓞 F), 0 < q v := by
    intro v
    have hn : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) :=
      Nat.cast_pos.mpr (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v))
    exact ENNReal.ofReal_pos.mpr (Real.sqrt_pos_of_pos (pow_pos hn _))
  have hQinv : ∏ v : Sf, (q (v : HeightOneSpectrum (𝓞 F)))⁻¹ = Q⁻¹ := by
    rw [hQ, ENNReal.prod_inv_distrib (fun _ _ _ _ _ => Or.inr ENNReal.ofReal_ne_top),
      ← Finset.prod_coe_sort Sf (fun v => (q v)⁻¹)]
  rw [hQinv] at hA
  -- the archimedean constant
  have hapos : 0 < a := by
    have := Units.regulator_pos F
    have := Real.pi_pos
    positivity
  have hd : 0 < Real.sqrt |(discr F : ℝ)| :=
    Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero F)))
  have hw : (0 : ℝ) < (Units.torsionOrder F : ℝ) := by
    exact_mod_cast Units.torsionOrder_pos F
  have hvolpos : 0 < tamagawaClassVolume F := dedekindZeta_residue_pos F
  have hreal : tamagawaClassVolume F * ((Units.torsionOrder F : ℝ) * Real.sqrt |(discr F : ℝ)|) =
      a * (classNumber F : ℝ) := by
    rw [tamagawaClassVolume, dedekindZeta_residue_def, ha]
    field_simp
  have e1 : ENNReal.ofReal (tamagawaClassVolume F) * (W * X) = ENNReal.ofReal a * H := by
    rw [hW, hH, hX, ← ENNReal.ofReal_natCast (Units.torsionOrder F),
      ← ENNReal.ofReal_natCast (classNumber F), ← ENNReal.ofReal_mul hw.le,
      ← ENNReal.ofReal_mul hvolpos.le, ← ENNReal.ofReal_mul hapos.le, hreal]
  -- nonvanishing and finiteness
  have hH0 : H ≠ 0 := by
    rw [hH]
    exact_mod_cast (classNumber_pos F).ne'
  have hHt : H ≠ ⊤ := ENNReal.natCast_ne_top _
  have hW0 : W ≠ 0 := by
    rw [hW]
    exact_mod_cast (Units.torsionOrder_pos F).ne'
  have hWt : W ≠ ⊤ := ENNReal.natCast_ne_top _
  have hM0 : M ≠ 0 := by
    intro h
    rw [h, mul_zero] at hM
    exact (ENNReal.ofReal_pos.mpr hapos).ne' hM.symm
  have hMt : M ≠ ⊤ := by
    intro h
    rw [h, ENNReal.mul_top hW0] at hM
    exact ENNReal.ofReal_ne_top hM.symm
  have hX0 : X ≠ 0 := (ENNReal.ofReal_pos.mpr hd).ne'
  have hXt : X ≠ ⊤ := ENNReal.ofReal_ne_top
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.mpr fun v _ => (hqpos v).ne'
  have hQt : Q ≠ ⊤ := ENNReal.prod_ne_top fun v _ => ENNReal.ofReal_ne_top
  -- solving for the constant
  have E1 : H * ((c : ℝ≥0∞) * (M * Q⁻¹)) * (W * X) = W * M * H := by
    rw [← hA, ← hcount, e1, ← hM]
  have E2 : (H * W * M) * ((c : ℝ≥0∞) * Q⁻¹ * X) = (H * W * M) * 1 := by
    calc (H * W * M) * ((c : ℝ≥0∞) * Q⁻¹ * X) = H * ((c : ℝ≥0∞) * (M * Q⁻¹)) * (W * X) := by ring
      _ = W * M * H := E1
      _ = (H * W * M) * 1 := by ring
  have hHWM0 : H * W * M ≠ 0 := mul_ne_zero (mul_ne_zero hH0 hW0) hM0
  have hHWMt : H * W * M ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hHt hWt) hMt
  have E3 : (c : ℝ≥0∞) * Q⁻¹ * X = 1 := (ENNReal.mul_right_inj hHWM0 hHWMt).mp E2
  have hcX : (c : ℝ≥0∞) = X⁻¹ * Q := by
    calc (c : ℝ≥0∞) = c * (Q⁻¹ * Q) * (X * X⁻¹) := by
          rw [ENNReal.inv_mul_cancel hQ0 hQt, ENNReal.mul_inv_cancel hX0 hXt, mul_one, mul_one]
      _ = ((c : ℝ≥0∞) * Q⁻¹ * X) * (X⁻¹ * Q) := by ring
      _ = X⁻¹ * Q := by rw [E3, one_mul]
  rw [hc B hB, hcX, mul_comm]

end

end Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa

open MasulloGRH Sol_MasulloGRH_tamagawaIdele_sIntegralIdeles_eq_sMultiplicativeTamagawa in
theorem solution
    (F : Type*) [Field F] [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F)))
    (B : Set (SIdeleGroup F Sf)) (hB : MeasurableSet B) :
    tamagawaIdele F
        {g : IdeleGroup F | g ∈ sIntegralIdeles Sf ∧
          ∃ b ∈ B, (b : SAdeleRing F Sf) =
            ((g : AdeleRing (𝓞 F) F).1,
              fun v : Sf => (g : AdeleRing (𝓞 F) F).2 (v : HeightOneSpectrum (𝓞 F)))} =
      sMultiplicativeTamagawa F Sf B *
        ((ENNReal.ofReal (Real.sqrt |(discr F : ℝ)|))⁻¹ *
          ∏ v ∈ Sf, ENNReal.ofReal (Real.sqrt ((Ideal.absNorm v.asIdeal : ℝ) ^
            multiplicity v.asIdeal (differentIdeal ℤ (𝓞 F))))) :=
  final F Sf B hB

