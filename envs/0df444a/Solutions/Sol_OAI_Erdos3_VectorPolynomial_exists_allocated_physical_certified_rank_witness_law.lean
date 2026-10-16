-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocated_physical_certified_rank_witness_law
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-16T02:53:35.558027+00:00
-- url     : https://prove2.me/submissions/4c70e6f2-64ed-44f9-8570-71e592611441

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B050
import Definitions.Def_OAIErdos3B158
import Definitions.Def_OAIErdos3B1374
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_spatial_witness_comparison

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SigmaProductMeasure
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem sigmaProductMeasure_flatten {D : Type*} [Fintype D] {I : D → Type*}
    [∀ d, Fintype (I d)] {X : (Σ d, I d) → Type*}
    [∀ s, MeasurableSpace (X s)] (μ : ∀ s, Measure (X s)) [∀ s, IsProbabilityMeasure (μ s)] :
    (Measure.pi (fun d => Measure.pi (fun i => μ ⟨d, i⟩))).map
      (fun x (s : Σ d, I d) => x s.1 s.2) = Measure.pi μ := by
  have hm : Measurable (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) :=
    measurable_pi_iff.mpr (fun index =>
      (measurable_pi_apply index.2).comp (measurable_pi_apply index.1))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : (fun (x : ∀ d i, X ⟨d, i⟩) (s : Σ d, I d) => x s.1 s.2) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun d => Set.univ.pi (fun i => s ⟨d, i⟩)) := by
    ext x
    constructor
    · intro hx d _ i _
      exact hx ⟨d, i⟩ (Set.mem_univ _)
    · intro hx t _
      exact hx t.1 (Set.mem_univ _) t.2 (Set.mem_univ _)
  rw [he, Measure.pi_pi]
  simp only [Measure.pi_pi, Fintype.prod_sigma]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem pmf_bind_pair_apply {X Y : Type*} (p : PMF X) (q : PMF Y) (z : X × Y) :
    (p.bind (fun x => q.map (fun y => (x, y)))) z = p z.1 * q z.2 := by
  rw [PMF.bind_apply, tsum_eq_single z.1]
  · congr 1
    exact pmf_map_injective_at q (fun y => (z.1, y))
      (fun _ _ h => congrArg Prod.snd h) z.2
  · intro x hx
    have hr : z ∉ Set.range (fun y => (x, y)) := by
      rintro ⟨y, he⟩
      exact hx (congrArg Prod.fst he)
    rw [pmf_map_zero_off_range _ _ _ hr, mul_zero]

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedCoefficientIntegerMarginal
namespace OAI

section

namespace Erdos3
open MeasureTheory

theorem mixedScalarArrayLaw_integer_marginal {I Z Q : Type*}
    [Fintype I] [Fintype Z] [Fintype Q]
    (c w : I → Q → ℝ) (hw : ∀ i q, 0 < w i q) (p : Z → Q → PMF ℤ) :
    MeasurePreserving Prod.snd (mixedScalarArrayLaw c w p)
      (Measure.pi (fun z => Measure.pi (fun q => (p z q).toMeasure))) := by
  let : ∀ i q, IsProbabilityMeasure (affineCoefficientMeasure (c i q) (w i q)) :=
    fun i q => affineCoefficientMeasure_probability _ (hw i q)
  exact measurePreserving_snd

theorem pmf_bind_pair_toMeasure {X Y : Type*} [Countable X] [Countable Y]
    [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (p : PMF X) (q : PMF Y) :
    (p.bind (fun x => q.map (fun y => (x, y)))).toMeasure = p.toMeasure.prod q.toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨x, y⟩
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), pmf_bind_pair_apply,
    ← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

namespace VectorPolynomial
open Module Submodule
open scoped BigOperators Classical

theorem coefficientIntegerScalars_measurePreserving {K : Type*} [Fintype K] {m : ℕ}
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (hw : ∀ j i q, 0 < w j i q)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ) :
    MeasurePreserving coefficientIntegerScalars
      (Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
      (Measure.pi (fun q : CoefficientIntegerScalarIndex K n => (p q.1 q.2.2 q.2.1).toMeasure)) := by
  let μ := fun q : CoefficientIntegerScalarIndex K n => (p q.1 q.2.2 q.2.1).toMeasure
  have hrow (j : Fin m) : MeasurePreserving
      (fun a : (I j → BoundedCoefficientExponent K (j.val + 1) → ℝ) ×
        (Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℤ) =>
          fun q : BoundedCoefficientExponent K (j.val + 1) × Fin (n j) => a.2 q.2 q.1)
      (mixedScalarArrayLaw (c j) (w j) (p j))
      (Measure.pi (fun q => μ ⟨j, q⟩)) := by
    exact ((finiteArray_uncurry_measurePreserving (fun q i => (p j i q).toMeasure)).comp
      (finiteArrayTranspose_measurePreserving (fun i q => (p j i q).toMeasure))).comp
        (mixedScalarArrayLaw_integer_marginal (c j) (w j) (hw j) (p j))
  have houter := measurePreserving_pi
    (fun j => mixedScalarArrayLaw (c j) (w j) (p j))
    (fun j => Measure.pi (fun q => μ ⟨j, q⟩)) hrow
  have hflat : MeasurePreserving
      (fun (x : ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) × Fin (n j) → ℤ)
        (q : CoefficientIntegerScalarIndex K n) => x q.1 q.2)
      (Measure.pi (fun j => Measure.pi (fun q => μ ⟨j, q⟩))) (Measure.pi μ) :=
    ⟨measurable_pi_iff.mpr (fun q => (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)),
      sigmaProductMeasure_flatten μ⟩
  exact hflat.comp houter

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedCoefficientSource_integer_measurePreserving :
    MeasurePreserving coefficientIntegerScalars
      (allocatedCoefficientSource B U b hR hσ S)
      (allocatedCoefficientIntegerPMF B U b hR hσ S).toMeasure := by
  simpa only [allocatedCoefficientSource, allocatedCoefficientIntegerPMF,
    independentProductPMF, Measure.toPMF_toMeasure] using
    coefficientIntegerScalars_measurePreserving
      (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerWidths_pos B U b hR hσ S) (allocatedLayerIntegerPMFs B U b hR hσ S)

theorem allocatedCoefficientSource_integer_prod_measurePreserving
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck) :
    MeasurePreserving (Prod.map coefficientIntegerScalars id)
      ((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
      ((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => (a, deck)))).toMeasure := by
  let : IsProbabilityMeasure (allocatedCoefficientSource B U b hR hσ S) :=
    allocatedCoefficientSource_probability B U b hR hσ S
  rw [pmf_bind_pair_toMeasure]
  exact (allocatedCoefficientSource_integer_measurePreserving B U b hR hσ S).prod
    (MeasurePreserving.id q.toMeasure)

theorem allocatedCoefficientSource_integer_prod_eventProbability
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (E : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → Prop) :
    (((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
      {a | E (coefficientIntegerScalars a.1) a.2}).toReal =
      (((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => decide (E a deck)))) true).toReal := by
  let p := (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
    (fun a => q.map (fun deck => (a, deck)))
  let obs := fun a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck =>
    decide (E a.1 a.2)
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  have hset :
      ((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
        {a | E (coefficientIntegerScalars a.1) a.2} = p.toMeasure {a | E a.1 a.2} := by
    rw [← hp.map_eq, Measure.map_apply hp.measurable (Set.to_countable _).measurableSet]
    rfl
  have hobs : (p.map obs) true = p.toMeasure {a | E a.1 a.2} := by
    rw [← PMF.toMeasure_apply_singleton _ true (measurableSet_singleton _),
      ← PMF.toMeasure_map _ _ (measurable_of_countable _),
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
    congr 1
    ext a
    simp [obs]
  rw [hset, ← hobs]
  congr 1
  simp only [p, PMF.map_bind, PMF.map_comp, obs, Function.comp_def]

theorem allocatedCoefficientSource_integer_prod_indicator
    {Deck : Type*} [Countable Deck] [MeasurableSpace Deck] [MeasurableSingletonClass Deck]
    (q : PMF Deck)
    (E : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) → Deck → Prop) :
    (∫ a, (if E (coefficientIntegerScalars a.1) a.2 then (1 : ℝ) else 0)
      ∂(allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) =
      (((allocatedCoefficientIntegerPMF B U b hR hσ S).bind
        (fun a => q.map (fun deck => decide (E a deck)))) true).toReal := by
  have hp := allocatedCoefficientSource_integer_prod_measurePreserving B U b hR hσ S q
  have hs : MeasurableSet
      {a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n × Deck |
        E (coefficientIntegerScalars a.1) a.2} :=
    (Set.to_countable {a : (CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ) × Deck |
      E a.1 a.2}).measurableSet.preimage hp.measurable
  calc
    _ = (((allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure)
        {a | E (coefficientIntegerScalars a.1) a.2}).toReal := by
      simpa only [Set.indicator, Set.mem_ofPred_eq, Pi.one_apply, Measure.real] using
        integral_indicator_one (μ := (allocatedCoefficientSource B U b hR hσ S).prod q.toMeasure) hs
    _ = _ := allocatedCoefficientSource_integer_prod_eventProbability B U b hR hσ S q E

end VectorPolynomial
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedSpatialCoefficientReferenceLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type*} [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedSpatialCoefficientReferenceLaw
    {X : Type*} [Fintype X] (q : ℕ) [NeZero q]
    (spatial : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ))
    (deck : PMF (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q))
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop) :
    (∑' z, (spatial z).toReal *
      ∫ a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
        (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q a.1 a.2)
          then (1 : ℝ) else 0)
        ∂(allocatedCoefficientSource B U b hR hσ S).prod deck.toMeasure) =
    ((spatial.bind fun z => (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      fun a => deck.map fun r => decide
        (event (fun v => (z v : ZMod q)) (coefficientIntegerDeckChartResidues q a r))) true).toReal := by
  rw [pmf_bind_toReal]
  apply tsum_congr
  intro z
  congr 1
  exact allocatedCoefficientSource_integer_prod_indicator B U b hR hσ S deck
    (fun a r => event (fun v => (z v : ZMod q)) (coefficientIntegerDeckChartResidues q a r))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedShortRankWitnessWidth
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_sampler_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (f : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (hinteger : ∀ (j : Fin m) (i : Fin (n j))
      (q : BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)),
      allocatedReadProjection f ⟨j,Sum.inr i⟩ q = (x j).2 i q) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun q => ((allocatedReadNoise f q : ℤ) : ZMod M))
      (coefficientSamplerChartResidues M x (fun j q i => ((allocatedReadDeck f j q i : ℤ) : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val) f := by
  rw [← allocatedReadCoefficientChartResidues_sampler M f x hinteger]
  exact allocatedChartResiduePrimePowerWitness_iff_actual inactive spatial kernel block C P A M hdiv f

theorem allocatedChartResiduePrimePowerWitness_mixedArray_iff_actual
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (M : ℕ) (hdiv : ∀ p : P, p.val ^ A p.val ∣ M)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (x : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (deck : ∀ j, BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun q => (noise q : ZMod M))
      (coefficientSamplerChartResidues M x (fun j q i => (deck j q i : ZMod M))) ↔
      ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
        (allocatedMixedFullArray
          (Sum.elim noise (fun ⟨j,q,i⟩ => (x j).2 i q))
          (fun ⟨j,q,i⟩ => deck j q i) continuous) := by
  exact allocatedChartResiduePrimePowerWitness_sampler_iff_actual
    inactive spatial kernel block C P A M hdiv
    (allocatedMixedFullArray
      (Sum.elim noise (fun ⟨j,q,i⟩ => (x j).2 i q))
      (fun ⟨j,q,i⟩ => deck j q i) continuous) x (fun _ _ _ => rfl)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}
variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

theorem allocatedChartResiduePrimePowerWitness_integerDeck_iff
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (q : ℕ) [NeZero q] (hdiv : ∀ p : P, p.val ^ A p.val ∣ q)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (a : CoefficientIntegerScalarIndex (LayerSamplerVariables G I n B) n → ℤ)
    (r : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q) :
    allocatedChartResiduePrimePowerWitness inactive C P A q hdiv
      (fun v => (noise v : ZMod q)) (coefficientIntegerDeckChartResidues q a r) ↔
    ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
      (allocatedMixedFullArray (Sum.elim noise a)
        (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)) := by
  let f := allocatedMixedFullArray (Sum.elim noise a)
    (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)
  have hchart : allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)) =
      coefficientIntegerDeckChartResidues q a r := by
    funext j e i
    cases i with
    | inl i => rfl
    | inr i =>
      change (((r j e i).val : ℤ) : ZMod q) = r j e i
      simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h := allocatedChartResiduePrimePowerWitness_iff_actual
    inactive spatial kernel block C P A q hdiv f
  rw [hchart] at h
  exact h

variable (B) {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)

theorem allocatedSpatialRankReferenceLaw
    (inactive : LayerSamplerAxis I n → Prop)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,b.val⟩)
    (C : ℝ) (P : Finset ℕ) [∀ p : P, NeZero p.val] (A : ℕ → ℕ)
    (q : ℕ) [NeZero q] (hdiv : ∀ p : P, p.val ^ A p.val ∣ q)
    (noiseLaw : PMF (Option (LayerSamplerVariables G I n B) × X → ℤ)) :
    (∑' z, (noiseLaw z).toReal *
      ∫ a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
          CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
        (if allocatedChartResiduePrimePowerWitness inactive C P A q hdiv
          (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q a.1 a.2)
          then (1 : ℝ) else 0)
        ∂(allocatedCoefficientSource B U b hR hσ S).prod
          (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure) =
    ((noiseLaw.bind fun z => (allocatedCoefficientIntegerPMF B U b hR hσ S).bind
      fun a => (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
        fun r => decide (∀ p : P, allocatedActualModulusBad inactive spatial kernel block C (p.val ^ A p.val)
          (allocatedMixedFullArray (Sum.elim z a)
            (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal := by
  have h := allocatedSpatialCoefficientReferenceLaw B U b hR hσ S q noiseLaw
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q))
    (allocatedChartResiduePrimePowerWitness inactive C P A q hdiv)
  simpa only [allocatedChartResiduePrimePowerWitness_integerDeck_iff
    inactive spatial kernel block C P A q hdiv] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_physical_rank_witness_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ) (primes : Finset ℕ) [∀ p : primes, NeZero p.val] (depth : ℕ → ℕ)
    (hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
            (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        (((selectedResidueSmoothPMF stride cells width hwidth hZ).bind fun z =>
          (allocatedCoefficientIntegerPMF B U b hR hσ S).bind fun a =>
            (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
              fun r => decide (∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
                rankC (p.val ^ depth p.val) (allocatedMixedFullArray (Sum.elim z a)
                  (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_witness_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells
      (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv)
      width hwidth hwide hfreqPs hmassPs hsmallError
  have href := allocatedSpatialRankReferenceLaw (E := E) B U b hR hσ S inactive spatial kernel block
    rankC primes depth q hdiv (selectedResidueSmoothPMF stride cells width hwidth hZ)
  rw [href] at he
  exact ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedPhysicalIntegerRankLaw
namespace OAI

section

namespace Erdos3
open scoped Classical

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators Classical

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule

variable {K : Type*} {m : ℕ} {J I E : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} {J I E : Fin m → Type*} {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem exists_allocatedPhysical_integer_coefficient_read :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (read z i : ZMod q)))) := by
  have hex (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      ∃ f : AllocatedActualCoefficientIndex G X I E n B → ℤ,
        allocatedReadNoise f = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
          ∀ event : CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop,
            coefficientDeckChartEvent U bW b hb o q event
              (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
            event (allocatedReadCoefficientChartResidues (fun i => (f i : ZMod q)))) := by
    by_cases hz : allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) = 0
    · refine ⟨allocatedMixedFullArray (Sum.elim z (fun _ => 0)) (fun _ => 0) (fun _ => 0), rfl, ?_⟩
      intro h
      exact (h hz).elim
    · obtain ⟨x, hx, _⟩ := canonicalCoefficientDensity_recover_unique U b hb o
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) hz
      have hsmall : ∀ a, |coefficientSamplerAmbientPoint U b o x a| < 1/2 := by
        intro a
        exact (hx.2 a.1.1).1 a.1.2 a.2
      obtain ⟨f, hfnoise, _hfint, hfevent⟩ := exists_allocatedCoefficient_integer_event_read
        U bW b hb o (affineSampleCoefficientArray U poly hm (fun k x => (z (k,x) : ℝ)))
        x hx.1 hsmall z
      refine ⟨f, hfnoise, ?_⟩
      intro _ q hq
      exact hfevent q hq
  choose read hread using hex
  exact ⟨read, hread⟩

variable [Fintype X]

theorem exists_allocatedPhysical_integer_rank_read
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ} (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (C : ℝ) :
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      ∀ z, allocatedReadNoise (read z) = z ∧
        (allocatedCoefficientDensity B U b hb o hR hσ S
          (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))) ≠ 0 →
        ∀ (P : Finset ℕ) (hP : ∀ p : P, NeZero p.val), letI := hP
          ∀ (A : ℕ → ℕ) (M : ℕ) (hM : 0 < M), letI : NeZero M := ⟨hM.ne'⟩
            ∀ hdiv : ∀ p : P, p.val ^ A p.val ∣ M,
              coefficientDeckChartEvent U bW b hb o M
                (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
                  (fun v => (z v : ZMod M)))
                (affineCoefficientCoverSample U poly hm M (fun k x => (z (k,x) : ℝ))) ↔
              ∀ p : P, allocatedActualModulusBad inactive spatial kernel block C
                (p.val ^ A p.val) (read z)) := by
  obtain ⟨read, hread⟩ := exists_allocatedPhysical_integer_coefficient_read
    B U bW b hb o S hR hσ poly hm
  refine ⟨read, ?_⟩
  intro z
  refine ⟨(hread z).1, ?_⟩
  intro hz P hP
  let := hP
  intro A M hM
  let : NeZero M := ⟨hM.ne'⟩
  intro hdiv
  have he := (hread z).2 hz M hM
    (allocatedChartResiduePrimePowerWitness inactive C P A M hdiv
      (fun v => (z v : ZMod M)))
  apply he.trans
  have hn : allocatedReadNoise (fun i => (read z i : ZMod M)) =
      fun v => (z v : ZMod M) := by
    funext v
    change ((allocatedReadNoise (read z) v : ℤ) : ZMod M) = _
    rw [(hread z).1]
  rw [← hn]
  exact allocatedChartResiduePrimePowerWitness_iff_actual
    inactive spatial kernel block C P A M hdiv (read z)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X] {I E J : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (E j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

local notation "Dphysical" => (fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
  allocatedCoefficientDensity B U b hb o hR hσ S
    (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ))))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedPhysicalCertifiedRankWitnessLaw
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include bW hC hV in

theorem exists_allocated_physical_certified_rank_witness_law_oai
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (cap : ℕ) (hcap : 0 < cap)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hcapP : (cap : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hcapPs : (cap : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * cap : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (inactive : LayerSamplerAxis I n → Prop) {L : ℕ}
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j,a.val⟩)
    (rankC : ℝ)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
    ∃ read : (Option (LayerSamplerVariables G I n B) × X → ℤ) →
        AllocatedActualCoefficientIndex G X I E n B → ℤ,
      (∀ z, allocatedReadNoise (read z) = z) ∧
      (∀ z, Dphysical z ≠ 0 →
        ∀ (primes : Finset ℕ) (hprimes : ∀ p : primes, NeZero p.val), letI := hprimes
          ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
            ∀ hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q,
              coefficientDeckChartEvent U bW b hb o q
                (allocatedChartResiduePrimePowerWitness inactive rankC primes depth q hdiv
                  (fun v => (z v : ZMod q)))
                (affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))) ↔
              ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block rankC
                (p.val ^ depth p.val) (read z)) ∧
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      ∀ (primes : Finset ℕ) (hprimes : ∀ p : primes, NeZero p.val), letI := hprimes
        ∀ (depth : ℕ → ℕ) (q : ℕ) (hq : 0 < q), letI : NeZero q := ⟨hq.ne'⟩
        ∀ (_hqcap : q ≤ cap) (_hdiv : ∀ p : primes, p.val ^ depth p.val ∣ q),
        |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
            (if ∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
              rankC (p.val ^ depth p.val) (read z) then (1 : ℝ) else 0)) -
          (((selectedResidueSmoothPMF stride cells width hwidth hZ).bind fun z =>
            (allocatedCoefficientIntegerPMF B U b hR hσ S).bind fun a =>
              (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).map
                fun r => decide (∀ p : primes, allocatedActualModulusBad inactive spatial kernel block
                  rankC (p.val ^ depth p.val) (allocatedMixedFullArray (Sum.elim z a)
                    (fun ⟨j,e,i⟩ => ((r j e i).val : ℤ)) (fun _ => 0)))) true).toReal| ≤
          12 * (2 * δ + ε) := by
  dsimp only
  let : NeZero cap := ⟨hcap.ne'⟩
  let emptyPrimes : Finset ℕ := ∅
  let : ∀ p : emptyPrimes, NeZero p.val := fun p =>
    False.elim (Finset.notMem_empty p.val p.property)
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, _⟩ :=
    exists_allocated_physical_rank_witness_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall cap hcap hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hcapP hδ hδP μ ν poly hp hm hPs hX hframe hcapPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC emptyPrimes (fun _ => 0) (fun p => False.elim (Finset.notMem_empty p.val p.property))
      width hwidth hwide hfreqPs hmassPs hsmallError
  obtain ⟨read, hread⟩ := exists_allocatedPhysical_integer_rank_read
    B U bW b hb o S hR hσ poly hm inactive spatial kernel block rankC
  refine ⟨hD0, hZ, hDpos, read, fun z => (hread z).1,
    fun z hz => (hread z).2 hz, hmass, hlower, hupper, ?_⟩
  intro primes hprimes
  let := hprimes
  intro depth q hq
  let : NeZero q := ⟨hq.ne'⟩
  intro hqcap hdiv
  have hqP : (q : ℝ) ≤ Real.exp P := (Nat.cast_le.mpr hqcap).trans hcapP
  have hqPs : (q : ℝ) ≤ Real.exp Ps := (Nat.cast_le.mpr hqcap).trans hcapPs
  have hstrideq : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax := fun x =>
    (Nat.cast_le.mpr (Nat.mul_le_mul_left (stride x) hqcap)).trans (hstrideMax x)
  obtain ⟨_, _, _, _, _, _, he⟩ :=
    exists_allocated_physical_rank_witness_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideq H hsize hrank hRs cells hcells inactive spatial kernel block
      rankC primes depth hdiv width hwidth hwide hfreqPs hmassPs hsmallError
  have hevent := selectedResidueDensityPMF_event_congr_of_density_ne_zero
    stride cells width hwidth hZ _ hD0 hDpos _ _
    (fun z hz => (hread z).2 hz primes hprimes depth q hq hdiv)
  rw [hevent] at he
  exact he

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocated_physical_certified_rank_witness_law_oai := @OAI.Erdos3.VectorPolynomial.exists_allocated_physical_certified_rank_witness_law_oai
