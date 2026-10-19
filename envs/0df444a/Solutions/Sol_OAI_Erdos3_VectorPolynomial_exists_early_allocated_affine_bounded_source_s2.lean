-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:10:57.760006+00:00
-- url     : https://prove2.me/submissions/3b1e3e43-a727-4fe1-a7fc-3f3079ed9f3c

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Definitions.Def_OAIE3v2B213
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineIdeal_profile_integrable_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceRadius_uniform_floor_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedAffineSourceTolerance_log_bound_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalCovered_test_comparison_of_l1_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSlicedLongJet_ideal_transfer_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_early_allocated_affine_reference_source_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CubeResidueSupport
namespace OAI


namespace Erdos3

theorem scalarCubeResidueWeights_support (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I+1)*M ≤ L)
    (x : IntegerScalarCubeBox I L)
    (hx : (scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x ≠ 0) :
    ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  apply (mem_scalarCubeResidueSet L m r x).mp
  by_contra hnot
  apply hx
  simp only [scalarCubeResidueWeights, FiniteProbabilityWeights.condition, hnot, ite_false, zero_div]

theorem scalarCubeResiduePi_support {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I+1)*M j ≤ L j)
    (x : ∀ j, IntegerScalarCubeBox I (L j))
    (hx : (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).weight x ≠ 0) :
    ∀ j i, ((x j i : ℤ) : ZMod (m j i)) = r j i := by
  intro j
  apply scalarCubeResidueWeights_support I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j) (x j)
  intro hz
  apply hx
  exact Finset.prod_eq_zero (Finset.mem_univ j) hz

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProgressionTupleSliceSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

namespace FiniteProbabilityWeights

theorem condition_weight_pos_iff {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (p : FiniteProbabilityWeights Ω) (S : Finset Ω) (hS : 0 < p.mass S) (x : Ω) :
    0 < (p.condition S hS).weight x ↔ x ∈ S ∧ 0 < p.weight x := by
  change 0 < (if x ∈ S then p.weight x else 0) / p.mass S ↔ _
  rw [lt_div_iff₀ hS, zero_mul]
  by_cases hx : x ∈ S <;> simp [hx]

theorem pi_weight_pos_component {J : Type*} [Fintype J] [DecidableEq J]
    {Ω : J → Type*} [∀ j, Fintype (Ω j)] (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (x : ∀ j, Ω j) (hx : 0 < (pi p).weight x) (j : J) : 0 < (p j).weight (x j) := by
  apply lt_of_le_of_ne ((p j).nonneg (x j))
  intro he
  have hz : (pi p).weight x = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_univ j) he.symm
  linarith

end FiniteProbabilityWeights

theorem scalarCubeResidueWeights_cube_support (I : Type*) [Fintype I] [DecidableEq I]
    (H M : ℕ) (hH : 0 < H) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ H) (z : IntegerScalarCubeBox I H)
    (hz : 0 < (scalarCubeResidueWeights I H M hH m r hm hmM hsize).weight z) :
    IntegerScalarCube H (fun i => (z i : ℤ)) := by
  have h1 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp hz
  have h2 := (FiniteProbabilityWeights.condition_weight_pos_iff _ _ _ z).mp h1.2
  exact (mem_integerScalarCubeSet H z).mp h2.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ContainedProgressionCubeMap
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem containedProgressionCubeMap_value (I : Type*) [Fintype I] [DecidableEq I]
    (L H step : ℕ) (c : ℤ) (hL : 0 < L)
    (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))
    (z : IntegerScalarCubeBox I H) (hz : IntegerScalarCube H (fun i => (z i : ℤ)))
    (i : Option I) :
    (containedProgressionCubeMap I L H step c hL hsubset z i : ℤ) =
      (if i = none then c else 0) + (step : ℤ) * (z i : ℤ) := by
  rw [containedProgressionCubeMap, dif_pos hz]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteGoodSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem mean_congr_on_support {f g : X → ℝ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.mean f = p.mean g :=
  le_antisymm (p.mean_mono_on_support (fun x hx => (h x hx).le))
    (p.mean_mono_on_support (fun x hx => (h x hx).ge))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PartitionedRegularizationBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem partitionedPolynomialParameter_card {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P] :
    Fintype.card (PolynomialParameter (PartitionedProfileNoiseIndex G Z α B h P)
      (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d))) =
    Fintype.card (PolynomialParameter (Z ⊕ (Σ d, SamplerCoefficientSlot G B h d))
      (JointBlockParameter B h α)) := by
  have he := dependentAxis_card_split (fun d => BlockParameter (B d) (Fin (h d)) α) P
  change Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P) +
    Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d)) =
    Fintype.card (JointBlockParameter B h α) at he
  simp only [PolynomialParameter, Fintype.card_option, PartitionedProfileNoiseIndex, Fintype.card_sum]
  change (Fintype.card Z + Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) P) +
      Fintype.card (Σ d, SamplerCoefficientSlot G B h d) +
      Fintype.card (PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d))) + 1 =
    (Fintype.card Z + Fintype.card (Σ d, SamplerCoefficientSlot G B h d) +
      Fintype.card (JointBlockParameter B h α)) + 1
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteFiberLawSupport
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

theorem fiberLaw_support {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (F : X → Y) (P : Y → Prop)
    (hP : ∀ x, p.weight x ≠ 0 → P (F x))
    (y : Y) (hy : (p.fiberLaw F).weight y ≠ 0) : P y := by
  classical
  by_contra hn
  apply hy
  change p.mean (fun x => if F x = y then (1 : ℝ) else 0) = 0
  calc
    _ = p.mean (fun _ => 0) := by
      apply p.mean_congr_on_support
      intro x hx
      apply if_neg
      intro he
      exact hn (he ▸ hP x hx)
    _ = 0 := p.mean_const 0

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (modulus : ℕ) (hm : 0 < modulus)
variable (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
variable (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)

local notation "weights" => principalResidueWeights B h H hH modulus hm r hsize
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

theorem principalResidueWeights_cube_support
    (v : PrincipalIntegerTuples B h α H) (hv : (weights).weight v ≠ 0)
    (j : PrincipalTupleIndex B h) : IntegerScalarCube (H j) (fun i => (v j i : ℤ)) := by
  apply scalarCubeResidueWeights_cube_support α (H j) modulus (hH j)
    (fun _ => modulus) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j)
  exact FiniteProbabilityWeights.pi_weight_pos_component _ v
    (lt_of_le_of_ne ((weights).nonneg v) (Ne.symm hv)) j

theorem containedProgressionResidueLaw_support
    (v : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0) :
    ∀ j i, ((v j i : ℤ) : ZMod modulus) =
      (if i = none then (c j : ZMod modulus) else 0) + (step j : ZMod modulus) * r j i := by
  apply (weights).fiberLaw_support tupleMap
    (fun v => ∀ j i, ((v j i : ℤ) : ZMod modulus) =
      (if i = none then (c j : ZMod modulus) else 0) + (step j : ZMod modulus) * r j i) _ v hv
  intro z hz j i
  have hc := principalResidueWeights_cube_support B h H hH modulus hm r hsize z hz j
  have hr := scalarCubeResiduePi_support H (fun _ => modulus) hH
    (fun _ _ => modulus) r (fun _ _ => hm) (fun _ _ => le_rfl) hsize z hz j i
  change ((containedProgressionCubeMap α (L j) (H j) (step j) (c j) (hL j) (hsubset j) (z j) i : ℤ) : ZMod modulus) = _
  rw [containedProgressionCubeMap_value _ _ _ _ _ _ _ _ hc]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, apply_ite, Int.cast_zero, hr]

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem containedProgressionResidueLaw_label_eq
    {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (modulus : ℕ) (hm : 0 < modulus)
    (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
    (v v₀ : PrincipalIntegerTuples B h α L)
    (hv : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v ≠ 0)
    (hv₀ : (containedProgressionResidueLaw B h L H step c hL hH hsubset modulus hm r hsize).weight v₀ ≠ 0) :
    principalResidueLabel modulus v = principalResidueLabel modulus v₀ := by
  funext j i
  exact (containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v hv j i).trans
    (containedProgressionResidueLaw_support B h L H step c hL hH hsubset modulus hm r hsize v₀ hv₀ j i).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedSlicedCoveredComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)
variable [∀ a, DecidableEq (B a)]
variable (period : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
variable (F : AllocatedFrozenCoefficients B U b S × EuclideanJetLayers U O → ℂ)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "activeB" => (fun a : {a // ¬grid a} => B (Subtype.val a))
local notation "activeDegree" => (fun a : {a // ¬grid a} => layerSamplerDegree I n (Subtype.val a))
local notation "lengths" => principalAxisLength (fun a => ¬grid a) (allocatedPrincipalSides B U b S)
local notation "tupleIndex" => PrincipalTupleIndex activeB activeDegree
local notation "positiveLengths" => (fun j : tupleIndex => allocatedPrincipalSides_pos B U b S
  (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j)))

local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "reference" => allocatedLongJetReference B U b S O
local notation "density" => (fun v z => allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "test" => allocatedCoveredFixedTest B U b S x u v₀ rows Q hb o bW d F
local notation "actual" weights:max => (∫ p, FiniteProbabilityWeights.complexMean weights (fun v => F (Prod.fst ((allocatedCoefficientSplit B U b S) (Prod.fst p)),
  euclideanCoefficientJetMap U (root v) (dirs v) rows
    (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
    ∂(Measure.prod source (PMF.toMeasure deck)))

include hperiod in
theorem allocatedSlicedPhysicalCovered_test_comparison_of_l1 [DecidableEq G]
    (H step : tupleIndex → ℕ) (c : tupleIndex → ℤ) (hH : ∀ j, 0 < H j)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (lengths j : ℤ))
    (hp : 0 < period) (r : tupleIndex → Option α → ZMod period)
    (hsize : ∀ j, (Fintype.card α + 1) * period ≤ H j)
    (hv₀ : (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize).weight v₀ ≠ 0)
    (g : AllocatedLongJetRows B U b S O → ℝ) (hg : Integrable g reference)
    {ε : ℝ} (he : (∫ z, |(containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize).mean (fun v => density v z) - g z| ∂reference) ≤ ε)
    (hF : Measurable F) (hbound : ∀ p, ‖F p‖ ≤ 1) :
    ‖actual (containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize) - ∫ a₀, ∫ z, (g z : ℂ) * test a₀ z ∂reference ∂frozenSource‖ ≤ ε := by
  let weights := containedProgressionResidueLaw activeB activeDegree lengths H step c positiveLengths hH
    hsubset period hp r hsize
  have hr (v) (hv : weights.weight v ≠ 0) :
      principalResidueLabel period v = principalResidueLabel period v₀ :=
    containedProgressionResidueLaw_label_eq activeB activeDegree lengths H step c positiveLengths hH
      hsubset period hp r hsize v v₀ hv hv₀
  exact allocatedPhysicalCovered_test_comparison_of_l1_s2 B U b hR hσ S x u v₀ rows Q hb o bW d
    s hA hσ1 weights period hperiod hr F g hg he hF hbound

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OneCubePrincipalSliceRiemann
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ)

omit [DecidableEq α] in
theorem principalProgressionSlice_parameters [DecidableEq α]
    (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
    (hL : ∀ j, 0 < L j) (hstep : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
    {δ : ℝ} (hδ : 0 < δ)
    (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
    (hdense : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ)) :
    ∀ i, 0 < principalProgressionSliceWidth (α := α) B h L H step i ∧
      δ / 2 ≤ |principalProgressionSliceWidth (α := α) B h L H step i| ∧
      |principalProgressionSliceCenter (α := α) B h L c i| +
        |principalProgressionSliceWidth (α := α) B h L H step i| ≤ 1 := by
  intro i
  let j : PrincipalTupleIndex B h := ⟨i.1, i.2.1, i.2.2.1⟩
  have hg := progression_slice_endpoint_geometry (c j) (hL j) (hstep j) (hH j) hδ
    (hsubset j) (hdense j)
  have hp : 0 < (step j : ℝ) * ((H j : ℝ) - 1) / L j := (half_pos hδ).trans_le hg.2.1
  refine ⟨hp, ?_, ?_⟩
  · change δ / 2 ≤ |(step j : ℝ) * ((H j : ℝ) - 1) / L j|
    rw [abs_of_pos hp]
    exact hg.2.1
  · change |if i.2.2.2 = none then (c j : ℝ) / L j else 0| +
      |(step j : ℝ) * ((H j : ℝ) - 1) / L j| ≤ 1
    split_ifs
    · exact hg.2.2.1
    · simpa only [abs_zero, zero_add] using
        (le_add_of_nonneg_left (abs_nonneg ((c j : ℝ) / L j))).trans hg.2.2.1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProfileRadiusLog
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

variable {D : Type*} [Fintype D] {B : D → Type*} [∀ d, Fintype (B d)]

theorem unitProfileCoefficientLog_nonneg (A T : ℝ≥0) :
    0 ≤ unitProfileCoefficientLog (B := B) A T := by
  unfold unitProfileCoefficientLog
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PartitionedAffineLogEnvelope
namespace OAI

section

namespace Erdos3

 theorem cubeMinor_counts_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hO : (Fintype.card O : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    (cubeMinorVariableCount O α h : ℝ) ≤ affineMinorVariableEnvelope D ∧
    (cubeMinorDegree O h : ℝ) ≤ affineMinorDegreeEnvelope D := by
  constructor
  · simp only [cubeMinorVariableCount, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      affineMinorVariableEnvelope]
    gcongr
  · have hs : ((h - 1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hh
    simp only [cubeMinorDegree, Nat.cast_max, Nat.cast_one, Nat.cast_mul, affineMinorDegreeEnvelope]
    apply max_le
    · nlinarith [sq_nonneg D]
    · exact (mul_le_mul hO hs (Nat.cast_nonneg _) hD).trans (by linarith)

 theorem canonicalAffineMinorLog_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {D P E F : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hO : (Fintype.card O : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    canonicalAffineMinorLog O α h P E F ≤ affineMinorLogEnvelope D P E F := by
  obtain ⟨hN, hd⟩ := cubeMinor_counts_le_envelope O α h hD hO hα hh
  have hN0 := affineMinorVariableEnvelope_nonneg hD
  have hd0 := affineMinorDegreeEnvelope_nonneg hD
  have hC0 := affineMinorConstantEnvelope_nonneg hD
  have hC : cubeMinorConstantLog (Fintype.card O) (Fintype.card α) h
      (cubeMinorVariableCount O α h) (cubeMinorDegree O h) ≤ affineMinorConstantEnvelope D := by
    unfold cubeMinorConstantLog affineMinorConstantEnvelope
    gcongr
  have hCold : 0 ≤ cubeMinorConstantLog (Fintype.card O) (Fintype.card α) h
      (cubeMinorVariableCount O α h) (cubeMinorDegree O h) := by
    unfold cubeMinorConstantLog
    positivity
  unfold canonicalAffineMinorLog canonicalBooleanMinorLog cubeMinorThresholdLog cubeMinorScaleLog
    affineMinorLogEnvelope
  push_cast
  gcongr

end Erdos3

end

section

namespace Erdos3

 theorem affineBlockParameter_card_le (B α : Type*) [Fintype B] [Fintype α]
    (h : ℕ) {D : ℝ} (hD : 0 ≤ D)
    (hB : (Fintype.card B : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    (Fintype.card (BlockParameter B (Fin h) α) : ℝ) ≤ affineMinorVariableEnvelope D := by
  simp only [BlockParameter, Fintype.card_prod, Fintype.card_fin, Fintype.card_option,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, affineMinorVariableEnvelope]
  gcongr

 theorem affineInverseAxisLog_le_envelope (O α : Type*) [Fintype O] [Fintype α]
    (h : ℕ) {D P E F : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hO : (Fintype.card O : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    F + productMinorInverseLog (Fintype.card O) (Fintype.card α) h P
      (canonicalAffineMinorLog O α h P E F) ≤ affineInverseAxisEnvelope D P E F := by
  have hminor := canonicalAffineMinorLog_le_envelope O α h hD hP hE hF hO hα hh
  have hj : ((Fintype.card O - 1 : ℕ) : ℝ) ≤ D := (Nat.cast_le.mpr (Nat.sub_le _ _)).trans hO
  unfold productMinorInverseLog productMinorEntryLog affineInverseAxisEnvelope
  gcongr

 theorem affineDerivativeAxisLog_le_envelope (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {D P : ℝ} (hD : 0 ≤ D)
    (hB : (Fintype.card B : ℝ) ≤ D) (hO : (Fintype.card O : ℝ) ≤ D)
    (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    productMinorDerivativeLog (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h P ≤ affineDerivativeAxisEnvelope D P := by
  have hn := affineBlockParameter_card_le B α h hD hB hα hh
  unfold productMinorDerivativeLog productMinorPartialLog affineDerivativeAxisEnvelope
  gcongr

 theorem affineWeightAxisLog_le_envelope (B O α : Type*) [Fintype B] [Fintype O] [Fintype α]
    (h : ℕ) {D P E F : ℝ} (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hB : (Fintype.card B : ℝ) ≤ D) (hO : (Fintype.card O : ℝ) ≤ D)
    (hα : (Fintype.card α : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) :
    affineBooleanAxisWeightLog B O α h P E F ≤ affineWeightAxisEnvelope D P E F := by
  have hn := affineBlockParameter_card_le B α h hD hB hα hh
  have hminor := canonicalAffineMinorLog_le_envelope O α h hD hP hE hF hO hα hh
  have hbh : (Fintype.card (B × Fin h) : ℝ) ≤ D * D := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    exact mul_le_mul hB hh (Nat.cast_nonneg _) hD
  unfold affineBooleanAxisWeightLog affineWeightAxisEnvelope scalarCubeDerivativeLog scalarCubeBoundaryLog
    productMinorDeterminantLog productMinorPartialLog productMinorEntryLog
  gcongr

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

 theorem affineLog_sum_le {ι : Type*} [Fintype ι] (f : ι → ℝ) {D C : ℝ}
    (hD : (Fintype.card ι : ℝ) ≤ D) (hC : 0 ≤ C) (hf : ∀ i, f i ≤ C) :
    (∑ i, f i) ≤ D * C := by
  calc
    _ ≤ ∑ _i : ι, C := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι * C := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hD hC

variable {ι α : Type*} [Fintype ι] [Fintype α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

 theorem jointAffineSourceInputLog_le_envelope (h : ι → ℕ) {D P E F : ℝ}
    (hD : 0 ≤ D) (hP : 0 ≤ P) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (haxes : (Fintype.card ι : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D)
    (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ D)
    (hO : ∀ i, (Fintype.card (O i) : ℝ) ≤ D) (hh : ∀ i, (h i : ℝ) ≤ D) :
    jointAffineSourceInputLog (B := B) (O := O) (α := α) h P E F ≤ jointAffineSourceEnvelope D P E F := by
  have hInv : jointAffineInverseLog (O := O) (α := α) h P E F ≤ jointAffineInverseEnvelope D P E F := by
    apply add_le_add haxes
    exact affineLog_sum_le _ haxes (affineInverseAxisEnvelope_nonneg hD hP hE hF)
      (fun i => affineInverseAxisLog_le_envelope (O i) α (h i) hD hP hE hF (hO i) hα (hh i))
  have hDer : jointBooleanDerivativeLog (B := B) (O := O) (α := α) h P ≤ jointAffineDerivativeEnvelope D P := by
    apply add_le_add haxes
    exact affineLog_sum_le _ haxes (affineDerivativeAxisEnvelope_nonneg hD hP)
      (fun i => affineDerivativeAxisLog_le_envelope (B i) (O i) α (h i) hD (hB i) (hO i) hα (hh i))
  have hWeight : jointAffineBooleanWeightLog (B := B) (O := O) (α := α) h P E F ≤ jointAffineWeightEnvelope D P E F := by
    apply add_le_add haxes
    exact affineLog_sum_le _ haxes (affineWeightAxisEnvelope_nonneg hD hP hE hF)
      (fun i => affineWeightAxisLog_le_envelope (B i) (O i) α (h i) hD hP hE hF (hB i) (hO i) hα (hh i))
  have hOut : (Fintype.card (Σ i, O i) : ℝ) ≤ D * D := by
    simp only [Fintype.card_sigma, Nat.cast_sum]
    exact affineLog_sum_le _ haxes hD hO
  have hParam : (Fintype.card (JointBlockParameter B h α) : ℝ) ≤ D * affineMinorVariableEnvelope D := by
    simp only [JointBlockParameter, Fintype.card_sigma, Nat.cast_sum]
    exact affineLog_sum_le _ haxes (affineMinorVariableEnvelope_nonneg hD)
      (fun i => affineBlockParameter_card_le (B i) α (h i) hD (hB i) hα (hh i))
  unfold jointAffineSourceInputLog jointAffineTranslationLog jointAffinePerturbationLog jointAffineSourceEnvelope
  push_cast
  gcongr

 theorem jointAffineSourceEnvelope_mono {D P P' E E' F F' : ℝ}
    (hD : 0 ≤ D) (hP : P ≤ P') (hE : E ≤ E') (hF : F ≤ F') :
    jointAffineSourceEnvelope D P E F ≤ jointAffineSourceEnvelope D P' E' F' := by
  dsimp only [jointAffineSourceEnvelope, jointAffineInverseEnvelope, jointAffineDerivativeEnvelope, jointAffineWeightEnvelope,
    affineInverseAxisEnvelope, affineDerivativeAxisEnvelope, affineWeightAxisEnvelope, affineMinorLogEnvelope,
    affineMinorVariableEnvelope, affineMinorDegreeEnvelope]
  gcongr

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators NNReal Classical

variable {ι G Z α : Type*} [Fintype ι] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
  {B O : ι → Type*} [∀ i, Fintype (B i)] [∀ i, Fintype (O i)]

omit [DecidableEq α] in
 theorem partitionedAffineInputLog_le_envelope (h : ι → ℕ) (partition : ι → Prop)
    (A T : ℝ≥0) {D E F : ℝ} (hD : 0 ≤ D)
    (haxes : (Fintype.card ι : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D)
    (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ D)
    (hO : ∀ i, (Fintype.card (O i) : ℝ) ≤ D) (hh : ∀ i, (h i : ℝ) ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F) :
    jointAffineSourceInputLog (B := fun i : {i // ¬partition i} => B i.val)
      (O := fun i : {i // ¬partition i} => O i.val) (α := α) (fun i => h i.val)
      (unitProfileCoefficientLog (B := B) A T) (E + Fintype.card {i // ¬partition i} + 4) F ≤
        affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F := by
  have ha : (Fintype.card {i // ¬partition i} : ℝ) ≤ D :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le _)).trans haxes
  have hC : unitProfileCoefficientLog (B := B) A T ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold unitProfileCoefficientLog affineProfileCoefficientEnvelope
    gcongr
    exact affineLog_sum_le _ haxes hD hB
  have hb := jointAffineSourceInputLog_le_envelope (B := fun i : {i // ¬partition i} => B i.val)
    (O := fun i : {i // ¬partition i} => O i.val) (α := α) (fun i => h i.val)
    (E := E + Fintype.card {i // ¬partition i} + 4) hD (unitProfileCoefficientLog_nonneg (B := B) A T) (by positivity) hF ha hα
    (fun i => hB i.val) (fun i => hO i.val) (fun i => hh i.val)
  exact hb.trans (jointAffineSourceEnvelope_mono (E' := E + D + 4) hD hC (by linarith) le_rfl)

omit [DecidableEq α] in
 theorem partitionedAffineToleranceLog_le_envelope (h : ι → ℕ) (partition : ι → Prop)
    (A T : ℝ≥0) (degree : ℕ) {D N E F : ℝ} (hD : 0 ≤ D)
    (haxes : (Fintype.card ι : ℝ) ≤ D) (hα : (Fintype.card α : ℝ) ≤ D)
    (hB : ∀ i, (Fintype.card (B i) : ℝ) ≤ D)
    (hO : ∀ i, (Fintype.card (O i) : ℝ) ≤ D) (hh : ∀ i, (h i : ℝ) ≤ D)
    (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hN : (Fintype.card (PolynomialParameter (Z ⊕ (Σ i, SamplerCoefficientSlot G B h i))
      (JointBlockParameter B h α)) : ℝ) ≤ N) :
    let P := unitProfileCoefficientLog (B := B) A T
    let Q := jointAffineSourceInputLog (B := fun i : {i // ¬partition i} => B i.val)
      (O := fun i : {i // ¬partition i} => O i.val) (α := α) (fun i => h i.val)
      P (E + Fintype.card {i // ¬partition i} + 4) F
    Real.log 16 + 6 * Q +
      booleanToleranceC2Log (B := fun i : {i // ¬partition i} => B i.val) (α := α)
        (PartitionedProfileNoiseIndex G Z α B h partition) (fun i => h i.val) degree P + 1 ≤
      affineProfileToleranceEnvelope degree D N (A : ℝ) (T : ℝ) E F := by
  intro P Q
  have hQ := partitionedAffineInputLog_le_envelope (B := B) (O := O) (α := α)
    h partition A T hD haxes hα hB hO hh hE hF
  have hC : P ≤ affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) := by
    unfold P unitProfileCoefficientLog affineProfileCoefficientEnvelope
    gcongr
    exact affineLog_sum_le _ haxes hD hB
  have hlog : Real.log 16 ≤ (16 : ℝ) := Real.log_le_self (by norm_num)
  have hc2 : booleanToleranceC2Log (B := fun i : {i // ¬partition i} => B i.val) (α := α)
      (PartitionedProfileNoiseIndex G Z α B h partition) (fun i => h i.val) degree P ≤
      3 * N * (degree + 2 : ℕ) +
        (2 * (D + affineProfileCoefficientEnvelope D (A : ℝ) (T : ℝ) + degree * D) + 1) := by
    unfold booleanToleranceC2Log booleanJetMassLog
    rw [partitionedPolynomialParameter_card]
    gcongr
  exact add_le_add (add_le_add (add_le_add hlog (mul_le_mul_of_nonneg_left hQ (by norm_num))) hc2) le_rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineLogEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]

 theorem allocatedBlock_card_le_tuples (a : LayerSamplerAxis I n) :
    Fintype.card (B a) ≤ Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) := by
  apply Fintype.card_le_of_injective
    (fun b : B a => (⟨a, b, ⟨0, Nat.zero_lt_succ _⟩⟩ : PrincipalTupleIndex B (layerSamplerDegree I n)))
  intro b c hbc
  simpa using hbc

 theorem allocatedAffine_block_dimensions {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α O D) :
    ∀ a, (Fintype.card (B a) : ℝ) ≤ D :=
  fun a => (Nat.cast_le.mpr (allocatedBlock_card_le_tuples B a)).trans hd.tuples

 theorem allocatedAffine_parameter_dimensions {D : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α O D) :
    (Fintype.card (PolynomialParameter
      ((G × Option α) ⊕ (Σ a, SamplerCoefficientSlot G B (layerSamplerDegree I n) a))
      (JointBlockParameter B (layerSamplerDegree I n) α)) : ℝ) ≤
        D * (D + 1) + D * D + D + 1 := by
  have hslots : (∑ a : LayerSamplerAxis I n,
      (Fintype.card (SamplerCoefficientSlot G B (layerSamplerDegree I n) a) : ℝ)) ≤ D * D := by
    apply affineLog_sum_le _ hd.axes hd.nonneg
    intro a
    exact hd.coefficients a.1
  have hG := hd.kernel_variables
  have hα := hd.cube
  have hparam := hd.parameters
  have hD := hd.nonneg
  simp only [PolynomialParameter, Fintype.card_option, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, Nat.cast_one]
  simp only [JointBlockParameter, BlockParameter, Fintype.card_sigma, Fintype.card_prod,
    Fintype.card_option, Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hparam
  gcongr

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
  {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
  {α : Type*} [Fintype α] [DecidableEq α]
  {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)]

omit [DecidableEq α] [∀ j, Nonempty (O j)] in
 theorem allocatedAffine_log_costs_le_envelope [DecidableEq α] [∀ j, Nonempty (O j)]
    (A T : ℝ≥0) {D E F : ℝ}
    (hd : AllocatedComparisonDimensions (G := G) B α O D) (hE : 0 ≤ E) (hF : 0 ≤ F) :
    allocatedAffineRadiusLog (O := O) (α := α) B A T E F ≤
      2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2 ∧
    allocatedAffineToleranceLog (G := G) (O := O) (α := α) B A T E F ≤
      affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F := by
  have hB := allocatedAffine_block_dimensions B hd
  have hh (a : LayerSamplerAxis I n) : (layerSamplerDegree I n a : ℝ) ≤ D :=
    hd.layer_degree B a.1
  have hO (a : LayerSamplerAxis I n) : (Fintype.card (O a.1) : ℝ) ≤ D := hd.rows a.1
  constructor
  · apply (Finset.sup'_le_iff _ _).mpr
    intro partition _
    exact add_le_add (mul_le_mul_of_nonneg_left
      (partitionedAffineInputLog_le_envelope (B := B) (O := fun a : LayerSamplerAxis I n => O a.1)
        (α := α) (layerSamplerDegree I n) partition A T hd.nonneg hd.axes hd.cube hB hO hh hE hF)
      (by norm_num)) le_rfl
  · apply (Finset.sup'_le_iff _ _).mpr
    intro partition _
    exact partitionedAffineToleranceLog_le_envelope (G := G) (Z := G × Option α)
      (B := B) (O := fun a : LayerSamplerAxis I n => O a.1) (α := α)
      (layerSamplerDegree I n) partition A T m hd.nonneg hd.axes hd.cube hB hO hh hE hF
      (allocatedAffine_parameter_dimensions B hd)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineWholeProfileComparison
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineCoefficient_from_reference_l1
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1) :
  ∀ {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
        {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
        (S : LayerSamplerScale (G := G) B U basis R σ),
      ∀ (hσsmall : ∀ j, σ j ≤ t),
      ∀ (x : G → IntegerScalarCubeBox α S.value)
        (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value) (allocatedPrincipalSides B U basis S)),
      ∀ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0),
      ∀ {Mk : ℕ} (_ : 0 < Mk)
        (_ : ∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val + 1) (rows j)
          (s j) (hA j) (1 / (Mk : ℝ)))
        {P : ℝ} (_ : 0 ≤ P) (_ : (Mk : ℝ) ≤ Real.exp P)
        (_ : ∀ j, R j ≤ Real.exp P) (_ : ∀ j, (R j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
        (_ : ∀ j : Fin m, (Fintype.card
          (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) + 1 ≤ Real.exp P),
      let L := principalAxisLength (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S)
      let hL := fun j : PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) => allocatedPrincipalSides_pos B U basis S
        (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j))
      ∀ (H step : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℕ) (c : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → ℤ)
        (_ : ∀ j, 0 < step j) (hH : ∀ j, 2 ≤ H j)
        (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
        (_ : ∀ j, δ * L j ≤ ((integerProgressionSupport (c j) (step j : ℤ) (H j)).card : ℝ))
        (modulus : ℕ) (hm : 0 < modulus)
        (residue : (PrincipalTupleIndex (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)) → Option α → ZMod modulus)
        (hsize : ∀ j, (Fintype.card α + 1) * modulus ≤ H j)
        (_ : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ) / H j) < volume.real (scalarCubeDomain α))
        {ε : ℝ} (_ : 0 ≤ ε) (_ : ∀ j, (step j : ℝ) / L j ≤ ε)
        (selection : α ↪ G) (_ : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
        (_ : Fintype.card α ≤ m + 1)
        {e εcoef : ℝ} (_ : 0 ≤ e) (_ : 0 < εcoef) (_ : εcoef⁻¹ ≤ Real.exp e)
        (_ : Real.exp (allocatedKernelReplacementLog (G := G) B α O P e) ≤ S.value)
        (_ : ∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
        (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬(allocatedGridAxis (I := I) U basis S.value) a) (allocatedPrincipalSides B U basis S))
        (_ : (containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
          (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize).weight v₀ ≠ 0),
      let outputResidue := fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v₀) modulus
      ∀ {mesh Cmask : ℝ} (_ : 0 ≤ mesh) (_ : mesh ≤ 1)
        (_ : 1 / (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ mesh)
        (_ : 1 ≤ Cmask)
        (_ : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ∧
          allocatedIntegerKernelMask B U basis S x rows j modulus (outputResidue j) z ≤ Cmask),
      let center := principalProgressionSliceCenter (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L c
      let width := principalProgressionSliceWidth (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step
      let ideal := diagonalImageDensity (fun o : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) => R o.1.val.1)
        (activeAveragedSlicedProfileIdeal (G := G) (B := B) (G × Option α)
          (layerSamplerDegree I n) (allocatedGridAxis (I := I) U basis S.value) (fun a => rows a.val.1) (ρ (allocatedGridAxis (I := I) U basis S.value)) center width)
      let law := containedProgressionResidueLaw (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) L H step c hL
        (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset modulus hm residue hsize
      let proxy := fun z : (Σ a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}, O a.val.1) → ℝ =>
        (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (H j) modulus
          (lt_of_lt_of_le (by decide : 0 < 2) (hH j)) (fun _ => modulus) (residue j) (fun _ => hm) (fun _ => le_rfl) (hsize j))).mean
          (fun v => allocatedNormalizedLongJetDensity B U basis S x u rows s hA
            (principalTupleFlatten (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val) α
              (fun j i => ((if i = none then (c j : ℝ) else 0) + (step j : ℝ) * (v j i : ℝ)) / L j)) z)
      (∫ z, |allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z -
        allocatedLongProfileDensity B U basis S x rows modulus outputResidue proxy z|
        ∂allocatedLongJetReference B U basis S O) ≤
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask →
      (∫ z, |law.mean (fun v => allocatedLongJetDensity B U basis hR hσ S x u v rows s hA
            (fun j => (hσsmall j).trans htone) z) -
          allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal z|
        ∂allocatedLongJetReference B U basis S O) ≤
        (2 * Real.exp (allocatedJetSupportLog (G := G) B α O P) + 1)^
          Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) *
          (Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} * εcoef *
            (1 + (layerKernelIndexBound m Mk : ℝ) * Real.exp (allocatedDensityLog (G := G) B α O P) + εcoef)^
              Fintype.card {a // ¬(allocatedGridAxis (I := I) U basis S.value) a}) +
        allocatedAffineSourceReferenceError B U basis S α O
          (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask
 := by
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law proxy href
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hw := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hg := allocatedAffineIdeal_profile_integrable_s2 B U basis hR S x rows hRP hRi
    (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρpos _) (hρone _)
    center width (fun i => (hw i).2.2) modulus outputResidue hCmask hmask
  have hlong := allocatedSlicedLongJet_ideal_transfer_s2 B U basis hR hσ S x rows
    hMk selection hx hq hrows hcard hσ1 hP he hεcoef hMkP hRP hRi hσi hcount hεe hlarge
    modulus hperiod s hA hi u H step c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j)) hsubset hm residue hsize
    v₀ hv₀ (allocatedLongProfileDensity B U basis S x rows modulus outputResidue ideal)
    hg (Eref := allocatedAffineSourceReferenceError B U basis S α O
      (ρ (allocatedGridAxis (I := I) U basis S.value)) P η (fun _ => modulus) H ε mesh Cmask) href
  exact hlong

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

include hrows hcard in
omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineCoefficientComparison_of_reference
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineReferenceComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t) :
    AllocatedAffineCoefficientComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  unfold AllocatedAffineCoefficientComparison
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have href := hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    L step H (fun _ => modulus) c hL hstep hH hsubset hdense (fun _ _ => modulus) residue
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize hsmall hε hmesh
    modulus outputResidue hmesh0 hmesh1 hscaleMesh hCmask hmask
  with_reducible
    refine allocatedAffineCoefficient_from_reference_l1 B rows hrows hcard hδ ρ hρpos hρone t htone
      U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
      H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
      selection hx hq he hεcoef hεe hlarge hperiod v₀ hv₀ hmesh0 hmesh1 hscaleMesh hCmask hmask ?_
  exact href

include hrows hcard in
theorem exists_early_allocated_affine_coefficient_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineCoefficientComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_reference_source_s2 (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  exact allocatedAffineCoefficientComparison_of_reference B rows hrows hcard hδ ρ
    (fun P => hρmin.trans_le (hρ P).1) (fun P => (hρ P).2) t htone hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory Module Submodule
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j o, (rows j o).card ≤ j.val + 1)

omit [∀ index, Nonempty (O index)] in
theorem allocatedAffineCoveredComparison_of_coefficient
    {δ η : ℝ} (hδ : 0 < δ) (ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0)
    (hρpos : ∀ P, 0 < ρ P) (hρone : ∀ P, ρ P ≤ 1) (t : ℝ) (htone : t ≤ 1)
    (hs : AllocatedAffineCoefficientComparison.{uJ, _, _, _, _, _} (G := G) B rows δ η ρ t htone) :
    AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  unfold AllocatedAffineCoveredComparison
  intro J _ U basis R σ hR hσ S hσsmall x u s hA Mk hMk hi P hP hMkP hRP hRi hσi hcount
    L hL H step c hstep hH hsubset hdense modulus hm residue hsize hsmall ε hε hmesh
    selection hx hq e εcoef he hεcoef hεe hlarge hperiod v₀ hv₀ outputResidue
    mesh Cmask hmesh0 hmesh1 hscaleMesh hCmask hmask
    center width ideal law Q _ hb o bW d _ F hF hFbound
  have hσ1 : ∀ j, σ j ≤ 1 := fun j => (hσsmall j).trans htone
  have hc := hs U basis hR hσ S hσsmall x u s hA hMk hi hP hMkP hRP hRi hσi hcount
    H step c hstep hH hsubset hdense modulus hm residue hsize hsmall hε hmesh
    selection hx hq he hεcoef hεe hlarge hperiod v₀ hv₀
    hmesh0 hmesh1 hscaleMesh hCmask hmask
  have hw := principalProgressionSlice_parameters (α := α) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => B a.val) (fun a : {a // ¬(allocatedGridAxis (I := I) U basis S.value) a} => layerSamplerDegree I n a.val)
    L H step c hL hstep hH hδ hsubset hdense
  have hg := allocatedAffineIdeal_profile_integrable_s2 B U basis hR S x rows hRP hRi
    (ρ (allocatedGridAxis (I := I) U basis S.value)) (hρpos _) (hρone _)
    center width (fun i => (hw i).2.2) modulus outputResidue hCmask hmask
  exact allocatedSlicedPhysicalCovered_test_comparison_of_l1 B U basis hR hσ S x u v₀ rows
    Q hb o bW d s hA hσ1 modulus hperiod F H step c (fun j => lt_of_lt_of_le (by decide : 0 < 2) (hH j))
    hsubset hm residue hsize hv₀ _ hg hc hF hFbound

include hrows hcard in
theorem exists_early_allocated_affine_covered_source
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ η : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    ∃ ρmin : ℝ≥0, 0 < ρmin ∧ ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, ρmin ≤ ρ P ∧ ρ P ≤ 1) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α) (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
      t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
      AllocatedAffineCoveredComparison.{uJ, uQ, _, _, _, _, _} (G := G) B rows δ η ρ t htone := by
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_coefficient_source (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  refine ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, ?_⟩
  exact allocatedAffineCoveredComparison_of_coefficient B rows hδ ρ
    (fun P => hρmin.trans_le (hρ P).1) (fun P => (hρ P).2) t htone hs

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uJ uQ
open MeasureTheory
open scoped BigOperators ContDiff NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, Nonempty (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (hrows : ∀ j, Function.Injective (rows j)) (hcard : ∀ j a, (rows j a).card ≤ j.val + 1)

include hrows hcard in
theorem exists_early_allocated_affine_bounded_source_s2_oai
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (block : ∀ a : LayerSamplerAxis I n, O a.1 → B a)
    (hblock : ∀ a, Function.Injective (block a))
    {δ target maskLog F D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (htarget : 0 ≤ target) (hmaskLog : 0 ≤ maskLog) (hF : 0 ≤ F)
    (hδF : (δ / 2)⁻¹ ≤ Real.exp F) :
    let E := target + maskLog + 5
    let η := Real.exp (-E)
    let radiusLog := 2 * affineProfileInputEnvelope D (A : ℝ) (T : ℝ) E F + 2
    let toleranceLog := affineProfileToleranceEnvelope m D (D * (D + 1) + D * D + D + 1) (A : ℝ) (T : ℝ) E F
    ∃ ρ : (LayerSamplerAxis I n → Prop) → ℝ≥0,
      (∀ P, 0 < ρ P ∧ ρ P ≤ 1 ∧ Real.exp (-radiusLog) ≤ ρ P) ∧
      (∀ P, (ρ P : ℝ) = partitionedAffineSourceRadius (B := B)
        (O := fun a : {a // ¬P a} => O a.val.1) (α := α)
        (layerSamplerDegree I n) P A T (δ / 2) η) ∧
      ∃ t : ℝ, 0 < t ∧ ∃ htone : t ≤ 1,
        t⁻¹ ≤ Real.exp toleranceLog ∧
        t = allocatedAffineSourceTolerance (G := G) (O := O) (α := α) B A T (δ / 2) η ∧
        AllocatedAffineCoveredComparison.{uJ,uQ,_,_,_,_,_} (G := G) B rows δ η ρ t htone := by
  intro E η radiusLog toleranceLog
  have hη : 0 < η := Real.exp_pos _
  have hE : 0 ≤ E := by dsimp [E]; linarith
  have hηE : η⁻¹ ≤ Real.exp E := by
    dsimp [η]
    rw [← Real.exp_neg]
    simp only [neg_neg, le_refl]
  have hδhalf : δ / 2 ≤ 1 := by linarith
  obtain ⟨ρmin, hρmin, ρ, hρ, hρeq, t, ht, htone, hteq, hs⟩ :=
    exists_early_allocated_affine_covered_source.{uJ,uQ} (G := G) B rows hrows hcard
      ψ hψ hrange hzero hone A T hLip hTransition block hblock hδ hδone hη
  have hρpos (P) : 0 < ρ P := hρmin.trans_le (hρ P).1
  have hfloor := allocatedAffineSourceRadius_uniform_floor_s2 (O := O) (α := α)
    B A T (half_pos hδ) hδhalf hη hE hF hηE hδF ρ hρpos hρeq
  have htlog := allocatedAffineSourceTolerance_log_bound_s2 (G := G) (O := O) (α := α)
    B A T (half_pos hδ) hδhalf hη hE hF hηE hδF
  rw [← hteq] at htlog
  have hlogs := allocatedAffine_log_costs_le_envelope B A T hdim hE hF
  refine ⟨ρ, fun P => ⟨hρpos P, (hρ P).2,
    (Real.exp_le_exp.mpr (neg_le_neg hlogs.1)).trans (hfloor P)⟩,
    hρeq, t, ht, htone, ?_, hteq, hs⟩
  exact (Real.log_le_iff_le_exp (inv_pos.mpr ht)).mp (htlog.trans hlogs.2)

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uJ, uQ, u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.exists_early_allocated_affine_bounded_source_s2_oai.{uJ, uQ, u_1, u_2, u_3, u_4, u_5}
