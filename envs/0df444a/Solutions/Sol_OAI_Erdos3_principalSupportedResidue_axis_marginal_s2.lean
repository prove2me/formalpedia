-- Prove2me | solution 1 for OAI.Erdos3.principalSupportedResidue_axis_marginal_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:08:17.397957+00:00
-- url     : https://prove2.me/submissions/22d03b42-f67d-444b-aa52-196c98813695

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B126
import Definitions.Def_OAIE3v2B136
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrincipalCoefficientMarginal
namespace OAI

section

namespace Erdos3

open MeasureTheory ProbabilityTheory

theorem dependentProductPMF_marginal {I J : Type*} [Fintype I] [Fintype J]
    {X : I → Type*} [∀ i, Countable (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, PMF (X i)) (e : J → I) (he : Function.Injective e) :
    (dependentProductPMF p).map (fun (x : ∀ i, X i) (j : J) => x (e j)) =
      dependentProductPMF (fun j => p (e j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun (x : ∀ i, X i) (j : J) => x (e j)) _ (by fun_prop)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  have hind : iIndepFun (fun i (x : ∀ i, X i) => x i)
      (Measure.pi (fun i => (p i).toMeasure)) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
  have hsel := iIndepFun.precomp he hind
  have hm := hsel.map_fun_eq_pi_map (fun j => (measurable_pi_apply (e j)).aemeasurable)
  apply hm.trans
  congr 1
  funext j
  exact (measurePreserving_eval (fun i => (p i).toMeasure) (e j)).map_eq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.IndependentFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {Ω : J → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]

theorem pi_condition (p : ∀ j, FiniteProbabilityWeights (Ω j))
    (G : ∀ j, Finset (Ω j)) (hG : ∀ j, 0 < (p j).mass (G j)) :
    pi (fun j => (p j).condition (G j) (hG j)) =
      (pi p).condition (piRestrictionSet G) (piRestriction_mass_pos p G hG) := by
  classical
  apply ext_weight
  funext x
  change (∏ j, (if x j ∈ G j then (p j).weight (x j) else 0) / (p j).mass (G j)) =
    (if x ∈ piRestrictionSet G then ∏ j, (p j).weight (x j) else 0) /
      (pi p).mass (piRestrictionSet G)
  rw [piRestriction_mass, Finset.prod_div_distrib]
  congr 1
  by_cases hx : ∀ j, x j ∈ G j
  · simp only [hx, ite_true, (mem_piRestrictionSet G x).mpr hx]
  · rw [if_neg ((mem_piRestrictionSet G x).not.mpr hx)]
    obtain ⟨j, hj⟩ := not_forall.mp hx
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedFrozenTupleGrouping
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dependentProductPMF_curry {B C : Type*} [Fintype B] [Fintype C]
    {X : B → C → Type*} [∀ b c, Countable (X b c)] [∀ b c, MeasurableSpace (X b c)]
    [∀ b c, MeasurableSingletonClass (X b c)] (p : ∀ b c, PMF (X b c)) :
    (dependentProductPMF (fun bc : B × C => p bc.1 bc.2)).map
      (fun x b c => x (b, c)) = dependentProductPMF (fun b => dependentProductPMF (p b)) := by
  have hinj : Function.Injective (fun (x : ∀ bc : B × C, X bc.1 bc.2) b c => x (b, c)) := by
    intro x y h
    funext bc
    exact congrFun (congrFun h bc.1) bc.2
  ext y
  let x : ∀ bc : B × C, X bc.1 bc.2 := fun bc => y bc.1 bc.2
  change (dependentProductPMF (fun bc : B × C => p bc.1 bc.2)).map
    (fun z b c => z (b, c)) (fun b c => x (b, c)) = _
  rw [pmf_map_injective_at _ _ hinj]
  simp only [dependentProductPMF_apply, Fintype.prod_prod_type, x]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.IndependentEmbeddedMixture
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {J : Type*} [Fintype J] [DecidableEq J]
  {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
  [∀ j, DecidableEq (R j)]

theorem pi_condition_fiber (p : ∀ j, FiniteProbabilityWeights (X j))
    (F : ∀ j, X j → R j) (r : ∀ j, R j)
    (hr : ∀ j, 0 < (p j).mass (Finset.univ.filter (fun x => F j x = r j))) :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r))
        (pi_fiber_mass_pos p F r hr) =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j)) (hr j)) := by
  simpa only [← pi_fiber_set F r] using
    (pi_condition p (fun j => Finset.univ.filter (fun x => F j x = r j)) hr).symm

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveFiberMarginal
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {J : Type*} [Fintype J] [DecidableEq J]
variable {X R : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
variable [∀ j, DecidableEq (R j)]
variable (p : ∀ j, FiniteProbabilityWeights (X j))
variable (F : ∀ j, X j → R j) (r : ∀ j, R j)
variable (hcell : 0 < (pi p).mass
  (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)))

theorem pi_condition_positive_fiber :
    (pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) hcell =
      pi (fun j => (p j).condition (Finset.univ.filter (fun x => F j x = r j))
        (coordinate_fiber_mass_pos p F r hcell j)) :=
  pi_condition_fiber p F r (coordinate_fiber_mass_pos p F r hcell)

theorem pi_condition_positive_fiber_marginal
    [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    {V : Type*} [Fintype V] (e : V → J) (he : Function.Injective e) :
    ((pi p).condition (Finset.univ.filter (fun x => (fun j => F j (x j)) = r)) hcell).toPMF.map
        (fun x v => x (e v)) =
      dependentProductPMF (fun v =>
        ((p (e v)).condition (Finset.univ.filter (fun x => F (e v) x = r (e v)))
          (coordinate_fiber_mass_pos p F r hcell (e v))).toPMF) := by
  rw [pi_condition_positive_fiber]
  have hp := toPMF_pi (fun j =>
    (p j).condition (Finset.univ.filter (fun x => F j x = r j))
      (coordinate_fiber_mass_pos p F r hcell j))
  exact (congrArg (fun μ : PMF (∀ j, X j) => μ.map (fun x v => x (e v))) hp).trans
    (dependentProductPMF_marginal _ e he)

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.AllocatedActiveAxisSourceLaw
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem normalizedUniformCubeSource_toPMF (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ L) :
    (normalizedUniformCubeSource I L M hL m r hm hmM hsize).source.toPMF =
      (scalarCubeResidueWeights I L M hL m r hm hmM hsize).toPMF := by
  ext x
  change ENNReal.ofReal ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x * 1) =
    ENNReal.ofReal ((scalarCubeResidueWeights I L M hL m r hm hmM hsize).weight x)
  rw [mul_one]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem scalarCubeResidue_fiber_eq {α : Type*} [Fintype α] [DecidableEq α]
    (L q : ℕ) (r : Option α → ZMod q) :
    Finset.univ.filter (fun x : IntegerScalarCubeBox α L =>
      (fun i => ((x i : ℤ) : ZMod q)) = r) =
        scalarCubeResidueSet α L (fun _ => q) r := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    mem_scalarCubeResidueSet, funext_iff]

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem principalSupportedResidue_marginal {V : Type*} [Fintype V]
    (e : V → PrincipalTupleIndex B h) (he : Function.Injective e)
    (hsize : ∀ v, (Fintype.card α + 1) * q ≤ L (e v)) :
    ((principalTupleWeights (α := α) B h L hL).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
        (fun y v => y (e v)) =
      dependentProductPMF (fun v =>
        (normalizedUniformCubeSource α (L (e v)) q (hL (e v)) (fun _ => q) (r (e v))
          (fun _ => hq) (fun _ => le_rfl) (hsize v)).source.toPMF) := by
  have hpositive : 0 < (FiniteProbabilityWeights.pi
      (fun t => integerScalarCubeWeights α (L t) (hL t))).mass
        (Finset.univ.filter (fun y => (fun t i => ((y t i : ℤ) : ZMod q)) = r)) := hcell
  have hp := FiniteProbabilityWeights.pi_condition_positive_fiber_marginal
    (fun t => integerScalarCubeWeights α (L t) (hL t))
    (fun t (x : IntegerScalarCubeBox α (L t)) i => ((x i : ℤ) : ZMod q)) r hpositive e he
  refine hp.trans ?_
  apply congrArg (fun p : ∀ v, PMF (IntegerScalarCubeBox α (L (e v))) => dependentProductPMF p)
  funext v
  rw [normalizedUniformCubeSource_toPMF]
  simp only [scalarCubeResidueWeights]
  congr 2
  exact scalarCubeResidue_fiber_eq (L (e v)) q (r (e v))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem principalSupportedResidue_axis_marginal_s2_oai :
    ((principalTupleWeights (α := α) B h L hL).condition
      (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell).toPMF.map
        (fun y (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩) =
      dependentProductPMF (fun b => dependentProductPMF (fun v => ((sources) b v).source.toPMF)) := by
  have hp := principalSupportedResidue_marginal B h L hL q hq r hcell
    (fun t : B a × Fin (h a) => ⟨a, t⟩)
    (by intro x y hxy; simpa using hxy) (fun t => hsize t.1 t.2)
  have ht := congrArg (fun p => p.map (fun x b v => x (b, v))) hp
  rw [PMF.map_comp] at ht
  exact ht.trans (dependentProductPMF_curry
    (fun b v => ((sources) b v).source.toPMF))

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.principalSupportedResidue_axis_marginal_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.principalSupportedResidue_axis_marginal_s2_oai.{u_1, u_2, u_3}
