-- Prove2me | solution 1 for OAI.Erdos3.principalSupportedResidue_selected_kernels_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:59:45.883205+00:00
-- url     : https://prove2.me/submissions/e496818d-23b6-4ad5-ad6f-791cda70463b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B218

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FiniteIndependentKernels
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

universe uA uX uY uZ

theorem dependentProductPMF_finite_bind
    {A : Type uA} [Fintype A] {X : A → Type uX} {Y : A → Type uY}
    [∀ a, Fintype (X a)] [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (p : ∀ a, PMF (X a)) (q : ∀ a, X a → PMF (Y a)) :
    (dependentProductPMF p).bind (fun x => dependentProductPMF (fun a => q a (x a))) =
      dependentProductPMF (fun a => (p a).bind (q a)) := by
  classical
  ext y
  simp only [PMF.bind_apply, tsum_fintype, dependentProductPMF_apply,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun a x => p a x * q a x (y a))).symm

theorem dependentProductPMF_eval
    {A : Type uA} [Fintype A] {X : A → Type uX}
    [∀ a, Countable (X a)] [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    (p : ∀ a, PMF (X a)) (a : A) :
    (dependentProductPMF p).map (fun x => x a) = p a := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map (fun x => x a) (dependentProductPMF p) (by fun_prop)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  exact (measurePreserving_eval (fun a => (p a).toMeasure) a).map_eq

theorem pmf_bind_of_finite_independent_coordinates
    {A : Type uA} [Fintype A] {X : A → Type uX} {Y : A → Type uY} {Z : Type uZ}
    [∀ a, Fintype (X a)] [∀ a, MeasurableSpace (X a)] [∀ a, MeasurableSingletonClass (X a)]
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (p : PMF Z) (g : Z → ∀ a, X a) (t : ∀ a, PMF (X a))
    (ht : p.map g = dependentProductPMF t) (q : ∀ a, X a → PMF (Y a)) :
    p.bind (fun z => dependentProductPMF (fun a => q a (g z a))) =
      dependentProductPMF (fun a => p.bind (fun z => q a (g z a))) := by
  have hcoord (a : A) : p.map (fun z => g z a) = t a :=
    (PMF.map_comp g p (fun x => x a)).symm.trans
      ((congrArg (fun μ : PMF (∀ a, X a) => μ.map (fun x => x a)) ht).trans
        (dependentProductPMF_eval t a))
  have hlocal (a : A) : p.bind (fun z => q a (g z a)) = (t a).bind (q a) :=
    (PMF.bind_map p (fun z => g z a) (q a)).symm.trans
      (congrArg (fun μ : PMF (X a) => μ.bind (q a)) (hcoord a))
  calc
    _ = (p.map g).bind (fun x => dependentProductPMF (fun a => q a (x a))) :=
      (PMF.bind_map p g (fun x => dependentProductPMF (fun a => q a (x a)))).symm
    _ = (dependentProductPMF t).bind (fun x => dependentProductPMF (fun a => q a (x a))) :=
      congrArg (fun μ : PMF (∀ a, X a) => μ.bind
        (fun x => dependentProductPMF (fun a => q a (x a)))) ht
    _ = dependentProductPMF (fun a => (t a).bind (q a)) := dependentProductPMF_finite_bind t q
    _ = _ := congrArg (fun μ : ∀ a, PMF (Y a) => dependentProductPMF μ)
      (funext (fun a => (hlocal a).symm))

end Erdos3

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

theorem dependentProductPMF_sigma_curry
    {A : Type*} [Fintype A] {B C : A → Type*}
    [∀ a, Fintype (B a)] [∀ a, Fintype (C a)]
    {X : ∀ a, B a → C a → Type*}
    [∀ a b c, Countable (X a b c)] [∀ a b c, MeasurableSpace (X a b c)]
    [∀ a b c, MeasurableSingletonClass (X a b c)]
    (p : ∀ a b c, PMF (X a b c)) :
    (dependentProductPMF (fun i : Σ a, B a × C a => p i.1 i.2.1 i.2.2)).map
      (fun x a b c => x ⟨a, b, c⟩) =
      dependentProductPMF (fun a => dependentProductPMF (fun b => dependentProductPMF (p a b))) := by
  have hinj : Function.Injective
      (fun (x : ∀ i : Σ a, B a × C a, X i.1 i.2.1 i.2.2) a b c => x ⟨a, b, c⟩) := by
    intro x y h
    funext i
    exact congrFun (congrFun (congrFun h i.1) i.2.1) i.2.2
  ext y
  let x : ∀ i : Σ a, B a × C a, X i.1 i.2.1 i.2.2 := fun i => y i.1 i.2.1 i.2.2
  change (dependentProductPMF (fun i : Σ a, B a × C a => p i.1 i.2.1 i.2.2)).map
    (fun z a b c => z ⟨a, b, c⟩) (fun a b c => x ⟨a, b, c⟩) = _
  rw [pmf_map_injective_at _ _ hinj]
  simp only [dependentProductPMF_apply, Fintype.prod_sigma, Fintype.prod_prod_type, x]

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

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell
local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem principalSupportedResidueWeights_eq_pi :
    (conditioned) = FiniteProbabilityWeights.pi (coord) :=
  FiniteProbabilityWeights.pi_condition_positive_fiber
    (fun t => integerScalarCubeWeights α (L t) (hL t))
    (fun t (z : IntegerScalarCubeBox α (L t)) i => ((z i : ℤ) : ZMod q)) r hcell

theorem principalSupportedResiduePMF_eq_product :
    (conditioned).toPMF = dependentProductPMF (fun t => ((coord) t).toPMF) := by
  exact (congrArg (fun p : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) => p.toPMF)
    (principalSupportedResidueWeights_eq_pi B h L hL q r hcell)).trans
      (FiniteProbabilityWeights.toPMF_pi (coord))

theorem principalSupportedResidue_full_axis_law :
    (conditioned).toPMF.map (fun y (a : D) (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩) =
      dependentProductPMF (principalSupportedAxisTuplePMF B h L hL q r hcell) := by
  have hp := congrArg (fun p : PMF (PrincipalIntegerTuples B h α L) =>
    p.map (fun y (a : D) (b : B a) (v : Fin (h a)) => y ⟨a, b, v⟩))
    (principalSupportedResiduePMF_eq_product B h L hL q r hcell)
  exact hp.trans (dependentProductPMF_sigma_curry
    (fun a b v => ((coord) ⟨a, b, v⟩).toPMF))

theorem principalSupportedResidue_selected_axis_law {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) :
    (conditioned).toPMF.map (fun y (a : A) (b : B (e a)) (v : Fin (h (e a))) => y ⟨e a, b, v⟩) =
      dependentProductPMF (fun a => principalSupportedAxisTuplePMF B h L hL q r hcell (e a)) := by
  have hp := congrArg (fun p : PMF (∀ a : D, ∀ b : B a, ∀ v : Fin (h a),
      IntegerScalarCubeBox α (L ⟨a, b, v⟩)) => p.map (fun y a => y (e a)))
    (principalSupportedResidue_full_axis_law B h L hL q r hcell)
  rw [PMF.map_comp] at hp
  exact hp.trans (dependentProductPMF_marginal
    (principalSupportedAxisTuplePMF B h L hL q r hcell) e he)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ContainedSupportedProgressionKernels
namespace OAI

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem principalSupportedResidue_selected_kernels_s2_oai {A : Type*} [Fintype A]
    (e : A → D) (he : Function.Injective e) {Y : A → Type*}
    [∀ a, Countable (Y a)] [∀ a, MeasurableSpace (Y a)] [∀ a, MeasurableSingletonClass (Y a)]
    (k : ∀ a, (∀ b : B (e a), ∀ v : Fin (h (e a)), IntegerScalarCubeBox α (L ⟨e a, b, v⟩)) →
      PMF (Y a)) :
    (conditioned).toPMF.bind (fun y => dependentProductPMF
      (fun a => k a (fun b v => y ⟨e a, b, v⟩))) =
      dependentProductPMF (fun a => (conditioned).toPMF.bind
        (fun y => k a (fun b v => y ⟨e a, b, v⟩))) := by
  exact pmf_bind_of_finite_independent_coordinates (conditioned).toPMF
    (fun y a b v => y ⟨e a, b, v⟩)
    (fun a => principalSupportedAxisTuplePMF B h L hL q r hcell (e a))
    (principalSupportedResidue_selected_axis_law B h L hL q r hcell e he) k

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.principalSupportedResidue_selected_kernels_s2_oai.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.principalSupportedResidue_selected_kernels_s2_oai.{u_1, u_2, u_3, u_4, u_5}
