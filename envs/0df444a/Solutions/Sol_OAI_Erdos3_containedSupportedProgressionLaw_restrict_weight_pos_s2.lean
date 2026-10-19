-- Prove2me | solution 1 for OAI.Erdos3.containedSupportedProgressionLaw_restrict_weight_pos_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:54:10.802742+00:00
-- url     : https://prove2.me/submissions/d695298e-3d25-416d-92e2-0eb3897bd154

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

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

theorem toPMF_toReal (p : FiniteProbabilityWeights X) (x : X) :
    (p.toPMF x).toReal = p.weight x := by
  rw [toPMF_apply, ENNReal.toReal_ofReal (p.nonneg x)]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteFiberPMF
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped Classical

theorem toPMF_fiberLaw {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (f : X → Y) :
    (p.fiberLaw f).toPMF = p.toPMF.map f := by
  ext y
  apply (ENNReal.toReal_eq_toReal_iff' ((p.fiberLaw f).toPMF.apply_ne_top y)
    ((p.toPMF.map f).apply_ne_top y)).mp
  rw [toPMF_toReal, toPMF_map_toReal]
  rfl

end Erdos3.FiniteProbabilityWeights

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ContainedFullIntervalResidueIdentity
namespace OAI

section

namespace Erdos3

open scoped Classical NNReal

theorem FiniteProbabilityWeights.toPMF_injective {X : Type*} [Fintype X] :
    Function.Injective (fun p : FiniteProbabilityWeights X => p.toPMF) := by
  intro p q hpq
  change p.toPMF = q.toPMF at hpq
  have hw : p.weight = q.weight := by
    funext x
    exact (FiniteProbabilityWeights.toPMF_toReal p x).symm.trans
      ((congrArg (fun μ : PMF X => (μ x).toReal) hpq).trans
        (FiniteProbabilityWeights.toPMF_toReal q x))
  cases p
  cases q
  cases hw
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (P : D → Prop) [DecidablePred P]

local notation "BP" => (fun a : {a // P a} => B (Subtype.val a))
local notation "hP" => (fun a : {a // P a} => h (Subtype.val a))
local notation "embed" => (fun j : PrincipalTupleIndex BP hP => (Sigma.mk (Subtype.val (Sigma.fst j)) (Sigma.snd j) : PrincipalTupleIndex B h))
local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

theorem containedSupportedProgressionLaw_axis_marginal :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).toPMF.map
      (principalAxisRestrict P) =
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).toPMF := by
  let w := principalSupportedCoordinateWeights B h H hH q r hcell
  have hinj : Function.Injective embed := by
    intro a b hab
    rcases a with ⟨⟨a, ha⟩, av⟩
    rcases b with ⟨⟨b, hb⟩, bv⟩
    cases hab
    rfl
  have hraw := FiniteProbabilityWeights.pi_condition_positive_fiber_marginal
    (fun j => integerScalarCubeWeights α (H j) (hH j))
    (fun j (z : IntegerScalarCubeBox α (H j)) a => ((z a : ℤ) : ZMod q)) r hcell embed hinj
  have hpi := FiniteProbabilityWeights.toPMF_pi (fun j : PrincipalTupleIndex BP hP => w (embed j))
  have hraw' : (conditioned).toPMF.map (principalAxisRestrict P) =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j))).toPMF := hraw.trans hpi.symm
  have hm := congrArg (fun p => p.map (containedProgressionTupleMap BP hP
      (principalAxisLength P L) (principalAxisLength P H) (principalAxisLength P step)
      (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))) hraw'
  rw [PMF.map_comp] at hm
  have hout := FiniteProbabilityWeights.toPMF_fiberLaw
    (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j)))
    (containedProgressionTupleMap BP hP (principalAxisLength P L) (principalAxisLength P H)
      (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j)))
  simp only [containedSupportedProgressionLaw, containedSupportedProgressionAxisLaw,
    FiniteProbabilityWeights.toPMF_fiberLaw, PMF.map_comp]
  refine Eq.trans ?_ (hm.trans hout.symm)
  apply congrArg (fun f : PrincipalIntegerTuples B h α H → PrincipalAxisTuples (α := α) P L =>
    (conditioned).toPMF.map f)
  funext y j
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedSlicedResidue
namespace OAI

section

namespace Erdos3
open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionAxisLaw_fiberLaw (P : D → Prop) [DecidablePred P] :
    (law).fiberLaw (principalAxisRestrict P) =
      containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P := by
  apply FiniteProbabilityWeights.toPMF_injective
  exact (FiniteProbabilityWeights.toPMF_fiberLaw (law) (principalAxisRestrict P)).trans
    (containedSupportedProgressionLaw_axis_marginal B h L H step c hL hH hsubset q r hcell P)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ContainedSupportedProgressionReference
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

private theorem fiberLaw_weight_pos_of_pos {X Y : Type*} [Fintype X] [Fintype Y]
    (p : FiniteProbabilityWeights X) (f : X → Y) (x : X) (hx : 0 < p.weight x) :
    0 < (p.fiberLaw f).weight (f x) := by
  change 0 < ∑ y, p.weight y * (if f y = f x then (1 : ℝ) else 0)
  apply Finset.sum_pos'
  · intro y _
    exact mul_nonneg (p.nonneg y) (by split_ifs <;> norm_num)
  · exact ⟨x, Finset.mem_univ _, by simpa using hx⟩

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_restrict_weight_pos_s2_oai
    (y : PrincipalIntegerTuples B h α L) (hy : 0 < (law).weight y) (P : D → Prop) :
    0 < (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight
      (principalAxisRestrict P y) := by
  rw [← containedSupportedProgressionAxisLaw_fiberLaw B h L H step c hL hH hsubset q r hcell P]
  exact fiberLaw_weight_pos_of_pos (law) (principalAxisRestrict P) y hy

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Erdos3.containedSupportedProgressionLaw_restrict_weight_pos_s2_oai.{u_1, u_2, u_3} := @OAI.Erdos3.containedSupportedProgressionLaw_restrict_weight_pos_s2_oai.{u_1, u_2, u_3}
