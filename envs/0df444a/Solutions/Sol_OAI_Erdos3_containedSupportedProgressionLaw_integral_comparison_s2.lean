-- Prove2me | solution 1 for OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:52:46.901249+00:00
-- url     : https://prove2.me/submissions/bd1836b4-0324-4e4c-92e1-1e9fe31509fb

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PrincipalCoordinatePartition
namespace OAI

section

namespace Erdos3
open scoped BigOperators
variable {D α : Type*} {B : D → Type*} {h : D → ℕ}
variable [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]

theorem principalCoordinateWeights_partition_weight (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (p : ∀ j, FiniteProbabilityWeights (IntegerScalarCubeBox α (L j))) (y : PrincipalIntegerTuples B h α L) :
    (FiniteProbabilityWeights.pi p).weight y =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).weight (principalAxisRestrict P y) *
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).weight
          (principalAxisRestrict (fun d => ¬P d) y) := by
  simp only [FiniteProbabilityWeights.pi, principalAxisRestrict, Fintype.prod_sigma]
  exact (Fintype.prod_subtype_mul_prod_subtype P
    (fun d => ∏ j : B d × Fin (h d),
      (p ⟨d,j⟩).weight (y ⟨d, j⟩))).symm

theorem principalCoordinateWeights_partition (P : D → Prop) [DecidablePred P]
    (L : PrincipalTupleIndex B h → ℕ) (p : ∀ j, FiniteProbabilityWeights (IntegerScalarCubeBox α (L j))) (f : PrincipalIntegerTuples B h α L → ℂ) :
    (FiniteProbabilityWeights.pi p).complexMean f =
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).complexMean (fun u =>
      (FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let pL := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun d : {d // P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)
  let pR := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun d : {d // ¬P d} => B d.val) (fun d => h d.val) => p ⟨j.1.val,j.2⟩)
  calc
    _ = ∑ z : PrincipalAxisTuples (α := α) P L × PrincipalAxisTuples (α := α) (fun d => ¬P d) L,
        ((pL.weight z.1 * pR.weight z.2 : ℝ) : ℂ) * f (principalAxisJoin P z.1 z.2) := by
      apply Fintype.sum_equiv (principalAxisPartitionEquiv P L)
      intro y
      simp only [principalAxisPartitionEquiv, Equiv.coe_fn_mk, principalAxisJoin_restrict]
      rw [principalCoordinateWeights_partition_weight P L p y]
    _ = _ := by
      simp only [FiniteProbabilityWeights.complexMean, Fintype.sum_prod_type,
        Complex.ofReal_mul, Finset.mul_sum, mul_assoc, pL, pR]
      rfl

end Erdos3

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

theorem containedSupportedProgressionLaw_partition (f : PrincipalIntegerTuples B h α L → ℂ) :
    (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean f =
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean (fun u =>
        (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
          (fun v => f (principalAxisJoin P u v))) := by
  let w := principalSupportedCoordinateWeights B h H hH q r hcell
  let map := containedProgressionTupleMap (α := α) B h L H step c hL hsubset
  let wL := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex BP hP => w (embed j))
  let wR := FiniteProbabilityWeights.pi (fun j : PrincipalTupleIndex
    (fun a : {a // ¬P a} => B a.val) (fun a => h a.val) => w ⟨j.1.val,j.2⟩)
  let mapL := containedProgressionTupleMap (α := α) BP hP (principalAxisLength P L) (principalAxisLength P H)
    (principalAxisLength P step) (fun j => c (embed j)) (fun j => hL (embed j)) (fun j => hsubset (embed j))
  let mapR := containedProgressionTupleMap (α := α) (fun a : {a // ¬P a} => B a.val) (fun a => h a.val)
    (principalAxisLength (fun a => ¬P a) L) (principalAxisLength (fun a => ¬P a) H)
    (principalAxisLength (fun a => ¬P a) step) (fun j => c ⟨j.1.val,j.2⟩)
    (fun j => hL ⟨j.1.val,j.2⟩) (fun j => hsubset ⟨j.1.val,j.2⟩)
  have hjoin (u : PrincipalAxisTuples (α := α) P H) (v : PrincipalAxisTuples (α := α) (fun a => ¬P a) H) :
      map (principalAxisJoin P u v) = principalAxisJoin P (mapL u) (mapR v) := by
    funext j
    rcases j with ⟨a, bv⟩
    by_cases ha : P a <;>
      simp only [map, mapL, mapR, containedProgressionTupleMap, principalAxisJoin, ha, ↓reduceDIte] <;> rfl
  have hpart := principalCoordinateWeights_partition P H w (fun y => f (map y))
  have hpart' := hpart.trans (congrArg (fun g => wL.complexMean g) (funext (fun u =>
    congrArg (fun g => wR.complexMean g) (funext (fun v => congrArg f (hjoin u v))))))
  have hleft := (conditioned).fiberLaw_complexMean map f
  have hright := wL.fiberLaw_complexMean mapL (fun u =>
    (wR.fiberLaw mapR).complexMean (fun v => f (principalAxisJoin P u v)))
  have hinner (u : PrincipalAxisTuples (α := α) P L) :=
    wR.fiberLaw_complexMean mapR (fun v => f (principalAxisJoin P u v))
  have hright' := hright.trans (congrArg (fun g => wL.complexMean g)
    (funext (fun u => hinner (mapL u))))
  exact hleft.trans ((congrArg (fun p => p.complexMean (fun y => f (map y)))
    (principalSupportedResidueWeights_eq_pi B h H hH q r hcell)).trans (hpart'.trans hright'.symm))

theorem containedSupportedProgressionLaw_partition_comparison
    (f : PrincipalIntegerTuples B h α L → ℂ) (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f (principalAxisJoin P u v)) - g u‖ ≤ E) :
    ‖(containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean f -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  rw [containedSupportedProgressionLaw_partition B h L H step c hL hH hsubset q r hcell P f]
  exact ((containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).norm_complexMean_sub_le
    _ _ (fun _ => E) hpoint).trans_eq (FiniteProbabilityWeights.mean_const _ E)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
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

theorem containedSupportedProgressionLaw_integral_comparison_s2_oai
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → PrincipalIntegerTuples B h α L → ℂ) (hf : ∀ y, Integrable (fun p => f p y) μ)
    (g : PrincipalAxisTuples (α := α) P L → ℂ) {E : ℝ}
    (hpoint : ∀ u,
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).weight u ≠ 0 →
      ‖(∫ p, (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).complexMean
        (fun v => f p (principalAxisJoin P u v)) ∂μ) - g u‖ ≤ E) :
    ‖(∫ p, (containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell).complexMean (f p) ∂μ) -
      (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell P).complexMean g‖ ≤ E := by
  rw [FiniteProbabilityWeights.integral_complexMean _ μ f hf]
  apply containedSupportedProgressionLaw_partition_comparison B h L H step c hL hH hsubset q r hcell P
  intro u hu
  have he := (containedSupportedProgressionAxisLaw B h L H step c hL hH hsubset q r hcell (fun a => ¬P a)).integral_complexMean
    μ (fun p v => f p (principalAxisJoin P u v)) (fun v => hf (principalAxisJoin P u v))
  exact he ▸ hpoint u hu

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison_s2_oai.{u_1, u_2, u_3, u_4} := @OAI.Erdos3.containedSupportedProgressionLaw_integral_comparison_s2_oai.{u_1, u_2, u_3, u_4}
