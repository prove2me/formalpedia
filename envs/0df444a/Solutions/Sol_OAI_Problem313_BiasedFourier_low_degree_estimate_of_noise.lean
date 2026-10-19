-- Prove2me | solution 1 for OAI.Problem313.BiasedFourier.low_degree_estimate_of_noise
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T03:34:59.47133+00:00
-- url     : https://prove2.me/submissions/948b8962-6eef-4188-87ec-be9da688756b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/LowDegree.lean:L19-L61
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.BiasedFourier.low_degree_estimate_of_noise. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption
import Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockCounting
import Definitions.Def_OAI_Combinatorics_SharpThreshold_GraphBlockCapture
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Permutation
import Definitions.Def_OAI_Combinatorics_SharpThreshold_InfluenceReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockRestrictionSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockSymmetry
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbits
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Probability
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierVariance
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RussoReindex
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BooleanDerivative
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionInfluence
import Definitions.Def_OAI_Combinatorics_SharpThreshold_RestrictionMassSubtype
import Definitions.Def_OAI_Combinatorics_SharpThreshold_ProjectionIdentities
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierProjection
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOptionExpectation
import Theorems.Thm_OAI_Problem313_BiasedFourier_booleanDifference_project_energy_le
import Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_insert_eq_sqrt_mul_delta
import Theorems.Thm_OAI_Problem313_BiasedFourier_parseval
import Theorems.Thm_OAI_Problem313_lowDegree_bound_of_projection

-- ---- from OAI.Combinatorics.SharpThreshold.InfluenceReindex ----
namespace OAI

universe u v

noncomputable section

namespace Problem313
namespace Reindex

variable {ι : Type u} {κ : Type v}

theorem weight_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : ι → Bool) : 0 ≤ weight p x := by
  unfold weight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> linarith

theorem influence_nonneg [Fintype ι] {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (f : (ι → Bool) → Bool) (i : ι) : 0 ≤ influence p f i := by
  classical
  unfold influence
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact weight_nonneg hp0 hp1 x
  · exact le_rfl

end Reindex
end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.FourierVariance ----
namespace OAI

universe u v

noncomputable section

open scoped BigOperators Classical

namespace Problem313.BiasedFourier

variable {ι : Type u} [Fintype ι]

/-- The total mass of the finite Bernoulli product is one, algebraically for every bias. -/
theorem weight_mass_one (p : ℝ) : ∑ x : ι → Bool, weight p x = 1 := by
  unfold weight
  rw [← Fintype.prod_sum]
  simp [scalarWeight]

theorem weight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (x : ι → Bool) :
    0 ≤ weight p x := by
  apply Finset.prod_nonneg
  intro i hi
  unfold scalarWeight
  split_ifs <;> linarith

/-- A Boolean function has total Fourier mass at most one. -/
theorem boolean_spectral_mass_le_one {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, coeff p (fun x => boolReal (f x)) S ^ 2) ≤ 1 := by
  rw [parseval hp hp1]
  calc
    (∑ x, weight p x * boolReal (f x) ^ 2) ≤ ∑ x : ι → Bool, weight p x := by
      apply Finset.sum_le_sum
      intro x hx
      rw [boolReal_sq]
      exact mul_le_of_le_one_right (weight_nonneg hp.le hp1.le x) (boolReal_le_one (f x))
    _ = 1 := weight_mass_one p

end Problem313.BiasedFourier

namespace Problem313

open BiasedFourier

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.FourierDerivative ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313.BiasedFourier

variable {ι : Type u} [DecidableEq ι]

variable [Fintype ι]

/-- Erasing a coordinate from a nonzero-degree coefficient gives the derivative coefficient. -/
theorem coeff_eq_sqrt_mul_delta_erase {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p g S = Real.sqrt (p * (1-p)) * coeff p (delta i g) (S.erase i) := by
  conv_lhs => rw [← Finset.insert_erase hi]
  exact coeff_insert_eq_sqrt_mul_delta hp hp1 g i (S.erase i) (Finset.notMem_erase i S)

/-- Squared Fourier derivative identity, in the normalization used by Dirichlet energy. -/
theorem coeff_sq_eq_variance_mul_delta_erase_sq {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p g S ^ 2 = p * (1-p) * coeff p (delta i g) (S.erase i) ^ 2 := by
  rw [coeff_eq_sqrt_mul_delta_erase hp hp1 g i S hi, mul_pow,
    Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le))]

end Problem313.BiasedFourier

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BooleanProjection ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The Boolean coordinate-difference energy bound with a real degree cutoff. -/
theorem booleanDifference_lowDegree_energy_le {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (rho k : ℝ) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, rho ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2)
    (f : (ι → Bool) → Bool) (i : ι) :
    (∑ S ∈ (Finset.univ.filter fun S : Finset ι => (S.card : ℝ) ≤ k),
      (coeff p (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S) ^ 2) ≤
      rho ^ (-2 * k) * (Reindex.influence p f i) ^ (3 / 2 : ℝ) := by
  apply booleanDifference_project_energy_le hp hp1 rho k hrho hrho1 hnoise _ f i
  intro S hS
  exact (Finset.mem_filter.mp hS).2

end Problem313.BiasedFourier

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.LowDegree ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open scoped BigOperators Classical

variable {ι : Type u} [Fintype ι]

/-- The biased low-degree influence estimate, with the product noise
contraction as its only remaining analytic premise. -/
theorem low_degree_estimate_of_noise {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (m : ℝ) (hm : 1 ≤ m)
    (horbit : ∀ i, Reindex.influence p f i ≤ (∑ j, Reindex.influence p f j) / m)
    (hnoise : ∀ a : Finset ι → ℝ,
      (∑ x, weight p x *
        (∑ S, (Real.sqrt (p * (1 - p)) / 4) ^ S.card * a S * char p S x) ^ 4) ≤
          (∑ S, (a S) ^ 2) ^ 2) :
    (∑ S : Finset ι,
      if S.Nonempty ∧ (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f x)) S ^ 2 else 0) ≤
        m ^ (-1 / 4 : ℝ) * ∑ i, Reindex.influence p f i := by
  have hvar : 0 < p * (1 - p) := mul_pos hp (sub_pos.mpr hp1)
  have hσ : 0 < Real.sqrt (p * (1 - p)) := Real.sqrt_pos.mpr hvar
  have hσhalf : Real.sqrt (p * (1 - p)) ≤ 1 / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith [sq_nonneg (p - 1 / 2)]
  have hρ : 0 < Real.sqrt (p * (1 - p)) / 4 := by positivity
  have hρ1 : Real.sqrt (p * (1 - p)) / 4 ≤ 1 := by linarith
  refine lowDegree_bound_of_projection
    (fun S => coeff p (fun x => boolReal (f x)) S ^ 2)
    (fun i S => coeff p (delta i (fun x => boolReal (f x))) S ^ 2)
    (Reindex.influence p f) (Real.sqrt (p * (1 - p))) m hσ hσhalf hm
    (fun S => sq_nonneg _) (fun i S => sq_nonneg _)
    (Reindex.influence_nonneg hp.le hp1.le f) horbit
    (boolean_spectral_mass_le_one hp hp1 f) ?_ ?_
  · intro i S hi
    rw [Real.sq_sqrt hvar.le]
    exact coeff_sq_eq_variance_mul_delta_erase_sq hp hp1
      (fun x => boolReal (f x)) i S hi
  · intro i
    change (∑ S : Finset ι,
      if (S.card : ℝ) ≤ Real.sqrt (p * (1 - p)) * Real.log m / 64
      then coeff p (fun x => boolReal (f (Function.update x i true)) -
        boolReal (f (Function.update x i false))) S ^ 2 else 0) ≤ _
    simpa only [Finset.sum_filter] using
      booleanDifference_lowDegree_energy_le hp hp1
        (Real.sqrt (p * (1 - p)) / 4)
        (Real.sqrt (p * (1 - p)) * Real.log m / 64)
        hρ hρ1 hnoise f i

end Problem313.BiasedFourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313 OAI.Problem313.BiasedFourier
open scoped BigOperators Classical


theorem solution.{u} : type_of% @_root_.OAI.Problem313.BiasedFourier.low_degree_estimate_of_noise.{u} := @_root_.OAI.Problem313.BiasedFourier.low_degree_estimate_of_noise.{u}
