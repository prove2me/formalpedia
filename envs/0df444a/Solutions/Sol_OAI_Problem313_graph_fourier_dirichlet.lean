-- Prove2me | solution 1 for OAI.Problem313.graph_fourier_dirichlet
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T02:31:51.957973+00:00
-- url     : https://prove2.me/submissions/03cbd0de-48ed-4104-a74a-11383846cd44

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/FourierDirichlet.lean:L79-L97
-- (upload_full_project.md Phase 4): solution for node OAI.Problem313.graph_fourier_dirichlet. The node keeps its source
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
import Theorems.Thm_OAI_Problem313_BiasedFourier_coeff_insert_eq_sqrt_mul_delta
import Theorems.Thm_OAI_Problem313_BiasedFourier_parseval
import Theorems.Thm_OAI_Problem313_sum_supports_containing

-- ---- from OAI.Combinatorics.SharpThreshold.FourierDerivative ----
namespace OAI

universe u

noncomputable section
open scoped BigOperators
namespace Problem313.BiasedFourier

variable {ι : Type u} [DecidableEq ι]

variable [Fintype ι]

/-- A coordinate derivative has no Fourier support containing that coordinate. -/
theorem coeff_delta_eq_zero_of_mem {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) (S : Finset ι) (hi : i ∈ S) :
    coeff p (delta i g) S = 0 := by
  classical
  rw [← Finset.insert_erase hi]
  rw [coeff_insert_eq_sqrt_mul_delta hp hp1 (delta i g) i (S.erase i)
    (Finset.notMem_erase i S)]
  simp [coeff]

end Problem313.BiasedFourier

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.BooleanDerivative ----
namespace OAI

universe u

noncomputable section
namespace Problem313

namespace Reindex
variable {ι : Type u} [Fintype ι] [dι : DecidableEq ι]

theorem boolean_delta_sq_moment (p : ℝ) (f : (ι → Bool) → Bool) (i : ι) :
    (∑ x, weight p x * (boolReal (f (Function.update x i true)) -
      boolReal (f (Function.update x i false))) ^ 2) = influence p f i := by
  classical
  have hd : dι = Classical.decEq ι := Subsingleton.elim _ _
  subst dι
  simp only [boolReal_sub_sq, mul_ite, mul_one, mul_zero, influence]

end Reindex
end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.DirichletEnergy ----
namespace OAI

universe u

noncomputable section
namespace Problem313
open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Algebraic coordinate energy identity from the derivative Fourier identities. -/
theorem spectral_coordinate_energy (i : ι) (a b : Finset ι → ℝ) (σ : ℝ)
    (hzero : ∀ S, i ∈ S → b S = 0)
    (hinsert : ∀ S, i ∉ S → a (insert i S) = σ * b S) :
    (∑ S : Finset ι, if i ∈ S then (a S)^2 else 0) =
      σ^2 * ∑ S : Finset ι, (b S)^2 := by
  rw [sum_supports_containing, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  by_cases hi : i ∈ S
  · simp [hi, hzero S hi]
  · simp [hi, hinsert S hi, mul_pow]

/-- Counting each spectral support once for every coordinate it contains. -/
theorem sum_card_mul_eq_sum_mem (a : Finset ι → ℝ) :
    (∑ S : Finset ι, (S.card : ℝ) * a S) =
      ∑ i : ι, ∑ S : Finset ι, if i ∈ S then a S else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp [Finset.sum_ite_mem, nsmul_eq_mul]

end Problem313

end

end OAI

-- ---- from OAI.Combinatorics.SharpThreshold.FourierDirichlet ----
namespace OAI

universe u

noncomputable section

namespace Problem313.BiasedFourier

open Finset
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- The coordinate Dirichlet identity, with only the two derivative coefficient
identities isolated as hypotheses. -/
theorem coordinate_energy_of_coeff_derivative {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g dg : (ι → Bool) → ℝ) (i : ι)
    (hzero : ∀ S, i ∈ S → coeff p dg S = 0)
    (hinsert : ∀ S, i ∉ S → coeff p g (insert i S) =
      Real.sqrt (p * (1 - p)) * coeff p dg S) :
    (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * ∑ x, weight p x * (dg x)^2 := by
  rw [Problem313.spectral_coordinate_energy i (coeff p g) (coeff p dg)
    (Real.sqrt (p * (1 - p))) hzero hinsert]
  rw [parseval hp hp1, Real.sq_sqrt (mul_nonneg hp.le (sub_nonneg.mpr hp1.le))]

/-- Summing coordinate Dirichlet identities gives degree-weighted Fourier energy. -/
theorem total_energy_of_coordinate_energy {p : ℝ}
    (g : (ι → Bool) → ℝ) (E : ι → ℝ)
    (hcoord : ∀ i, (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * E i) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p g S)^2) =
      p * (1 - p) * ∑ i, E i := by
  rw [Problem313.sum_card_mul_eq_sum_mem]
  simp_rw [hcoord]
  rw [Finset.mul_sum]

/-- The Fourier mass on supports containing a fixed coordinate equals its
weighted squared discrete derivative. -/
theorem coordinate_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (g : (ι → Bool) → ℝ) (i : ι) :
    (∑ S : Finset ι, if i ∈ S then (coeff p g S)^2 else 0) =
      p * (1 - p) * ∑ x, weight p x * (delta i g x)^2 := by
  exact coordinate_energy_of_coeff_derivative hp hp1 g (delta i g) i
    (fun S hS => coeff_delta_eq_zero_of_mem hp hp1 g i S hS)
    (fun S hS => coeff_insert_eq_sqrt_mul_delta hp hp1 g i S hS)

/-- For Boolean observables, squared derivative energy is pivotal influence. -/
theorem boolean_coordinate_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) (i : ι) :
    (∑ S : Finset ι, if i ∈ S then (coeff p (fun x => boolReal (f x)) S)^2 else 0) =
      p * (1 - p) * Reindex.influence p f i := by
  rw [coordinate_dirichlet hp hp1]
  congr 1
  simpa only [delta, weight, scalarWeight, Reindex.weight] using
    Reindex.boolean_delta_sq_moment p f i

/-- The degree-weighted Fourier mass of a Boolean function is its total pivotal
influence times the Bernoulli variance. -/
theorem boolean_dirichlet {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : (ι → Bool) → Bool) :
    (∑ S : Finset ι, (S.card : ℝ) * (coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * ∑ i, Reindex.influence p f i := by
  exact total_energy_of_coordinate_energy _ _ (boolean_coordinate_dirichlet hp hp1 f)

end Problem313.BiasedFourier

namespace Problem313

/-- The graph Dirichlet identity for pivotal total influence. -/
theorem graph_fourier_dirichlet {n : ℕ} {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (f : GraphConfig n → Bool) :
    (∑ S : Finset (GraphEdge n), (S.card : ℝ) *
      (BiasedFourier.coeff p (fun x => boolReal (f x)) S)^2) =
      p * (1 - p) * totalInfluence p f := by
  classical
  have hi : (∑ e : GraphEdge n, Reindex.influence p f e) = totalInfluence p f := by
    unfold totalInfluence
    apply Finset.sum_congr rfl
    intro e he
    unfold Reindex.influence edgeInfluence
    apply Finset.sum_congr (by ext; simp)
    intro x hx
    congr 1
    congr 4 <;> exact Subsingleton.elim _ _
  have h := BiasedFourier.boolean_dirichlet hp hp1 f
  rw [hi] at h
  exact h

end Problem313

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem313


theorem solution : type_of% @_root_.OAI.Problem313.graph_fourier_dirichlet := @_root_.OAI.Problem313.graph_fourier_dirichlet
