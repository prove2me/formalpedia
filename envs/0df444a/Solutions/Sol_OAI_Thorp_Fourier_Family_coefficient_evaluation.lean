-- Prove2me | solution 1 for OAI.Thorp.Fourier.Family.coefficient_evaluation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:26:56.245918+00:00
-- url     : https://prove2.me/submissions/a3af8aed-27e3-4bf8-b82d-d4ce4a2d2ed7

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/JointProjectors.lean:L29-L43
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.Family.coefficient_evaluation. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors
import Theorems.Thm_OAI_Thorp_Fourier_Family_kernel_sum_sq

-- ---- from OAI.Probability.ThorpShuffle.Reynolds ----
namespace OAI

universe uG uV uW uE uI

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

open scoped BigOperators ComplexConjugate InnerProductSpace

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

section Unitary
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

end Unitary
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

lemma integrated_sum {I : Type uI} (ρ : Representation ℂ G V) (s : Finset I) (f : I → G → ℂ) :
    integrated ρ (∑ i ∈ s, f i) = ∑ i ∈ s, integrated ρ (f i) := by
  simp only [integrated, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

end Thorp.Fourier

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.JointProjectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uI uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

lemma complex_cauchy {I : Type uI} (s : Finset I) (a b : I → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have ht : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => a i * b i)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem coefficient_evaluation (ρ : Representation ℂ G E) (s : Finset F.Index)
    (v w : E) (hv : (∑ i ∈ s, F.projector ρ i) v = v) :
    (Fintype.card G : ℝ) * ‖⟪w, v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 := by
  have he : ⟪w, v⟫_ℂ = ∑ g, (∑ i ∈ s, F.kernel i g) * ⟪w, ρ g v⟫_ℂ := by
    conv_lhs => rw [← hv]
    conv_lhs => rw [show ∑ i ∈ s, F.projector ρ i = integrated ρ (∑ i ∈ s, F.kernel i) by
      simp only [projector, integrated_sum]]
    simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right,
      Finset.sum_apply]
  have hh := mul_le_mul_of_nonneg_left
    (complex_cauchy Finset.univ (fun g => ∑ i ∈ s, F.kernel i g) (fun g => ⟪w, ρ g v⟫_ℂ))
    (Nat.cast_nonneg (α := ℝ) (Fintype.card G))
  rw [← he, ← mul_assoc, F.kernel_sum_sq] at hh
  exact hh

end Family
end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

end Thorp.Fourier.Family

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical


theorem solution.{uE} : type_of% @_root_.OAI.Thorp.Fourier.Family.coefficient_evaluation.{uE} := @_root_.OAI.Thorp.Fourier.Family.coefficient_evaluation.{uE}
