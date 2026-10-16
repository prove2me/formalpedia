-- Prove2me | solution 1 for OAI.Thorp.Fourier.coefficient_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:19:23.829496+00:00
-- url     : https://prove2.me/submissions/8bc7d8fa-bb24-4a53-a180-c2cc8059cc9f

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Reynolds.lean:L93-L113
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.coefficient_second_moment. The node keeps its source
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

lemma reynolds_scalar (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    ∃ c : ℂ, reynolds ρ ρ A = c • LinearMap.id := by
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ)).surjective (reynoldsMap ρ ρ A)
  refine ⟨c, ?_⟩
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  exact hh.symm

lemma trace_reynolds (ρ : Representation ℂ G V) [FiniteDimensional ℂ V] (A : Module.End ℂ V) :
    LinearMap.trace ℂ V (reynolds ρ ρ A) = LinearMap.trace ℂ V A := by
  simp only [reynolds, map_smul, map_sum]
  have hh (g : G) : LinearMap.trace ℂ V (ρ g ∘ₗ A ∘ₗ ρ g⁻¹) = LinearMap.trace ℂ V A := by
    rw [LinearMap.trace_comp_comm']
    rw [LinearMap.comp_assoc]
    have he : ρ g⁻¹ ∘ₗ ρ g = LinearMap.id := by
      change ρ g⁻¹ * ρ g = 1
      rw [← map_mul, inv_mul_cancel, map_one]
    rw [he, LinearMap.comp_id]
  simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul]

lemma reynolds_eq_trace (ρ : Representation ℂ G V) [Representation.IsIrreducible ρ]
    [FiniteDimensional ℂ V] (hV : Module.finrank ℂ V ≠ 0) (A : Module.End ℂ V) :
    reynolds ρ ρ A = (LinearMap.trace ℂ V A / Module.finrank ℂ V) • LinearMap.id := by
  obtain ⟨c, hc⟩ := reynolds_scalar ρ A
  have ht := trace_reynolds ρ A
  rw [hc, map_smul, LinearMap.trace_id, smul_eq_mul] at ht
  have hD : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast hV
  rw [hc, ← ht, mul_div_cancel_right₀ _ hD]

section Unitary
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma inner_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) (x y : E) :
    ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  have hh := hu g x (ρ g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh.symm

theorem coefficient_second_moment (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (v w : E) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E := by
  have hh := congrArg (fun A : Module.End ℂ E => ⟪w, A w⟫_ℂ)
    (reynolds_eq_trace ρ hE (InnerProductSpace.rankOne ℂ v v).toLinearMap)
  simp only [reynolds, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    inner_smul_right, inner_sum, ContinuousLinearMap.coe_coe,
    InnerProductSpace.rankOne_apply, map_smul, inner_inv ρ hu,
    InnerProductSpace.trace_rankOne, LinearMap.id_apply] at hh
  have hc (g : G) : ⟪ρ g v, w⟫_ℂ * ⟪w, ρ g v⟫_ℂ = (‖⟪w, ρ g v⟫_ℂ‖ ^ 2 : ℝ) := by
    rw [← inner_conj_symm (ρ g v) w, Complex.conj_mul', Complex.ofReal_pow]
  simp only [hc, inner_self_eq_norm_sq_to_K] at hh
  have hr : (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 / Module.finrank ℂ E * ‖w‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] using hh
  simpa only [div_mul_eq_mul_div] using hr

end Unitary
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Thorp.Fourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped Classical


theorem solution.{uG,uE} : type_of% @_root_.OAI.Thorp.Fourier.coefficient_second_moment.{uG,uE} := @_root_.OAI.Thorp.Fourier.coefficient_second_moment.{uG,uE}
