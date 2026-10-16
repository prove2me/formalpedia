-- Prove2me | solution 1 for OAI.Thorp.Fourier.Family.kernel_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:23:39.389208+00:00
-- url     : https://prove2.me/submissions/d718f082-d276-4ff7-a5e5-60bd054199d5

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean:L103-L116
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.Family.kernel_convolution. The node keeps its source
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
import Theorems.Thm_OAI_Thorp_Fourier_Family_integrated_kernel

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

lemma integrated_sub (ρ : Representation ℂ G V) (f k : G → ℂ) :
    integrated ρ (f - k) = integrated ρ f - integrated ρ k := by
  simp only [integrated, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

lemma integrated_convolution (ρ : Representation ℂ G V) (f k : G → ℂ) :
    integrated ρ (convolution f k) = integrated ρ f * integrated ρ k := by
  simp only [integrated, convolution, Finset.sum_smul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have he := Equiv.sum_comp (Equiv.mulLeft g) (fun x => (f g * k (g⁻¹ * x)) • ρ x)
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  simp only [Equiv.coe_mulLeft, inv_mul_cancel_left, map_mul, smul_mul_smul]

end Thorp.Fourier

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.FourierFamilies ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uG uE uV

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

attribute [instance] Family.finiteIndex Family.normed Family.innerSpace Family.finiteDim Family.irreducible

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma integrated_faithful (f : G → ℂ) (hf : ∀ i, integrated (F.rep i) f = 0) : f = 0 := by
  funext x
  have hh : ∑ i, (F.degree i : ℂ) * LinearMap.trace ℂ (F.Space i)
      (integrated (F.rep i) f * F.rep i x⁻¹) = 0 := by simp [hf]
  simp only [integrated, Finset.sum_mul, smul_mul_assoc, ← map_mul, map_sum, map_smul, smul_eq_mul] at hh
  change ∑ i, (F.degree i : ℂ) * ∑ g, f g * (F.rep i).character (g * x⁻¹) = 0 at hh
  simp_rw [Finset.mul_sum] at hh
  rw [Finset.sum_comm] at hh
  have he (g : G) : ∑ i, (F.degree i : ℂ) * (f g * (F.rep i).character (g * x⁻¹)) =
      f g * (if g * x⁻¹ = 1 then (Fintype.card G : ℂ) else 0) := by
    rw [← F.regular]
    simp only [Finset.mul_sum, degree]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [he, mul_inv_eq_one, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at hh
  exact (mul_eq_zero.mp hh).resolve_right (by exact_mod_cast Fintype.card_ne_zero)

lemma integrated_injective (f k : G → ℂ) (h : ∀ i, integrated (F.rep i) f = integrated (F.rep i) k) : f = k := by
  apply sub_eq_zero.mp
  apply F.integrated_faithful
  intro i
  rw [integrated_sub, h i, sub_self]

lemma kernel_convolution (i j : F.Index) : convolution (F.kernel i) (F.kernel j) =
    if i = j then F.kernel i else 0 := by
  apply F.integrated_injective
  intro k
  rw [integrated_convolution, F.integrated_kernel, F.integrated_kernel]
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, integrated_kernel]
    split_ifs <;> simp
  · rw [ite_eq_right hij]
    simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]
    by_cases hik : i = k
    · subst k; simp [Ne.symm hij]
    · simp [hik]

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Family
end Thorp.Fourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical


theorem solution : type_of% @_root_.OAI.Thorp.Fourier.Family.kernel_convolution := @_root_.OAI.Thorp.Fourier.Family.kernel_convolution
