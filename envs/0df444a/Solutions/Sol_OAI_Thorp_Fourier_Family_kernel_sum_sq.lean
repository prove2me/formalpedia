-- Prove2me | solution 1 for OAI.Thorp.Fourier.Family.kernel_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:25:23.226407+00:00
-- url     : https://prove2.me/submissions/8dc212e2-dccf-4060-9e77-40632c3c2fb9

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean:L185-L223
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.Family.kernel_sum_sq. The node keeps its source
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

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma inner_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) (x y : E) :
    ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  have hh := hu g x (ρ g⁻¹ y)
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh.symm

end Unitary
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Thorp.Fourier

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.FourierFamilies ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
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

lemma orthogonal (i j : F.Index) :
    (Fintype.card G : ℂ)⁻¹ * ∑ g, (F.rep i).character g * (F.rep j).character g⁻¹ =
      if i = j then 1 else 0 := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [Fintype.card_eq_nat_card, Representation.char_orthonormal]
  congr 1
  apply propext
  exact ⟨fun h => (F.distinct j i h).symm, fun h => by subst j; exact ⟨Representation.Equiv.refl _⟩⟩

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] in
lemma character_inv (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (g : G) :
    ρ.character g⁻¹ = conj (ρ.character g) := by
  let b := stdOrthonormalBasis ℂ E
  simp only [Representation.character, LinearMap.trace_eq_sum_inner _ b, map_sum,
    inner_inv ρ hu, inner_conj_symm]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma kernel_star (i : F.Index) (g : G) : conj (F.kernel i g⁻¹) = F.kernel i g := by
  simp only [kernel, inv_inv, map_mul, map_inv₀, map_natCast, character_inv _ (F.unitary i)]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

lemma kernel_sum_sq (s : Finset F.Index) :
    (Fintype.card G : ℝ) * ∑ g, ‖∑ i ∈ s, F.kernel i g‖ ^ 2 = ∑ i ∈ s, (F.degree i : ℝ) ^ 2 := by
  have hh (i j : F.Index) : (Fintype.card G : ℂ) * ∑ g, conj (F.kernel i g) * F.kernel j g =
      if i = j then (F.degree i : ℂ) ^ 2 else 0 := by
    have hc : ∀ g, conj (F.kernel i g) =
        (F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g := by
      intro g
      calc
        _ = F.kernel i g⁻¹ := by simpa only [inv_inv] using F.kernel_star i g⁻¹
        _ = _ := by rw [kernel, inv_inv]
    simp_rw [hc]
    simp only [kernel]
    have he : (Fintype.card G : ℂ) * ∑ g,
        ((F.degree i : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep i).character g) *
          ((F.degree j : ℂ) * (Fintype.card G : ℂ)⁻¹ * (F.rep j).character g⁻¹) =
        (F.degree i : ℂ) * (F.degree j : ℂ) *
          ((Fintype.card G : ℂ)⁻¹ * ∑ g, (F.rep i).character g * (F.rep j).character g⁻¹) := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      field_simp
    rw [he, F.orthogonal]
    split_ifs with h
    · subst j; ring
    · ring
  have he : (Fintype.card G : ℂ) * ∑ g, conj (∑ i ∈ s, F.kernel i g) * (∑ i ∈ s, F.kernel i g) =
      ∑ i ∈ s, (F.degree i : ℂ) ^ 2 := by
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    have hz (i : F.Index) : ∑ g, (Fintype.card G : ℂ) * (conj (F.kernel i g) * F.kernel j g) =
        if i = j then (F.degree i : ℂ)^2 else 0 := by rw [← Finset.mul_sum, hh]
    simp only [hz, Finset.sum_ite_eq', hj, ↓reduceIte]
  simp only [Complex.conj_mul'] at he
  apply Complex.ofReal_injective
  push_cast
  exact he

end Family
end Thorp.Fourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical


theorem solution : type_of% @_root_.OAI.Thorp.Fourier.Family.kernel_sum_sq := @_root_.OAI.Thorp.Fourier.Family.kernel_sum_sq
