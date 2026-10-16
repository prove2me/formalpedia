-- Prove2me | solution 1 for OAI.Thorp.Fourier.Family.joint_degree_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:29:54.625406+00:00
-- url     : https://prove2.me/submissions/45f46ea7-7615-41db-a7cf-b2feb79d8554

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/JointProjectors.lean:L156-L174
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.Family.joint_degree_le. The node keeps its source
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
import Theorems.Thm_OAI_Thorp_Fourier_Family_kernel_convolution

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

lemma trace_integrated (ρ : Representation ℂ G V) (f : G → ℂ) :
    LinearMap.trace ℂ V (integrated ρ f) = ∑ g, f g * ρ.character g := by
  simp only [integrated, map_sum, map_smul, smul_eq_mul, Representation.character]

end Thorp.Fourier

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.JointProjectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uI uE

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Family
end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

lemma jointKernel_convolution (a b : I → F.Index) :
    convolution (F.jointKernel a) (F.jointKernel b) = if a = b then F.jointKernel a else 0 := by
  funext g
  simp only [convolution, jointKernel, Pi.mul_apply, Pi.inv_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (h : H) => F.kernel (a i) h * F.kernel (b i) (h⁻¹ * g i))]
  have hh (i : I) : ∑ h, F.kernel (a i) h * F.kernel (b i) (h⁻¹ * g i) =
      if a i = b i then F.kernel (a i) (g i) else 0 := by
    have he := congrFun (F.kernel_convolution (a i) (b i)) (g i)
    simpa only [convolution, ite_apply, Pi.zero_apply] using he
  simp only [hh]
  by_cases hab : a = b
  · subst b; simp only [↓reduceIte, jointKernel]
  · rw [ite_eq_right hab]
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
      by_contra hn; push Not at hn; exact hab (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma jointProjector_mul (ρ : Representation ℂ (I → H) E) (a b : I → F.Index) :
    F.jointProjector ρ a * F.jointProjector ρ b = if a = b then F.jointProjector ρ a else 0 := by
  rw [jointProjector, jointProjector, ← integrated_convolution, jointKernel_convolution]
  split_ifs <;> simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

lemma jointProjector_idempotent (ρ : Representation ℂ (I → H) E) (a : I → F.Index) :
    IsIdempotentElem (F.jointProjector ρ a) := by
  simpa only [IsIdempotentElem, ↓reduceIte] using F.jointProjector_mul ρ a a

omit [Fintype I] in
lemma tensorList_character (a : I → F.Index) (l : List I) (g : I → H) :
    Representation.character (F.tensorList a l).ρ g = (l.map (fun i => (F.rep (a i)).character (g i))).prod := by
  induction l with
  | nil =>
    change LinearMap.trace ℂ ℂ (1 : Module.End ℂ ℂ) = 1
    simp
  | cons i l ih =>
    change (Representation.tprod ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i))
      (F.tensorList a l).ρ).character g = _
    rw [Representation.char_tensor ((F.rep (a i)).comp (Pi.evalMonoidHom (fun _ : I => H) i))
      (F.tensorList a l).ρ]
    change (F.rep (a i)).character (g i) * Representation.character (F.tensorList a l).ρ g = _
    rw [ih]
    rfl

lemma tensorFamily_character (a : I → F.Index) (g : I → H) :
    Representation.character (F.tensorFamily a).ρ g = ∏ i, (F.rep (a i)).character (g i) := by
  rw [tensorFamily, tensorList_character]
  exact Finset.prod_map_toList _ _

lemma jointKernel_formula (a : I → F.Index) (g : I → H) :
    F.jointKernel a g = (∏ i, (F.degree (a i) : ℂ)) * (Fintype.card (I → H) : ℂ)⁻¹ *
      Representation.character (F.tensorFamily a).ρ g⁻¹ := by
  simp only [jointKernel, kernel, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, tensorFamily_character, Pi.inv_apply, Fintype.card_fun, Nat.cast_pow, inv_pow]

lemma trace_jointProjector [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) : LinearMap.trace ℂ E (F.jointProjector ρ a) =
      (∏ i, (F.degree (a i) : ℂ)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) := by
  let : Invertible (Nat.card (I → H) : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [jointProjector, trace_integrated]
  simp only [jointKernel_formula]
  rw [← Representation.card_inv_mul_sum_char_mul_char_eq_finrank]
  simp only [Finset.mul_sum, Fintype.card_eq_nat_card]
  apply Finset.sum_congr rfl
  intro g _
  ring

theorem joint_degree_le [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    (∏ i, F.degree (a i)) ≤ Module.finrank ℂ E := by
  have hp := F.jointProjector_idempotent ρ a
  have ht := F.trace_jointProjector ρ a
  rw [(LinearMap.IsIdempotentElem.isProj_range _ hp).trace] at ht
  have hm : Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) ≠ 0 := by
    intro hz
    have hh := F.trace_jointProjector ρ a
    rw [hz, Nat.cast_zero, mul_zero] at hh
    exact ha (LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hp hh)
  have hn : Module.finrank ℂ (LinearMap.range (F.jointProjector ρ a)) =
      (∏ i, F.degree (a i)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) := by
    exact_mod_cast ht
  calc
    _ ≤ (∏ i, F.degree (a i)) * Module.finrank ℂ (Representation.IntertwiningMap (F.tensorFamily a).ρ ρ) :=
      Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hm)
    _ = _ := hn.symm
    _ ≤ Module.finrank ℂ E := Submodule.finrank_le _

end Thorp.Fourier.Family

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical


theorem solution.{uE} : type_of% @_root_.OAI.Thorp.Fourier.Family.joint_degree_le.{uE} := @_root_.OAI.Thorp.Fourier.Family.joint_degree_le.{uE}
