-- Prove2me | solution 1 for OAI.Thorp.Fourier.Family.splitVector_low
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:31:48.287055+00:00
-- url     : https://prove2.me/submissions/72dfd46e-0ec5-4512-909e-3d474c119539

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ProductProjectors.lean:L174-L190
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.Family.splitVector_low. The node keeps its source
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
import Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors
import Theorems.Thm_OAI_Thorp_Fourier_Family_joint_degree_le
import Theorems.Thm_OAI_Thorp_Fourier_Family_kernel_convolution

-- ---- from OAI.Probability.ThorpShuffle.ProductProjectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

universe uH uI uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {H : Type uH} {I : Type uI} {E : Type uE} [Group H] [Fintype H] [Fintype I] [AddCommGroup E] [Module ℂ E]

lemma integrated_single_mul (ρ : Representation ℂ (I → H) E) (i : I) (k : H → ℂ) (f : (I → H) → ℂ) :
    integrated (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) k * integrated ρ f =
      integrated ρ (fun g => ∑ h, k h * f (Pi.mulSingle i h⁻¹ * g)) := by
  simp only [integrated, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul]
  conv_rhs => rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  have he := Equiv.sum_comp (Equiv.mulLeft (Pi.mulSingle i h))
    (fun g : I → H => (k h * f (Pi.mulSingle i h⁻¹ * g)) • ρ g)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  have hi : Pi.mulSingle i h⁻¹ = (Pi.mulSingle i h : I → H)⁻¹ :=
    (map_inv (MonoidHom.mulSingle (fun _ : I => H) i) h).symm.symm
  simp only [Equiv.coe_mulLeft, hi, inv_mul_cancel_left, smul_mul_smul,
    MonoidHom.comp_apply, MonoidHom.mulSingle_apply, map_mul]

end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

lemma jointKernel_single (a : I → F.Index) (i : I) (h : H) (g : I → H) :
    F.jointKernel a (Pi.mulSingle i h * g) =
      F.kernel (a i) (h * g i) * ∏ j ∈ Finset.univ.erase i, F.kernel (a j) (g j) := by
  rw [jointKernel, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Pi.mul_apply, Pi.mulSingle_eq_same]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  simp only [Pi.mulSingle_eq_of_ne hji, one_mul]

lemma jointKernel_split (a : I → F.Index) (i : I) (g : I → H) :
    F.jointKernel a g = F.kernel (a i) (g i) * ∏ j ∈ Finset.univ.erase i, F.kernel (a j) (g j) :=
  (Finset.mul_prod_erase Finset.univ (fun j => F.kernel (a j) (g j)) (Finset.mem_univ i)).symm

lemma jointKernel_single_convolution (a : I → F.Index) (i : I) (b : F.Index) (g : I → H) :
    ∑ h, F.kernel b h * F.jointKernel a (Pi.mulSingle i h⁻¹ * g) =
      if b = a i then F.jointKernel a g else 0 := by
  simp only [F.jointKernel_single, ← mul_assoc, ← Finset.sum_mul]
  change convolution (F.kernel b) (F.kernel (a i)) (g i) * _ = _
  rw [F.kernel_convolution]
  split_ifs with hb
  · simp only [hb]
    exact (F.jointKernel_split a i g).symm
  · simp

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma projector_jointProjector (ρ : Representation ℂ (I → H) E) (a : I → F.Index)
    (i : I) (b : F.Index) :
    F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b * F.jointProjector ρ a =
      if b = a i then F.jointProjector ρ a else 0 := by
  rw [projector, jointProjector, integrated_single_mul]
  simp only [F.jointKernel_single_convolution]
  split_ifs <;> simp only [integrated, zero_smul, Finset.sum_const_zero]

lemma low_fixes_joint (ρ : Representation ℂ (I → H) E) (a : I → F.Index)
    (i : I) (s : Finset F.Index) (ha : a i ∈ s) :
    (∑ b ∈ s, F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) * F.jointProjector ρ a =
      F.jointProjector ρ a := by
  rw [Finset.sum_mul]
  simp only [F.projector_jointProjector, Finset.sum_ite_eq', ha, ↓reduceIte]

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical

namespace Family
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)

lemma leastFactor_le (a : I → F.Index) (i : I) :
    F.degree (a (F.leastFactor a)) ≤ F.degree (a i) :=
  (Classical.choose_spec (Finset.exists_min_image Finset.univ
    (fun i => F.degree (a i)) Finset.univ_nonempty)).2 i (Finset.mem_univ i)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

lemma leastFactor_pow_le (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    F.degree (a (F.leastFactor a)) ^ Fintype.card I ≤ Module.finrank ℂ E := by
  calc
    _ = ∏ _ : I, F.degree (a (F.leastFactor a)) := by simp
    _ ≤ ∏ i, F.degree (a i) := Finset.prod_le_prod' (fun i _ => F.leastFactor_le a i)
    _ ≤ _ := F.joint_degree_le ρ a ha

lemma splitVector_low (ρ : Representation ℂ (I → H) E) (v : E) (i : I) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
      F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) (F.splitVector ρ v i) =
        F.splitVector ρ v i := by
  unfold splitVector
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hai : F.leastFactor a = i
  · simp only [ite_eq_left hai]
    by_cases ha : F.jointProjector ρ a = 0
    · simp [ha]
    · have hb : a i ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [hai] using F.leastFactor_pow_le ρ a ha
      exact congrArg (fun f : Module.End ℂ E => f v) (F.low_fixes_joint ρ a i _ hb)
  · simp [hai]

end Family
end Thorp.Fourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical


theorem solution.{uE} : type_of% @_root_.OAI.Thorp.Fourier.Family.splitVector_low.{uE} := @_root_.OAI.Thorp.Fourier.Family.splitVector_low.{uE}
