-- Prove2me | solution 1 for OAI.Thorp.Fourier.Family.integrated_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:33:41.511114+00:00
-- url     : https://prove2.me/submissions/3fbe3263-c638-4b17-998d-61e0b5fd5577

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/CosetBounds.lean:L154-L185
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Fourier.Family.integrated_norm_sq. The node keeps its source
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
import Theorems.Thm_OAI_Thorp_Fourier_Family_coefficient_evaluation
import Theorems.Thm_OAI_Thorp_Fourier_Family_integrated_kernel
import Theorems.Thm_OAI_Thorp_Fourier_Family_kernel_convolution
import Theorems.Thm_OAI_Thorp_Fourier_Family_splitVector_low
import Theorems.Thm_OAI_Thorp_Fourier_coefficient_second_moment

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

lemma integrated_delta (ρ : Representation ℂ G V) : integrated ρ delta = 1 := by
  simp [integrated, delta]

lemma integrated_sum {I : Type uI} (ρ : Representation ℂ G V) (s : Finset I) (f : I → G → ℂ) :
    integrated ρ (∑ i ∈ s, f i) = ∑ i ∈ s, integrated ρ (f i) := by
  simp only [integrated, Finset.sum_apply, Finset.sum_smul]
  rw [Finset.sum_comm]

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

lemma kernel_sum : (∑ i, F.kernel i) = delta := by
  apply F.integrated_injective
  intro j
  rw [integrated_sum, integrated_delta]
  simp only [integrated_kernel, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

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

omit [FiniteDimensional ℂ E] in
lemma integrated_symmetric (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (f : G → ℂ) (hf : ∀ g, conj (f g⁻¹) = f g) : (integrated ρ f).IsSymmetric := by
  intro x y
  simp only [integrated, LinearMap.sum_apply, LinearMap.smul_apply, sum_inner,
    inner_sum, inner_smul_left, inner_smul_right]
  have he := Equiv.sum_comp (Equiv.inv G) (fun g => conj (f g) * ⟪ρ g x, y⟫_ℂ)
  rw [← he]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Equiv.inv_apply, hf]
  rw [← inner_inv ρ hu, inv_inv]

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)

lemma kernel_star (i : F.Index) (g : G) : conj (F.kernel i g⁻¹) = F.kernel i g := by
  simp only [kernel, inv_inv, map_mul, map_inv₀, map_natCast, character_inv _ (F.unitary i)]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Family
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

lemma complex_cauchy {I : Type uI} (s : Finset I) (a b : I → ℂ) :
    ‖∑ i ∈ s, a i * b i‖ ^ 2 ≤ (∑ i ∈ s, ‖a i‖ ^ 2) * ∑ i ∈ s, ‖b i‖ ^ 2 := by
  have ht : ‖∑ i ∈ s, a i * b i‖ ≤ ∑ i ∈ s, ‖a i‖ * ‖b i‖ := by
    simpa only [norm_mul] using norm_sum_le s (fun i => a i * b i)
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    (Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖a i‖) (fun i => ‖b i‖))

namespace Family
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end Family
end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

lemma jointKernel_sum : (∑ a : I → F.Index, F.jointKernel a) = delta := by
  funext g
  simp only [Finset.sum_apply, jointKernel]
  rw [← Fintype.prod_sum (fun i (j : F.Index) => F.kernel j (g i))]
  have hh (i : I) : ∑ j : F.Index, F.kernel j (g i) = if g i = 1 then 1 else 0 :=
    by simpa only [Finset.sum_apply, delta] using congrFun F.kernel_sum (g i)
  simp only [hh]
  by_cases hg : g = 1
  · subst g; simp [delta]
  · have hn : ∃ i, g i ≠ 1 := by
      by_contra hn
      push Not at hn
      exact hg (funext hn)
    obtain ⟨i, hi⟩ := hn
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)]
    simp [delta, hg]

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

lemma jointKernel_star (a : I → F.Index) (g : I → H) :
    conj (F.jointKernel a g⁻¹) = F.jointKernel a g := by
  simp only [jointKernel, map_prod, Pi.inv_apply, F.kernel_star]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

lemma jointProjector_mul (ρ : Representation ℂ (I → H) E) (a b : I → F.Index) :
    F.jointProjector ρ a * F.jointProjector ρ b = if a = b then F.jointProjector ρ a else 0 := by
  rw [jointProjector, jointProjector, ← integrated_convolution, jointKernel_convolution]
  split_ifs <;> simp only [integrated, Pi.zero_apply, zero_smul, Finset.sum_const_zero]

lemma jointProjector_sum (ρ : Representation ℂ (I → H) E) : ∑ a, F.jointProjector ρ a = 1 := by
  simp only [jointProjector]
  rw [← integrated_sum, F.jointKernel_sum, integrated_delta]

end Thorp.Fourier.Family

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.ProductProjectors ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uH uI uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {H : Type uH} {I : Type uI} {E : Type uE} [Group H] [Fintype H] [Fintype I] [AddCommGroup E] [Module ℂ E]

end Thorp.Fourier

namespace Thorp.Fourier.Family
open scoped Classical
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]

variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

end Thorp.Fourier.Family

namespace Thorp.Fourier
open scoped Classical

lemma norm_sum_sq_of_orthogonal {J : Type uJ} {E : Type uE} [Fintype J]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : J → E)
    (hv : ∀ i j, i ≠ j → ⟪v i, v j⟫_ℂ = 0) :
    ‖∑ i, v i‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := by
  have he : ⟪∑ i, v i, ∑ i, v i⟫_ℂ = ∑ i, ⟪v i, v i⟫_ℂ := by
    simp only [sum_inner, inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_eq_single i (fun j _ hji => hv j i hji) (by simp)
  have hr := congrArg Complex.re he
  simpa only [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
    ← Complex.ofReal_sum, Complex.ofReal_re] using hr

namespace Family
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Nonempty I] [FiniteDimensional ℂ E] in
lemma jointProjector_symmetric (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (a : I → F.Index) :
    (F.jointProjector ρ a).IsSymmetric := integrated_symmetric ρ hu _ (F.jointKernel_star a)

omit [Nonempty I] [FiniteDimensional ℂ E] in
lemma jointProjector_orthogonal (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (a b : I → F.Index) (hab : a ≠ b) (x y : E) :
    ⟪F.jointProjector ρ a x, F.jointProjector ρ b y⟫_ℂ = 0 := by
  rw [F.jointProjector_symmetric ρ hu a]
  change ⟪x, (F.jointProjector ρ a * F.jointProjector ρ b) y⟫_ℂ = 0
  rw [F.jointProjector_mul, ite_eq_right hab]
  simp

omit [FiniteDimensional ℂ E] in
lemma splitVector_sum (ρ : Representation ℂ (I → H) E) (v : E) :
    ∑ i, F.splitVector ρ v i = v := by
  simp only [splitVector]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  rw [← LinearMap.sum_apply, F.jointProjector_sum]
  rfl

omit [FiniteDimensional ℂ E] in
lemma splitVector_orthogonal (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (v : E) (i j : I) (hij : i ≠ j) :
    ⟪F.splitVector ρ v i, F.splitVector ρ v j⟫_ℂ = 0 := by
  simp only [splitVector, sum_inner, inner_sum]
  apply Finset.sum_eq_zero
  intro a _
  apply Finset.sum_eq_zero
  intro b _
  split_ifs with hai hbj
  · exact F.jointProjector_orthogonal ρ hu b a (by intro h; subst b; exact hij (hai.symm.trans hbj)) v v
  all_goals simp

omit [FiniteDimensional ℂ E] in
lemma splitVector_sq_sum (ρ : Representation ℂ (I → H) E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ) (v : E) :
    ∑ i, ‖F.splitVector ρ v i‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [← norm_sum_sq_of_orthogonal _ (F.splitVector_orthogonal ρ hu v), F.splitVector_sum]

end Family
end Thorp.Fourier

end

end OAI

-- ---- from OAI.Probability.ThorpShuffle.CosetBounds ----
namespace OAI

universe uG uH uE uJ

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology

namespace Thorp.Fourier
open scoped Classical
variable {G : Type uG} {H : Type uH} [Group G] [Fintype G] [Group H] [Fintype H]

lemma coset_sum_reindex (φ : H →* G) (ν f : G → ℝ) :
    ∑ g, ν g * ∑ h, f (g * φ h) = ∑ g, (∑ h, ν (g * φ h)) * f g := by
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun g h => ν (g * φ h) * f g)]
  have he := Equiv.sum_comp (Equiv.inv H) (fun h => ∑ g, ν (g * φ h) * f g)
  rw [← he]
  apply Finset.sum_congr rfl
  intro h _
  have hh := Equiv.sum_comp (Equiv.mulRight ((φ h)⁻¹)) (fun g => ν g * f (g * φ h))
  rw [← hh]
  simp only [Equiv.coe_mulRight, Equiv.inv_apply, map_inv, inv_mul_cancel_right]

lemma weighted_coset_bound (φ : H →* G) (ν f : G → ℝ) (S C : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (hf : ∀ g, 0 ≤ f g) (hS : 0 ≤ S)
    (heval : ∀ g, (Fintype.card H : ℝ) * f g ≤ S * ∑ h, f (g * φ h))
    (hcoset : ∀ g, ∑ h, ν (g * φ h) ≤ C) :
    (Fintype.card H : ℝ) * ∑ g, ν g * f g ≤ S * C * ∑ g, f g := by
  calc
    _ = ∑ g, ν g * ((Fintype.card H : ℝ) * f g) := by rw [Finset.mul_sum]; congr 1; funext g; ring
    _ ≤ ∑ g, ν g * (S * ∑ h, f (g * φ h)) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (heval g) (hν g))
    _ = S * ∑ g, (∑ h, ν (g * φ h)) * f g := by
      rw [← coset_sum_reindex φ ν f, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    _ ≤ S * ∑ g, C * f g := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_right (hcoset g) (hf g))) hS
    _ = _ := by rw [← Finset.mul_sum]; ring

namespace Family
variable {G H : Type} [Group G] [Fintype G] [Group H] [Fintype H] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

omit [Fintype G] [FiniteDimensional ℂ E] in
lemma coset_coefficient_evaluation (ρ : Representation ℂ G E)
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (φ : H →* G) (s : Finset F.Index) (v w : E)
    (hv : (∑ i ∈ s, F.projector (ρ.comp φ) i) v = v) (g : G) :
    (Fintype.card H : ℝ) * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ h, ‖⟪w, ρ (g * φ h) v⟫_ℂ‖ ^ 2 := by
  have he := F.coefficient_evaluation (ρ.comp φ) s v (ρ g⁻¹ w) hv
  have hh (x : E) : ⟪ρ g⁻¹ w, x⟫_ℂ = ⟪w, ρ g x⟫_ℂ := by
    simpa only [inv_inv] using (inner_inv ρ hu g⁻¹ w x).symm
  simpa only [hh, MonoidHom.comp_apply, map_mul, Module.End.mul_apply] using he

theorem weighted_coefficient (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (φ : H →* G) (s : Finset F.Index) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g)
    (hcoset : ∀ g, ∑ h, ν (g * φ h) ≤ B * (Fintype.card H : ℝ) / Fintype.card G)
    (v w : E) (hv : (∑ i ∈ s, F.projector (ρ.comp φ) i) v = v) :
    ∑ g, ν g * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      B * (∑ i ∈ s, (F.degree i : ℝ)^2) / Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  have hh := weighted_coset_bound φ ν (fun g => ‖⟪w, ρ g v⟫_ℂ‖ ^ 2)
    (∑ i ∈ s, (F.degree i : ℝ)^2) (B * (Fintype.card H : ℝ) / Fintype.card G)
    hν (fun _ => sq_nonneg _) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (F.coset_coefficient_evaluation ρ hu φ s v w hv) hcoset
  have hcG : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hcH : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos
  have hd : (Module.finrank ℂ E : ℝ) ≠ 0 := by exact_mod_cast hE
  have hs := coefficient_second_moment ρ hu hE v w
  have hs' : ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      (Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E) := by
    calc
      _ = (Fintype.card G : ℝ) * ((Fintype.card G : ℝ)⁻¹ * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2) := by field_simp
      _ = _ := by rw [hs]
  rw [hs'] at hh
  have he : (∑ i ∈ s, (F.degree i : ℝ)^2) * (B * (Fintype.card H : ℝ) / Fintype.card G) *
      ((Fintype.card G : ℝ) * (‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E)) =
      (Fintype.card H : ℝ) * (B * (∑ i ∈ s, (F.degree i : ℝ)^2) /
        Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2)) := by field_simp
  rw [he] at hh
  exact (mul_le_mul_iff_right₀ hcH).mp hh

end Family
end Thorp.Fourier

namespace Thorp.Fourier
open scoped Classical

lemma norm_weighted_sum_sq {J : Type uJ} [Fintype J] (ν : J → ℝ) (f : J → ℂ)
    (hν : ∀ j, 0 ≤ ν j) (h1 : ∑ j, ν j = 1) :
    ‖∑ j, (ν j : ℂ) * f j‖ ^ 2 ≤ ∑ j, ν j * ‖f j‖ ^ 2 := by
  have ht : ‖∑ j, (ν j : ℂ) * f j‖ ≤ ∑ j, ν j * ‖f j‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hν _)] using
      norm_sum_le Finset.univ (fun j => (ν j : ℂ) * f j)
  have hc := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (f := ν) (g := fun j => ν j * ‖f j‖ ^ 2) (r := fun j => ν j * ‖f j‖)
    (fun j _ => hν j) (fun j _ => mul_nonneg (hν j) (sq_nonneg _))
    (fun j _ => by nlinarith [sq_nonneg (ν j * ‖f j‖)])
  rw [h1, one_mul] at hc
  exact (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hc

namespace Family
variable {G H I : Type} [Group G] [Fintype G] [Group H] [Fintype H]
  [Fintype I] [Nonempty I] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem split_weighted_coefficient (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v w : E) :
    ∑ g, ν g * ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * (‖v‖ ^ 2 * ‖w‖ ^ 2) := by
  let z := F.splitVector (ρ.comp ψ) v
  let s := Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E)
  let S : ℝ := ∑ b ∈ s, (F.degree b : ℝ)^2
  have hz : ∑ i, z i = v := F.splitVector_sum (ρ.comp ψ) v
  have hz2 : ∑ i, ‖z i‖ ^ 2 = ‖v‖ ^ 2 := F.splitVector_sq_sum (ρ.comp ψ) (fun g => hu (ψ g)) v
  have hpoint (g : G) : ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 ≤ (Fintype.card I : ℝ) * ∑ i, ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 := by
    have hh := complex_cauchy Finset.univ (fun _ : I => 1) (fun i => ⟪w, ρ g (z i)⟫_ℂ)
    simpa only [one_mul, norm_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one, ← inner_sum, ← map_sum, hz] using hh
  have hi (i : I) : ∑ g, ν g * ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 ≤
      B * S / Module.finrank ℂ E * (‖z i‖ ^ 2 * ‖w‖ ^ 2) := by
    exact F.weighted_coefficient ρ hu hE (ψ.comp (MonoidHom.mulSingle (fun _ : I => H) i))
      s ν B hν (hcoset i) (z i) w (F.splitVector_low (ρ.comp ψ) v i)
  calc
    _ ≤ ∑ g, ν g * ((Fintype.card I : ℝ) * ∑ i, ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2) :=
      Finset.sum_le_sum (fun g _ => mul_le_mul_of_nonneg_left (hpoint g) (hν g))
    _ = (Fintype.card I : ℝ) * ∑ i, ∑ g, ν g * ‖⟪w, ρ g (z i)⟫_ℂ‖ ^ 2 := by
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      rw [← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card I : ℝ) * ∑ i, B * S / Module.finrank ℂ E * (‖z i‖ ^ 2 * ‖w‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul, hz2]
      dsimp [S, s]
      ring

theorem integrated_norm_sq (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v : E) :
    ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * ‖v‖ ^ 2 := by
  let A := integrated ρ (fun g => (ν g : ℂ))
  let R := (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E
  have hc : ‖⟪A v, A v⟫_ℂ‖ ^ 2 ≤ R * (‖v‖ ^ 2 * ‖A v‖ ^ 2) := by
    calc
      _ = ‖∑ g, (ν g : ℂ) * ⟪A v, ρ g v⟫_ℂ‖ ^ 2 := by
        congr 2
        simp only [A, integrated, LinearMap.sum_apply, LinearMap.smul_apply,
          inner_sum, inner_smul_right]
      _ ≤ ∑ g, ν g * ‖⟪A v, ρ g v⟫_ℂ‖ ^ 2 := norm_weighted_sum_sq ν _ hν h1
      _ ≤ _ := F.split_weighted_coefficient ρ hu hE ψ ν B hν hcoset v (A v)
  have hinner : ‖⟪A v, A v⟫_ℂ‖ = ‖A v‖ ^ 2 := by simp [inner_self_eq_norm_sq_to_K]
  rw [hinner] at hc
  have hR : 0 ≤ R := by positivity
  by_cases hz : ‖A v‖ ^ 2 = 0
  · change ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2
    rw [hz]
    exact mul_nonneg hR (sq_nonneg _)
  · have hp : 0 < ‖A v‖ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hz)
    change ‖A v‖ ^ 2 ≤ R * ‖v‖ ^ 2
    nlinarith

end Family
end Thorp.Fourier

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical


theorem solution.{uE} : type_of% @_root_.OAI.Thorp.Fourier.Family.integrated_norm_sq.{uE} := @_root_.OAI.Thorp.Fourier.Family.integrated_norm_sq.{uE}
