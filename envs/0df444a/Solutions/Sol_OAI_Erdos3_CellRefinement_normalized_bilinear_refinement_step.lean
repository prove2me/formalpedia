-- Prove2me | solution 1 for OAI.Erdos3.CellRefinement.normalized_bilinear_refinement_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T00:29:22.183264+00:00
-- url     : https://prove2.me/submissions/e5427d9a-59de-4520-908f-cc8c818558f5

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034
import Theorems.Thm_OAI_Erdos3_CellRefinement_capped_parent_bound_of_children

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComplexFiniteMeans
namespace OAI

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*}

theorem cellAverage_nonneg [Add G] (C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (x : G) : 0 ≤ cellAverage C f x :=
  Finset.expect_nonneg (fun c _ => hf (x + c))

variable [Fintype G] [DecidableEq G]

theorem expect_comp_le_expect_of_support (L : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0)
    (phi : G → G) (hphi : Function.Injective phi) :
    (𝔼 x ∈ L, f (phi x)) ≤ 𝔼 x ∈ L, f x := by
  have hsum : (∑ x ∈ L, f (phi x)) ≤ ∑ x, f x := by
    rw [← Finset.sum_image hphi.injOn]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun x _ _ => hf x)
  have htotal : (∑ x ∈ L, f x) = ∑ x, f x :=
    Finset.sum_subset (Finset.subset_univ L) (fun x _ hx => hsupport x hx)
  simp only [Finset.expect_eq_sum_div_card]
  rw [htotal]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg L.card)

variable [AddCommGroup G]

theorem expect_cellAverage_comp_le (L C : Finset G) (hC : C.Nonempty) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ L → f x = 0)
    (phi : G → G) (hphi : Function.Injective phi) :
    (𝔼 x ∈ L, cellAverage C f (phi x)) ≤ 𝔼 x ∈ L, f x := by
  unfold cellAverage
  rw [Finset.expect_comm]
  have h := Finset.expect_le_expect (fun c (_ : c ∈ C) =>
    expect_comp_le_expect_of_support L f hf hsupport (fun x => phi x + c)
      (fun _ _ h => hphi (add_right_cancel h)))
  simpa only [Finset.expect_const hC] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FlatWeightedComparison
namespace OAI

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

variable {ι : Type*}

end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem momentAmplificationFactor_pos (delta : ℝ) : 0 < momentAmplificationFactor delta := by
  unfold momentAmplificationFactor
  omega

theorem momentAmplificationGain_pos (delta : ℝ) : 0 < momentAmplificationGain delta := by
  have hR : (0 : ℝ) < momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have h := Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) (by positivity : 0 < 1 / (momentAmplificationFactor delta : ℝ))
  unfold momentAmplificationGain
  linarith

theorem momentAmplificationGain_le_one (delta : ℝ) : momentAmplificationGain delta ≤ 1 := by
  have hR : (1 : ℝ) ≤ momentAmplificationFactor delta := by
    exact_mod_cast momentAmplificationFactor_pos delta
  have hinv : 1 / (momentAmplificationFactor delta : ℝ) ≤ 1 :=
    (div_le_one (by linarith)).mpr hR
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hinv
  rw [Real.rpow_one] at h
  unfold momentAmplificationGain
  linarith

end Erdos3.LocalConvolution

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

end Erdos3.LocalConvolution

namespace Erdos3

open scoped BigOperators

end Erdos3

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingDecomposition
namespace OAI

namespace Erdos3

open scoped BigOperators

theorem abs_expect_le_of_bound {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f : ι → ℝ) {epsilon : ℝ} (hf : ∀ x ∈ S, |f x| ≤ epsilon) :
    |𝔼 x ∈ S, f x| ≤ epsilon := by
  have h := RCLike.norm_expect_le (K := ℝ) (s := S) (f := f)
  calc
    _ ≤ 𝔼 x ∈ S, |f x| := by simpa only [Real.norm_eq_abs] using h
    _ ≤ 𝔼 _x ∈ S, epsilon := Finset.expect_le_expect hf
    _ = epsilon := Finset.expect_const hS epsilon

theorem abs_expect_sub_expect_le {ι : Type*} (S : Finset ι) (hS : S.Nonempty)
    (f g : ι → ℝ) {epsilon : ℝ} (hfg : ∀ x ∈ S, |f x - g x| ≤ epsilon) :
    |(𝔼 x ∈ S, f x) - 𝔼 x ∈ S, g x| ≤ epsilon := by
  rw [← Finset.expect_sub_distrib]
  exact abs_expect_le_of_bound S hS _ hfg

theorem abs_weighted_expect_sub_le {ι : Type*} (S : Finset ι)
    (u f g : ι → ℝ) (hu : ∀ x ∈ S, 0 ≤ u x) {epsilon : ℝ}
    (hfg : ∀ x ∈ S, |f x - g x| ≤ epsilon) :
    |(𝔼 x ∈ S, u x * f x) - 𝔼 x ∈ S, u x * g x| ≤ epsilon * (𝔼 x ∈ S, u x) := by
  rw [← Finset.expect_sub_distrib]
  have h := RCLike.norm_expect_le (K := ℝ) (s := S) (f := fun x => u x * f x - u x * g x)
  calc
    _ ≤ 𝔼 x ∈ S, |u x * f x - u x * g x| := by simpa only [Real.norm_eq_abs] using h
    _ ≤ 𝔼 x ∈ S, epsilon * u x := by
      apply Finset.expect_le_expect
      intro x hx
      rw [← mul_sub, abs_mul, abs_of_nonneg (hu x hx)]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hfg x hx) (hu x hx)
    _ = _ := (Finset.mul_expect S u epsilon).symm

end Erdos3

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem remainder_nonneg (C : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    0 ≤ remainder C f x := by
  by_cases hx : x ∈ C <;> simp [remainder, hx, hf x]

omit [Fintype G] in
theorem remainder_le (C : Finset G) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) (x : G) :
    remainder C f x ≤ f x := by
  by_cases hx : x ∈ C <;> simp [remainder, hx, hf x]

omit [Fintype G] in
theorem remainder_supported (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) : ∀ x, x ∉ B → remainder C f x = 0 := by
  intro x hx
  simp [remainder, hf x hx]

omit [Fintype G] in
theorem remainder_add_slice (C : Finset G) (f : G → ℝ) (x : G) :
    remainder C f x + slice C f x = f x := by
  by_cases hx : x ∈ C <;> simp [remainder, slice, hx]

theorem sum_slice (C : Finset G) (f : G → ℝ) : (∑ x, slice C f x) = ∑ x ∈ C, f x := by
  simp [slice]

theorem sum_remainder_add (C : Finset G) (f : G → ℝ) :
    (∑ x, remainder C f x) + ∑ x ∈ C, f x = ∑ x, f x := by
  rw [← sum_slice C f, ← Finset.sum_add_distrib]
  simp only [remainder_add_slice]

omit [DecidableEq G] in
theorem expect_eq_total_div (B : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) : (𝔼 x ∈ B, f x) = (∑ x, f x) / B.card := by
  rw [Finset.expect_eq_sum_div_card]
  congr 1
  exact Finset.sum_subset (Finset.subset_univ B) (fun x _ hx => hf x hx)

theorem expect_remainder (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, x ∉ B → f x = 0) :
    (𝔼 x ∈ B, remainder C f x) =
      (𝔼 x ∈ B, f x) - (C.card : ℝ) / B.card * (𝔼 x ∈ C, f x) := by
  have hsum := sum_remainder_add C f
  have hC : (C.card : ℝ) * (𝔼 x ∈ C, f x) = ∑ x ∈ C, f x := Finset.card_mul_expect C f
  rw [expect_eq_total_div B (remainder C f) (remainder_supported B C f hf), expect_eq_total_div B f hf]
  have hrem : (∑ x, remainder C f x) = (∑ x, f x) - ∑ x ∈ C, f x := by linarith
  rw [hrem, ← hC]
  ring

theorem positiveSupport_remainder_subset (C : Finset G) (f : G → ℝ) :
    positiveSupport (remainder C f) ⊆ positiveSupport f := by
  intro x hx
  have hpos : 0 < remainder C f x := (Finset.mem_filter.mp hx).2
  by_cases hxC : x ∈ C
  · simp [remainder, hxC] at hpos
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [remainder, hxC] using hpos⟩

theorem positiveSupport_remainder_card_lt (C : Finset G) (f : G → ℝ)
    (hmean : 0 < 𝔼 x ∈ C, f x) :
    (positiveSupport (remainder C f)).card < (positiveSupport f).card := by
  have hC : C.Nonempty := by
    by_contra h
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he] at hmean
  obtain ⟨x, hx, hfx⟩ := Finset.exists_lt_of_lt_expect hC hmean
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨positiveSupport_remainder_subset C f, ?_⟩
  intro heq
  have hmem : x ∈ positiveSupport f := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfx⟩
  rw [← heq] at hmem
  have hpos : 0 < remainder C f x := (Finset.mem_filter.mp hmem).2
  simp only [remainder, hx, ite_true, lt_self_iff_false] at hpos

end Erdos3.Peeling

namespace Erdos3

open scoped BigOperators

namespace Peeling

theorem expect_slice_scale {G : Type*} [Fintype G] [DecidableEq G]
    (B D : Finset G) (f : G → ℝ) (hf : ∀ x, x ∉ B → f x = 0) :
    (𝔼 x ∈ B, slice D f x) = (D.card : ℝ) / B.card * (𝔼 x ∈ D, f x) := by
  have hs : ∀ x, x ∉ B → slice D f x = 0 := by
    intro x hx
    simp [slice, hf x hx]
  rw [expect_eq_total_div B (slice D f) hs, sum_slice, ← Finset.card_mul_expect D f]
  ring

end Peeling

namespace CellRefinement

variable {G : Type*} [AddCommGroup G]

theorem bilinearIntegral_swap (A B : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a f g = bilinearIntegral B A a g f := by
  unfold bilinearIntegral
  rw [Finset.expect_comm]
  apply Finset.expect_congr rfl
  intro y _
  apply Finset.expect_congr rfl
  intro x _
  rw [add_comm x y, mul_comm (f x) (g y)]

theorem bilinearIntegral_le (A B : Finset G) (a f g : G → ℝ) {M : ℝ}
    (ha : ∀ x, a x ≤ M) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    bilinearIntegral A B a f g ≤ M * (𝔼 x ∈ A, f x) * (𝔼 y ∈ B, g y) := by
  calc
    _ ≤ 𝔼 x ∈ A, 𝔼 y ∈ B, f x * g y * M := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro y _
      exact mul_le_mul_of_nonneg_left (ha _) (mul_nonneg (hf x) (hg y))
    _ = _ := by
      simp_rw [← Finset.expect_mul]
      rw [← Finset.expect_mul_expect]
      ring

variable [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem bilinearIntegral_peeling (A B D : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a f g =
      bilinearIntegral A B a (Peeling.remainder D f) g +
        bilinearIntegral A B a (Peeling.slice D f) g := by
  unfold bilinearIntegral
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_congr rfl
  intro x _
  rw [← Finset.expect_add_distrib]
  apply Finset.expect_congr rfl
  intro y _
  rw [← add_mul, ← add_mul, Peeling.remainder_add_slice]

theorem bilinearIntegral_slice_scale (A B D : Finset G) (a f g : G → ℝ)
    (hf : ∀ x, x ∉ A → f x = 0) :
    bilinearIntegral A B a (Peeling.slice D f) g =
      (D.card : ℝ) / A.card * bilinearIntegral D B a f g := by
  have hs : ∀ x, x ∉ A → (𝔼 y ∈ B, f x * g y * a (x + y)) = 0 := by
    intro x hx
    simp [hf x hx]
  have hpoint (x : G) :
      (𝔼 y ∈ B, Peeling.slice D f x * g y * a (x + y)) =
        Peeling.slice D (fun x => 𝔼 y ∈ B, f x * g y * a (x + y)) x := by
    by_cases hx : x ∈ D <;> simp [Peeling.slice, hx]
  unfold bilinearIntegral
  simp_rw [hpoint]
  exact Peeling.expect_slice_scale A D _ hs

end CellRefinement
end Erdos3

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

namespace Chain

variable {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
  {f g : G → ℝ} {cs : List (Finset G)}

omit [Fintype G] in
theorem bounds (h : Chain B Admissible K kappa f g cs) :
    (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ g x ∧ g x ≤ f x := by
  induction h with
  | nil f => intro hf x; exact ⟨hf x, le_rfl⟩
  | @step f g cs C _ _ _ _ ih =>
    intro hf x
    obtain ⟨hg, hgf⟩ := ih (remainder_nonneg C f hf) x
    exact ⟨hg, hgf.trans (remainder_le C f hf x)⟩

omit [Fintype G] in
theorem supported (h : Chain B Admissible K kappa f g cs)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    ∀ x, x ∉ B → g x = 0 := by
  intro x hx
  have hb := h.bounds hf x
  have hz := hsupport x hx
  linarith

omit [Fintype G] in
theorem admissible_mem (h : Chain B Admissible K kappa f g cs) : ∀ C ∈ cs, Admissible C := by
  induction h with
  | nil f => simp
  | step C _ hC _ _ ih =>
    intro D hD
    rcases List.mem_cons.mp hD with rfl | hD
    · exact hC
    · exact ih D hD

theorem length_le_support (h : Chain B Admissible K kappa f g cs)
    (hK : 0 < K) (hkappa : 0 < kappa) : cs.length ≤ (positiveSupport f).card := by
  induction h with
  | nil f => simp
  | @step f g cs C hactive _ hconc _ ih =>
    have hu : 0 < 𝔼 x ∈ B, f x := hkappa.trans_le hactive
    have hC : 0 < 𝔼 x ∈ C, f x := (mul_pos hK hu).trans hconc
    have hdrop := positiveSupport_remainder_card_lt C f hC
    simp only [List.length_cons]
    omega

end Chain
end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem exists_terminal_chain (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f : G → ℝ) :
    ∃ g cs, Chain B Admissible K kappa f g cs ∧
      ((𝔼 x ∈ B, g x) < kappa ∨ ∀ C, Admissible C → (𝔼 x ∈ C, g x) ≤ K * (𝔼 x ∈ B, g x)) := by
  classical
  suffices h : ∀ n : ℕ, ∀ f : G → ℝ, (positiveSupport f).card = n →
      ∃ g cs, Chain B Admissible K kappa f g cs ∧
        ((𝔼 x ∈ B, g x) < kappa ∨ ∀ C, Admissible C → (𝔼 x ∈ C, g x) ≤ K * (𝔼 x ∈ B, g x)) by
    exact h _ f rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hsize
    by_cases htiny : (𝔼 x ∈ B, f x) < kappa
    · exact ⟨f, [], Chain.nil f, Or.inl htiny⟩
    by_cases hfree : ∀ C, Admissible C → (𝔼 x ∈ C, f x) ≤ K * (𝔼 x ∈ B, f x)
    · exact ⟨f, [], Chain.nil f, Or.inr hfree⟩
    push Not at hfree
    obtain ⟨C, hC, hconc⟩ := hfree
    have hactive : kappa ≤ 𝔼 x ∈ B, f x := le_of_not_gt htiny
    have hmean : 0 < 𝔼 x ∈ C, f x := (mul_pos hK (hkappa.trans_le hactive)).trans hconc
    have hdrop : (positiveSupport (remainder C f)).card < n := by
      rw [← hsize]
      exact positiveSupport_remainder_card_lt C f hmean
    obtain ⟨g, cs, hchain, hterminal⟩ := ih _ hdrop (remainder C f) rfl
    exact ⟨g, C :: cs, Chain.step C hactive hC hconc hchain, hterminal⟩

end Erdos3.Peeling

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

end Erdos3.Peeling

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalMomentScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem abs_sum_mul_sub_le {ι : Type*} [Fintype ι] (u v f : ι → ℝ) {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) :
    |(∑ x, u x * f x) - ∑ x, v x * f x| ≤ M * ∑ x, |u x - v x| := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ x, |u x * f x - v x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, |u x - v x| * |f x| := by simp only [← sub_mul, abs_mul]
    _ ≤ ∑ x, |u x - v x| * M :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _))
    _ = M * ∑ x, |u x - v x| := by rw [← Finset.sum_mul]; ring

namespace LocalConvolution

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end LocalConvolution
end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

variable [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem sum_uniformMass_mul_eq_expect (S : Finset G) (f : G → ℝ) :
    (∑ x, realUniformMass S x * f x) = 𝔼 x ∈ S, f x := by
  rw [Finset.expect_eq_sum_div_card]
  simp only [realUniformMass, ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [← Finset.mul_sum]
  ring

variable [AddCommGroup G]

theorem expect_add_eq_shift_mass (S : Finset G) (f : G → ℝ) (t : G) :
    (𝔼 x ∈ S, f (x + t)) = ∑ x, realUniformMass S (x - t) * f x := by
  rw [← sum_uniformMass_mul_eq_expect]
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro x
  simp

theorem abs_expect_add_sub_le (S : Finset G) (f : G → ℝ) (t : G)
    {M : ℝ} (hf : ∀ x, |f x| ≤ M) :
    |(𝔼 x ∈ S, f (x + t)) - 𝔼 x ∈ S, f x| ≤
      M * ∑ x, |realUniformMass S (x - t) - realUniformMass S x| := by
  rw [expect_add_eq_shift_mass, ← sum_uniformMass_mul_eq_expect]
  exact abs_sum_mul_sub_le _ _ f hf

end Erdos3

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

theorem localMomentGain_pos (delta : ℝ) : 0 < localMomentGain delta :=
  div_pos (momentAmplificationGain_pos _) (by norm_num)

theorem localMomentGain_le_half (delta : ℝ) : localMomentGain delta ≤ 1 / 2 :=
  div_le_div_of_nonneg_right (momentAmplificationGain_le_one _) (by norm_num)

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem replacementIntegral_weighted (D Q C : Finset G) (a f g : G → ℝ) :
    replacementIntegral D Q C a f g =
      𝔼 x ∈ D, f x * (𝔼 t ∈ C, 𝔼 z ∈ Q, g (z + t) * a (x + (z + t))) := by
  unfold replacementIntegral
  rw [Finset.expect_comm Q D]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_comm Q C]
  simp_rw [mul_assoc, ← Finset.mul_expect]

variable [DecidableEq G]

theorem replacementIntegral_eq_cells (D Q C : Finset G) (a f g : G → ℝ) :
    replacementIntegral D Q C a f g =
      𝔼 z ∈ Q, bilinearIntegral D (C.image (fun t => z + t)) a f g := by
  apply Finset.expect_congr rfl
  intro z _
  unfold bilinearIntegral
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]

variable [Fintype G]

theorem abs_replacementIntegral_sub_le (D Q C : Finset G) (hC : C.Nonempty)
    (a f g : G → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (hf : ∀ x ∈ D, 0 ≤ f x)
    (htest : ∀ x ∈ D, ∀ y, |g y * a (x + y)| ≤ M)
    (hTV : ∀ t ∈ C,
      (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    |replacementIntegral D Q C a f g - bilinearIntegral D Q a f g| ≤
      M * eta * (𝔼 x ∈ D, f x) := by
  have hpoint (x : G) (hx : x ∈ D) :
      |(𝔼 t ∈ C, 𝔼 z ∈ Q, g (z + t) * a (x + (z + t))) -
        𝔼 z ∈ Q, g z * a (x + z)| ≤ M * eta := by
    calc
      _ = |(𝔼 t ∈ C, 𝔼 z ∈ Q, g (z + t) * a (x + (z + t))) -
          𝔼 _t ∈ C, 𝔼 z ∈ Q, g z * a (x + z)| := by
        rw [Finset.expect_const hC]
      _ ≤ M * eta := by
        apply abs_expect_sub_expect_le C hC
        intro t ht
        exact (abs_expect_add_sub_le Q (fun y => g y * a (x + y)) t (htest x hx)).trans
          (mul_le_mul_of_nonneg_left (hTV t ht) hM)
  rw [replacementIntegral_weighted]
  unfold bilinearIntegral
  simp_rw [mul_assoc, ← Finset.mul_expect]
  simpa only [mul_assoc] using abs_weighted_expect_sub_le D f _ _ hf hpoint

theorem abs_replacementIntegral_sub_le_of_unit_weights
    (D Q C : Finset G) (hD : D.Nonempty) (hC : C.Nonempty)
    (a f g : G → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hTV : ∀ t ∈ C,
      (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    |replacementIntegral D Q C a f g - bilinearIntegral D Q a f g| ≤ M * eta := by
  have htest (x : G) (_hx : x ∈ D) (y : G) : |g y * a (x + y)| ≤ M := by
    rw [abs_mul, abs_of_nonneg (hg y).1]
    exact (mul_le_mul_of_nonneg_left (ha _) (hg y).1).trans
      ((mul_le_mul_of_nonneg_right (hg y).2 hM).trans_eq (one_mul M))
  have hmean : (𝔼 x ∈ D, f x) ≤ 1 :=
    (Finset.expect_le_expect (fun x (_ : x ∈ D) => (hf x).2)).trans_eq
      (Finset.expect_const hD 1)
  exact (abs_replacementIntegral_sub_le D Q C hC a f g hM
    (fun x _ => (hf x).1) htest hTV).trans
      ((mul_le_mul_of_nonneg_left hmean (mul_nonneg hM heta)).trans_eq (mul_one _))

theorem abs_slice_sub_replacement_le
    (A Q D C : Finset G) (hD : D.Nonempty) (hC : C.Nonempty)
    (a f g : G → ℝ) {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (ha : ∀ x, |a x| ≤ M) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) (hsupport : ∀ x, x ∉ A → f x = 0)
    (hTV : ∀ t ∈ C,
      (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    |bilinearIntegral A Q a (Peeling.slice D f) g -
      (D.card : ℝ) / A.card * replacementIntegral D Q C a f g| ≤
      (D.card : ℝ) / A.card * (M * eta) := by
  rw [bilinearIntegral_slice_scale A Q D a f g hsupport, ← mul_sub, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ (D.card : ℝ) / A.card), abs_sub_comm]
  exact mul_le_mul_of_nonneg_left
    (abs_replacementIntegral_sub_le_of_unit_weights D Q C hD hC a f g hM heta ha hf hg hTV)
    (by positivity)

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped NNReal

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem rpow_sub_rpow_ge_tangent {u v θ : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * u ^ (θ - 1) * (u - v) ≤ u ^ θ - v ^ θ := by
  have hratio : (v / u) ^ θ ≤ 1 + θ * (v / u - 1) := by
    have h := rpow_one_add_le_one_add_mul_self
      (s := v / u - 1) (by have := div_nonneg hv hu.le; linarith) hθ0 hθ1
    simpa only [add_sub_cancel] using h
  have hscaled := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hu.le θ)
  have heq : u ^ θ * (v / u) ^ θ = v ^ θ := by
    rw [Real.div_rpow hv hu.le]
    field_simp
  rw [heq] at hscaled
  rw [Real.rpow_sub_one hu.ne']
  calc
    θ * (u ^ θ / u) * (u - v) =
        u ^ θ - u ^ θ * (1 + θ * (v / u - 1)) := by field_simp; ring
    _ ≤ _ := sub_le_sub_left hscaled _

theorem peeling_rpow {u v u₁ b K θ : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hK : 0 < K) (hbu : 0 ≤ b * u₁ ∧ b * u₁ ≤ u) (hKu : K * u ≤ u₁)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * K ^ (1 - θ) * b * (u₁ * v) ^ θ ≤
      (u * v) ^ θ - ((u - b * u₁) * v) ^ θ := by
  have hu₁ : 0 < u₁ := (mul_pos hK hu).trans_le hKu
  have hb : 0 ≤ b := by nlinarith [hbu.1]
  have hremaining : 0 ≤ u - b * u₁ := sub_nonneg.mpr hbu.2
  have hratio : K ≤ u₁ / u := (le_div_iff₀ hu).mpr hKu
  have hratioPow := Real.rpow_le_rpow hK.le hratio (sub_nonneg.mpr hθ1)
  have hinv : u ^ (θ - 1) = (u ^ (1 - θ))⁻¹ := by
    rw [show θ - 1 = -(1 - θ) by ring, Real.rpow_neg hu.le]
  have hidentity : (u₁ / u) ^ (1 - θ) * u₁ ^ θ = u ^ (θ - 1) * u₁ := by
    calc
      _ = (u₁ ^ (1 - θ) * u₁ ^ θ) / u ^ (1 - θ) := by
        rw [Real.div_rpow hu₁.le hu.le]
        ring
      _ = u₁ / u ^ (1 - θ) := by
        rw [← Real.rpow_add hu₁, sub_add_cancel, Real.rpow_one]
      _ = _ := by rw [hinv]; ring
  have hpower : K ^ (1 - θ) * u₁ ^ θ ≤ u ^ (θ - 1) * u₁ := by
    rw [← hidentity]
    exact mul_le_mul_of_nonneg_right hratioPow (Real.rpow_nonneg hu₁.le θ)
  have htangent := rpow_sub_rpow_ge_tangent hu hremaining hθ0 hθ1
  calc
    θ * K ^ (1 - θ) * b * (u₁ * v) ^ θ =
        v ^ θ * (θ * b * (K ^ (1 - θ) * u₁ ^ θ)) := by
      rw [Real.mul_rpow hu₁.le hv.le]
      ring
    _ ≤ v ^ θ * (θ * b * (u ^ (θ - 1) * u₁)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpower (mul_nonneg hθ0 hb)) (Real.rpow_nonneg hv.le θ)
    _ = v ^ θ * (θ * u ^ (θ - 1) * (u - (u - b * u₁))) := by ring
    _ ≤ v ^ θ * (u ^ θ - (u - b * u₁) ^ θ) :=
      mul_le_mul_of_nonneg_left htangent (Real.rpow_nonneg hv.le θ)
    _ = _ := by
      rw [Real.mul_rpow hu.le hv.le, Real.mul_rpow hremaining hv.le]
      ring

theorem peeling_quarter {u v u₁ b K : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hK : 0 < K) (hbu : 0 ≤ b * u₁ ∧ b * u₁ ≤ u) (hKu : K * u ≤ u₁) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * b * (u₁ * v) ^ (1 / 4 : ℝ) ≤
      (u * v) ^ (1 / 4 : ℝ) - ((u - b * u₁) * v) ^ (1 / 4 : ℝ) := by
  convert peeling_rpow hu hv hK hbu hKu (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) ≤ 1) using 1
  norm_num

theorem sqrt_average_sq_le {ι : Type*} [Fintype ι] (w X : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1) (hX : ∀ i, 0 ≤ X i) :
    (∑ i, w i * Real.sqrt (X i)) ^ 2 ≤ ∑ i, w i * X i := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i ↦ w i * Real.sqrt (X i)) (f := w) (g := fun i ↦ w i * X i)
    (fun i _ ↦ hw i) (fun i _ ↦ mul_nonneg (hw i) (hX i))
    (fun i _ ↦ by rw [mul_pow, Real.sq_sqrt (hX i)]; nlinarith)
  simpa only [hwSum, one_mul] using h

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem step_mass_bounds (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    0 ≤ (C.card : ℝ) / B.card * (𝔼 x ∈ C, f x) ∧
      (C.card : ℝ) / B.card * (𝔼 x ∈ C, f x) ≤ 𝔼 x ∈ B, f x := by
  constructor
  · exact mul_nonneg (by positivity) (Finset.expect_nonneg (fun x _ => hf x))
  · have h := Finset.expect_nonneg (s := B) (fun x _ => remainder_nonneg C f hf x)
    rw [expect_remainder B C f hsupport] at h
    linarith

theorem step_potential_le (B C : Finset G) (f : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0)
    {v K : ℝ} (hu : 0 < 𝔼 x ∈ B, f x) (hv : 0 < v) (hK : 0 < K)
    (hconc : K * (𝔼 x ∈ B, f x) ≤ 𝔼 x ∈ C, f x) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * ((C.card : ℝ) / B.card) *
        ((𝔼 x ∈ C, f x) * v) ^ (1 / 4 : ℝ) ≤
      ((𝔼 x ∈ B, f x) * v) ^ (1 / 4 : ℝ) -
        ((𝔼 x ∈ B, remainder C f x) * v) ^ (1 / 4 : ℝ) := by
  rw [expect_remainder B C f hsupport]
  exact peeling_quarter hu hv hK (step_mass_bounds B C f hf hsupport) hconc

theorem step_coefficient_le_mass_drop (B C : Finset G) (f : G → ℝ)
    (hsupport : ∀ x, x ∉ B → f x = 0) {K kappa : ℝ}
    (hK : 0 ≤ K) (hactive : kappa ≤ 𝔼 x ∈ B, f x)
    (hconc : K * (𝔼 x ∈ B, f x) ≤ 𝔼 x ∈ C, f x) :
    (K * kappa) * ((C.card : ℝ) / B.card) ≤
      (𝔼 x ∈ B, f x) - 𝔼 x ∈ B, remainder C f x := by
  have hlower := (mul_le_mul_of_nonneg_left hactive hK).trans hconc
  have h := mul_le_mul_of_nonneg_right hlower (show 0 ≤ (C.card : ℝ) / B.card by positivity)
  rw [expect_remainder B C f hsupport]
  nlinarith

end Erdos3.Peeling

end

section

namespace Erdos3

open scoped BigOperators

theorem fourth_root_product_average_le_means {ι : Type*} [Fintype ι]
    (w X Y : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwSum : ∑ i, w i = 1)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) :
    (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ≤
      ((∑ i, w i * X i) * ∑ i, w i * Y i) ^ (1 / 4 : ℝ) := by
  have hroot (i : ι) : (X i * Y i) ^ (1 / 4 : ℝ) =
      Real.sqrt (Real.sqrt (X i * Y i)) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (mul_nonneg (hX i) (hY i))]
    norm_num
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun i => w i * (X i * Y i) ^ (1 / 4 : ℝ))
    (f := fun i => w i * Real.sqrt (X i)) (g := fun i => w i * Real.sqrt (Y i))
    (fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _))
    (fun i _ => mul_nonneg (hw i) (Real.sqrt_nonneg _)) (fun i _ => by
      rw [hroot, mul_pow, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sqrt_mul (hX i)]
      exact le_of_eq (by ring))
  have hXs := sqrt_average_sq_le w X hw hwSum hX
  have hYs := sqrt_average_sq_le w Y hw hwSum hY
  have hXm : 0 ≤ ∑ i, w i * X i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hX i))
  have hYm : 0 ≤ ∑ i, w i * Y i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hY i))
  have hprod := mul_le_mul hXs hYs (sq_nonneg _) hXm
  have hfour := pow_le_pow_left₀ (sq_nonneg _) hcs 2
  have hfour' : (∑ i, w i * (X i * Y i) ^ (1 / 4 : ℝ)) ^ 4 ≤
      (∑ i, w i * X i) * ∑ i, w i * Y i := by
    nlinarith
  have hrootPow : (((∑ i, w i * X i) * ∑ i, w i * Y i) ^ (1 / 4 : ℝ)) ^ (4 : ℕ) =
      (∑ i, w i * X i) * ∑ i, w i * Y i := by
    simpa only [Nat.cast_ofNat, one_div] using
      Real.rpow_inv_natCast_pow (mul_nonneg hXm hYm) (by norm_num : (4 : ℕ) ≠ 0)
  apply le_of_pow_le_pow_left₀ (by norm_num : (4 : ℕ) ≠ 0)
    (Real.rpow_nonneg (mul_nonneg hXm hYm) (1 / 4 : ℝ))
  rwa [hrootPow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem expect_quarter_product_le (S : Finset ι) (hS : S.Nonempty) (X Y : ι → ℝ)
    (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i) {u v : ℝ}
    (hu : (𝔼 i ∈ S, X i) ≤ u) (hv : (𝔼 i ∈ S, Y i) ≤ v) :
    (𝔼 i ∈ S, (X i * Y i) ^ (1 / 4 : ℝ)) ≤ (u * v) ^ (1 / 4 : ℝ) := by
  have h := fourth_root_product_average_le_means (realUniformMass S) X Y
    (realUniformMass_nonneg S) (sum_realUniformMass hS) hX hY
  simp only [sum_uniformMass_mul_eq_expect] at h
  apply h.trans
  apply Real.rpow_le_rpow
  · exact mul_nonneg (Finset.expect_nonneg (fun i _ => hX i)) (Finset.expect_nonneg (fun i _ => hY i))
  · exact mul_le_mul hu hv (Finset.expect_nonneg (fun i _ => hY i))
      ((Finset.expect_nonneg (fun i _ => hX i)).trans hu)
  · norm_num

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem quarter_contraction_factor_bounds {M c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    3 / 4 ≤ 1 - c / (4 * (1 + Real.sqrt M) ^ 2) ∧
      1 - c / (4 * (1 + Real.sqrt M) ^ 2) < 1 := by
  have hden : 0 < 4 * (1 + Real.sqrt M) ^ 2 := by positivity
  have hratio : c / (4 * (1 + Real.sqrt M) ^ 2) ≤ 1 / 4 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [Real.sqrt_nonneg M, sq_nonneg (Real.sqrt M)]
  have hpos := div_pos hc hden
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

theorem replacementPotential_nonneg (D Q C : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x) :
    0 ≤ replacementPotential D Q C f g := by
  apply Finset.expect_nonneg
  intro z _
  exact Real.rpow_nonneg
    (mul_nonneg (Finset.expect_nonneg (fun x _ => hf x)) (cellAverage_nonneg C g hg z)) _

variable [Fintype G] [DecidableEq G]

theorem replacementPotential_le (D Q C : Finset G) (hQ : Q.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hgsupport : ∀ x, x ∉ Q → g x = 0) :
    replacementPotential D Q C f g ≤
      ((𝔼 x ∈ D, f x) * (𝔼 y ∈ Q, g y)) ^ (1 / 4 : ℝ) := by
  apply expect_quarter_product_le Q hQ (fun _ => 𝔼 x ∈ D, f x) (cellAverage C g)
  · intro _
    exact Finset.expect_nonneg (fun x _ => hf x)
  · exact cellAverage_nonneg C g hg
  · exact (Finset.expect_const hQ _).le
  · exact expect_cellAverage_comp_le Q C hC g hg hgsupport id Function.injective_id

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCost
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem Chain.potential_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa v : ℝ}
    {f g : G → ℝ} {cs : List (Finset G)} (h : Chain B Admissible K kappa f g cs)
    (hK : 0 < K) (hkappa : 0 < kappa) (hv : 0 < v) :
    (∀ x, 0 ≤ f x) → (∀ x, x ∉ B → f x = 0) →
      (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * potentialCost B v f cs ≤
        ((𝔼 x ∈ B, f x) * v) ^ (1 / 4 : ℝ) - ((𝔼 x ∈ B, g x) * v) ^ (1 / 4 : ℝ) := by
  induction h with
  | nil f => intro _ _; simp [potentialCost]
  | @step f g cs C hactive _ hconc _ ih =>
    intro hf hsupport
    have hstep := step_potential_le B C f hf hsupport (hkappa.trans_le hactive) hv hK hconc.le
    have htail := ih (remainder_nonneg C f hf) (remainder_supported B C f hsupport)
    simp only [potentialCost]
    nlinarith

theorem Chain.coefficient_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f g : G → ℝ} {cs : List (Finset G)} (h : Chain B Admissible K kappa f g cs)
    (hK : 0 ≤ K) : (∀ x, x ∉ B → f x = 0) →
      (K * kappa) * coefficientCost B cs ≤ (𝔼 x ∈ B, f x) - 𝔼 x ∈ B, g x := by
  induction h with
  | nil f => intro _; simp [coefficientCost]
  | @step f g cs C hactive _ hconc _ ih =>
    intro hsupport
    have hstep := step_coefficient_le_mass_drop B C f hsupport hK hactive hconc.le
    have htail := ih (remainder_supported B C f hsupport)
    simp only [coefficientCost, List.map_cons, List.sum_cons] at htail ⊢
    nlinarith

end Erdos3.Peeling

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PeelingReplacementPotential
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem potentialCost_zero (B : Finset G) (f : G → ℝ) (cs : List (Finset G)) :
    potentialCost B 0 f cs = 0 := by
  induction cs generalizing f with
  | nil => rfl
  | cons C cs ih =>
    simp only [potentialCost, mul_zero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), zero_add]
    exact ih (remainder C f)

theorem Chain.potential_budget_nonneg {B : Finset G} {Admissible : Finset G → Prop}
    {K kappa v : ℝ} {f g : G → ℝ} {cs : List (Finset G)}
    (h : Chain B Admissible K kappa f g cs) (hK : 0 < K) (hkappa : 0 < kappa) (hv : 0 ≤ v)
    (hf : ∀ x, 0 ≤ f x) (hsupport : ∀ x, x ∉ B → f x = 0) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * potentialCost B v f cs ≤
      ((𝔼 x ∈ B, f x) * v) ^ (1 / 4 : ℝ) - ((𝔼 x ∈ B, g x) * v) ^ (1 / 4 : ℝ) := by
  rcases hv.eq_or_lt with hv | hv
  · subst v
    simp only [potentialCost_zero, mul_zero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), sub_self, le_refl]
  · exact h.potential_budget hK hkappa hv hf hsupport

theorem pair_potential_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
        (potentialCost B (𝔼 x ∈ B, g x) f cs + potentialCost B (𝔼 x ∈ B, f' x) g ds) ≤
      ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
        ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) := by
  have h₁ := hF.potential_budget_nonneg hK hkappa (Finset.expect_nonneg (s := B) (fun x _ => hg x)) hf hfsupport
  have h₂ := hG.potential_budget_nonneg hK hkappa
    (Finset.expect_nonneg (s := B) (fun x _ => (hF.bounds hf x).1)) hg hgsupport
  have h₂' : (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) * potentialCost B (𝔼 x ∈ B, f' x) g ds ≤
      ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
        ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) := by
    simpa only [mul_comm] using h₂
  nlinarith

theorem pair_coefficient_budget {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 ≤ K) (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (K * kappa) * (coefficientCost B cs + coefficientCost B ds) ≤
      ((𝔼 x ∈ B, f x) - 𝔼 x ∈ B, f' x) + ((𝔼 x ∈ B, g x) - 𝔼 x ∈ B, g' x) := by
  have h₁ := hF.coefficient_budget hK hfsupport
  have h₂ := hG.coefficient_budget hK hgsupport
  nlinarith

end Erdos3.Peeling

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem pair_coefficientCost_le {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    coefficientCost B cs + coefficientCost B ds ≤
      ((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa) := by
  have h := pair_coefficient_budget hF hG hK.le hfsupport hgsupport
  have hf' := Finset.expect_nonneg (s := B) (fun x _ => (hF.bounds hf x).1)
  have hg' := Finset.expect_nonneg (s := B) (fun x _ => (hG.bounds hg x).1)
  apply (le_div_iff₀ (mul_pos hK hkappa)).mpr
  nlinarith

theorem weighted_pair_error_le {B : Finset G} {Admissible : Finset G → Prop} {K kappa epsilon : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Chain B Admissible K kappa f f' cs) (hG : Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hepsilon : 0 ≤ epsilon)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    epsilon * (coefficientCost B cs + coefficientCost B ds) ≤
      epsilon * (((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa)) :=
  mul_le_mul_of_nonneg_left (pair_coefficientCost_le hF hG hK hkappa hf hg hfsupport hgsupport) hepsilon

theorem contraction_after_peeling {P remainder initial a rho : ℝ}
    (hP : 0 ≤ P) (ha : 2 ≤ a) (hrho : 1 / 2 ≤ rho)
    (hbudget : a * P + remainder ≤ initial) :
    P + rho * remainder ≤ rho * initial := by
  have hrho0 : 0 ≤ rho := by linarith
  have hprod : 1 ≤ rho * a := by
    have h := mul_le_mul hrho ha (by norm_num : (0 : ℝ) ≤ 2) hrho0
    norm_num at h
    exact h
  nlinarith [mul_le_mul_of_nonneg_right hprod hP,
    mul_le_mul_of_nonneg_left hbudget hrho0]

end Erdos3.Peeling

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem replacementPotentialSum_nonneg (A Q : Finset G) (shape : Finset G → Finset G)
    (g : G → ℝ) (hg : ∀ x, 0 ≤ g x) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ds : List (Finset G)) : 0 ≤ replacementPotentialSum A Q shape g f ds := by
  induction ds generalizing f with
  | nil => simp [replacementPotentialSum]
  | cons D ds ih =>
    exact add_nonneg (mul_nonneg (by positivity) (replacementPotential_nonneg D Q (shape D) f g hf hg))
      (ih (Peeling.remainder D f) (Peeling.remainder_nonneg D f hf))

variable [Fintype G]

theorem replacementPotentialSum_le_cost (A Q : Finset G) (hQ : Q.Nonempty)
    (shape : Finset G → Finset G) (g : G → ℝ) (hg : ∀ x, 0 ≤ g x)
    (hgsupport : ∀ x, x ∉ Q → g x = 0) (f : G → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ds : List (Finset G)) (hshape : ∀ D ∈ ds, (shape D).Nonempty) :
    replacementPotentialSum A Q shape g f ds ≤ Peeling.potentialCost A (𝔼 y ∈ Q, g y) f ds := by
  induction ds generalizing f with
  | nil => simp [replacementPotentialSum, Peeling.potentialCost]
  | cons D ds ih =>
    simp only [replacementPotentialSum, Peeling.potentialCost]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (replacementPotential_le D Q (shape D) hQ (hshape D (List.mem_cons_self)) f g hf hg hgsupport)
        (by positivity))
      (ih (Peeling.remainder D f) (Peeling.remainder_nonneg D f hf)
        (fun C hC => hshape C (List.mem_cons_of_mem D hC)))

theorem pair_replacement_potential_budget
    {B : Finset G} (hB : B.Nonempty) {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (shape : Finset G → Finset G)
    (hshape : ∀ D, Admissible D → (shape D).Nonempty)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
      (replacementPotentialSum B B shape g f cs + replacementPotentialSum B B shape f' g ds) ≤
        ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
          ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) := by
  have hfirst := replacementPotentialSum_le_cost B B hB shape g hg hgsupport f hf cs
    (fun D hD => hshape D (hF.admissible_mem D hD))
  have hsecond := replacementPotentialSum_le_cost B B hB shape f'
    (fun x => (hF.bounds hf x).1) (hF.supported hf hfsupport) g hg ds
    (fun D hD => hshape D (hG.admissible_mem D hD))
  exact (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (by positivity)).trans (Peeling.pair_potential_budget hF hG hK hkappa hf hg hfsupport hgsupport)

theorem pair_replacement_contraction
    {B : Finset G} (hB : B.Nonempty) {Admissible : Finset G → Prop} {K kappa rho : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hrho : 1 / 2 ≤ rho) (shape : Finset G → Finset G)
    (hshape : ∀ D, Admissible D → (shape D).Nonempty)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    replacementPotentialSum B B shape g f cs + replacementPotentialSum B B shape f' g ds +
      rho * ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) ≤
        rho * ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) := by
  have hbudget := pair_replacement_potential_budget hB hF hG hK hkappa shape hshape hf hg
    hfsupport hgsupport
  apply Peeling.contraction_after_peeling
    (add_nonneg (replacementPotentialSum_nonneg B B shape g hg f hf cs)
      (replacementPotentialSum_nonneg B B shape f' (fun x => (hF.bounds hf x).1) g hg ds))
    hKfactor hrho
  linarith

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalWeightCaps
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem translated_slice_le (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : Peeling.slice L (fun t => f (x + t)) r ≤ f (x + r) := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem translated_slice_nonneg (L : Finset G) (f : G → ℝ) (hf : ∀ r, 0 ≤ f r)
    (x r : G) : 0 ≤ Peeling.slice L (fun t => f (x + t)) r := by
  by_cases hr : r ∈ L <;> simp [Peeling.slice, hr, hf]

omit [Fintype G] in
theorem expect_translated_slice (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, Peeling.slice L (fun t => f (x + t)) r) = cellAverage L f x := by
  apply Finset.expect_congr rfl
  intro r hr
  simp only [Peeling.slice, hr, ite_true]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteCellRefinement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem bilinearIntegral_restrict (A B : Finset G) (a f g : G → ℝ) :
    bilinearIntegral A B a (Peeling.slice A f) (Peeling.slice B g) =
      bilinearIntegral A B a f g := by
  apply Finset.expect_congr rfl
  intro x hx
  apply Finset.expect_congr rfl
  intro y hy
  simp only [Peeling.slice, hx, hy, ite_true]

theorem bilinearIntegral_translate (A B : Finset G) (a f g : G → ℝ) (x₀ y₀ : G) :
    bilinearIntegral (A.image (fun x => x₀ + x)) (B.image (fun y => y₀ + y)) a f g =
      bilinearIntegral A B (fun z => a (x₀ + y₀ + z)) (fun x => f (x₀ + x))
        (fun y => g (y₀ + y)) := by
  unfold bilinearIntegral
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro x _
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  apply Finset.expect_congr rfl
  intro y _
  have heq : x₀ + x + (y₀ + y) = x₀ + y₀ + (x + y) := by abel
  rw [heq]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

end Erdos3

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

theorem expect_translated_cell (C : Finset G) (f : G → ℝ) (z : G) :
    (𝔼 x ∈ C.image (fun t => z + t), f x) = cellAverage C f z := by
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)]
  rfl

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

variable [Fintype G] [DecidableEq G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem centerSlice_bounds (L : Finset G) (f : G → ℝ)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (x r : G) :
    0 ≤ centerSlice L f x r ∧ centerSlice L f x r ≤ 1 := by
  exact ⟨translated_slice_nonneg L f (fun t => (hf t).1) x r,
    (translated_slice_le L f (fun t => (hf t).1) x r).trans (hf (x + r)).2⟩

theorem centerSlice_supported (L : Finset G) (f : G → ℝ) (x : G) :
    ∀ r, r ∉ L → centerSlice L f x r = 0 := by
  intro r hr
  simp only [centerSlice, Peeling.slice, hr, ite_false]

theorem centerSlice_mean (L : Finset G) (f : G → ℝ) (x : G) :
    (𝔼 r ∈ L, centerSlice L f x r) = cellAverage L f x :=
  expect_translated_slice L f x

variable [Fintype G]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem bilinearIntegral_translated_centerSlices (C : Finset G) (a f g : G → ℝ) (x y : G) :
    bilinearIntegral (C.image (fun r => x + r)) (C.image (fun r => y + r)) a f g =
      bilinearIntegral C C (fun r => a (x + y + r)) (centerSlice C f x) (centerSlice C g y) := by
  rw [bilinearIntegral_translate]
  exact (bilinearIntegral_restrict C C (fun r => a (x + y + r))
    (fun r => f (x + r)) (fun r => g (y + r))).symm

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G]

variable [DecidableEq G]

theorem translated_integral_le_of_cellBilinearBound
    (C : Finset G) (a f g : G → ℝ) (origin x y : G) {T : ℝ}
    (hbound : CellBilinearBound C a T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    bilinearIntegral (C.image (fun r => x + r)) (C.image (fun r => y + r))
        (fun r => a (origin + r)) f g ≤
      T * (cellAverage C f x * cellAverage C g y) ^ (1 / 4 : ℝ) := by
  rw [bilinearIntegral_translated_centerSlices]
  have h := hbound (origin + (x + y)) (centerSlice C f x) (centerSlice C g y)
    (centerSlice_bounds C f hf x) (centerSlice_bounds C g hg y)
    (centerSlice_supported C f x) (centerSlice_supported C g y)
  simpa only [centerSlice_mean, add_assoc] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] {I : Type*}

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingCellCaps
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem exists_terminal_pair (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : G → ℝ) :
    ∃ f' g' cs ds, Chain B Admissible K kappa f f' cs ∧ Chain B Admissible K kappa g g' ds ∧
      ((𝔼 x ∈ B, f' x) < kappa ∨ (𝔼 x ∈ B, g' x) < kappa ∨
        ((∀ C, Admissible C → (𝔼 x ∈ C, f' x) ≤ K * (𝔼 x ∈ B, f' x)) ∧
         (∀ C, Admissible C → (𝔼 x ∈ C, g' x) ≤ K * (𝔼 x ∈ B, g' x)))) := by
  classical
  by_cases hgsmall : (𝔼 x ∈ B, g x) < kappa
  · exact ⟨f, g, [], [], Chain.nil f, Chain.nil g, Or.inr (Or.inl hgsmall)⟩
  obtain ⟨f', cs, hF, hfstop⟩ := exists_terminal_chain B Admissible hK hkappa f
  by_cases hfsmall : (𝔼 x ∈ B, f' x) < kappa
  · exact ⟨f', g, cs, [], hF, Chain.nil g, Or.inl hfsmall⟩
  have hffree := hfstop.resolve_left hfsmall
  obtain ⟨g', ds, hG, hgstop⟩ := exists_terminal_chain B Admissible hK hkappa g
  refine ⟨f', g', cs, ds, hF, hG, Or.inr ?_⟩
  rcases hgstop with hgsmall | hgfree
  · exact Or.inl hgsmall
  · exact Or.inr ⟨hffree, hgfree⟩

end Erdos3.Peeling

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

omit [Fintype G] in
theorem cap_of_translated_terminal (B : Finset G) (Shape : Finset G → Prop)
    (f : G → ℝ) {K : ℝ}
    (hflat : ∀ A, translatedCellFamily Shape A → (𝔼 x ∈ A, f x) ≤ K * (𝔼 x ∈ B, f x)) :
    ∀ C, Shape C → ∀ z, cellAverage C f z ≤ K * (𝔼 x ∈ B, f x) := by
  intro C hC z
  have h := hflat (C.image (fun t => z + t)) ⟨C, hC, z, rfl⟩
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)] at h
  exact h

theorem exists_terminal_pair_with_cell_caps (B : Finset G) (Shape : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : G → ℝ) :
    ∃ f' g' cs ds,
      Chain B (translatedCellFamily Shape) K kappa f f' cs ∧
      Chain B (translatedCellFamily Shape) K kappa g g' ds ∧
      ((𝔼 x ∈ B, f' x) < kappa ∨ (𝔼 x ∈ B, g' x) < kappa ∨
        ((∀ C, Shape C → ∀ z, cellAverage C f' z ≤ K * (𝔼 x ∈ B, f' x)) ∧
         (∀ C, Shape C → ∀ z, cellAverage C g' z ≤ K * (𝔼 x ∈ B, g' x)))) := by
  obtain ⟨f', g', cs, ds, hF, hG, hterminal⟩ :=
    exists_terminal_pair B (translatedCellFamily Shape) hK hkappa f g
  refine ⟨f', g', cs, ds, hF, hG, ?_⟩
  rcases hterminal with hfsmall | hgsmall | ⟨hfflat, hgflat⟩
  · exact Or.inl hfsmall
  · exact Or.inr (Or.inl hgsmall)
  · exact Or.inr (Or.inr ⟨cap_of_translated_terminal B Shape f' hfflat,
      cap_of_translated_terminal B Shape g' hgflat⟩)

end Erdos3.Peeling

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PeelingChildBound
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

variable [Fintype G]

theorem chain_replacement_integral_error
    {A : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' : G → ℝ} {ds : List (Finset G)} (h : Peeling.Chain A Admissible K kappa f f' ds)
    (Q : Finset G) (shape : Finset G → Finset G) (a g : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta) (ha : ∀ x, |a x| ≤ M)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass Q (y - t) - realUniformMass Q y|) ≤ eta) :
    (∀ x, 0 ≤ f x ∧ f x ≤ 1) → (∀ x, x ∉ A → f x = 0) →
    |bilinearIntegral A Q a f g -
      (bilinearIntegral A Q a f' g + replacementIntegralSum A Q shape a g f ds)| ≤
        (M * eta) * Peeling.coefficientCost A ds := by
  induction h with
  | nil f => intro _ _; simp [replacementIntegralSum, Peeling.coefficientCost]
  | @step f f' ds D _ hD _ _ ih =>
    intro hf hsupport
    have hrem : ∀ x, 0 ≤ Peeling.remainder D f x ∧ Peeling.remainder D f x ≤ 1 := by
      intro x
      exact ⟨Peeling.remainder_nonneg D f (fun y => (hf y).1) x,
        (Peeling.remainder_le D f (fun y => (hf y).1) x).trans (hf x).2⟩
    have htail := ih hrem (Peeling.remainder_supported A D f hsupport)
    obtain ⟨hDn, hCn, hTV⟩ := hshape D hD
    have hstep := abs_slice_sub_replacement_le A Q D (shape D) hDn hCn a f g
      hM heta ha hf hg hsupport hTV
    rw [bilinearIntegral_peeling A Q D a f g]
    simp only [replacementIntegralSum, Peeling.coefficientCost, List.map_cons,
      List.sum_cons] at htail ⊢
    calc
      _ = |(bilinearIntegral A Q a (Peeling.remainder D f) g -
          (bilinearIntegral A Q a f' g +
            replacementIntegralSum A Q shape a g (Peeling.remainder D f) ds)) +
          (bilinearIntegral A Q a (Peeling.slice D f) g -
            (D.card : ℝ) / A.card * replacementIntegral D Q (shape D) a f g)| := by
        congr 1
        ring
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add htail hstep
      _ = _ := by ring

theorem pair_replacement_integral_error
    {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (shape : Finset G → Finset G) (a : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass B (y - t) - realUniformMass B y|) ≤ eta) :
    |bilinearIntegral B B a f g -
      (bilinearIntegral B B a f' g' + replacementIntegralSum B B shape a g f cs +
        replacementIntegralSum B B shape a f' g ds)| ≤
      (M * eta) * (Peeling.coefficientCost B cs + Peeling.coefficientCost B ds) := by
  have hf' : ∀ x, 0 ≤ f' x ∧ f' x ≤ 1 := by
    intro x
    have h := hF.bounds (fun y => (hf y).1) x
    exact ⟨h.1, h.2.trans (hf x).2⟩
  have hfirst := chain_replacement_integral_error hF B shape a g hM heta ha hg hshape hf hfsupport
  have hsecond := chain_replacement_integral_error hG B shape a f' hM heta ha hf' hshape hg hgsupport
  rw [bilinearIntegral_swap B B a g f', bilinearIntegral_swap B B a g' f'] at hsecond
  calc
    _ = |(bilinearIntegral B B a f g -
        (bilinearIntegral B B a f' g + replacementIntegralSum B B shape a g f cs)) +
        (bilinearIntegral B B a f' g -
          (bilinearIntegral B B a f' g' + replacementIntegralSum B B shape a f' g ds))| := by
      congr 1
      ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hfirst hsecond
    _ = _ := by ring

theorem pair_replacement_integral_error_le_mass
    {B : Finset G} {Admissible : Finset G → Prop} {K kappa : ℝ}
    {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (shape : Finset G → Finset G) (a : G → ℝ)
    {M eta : ℝ} (hM : 0 ≤ M) (heta : 0 ≤ eta) (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass B (y - t) - realUniformMass B y|) ≤ eta) :
    |bilinearIntegral B B a f g -
      (bilinearIntegral B B a f' g' + replacementIntegralSum B B shape a g f cs +
        replacementIntegralSum B B shape a f' g ds)| ≤
      (M * eta) * (((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa)) :=
  (pair_replacement_integral_error hF hG shape a hM heta ha hf hg hfsupport hgsupport hshape).trans
    (Peeling.weighted_pair_error_le hF hG hK hkappa (mul_nonneg hM heta)
      (fun x => (hf x).1) (fun x => (hg x).1) hfsupport hgsupport)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem replacementIntegral_le_of_cellBilinearBound
    (D Q C : Finset G) (a f g : G → ℝ) (origin : G) {T : ℝ}
    (hD : ∃ x, D = C.image (fun r => x + r)) (hbound : CellBilinearBound C a T)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) :
    replacementIntegral D Q C (fun r => a (origin + r)) f g ≤ T * replacementPotential D Q C f g := by
  obtain ⟨x, rfl⟩ := hD
  rw [replacementIntegral_eq_cells]
  unfold replacementPotential
  rw [expect_translated_cell]
  calc
    _ ≤ 𝔼 y ∈ Q, T * (cellAverage C f x * cellAverage C g y) ^ (1 / 4 : ℝ) := by
      apply Finset.expect_le_expect
      intro y _
      exact translated_integral_le_of_cellBilinearBound C a f g origin x y hbound hf hg
    _ = _ := (Finset.mul_expect _ _ T).symm

theorem replacementIntegralSum_le_of_cellBilinearBound
    (A Q : Finset G) (shape : Finset G → Finset G) (a g : G → ℝ) (origin : G)
    (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1) {T : ℝ} (ds : List (Finset G))
    (hshape : ∀ D ∈ ds, (∃ x, D = (shape D).image (fun r => x + r)) ∧
      CellBilinearBound (shape D) a T)
    (f : G → ℝ) (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) :
    replacementIntegralSum A Q shape (fun r => a (origin + r)) g f ds ≤
      T * replacementPotentialSum A Q shape g f ds := by
  induction ds generalizing f with
  | nil => simp [replacementIntegralSum, replacementPotentialSum]
  | cons D ds ih =>
    have hrem : ∀ r, 0 ≤ Peeling.remainder D f r ∧ Peeling.remainder D f r ≤ 1 := by
      intro r
      exact ⟨Peeling.remainder_nonneg D f (fun t => (hf t).1) r,
        (Peeling.remainder_le D f (fun t => (hf t).1) r).trans (hf r).2⟩
    have hhead := replacementIntegral_le_of_cellBilinearBound D Q (shape D) a f g origin
      (hshape D List.mem_cons_self).1 (hshape D List.mem_cons_self).2 hf hg
    have htail := ih (fun C hC => hshape C (List.mem_cons_of_mem D hC)) (Peeling.remainder D f) hrem
    simp only [replacementIntegralSum, replacementPotentialSum]
    calc
      _ ≤ (D.card : ℝ) / A.card * (T * replacementPotential D Q (shape D) f g) +
          T * replacementPotentialSum A Q shape g (Peeling.remainder D f) ds :=
        add_le_add (mul_le_mul_of_nonneg_left hhead (by positivity)) htail
      _ = _ := by ring

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem peeling_parent_bound_of_remainder
    {B : Finset G} (hB : B.Nonempty) {Admissible : Finset G → Prop}
    {K kappa T rho error M eta : ℝ} {f f' g g' : G → ℝ} {cs ds : List (Finset G)}
    (hF : Peeling.Chain B Admissible K kappa f f' cs)
    (hG : Peeling.Chain B Admissible K kappa g g' ds)
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hT : 0 ≤ T) (hrho : 1 / 2 ≤ rho) (hM : 0 ≤ M) (heta : 0 ≤ eta)
    (shape : Finset G → Finset G) (a : G → ℝ) (origin : G)
    (ha : ∀ x, |a x| ≤ M)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0)
    (hshape : ∀ D, Admissible D → D.Nonempty ∧ (shape D).Nonempty ∧
      (∃ x, D = (shape D).image (fun r => x + r)) ∧ CellBilinearBound (shape D) a T ∧
      ∀ t ∈ shape D, (∑ y, |realUniformMass B (y - t) - realUniformMass B y|) ≤ eta)
    (hremainder : bilinearIntegral B B (fun r => a (origin + r)) f' g' ≤
      T * rho * ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) + error) :
    bilinearIntegral B B (fun r => a (origin + r)) f g ≤
      T * rho * ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) + error +
        (M * eta) * (((𝔼 x ∈ B, f x) + 𝔼 x ∈ B, g x) / (K * kappa)) := by
  have hf' : ∀ x, 0 ≤ f' x ∧ f' x ≤ 1 := by
    intro x
    have h := hF.bounds (fun y => (hf y).1) x
    exact ⟨h.1, h.2.trans (hf x).2⟩
  have hfirst := replacementIntegralSum_le_of_cellBilinearBound B B shape a g origin hg cs
    (fun D hD => ⟨(hshape D (hF.admissible_mem D hD)).2.2.1,
      (hshape D (hF.admissible_mem D hD)).2.2.2.1⟩) f hf
  have hsecond := replacementIntegralSum_le_of_cellBilinearBound B B shape a f' origin hf' ds
    (fun D hD => ⟨(hshape D (hG.admissible_mem D hD)).2.2.1,
      (hshape D (hG.admissible_mem D hD)).2.2.2.1⟩) g hg
  have hbudget := pair_replacement_contraction hB hF hG hK hkappa hKfactor hrho shape
    (fun D hD => (hshape D hD).2.1) (fun x => (hf x).1) (fun x => (hg x).1)
    hfsupport hgsupport
  have hbudgetT := mul_le_mul_of_nonneg_left hbudget hT
  have herr := pair_replacement_integral_error_le_mass hF hG hK hkappa shape
    (fun r => a (origin + r)) hM heta (fun r => ha (origin + r)) hf hg hfsupport hgsupport
    (fun D hD => ⟨(hshape D hD).1, (hshape D hD).2.1, (hshape D hD).2.2.2.2⟩)
  have herrUpper := (abs_le.mp herr).2
  nlinarith only [hfirst, hsecond, hbudgetT, hremainder, herrUpper]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementErrorNormalization
namespace OAI

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem tiny_product_quarter_le {u v kappa : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1)
    (hsmall : u ≤ kappa ∨ v ≤ kappa) :
    u * v ≤ kappa ^ (3 / 4 : ℝ) * (u * v) ^ (1 / 4 : ℝ) := by
  have huv : 0 ≤ u * v := mul_nonneg hu hv
  have huvK : u * v ≤ kappa := by
    rcases hsmall with hsmall | hsmall
    · calc
        u * v ≤ u := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv1 hu
        _ ≤ kappa := hsmall
    · calc
        u * v ≤ v := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hu1 hv
        _ ≤ kappa := hsmall
  by_cases hzero : u * v = 0
  · simp only [hzero, Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0), mul_zero, le_refl]
  have hpos : 0 < u * v := lt_of_le_of_ne huv (Ne.symm hzero)
  calc
    _ = (u * v) ^ (3 / 4 : ℝ) * (u * v) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_add hpos]
      norm_num
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow huv huvK (by norm_num)) (Real.rpow_nonneg huv _)

variable {G : Type*} [AddCommGroup G]

theorem tiny_cell_integral_le (B : Finset G) (hB : B.Nonempty) (a f g : G → ℝ) (origin : G)
    {M kappa : ℝ} (hM : 0 ≤ M) (ha : ∀ r, a r ≤ M)
    (hf : ∀ r, 0 ≤ f r ∧ f r ≤ 1) (hg : ∀ r, 0 ≤ g r ∧ g r ≤ 1)
    (htiny : min (𝔼 r ∈ B, f r) (𝔼 r ∈ B, g r) < kappa) :
    bilinearIntegral B B (fun r => a (origin + r)) f g ≤
      (M * kappa ^ (3 / 4 : ℝ)) * ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  have hu : 0 ≤ 𝔼 r ∈ B, f r := Finset.expect_nonneg (fun r _ => (hf r).1)
  have hv : 0 ≤ 𝔼 r ∈ B, g r := Finset.expect_nonneg (fun r _ => (hg r).1)
  have hu1 : (𝔼 r ∈ B, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ B) => (hf r).2)).trans_eq (Finset.expect_const hB 1)
  have hv1 : (𝔼 r ∈ B, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ B) => (hg r).2)).trans_eq (Finset.expect_const hB 1)
  have hprod := tiny_product_quarter_le hu hv hu1 hv1 ((min_lt_iff.mp htiny).imp le_of_lt le_of_lt)
  have h := bilinearIntegral_le B B (fun r => a (origin + r)) f g
    (fun r => ha (origin + r)) (fun r => (hf r).1) (fun r => (hg r).1)
  have hscaled := mul_le_mul_of_nonneg_left hprod hM
  nlinarith only [h, hscaled]

omit [AddCommGroup G] in
theorem quarter_cell_potential_mono (B : Finset G) (f f' g g' : G → ℝ)
    (hf' : ∀ r, 0 ≤ f' r) (hg' : ∀ r, 0 ≤ g' r)
    (hff' : ∀ r, f' r ≤ f r) (hgg' : ∀ r, g' r ≤ g r) :
    ((𝔼 r ∈ B, f' r) * (𝔼 r ∈ B, g' r)) ^ (1 / 4 : ℝ) ≤
      ((𝔼 r ∈ B, f r) * (𝔼 r ∈ B, g r)) ^ (1 / 4 : ℝ) := by
  have hF := Finset.expect_nonneg (s := B) (fun r _ => hf' r)
  have hG := Finset.expect_nonneg (s := B) (fun r _ => hg' r)
  have hFl := Finset.expect_le_expect (s := B) (fun r _ => hff' r)
  have hGl := Finset.expect_le_expect (s := B) (fun r _ => hgg' r)
  exact Real.rpow_le_rpow (mul_nonneg hF hG) (mul_le_mul hFl hGl hG (hF.trans hFl)) (by norm_num)

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators

theorem cutoff_sq_le_quarter_potential {u v cutoff : ℝ}
    (hcutoff : 0 ≤ cutoff) (hu : cutoff ≤ u) (hv : cutoff ≤ v)
    (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    cutoff ^ 2 ≤ (u * v) ^ (1 / 4 : ℝ) := by
  have hu0 : 0 ≤ u := hcutoff.trans hu
  have hv0 : 0 ≤ v := hcutoff.trans hv
  have hprod : u * v ≤ 1 := by nlinarith
  calc
    cutoff ^ 2 ≤ u * v := by
      simpa only [pow_two] using mul_le_mul hu hv hcutoff hu0
    _ ≤ _ := Real.self_le_rpow_of_le_one (mul_nonneg hu0 hv0) hprod (by norm_num)

theorem refinement_error_le_potential {u v cutoff K error loss : ℝ}
    (hcutoff : 0 < cutoff) (hK : 0 < K) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (hu : cutoff ≤ u) (hv : cutoff ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) :
    error + loss * ((u + v) / (K * cutoff)) ≤
      (error / cutoff ^ 2 + 2 * loss / (K * cutoff ^ 3)) * (u * v) ^ (1 / 4 : ℝ) := by
  have hpotential := cutoff_sq_le_quarter_potential hcutoff.le hu hv hu1 hv1
  have he : error ≤ error / cutoff ^ 2 * (u * v) ^ (1 / 4 : ℝ) := by
    calc
      error = error / cutoff ^ 2 * cutoff ^ 2 := by
        exact (div_mul_cancel₀ error (pow_ne_zero 2 hcutoff.ne')).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hpotential (div_nonneg herror (sq_nonneg cutoff))
  have hl : loss * ((u + v) / (K * cutoff)) ≤
      (2 * loss / (K * cutoff ^ 3)) * (u * v) ^ (1 / 4 : ℝ) := by
    calc
      loss * ((u + v) / (K * cutoff)) ≤ loss * (2 / (K * cutoff)) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (by linarith)
          (mul_pos hK hcutoff).le) hloss
      _ = (2 * loss / (K * cutoff ^ 3)) * cutoff ^ 2 := by
        field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpotential (by positivity)
  nlinarith only [he, hl]

variable {G : Type*} [AddCommGroup G]

theorem cellBilinearBound_of_refinement
    (C : Finset G) (hC : C.Nonempty) (a : G → ℝ)
    {W cutoff K T epsilon error loss : ℝ}
    (hW : 0 ≤ W) (ha : ∀ r, a r ≤ W) (hcutoff : 0 < cutoff) (hK : 0 < K)
    (hT : 0 ≤ T) (herror : 0 ≤ error) (hloss : 0 ≤ loss)
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ epsilon)
    (hstep : ∀ origin : G, ∀ f g : G → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      (∀ r, r ∉ C → f r = 0) → (∀ r, r ∉ C → g r = 0) →
      cutoff ≤ (𝔼 r ∈ C, f r) → cutoff ≤ (𝔼 r ∈ C, g r) →
      bilinearIntegral C C (fun r => a (origin + r)) f g ≤
        (T + epsilon) * ((𝔼 r ∈ C, f r) * (𝔼 r ∈ C, g r)) ^ (1 / 4 : ℝ) + error +
          loss * (((𝔼 r ∈ C, f r) + 𝔼 r ∈ C, g r) / (K * cutoff))) :
    CellBilinearBound C a
      (T + epsilon + error / cutoff ^ 2 + 2 * loss / (K * cutoff ^ 3)) := by
  intro origin f g hf hg hfs hgs
  have hu1 : (𝔼 r ∈ C, f r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ C) => (hf r).2)).trans_eq (Finset.expect_const hC 1)
  have hv1 : (𝔼 r ∈ C, g r) ≤ 1 :=
    (Finset.expect_le_expect (fun r (_ : r ∈ C) => (hg r).2)).trans_eq (Finset.expect_const hC 1)
  have hPhi : 0 ≤ ((𝔼 r ∈ C, f r) * (𝔼 r ∈ C, g r)) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun r _ => (hf r).1))
      (Finset.expect_nonneg (fun r _ => (hg r).1))) _
  by_cases hsmall : min (𝔼 r ∈ C, f r) (𝔼 r ∈ C, g r) < cutoff
  · have h := tiny_cell_integral_le C hC a f g origin hW ha hf hg hsmall
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ hPhi
    have he : 0 ≤ error / cutoff ^ 2 := by positivity
    have hl : 0 ≤ 2 * loss / (K * cutoff ^ 3) := by positivity
    linarith
  · obtain ⟨hu, hv⟩ := le_min_iff.mp (le_of_not_gt hsmall)
    have h := hstep origin f g hf hg hfs hgs hu hv
    have he := refinement_error_le_potential hcutoff hK herror hloss hu hv hu1 hv1
    nlinarith only [h, he]

end Erdos3.CellRefinement

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UnbalancedBohrShape
namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_budgeted_bohr_peeling
    (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ) (minimumWidth : ℝ)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : ZMod N → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0) (hgsupport : ∀ x, x ∉ B.carrier → g x = 0) :
    let Shapes := admissibleBohrCarriers B scale rankExtra minimumWidth
    ∃ f' g' cs ds, Chain B.carrier (translatedCellFamily Shapes) K kappa f f' cs ∧
      Chain B.carrier (translatedCellFamily Shapes) K kappa g g' ds ∧
      cs.length + ds.length ≤ (positiveSupport f).card + (positiveSupport g).card ∧
      (∀ x, 0 ≤ f' x ∧ f' x ≤ f x) ∧ (∀ x, 0 ≤ g' x ∧ g' x ≤ g x) ∧
      (∀ x, x ∉ B.carrier → f' x = 0) ∧ (∀ x, x ∉ B.carrier → g' x = 0) ∧
      (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
          (potentialCost B.carrier (𝔼 x ∈ B.carrier, g x) f cs +
            potentialCost B.carrier (𝔼 x ∈ B.carrier, f' x) g ds) ≤
        ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) -
          ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) ∧
      coefficientCost B.carrier cs + coefficientCost B.carrier ds ≤
        ((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa) ∧
      ((𝔼 x ∈ B.carrier, f' x) < kappa ∨ (𝔼 x ∈ B.carrier, g' x) < kappa ∨
        ((∀ C, admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
            cellAverage C.carrier f' z ≤ K * (𝔼 x ∈ B.carrier, f' x)) ∧
         (∀ C, admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
            cellAverage C.carrier g' z ≤ K * (𝔼 x ∈ B.carrier, g' x)))) := by
  intro Shapes
  obtain ⟨f', g', cs, ds, hF, hG, hterminal⟩ :=
    exists_terminal_pair_with_cell_caps B.carrier Shapes hK hkappa f g
  refine ⟨f', g', cs, ds, hF, hG,
    Nat.add_le_add (hF.length_le_support hK hkappa) (hG.length_le_support hK hkappa),
    hF.bounds hf, hG.bounds hg, hF.supported hf hfsupport, hG.supported hg hgsupport,
    pair_potential_budget hF hG hK hkappa hf hg hfsupport hgsupport,
    pair_coefficientCost_le hF hG hK hkappa hf hg hfsupport hgsupport, ?_⟩
  rcases hterminal with hfsmall | hgsmall | ⟨hfcap, hgcap⟩
  · exact Or.inl hfsmall
  · exact Or.inr (Or.inl hgsmall)
  · exact Or.inr (Or.inr ⟨fun C hC z => hfcap C.carrier ⟨C, hC, rfl⟩ z,
      fun C hC z => hgcap C.carrier ⟨C, hC, rfl⟩ z⟩)

end Erdos3.Peeling

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.Peeling

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem exists_admissible_shape_selection
    (B : CyclicBohr.Set N) (scale : ℝ≥0) (rankExtra : ℕ) (minimumWidth : ℝ) :
    ∃ shape : Finset (ZMod N) → CyclicBohr.Set N, ∀ D,
      translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth) D →
        admissibleBohrShape B scale rankExtra minimumWidth (shape D) ∧
          ∃ z, D = (shape D).carrier.image (fun t => z + t) := by
  classical
  have hex : ∀ D : Finset (ZMod N), ∃ C : CyclicBohr.Set N,
      translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth) D →
        admissibleBohrShape B scale rankExtra minimumWidth C ∧
          ∃ z, D = C.carrier.image (fun t => z + t) := by
    intro D
    by_cases hD : translatedCellFamily (admissibleBohrCarriers B scale rankExtra minimumWidth) D
    · obtain ⟨E, ⟨C, hC, hE⟩, z, hz⟩ := hD
      exact ⟨C, fun _ => ⟨hC, z, by simpa only [hE] using hz⟩⟩
    · exact ⟨B, fun h => False.elim (hD h)⟩
  choose shape hshape using hex
  exact ⟨shape, hshape⟩

theorem admissible_shape_translation_control
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    {rankExtra : ℕ} {minimumWidth : ℝ} (D : Finset (ZMod N)) (C : CyclicBohr.Set N)
    (hC : admissibleBohrShape B scale rankExtra minimumWidth C)
    (hD : ∃ z, D = C.carrier.image (fun t => z + t)) :
    D.Nonempty ∧ C.carrier.Nonempty ∧ ∀ t ∈ C.carrier,
      (∑ y, |realUniformMass B.carrier (y - t) - realUniformMass B.carrier y|) ≤
        400 * (max B.rank 1 : ℕ) * (scale : ℝ) := by
  refine ⟨?_, C.carrier_nonempty, ?_⟩
  · obtain ⟨z, rfl⟩ := hD
    obtain ⟨x, hx⟩ := C.carrier_nonempty
    exact ⟨z + x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro t ht
    apply CyclicBohr.Set.uniformMass_translation_le_of_rankRegular hB hscale
    simpa only [CyclicBohr.Set.mem_iff, CyclicBohr.Set.mem_carrier] using hC.2.1 ht

end Erdos3.Peeling

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

section

namespace Erdos3.CellRefinement

open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

theorem bohr_peeling_parent_bound
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (rankExtra : ℕ) (minimumWidth : ℝ) {K kappa T rho error W : ℝ}
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hT : 0 ≤ T) (hrho : 1 / 2 ≤ rho) (hW : 0 ≤ W)
    (a f g : ZMod N → ℝ) (origin : ZMod N) (ha : ∀ x, |a x| ≤ W)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0) (hgsupport : ∀ x, x ∉ B.carrier → g x = 0)
    {f' g' : ZMod N → ℝ} {cs ds : List (Finset (ZMod N))}
    (hF : Peeling.Chain B.carrier
      (Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa f f' cs)
    (hG : Peeling.Chain B.carrier
      (Peeling.translatedCellFamily (Peeling.admissibleBohrCarriers B scale rankExtra minimumWidth))
      K kappa g g' ds)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C →
      CellBilinearBound C.carrier a T)
    (hremainder : bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
      T * rho * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) + error) :
    bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f g ≤
      T * rho * ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) + error +
        (W * (400 * (max B.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa)) := by
  obtain ⟨shape, hshape⟩ := Peeling.exists_admissible_shape_selection B scale rankExtra minimumWidth
  apply peeling_parent_bound_of_remainder B.carrier_nonempty hF hG hK hkappa hKfactor hT hrho
    hW (by positivity) (fun D => (shape D).carrier) a origin ha hf hg hfsupport hgsupport _ hremainder
  intro D hD
  obtain ⟨hC, htranslate⟩ := hshape D hD
  obtain ⟨hDn, hCn, hTV⟩ := Peeling.admissible_shape_translation_control B hB hscale D (shape D) hC htranslate
  exact ⟨hDn, hCn, htranslate, hchildren (shape D) hC, hTV⟩

theorem bohr_parent_bound_from_capped
    (B : CyclicBohr.Set N) (hB : B.IsRankRegular) {scale : ℝ≥0}
    (hscale : scale ≤ 1 / (100 * (2 * max B.rank 1 : ℕ) : ℝ≥0))
    (rankExtra : ℕ) (minimumWidth : ℝ) {K kappa T rho epsilon eta W : ℝ}
    (hK : 0 < K) (hkappa : 0 < kappa) (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hT : 0 ≤ T) (hrho : 1 / 2 ≤ rho) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta) (hW : 0 ≤ W)
    (htiny : W * kappa ^ (3 / 4 : ℝ) ≤ epsilon)
    (a f g : ZMod N → ℝ) (origin : ZMod N) (ha : ∀ x, |a x| ≤ W)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hfsupport : ∀ x, x ∉ B.carrier → f x = 0) (hgsupport : ∀ x, x ∉ B.carrier → g x = 0)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C →
      CellBilinearBound C.carrier a T)
    (hcapped : ∀ f' g' : ZMod N → ℝ,
      (∀ x, 0 ≤ f' x ∧ f' x ≤ 1) → (∀ x, 0 ≤ g' x ∧ g' x ≤ 1) →
      (∀ x, x ∉ B.carrier → f' x = 0) → (∀ x, x ∉ B.carrier → g' x = 0) →
      kappa ≤ (𝔼 x ∈ B.carrier, f' x) → kappa ≤ (𝔼 x ∈ B.carrier, g' x) →
      (∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
        cellAverage C.carrier f' z ≤ K * (𝔼 x ∈ B.carrier, f' x)) →
      (∀ C, Peeling.admissibleBohrShape B scale rankExtra minimumWidth C → ∀ z,
        cellAverage C.carrier g' z ≤ K * (𝔼 x ∈ B.carrier, g' x)) →
      bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
        (T * rho + epsilon) * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) + eta) :
    bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f g ≤
      (T * rho + epsilon) * ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) + eta +
        (W * (400 * (max B.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 x ∈ B.carrier, f x) + 𝔼 x ∈ B.carrier, g x) / (K * kappa)) := by
  obtain ⟨f', g', cs, ds, hF, hG, _, hfb, hgb, hfs, hgs, _, _, hterminal⟩ :=
    Peeling.exists_budgeted_bohr_peeling B scale rankExtra minimumWidth hK hkappa f g
      (fun x => (hf x).1) (fun x => (hg x).1) hfsupport hgsupport
  have hf' : ∀ x, 0 ≤ f' x ∧ f' x ≤ 1 := fun x => ⟨(hfb x).1, (hfb x).2.trans (hf x).2⟩
  have hg' : ∀ x, 0 ≤ g' x ∧ g' x ≤ 1 := fun x => ⟨(hgb x).1, (hgb x).2.trans (hg x).2⟩
  have hPhi := quarter_cell_potential_mono B.carrier f f' g g' (fun x => (hfb x).1)
    (fun x => (hgb x).1) (fun x => (hfb x).2) (fun x => (hgb x).2)
  have hPhi0 : 0 ≤ ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (Finset.expect_nonneg (fun x _ => (hf' x).1))
      (Finset.expect_nonneg (fun x _ => (hg' x).1))) _
  have hrem : bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
      (T * rho + epsilon) * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) + eta := by
    by_cases hsmall : min (𝔼 x ∈ B.carrier, f' x) (𝔼 x ∈ B.carrier, g' x) < kappa
    · have h := tiny_cell_integral_le B.carrier B.carrier_nonempty a f' g' origin hW
        (fun x => (le_abs_self (a x)).trans (ha x)) hf' hg' hsmall
      have hcoef := mul_nonneg hT (show 0 ≤ rho by linarith)
      have ht := mul_le_mul_of_nonneg_right htiny hPhi0
      nlinarith only [h, ht, mul_nonneg hcoef hPhi0, heta]
    · have hlower := le_min_iff.mp (le_of_not_gt hsmall)
      rcases hterminal with hsmallF | hsmallG | ⟨hcapF, hcapG⟩
      · exact False.elim (hsmall (min_lt_iff.mpr (Or.inl hsmallF)))
      · exact False.elim (hsmall (min_lt_iff.mpr (Or.inr hsmallG)))
      · exact hcapped f' g' hf' hg' hfs hgs hlower.1 hlower.2 hcapF hcapG
  have hrem' : bilinearIntegral B.carrier B.carrier (fun r => a (origin + r)) f' g' ≤
      T * rho * ((𝔼 x ∈ B.carrier, f' x) * (𝔼 x ∈ B.carrier, g' x)) ^ (1 / 4 : ℝ) +
        (epsilon * ((𝔼 x ∈ B.carrier, f x) * (𝔼 x ∈ B.carrier, g x)) ^ (1 / 4 : ℝ) + eta) := by
    have h := mul_le_mul_of_nonneg_left hPhi hepsilon
    nlinarith only [hrem, h]
  have h := bohr_peeling_parent_bound B hB hscale rankExtra minimumWidth hK hkappa hKfactor
    hT hrho hW a f g origin ha hf hg hfsupport hgsupport hF hG hchildren hrem'
  nlinarith only [h]

end Erdos3.CellRefinement

end

section

namespace Erdos3.LocalConvolution

open scoped BigOperators NNReal
open CyclicCrootSisask

variable {N : ℕ} [NeZero N]

end Erdos3.LocalConvolution

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefinementEnlargement
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N]

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

theorem unbalanced_factor_bounds {c M : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    3 / 4 ≤ 1 - c / (128 * (1 + Real.sqrt M) ^ 2) ∧
      1 - c / (128 * (1 + Real.sqrt M) ^ 2) < 1 := by
  have h := quarter_contraction_factor_bounds (M := M)
    (show 0 < c / 32 by positivity) (show c / 32 ≤ 1 by linarith)
  have heq : c / 32 / (4 * (1 + Real.sqrt M) ^ 2) = c / (128 * (1 + Real.sqrt M) ^ 2) := by
    rw [div_div]
    congr 1
    ring
  simpa only [heq] using h

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem bilinear_refinement_step
    (B₀ L S : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hscale : scale ≤ 1 / (100 * (2 * max B₀.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B F G : ZMod N → ℝ) (origin : ZMod N)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    (hF : ∀ r, 0 ≤ F r ∧ F r ≤ 1) (hG : ∀ r, 0 ≤ G r ∧ G r ≤ 1)
    (hFsupport : ∀ r, r ∉ B₀.carrier → F r = 0)
    (hGsupport : ∀ r, r ∉ B₀.carrier → G r = 0)
    {M K c₀ cutoff : ℝ} (hc₀ : 0 < c₀) (hK : 0 < K) (hcutoff : 0 < cutoff)
    (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMcutoff : 1 ≤ M * (c₀ * cutoff))
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ Real.exp (-(D * p)))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      |bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g -
        parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    let Phi := ((𝔼 r ∈ B₀.carrier, F r) * (𝔼 r ∈ B₀.carrier, G r)) ^ (1 / 4 : ℝ)
    bilinearIntegral B₀.carrier B₀.carrier
        (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) F G ≤
      (T * ((1 + rho) / 2) + Real.exp (-(D * p))) * Phi + Real.exp (-E) + matchingError +
        (W * (400 * (max B₀.rank 1 : ℕ) * (scale : ℝ))) *
          (((𝔼 r ∈ B₀.carrier, F r) + 𝔼 r ∈ B₀.carrier, G r) / (K * cutoff)) := by
  intro rho Phi
  have hgamma : 0 < γ := localMomentGain_pos δ
  have hgamma1 : γ ≤ 1 := (localMomentGain_le_half δ).trans (by norm_num)
  have hrho := (unbalanced_factor_bounds (M := K / c₀) hgamma hgamma1).1
  have hmatching0 : 0 ≤ matchingError := (abs_nonneg _).trans (hmatching F G hF hG)
  have hcapped : ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      (∀ r, r ∉ B₀.carrier → f r = 0) → (∀ r, r ∉ B₀.carrier → g r = 0) →
      cutoff ≤ (𝔼 r ∈ B₀.carrier, f r) → cutoff ≤ (𝔼 r ∈ B₀.carrier, g r) →
      (∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C → ∀ z,
        cellAverage C.carrier f z ≤ K * (𝔼 r ∈ B₀.carrier, f r)) →
      (∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C → ∀ z,
        cellAverage C.carrier g z ≤ K * (𝔼 r ∈ B₀.carrier, g r)) →
      bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g ≤
        (T * ((1 + rho) / 2) + Real.exp (-(D * p))) *
          ((𝔼 r ∈ B₀.carrier, f r) * (𝔼 r ∈ B₀.carrier, g r)) ^ (1 / 4 : ℝ) +
          (Real.exp (-E) + matchingError) := by
    intro f g hf hg hfs hgs hlu hlv hfcap hgcap
    have hMu : 1 ≤ M * (c₀ * (𝔼 r ∈ B₀.carrier, f r)) := hMcutoff.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlu hc₀.le) hM.le)
    have hMv : 1 ≤ M * (c₀ * (𝔼 r ∈ B₀.carrier, g r)) := hMcutoff.trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlv hc₀.le) hM.le)
    have h := capped_parent_bound_of_children B₀ L S hL hSpos hSwidth hSreg hSrank
      hfreq hlocalWidth hepsilon hp hD hR hH hSL hkappa hSB hrank hwidth hLshape
      A B f g origin hA hB hf hg hfs hgs (hcutoff.trans_le hlu) (hcutoff.trans_le hlv)
      hc₀ hK.le rfl rfl hfactor hfcap hgcap hM hMcap hMu hMv hSLmoment herror hSlog
      hcomplexity hprecision hcompare hW hWcap hQ hE ha (hmatching f g hf hg)
      m hm horder horders hT hchildren
    simpa only [add_assoc] using h
  have h := bohr_parent_bound_from_capped B₀ hB₀ hscale extra minimumWidth hK hcutoff hKfactor
    hT (by linarith : 1 / 2 ≤ (1 + rho) / 2) (Real.exp_nonneg _) (by positivity) hW htiny
    (fun r => A r - (1 + epsilon) * B r) F G origin ha hF hG hFsupport hGsupport hchildren hcapped
  simpa only [add_assoc] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution
open scoped BigOperators NNReal

variable {N : ℕ} [NeZero N] {epsilon : ℝ}

local notation "δ" => flatComparisonDelta epsilon
local notation "γ" => localMomentGain δ

theorem normalized_bilinear_refinement_step
    (B₀ L S : CyclicBohr.Set N) (hB₀ : B₀.IsRankRegular) (hL : L.IsRankRegular)
    (hSpos : 0 < S.radius) (hSwidth : S.radius ≤ 1)
    (hSreg : S.IsRankRegular) (hSrank : 1 ≤ S.rank)
    (hfreq : S.frequencies = L.frequencies) (hlocalWidth : S.radius ≤ L.radius)
    {kappa scale : ℝ≥0} {extra : ℕ} {minimumWidth p D R P H W Q E : ℝ}
    (hepsilon : 0 < epsilon) (hp : 1 ≤ p) (hD : 0 ≤ D) (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hSL : S.carrier ⊆ (L.ndilate kappa).carrier)
    (hkappa : kappa + kappa ≤ 1 / (100 * (2 * max L.rank 1 : ℕ) : ℝ≥0))
    (hscale : scale ≤ 1 / (100 * (2 * max B₀.rank 1 : ℕ) : ℝ≥0))
    (hSB : S.carrier ⊆ (B₀.ndilate scale).carrier)
    (hrank : S.rank + unbalancedRankExtra γ p H ≤ B₀.rank + extra)
    (hwidth : minimumWidth ≤ S.radius * Real.exp (-unbalancedReturnWidthLoss S.rank γ p H Q E))
    (hLshape : Peeling.admissibleBohrShape B₀ scale extra minimumWidth L)
    (A B : ZMod N → ℝ)
    (hA : ∀ r, 0 ≤ A r ∧ A r ≤ Real.exp p)
    (hB : ∀ r, 0 ≤ B r ∧ B r ≤ Real.exp p)
    {M K c₀ cutoff : ℝ} (hc₀ : 0 < c₀) (hK : 0 < K) (hcutoff : 0 < cutoff)
    (hKfactor : 2 ≤ (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ))
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2)
    (hM : 0 < M) (hMcap : M ≤ Real.exp p)
    (hMcutoff : 1 ≤ M * (c₀ * cutoff))
    (htiny : W * cutoff ^ (3 / 4 : ℝ) ≤ Real.exp (-(D * p)))
    (hSLmoment : S.carrier ⊆ (L.ndilate (controlledLocalMomentScale L.rank M δ)).carrier)
    (herror : M ^ 2 * (400 * (max L.rank 1 : ℕ) * ((kappa + kappa : ℝ≥0) : ℝ)) ≤ γ / 32)
    (hSlog : Real.exp (-R) ≤ S.radius)
    (hcomplexity : 2 * (S.rank : ℝ) + p + (D + 2) * p + R + 1612 ≤ P)
    (hprecision : (D + 2) * p + 2 + (S.rank : ℝ) * (R + 10) ≤ P)
    (hcompare : CyclicNiltestUpperComparison.{0} 1 N P (Real.exp (-P)) A B)
    (hW : 0 ≤ W) (hWcap : W ≤ Real.exp Q) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (ha : ∀ r, |A r - (1 + epsilon) * B r| ≤ W)
    {matchingError : ℝ}
    (hmatching : ∀ origin : ZMod N, ∀ f g : ZMod N → ℝ,
      (∀ r, 0 ≤ f r ∧ f r ≤ 1) → (∀ r, 0 ≤ g r ∧ g r ≤ 1) →
      |bilinearIntegral B₀.carrier B₀.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g -
        parentTruncatedIntegral B₀.carrier B₀.carrier L.carrier S.carrier
          (fun r => A (origin + r) - (1 + epsilon) * B (origin + r)) f g| ≤ matchingError)
    (m : ℕ) (hm : 0 < m)
    (horder : (1 + 1 + (D + 1) + Real.log 3) * p ≤ ((2 * m : ℕ) : ℝ) * Real.log 2)
    (horders : ∀ m' : ℕ, m ≤ m' → m' ≤ localMomentExponentFactor δ * m →
      ((2 * m' : ℕ) : ℝ) ≤ H * p ∧
      (1 + γ / 4) ^ (2 * m') ≤ (γ / 64) / 2 * (1 + γ / 2) ^ (2 * m'))
    {T : ℝ} (hT : 0 ≤ T)
    (hchildren : ∀ C, Peeling.admissibleBohrShape B₀ scale extra minimumWidth C →
      CellBilinearBound C.carrier (fun r => A r - (1 + epsilon) * B r) T) :
    let rho := 1 - γ / (128 * (1 + Real.sqrt (K / c₀)) ^ 2)
    CellBilinearBound B₀.carrier (fun r => A r - (1 + epsilon) * B r)
      (T * ((1 + rho) / 2) + Real.exp (-(D * p)) +
        (Real.exp (-E) + matchingError) / cutoff ^ 2 +
        2 * (W * (400 * (max B₀.rank 1 : ℕ) * (scale : ℝ))) / (K * cutoff ^ 3)) := by
  intro rho
  have hgamma : 0 < γ := localMomentGain_pos δ
  have hgamma1 : γ ≤ 1 := (localMomentGain_le_half δ).trans (by norm_num)
  have hrho := (unbalanced_factor_bounds (M := K / c₀) hgamma hgamma1).1
  have hmatching0 : 0 ≤ matchingError := (abs_nonneg _).trans
    (hmatching 0 (fun _ => 0) (fun _ => 0) (by intro r; norm_num) (by intro r; norm_num))
  apply cellBilinearBound_of_refinement B₀.carrier B₀.carrier_nonempty
    (fun r => A r - (1 + epsilon) * B r) hW
    (fun r => (le_abs_self _).trans (ha r)) hcutoff hK
    (mul_nonneg hT (by linarith : 0 ≤ (1 + rho) / 2))
    (add_nonneg (Real.exp_nonneg _) hmatching0) (by positivity) htiny
  intro origin f g hf hg hfs hgs _ _
  have h := bilinear_refinement_step B₀ L S hB₀ hL hSpos hSwidth hSreg hSrank
    hfreq hlocalWidth hepsilon hp hD hR hH hSL hkappa hscale hSB hrank hwidth hLshape
    A B f g origin hA hB hf hg hfs hgs hc₀ hK hcutoff hKfactor hfactor hM hMcap hMcutoff
    htiny hSLmoment herror hSlog hcomplexity hprecision hcompare hW hWcap hQ hE ha
    (hmatching origin) m hm horder horders hT hchildren
  simpa only [add_assoc] using h

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

open LocalConvolution

end Erdos3.CellRefinement

end

section

namespace Erdos3.CellRefinement

end Erdos3.CellRefinement

end

end OAI

end

theorem solution : type_of% @OAI.Erdos3.CellRefinement.normalized_bilinear_refinement_step := @OAI.Erdos3.CellRefinement.normalized_bilinear_refinement_step
