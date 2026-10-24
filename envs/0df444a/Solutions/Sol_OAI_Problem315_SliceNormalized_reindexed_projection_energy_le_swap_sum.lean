-- Prove2me | solution 1 for OAI.Problem315.SliceNormalized.reindexed_projection_energy_le_swap_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:16:39.962137+00:00
-- url     : https://prove2.me/submissions/d30979dd-f4bc-47b8-9e63-47a4e8573e8b

import Mathlib
import Definitions.Def_OAIQWSWC002

section
-- module Solutions.OAIQW_Problem315.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_Problem315.FrameSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


noncomputable section

open scoped BigOperators

namespace Problem315.FrameSynthesis

variable {ι E : Type*} [Fintype ι] [sectionDecidableEqι : DecidableEq ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

section Adjoint
variable [FiniteDimensional ℝ E]

theorem synthesis_adjoint_apply (z : ι → E) (f : E) :
    synthesis z ((synthesis z).adjoint f) = ∑ i, ⟪z i, f⟫ • z i := by
  simp only [synthesis_apply, adjoint_synthesis_apply]

end Adjoint

variable [FiniteDimensional ℝ E]

theorem frame_apply_of_common_norm_sq (z : ι → E) (a : ℝ)
    (hz : ∀ i, z i = 0 ∨ ‖z i‖ ^ 2 = a) (f : E) :
    synthesis z ((synthesis z).adjoint f) = a • ∑ i, (ℝ ∙ z i).starProjection f := by
  rw [synthesis_adjoint_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rcases hz i with hzero | hnorm
  · simp [hzero]
  · rw [← Submodule.smul_starProjection_singleton ℝ f]
    change ‖z i‖ ^ 2 • (ℝ ∙ z i).starProjection f = _
    rw [hnorm]

theorem frame_energy_of_common_norm_sq (z : ι → E) (a : ℝ)
    (hz : ∀ i, z i = 0 ∨ ‖z i‖ ^ 2 = a) (f : E) :
    ⟪f, synthesis z ((synthesis z).adjoint f)⟫ =
      a * ∑ i, ‖(ℝ ∙ z i).starProjection f‖ ^ 2 := by
  rw [frame_apply_of_common_norm_sq z a hz, inner_smul_right, inner_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have h := (ℝ ∙ z i).re_inner_starProjection_eq_normSq f
  simpa only [RCLike.re_to_real, real_inner_comm,
    Submodule.starProjection_apply, Submodule.norm_coe] using h


end Problem315.FrameSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.GramComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem315.Analytic

variable {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem gram_comparison_of_range
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (hinv : ∀ y : E, y ∈ LinearMap.range B → G y ∈ LinearMap.range B)
    (hcomp : ∀ c : F, ‖LinearMap.adjoint B (B c)‖ ^ 2 ≤ ⟪B c, G (B c)⟫)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  let M := LinearMap.range B
  let p := M.starProjection x
  let q := x - p
  have hp : p ∈ M := M.starProjection_apply_mem x
  have hq : q ∈ Mᗮ := M.sub_starProjection_mem_orthogonal x
  have hx : x = p + q := by dsimp only [q]; abel
  have hBq : LinearMap.adjoint B q = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [LinearMap.adjoint_inner_left]
    rw [real_inner_comm]
    exact hq (B (LinearMap.adjoint B q)) (LinearMap.mem_range_self _ _)
  have hcross : ⟪p, G q⟫ = 0 := by
    rw [← hG p q]
    exact hq (G p) (hinv p hp)
  have hcross' : ⟪q, G p⟫ = 0 := by
    rw [real_inner_comm]
    exact hq (G p) (hinv p hp)
  have hnorm : ‖LinearMap.adjoint B x‖ ^ 2 = ‖LinearMap.adjoint B p‖ ^ 2 := by
    rw [hx, map_add, hBq, add_zero]
  have hform : ⟪x, G x⟫ = ⟪p, G p⟫ + ⟪q, G q⟫ := by
    rw [hx, map_add, inner_add_left, inner_add_right, inner_add_right,
      hcross, hcross']
    ring
  obtain ⟨c, hc⟩ := hp
  have hccomp := hcomp c
  rw [hc] at hccomp
  rw [← LinearMap.adjoint_inner_left, real_inner_self_eq_norm_sq, hnorm, hform]
  exact hccomp.trans (le_add_of_nonneg_right (hpos q))

theorem gram_comparison_of_two_blocks_without_signs
    (B : F →ₗ[ℝ] E) (G : E →ₗ[ℝ] E) (hG : G.IsSymmetric)
    (hpos : ∀ x : E, 0 ≤ ⟪x, G x⟫)
    (μ₁ μ₂ lam₁ lam₂ : ℝ)
    (hbound₁ : μ₁ ≤ lam₁) (hbound₂ : μ₂ ≤ lam₂)
    (hdecomp : ∀ c : F, ∃ u v : F,
      B c = B u + B v ∧ ⟪u, v⟫ = 0 ∧
      LinearMap.adjoint B (B u) = μ₁ • u ∧
      LinearMap.adjoint B (B v) = μ₂ • v ∧
      G (B u) = lam₁ • B u ∧ G (B v) = lam₂ • B v)
    (x : E) : ⟪x, B (LinearMap.adjoint B x)⟫ ≤ ⟪x, G x⟫ := by
  apply gram_comparison_of_range B G hG hpos
  · rintro y ⟨c, rfl⟩
    obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
    rw [hc, map_add, hGu, hGv]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (LinearMap.mem_range_self B u))
      (Submodule.smul_mem _ _ (LinearMap.mem_range_self B v))
  · intro c
    obtain ⟨u, v, hc, huv, hKu, hKv, hGu, hGv⟩ := hdecomp c
    have hvu : ⟪v, u⟫ = 0 := by rw [real_inner_comm]; exact huv
    have hBu : ⟪B u, B u⟫ = μ₁ * ‖u‖ ^ 2 := by
      rw [← B.adjoint_inner_right, hKu, inner_smul_right, real_inner_self_eq_norm_sq]
    have hBv : ⟪B v, B v⟫ = μ₂ * ‖v‖ ^ 2 := by
      rw [← B.adjoint_inner_right, hKv, inner_smul_right, real_inner_self_eq_norm_sq]
    have hBuv : ⟪B u, B v⟫ = 0 := by
      rw [← B.adjoint_inner_right, hKv, inner_smul_right, huv, mul_zero]
    have hBvu : ⟪B v, B u⟫ = 0 := by rw [real_inner_comm]; exact hBuv
    rw [hc, map_add, hKu, hKv, ← real_inner_self_eq_norm_sq,
      map_add, hGu, hGv]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real, huv, hvu, hBuv, hBvu, hBu, hBv,
      real_inner_self_eq_norm_sq, mul_zero, add_zero, zero_add]
    have hposu : 0 ≤ μ₁ * ‖u‖ ^ 2 := by
      rw [← hBu]
      rw [real_inner_self_eq_norm_sq]
      positivity
    have hposv : 0 ≤ μ₂ * ‖v‖ ^ 2 := by
      rw [← hBv]
      rw [real_inner_self_eq_norm_sq]
      positivity
    have h₁ := mul_le_mul_of_nonneg_right hbound₁ hposu
    have h₂ := mul_le_mul_of_nonneg_right hbound₂ hposv
    nlinarith

end Problem315.Analytic

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.PairOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.PairOrbit

variable {α : Type*} [sectionFintypeα : Fintype α] [DecidableEq α]

theorem color_filter (S T : Finset α) (b c : Bool) :
    (Finset.univ.filter fun a => membershipColor S T a = (b,c)) =
      if b then (if c then S ∩ T else S \ T)
      else (if c then T \ S else Finset.univ \ (S ∪ T)) := by
  cases b <;> cases c <;> ext a <;>
    simp [membershipColor, not_or, and_comm]

theorem membershipColor_fiber_card
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) (b : Bool × Bool) :
    Fintype.card {a // membershipColor S T a = b} =
      Fintype.card {a // membershipColor U V a = b} := by
  have hdiff : (S \ T).card = (U \ V).card := by
    have ha := Finset.card_sdiff_add_card_inter S T
    have hb := Finset.card_sdiff_add_card_inter U V
    omega
  have hdiff' : (T \ S).card = (V \ U).card := by
    have ha := Finset.card_sdiff_add_card_inter T S
    have hb := Finset.card_sdiff_add_card_inter V U
    have hI' : (T ∩ S).card = (V ∩ U).card := by simpa [Finset.inter_comm] using hI
    omega
  have hunion : (S ∪ T).card = (U ∪ V).card := by
    have ha := Finset.card_union_add_card_inter S T
    have hb := Finset.card_union_add_card_inter U V
    omega
  have hcompl : (Finset.univ \ (S ∪ T)).card = (Finset.univ \ (U ∪ V)).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      Finset.card_sdiff_of_subset (Finset.subset_univ _), hunion]
  rcases b with ⟨b,c⟩
  rw [Fintype.card_subtype, Fintype.card_subtype, color_filter, color_filter]
  cases b <;> cases c <;> simp [hI, hdiff, hdiff', hcompl]

theorem exists_perm_membership
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    ∃ e : Equiv.Perm α,
      (∀ a, a ∈ S ↔ e a ∈ U) ∧ (∀ a, a ∈ T ↔ e a ∈ V) := by
  let ef : ∀ b : Bool × Bool,
      {a // membershipColor S T a = b} ≃ {a // membershipColor U V a = b} :=
    fun b => Fintype.equivOfCardEq (membershipColor_fiber_card S T U V hS hT hI b)
  let e : Equiv.Perm α := Equiv.ofFiberEquiv ef
  have hc (a : α) : membershipColor U V (e a) = membershipColor S T a :=
    Equiv.ofFiberEquiv_map ef a
  refine ⟨e, ?_, ?_⟩
  · intro a
    have hh := congrArg Prod.fst (hc a)
    simpa [membershipColor, eq_comm] using hh
  · intro a
    have hh := congrArg Prod.snd (hc a)
    simpa [membershipColor, eq_comm] using hh

include sectionFintypeα in
theorem image_eq_of_membership (S U : Finset α) (e : Equiv.Perm α)
    (h : ∀ a, a ∈ S ↔ e a ∈ U) : S.image e = U := by
  have retainedsectionFintypeα := sectionFintypeα
  ext b
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    exact (h a).mp ha
  · intro hb
    apply Finset.mem_image.mpr
    refine ⟨e.symm b, ?_, e.apply_symm_apply b⟩
    apply (h (e.symm b)).mpr
    simpa using hb

theorem exists_perm_image
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) :
    ∃ e : Equiv.Perm α, S.image e = U ∧ T.image e = V := by
  obtain ⟨e, heS, heT⟩ := exists_perm_membership S T U V hS hT hI
  exact ⟨e, image_eq_of_membership S U e heS, image_eq_of_membership T V e heT⟩

theorem invariant_kernel_eq_of_card
    {β : Type*} (K : Finset α → Finset α → β)
    (hinv : ∀ (e : Equiv.Perm α) S T, K (S.image e) (T.image e) = K S T)
    (S T U V : Finset α)
    (hS : S.card = U.card) (hT : T.card = V.card)
    (hI : (S ∩ T).card = (U ∩ V).card) : K S T = K U V := by
  obtain ⟨e, heS, heT⟩ := exists_perm_image S T U V hS hT hI
  simpa only [heS, heT] using (hinv e S T).symm

theorem invariant_pair_kernel_eq_of_intersection
    {β : Type*} (K : Finset α → Finset α → β)
    (hinv : ∀ (e : Equiv.Perm α) S T, K (S.image e) (T.image e) = K S T)
    (S T U V : Finset α)
    (hS : S.card = 2) (hT : T.card = 2) (hU : U.card = 2) (hV : V.card = 2)
    (hI : (S ∩ T).card = (U ∩ V).card) : K S T = K U V := by
  exact invariant_kernel_eq_of_card K hinv S T U V (hS.trans hU.symm)
    (hT.trans hV.symm) hI

end Problem315.PairOrbit

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceEquality

theorem equalityIndicator_polynomial
    {α : Type*} (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (i j : α) :
    equalityIndicator x i j = 1 - x i - x j + 2 * x i * x j := by
  rcases hbinary i with hi | hi <;> rcases hbinary j with hj | hj <;>
    norm_num [equalityIndicator, hi, hj]

theorem centeredEquality_polynomial
    {α : Type*} (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (i j : α) :
    centeredEquality x p i j = (1 - p - x i) - x j + (2 * x i) * x j := by
  rw [centeredEquality, equalityIndicator_polynomial x hbinary]
  ring

theorem centeredEquality_symmetric
    {α : Type*} (x : α → ℝ) (p : ℝ) (i j : α) :
    centeredEquality x p i j = centeredEquality x p j i := by
  simp [centeredEquality, equalityIndicator, eq_comm]

theorem offDiagonal_symmetric
    {α : Type*} [DecidableEq α] (z : α → α → ℝ)
    (hsymm : ∀ i j, z i j = z j i) (i j : α) :
    offDiagonal z i j = offDiagonal z j i := by
  simp [offDiagonal, eq_comm, hsymm]

theorem sum_offDiagonal
    {α : Type*} [Fintype α] [DecidableEq α] (z : α → α → ℝ) (i : α) :
    (∑ j, offDiagonal z i j) = (∑ j, z i j) - z i i := by
  have hterm (j : α) : offDiagonal z i j = z i j - if i = j then z i i else 0 := by
    by_cases hij : i = j
    · subst j
      simp [offDiagonal]
    · simp [offDiagonal, hij]
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib]

theorem centeredEquality_row_sum
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q) (i : α) :
    (∑ j, offDiagonal (centeredEquality x p) i j) =
      ((Fintype.card α : ℝ) - q - 1) - ((Fintype.card α : ℝ) - 1) * p +
        (2 * q - (Fintype.card α : ℝ)) * x i := by
  rw [sum_offDiagonal]
  have hdiag : centeredEquality x p i i = 1 - p := by
    simp [centeredEquality, equalityIndicator]
  rw [hdiag]
  simp_rw [centeredEquality_polynomial x hbinary]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum, hsum]
  ring

theorem additive_coeff_pairing
    {α : Type*} [Fintype α]
    (u : α → ℝ) (z : α → α → ℝ) (hsymm : ∀ i j, z i j = z j i) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, (u i + u j) * z i j) =
      ∑ i, u i * (∑ j, z i j) := by
  have htranspose : (∑ i, ∑ j, u j * z i j) = ∑ i, ∑ j, u i * z i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hsymm j i]
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [htranspose]
  simp_rw [← Finset.mul_sum]
  ring

theorem additive_centeredEquality_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    (1 / 2 : ℝ) *
      (∑ i, ∑ j, (u i + u j) * offDiagonal (centeredEquality x p) i j) =
      (2 * q - (Fintype.card α : ℝ)) * (∑ i, u i * x i) := by
  rw [additive_coeff_pairing u _
    (offDiagonal_symmetric _ (centeredEquality_symmetric x p))]
  simp_rw [centeredEquality_row_sum x hbinary q p hsum]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hu, zero_mul, zero_add]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem centeredEquality_total
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q p : ℝ) (hsum : ∑ j, x j = q) :
    (∑ i, ∑ j, offDiagonal (centeredEquality x p) i j) =
      q * (q - 1) + ((Fintype.card α : ℝ) - q) * ((Fintype.card α : ℝ) - q - 1) -
        (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) * p := by
  simp_rw [centeredEquality_row_sum x hbinary q p hsum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ← Finset.mul_sum, hsum]
  ring

theorem centeredEquality_total_zero
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : 2 ≤ Fintype.card α)
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (q : ℝ) (hsum : ∑ j, x j = q) :
    (∑ i, ∑ j, offDiagonal
      (centeredEquality x
        ((q * (q - 1) + ((Fintype.card α : ℝ) - q) * ((Fintype.card α : ℝ) - q - 1)) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)))) i j) = 0 := by
  rw [centeredEquality_total x hbinary q _ hsum]
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hcard
  have hn : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have hm : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

theorem row_zero_centeredEquality_image
    {α : Type*} [Fintype α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (c : α → α → ℝ)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j * centeredEquality x p i j) =
      2 * (∑ i, ∑ j, c i j * (x i * x j)) := by
  have hconstant : (∑ i, ∑ j, c i j * (1 - p)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hleft : (∑ i, ∑ j, c i j * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hright : (∑ i, ∑ j, c i j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol, zero_mul]
  calc
    _ = ∑ i, ∑ j,
        (c i j * (1 - p) - c i j * x i - c i j * x j +
          2 * (c i j * (x i * x j))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [centeredEquality_polynomial x hbinary]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hconstant, hleft, hright]
      ring

theorem row_zero_offDiagonal_centeredEquality_image
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (p : ℝ) (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (1 / 2 : ℝ) * (∑ i, ∑ j, c i j * offDiagonal (centeredEquality x p) i j) =
      ∑ i, ∑ j, c i j * (x i * x j) := by
  have hterm (i j : α) :
      c i j * offDiagonal (centeredEquality x p) i j =
        c i j * centeredEquality x p i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp [offDiagonal, hij]
  simp_rw [hterm]
  rw [row_zero_centeredEquality_image x hbinary p c hrow hcol]
  ring

end Problem315.SliceEquality

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceEuclideanGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem moveOperator_symmetric (q : ℕ) (a b : α) :
    (moveOperator q a b).IsSymmetric := by
  intro f g
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, moveOperator_apply]
  have h := Equiv.sum_comp (swapState q a b)
    (fun S : State α q => g S * f (swapState q a b S))
  simpa only [swapState_twice] using h.symm

theorem move_energy (q : ℕ) (a b : α) (f : EuclideanSpace ℝ (State α q)) :
    ⟪f, f - moveOperator q a b f⟫ =
      (1 / 2 : ℝ) * ‖f - moveOperator q a b f‖ ^ 2 := by
  have hs := moveOperator_symmetric q a b f (moveOperator q a b f)
  rw [moveOperator_twice] at hs
  have hn := norm_sub_sq_real f (moveOperator q a b f)
  have hnorm : ‖moveOperator q a b f‖ ^ 2 = ‖f‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using hs
  rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [hn, hnorm]
  ring

theorem generator_symmetric (q : ℕ) : (generator (α := α) q).IsSymmetric := by
  apply LinearMap.IsSymmetric.smul (by simp)
  apply LinearMap.isSymmetric_sum
  intro a _
  apply LinearMap.isSymmetric_sum
  intro b _
  exact LinearMap.IsSymmetric.id.sub (moveOperator_symmetric q a b)

theorem generator_energy (q : ℕ) (f : EuclideanSpace ℝ (State α q)) :
    ⟪f, generator q f⟫ =
      (1 / 8 : ℝ) * ∑ a : α, ∑ b : α, ‖f - moveOperator q a b f‖ ^ 2 := by
  simp only [generator, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.id_apply, inner_smul_right, inner_sum]
  simp_rw [move_energy, ← Finset.mul_sum]
  ring

theorem generator_positive (q : ℕ) (f : EuclideanSpace ℝ (State α q)) :
    0 ≤ ⟪f, generator q f⟫ := by
  rw [generator_energy]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _)

end Problem315.SliceEuclideanGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGenerator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGenerator

theorem sum_swap_coordinate
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k : α) :
    (∑ i, ∑ j, (x k - x (Equiv.swap i j k))) =
      2 * ((Fintype.card α : ℝ) * x k - ∑ i, x i) := by
  have inner_sum (i : α) :
      (∑ j, (x k - x (Equiv.swap i j k))) =
        (if i = k then (Fintype.card α : ℝ) * x k - ∑ j, x j else 0) +
          (x k - x i) := by
    by_cases hi : i = k
    · subst i
      simp [Finset.sum_sub_distrib, mul_comm]
    · have hterm (j : α) :
          x k - x (Equiv.swap i j k) = if j = k then x k - x i else 0 := by
        by_cases hj : j = k
        · subst j
          simp
        · simp [Equiv.swap_apply_of_ne_of_ne (Ne.symm hi) (Ne.symm hj), hj]
      simp_rw [hterm]
      simp [hi]
  simp_rw [inner_sum]
  simp only [Finset.sum_add_distrib]
  simp [Finset.sum_sub_distrib, mul_comm]
  ring

theorem sum_swap_coordinate_cross
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k l : α) (hkl : k ≠ l) :
    (∑ i, ∑ j,
      (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) =
      -2 * (x k - x l) ^ 2 := by
  have hterm (i j : α) :
      (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l)) =
        (if i = k ∧ j = l then -(x k - x l) ^ 2 else 0) +
        (if i = l ∧ j = k then -(x k - x l) ^ 2 else 0) := by
    by_cases hik : i = k <;> by_cases hil : i = l <;>
      by_cases hjk : j = k <;> by_cases hjl : j = l <;>
      simp_all [Equiv.swap_apply_def, eq_comm] <;> ring
  simp_rw [hterm, Finset.sum_add_distrib]
  simp_rw [ite_and]
  simp
  ring

theorem sum_swap_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (k l : α) (hkl : k ≠ l) :
    (∑ i, ∑ j,
      (x k * x l - x (Equiv.swap i j k) * x (Equiv.swap i j l))) =
      4 * ((Fintype.card α : ℝ) - 1) * x k * x l +
      2 * (x k ^ 2 + x l ^ 2) - 2 * (∑ i, x i) * (x k + x l) := by
  calc
    _ = ∑ i, ∑ j,
        (x l * (x k - x (Equiv.swap i j k)) +
         x k * (x l - x (Equiv.swap i j l)) -
         (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = x l * (∑ i, ∑ j, (x k - x (Equiv.swap i j k))) +
        x k * (∑ i, ∑ j, (x l - x (Equiv.swap i j l))) -
        (∑ i, ∑ j,
          (x k - x (Equiv.swap i j k)) * (x l - x (Equiv.swap i j l))) := by
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = _ := by
      rw [sum_swap_coordinate, sum_swap_coordinate,
        sum_swap_coordinate_cross x k l hkl]
      ring

theorem generator_coordinate
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q) (k : α) :
    generator (fun y => y k) x = ((Fintype.card α : ℝ) * x k - q) / 2 := by
  unfold generator
  simp only [Function.comp_apply]
  rw [sum_swap_coordinate, hsum]
  ring

theorem generator_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (k l : α) (hkl : k ≠ l) :
    generator (fun y => y k * y l) x =
      ((Fintype.card α : ℝ) - 1) * x k * x l - (q - 1) / 2 * (x k + x l) := by
  have hsq (i : α) : x i ^ 2 = x i := by
    rcases hbinary i with h | h <;> simp [h]
  unfold generator
  simp only [Function.comp_apply]
  rw [sum_swap_quadratic x k l hkl, hsum, hsq k, hsq l]
  ring

theorem generator_centered_linear
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator (fun y => ∑ i, u i * y i) x =
      (Fintype.card α : ℝ) / 2 * (∑ i, u i * x i) := by
  have heq : (fun y : α → ℝ => ∑ i, u i * y i) =
      ∑ i, u i • (fun y : α → ℝ => y i) := by
    ext y
    simp
  change generatorLinearMap (fun y => ∑ i, u i * y i) x = _
  rw [heq, map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, u i * generator (fun y => y i) x) = _
  simp_rw [generator_coordinate x (∑ j, x j) rfl]
  simp_rw [← mul_div_assoc, ← Finset.sum_div, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, hu, zero_mul, sub_zero]
  rw [show (∑ i, u i * ((Fintype.card α : ℝ) * x i)) =
      (Fintype.card α : ℝ) * ∑ i, u i * x i by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring]
  ring

theorem sum_coeff_linear_eq_zero
    {α : Type*} [Fintype α]
    (c : α → α → ℝ) (x : α → ℝ)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j * (x i + x j)) = 0 := by
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hleft : (∑ i, ∑ j, c i j * x i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [← Finset.sum_mul, hrow, zero_mul]
  have hright : (∑ i, ∑ j, c i j * x j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    rw [← Finset.sum_mul, hcol, zero_mul]
  rw [hleft, hright, add_zero]

theorem generator_row_zero_quadratic
    {α : Type*} [Fintype α] [DecidableEq α]
    (x : α → ℝ) (q : ℝ) (hsum : ∑ i, x i = q)
    (hbinary : ∀ i, x i = 0 ∨ x i = 1)
    (c : α → α → ℝ) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, ∑ j, c i j = 0) (hcol : ∀ j, ∑ i, c i j = 0) :
    generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x =
      ((Fintype.card α : ℝ) - 1) * (∑ i, ∑ j, c i j * (x i * x j)) := by
  have heq : (fun y : α → ℝ => ∑ i, ∑ j, c i j * (y i * y j)) =
      ∑ i, ∑ j, c i j • (fun y : α → ℝ => y i * y j) := by
    ext y
    simp
  change generatorLinearMap (fun y => ∑ i, ∑ j, c i j * (y i * y j)) x = _
  rw [heq, map_sum]
  simp_rw [map_sum, map_smul]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ i, ∑ j, c i j * generator (fun y => y i * y j) x) = _
  have hterm (i j : α) : c i j * generator (fun y => y i * y j) x =
      ((Fintype.card α : ℝ) - 1) * (c i j * (x i * x j)) -
        (q - 1) / 2 * (c i j * (x i + x j)) := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · rw [generator_quadratic x q hsum hbinary i j hij]
      ring
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [sum_coeff_linear_eq_zero c x hrow hcol]
  ring

end Problem315.SliceGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGeneratorSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem coordinates_binary {q : ℕ} (S : State α q) (i : α) :
    coordinates S i = 0 ∨ coordinates S i = 1 := by
  by_cases hi : i ∈ S.val <;> simp [coordinates, hi]

theorem coordinates_sum {q : ℕ} (S : State α q) :
    ∑ i, coordinates S i = (q : ℝ) := by
  have hc := (Finset.mem_powersetCard.mp S.property).2
  simp [coordinates, hc]

theorem coordinates_swap {q : ℕ} (S : State α q) (a b : α) :
    coordinates (swapState q a b S) = coordinates S ∘ Equiv.swap a b := by
  ext i
  have hm : i ∈ (swapState q a b S).val ↔ Equiv.swap a b i ∈ S.val := by
    change i ∈ S.val.image (Equiv.swap a b) ↔ _
    constructor
    · intro hi
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hi
      have he' := congrArg (Equiv.swap a b) he
      have hji : j = Equiv.swap a b i := by simpa using he'
      exact hji ▸ hj
    · intro hi
      apply Finset.mem_image.mpr
      exact ⟨Equiv.swap a b i, hi, by simp⟩
  simp only [coordinates, Function.comp_apply, hm]

theorem generator_sample (q : ℕ) (f : (α → ℝ) → ℝ) :
    generator q (sample q f) = sample q (SliceGenerator.generator f) := by
  ext S
  rw [generator_apply]
  simp only [sample_apply, SliceGenerator.generator, coordinates_swap]
  ring

theorem generator_sample_linear (q : ℕ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator q (sample q (fun y => ∑ i, u i * y i)) =
      ((Fintype.card α : ℝ) / 2) • sample q (fun y => ∑ i, u i * y i) := by
  rw [generator_sample]
  ext S
  change SliceGenerator.generator (fun y => ∑ i, u i * y i) (coordinates S) = _
  simpa only [PiLp.smul_apply, smul_eq_mul, sample_apply] using
    SliceGenerator.generator_centered_linear (coordinates S) u hu

theorem generator_sample_quadratic (q : ℕ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    generator q (sample q (fun y => ∑ i, ∑ j, c i j * (y i * y j))) =
      ((Fintype.card α : ℝ) - 1) • sample q (fun y => ∑ i, ∑ j, c i j * (y i * y j)) := by
  rw [generator_sample]
  ext S
  change SliceGenerator.generator (fun y => ∑ i, ∑ j, c i j * (y i * y j)) (coordinates S) = _
  simpa only [PiLp.smul_apply, smul_eq_mul, sample_apply] using
    SliceGenerator.generator_row_zero_quadratic (coordinates S) (q : ℝ)
      (coordinates_sum S) (coordinates_binary S) c hdiag hrow hcol

end Problem315.SliceEuclideanGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Problem315.SliceMoments

variable {V : Type*} [sectionDecidableEqV : DecidableEq V]

theorem average_containment (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) (hCq : C.card ≤ q) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hdenC : (U.card.choose C.card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (hCq.trans hq)).ne'
  have hmul := Nat.choose_mul (n := U.card) hCq
  have hmulR : (U.card.choose q : ℝ) * (q.choose C.card : ℝ) =
      (U.card.choose C.card : ℝ) * ((U.card - C.card).choose (q - C.card) : ℝ) := by
    exact_mod_cast hmul
  unfold average
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.card_filter_powersetCard_subset C U q hCU hCq]
  apply (div_eq_div_iff hden hdenC).mpr
  nlinarith

theorem average_containment_all (U C : Finset V) (q : ℕ)
    (hCU : C ⊆ U) (hq : q ≤ U.card) :
    average U q (fun S => if C ⊆ S then 1 else 0) =
      (q.choose C.card : ℝ) / (U.card.choose C.card : ℝ) := by
  by_cases hCq : C.card ≤ q
  · exact average_containment U C q hCU hq hCq
  · have hlt : q < C.card := by omega
    have hempty : (U.powersetCard q).filter (C ⊆ ·) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro S hS hCS
      have hcard := Finset.card_le_card hCS
      have hScard := (Finset.mem_powersetCard.mp hS).2
      omega
    unfold average
    rw [← Finset.sum_filter, hempty]
    simp [Nat.choose_eq_zero_of_lt hlt]

theorem average_coord (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i : V) (hi : i ∈ U) :
    average U q (coord i) = (q : ℝ) / U.card := by
  change average U q (fun S => if i ∈ S then 1 else 0) = _
  simpa using average_containment_all U {i} q
    (Finset.singleton_subset_iff.mpr hi) hq

theorem average_coord_mul (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => coord i S * coord j S) =
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
  have hpair : ({i, j} : Finset V).card = 2 := by simp [hne]
  have hCU : ({i, j} : Finset V) ⊆ U := by simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
  have hfun : (fun S => coord i S * coord j S) =
      (fun S : Finset V => if ({i, j} : Finset V) ⊆ S then (1 : ℝ) else 0) := by
    funext S
    by_cases hiS : i ∈ S <;> by_cases hjS : j ∈ S <;> simp [coord, Finset.insert_subset_iff, Finset.singleton_subset_iff, hiS, hjS]
  rw [hfun, average_containment_all U {i, j} q hCU hq, hpair,
    Nat.cast_choose_two, Nat.cast_choose_two]
  exact div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0) _ _

include sectionDecidableEqV in
theorem average_sum {I : Type*} (U : Finset V) (q : ℕ) (s : Finset I)
    (f : I → Finset V → ℝ) :
    average U q (fun S => ∑ i ∈ s, f i S) = ∑ i ∈ s, average U q (f i) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  unfold average
  rw [Finset.sum_comm, Finset.sum_div]

theorem average_linear_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card) (u : V → ℝ) :
    average U q (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      ((q : ℝ) / U.card -
        (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1))) *
        (∑ i ∈ U, (u i)^2) +
      ((q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1))) *
        (∑ i ∈ U, u i)^2 := by
  let p₁ : ℝ := (q : ℝ) / U.card
  let p₂ : ℝ := (q : ℝ) * ((q : ℝ) - 1) /
    ((U.card : ℝ) * ((U.card : ℝ) - 1))
  have hm : ∀ i ∈ U, ∀ j ∈ U,
      average U q (fun S => coord i S * coord j S) = if i = j then p₁ else p₂ := by
    intro i hi j hj
    by_cases hij : i = j
    · subst j
      simpa only [↓reduceIte, ← pow_two, coord_sq] using average_coord U q hq i hi
    · simpa only [ite_eq_right hij] using average_coord_mul U q hq i j hi hj hij
  have hfun : (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      (fun S => ∑ i ∈ U, ∑ j ∈ U, (u i * u j) * (coord i S * coord j S)) := by
    funext S
    rw [pow_two, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun, average_sum]
  simp only [average_sum, average_mul_left]
  have hrearrange : (∑ i ∈ U, ∑ j ∈ U,
      (u i * u j) * average U q (fun S => coord i S * coord j S)) =
      ∑ i ∈ U, ∑ j ∈ U,
        (p₂ * (u i * u j) + if i = j then (p₁ - p₂) * (u i)^2 else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hm i hi j hj]
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte]
      ring
    · simp only [ite_eq_right hij, add_zero]
      ring
  rw [hrearrange]
  have hconstant : (∑ i ∈ U, ∑ j ∈ U, p₂ * (u i * u j)) =
      p₂ * (∑ i ∈ U, u i)^2 := by
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  have hdiag : (∑ i ∈ U, ∑ j ∈ U,
      if i = j then (p₁ - p₂) * (u i)^2 else 0) =
      (p₁ - p₂) * ∑ i ∈ U, (u i)^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [hi]
  simp only [Finset.sum_add_distrib]
  rw [hconstant, hdiag]
  change p₂ * (∑ i ∈ U, u i)^2 + (p₁ - p₂) * (∑ i ∈ U, (u i)^2) =
    (p₁ - p₂) * (∑ i ∈ U, (u i)^2) + p₂ * (∑ i ∈ U, u i)^2
  ring

theorem average_linear_sq_zero_sum (U : Finset V) (q : ℕ)
    (hN : 2 ≤ U.card) (hq : q ≤ U.card) (u : V → ℝ)
    (hu : ∑ i ∈ U, u i = 0) :
    average U q (fun S => (∑ i ∈ U, u i * coord i S)^2) =
      ((q : ℝ) * ((U.card : ℝ) - q) /
        ((U.card : ℝ) * ((U.card : ℝ) - 1))) * (∑ i ∈ U, (u i)^2) := by
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hcoeff : (q : ℝ) / U.card -
      (q : ℝ) * ((q : ℝ) - 1) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) =
      (q : ℝ) * ((U.card : ℝ) - q) / ((U.card : ℝ) * ((U.card : ℝ) - 1)) := by
    field_simp
    ; ring
  rw [average_linear_sq U q hq u, hu, hcoeff]
  simp

include sectionDecidableEqV in
theorem average_congr (U : Finset V) (q : ℕ) (f g : Finset V → ℝ)
    (h : ∀ S ∈ U.powersetCard q, f S = g S) : average U q f = average U q g := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  unfold average
  congr 1
  exact Finset.sum_congr rfl h

theorem equalIndicator_eq (i j : V) (S : Finset V) :
    equalIndicator i j S = 1 - coord i S - coord j S + 2 * (coord i S * coord j S) := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> norm_num [equalIndicator, coord, hi, hj]

theorem average_equalIndicator (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (equalIndicator i j) = equalMean U q := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  have hf : equalIndicator i j =
      (fun S => 1 - coord i S - coord j S + 2 * (coord i S * coord j S)) := by
    funext S
    exact equalIndicator_eq i j S
  rw [hf, average_add, average_sub, average_sub, average_const U q hq 1,
    average_coord U q hq i hi, average_coord U q hq j hj,
    average_mul_left, average_coord_mul U q hq i j hi hj hne]
  unfold equalMean
  field_simp
  ring

theorem average_centeredEqual_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j) :
    average U q (fun S => (centeredEqual U q i j S)^2) =
      equalMean U q * (1 - equalMean U q) := by
  have hf : (fun S => (centeredEqual U q i j S)^2) =
      (fun S => equalIndicator i j S -
        (2 * equalMean U q) * equalIndicator i j S + (equalMean U q)^2) := by
    funext S
    have hs := equalIndicator_sq i j S
    unfold centeredEqual
    nlinarith
  rw [hf, average_add, average_sub, average_mul_left,
    average_equalIndicator U q hq i j hi hj hne, average_const U q hq]
  ring

include sectionDecidableEqV in
theorem average_sq_eq_zero_iff (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f : Finset V → ℝ) :
    average U q (fun S => (f S)^2) = 0 ↔ ∀ S ∈ U.powersetCard q, f S = 0 := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  constructor
  · intro h S hS
    have hsum : (∑ T ∈ U.powersetCard q, (f T)^2) = 0 := by
      exact (div_eq_zero_iff.mp h).resolve_right hden
    have hf := (Finset.sum_eq_zero_iff_of_nonneg
      (fun T _ => sq_nonneg (f T))).mp hsum S hS
    exact sq_eq_zero_iff.mp hf
  · intro h
    unfold average
    have hs : (∑ S ∈ U.powersetCard q, (f S)^2) = 0 := by
      apply Finset.sum_eq_zero
      intro S hS
      rw [h S hS]
      norm_num
    rw [hs, zero_div]

theorem centeredEqual_eq_zero_of_degenerate_mean (U : Finset V) (q : ℕ)
    (hq : q ≤ U.card) (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j)
    (hp : equalMean U q = 0 ∨ equalMean U q = 1) :
    ∀ S ∈ U.powersetCard q, centeredEqual U q i j S = 0 := by
  apply (average_sq_eq_zero_iff U q hq (centeredEqual U q i j)).mp
  rw [average_centeredEqual_sq U q hq i j hi hj hne]
  rcases hp with hp | hp <;> rw [hp] <;> norm_num

theorem centeredEqual_eq_zero_of_boundary (U : Finset V) (q : ℕ)
    (hq : q ≤ U.card) (i j : V) (hi : i ∈ U) (hj : j ∈ U) (hne : i ≠ j)
    (hboundary : q = 0 ∨ q = U.card ∨ U.card ≤ 2) :
    ∀ S ∈ U.powersetCard q, centeredEqual U q i j S = 0 := by
  have hN : 2 ≤ U.card := by
    have hsub : ({i, j} : Finset V) ⊆ U := by
      simp [Finset.insert_subset_iff, Finset.singleton_subset_iff, hi, hj]
    have := Finset.card_le_card hsub
    simpa [hne] using this
  have hNR : (2 : ℝ) ≤ U.card := by exact_mod_cast hN
  have hN0 : (U.card : ℝ) ≠ 0 := by linarith
  have hN1 : (U.card : ℝ) - 1 ≠ 0 := by linarith
  apply centeredEqual_eq_zero_of_degenerate_mean U q hq i j hi hj hne
  rcases hboundary with hzero | hfull | hsmall
  · right
    subst q
    unfold equalMean
    field_simp
    ring
  · right
    subst q
    unfold equalMean
    field_simp
    ring
  · have hcard : U.card = 2 := by omega
    have hq2 : q ≤ 2 := by omega
    interval_cases q <;> norm_num [equalMean, hcard]

include sectionDecidableEqV in
theorem average_eq_fintype_sum (U : Finset V) (q : ℕ) (f : Finset V → ℝ) :
    average U q f = (∑ S : State U q, f S.val) / (Fintype.card (State U q) : ℝ) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [average, State, Finset.sum_attach, Finset.card_powersetCard]

theorem vector_norm_sq (U : Finset V) (q : ℕ) (hq : q ≤ U.card)
    (f : Finset V → ℝ) :
    ‖vector U q f‖^2 = (U.card.choose q : ℝ) * average U q (fun S => (f S)^2) := by
  have hden : (U.card.choose q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  rw [EuclideanSpace.real_norm_sq_eq, average_eq_fintype_sum]
  simp [vector, State, Finset.card_powersetCard]
  field_simp

end Problem315.SliceMoments

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGeneratorEquality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Problem315.SliceEuclideanGenerator

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem equalityVector_apply (q : ℕ) (p : ℝ) (i j : α) (S : State α q) :
    equalityVector q p i j S =
      if i = j then 0 else SliceMoments.equalIndicator i j S.val - p := by
  by_cases hij : i = j
  · simp [equalityVector, sample, SliceEquality.offDiagonal, hij]
  · by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;>
      simp [equalityVector, sample, SliceEquality.offDiagonal, hij,
        SliceEquality.centeredEquality, SliceEquality.equalityIndicator,
        coordinates, SliceMoments.equalIndicator, hi, hj]

theorem additive_equality_image (q : ℕ) (p : ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) =
      (2 * (2 * (q : ℝ) - (Fintype.card α : ℝ))) •
        sample q (fun x => ∑ i, u i * x i) := by
  ext S
  have h := SliceEquality.additive_centeredEquality_image (coordinates S)
    (coordinates_binary S) (q : ℝ) p (coordinates_sum S) u hu
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    equalityVector, sample_apply]
  linarith

theorem rowzero_equality_image (q : ℕ) (p : ℝ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    (∑ i, ∑ j, c i j • equalityVector q p i j) =
      (2 : ℝ) • sample q (fun x => ∑ i, ∑ j, c i j * (x i * x j)) := by
  ext S
  have h := SliceEquality.row_zero_offDiagonal_centeredEquality_image (coordinates S)
    (coordinates_binary S) p c hdiag hrow hcol
  simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul,
    equalityVector, sample_apply]
  linarith

theorem generator_additive_equality (q : ℕ) (p : ℝ) (u : α → ℝ) (hu : ∑ i, u i = 0) :
    generator q (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) =
      ((Fintype.card α : ℝ) / 2) • (∑ i, ∑ j, (u i + u j) • equalityVector q p i j) := by
  rw [additive_equality_image q p u hu, map_smul, generator_sample_linear q u hu]
  simp only [smul_smul]
  congr 1
  ring

theorem generator_rowzero_equality (q : ℕ) (p : ℝ) (c : α → α → ℝ)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, ∑ j, c i j = 0)
    (hcol : ∀ j, ∑ i, c i j = 0) :
    generator q (∑ i, ∑ j, c i j • equalityVector q p i j) =
      ((Fintype.card α : ℝ) - 1) • (∑ i, ∑ j, c i j • equalityVector q p i j) := by
  rw [rowzero_equality_image q p c hdiag hrow hcol, map_smul,
    generator_sample_quadratic q c hdiag hrow hcol]
  simp only [smul_smul]
  congr 1
  ring

end Problem315.SliceEuclideanGenerator

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Problem315.SliceBounds

theorem product_ge_sum_sub_one {q r : ℝ} (hq : 1 ≤ q) (hr : 1 ≤ r) :
    q + r - 1 ≤ q * r := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hr)]

theorem equalityProbability_pos {N q r : ℝ}
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    0 < equalityProbability N q r := by
  unfold equalityProbability
  apply div_pos
  · have hq0 : 0 ≤ q - 1 := sub_nonneg.mpr hq
    have hr0 : 0 ≤ r - 1 := sub_nonneg.mpr hr
    have hqprod := mul_nonneg hq0 hq0
    have hrprod := mul_nonneg hr0 hr0
    nlinarith
  · exact mul_pos (by linarith) (by linarith)

theorem linear_numerator_identity {N q r : ℝ}
    (hN : 1 < N) (hsum : q + r = N) :
    N * (N - 2) * equalityProbability N q r - (2 * q - N) ^ 2 =
      2 * N / (N - 1) * (q * r - (N - 1)) := by
  have hN0 : N ≠ 0 := ne_of_gt (lt_trans (by norm_num) hN)
  have hN1 : N - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hN)
  unfold equalityProbability
  rw [← hsum] at *
  field_simp
  ring

theorem linear_eigenvalue_le {N q r : ℝ}
    (hN : 3 ≤ N) (hq : 1 ≤ q) (hr : 1 ≤ r) (hsum : q + r = N) :
    (2 * q - N) ^ 2 / (2 * (N - 2) * equalityProbability N q r) ≤ N / 2 := by
  have hp := equalityProbability_pos hN hq hr hsum
  have hden : 0 < 2 * (N - 2) * equalityProbability N q r :=
    mul_pos (mul_pos (by norm_num) (by linarith)) hp
  apply (div_le_iff₀ hden).2
  have hid := linear_numerator_identity (by linarith : 1 < N) hsum
  have hqr : 0 ≤ q * r - (N - 1) := by
    have := product_ge_sum_sub_one hq hr
    linarith
  have hquot : 0 ≤ 2 * N / (N - 1) :=
    div_nonneg (by linarith) (by linarith)
  have hnonneg := mul_nonneg hquot hqr
  nlinarith

end Problem315.SliceBounds

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceCoefficientAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [sectionFintypeV : Fintype V] [DecidableEq V]

theorem sum_outside (f : V → ℝ) {i j : V} (hij : i ≠ j) :
    (∑ k ∈ outside i j, f k) = (∑ k, f k) - f i - f j := by
  have hi := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
  have hj := Finset.sum_erase_add (Finset.univ.erase i) f
    (by simp [Ne.symm hij] : j ∈ Finset.univ.erase i)
  unfold outside
  linarith

theorem linearPair_rowSum (u : V → ℝ) (hu : ∑ i, u i = 0) (i : V) :
    rowSum (linearPair u) i = ((Fintype.card V : ℝ) - 2) * u i := by
  have heq (j : V) : linearPair u i j =
      (u i + u j) - (if i = j then 2 * u i else 0) := by
    by_cases hij : i = j <;> simp [linearPair, hij] ; ring
  simp only [rowSum, heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hu,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem meetingSum_eq (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    meetingSum c i j = rowSum c i + rowSum c j - 2 * c i j := by
  unfold meetingSum
  rw [Finset.sum_add_distrib, sum_outside _ hij, sum_outside _ hij]
  simp only [hdiag, hsym j i, rowSum]
  ring

theorem double_outside_eq (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) =
      (∑ k, rowSum c k) - 2 * rowSum c i - 2 * rowSum c j + 2 * c i j := by
  simp_rw [sum_outside (fun l => c _ l) hij]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    sum_outside _ hij, sum_outside _ hij, sum_outside _ hij]
  have hci : (∑ k, c k i) = rowSum c i := by
    unfold rowSum
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym k i
  have hcj : (∑ k, c k j) = rowSum c j := by
    unfold rowSum
    apply Finset.sum_congr rfl
    intro k hk
    exact hsym k j
  simp only [hdiag, hsym j i, hci, hcj]
  change (∑ k, rowSum c k) - rowSum c i - rowSum c j -
    (rowSum c i - 0 - c i j) - (rowSum c j - c i j - 0) = _
  ring

include sectionFintypeV in
theorem linearPair_symmetric (u : V → ℝ) (i j : V) :
    linearPair u i j = linearPair u j i := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [linearPair, eq_comm, add_comm]

theorem linearPair_total (u : V → ℝ) (hu : ∑ i, u i = 0) :
    ∑ i, rowSum (linearPair u) i = 0 := by
  simp_rw [linearPair_rowSum u hu, ← Finset.mul_sum, hu, mul_zero]

theorem linearPair_meetingSum (u : V → ℝ) (hu : ∑ i, u i = 0)
    {i j : V} (hij : i ≠ j) :
    meetingSum (linearPair u) i j =
      ((Fintype.card V : ℝ) - 4) * linearPair u i j := by
  rw [meetingSum_eq _ (linearPair_symmetric u) (linearPair_diag u) hij]
  simp only [linearPair_rowSum u hu, linearPair, hij, ite_false]
  ring

theorem linearPair_disjointSum (u : V → ℝ) (hu : ∑ i, u i = 0)
    {i j : V} (hij : i ≠ j) :
    disjointSum (linearPair u) i j =
      -((Fintype.card V : ℝ) - 3) * linearPair u i j := by
  unfold disjointSum
  rw [double_outside_eq _ (linearPair_symmetric u) (linearPair_diag u) hij,
    linearPair_total u hu]
  simp only [linearPair_rowSum u hu, linearPair, hij, ite_false]
  ring

theorem rowZero_meetingSum (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j) :
    meetingSum c i j = -2 * c i j := by
  rw [meetingSum_eq c hsym hdiag hij, hrow, hrow]
  ring

theorem rowZero_disjointSum (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) {i j : V} (hij : i ≠ j) :
    disjointSum c i j = c i j := by
  unfold disjointSum
  rw [double_outside_eq c hsym hdiag hij]
  simp [hrow]

theorem linearPair_orthogonal_rowZero (u : V → ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) :
    (∑ i, ∑ j, linearPair u i j * c i j) = 0 := by
  have heq (i j : V) : linearPair u i j * c i j =
      u i * c i j + u j * c i j := by
    by_cases hij : i = j
    · subst j
      simp [hdiag]
    · simp only [linearPair, hij, ite_false]
      ring
  simp_rw [heq, Finset.sum_add_distrib]
  have hfirst : (∑ i, ∑ j, u i * c i j) = 0 := by
    simp_rw [← Finset.mul_sum]
    change (∑ i, u i * rowSum c i) = 0
    simp [hrow]
  have hsecond : (∑ i, ∑ j, u j * c i j) = 0 := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    have hcol (j : V) : (∑ i, c i j) = 0 := by
      calc
        (∑ i, c i j) = rowSum c j := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsym i j
        _ = 0 := hrow j
    simp [hcol]
  rw [hfirst, hsecond, add_zero]

theorem linearPair_row_sq (u : V → ℝ) (hu : ∑ i, u i = 0) (i : V) :
    (∑ j, linearPair u i j ^ 2) =
      ((Fintype.card V : ℝ) - 4) * u i ^ 2 + ∑ j, u j ^ 2 := by
  have heq (j : V) : linearPair u i j ^ 2 =
      (u i ^ 2 + 2 * u i * u j + u j ^ 2) -
        (if i = j then 4 * u i ^ 2 else 0) := by
    by_cases hij : i = j <;> simp [linearPair, hij] <;> ring
  simp only [heq, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, hu, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  ring

theorem linearPair_norm_sq (u : V → ℝ) (hu : ∑ i, u i = 0) :
    (∑ i, ∑ j, linearPair u i j ^ 2) / 2 =
      ((Fintype.card V : ℝ) - 2) * ∑ i, u i ^ 2 := by
  simp only [linearPair_row_sq u hu, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

include sectionFintypeV in
theorem constantPair_symmetric (a : ℝ) (i j : V) :
    constantPair a i j = constantPair a j i := by
  have retainedsectionFintypeV := sectionFintypeV
  simp [constantPair, eq_comm]

theorem constantPair_rowSum (a : ℝ) (i : V) :
    rowSum (constantPair a) i = ((Fintype.card V : ℝ) - 1) * a := by
  have heq (j : V) : constantPair a i j = a - (if i = j then a else 0) := by
    by_cases h : i = j <;> simp [constantPair, h]
  simp only [rowSum, heq, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  ring

theorem exists_coefficient_decomposition (hcard : 3 ≤ Fintype.card V)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    ∃ a : ℝ, ∃ u : V → ℝ, ∃ z : V → V → ℝ,
      (∑ i, u i) = 0 ∧ (∀ i, rowSum z i = 0) ∧
      (∀ i j, z i j = z j i) ∧ (∀ i, z i i = 0) ∧
      (∀ i j, c i j = constantPair a i j + linearPair u i j + z i j) := by
  let N : ℝ := Fintype.card V
  let C : ℝ := ∑ i, rowSum c i
  let a : ℝ := C / (N * (N - 1))
  let u : V → ℝ := fun i => (rowSum c i - C / N) / (N - 2)
  let z : V → V → ℝ := fun i j => c i j - constantPair a i j - linearPair u i j
  have hN3 : 3 ≤ N := by
    dsimp [N]
    exact_mod_cast hcard
  have hN : N ≠ 0 := by linarith
  have hN1 : N - 1 ≠ 0 := by linarith
  have hN2 : N - 2 ≠ 0 := by linarith
  have hu : (∑ i, u i) = 0 := by
    simp only [u, ← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    change (C - N * C / N) / (N - 2) = 0
    field_simp
    ring
  have hzrow (i : V) : rowSum z i = 0 := by
    change (∑ j, (c i j - constantPair a i j - linearPair u i j)) = 0
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    change rowSum c i - rowSum (constantPair a) i - rowSum (linearPair u) i = 0
    rw [constantPair_rowSum, linearPair_rowSum u hu]
    change rowSum c i - (N - 1) * (C / (N * (N - 1))) -
      (N - 2) * ((rowSum c i - C / N) / (N - 2)) = 0
    field_simp
    ring
  refine ⟨a, u, z, hu, hzrow, ?_, ?_, ?_⟩
  · intro i j
    simp only [z, hsym i j, constantPair_symmetric a i j, linearPair_symmetric u i j]
  · intro i
    simp [z, hdiag]
  · intro i j
    dsimp [z]
    ring

theorem intersectionAction_linearPair (a b d : ℝ) (u : V → ℝ)
    (hu : ∑ i, u i = 0) (i j : V) :
    intersectionAction a b d (linearPair u) i j =
      (a + ((Fintype.card V : ℝ) - 4) * b -
        ((Fintype.card V : ℝ) - 3) * d) * linearPair u i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction]
  · simp only [intersectionAction, hij, ite_false,
      linearPair_meetingSum u hu hij, linearPair_disjointSum u hu hij]
    ring

theorem intersectionAction_rowZero (a b d : ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    (hrow : ∀ i, rowSum c i = 0) (i j : V) :
    intersectionAction a b d c i j = (a - 2 * b + d) * c i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction, hdiag]
  · simp only [intersectionAction, hij, ite_false,
      rowZero_meetingSum c hsym hdiag hrow hij,
      rowZero_disjointSum c hsym hdiag hrow hij]
    ring

end Problem315.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceImageNorm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceImageNorm

variable {α : Type*} [Fintype α] [sectionDecidableEqα : DecidableEq α]

theorem coord_sum (S : Finset α) :
    (∑ i, SliceMoments.coord i S) = (S.card : ℝ) := by
  simp [SliceMoments.coord]

theorem centeredEquality_coord (q : ℕ) (S : Finset α) (i j : α) :
    SliceEquality.centeredEquality (fun k => SliceMoments.coord k S)
      (SliceMoments.equalMean (Finset.univ : Finset α) q) i j =
      SliceMoments.centeredEqual Finset.univ q i j S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [SliceEquality.centeredEquality, SliceEquality.equalityIndicator,
      SliceMoments.centeredEqual, SliceMoments.equalIndicator, SliceMoments.coord, hi, hj]

theorem equalityImage_linearPair (q : ℕ) (S : Finset α) (hS : S.card = q)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    equalityImage q (SliceCoefficients.linearPair u) S =
      (2 * (q : ℝ) - (Fintype.card α : ℝ)) * ∑ i, u i * SliceMoments.coord i S := by
  have hb (i : α) : SliceMoments.coord i S = 0 ∨ SliceMoments.coord i S = 1 := by
    by_cases hi : i ∈ S <;> simp [SliceMoments.coord, hi]
  have hs : (∑ i, SliceMoments.coord i S) = (q : ℝ) := by rw [coord_sum, hS]
  have h := SliceEquality.additive_centeredEquality_image
    (fun i => SliceMoments.coord i S) hb q (SliceMoments.equalMean (Finset.univ : Finset α) q) hs u hu
  have ht (i j : α) :
      (u i + u j) * SliceEquality.offDiagonal
        (SliceEquality.centeredEquality (fun k => SliceMoments.coord k S)
          (SliceMoments.equalMean (Finset.univ : Finset α) q)) i j =
      SliceCoefficients.linearPair u i j * SliceMoments.centeredEqual Finset.univ q i j S := by
    by_cases hij : i = j
    · subst j
      simp [SliceEquality.offDiagonal, SliceCoefficients.linearPair]
    · simp [SliceEquality.offDiagonal, SliceCoefficients.linearPair, hij, centeredEquality_coord]
  simpa only [ht, equalityImage] using h

theorem average_equalityImage_linearPair_sq
    (hN : 2 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) =
      (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 *
        ((q : ℝ) * ((Fintype.card α : ℝ) - q) /
          ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1))) * (∑ i, (u i)^2) := by
  calc
    _ = SliceMoments.average Finset.univ q (fun S =>
        (2 * (q : ℝ) - (Fintype.card α : ℝ))^2 *
          (∑ i, u i * SliceMoments.coord i S)^2) := by
      apply SliceMoments.average_congr
      intro S hS
      rw [equalityImage_linearPair q S (Finset.mem_powersetCard.mp hS).2 u hu]
      ring
    _ = _ := by
      rw [SliceMoments.average_mul_left]
      have hm := SliceMoments.average_linear_sq_zero_sum
        (Finset.univ : Finset α) q (by simpa using hN) (by simpa using hq) u (by simpa using hu)
      simp only [Finset.card_univ] at hm
      rw [hm]
      ring

include sectionDecidableEqα in
theorem equalMean_complement (hN : 2 ≤ Fintype.card α) (q : ℕ) :
    1 - SliceMoments.equalMean (Finset.univ : Finset α) q =
      2 * (q : ℝ) * ((Fintype.card α : ℝ) - q) /
        ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hc : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  unfold SliceMoments.equalMean
  simp only [Finset.card_univ]
  field_simp
  ring

theorem average_equalityImage_linearPair_sq_ratio
    (hN : 3 ≤ Fintype.card α) (q : ℕ) (hq : q ≤ Fintype.card α)
    (hp : SliceMoments.equalMean (Finset.univ : Finset α) q ≠ 0)
    (u : α → ℝ) (hu : ∑ i, u i = 0) :
    SliceMoments.average Finset.univ q
      (fun S => (equalityImage q (SliceCoefficients.linearPair u) S)^2) =
      linearGramScalar (α := α) q *
        (SliceMoments.equalMean (Finset.univ : Finset α) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset α) q)) *
        ((∑ i, ∑ j, (SliceCoefficients.linearPair u i j)^2) / 2) := by
  have hc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have h0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card α : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (Fintype.card α : ℝ) - 2 ≠ 0 := by linarith
  have hN' : 2 ≤ Fintype.card α := by omega
  rw [average_equalityImage_linearPair_sq hN' q hq u hu,
    SliceCoefficients.linearPair_norm_sq u hu, equalMean_complement hN' q]
  unfold linearGramScalar
  field_simp

include sectionDecidableEqα in
theorem equalMean_pos (hN : 3 ≤ Fintype.card α) (q : ℕ) :
    0 < SliceMoments.equalMean (Finset.univ : Finset α) q := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hN3 : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < Fintype.card α := by linarith
  have hN1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (Fintype.card α : ℝ) - 2 := by linarith
  have hnprod := mul_pos hN0 hN2
  unfold SliceMoments.equalMean
  simp only [Finset.card_univ]
  apply div_pos _ (mul_pos hN0 hN1)
  nlinarith [sq_nonneg ((q : ℝ) - ((Fintype.card α : ℝ) - q))]

theorem equalMean_lt_one (hN : 2 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α) :
    SliceMoments.equalMean (Finset.univ : Finset α) q < 1 := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hqcard : (q : ℝ) < Fintype.card α := by exact_mod_cast hqN
  have hN2 : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hdiff : 0 < 1 - SliceMoments.equalMean (Finset.univ : Finset α) q := by
    rw [equalMean_complement hN q]
    apply div_pos
    · exact mul_pos (mul_pos (by norm_num) hqpos) (sub_pos.mpr hqcard)
    · exact mul_pos (by linarith) (by linarith)
  linarith

include sectionDecidableEqα in
theorem linearGramScalar_le
    (hN : 3 ≤ Fintype.card α) (q : ℕ)
    (hq0 : 0 < q) (hqN : q < Fintype.card α) :
    linearGramScalar (α := α) q ≤ (Fintype.card α : ℝ) / 2 := by
  have retainedsectionDecidableEqα := sectionDecidableEqα
  have hNc : (3 : ℝ) ≤ Fintype.card α := by exact_mod_cast hN
  have hqc : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hqnext : q + 1 ≤ Fintype.card α := by omega
  have hqnextc : (q : ℝ) + 1 ≤ Fintype.card α := by exact_mod_cast hqnext
  have hr : (1 : ℝ) ≤ (Fintype.card α : ℝ) - q := by linarith
  have h := SliceBounds.linear_eigenvalue_le hNc hqc hr
    (by ring : (q : ℝ) + ((Fintype.card α : ℝ) - q) = Fintype.card α)
  simpa only [linearGramScalar, SliceBounds.equalityProbability, SliceMoments.equalMean,
    Finset.card_univ] using h

end Problem315.SliceImageNorm

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceNormalizedFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]

theorem raw_symmetric (q : ℕ) (i j : V) : raw q i j = raw q j i := by
  ext S
  simp [raw, SliceMoments.centeredEqual, SliceMoments.equalIndicator, eq_comm, iff_comm]

theorem column_symmetric (q : ℕ) (i j : V) : column q i j = column q j i := by
  rw [column, column, raw_symmetric q i j]

theorem coord_sum (q : ℕ) (S : State V q) :
    ∑ i, SliceMoments.coord i S.val = (q : ℝ) := by
  have hcard := (Finset.mem_powersetCard.mp S.property).2
  simp [SliceMoments.coord, ← hcard]

theorem centered_eq_binary (q : ℕ) (S : State V q) (i j : V) :
    SliceEquality.centeredEquality (fun k => SliceMoments.coord k S.val)
      (SliceMoments.equalMean (Finset.univ : Finset V) q) i j =
    SliceMoments.centeredEqual Finset.univ q i j S.val := by
  unfold SliceEquality.centeredEquality SliceEquality.equalityIndicator
    SliceMoments.centeredEqual SliceMoments.equalIndicator SliceMoments.coord
  by_cases hi : i ∈ S.val <;> by_cases hj : j ∈ S.val <;> simp [hi, hj]

theorem raw_total (q : ℕ) (hN : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, raw q i j : Space V q) = 0 := by
  ext S
  have hb (i : V) : SliceMoments.coord i S.val = 0 ∨
      SliceMoments.coord i S.val = 1 := by
    by_cases hi : i ∈ S.val <;> simp [SliceMoments.coord, hi]
  have ht := SliceEquality.centeredEquality_total_zero hN
    (fun i => SliceMoments.coord i S.val) hb (q : ℝ) (coord_sum q S)
  have hp : SliceMoments.equalMean (Finset.univ : Finset V) q =
      ((q : ℝ) * (q - 1) + ((Fintype.card V : ℝ) - q) *
        ((Fintype.card V : ℝ) - q - 1)) /
        ((Fintype.card V : ℝ) * ((Fintype.card V : ℝ) - 1)) := by
    simp [SliceMoments.equalMean]
  rw [← hp] at ht
  simp_rw [SliceEquality.offDiagonal, centered_eq_binary q S] at ht
  simpa [raw, SliceEquality.offDiagonal] using ht

theorem column_total (q : ℕ) (hN : 2 ≤ Fintype.card V) :
    (∑ i, ∑ j, column q i j : Space V q) = 0 := by
  simp only [column, ← Finset.smul_sum, raw_total q hN, smul_zero]

theorem raw_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪raw q i j, raw q k l⟫ = (Nat.choose (Fintype.card V) q : ℝ) *
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) := by
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  simp only [raw, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    star_trivial, hij, hkl, ite_false]
  change (∑ S : ↥((Finset.univ : Finset V).powersetCard q),
    SliceMoments.centeredEqual Finset.univ q k l S.val *
    SliceMoments.centeredEqual Finset.univ q i j S.val) = _
  rw [Finset.sum_coe_sort ((Finset.univ : Finset V).powersetCard q)
    (fun S => SliceMoments.centeredEqual Finset.univ q k l S *
      SliceMoments.centeredEqual Finset.univ q i j S)]
  simp only [SliceMoments.average, Finset.card_univ]
  field_simp
  simp only [mul_comm]

include sectionDecidableEqV in
theorem denominator_sq (q : ℕ)
    (hp : 0 ≤ SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q ≤ 1) :
    denominator V q ^ 2 = 2 * (Nat.choose (Fintype.card V) q : ℝ) *
      SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  apply Real.sq_sqrt
  exact mul_nonneg (mul_nonneg (by positivity) hp) (sub_nonneg.mpr hp1)

theorem column_inner_unsimplified (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪column q i j, column q k l⟫ =
      ((Nat.choose (Fintype.card V) q : ℝ) / denominator V q ^ 2) *
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) := by
  rw [column, column, inner_smul_left, inner_smul_right,
    raw_inner q hq i j k l hij hkl]
  simp only [RCLike.conj_to_real]
  ring

theorem column_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    ⟪column q i j, column q k l⟫ =
      SliceMoments.average Finset.univ q (fun S =>
        SliceMoments.centeredEqual Finset.univ q i j S *
        SliceMoments.centeredEqual Finset.univ q k l S) /
      (2 * SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [column_inner_unsimplified q hq i j k l hij hkl,
    denominator_sq q hp.le hp1.le]
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hq).ne'
  have hpc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by
    linarith
  field_simp

theorem column_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j : V) (hij : i ≠ j) : ‖column q i j‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, column_inner q hq hp hp1 i j i j hij hij]
  simp_rw [← pow_two]
  rw [SliceMoments.average_centeredEqual_sq Finset.univ q
    (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij]
  have hpc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by
    linarith
  field_simp

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem symMatrix_symmetric (c : Coeff V) (i j : V) :
    symMatrix c i j = symMatrix c j i := by simp [symMatrix, eq_comm, add_comm]

theorem synthesis_symMatrix (z : V → V → E)
    (hzsym : ∀ i j, z i j = z j i) (hzdiag : ∀ i, z i i = 0)
    (c : Coeff V) : synthesis z (ofMatrix (symMatrix c)) = synthesis z c := by
  have hterm (i j : V) : symMatrix c i j • z i j =
      (1 / 2 : ℝ) • (c (i,j) • z i j + c (j,i) • z i j) := by
    by_cases hij : i = j
    · subst j; simp [hzdiag]
    · simp only [symMatrix, hij, ite_false, ← add_smul, ← mul_smul]
      congr 1
      ring
  have htranspose : (∑ i, ∑ j, c (j,i) • z i j) = ∑ i, ∑ j, c (i,j) • z i j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hzsym]
  rw [synthesis_ofMatrix]
  simp_rw [hterm, ← Finset.smul_sum, Finset.sum_add_distrib]
  rw [htranspose, smul_add, ← add_smul]
  norm_num
  rfl

theorem synthesis_constant (z : V → V → E)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (a : ℝ) : synthesis z (ofMatrix (constantPair a)) = 0 := by
  have hterm (i j : V) : constantPair a i j • z i j = a • z i j := by
    by_cases hij : i = j
    · subst j; simp [hzdiag]
    · simp [constantPair, hij]
  rw [synthesis_ofMatrix]
  simp_rw [hterm, ← Finset.smul_sum]
  rw [hztotal, smul_zero]

include sectionDecidableEqV in
theorem ofMatrix_inner (c d : V → V → ℝ) :
    ⟪ofMatrix c, ofMatrix d⟫ = ∑ i, ∑ j, c i j * d i j := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fintype.sum_prod_type, ofMatrix, mul_comm]

theorem exists_synthesis_decomposition (hcard : 3 ≤ Fintype.card V)
    (z : V → V → E) (hzsym : ∀ i j, z i j = z j i)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (c : Coeff V) :
    ∃ u : V → ℝ, ∃ v : V → V → ℝ,
      (∑ i, u i) = 0 ∧ (∀ i, rowSum v i = 0) ∧
      (∀ i j, v i j = v j i) ∧ (∀ i, v i i = 0) ∧
      synthesis z c = synthesis z (ofMatrix (linearPair u)) + synthesis z (ofMatrix v) ∧
      ⟪ofMatrix (linearPair u), ofMatrix v⟫ = 0 := by
  obtain ⟨a,u,v,hu,hvrow,hvsym,hvdiag,hdecomp⟩ :=
    exists_coefficient_decomposition hcard (symMatrix c)
      (symMatrix_symmetric c) (symMatrix_diag c)
  refine ⟨u,v,hu,hvrow,hvsym,hvdiag,?_,?_⟩
  · rw [← synthesis_symMatrix z hzsym hzdiag c]
    have heq : ofMatrix (symMatrix c) =
        ofMatrix (constantPair a) + ofMatrix (linearPair u) + ofMatrix v := by
      ext p
      exact hdecomp p.1 p.2
    rw [heq, map_add, map_add, synthesis_constant z hzdiag hztotal, zero_add]
  · rw [ofMatrix_inner]
    exact linearPair_orthogonal_rowZero u v hvsym hvdiag hvrow

variable [sectionFiniteDimensionalℝE : FiniteDimensional ℝ E]

include sectionFiniteDimensionalℝE in
theorem synthesis_single (z : V → V → E) (i j : V) :
    synthesis z (EuclideanSpace.single (i,j) 1) = z i j := by
  have retainedsectionFiniteDimensionalℝE := sectionFiniteDimensionalℝE
  simp [synthesis, ite_and]

theorem adjoint_synthesis_apply (z : V → V → E) (x : E) (i j : V) :
    LinearMap.adjoint (synthesis z) x (i,j) = ⟪z i j,x⟫ := by
  have h := (synthesis z).adjoint_inner_right (EuclideanSpace.single (i,j) 1) x
  simpa [synthesis_single, EuclideanSpace.inner_single_left] using h

theorem gram_synthesis_apply (z : V → V → E) (c : Coeff V) (i j : V) :
    LinearMap.adjoint (synthesis z) (synthesis z c) (i,j) =
      ∑ k, ∑ l, c (k,l) * ⟪z i j,z k l⟫ := by
  rw [adjoint_synthesis_apply]
  simp [synthesis, inner_sum, inner_smul_right]

end Problem315.SliceSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceActualSynthesis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem raw_eq_equalityVector (q : ℕ) (i j : V) :
    raw q i j = SliceEuclideanGenerator.equalityVector q
      (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  ext S
  rw [SliceEuclideanGenerator.equalityVector_apply]
  rfl

 theorem synthesis_column (q : ℕ) (c : V → V → ℝ) :
    synthesis (column q) (ofMatrix c) = (denominator V q)⁻¹ •
      ∑ i, ∑ j, c i j • SliceEuclideanGenerator.equalityVector q
        (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  simp only [synthesis_ofMatrix, column, raw_eq_equalityVector,
    Finset.smul_sum, smul_smul]
  simp only [mul_comm]

 theorem synthesis_linearPair_column (q : ℕ) (u : V → ℝ) :
    synthesis (column q) (ofMatrix (linearPair u)) = (denominator V q)⁻¹ •
      ∑ i, ∑ j, (u i + u j) • SliceEuclideanGenerator.equalityVector q
        (SliceMoments.equalMean (Finset.univ : Finset V) q) i j := by
  rw [synthesis_column]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i = j
  · subst j
    rw [← raw_eq_equalityVector, raw_diag]
    simp
  · simp [linearPair, hij]

 theorem generator_synthesis_linear (q : ℕ) (u : V → ℝ) (hu : ∑ i, u i = 0) :
    SliceEuclideanGenerator.generator q (synthesis (column q) (ofMatrix (linearPair u))) =
      ((Fintype.card V : ℝ) / 2) • synthesis (column q) (ofMatrix (linearPair u)) := by
  rw [synthesis_linearPair_column, map_smul,
    SliceEuclideanGenerator.generator_additive_equality q _ u hu, smul_smul,
    smul_smul]
  congr 1
  ring

 theorem generator_synthesis_rowZero (q : ℕ) (c : V → V → ℝ)
    (hrow : ∀ i, rowSum c i = 0) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    SliceEuclideanGenerator.generator q (synthesis (column q) (ofMatrix c)) =
      ((Fintype.card V : ℝ) - 1) • synthesis (column q) (ofMatrix c) := by
  have hcol : ∀ j, ∑ i, c i j = 0 := by
    intro j
    simpa only [rowSum, hsym] using hrow j
  rw [synthesis_column, map_smul,
    SliceEuclideanGenerator.generator_rowzero_equality q _ c hdiag hrow hcol,
    smul_smul, smul_smul]
  congr 1
  ring

 theorem synthesis_column_eq_vector (q : ℕ) (c : V → V → ℝ)
    (hdiag : ∀ i, c i i = 0) :
    synthesis (column q) (ofMatrix c) = (2 / denominator V q) •
      SliceMoments.vector Finset.univ q (SliceImageNorm.equalityImage q c) := by
  ext S
  simp only [synthesis_ofMatrix, WithLp.ofLp_sum, Finset.sum_apply,
    PiLp.smul_apply, smul_eq_mul, column, raw, 
    SliceMoments.vector, SliceImageNorm.equalityImage]
  have hterm (i j : V) : c i j * ((denominator V q)⁻¹ *
      (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val)) =
      (denominator V q)⁻¹ *
        (c i j * SliceMoments.centeredEqual Finset.univ q i j S.val) := by
    by_cases hij : i = j
    · subst j; simp [hdiag]
    · simp only [hij, ite_false]; ring
  simp_rw [hterm, ← Finset.mul_sum]
  ring

 theorem synthesis_linear_norm_sq (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V)
    (u : V → ℝ) (hu : ∑ i, u i = 0) :
    ‖synthesis (column q) (ofMatrix (linearPair u))‖ ^ 2 =
      SliceImageNorm.linearGramScalar (α := V) q * ‖ofMatrix (linearPair u)‖ ^ 2 := by
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  have hd := denominator_sq (V := V) q hp.le hp1.le
  have hdenpos : 0 < denominator V q := by
    apply Real.sqrt_pos.2
    have hc : (0 : ℝ) < Nat.choose (Fintype.card V) q := by
      exact_mod_cast Nat.choose_pos hqN.le
    exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hp) (sub_pos.mpr hp1)
  have hcoeff : ‖ofMatrix (linearPair u)‖ ^ 2 =
      ∑ i, ∑ j, (linearPair u i j)^2 := by
    rw [← real_inner_self_eq_norm_sq, ofMatrix_inner]
    simp only [pow_two]
  rw [synthesis_column_eq_vector q _ (linearPair_diag u), norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, SliceMoments.vector_norm_sq _ q
      (by simpa using hqN.le), Finset.card_univ,
    SliceImageNorm.average_equalityImage_linearPair_sq_ratio hN q hqN.le hp.ne' u hu,
    hcoeff, div_pow, hd]
  have hc : (Nat.choose (Fintype.card V) q : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hqN.le).ne'
  have hp0 := hp.ne'
  have hp10 : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by linarith
  field_simp

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceFrameProjection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis

variable {V E : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

include sectionDecidableEqV in
theorem synthesis_eq_frame (z : V → V → E) :
    synthesis z = FrameSynthesis.synthesis (fun p : V × V => z p.1 p.2) := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  apply LinearMap.ext
  intro c
  simp [synthesis, FrameSynthesis.synthesis, Fintype.sum_prod_type]

end Problem315.SliceSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_two_and_outside (f : V → ℝ) {i j : V} (hij : i ≠ j) :
    (∑ k, f k) = f i + f j + ∑ k ∈ outside i j, f k := by
  have h := sum_outside f hij
  linarith

theorem half_sum_orbitKernel (a b d : ℝ) (c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j) :
    (∑ k, ∑ l, orbitKernel a b d i j k l * c k l) / 2 =
      intersectionAction a b d c i j := by
  have hji : j ≠ i := Ne.symm hij
  have hout (k : V) (hk : k ∈ outside i j) : k ≠ i ∧ k ≠ j := by
    simpa [outside, and_comm] using hk
  have hfirst : (∑ l, orbitKernel a b d i j i l * c i l) =
      a * c i j + b * ∑ l ∈ outside i j, c i l := by
    rw [sum_two_and_outside _ hij]
    have hrest : (∑ l ∈ outside i j, orbitKernel a b d i j i l * c i l) =
        b * ∑ l ∈ outside i j, c i l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hij, hli, hlj]
    rw [hrest]
    simp [orbitKernel, hij, hji, hdiag]
  have hsecond : (∑ l, orbitKernel a b d i j j l * c j l) =
      a * c i j + b * ∑ l ∈ outside i j, c j l := by
    rw [sum_two_and_outside _ hij]
    have hrest : (∑ l ∈ outside i j, orbitKernel a b d i j j l * c j l) =
        b * ∑ l ∈ outside i j, c j l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hji, hli, hlj]
    rw [hrest]
    simp [orbitKernel, hij, hji, hdiag, hsym j i]
  have hrest (k : V) (hk : k ∈ outside i j) :
      (∑ l, orbitKernel a b d i j k l * c k l) =
        b * (c i k + c j k) + d * ∑ l ∈ outside i j, c k l := by
    obtain ⟨hki, hkj⟩ := hout k hk
    rw [sum_two_and_outside _ hij]
    have hinner : (∑ l ∈ outside i j, orbitKernel a b d i j k l * c k l) =
        d * ∑ l ∈ outside i j, c k l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l hl
      obtain ⟨hli, hlj⟩ := hout l hl
      simp [orbitKernel, hki, hkj, hli, hlj]
    rw [hinner]
    simp only [orbitKernel, hki, hkj, false_and, or_false,
      and_false, hij, hji, ite_false, or_true, ite_true,
      hsym k i, hsym k j]
    ring
  rw [sum_two_and_outside _ hij, hfirst, hsecond]
  have houter : (∑ k ∈ outside i j, ∑ l, orbitKernel a b d i j k l * c k l) =
      b * meetingSum c i j + 2 * d * disjointSum c i j := by
    rw [Finset.sum_congr rfl hrest]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, meetingSum, disjointSum]
    ring
  rw [houter]
  simp only [intersectionAction, hij, ite_false, meetingSum, Finset.sum_add_distrib]
  ring

omit [Fintype V] in

theorem orbitKernel_eq_intersection_card (a b d : ℝ) (i j k l : V)
    (hij : i ≠ j) (hkl : k ≠ l) :
    orbitKernel a b d i j k l =
      if (({i, j} : Finset V) ∩ {k, l}).card = 2 then a
      else if (({i, j} : Finset V) ∩ {k, l}).card = 1 then b else d := by
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    by_cases hli : l = i <;> by_cases hlj : l = j <;>
    simp_all [orbitKernel, Finset.inter_insert, eq_comm]

theorem half_sum_kernel_eq_intersectionAction (a b d : ℝ) (K c : V → V → ℝ)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0)
    {i j : V} (hij : i ≠ j)
    (hK : ∀ k l, k ≠ l → K k l = orbitKernel a b d i j k l) :
    (∑ k, ∑ l, K k l * c k l) / 2 = intersectionAction a b d c i j := by
  rw [← half_sum_orbitKernel a b d c hsym hdiag hij]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  by_cases hkl : k = l
  · subst l; simp [hdiag]
  · rw [hK k l hkl]

end Problem315.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramScalars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Problem315.SliceGram

theorem eigenvalue_relation (N b d mu₁ mu₂ : ℝ)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) :
    N * (N - 3) * mu₂ = (N - 1) * (N - 2 * mu₁) := by
  rw [hmu₁, hmu₂]
  nlinarith [hconstant]

theorem degree_two_eigenvalue_le (N b d mu₁ mu₂ : ℝ) (hN : 4 ≤ N)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) (hpos : 0 ≤ mu₁) :
    mu₂ ≤ (N - 1) / (N - 3) := by
  have hrel := eigenvalue_relation N b d mu₁ mu₂ hconstant hmu₁ hmu₂
  have hfactor : 0 < N * (N - 3) := mul_pos (by linarith) (by linarith)
  apply (mul_le_mul_iff_right₀ hfactor).mp
  have hden : N - 3 ≠ 0 := by linarith
  calc
    N * (N - 3) * mu₂ = (N - 1) * (N - 2 * mu₁) := hrel
    _ ≤ (N - 1) * N := by nlinarith
    _ = N * (N - 3) * ((N - 1) / (N - 3)) := by field_simp

theorem degree_two_eigenvalue_le_johnson (N b d mu₁ mu₂ : ℝ) (hN : 4 ≤ N)
    (hconstant : 1 + 2 * (N - 2) * b + ((N - 2) * (N - 3) / 2) * d = 0)
    (hmu₁ : mu₁ = 1 + (N - 4) * b - (N - 3) * d)
    (hmu₂ : mu₂ = 1 - 2 * b + d) (hpos : 0 ≤ mu₁) :
    mu₂ ≤ N - 1 := by
  apply (degree_two_eigenvalue_le N b d mu₁ mu₂ hN hconstant hmu₁ hmu₂ hpos).trans
  apply (div_le_iff₀ (by linarith : 0 < N - 3)).mpr
  nlinarith

end Problem315.SliceGram

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramConstant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem constantPair_meetingSum (c : ℝ) {i j : V} (hij : i ≠ j) :
    meetingSum (constantPair c) i j = 2 * ((Fintype.card V : ℝ) - 2) * c := by
  rw [meetingSum_eq _ (constantPair_symmetric c) (constantPair_diag c) hij,
    constantPair_rowSum, constantPair_rowSum]
  simp only [constantPair, hij, ite_false]
  ring

theorem constantPair_disjointSum (c : ℝ) {i j : V} (hij : i ≠ j) :
    disjointSum (constantPair c) i j =
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * c := by
  unfold disjointSum
  rw [double_outside_eq _ (constantPair_symmetric c) (constantPair_diag c) hij]
  simp only [constantPair_rowSum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    constantPair, hij, ite_false]
  ring

theorem intersectionAction_constantPair (a b d c : ℝ) (i j : V) :
    intersectionAction a b d (constantPair c) i j =
      (a + 2 * ((Fintype.card V : ℝ) - 2) * b +
        (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d) *
      constantPair c i j := by
  by_cases hij : i = j
  · subst j
    simp [intersectionAction]
  · simp only [intersectionAction, hij, ite_false,
      constantPair_meetingSum c hij, constantPair_disjointSum c hij,
      constantPair]
    ring

theorem constant_relation_of_intersectionAction_eq_zero [Nontrivial V] (b d : ℝ)
    (hzero : ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0) :
    1 + 2 * ((Fintype.card V : ℝ) - 2) * b +
      (((Fintype.card V : ℝ) - 2) * ((Fintype.card V : ℝ) - 3) / 2) * d = 0 := by
  obtain ⟨i, j, hij⟩ := exists_pair_ne V
  have h := hzero i j
  rw [intersectionAction_constantPair] at h
  simpa [constantPair, hij] using h

theorem degree_two_bound_of_intersectionAction_eq_zero [Nontrivial V]
    (hcard : 4 ≤ Fintype.card V) (b d : ℝ)
    (hzero : ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0)
    (hpositive : 0 ≤ 1 + ((Fintype.card V : ℝ) - 4) * b -
      ((Fintype.card V : ℝ) - 3) * d) :
    1 - 2 * b + d ≤ (Fintype.card V : ℝ) - 1 := by
  apply Problem315.SliceGram.degree_two_eigenvalue_le_johnson
    (Fintype.card V : ℝ) b d
    (1 + ((Fintype.card V : ℝ) - 4) * b - ((Fintype.card V : ℝ) - 3) * d)
    (1 - 2 * b + d) (by exact_mod_cast hcard)
    (constant_relation_of_intersectionAction_eq_zero b d hzero) rfl rfl hpositive

end Problem315.SliceCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem315.SliceGramOrbit

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem average_relabel (q : ℕ) (e : Equiv.Perm α) (f : Finset α → ℝ) :
    SliceMoments.average Finset.univ q (fun S => f (S.image e)) =
      SliceMoments.average Finset.univ q f := by
  unfold SliceMoments.average
  congr 1
  apply Finset.sum_bij (fun S _ => S.image e)
  · intro S hS
    have hc := (Finset.mem_powersetCard.mp hS).2
    simp [Finset.mem_powersetCard, Finset.card_image_of_injective S e.injective, hc]
  · intro S hS T hT hST
    have hh := congrArg (Finset.image e.symm) hST
    simpa [Finset.image_image] using hh
  · intro T hT
    refine ⟨T.image e.symm, ?_, ?_⟩
    · have hc := (Finset.mem_powersetCard.mp hT).2
      simp [Finset.mem_powersetCard, Finset.card_image_of_injective T e.symm.injective, hc]
    · simp [Finset.image_image]
  · intro S hS
    rfl

omit [Fintype α] in
theorem pairEquality_relabel (e : Equiv.Perm α) (P S : Finset α) :
    pairEquality (P.image e) (S.image e) = pairEquality P S := by
  unfold pairEquality
  rw [← Finset.image_inter P S e.injective, Finset.card_image_of_injective _ e.injective]

omit [Fintype α] in
theorem pairEquality_pair (i j : α) (hij : i ≠ j) (S : Finset α) :
    pairEquality {i,j} S = SliceMoments.equalIndicator i j S := by
  by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
    simp [pairEquality, SliceMoments.equalIndicator, hi, hj, hij]

theorem centeredPair_relabel (q : ℕ) (e : Equiv.Perm α) (P S : Finset α) :
    centeredPair q (P.image e) (S.image e) = centeredPair q P S := by
  simp only [centeredPair, pairEquality_relabel]

theorem centeredPair_pair (q : ℕ) (i j : α) (hij : i ≠ j) (S : Finset α) :
    centeredPair q {i,j} S = SliceMoments.centeredEqual Finset.univ q i j S := by
  simp only [centeredPair, SliceMoments.centeredEqual, pairEquality_pair i j hij]

theorem gram_relabel (q : ℕ) (e : Equiv.Perm α) (P Q : Finset α) :
    gram q (P.image e) (Q.image e) = gram q P Q := by
  unfold gram
  rw [← average_relabel q e (fun S =>
    centeredPair q (P.image e) S * centeredPair q (Q.image e) S)]
  simp_rw [centeredPair_relabel]

theorem gram_eq_of_intersection (q : ℕ) (P Q R T : Finset α)
    (hP : P.card = 2) (hQ : Q.card = 2) (hR : R.card = 2) (hT : T.card = 2)
    (hI : (P ∩ Q).card = (R ∩ T).card) :
    gram q P Q = gram q R T := by
  exact PairOrbit.invariant_pair_kernel_eq_of_intersection (gram q) (gram_relabel q)
    P Q R T hP hQ hR hT hI

end Problem315.SliceGramOrbit

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceGramProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceGramProfile

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem gram_eq_profile (q : ℕ) (P Q : Finset V)
    (hP : P.card = 2) (hQ : Q.card = 2) :
    SliceGramOrbit.gram q P Q = profile (V := V) q (P ∩ Q).card := by
  unfold profile
  split_ifs with h
  · exact SliceGramOrbit.gram_eq_of_intersection q P Q h.choose.1 h.choose.2
      hP hQ h.choose_spec.1 h.choose_spec.2.1 h.choose_spec.2.2.symm
  · exact False.elim (h ⟨(P,Q), hP, hQ, rfl⟩)

theorem twice_column_inner (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l) :
    2 * ⟪SliceNormalized.column q i j, SliceNormalized.column q k l⟫ =
      SliceGramOrbit.gram q {i,j} {k,l} /
        (SliceMoments.equalMean (Finset.univ : Finset V) q *
          (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)) := by
  rw [SliceNormalized.column_inner q hq hp hp1 i j k l hij hkl]
  simp only [SliceGramOrbit.gram, SliceGramOrbit.centeredPair_pair q i j hij,
    SliceGramOrbit.centeredPair_pair q k l hkl]
  have hp0 := hp.ne'
  have hc : 1 - SliceMoments.equalMean (Finset.univ : Finset V) q ≠ 0 := by linarith
  field_simp

theorem gram_of_intersection_two (q : ℕ) (hq : q ≤ Fintype.card V)
    (i j k l : V) (hij : i ≠ j) (hkl : k ≠ l)
    (hI : (({i,j} : Finset V) ∩ {k,l}).card = 2) :
    SliceGramOrbit.gram q {i,j} {k,l} =
      SliceMoments.equalMean (Finset.univ : Finset V) q *
        (1 - SliceMoments.equalMean (Finset.univ : Finset V) q) := by
  have hg := SliceGramOrbit.gram_eq_of_intersection q {i,j} {k,l} {i,j} {i,j}
    (by simp [hij]) (by simp [hkl]) (by simp [hij]) (by simp [hij])
    (by simpa [hij] using hI)
  rw [hg]
  simp only [SliceGramOrbit.gram, SliceGramOrbit.centeredPair_pair q i j hij,
    ← pow_two]
  exact SliceMoments.average_centeredEqual_sq Finset.univ q (by simpa using hq)
    i j (Finset.mem_univ i) (Finset.mem_univ j) hij

theorem exists_normalized_orbit_entries (q : ℕ) (hq : q ≤ Fintype.card V)
    (hp : 0 < SliceMoments.equalMean (Finset.univ : Finset V) q)
    (hp1 : SliceMoments.equalMean (Finset.univ : Finset V) q < 1) :
    ∃ b d : ℝ, ∀ i j : V, i ≠ j → ∀ k l : V, k ≠ l →
      2 * ⟪SliceNormalized.column q i j, SliceNormalized.column q k l⟫ =
        SliceCoefficients.orbitKernel 1 b d i j k l := by
  let v := SliceMoments.equalMean (Finset.univ : Finset V) q *
    (1 - SliceMoments.equalMean (Finset.univ : Finset V) q)
  have hv : v ≠ 0 := mul_ne_zero hp.ne' (by linarith)
  refine ⟨profile (V := V) q 1 / v, profile (V := V) q 0 / v, ?_⟩
  intro i j hij k l hkl
  rw [twice_column_inner q hq hp hp1 i j k l hij hkl,
    SliceCoefficients.orbitKernel_eq_intersection_card _ _ _ i j k l hij hkl]
  change SliceGramOrbit.gram q {i,j} {k,l} / v = _
  by_cases h2 : (({i,j} : Finset V) ∩ {k,l}).card = 2
  · rw [ite_eq_left h2, gram_of_intersection_two q hq i j k l hij hkl h2]
    exact div_self hv
  · rw [ite_eq_right h2, gram_eq_profile q {i,j} {k,l} (by simp [hij]) (by simp [hkl])]
    by_cases h1 : (({i,j} : Finset V) ∩ {k,l}).card = 1
    · rw [ite_eq_left h1, h1]
    · rw [ite_eq_right h1]
      have hle : (({i,j} : Finset V) ∩ {k,l}).card ≤ 2 := by
        calc
          _ ≤ ({i,j} : Finset V).card := Finset.card_le_card Finset.inter_subset_left
          _ = 2 := by simp [hij]
      have h0 : (({i,j} : Finset V) ∩ {k,l}).card = 0 := by omega
      rw [h0]

end Problem315.SliceGramProfile

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceSynthesisAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem gram_action_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix c)) =
      ofMatrix (intersectionAction a b d c) := by
  ext p
  rcases p with ⟨i,j⟩
  rw [gram_synthesis_apply, ofMatrix_apply]
  simp only [ofMatrix_apply]
  by_cases hij : i=j
  · subst j
    simp [hzdiag, intersectionAction]
  · have h := half_sum_kernel_eq_intersectionAction a b d
      (fun k l => 2 * ⟪z i j,z k l⟫) c hsym hdiag hij (hgram i j hij)
    have hsum : (∑ k, ∑ l, (2 * ⟪z i j,z k l⟫) * c k l) =
        2 * (∑ k, ∑ l, c k l * ⟪z i j,z k l⟫) := by
      simp_rw [show ∀ k l, (2 * ⟪z i j,z k l⟫) * c k l =
        2 * (c k l * ⟪z i j,z k l⟫) by intros; ring]
      simp only [← Finset.mul_sum]
    rw [hsum] at h
    linarith

theorem gram_linear_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (u : V → ℝ) (hu : (∑ i, u i) = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix (linearPair u))) =
      (a + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d) •
        ofMatrix (linearPair u) := by
  rw [gram_action_of_orbit_entries z a b d hzdiag hgram _
    (linearPair_symmetric u) (linearPair_diag u)]
  ext p
  exact intersectionAction_linearPair a b d u hu p.1 p.2

theorem gram_rowZero_of_orbit_entries (z : V → V → E) (a b d : ℝ)
    (hzdiag : ∀ i, z i i = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel a b d i j k l)
    (c : V → V → ℝ) (hsym : ∀ i j, c i j = c j i)
    (hdiag : ∀ i, c i i = 0) (hrow : ∀ i, rowSum c i = 0) :
    LinearMap.adjoint (synthesis z) (synthesis z (ofMatrix c)) =
      (a-2*b+d) • ofMatrix c := by
  rw [gram_action_of_orbit_entries z a b d hzdiag hgram c hsym hdiag]
  ext p
  exact intersectionAction_rowZero a b d c hsym hdiag hrow p.1 p.2

end Problem315.SliceSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceSynthesisBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceSynthesis
open SliceCoefficients

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem intersectionAction_constant_zero_of_total (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l) :
    ∀ i j : V, intersectionAction 1 b d (constantPair 1) i j = 0 := by
  have h := gram_action_of_orbit_entries z 1 b d hzdiag hgram
    (constantPair 1) (constantPair_symmetric 1) (constantPair_diag 1)
  rw [synthesis_constant z hzdiag hztotal, map_zero] at h
  intro i j
  have he := congrArg (fun c : Coeff V => c (i,j)) h
  simpa only [ofMatrix_apply, PiLp.zero_apply] using he.symm

theorem degree_two_bound_of_orbit_entries
    (hcard : 4 ≤ Fintype.card V) (z : V → V → E) (b d : ℝ)
    (hzdiag : ∀ i, z i i = 0) (hztotal : (∑ i, ∑ j, z i j) = 0)
    (hgram : ∀ i j, i ≠ j → ∀ k l, k ≠ l →
      2 * ⟪z i j,z k l⟫ = orbitKernel 1 b d i j k l)
    (hpositive : 0 ≤ 1 + ((Fintype.card V : ℝ) - 4) * b -
      ((Fintype.card V : ℝ) - 3) * d) :
    1 - 2 * b + d ≤ (Fintype.card V : ℝ) - 1 := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  exact degree_two_bound_of_intersectionAction_eq_zero hcard b d
    (intersectionAction_constant_zero_of_total z b d hzdiag hztotal hgram) hpositive

end Problem315.SliceSynthesis

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceOperatorComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem exists_nonzero_linear_coeff (hN : 3 ≤ Fintype.card V) :
    ∃ u : V → ℝ, (∑ i, u i) = 0 ∧ ofMatrix (linearPair u) ≠ 0 := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨i,j,hij⟩ := exists_pair_ne V
  let u : V → ℝ := Pi.single i 1 - Pi.single j 1
  have hu : ∑ k, u k = 0 := by simp [u, Finset.sum_sub_distrib]
  have hui : u i = 1 := by simp [u, hij]
  refine ⟨u, hu, ?_⟩
  intro hc
  have hz : rowSum (linearPair u) i = 0 := by
    unfold rowSum
    apply Finset.sum_eq_zero
    intro k _
    have hh := congrArg (fun c : Coeff V => c (i,k)) hc
    simpa only [ofMatrix_apply, PiLp.zero_apply] using hh
  rw [linearPair_rowSum u hu, hui, mul_one] at hz
  have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  linarith

 theorem linear_orbit_scalar_eq (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (b d : ℝ)
    (hgram : ∀ i j : V, i ≠ j → ∀ k l : V, k ≠ l →
      2 * ⟪column q i j, column q k l⟫ = orbitKernel 1 b d i j k l) :
    1 + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d =
      SliceImageNorm.linearGramScalar (α := V) q := by
  obtain ⟨u,hu,hc⟩ := exists_nonzero_linear_coeff (V := V) hN
  have hg := gram_linear_of_orbit_entries (column q) 1 b d
    (column_diag q) hgram u hu
  have hn := synthesis_linear_norm_sq q hN hq0 hqN u hu
  have hi := (synthesis (column q)).adjoint_inner_right
    (ofMatrix (linearPair u)) (synthesis (column q) (ofMatrix (linearPair u)))
  rw [hg, inner_smul_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq] at hi
  apply mul_right_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))
  linarith

 theorem rowZero_eq_zero_of_card_le_three (hN : Fintype.card V ≤ 3)
    (c : V → V → ℝ) (hrow : ∀ i, rowSum c i = 0)
    (hsym : ∀ i j, c i j = c j i) (hdiag : ∀ i, c i i = 0) : c = 0 := by
  funext i j
  by_cases hij : i = j
  · subst j
    exact hdiag i
  · have hout : ∀ k ∈ outside i j, ∀ l ∈ outside i j, k = l := by
      intro k hk l hl
      by_contra hkl
      have hk' : k ≠ j ∧ k ≠ i := by simpa [outside] using hk
      have hl' : l ≠ j ∧ l ≠ i := by simpa [outside] using hl
      have hc := Finset.card_le_card (Finset.subset_univ ({i,j,k,l} : Finset V))
      have hfour : ({i,j,k,l} : Finset V).card = 4 := by
        simp [hij, hkl, Ne.symm hk'.1,
          Ne.symm hk'.2, Ne.symm hl'.1, Ne.symm hl'.2]
      rw [hfour, Finset.card_univ] at hc
      omega
    have hz : disjointSum c i j = 0 := by
      unfold disjointSum
      have hs : (∑ k ∈ outside i j, ∑ l ∈ outside i j, c k l) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        apply Finset.sum_eq_zero
        intro l hl
        rw [hout k hk l hl]
        exact hdiag l
      rw [hs, zero_div]
    rw [rowZero_disjointSum c hsym hdiag hrow hij] at hz
    exact hz

 theorem column_eq_zero_of_boundary (q : ℕ) (hq : q ≤ Fintype.card V)
    (hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2) (i j : V) :
    column q i j = 0 := by
  by_cases hij : i = j
  · subst j; exact column_diag q i
  · have hr : raw q i j = 0 := by
      ext S
      change (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
      rw [ite_eq_right hij]
      exact SliceMoments.centeredEqual_eq_zero_of_boundary Finset.univ q
        (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
        (by simpa using hb) S.val S.property
    simp [column, hr]

 theorem operator_comparison_nontrivial (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  obtain ⟨b,d,hgram⟩ := SliceGramProfile.exists_normalized_orbit_entries
    (V := V) q hqN.le hp hp1
  let μ₁ : ℝ := 1 + ((Fintype.card V : ℝ)-4)*b - ((Fintype.card V : ℝ)-3)*d
  let μ₂ : ℝ := if 4 ≤ Fintype.card V then 1-2*b+d else 0
  have hμ₁ : μ₁ = SliceImageNorm.linearGramScalar (α := V) q :=
    linear_orbit_scalar_eq q hN hq0 hqN b d hgram
  have hμ₁pos : 0 ≤ μ₁ := by
    rw [hμ₁]
    unfold SliceImageNorm.linearGramScalar
    have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    apply div_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hp.le
  have hb₁ : μ₁ ≤ (Fintype.card V : ℝ)/2 := by
    rw [hμ₁]
    exact SliceImageNorm.linearGramScalar_le hN q hq0 hqN
  have hb₂ : μ₂ ≤ (Fintype.card V : ℝ)-1 := by
    dsimp only [μ₂]
    split_ifs with h4
    · exact degree_two_bound_of_orbit_entries h4 (column q) b d
        (column_diag q) (column_total q (by omega)) hgram hμ₁pos
    · have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
      linarith
  refine Analytic.gram_comparison_of_two_blocks_without_signs
    (E := Space V q) (F := Coeff V) (synthesis (column q)) (SliceEuclideanGenerator.generator q)
    (SliceEuclideanGenerator.generator_symmetric q)
    (SliceEuclideanGenerator.generator_positive q) μ₁ μ₂
    ((Fintype.card V : ℝ)/2) ((Fintype.card V : ℝ)-1) hb₁ hb₂ ?_ f
  intro c
  obtain ⟨u,v,hu,hvrow,hvsym,hvdiag,hdec,horth⟩ :=
    exists_synthesis_decomposition hN (column q) (column_symmetric q)
      (column_diag q) (column_total q (by omega)) c
  refine ⟨ofMatrix (linearPair u),ofMatrix v,hdec,horth,?_,?_,?_,?_⟩
  · exact gram_linear_of_orbit_entries (column q) 1 b d (column_diag q) hgram u hu
  · by_cases h4 : 4 ≤ Fintype.card V
    · simpa only [μ₂, ite_eq_left h4] using gram_rowZero_of_orbit_entries
        (column q) 1 b d (column_diag q) hgram v hvsym hvdiag hvrow
    · have hv := rowZero_eq_zero_of_card_le_three (by omega) v hvrow hvsym hvdiag
      subst v
      simp [ofMatrix, synthesis, μ₂, h4]
  · exact generator_synthesis_linear q u hu
  · exact generator_synthesis_rowZero q v hvrow hvsym hvdiag

 theorem operator_comparison (q : ℕ) (hq : q ≤ Fintype.card V) (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · have hz : synthesis (column (V := V) q) = 0 := by
      ext c S
      simp [synthesis, column_eq_zero_of_boundary q hq hb]
    rw [hz]
    simpa using SliceEuclideanGenerator.generator_positive q f
  · apply operator_comparison_nontrivial
    · omega
    · omega
    · omega

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceProjectionComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized
open SliceSynthesis

variable {V : Type*} [Fintype V] [DecidableEq V]

 theorem raw_eq_zero_of_boundary (q : ℕ) (hq : q ≤ Fintype.card V)
    (hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2) (i j : V) :
    raw q i j = 0 := by
  by_cases hij : i = j
  · subst j; exact raw_diag q i
  · ext S
    change (if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
    rw [ite_eq_right hij]
    exact SliceMoments.centeredEqual_eq_zero_of_boundary Finset.univ q
      (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
      (by simpa using hb) S.val S.property

 theorem denominator_pos (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) : 0 < denominator V q := by
  apply Real.sqrt_pos.2
  have hc : (0 : ℝ) < Nat.choose (Fintype.card V) q := by
    exact_mod_cast Nat.choose_pos hqN.le
  have hp := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  exact mul_pos (mul_pos (mul_pos (by norm_num) hc) hp) (sub_pos.mpr hp1)

 theorem column_span_eq_raw_span (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    (ℝ ∙ column q i j) = (ℝ ∙ raw q i j) := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · rw [column_eq_zero_of_boundary q hq hb, raw_eq_zero_of_boundary q hq hb]
  · unfold column
    apply Submodule.span_singleton_smul_eq
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (denominator_pos q (by omega)
      (by omega) (by omega)).ne')

 theorem column_zero_or_norm_sq (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    column q i j = 0 ∨ ‖column q i j‖ ^ 2 = (1/2 : ℝ) := by
  by_cases hij : i = j
  · subst j; exact Or.inl (column_diag q i)
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · exact Or.inl (column_eq_zero_of_boundary q hq hb i j)
  · right
    exact column_norm_sq q hq (SliceImageNorm.equalMean_pos (by omega) q)
      (SliceImageNorm.equalMean_lt_one (by omega) q (by omega) (by omega)) i j hij

 theorem raw_projection_frame_energy (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) :
    ⟪f, synthesis (column q) (LinearMap.adjoint (synthesis (column q)) f)⟫ =
      (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 := by
  rw [synthesis_eq_frame]
  have h := FrameSynthesis.frame_energy_of_common_norm_sq
    (fun p : V × V => column q p.1 p.2) (1/2)
    (fun p => column_zero_or_norm_sq q hq p.1 p.2) f
  simpa only [Fintype.sum_prod_type, column_span_eq_raw_span q hq] using h

 theorem projection_comparison (q : ℕ) (hq : q ≤ Fintype.card V) (f : Space V q) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  rw [← raw_projection_frame_energy q hq f]
  exact operator_comparison q hq f

 theorem projection_energy_le_swap_energy (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ raw q i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j,
        ‖f - SliceEuclideanGenerator.moveOperator q i j f‖ ^ 2 := by
  rw [← SliceEuclideanGenerator.generator_energy]
  exact projection_comparison q hq f

end Problem315.SliceNormalized

end

end OAI
end

section
-- module Solutions.OAIQW_Problem315.SliceReindexedComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.SliceNormalized

variable {V Ω : Type*} [Fintype V] [sectionDecidableEqV : DecidableEq V] [sectionFintypeΩ : Fintype Ω]

 theorem pullback_move {q : ℕ} (e : Ω ≃ State V q) (i j : V) (f : Space V q) :
    pullback e (SliceEuclideanGenerator.moveOperator q i j f) =
      reindexedMove e i j (pullback e f) := by
  ext ω
  simp

include sectionDecidableEqV in
 theorem norm_projection_pullback {q : ℕ} (e : Ω ≃ State V q)
    (z f : Space V q) :
    ‖(ℝ ∙ pullback e z).starProjection (pullback e f)‖ =
      ‖(ℝ ∙ z).starProjection f‖ := by
  have retainedsectionDecidableEqV := sectionDecidableEqV
  rw [Submodule.starProjection_singleton, Submodule.starProjection_singleton]
  simp only [norm_smul, (pullback e).inner_map_map, (pullback e).norm_map]

 theorem reindexed_projection_energy_le_swap_energy {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ‖f - reindexedMove e i j f‖ ^ 2 := by
  let g : Space V q := (pullback e).symm f
  have hfg : pullback e g = f := (pullback e).apply_symm_apply f
  have hp (i j : V) : ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 =
      ‖(ℝ ∙ raw q i j).starProjection g‖ ^ 2 := by
    rw [← hfg]
    exact congrArg (fun t : ℝ => t^2) (norm_projection_pullback e (raw q i j) g)
  have hm (i j : V) : ‖f - reindexedMove e i j f‖ ^ 2 =
      ‖g - SliceEuclideanGenerator.moveOperator q i j g‖ ^ 2 := by
    rw [← hfg, ← pullback_move, ← map_sub, (pullback e).norm_map]
  simp_rw [hp, hm]
  exact projection_energy_le_swap_energy q hq g

 theorem reindexed_projection_energy_le_swap_sum_oai {q : ℕ}
    (e : Ω ≃ State V q) (hq : q ≤ Fintype.card V) (f : EuclideanSpace ℝ Ω) :
    (1/2 : ℝ) * ∑ i, ∑ j, ‖(ℝ ∙ reindexedRaw e i j).starProjection f‖ ^ 2 ≤
      (1/8 : ℝ) * ∑ i, ∑ j, ∑ ω : Ω,
        (f ω - f (e.symm (SliceEuclideanGenerator.swapState q i j (e ω)))) ^ 2 := by
  have h := reindexed_projection_energy_le_swap_energy e hq f
  simpa only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply, reindexedMove_apply] using h

end Problem315.SliceNormalized

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Problem315.SliceNormalized.reindexed_projection_energy_le_swap_sum_oai.{u_1, u_2} := @OAI.Problem315.SliceNormalized.reindexed_projection_energy_le_swap_sum_oai.{u_1, u_2}
