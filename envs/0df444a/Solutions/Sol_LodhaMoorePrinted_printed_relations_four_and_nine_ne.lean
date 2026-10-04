-- Prove2me | solution 1 for LodhaMoorePrinted.printed_relations_four_and_nine_ne
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-02T19:34:53.770972+00:00
-- url     : https://prove2.me/submissions/df80c22b-e3bd-40b1-a9d4-5d57b553e9d9

import Definitions.Def_LodhaMoore
import Mathlib

section
namespace LodhaMoorePrinted

open LodhaMoore

theorem ofReal_coe {f : ℝ → ℝ} (e : ℝ ≃ₜ ℝ) (he : ∀ t, e t = f t) (t : ℝ) :
    ofReal f (t : OnePoint ℝ) = ((f t : ℝ) : OnePoint ℝ) := by
  have h : ∃ E : OnePoint ℝ ≃ₜ OnePoint ℝ, ∀ t : ℝ, E t = ((f t : ℝ) : OnePoint ℝ) :=
    ⟨e.onePointCongr, fun t => by rw [Homeomorph.onePointCongr_apply, OnePoint.map_some, he]⟩
  unfold ofReal
  rw [dif_pos h]
  exact h.choose_spec t

theorem aFun_strictMono : StrictMono aFun := fun x y h => by unfold aFun; linarith

theorem aFun_surjective : Function.Surjective aFun := fun u => ⟨u - 1, by unfold aFun; ring⟩

theorem bFun_strictMono : StrictMono bFun := by
  intro x y hxy
  unfold bFun
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 <;> try linarith
  all_goals first
    | (rw [lt_div_iff₀ (by linarith)]; nlinarith)
    | (rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith)
    | (have : 1 / y < 1 / x := one_div_lt_one_div_of_lt (by linarith) hxy; linarith)
    | (have : 1 / y < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
       have : x / (1 - x) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
       linarith)
    | (have : x / (1 - x) ≤ 1 := by rw [div_le_iff₀ (by linarith)]; linarith
       linarith)
    | (have : 1 / x ≥ 1 := by rw [ge_iff_le, le_div_iff₀ (by linarith)]; linarith
       linarith)

theorem bFun_surjective : Function.Surjective bFun := by
  intro u
  unfold bFun
  by_cases h0 : u ≤ 0
  · exact ⟨u, by simp [h0]⟩
  by_cases h1 : u ≤ 1
  · refine ⟨u / (1 + u), ?_⟩
    have hp : 0 < 1 + u := by linarith
    have hpos : ¬ u / (1 + u) ≤ 0 := not_le.mpr (div_pos (by linarith) hp)
    have hh : u / (1 + u) ≤ 1 / 2 := by rw [div_le_iff₀ hp]; linarith
    simp only [hpos, hh, if_false, if_true]
    field_simp
    ring
  by_cases h2 : u ≤ 2
  · refine ⟨1 / (3 - u), ?_⟩
    have hp : 0 < 3 - u := by linarith
    have hpos : ¬ 1 / (3 - u) ≤ 0 := not_le.mpr (div_pos one_pos hp)
    have hh : ¬ 1 / (3 - u) ≤ 1 / 2 := by
      rw [not_le, div_lt_div_iff₀ two_pos hp]; linarith
    have hh1 : 1 / (3 - u) ≤ 1 := by rw [div_le_iff₀ hp]; linarith
    simp only [hpos, hh, hh1, if_false, if_true]
    field_simp
    ring
  · refine ⟨u - 1, ?_⟩
    have a1 : ¬ u - 1 ≤ 0 := by linarith
    have a2 : ¬ u - 1 ≤ 1 / 2 := by linarith
    have a3 : ¬ u - 1 ≤ 1 := by linarith
    simp only [a1, a2, a3, if_false]
    ring

theorem cFun_strictMono : StrictMono cFun := by
  intro x y hxy
  unfold cFun
  split_ifs with h1 h2 h2 <;> try linarith
  · rw [div_lt_div_iff₀ (by linarith) (by linarith)]; nlinarith
  · -- x ∈ [0,1], y ∉ [0,1], so y > 1
    have hy : 1 < y := by
      by_contra hc; exact h2 ⟨by linarith, by linarith⟩
    rw [div_lt_iff₀ (by linarith)]; nlinarith
  · -- x ∉ [0,1], y ∈ [0,1], so x < 0
    have hx : x < 0 := by
      by_contra hc; exact h1 ⟨by linarith, by linarith⟩
    rw [lt_div_iff₀ (by linarith)]; nlinarith

theorem cFun_surjective : Function.Surjective cFun := by
  intro u
  unfold cFun
  by_cases h : 0 ≤ u ∧ u ≤ 1
  · refine ⟨u / (2 - u), ?_⟩
    have hp : 0 < 2 - u := by linarith
    have hh : 0 ≤ u / (2 - u) ∧ u / (2 - u) ≤ 1 :=
      ⟨div_nonneg h.1 hp.le, by rw [div_le_iff₀ hp]; linarith⟩
    rw [if_pos hh]
    field_simp
    ring
  · exact ⟨u, by rw [if_neg h]⟩

noncomputable def aHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective aFun aFun_strictMono aFun_surjective).toHomeomorph
noncomputable def bHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective bFun bFun_strictMono bFun_surjective).toHomeomorph
noncomputable def cHom : ℝ ≃ₜ ℝ :=
  (StrictMono.orderIsoOfSurjective cFun cFun_strictMono cFun_surjective).toHomeomorph

theorem a_coe (t : ℝ) : a (t : OnePoint ℝ) = ((aFun t : ℝ) : OnePoint ℝ) := ofReal_coe aHom (fun _ => rfl) t
theorem b_coe (t : ℝ) : b (t : OnePoint ℝ) = ((bFun t : ℝ) : OnePoint ℝ) := ofReal_coe bHom (fun _ => rfl) t
theorem c_coe (t : ℝ) : c (t : OnePoint ℝ) = ((cFun t : ℝ) : OnePoint ℝ) := ofReal_coe cHom (fun _ => rfl) t


theorem printed_relations_four_and_nine_ne :
    (MulOpposite.op LodhaMoore.c : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * MulOpposite.op LodhaMoore.b ^ (2 : ℕ) * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.b ≠
      (MulOpposite.op LodhaMoore.b ^ (2 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.c ∧
    (MulOpposite.op LodhaMoore.c : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) ≠
      (MulOpposite.op LodhaMoore.b ^ (2 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * (MulOpposite.op LodhaMoore.a)⁻¹ * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.c * (MulOpposite.op LodhaMoore.b)⁻¹ ^ (2 : ℕ) * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * (MulOpposite.op LodhaMoore.c)⁻¹ * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.c * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ := by
  have s0 : c ((1 / 2 : ℝ) : OnePoint ℝ) = ((2 / 3 : ℝ) : OnePoint ℝ) := by rw [c_coe]; norm_num [cFun]
  have s1 : b ((2 / 3 : ℝ) : OnePoint ℝ) = ((3 / 2 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s2 : b ((3 / 2 : ℝ) : OnePoint ℝ) = ((5 / 2 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s3 : a.symm ((5 / 2 : ℝ) : OnePoint ℝ) = ((3 / 2 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, a_coe]; norm_num [aFun]
  have s4 : a ((5 / 2 : ℝ) : OnePoint ℝ) = ((7 / 2 : ℝ) : OnePoint ℝ) := by rw [a_coe]; norm_num [aFun]
  have s5 : b ((7 / 2 : ℝ) : OnePoint ℝ) = ((9 / 2 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s6 : b ((1 / 2 : ℝ) : OnePoint ℝ) = ((1 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s7 : b ((1 : ℝ) : OnePoint ℝ) = ((2 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s8 : a.symm ((2 : ℝ) : OnePoint ℝ) = ((1 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, a_coe]; norm_num [aFun]
  have s9 : a ((2 : ℝ) : OnePoint ℝ) = ((3 : ℝ) : OnePoint ℝ) := by rw [a_coe]; norm_num [aFun]
  have s10 : b ((3 : ℝ) : OnePoint ℝ) = ((4 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s11 : c ((4 : ℝ) : OnePoint ℝ) = ((4 : ℝ) : OnePoint ℝ) := by rw [c_coe]; norm_num [cFun]
  have s12 : c ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by rw [c_coe]; norm_num [cFun]
  have s13 : b ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s14 : a.symm ((0 : ℝ) : OnePoint ℝ) = ((-1 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, a_coe]; norm_num [aFun]
  have s15 : b.symm ((-1 : ℝ) : OnePoint ℝ) = ((-1 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, b_coe]; norm_num [bFun]
  have s16 : a ((-1 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by rw [a_coe]; norm_num [aFun]
  have s17 : b.symm ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, b_coe]; norm_num [bFun]
  have s18 : a ((0 : ℝ) : OnePoint ℝ) = ((1 : ℝ) : OnePoint ℝ) := by rw [a_coe]; norm_num [aFun]
  have s19 : b.symm ((1 : ℝ) : OnePoint ℝ) = ((1 / 2 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, b_coe]; norm_num [bFun]
  have s20 : c.symm ((1 / 2 : ℝ) : OnePoint ℝ) = ((1 / 3 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, c_coe]; norm_num [cFun]
  have s21 : b ((1 / 3 : ℝ) : OnePoint ℝ) = ((1 / 2 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s22 : a.symm ((1 / 2 : ℝ) : OnePoint ℝ) = ((-1 / 2 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, a_coe]; norm_num [aFun]
  have s23 : b ((-1 / 2 : ℝ) : OnePoint ℝ) = ((-1 / 2 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s24 : a ((-1 / 2 : ℝ) : OnePoint ℝ) = ((1 / 2 : ℝ) : OnePoint ℝ) := by rw [a_coe]; norm_num [aFun]
  have s25 : b.symm ((1 / 2 : ℝ) : OnePoint ℝ) = ((1 / 3 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, b_coe]; norm_num [bFun]
  have s26 : a ((1 / 3 : ℝ) : OnePoint ℝ) = ((4 / 3 : ℝ) : OnePoint ℝ) := by rw [a_coe]; norm_num [aFun]
  have s27 : b.symm ((4 / 3 : ℝ) : OnePoint ℝ) = ((3 / 5 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, b_coe]; norm_num [bFun]
  have s28 : c ((3 / 5 : ℝ) : OnePoint ℝ) = ((3 / 4 : ℝ) : OnePoint ℝ) := by rw [c_coe]; norm_num [cFun]
  have s29 : b ((3 / 4 : ℝ) : OnePoint ℝ) = ((5 / 3 : ℝ) : OnePoint ℝ) := by rw [b_coe]; norm_num [bFun]
  have s30 : a.symm ((5 / 3 : ℝ) : OnePoint ℝ) = ((2 / 3 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, a_coe]; norm_num [aFun]
  have s31 : a.symm ((3 / 2 : ℝ) : OnePoint ℝ) = ((1 / 2 : ℝ) : OnePoint ℝ) := by rw [Homeomorph.symm_apply_eq, a_coe]; norm_num [aFun]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have e := congrArg (fun g : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ => MulOpposite.unop g ((1 / 2 : ℝ) : OnePoint ℝ)) h
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_inv, pow_two, Homeomorph.mul_apply, Homeomorph.inv_apply] at e
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31] at e
    have := OnePoint.coe_injective e
    norm_num at this
  · have e := congrArg (fun g : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ => MulOpposite.unop g ((0 : ℝ) : OnePoint ℝ)) h
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_inv, pow_two, Homeomorph.mul_apply, Homeomorph.inv_apply] at e
    simp only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17, s18, s19, s20, s21, s22, s23, s24, s25, s26, s27, s28, s29, s30, s31] at e
    have := OnePoint.coe_injective e
    norm_num at this

end LodhaMoorePrinted
end


open LodhaMoorePrinted in
theorem solution :
    (MulOpposite.op LodhaMoore.c : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * MulOpposite.op LodhaMoore.b ^ (2 : ℕ) * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.b ≠
      (MulOpposite.op LodhaMoore.b ^ (2 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.c ∧
    (MulOpposite.op LodhaMoore.c : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) ≠
      (MulOpposite.op LodhaMoore.b ^ (2 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) * (MulOpposite.op LodhaMoore.a)⁻¹ * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.a * MulOpposite.op LodhaMoore.c * (MulOpposite.op LodhaMoore.b)⁻¹ ^ (2 : ℕ) * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * (MulOpposite.op LodhaMoore.c)⁻¹ * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.a * (MulOpposite.op LodhaMoore.b)⁻¹ * MulOpposite.op LodhaMoore.c * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ * MulOpposite.op LodhaMoore.b * (MulOpposite.op LodhaMoore.a)⁻¹ :=
  by
  first
    | exact LodhaMoorePrinted.printed_relations_four_and_nine_ne
    | exact LodhaMoorePrinted.printed_relations_four_and_nine_ne ..
    | (apply LodhaMoorePrinted.printed_relations_four_and_nine_ne <;> first | assumption | infer_instance)
    | simpa using LodhaMoorePrinted.printed_relations_four_and_nine_ne
