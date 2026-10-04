-- Prove2me | solution 1 for LodhaMoore.eqOn_two_mul_and_eqOn_neg_inv
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T11:34:28.987401+00:00
-- url     : https://prove2.me/submissions/c5e01f03-73ae-4698-95b3-f2695cb5238e

import Mathlib
import Definitions.Def_LodhaMoore

section
/-! Development: `a`, `b`, `c` are the homeomorphisms the bundle names (`ofReal` returns the
extension of `aFun`, `bFun`, `cFun`), and their values on `ℝ`. -/

namespace LodhaMoore

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

theorem a_symm_coe' (t : ℝ) : a.symm (t : OnePoint ℝ) = ((t - 1 : ℝ) : OnePoint ℝ) := by
  rw [Homeomorph.symm_apply_eq, a_coe]; simp [aFun]

theorem c_symm_coe_of_mem {v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    c.symm (v : OnePoint ℝ) = ((v / (2 - v) : ℝ) : OnePoint ℝ) := by
  rw [Homeomorph.symm_apply_eq, c_coe]
  have hp : 0 < 2 - v := by linarith
  have hm : 0 ≤ v / (2 - v) ∧ v / (2 - v) ≤ 1 := ⟨div_nonneg h0 hp.le, by rw [div_le_iff₀ hp]; linarith⟩
  unfold cFun
  rw [if_pos hm]
  congr 1
  field_simp
  ring

theorem c_symm_coe_of_not_mem {v : ℝ} (h : ¬ (0 ≤ v ∧ v ≤ 1)) :
    c.symm (v : OnePoint ℝ) = (v : OnePoint ℝ) := by
  rw [Homeomorph.symm_apply_eq, c_coe]
  unfold cFun
  rw [if_neg h]

end LodhaMoore
end

section
namespace LodhaMoore

end LodhaMoore

end

section
open LodhaMoore
theorem solution :
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      MulOpposite.unop (MulOpposite.op b * MulOpposite.op c * (MulOpposite.op a)⁻¹ * (MulOpposite.op c)⁻¹ * MulOpposite.op a) (t : OnePoint ℝ) = ((2 * t : ℝ) : OnePoint ℝ)) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) (-1 / 2),
      MulOpposite.unop (MulOpposite.op a * MulOpposite.op b * MulOpposite.op a) (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ)) ∧
    (∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MulOpposite.unop (MulOpposite.op b * (MulOpposite.op a)⁻¹ ^ (3 : ℕ) : (OnePoint ℝ ≃ₜ OnePoint ℝ)ᵐᵒᵖ) (t : OnePoint ℝ) = ((-1 / t : ℝ) : OnePoint ℝ)) := by
  refine ⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_⟩
  · obtain ⟨h0, h1⟩ := ht
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_inv, Homeomorph.mul_apply,
      Homeomorph.inv_apply]
    rw [b_coe, c_coe]
    by_cases hh : t ≤ 1 / 2
    · have hb : bFun t = t / (1 - t) := by
        unfold bFun
        by_cases ht0 : t ≤ 0
        · have : t = 0 := le_antisymm ht0 h0
          subst this; simp
        · rw [if_neg ht0, if_pos hh]
      have hp : 0 < 1 - t := by linarith
      have hm : 0 ≤ t / (1 - t) ∧ t / (1 - t) ≤ 1 :=
        ⟨div_nonneg h0 hp.le, by rw [div_le_iff₀ hp]; linarith⟩
      have hc : cFun (bFun t) = 2 * t := by
        rw [hb]; unfold cFun; rw [if_pos hm]; field_simp; ring
      rw [hc, a_symm_coe']
      by_cases hz : t = 1 / 2
      · subst hz
        rw [c_symm_coe_of_mem (by norm_num) (by norm_num), a_coe]
        norm_num [aFun]
      · rw [c_symm_coe_of_not_mem (by intro h; apply hz; linarith [h.1]), a_coe]
        simp [aFun]
    · have hb : bFun t = 3 - 1 / t := by
        unfold bFun
        rw [if_neg (by linarith), if_neg hh, if_pos h1]
      have hgt : 1 < 3 - 1 / t := by
        have : 1 / t < 2 := by rw [div_lt_iff₀ (by linarith)]; linarith
        linarith
      have hc : cFun (bFun t) = 3 - 1 / t := by
        rw [hb]; unfold cFun; rw [if_neg (by intro h; linarith [h.2])]
      rw [hc, a_symm_coe']
      have hv0 : 0 ≤ 3 - 1 / t - 1 := by
        have : 1 / t ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
        linarith
      have hv1 : 3 - 1 / t - 1 ≤ 1 := by
        have : 1 ≤ 1 / t := by rw [le_div_iff₀ (by linarith)]; linarith
        linarith
      rw [c_symm_coe_of_mem hv0 hv1, a_coe]
      congr 1
      unfold aFun
      have ht0 : t ≠ 0 := by intro h; linarith
      field_simp
      ring
  · obtain ⟨h0, h1⟩ := ht
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, Homeomorph.mul_apply]
    rw [a_coe, b_coe, a_coe]
    congr 1
    unfold aFun bFun
    by_cases hm1 : t = -1
    · subst hm1; norm_num
    have hlt : -1 < t := lt_of_le_of_ne h0 (Ne.symm hm1)
    rw [if_neg (by linarith), if_pos (by linarith)]
    have ht0 : t ≠ 0 := by intro h; linarith
    have ht1 : 1 - (t + 1) ≠ 0 := by intro h; apply ht0; linarith
    field_simp
    ring
  · obtain ⟨h0, h1⟩ := ht
    simp only [MulOpposite.unop_mul, MulOpposite.unop_op, MulOpposite.unop_inv,
      pow_succ, pow_zero, one_mul, Homeomorph.mul_apply, Homeomorph.inv_apply]
    rw [b_coe, a_symm_coe', a_symm_coe', a_symm_coe']
    congr 1
    have hb : bFun t = 3 - 1 / t := by
      unfold bFun
      by_cases hh : t ≤ 1 / 2
      · have : t = 1 / 2 := le_antisymm hh h0
        subst this; norm_num
      · rw [if_neg (by linarith), if_neg hh, if_pos h1]
    rw [hb]
    ring
end
