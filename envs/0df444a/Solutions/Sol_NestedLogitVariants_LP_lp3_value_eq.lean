-- Prove2me | solution 1 for NestedLogitVariants.LP.lp3_value_eq
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-06T13:39:34.659158+00:00
-- url     : https://prove2.me/submissions/910a4bfc-da77-42a0-ba61-69399a50c1c4

import Definitions.Def_NestedLogitVariants_LP_Model

namespace NestedLogitVariants.LP

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

private lemma V_nonneg (I : Instance ι n) (hI : I.Standing) (i : ι) (S : Finset (Fin n)) :
    0 ≤ V I i S := by
  exact add_nonneg (hI.vnp_nonneg i) (Finset.sum_nonneg fun j _ => (hI.v_pos i j).le)

private lemma weight_nonneg (I : Instance ι n) (hI : I.Standing) (i : ι) (S : Finset (Fin n)) :
    0 ≤ nestWeight I i S := Real.rpow_nonneg (V_nonneg I hI i S) _

private lemma R_nonneg (I : Instance ι n) (hI : I.Standing) (i : ι) (S : Finset (Fin n)) :
    0 ≤ R I i S := by
  exact div_nonneg
    (Finset.sum_nonneg fun j _ => mul_nonneg (hI.r_nonneg i j) (hI.v_pos i j).le)
    (V_nonneg I hI i S)

private lemma denominator_nonneg (I : Instance ι n) (hI : I.Standing) (S : ι → Finset (Fin n)) :
    0 ≤ I.v0 + ∑ i, nestWeight I i (S i) :=
  add_nonneg hI.v0_nonneg (Finset.sum_nonneg fun i _ => weight_nonneg I hI i (S i))

private lemma revenue_nonneg (I : Instance ι n) (hI : I.Standing) (S : ι → Finset (Fin n)) :
    0 ≤ revenue I S := by
  exact div_nonneg
    (Finset.sum_nonneg fun i _ => mul_nonneg (weight_nonneg I hI i (S i)) (R_nonneg I hI i (S i)))
    (denominator_nonneg I hI S)

private lemma revenue_mul_denominator (I : Instance ι n) (hI : I.Standing)
    (S : ι → Finset (Fin n)) :
    revenue I S * (I.v0 + ∑ i, nestWeight I i (S i)) =
      ∑ i, nestWeight I i (S i) * R I i (S i) := by
  by_cases hd : I.v0 + ∑ i, nestWeight I i (S i) = 0
  · have hw : ∀ i, nestWeight I i (S i) = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j _ => weight_nonneg I hI j (S j)) (Finset.mem_univ i)
      have h0 := weight_nonneg I hI i (S i)
      have hv := hI.v0_nonneg
      linarith
    rw [hd, mul_zero]
    symm
    exact Finset.sum_eq_zero (fun i _ => by rw [hw i, zero_mul])
  · exact div_mul_cancel₀ _ hd

private lemma objective_sum (I : Instance ι n) (S : ι → Finset (Fin n)) (x : ℝ) :
    (∑ i, nestWeight I i (S i) * (R I i (S i) - x)) =
      (∑ i, nestWeight I i (S i) * R I i (S i)) -
      (∑ i, nestWeight I i (S i)) * x := by
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

private lemma feasible_sum (I : Instance ι n) (x : ℝ) (y : ι → ℝ)
    (h : LP3Feasible I x y) (S : ι → Finset (Fin n)) :
    (∑ i, nestWeight I i (S i) * R I i (S i)) ≤
      x * (I.v0 + ∑ i, nestWeight I i (S i)) := by
  have hs := (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => h.2 i (S i)).trans h.1
  rw [objective_sum] at hs
  nlinarith

private lemma feasible_at_optimal (I : Instance ι n) (hI : I.Standing)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar) :
    ∃ y, LP3Feasible I (revenue I Sstar) y := by
  classical
  have hm (i : ι) : ∃ S : Finset (Fin n), ∀ T : Finset (Fin n),
      nestWeight I i T * (R I i T - revenue I Sstar) ≤
        nestWeight I i S * (R I i S - revenue I Sstar) := by
    obtain ⟨S, _, hS⟩ := Finset.exists_max_image Finset.univ
      (fun S : Finset (Fin n) => nestWeight I i S * (R I i S - revenue I Sstar))
      Finset.univ_nonempty
    exact ⟨S, fun T => hS T (Finset.mem_univ T)⟩
  choose Sh hSh using hm
  refine ⟨fun i => nestWeight I i (Sh i) * (R I i (Sh i) - revenue I Sstar), ?_, hSh⟩
  have hs := mul_le_mul_of_nonneg_right (hopt Sh) (denominator_nonneg I hI Sh)
  rw [revenue_mul_denominator I hI Sh] at hs
  rw [objective_sum]
  nlinarith

private lemma feasible_revenue_le_of_pos (I : Instance ι n) (x : ℝ) (y : ι → ℝ)
    (h : LP3Feasible I x y) (S : ι → Finset (Fin n))
    (hd : 0 < I.v0 + ∑ i, nestWeight I i (S i)) : revenue I S ≤ x := by
  exact (div_le_iff₀ hd).2 (feasible_sum I x y h S)

private lemma feasible_nonneg (I : Instance ι n) (hI : I.Standing) [Nonempty ι]
    (hn : 0 < n) (x : ℝ) (y : ι → ℝ) (h : LP3Feasible I x y) : 0 ≤ x := by
  let j : Fin n := ⟨0, hn⟩
  let S : ι → Finset (Fin n) := fun _ => {j}
  have hw : ∀ i, 0 < nestWeight I i (S i) := by
    intro i
    apply Real.rpow_pos_of_pos
    change 0 < I.vnp i + ∑ k ∈ ({j} : Finset (Fin n)), I.v i k
    simpa using add_pos_of_nonneg_of_pos (hI.vnp_nonneg i) (hI.v_pos i j)
  have hsum : 0 < ∑ i, nestWeight I i (S i) := Finset.sum_pos (fun i _ => hw i) Finset.univ_nonempty
  have hd : 0 < I.v0 + ∑ i, nestWeight I i (S i) := add_pos_of_nonneg_of_pos hI.v0_nonneg hsum
  exact (revenue_nonneg I hI S).trans (feasible_revenue_le_of_pos I x y h S hd)

private lemma feasible_revenue_le (I : Instance ι n) (hI : I.Standing) [Nonempty ι]
    (hn : 0 < n) (x : ℝ) (y : ι → ℝ) (h : LP3Feasible I x y)
    (S : ι → Finset (Fin n)) : revenue I S ≤ x := by
  rcases (denominator_nonneg I hI S).eq_or_lt with hd | hd
  · have hx := feasible_nonneg I hI hn x y h
    simpa [revenue, ← hd] using hx
  · exact feasible_revenue_le_of_pos I x y h S hd

end NestedLogitVariants.LP


open NestedLogitVariants.LP

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) [Nonempty ι] (hn : 0 < n)
    (Sstar : ι → Finset (Fin n)) (hopt : IsOptimal I Sstar) :
    IsLeast {x | ∃ y, LP3Feasible I x y} (revenue I Sstar) := by
  refine ⟨feasible_at_optimal I hI Sstar hopt, ?_⟩
  rintro x ⟨y, hy⟩
  exact feasible_revenue_le I hI hn x y hy Sstar
