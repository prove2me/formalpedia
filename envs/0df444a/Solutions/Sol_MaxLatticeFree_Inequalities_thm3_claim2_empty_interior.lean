-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.thm3_claim2_empty_interior
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T19:27:31.892984+00:00
-- url     : https://prove2.me/submissions/f41675a4-2aef-4455-b57f-420376d0602b

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_ValidInequalities

set_option autoImplicit false

namespace MaxLatticeFree.Inequalities.P608

variable {q : ℕ}

lemma combo_add (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (s t : W →₀ ℝ) :
    combo W (s + t) = combo W s + combo W t := by
  unfold combo
  exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)

lemma combo_single (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (a : W) (c : ℝ) :
    combo W (Finsupp.single a c) = c • (a : EuclideanSpace ℝ (Fin q)) := by
  unfold combo
  exact Finsupp.sum_single_index (zero_smul _ _)

lemma combo_zero (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) : combo W 0 = 0 := by
  unfold combo; simp

lemma linVal_add {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) (s t : W →₀ ℝ) :
    linVal ψ (s + t) = linVal ψ s + linVal ψ t := by
  unfold linVal
  exact Finsupp.sum_add_index' (fun _ => mul_zero _) (fun _ _ _ => mul_add _ _ _)

lemma linVal_single {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) (a : W) (c : ℝ) :
    linVal ψ (Finsupp.single a c) = ψ a * c := by
  unfold linVal
  exact Finsupp.sum_single_index (mul_zero _)

lemma linVal_zero {W : Submodule ℝ (EuclideanSpace ℝ (Fin q))} (ψ : W → ℝ) :
    linVal ψ 0 = 0 := by
  unfold linVal; simp

lemma int_add {x y : EuclideanSpace ℝ (Fin q)} (hx : x ∈ integralPoints q)
    (hy : y ∈ integralPoints q) : x + y ∈ integralPoints q := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  obtain ⟨b, hb⟩ := hy i
  exact ⟨a + b, by simp [ha, hb]⟩

lemma int_sub {x y : EuclideanSpace ℝ (Fin q)} (hx : x ∈ integralPoints q)
    (hy : y ∈ integralPoints q) : x - y ∈ integralPoints q := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  obtain ⟨b, hb⟩ := hy i
  exact ⟨a - b, by simp [ha, hb]⟩

lemma int_zsmul (k : ℤ) {x : EuclideanSpace ℝ (Fin q)} (hx : x ∈ integralPoints q) :
    (k : ℝ) • x ∈ integralPoints q := by
  intro i
  obtain ⟨a, ha⟩ := hx i
  exact ⟨k * a, by simp [ha]⟩

lemma int_zero : (0 : EuclideanSpace ℝ (Fin q)) ∈ integralPoints q := fun _ => ⟨0, by simp⟩

/-- `v` can be pushed to the lattice from any multiple `t • v` by nonnegative rays of bounded cost. -/
def Good (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (ψ : W → ℝ)
    (v : EuclideanSpace ℝ (Fin q)) : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, ∃ s : W →₀ ℝ, (∀ w, 0 ≤ s w) ∧ linVal ψ s ≤ C ∧
    t • v + combo W s ∈ integralPoints q

lemma good_of_span (W : Submodule ℝ (EuclideanSpace ℝ (Fin q))) (ψ : W → ℝ)
    {v : EuclideanSpace ℝ (Fin q)}
    (hv : v ∈ Submodule.span ℝ {u | u ∈ W ∧ u ∈ integralPoints q}) : Good W ψ v := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨hxW, hxI⟩ := hx
    refine ⟨|ψ ⟨-x, W.neg_mem hxW⟩|, fun t =>
      ⟨Finsupp.single ⟨-x, W.neg_mem hxW⟩ (Int.fract t), ?_, ?_, ?_⟩⟩
    · intro w
      rw [Finsupp.single_apply]
      split_ifs
      · exact Int.fract_nonneg t
      · exact le_refl 0
    · rw [linVal_single]
      calc ψ ⟨-x, W.neg_mem hxW⟩ * Int.fract t ≤ |ψ ⟨-x, W.neg_mem hxW⟩ * Int.fract t| :=
            le_abs_self _
        _ = |ψ ⟨-x, W.neg_mem hxW⟩| * Int.fract t := by
            rw [abs_mul, abs_of_nonneg (Int.fract_nonneg t)]
        _ ≤ |ψ ⟨-x, W.neg_mem hxW⟩| * 1 :=
            mul_le_mul_of_nonneg_left (Int.fract_lt_one t).le (abs_nonneg _)
        _ = _ := mul_one _
    · rw [combo_single]
      have h : t • x + Int.fract t • (-x) = ((⌊t⌋ : ℤ) : ℝ) • x := by
        rw [smul_neg, ← sub_eq_add_neg, ← sub_smul, Int.self_sub_fract]
      simp only [Submodule.coe_mk]
      rw [h]
      exact int_zsmul _ hxI
  | zero =>
    exact ⟨0, fun _ => ⟨0, fun _ => le_refl _, by rw [linVal_zero],
      by rw [smul_zero, combo_zero, add_zero]; exact int_zero⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨C1, h1⟩ := hx
    obtain ⟨C2, h2⟩ := hy
    refine ⟨C1 + C2, fun t => ?_⟩
    obtain ⟨s1, n1, l1, i1⟩ := h1 t
    obtain ⟨s2, n2, l2, i2⟩ := h2 t
    refine ⟨s1 + s2, fun w => ?_, ?_, ?_⟩
    · rw [Finsupp.add_apply]; exact add_nonneg (n1 w) (n2 w)
    · rw [linVal_add]; linarith
    · have h : t • (x + y) + combo W (s1 + s2) = (t • x + combo W s1) + (t • y + combo W s2) := by
        rw [combo_add, smul_add]; abel
      rw [h]
      exact int_add i1 i2
  | smul a x _ hx =>
    obtain ⟨C, h⟩ := hx
    refine ⟨C, fun t => ?_⟩
    obtain ⟨s, n, l, i⟩ := h (t * a)
    exact ⟨s, n, l, by rw [smul_smul]; exact i⟩

end MaxLatticeFree.Inequalities.P608

open MaxLatticeFree.Inequalities in
theorem solution {q : ℕ} (f : EuclideanSpace ℝ (Fin q)) (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (hf : (affSpace f W ∩ integralPoints q).Nonempty) (ψ : W → ℝ) (α : ℝ)
    (hvalid : IsValid f W ψ α) (hsub : IsSublinear ψ)
    (hfV : f ∈ affHullInt f W) (hα : α ≤ 0) :
    Disjoint (intBpsi f W ψ α) (affHullInt f W : Set (EuclideanSpace ℝ (Fin q))) := by
  rw [Set.disjoint_left]
  rintro x ⟨hxW, hlt⟩ hxV
  have hr : ψ ⟨x - f, hxW⟩ < 0 := lt_of_lt_of_le hlt hα
  have hspan : x - f ∈ Submodule.span ℝ {u | u ∈ W ∧ u ∈ integralPoints q} := by
    have h1 : x -ᵥ f ∈ (affHullInt f W).direction := AffineSubspace.vsub_mem_direction hxV hfV
    rw [affHullInt, direction_affineSpan, vectorSpan_def] at h1
    refine Submodule.span_mono ?_ h1
    rintro _ ⟨a, ⟨haW, haI⟩, b, ⟨hbW, hbI⟩, rfl⟩
    refine ⟨?_, P608.int_sub haI hbI⟩
    have h2 := W.sub_mem haW hbW
    have h3 : (a - f) - (b - f) = a -ᵥ b := by rw [vsub_eq_sub]; abel
    rw [h3] at h2
    exact h2
  obtain ⟨C, hC⟩ := P608.good_of_span W ψ hspan
  obtain ⟨z, hzW, hzI⟩ := hf
  have hzW' : z - f ∈ W := hzW
  set K : ℝ := ψ ⟨z - f, hzW'⟩ + C - α with hK
  set t : ℝ := (|K| + 1) / (-ψ ⟨x - f, hxW⟩) with ht
  have ht0 : 0 ≤ t := div_nonneg (by positivity) (by linarith)
  have htr : t * ψ ⟨x - f, hxW⟩ = -(|K| + 1) := by
    rw [ht, div_mul_eq_mul_div, div_eq_iff (by linarith : -ψ ⟨x - f, hxW⟩ ≠ 0)]
    ring
  obtain ⟨s, hs0, hsl, hsi⟩ := hC t
  have hSR : (Finsupp.single (⟨z - f, hzW'⟩ : W) (1 : ℝ) + Finsupp.single ⟨x - f, hxW⟩ t + s)
      ∈ Rf f W := by
    refine ⟨?_, ?_⟩
    · have h : f + combo W (Finsupp.single (⟨z - f, hzW'⟩ : W) (1 : ℝ)
          + Finsupp.single ⟨x - f, hxW⟩ t + s) = z + (t • (x - f) + combo W s) := by
        rw [P608.combo_add, P608.combo_add, P608.combo_single, P608.combo_single]
        simp only [Submodule.coe_mk, one_smul]
        abel
      rw [h]
      exact P608.int_add hzI hsi
    · intro w
      simp only [Finsupp.add_apply]
      have h1 : 0 ≤ Finsupp.single (⟨z - f, hzW'⟩ : W) (1 : ℝ) w := by
        rw [Finsupp.single_apply]; split_ifs <;> norm_num
      have h2 : 0 ≤ Finsupp.single (⟨x - f, hxW⟩ : W) t w := by
        rw [Finsupp.single_apply]; split_ifs
        · exact ht0
        · exact le_refl 0
      linarith [hs0 w]
  have hv := hvalid _ hSR
  rw [P608.linVal_add, P608.linVal_add, P608.linVal_single, P608.linVal_single, mul_one, mul_comm, htr] at hv
  have hKa := le_abs_self K
  linarith
