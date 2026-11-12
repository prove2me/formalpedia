-- Prove2me | solution 1 for HindsightGain.Uniform.lemma_2_1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T01:53:16.98657+00:00
-- url     : https://prove2.me/submissions/bdc1e9e4-8ed1-4340-a6e1-921b691170bf

import Mathlib
import Definitions.Def_HindsightGain_Uniform_optima

section
set_option autoImplicit false

namespace HindsightGain.Uniform.Dev.Lem21
open HindsightGain.Uniform

lemma edge_eq_map {n r : ℕ} (e : Edge n r) :
    e.val = Finset.univ.map (e.val.orderEmbOfFin e.property).toEmbedding := by
  ext i
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  have := Finset.range_orderEmbOfFin e.val e.property
  constructor
  · intro h
    have : i ∈ Set.range (e.val.orderEmbOfFin e.property) := by rw [this]; exact h
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact Finset.orderEmbOfFin_mem _ _ _

lemma prod_edge {n r : ℕ} (e : Edge n r) (f : Fin n → ℝ) :
    ∏ i ∈ e.val, f i = ∏ j : Fin r, f (e.val.orderEmbOfFin e.property j) := by
  conv_lhs => rw [edge_eq_map e]
  rw [Finset.prod_map]; rfl

lemma objective_scale {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ) (x : Fin n → Vec D) :
    objective M a x = objective M (fun _ => 1) (fun i => a i • x i) := by
  unfold objective interaction
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Finset.prod_const_one, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [PiLp.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  rw [prod_edge e a]; ring

lemma objective_cont {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ) :
    Continuous (objective M a) := by
  unfold objective interaction
  refine continuous_finset_sum _ fun e _ => ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finset_sum _ fun b _ => ?_
  refine Continuous.mul continuous_const ?_
  refine continuous_finset_prod _ fun j _ => ?_
  have h1 : Continuous fun x : Fin n → Vec D => x (e.val.orderEmbOfFin e.property j) :=
    continuous_apply _
  exact (PiLp.continuous_apply 2 (fun _ : Fin D => ℝ) (b j)).comp h1

lemma interaction_affine {n D r : ℕ} (M : Model n D r) (e : Edge n r) (x : Fin n → Vec D)
    (j : Fin n) (u w : Vec D) (s t : ℝ) (hst : s + t = 1) :
    interaction M e (Function.update x j (s • u + t • w)) =
      s * interaction M e (Function.update x j u) + t * interaction M e (Function.update x j w) := by
  unfold interaction
  by_cases hj : j ∈ e.val
  · obtain ⟨l0, hl0⟩ : ∃ l0, e.val.orderEmbOfFin e.property l0 = j := by
      have := Finset.range_orderEmbOfFin e.val e.property
      have h : j ∈ Set.range (e.val.orderEmbOfFin e.property) := by rw [this]; exact hj
      exact h
    have key : ∀ v : Vec D, ∀ b : Fin r → Fin D,
        ∏ l, (Function.update x j v (e.val.orderEmbOfFin e.property l)) (b l)
          = v (b l0) * ∏ l ∈ Finset.univ.erase l0, x (e.val.orderEmbOfFin e.property l) (b l) := by
      intro v b
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l0), hl0]
      simp only [Function.update_self]
      congr 1
      refine Finset.prod_congr rfl fun l hl => ?_
      have : e.val.orderEmbOfFin e.property l ≠ j := by
        rw [← hl0]; intro h
        exact (Finset.ne_of_mem_erase hl) ((e.val.orderEmbOfFin e.property).injective h)
      rw [Function.update_of_ne this]
    simp only [key, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring
  · have key : ∀ v : Vec D, ∀ b : Fin r → Fin D,
        ∏ l, (Function.update x j v (e.val.orderEmbOfFin e.property l)) (b l)
          = ∏ l, x (e.val.orderEmbOfFin e.property l) (b l) := by
      intro v b
      refine Finset.prod_congr rfl fun l _ => ?_
      have : e.val.orderEmbOfFin e.property l ≠ j := fun h => hj (h ▸ Finset.orderEmbOfFin_mem _ _ _)
      rw [Function.update_of_ne this]
    simp only [key, Finset.mul_sum, ← Finset.sum_add_distrib]
    have : ∀ b : Fin r → Fin D, M.A e b * ∏ l, x (e.val.orderEmbOfFin e.property l) (b l)
        = s * (M.A e b * ∏ l, x (e.val.orderEmbOfFin e.property l) (b l))
          + t * (M.A e b * ∏ l, x (e.val.orderEmbOfFin e.property l) (b l)) := by
      intro b; rw [← add_mul, hst, one_mul]
    exact Finset.sum_congr rfl fun b _ => this b

lemma objective_affine {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ) (x : Fin n → Vec D)
    (j : Fin n) (u w : Vec D) (s t : ℝ) (hst : s + t = 1) :
    objective M a (Function.update x j (s • u + t • w)) =
      s * objective M a (Function.update x j u) + t * objective M a (Function.update x j w) := by
  unfold objective
  simp only [interaction_affine M _ x j u w s t hst, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun e _ => by ring

lemma bound {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ) (c : ℝ)
    (hc : ∀ x ∈ feasible M, objective M a x ≤ c) (s : Finset (Fin n)) :
    ∀ x : Fin n → Vec D, (∀ i, x i ∈ convexHull ℝ (M.K i)) → (∀ i, i ∉ s → x i ∈ M.K i) →
      objective M a x ≤ c := by
  induction s using Finset.induction_on with
  | empty => intro x _ h; exact hc x (fun i => h i (by simp))
  | insert j s hj ih =>
    intro x hx h
    have hconv : Convex ℝ {v : Vec D | objective M a (Function.update x j v) ≤ c} := by
      intro u hu w hw p q hp hq hpq
      simp only [Set.mem_setOf_eq] at *
      rw [objective_affine M a x j u w p q hpq]
      have hq' : q = 1 - p := by linarith
      subst hq'
      nlinarith [mul_le_mul_of_nonneg_left hu hp, mul_le_mul_of_nonneg_left hw hq]
    have hsub : M.K j ⊆ {v : Vec D | objective M a (Function.update x j v) ≤ c} := by
      intro v hv
      apply ih
      · intro i; by_cases hij : i = j
        · subst hij; simp; exact subset_convexHull ℝ _ hv
        · simp [hij, hx i]
      · intro i hi; by_cases hij : i = j
        · subst hij; simp; exact hv
        · simp [hij]; exact h i (by simp [hij, hi])
    have := convexHull_min hsub hconv (hx j)
    have h2 : Function.update x j (x j) = x := by simp
    simpa [h2] using this

end HindsightGain.Uniform.Dev.Lem21

namespace HindsightGain.Uniform
open HindsightGain.Uniform.Dev.Lem21 in
theorem chk_lemma_2_1 {n D r : ℕ} (M : Model n D r) (a : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    val M a = sSup (objective M (fun _ => 1) '' convexBody M a) ∧
      ∃ y ∈ convexBody M a, objective M (fun _ => 1) y = val M a := by
  have hfc : IsCompact (feasible M) := by
    have : feasible M = Set.pi Set.univ M.K := by ext x; simp [feasible]
    rw [this]; exact isCompact_univ_pi M.compact
  have hfne : (feasible M).Nonempty := by
    choose p hp using M.nonempty
    exact ⟨p, fun i => hp i⟩
  obtain ⟨x0, hx0, hmax⟩ := hfc.exists_isMaxOn hfne (objective_cont M a).continuousOn
  have hgreat : IsGreatest (objective M a '' feasible M) (objective M a x0) :=
    ⟨⟨x0, hx0, rfl⟩, by rintro _ ⟨x, hx, rfl⟩; exact hmax hx⟩
  have hval : val M a = objective M a x0 := hgreat.csSup_eq
  have hmem : (fun i => a i • x0 i) ∈ convexBody M a := fun i =>
    ⟨x0 i, subset_convexHull ℝ _ (hx0 i), rfl⟩
  have hF : objective M (fun _ => 1) (fun i => a i • x0 i) = val M a := by
    rw [hval]; exact (objective_scale M a x0).symm
  refine ⟨?_, ⟨_, hmem, hF⟩⟩
  have hg : IsGreatest (objective M (fun _ => 1) '' convexBody M a) (val M a) := by
    refine ⟨⟨_, hmem, hF⟩, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    choose x hx hxy using hy
    have : y = fun i => a i • x i := funext fun i => (hxy i).symm
    subst this
    rw [← objective_scale]
    exact bound M a (val M a) (fun z hz => by
      rw [hval]; exact hmax hz) Finset.univ x hx (by simp)
  exact hg.csSup_eq.symm
end HindsightGain.Uniform
end

theorem solution : type_of% @HindsightGain.Uniform.chk_lemma_2_1 := @HindsightGain.Uniform.chk_lemma_2_1
