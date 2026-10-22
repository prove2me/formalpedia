-- Prove2me | solution 1 for MyersonBargaining.NashSolution.theorem1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:00:42.451891+00:00
-- url     : https://prove2.me/submissions/e618f7f4-d46e-4538-9a26-18e6be5cff42

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining



namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

lemma t1_Z_comb (G : Problem ι A C) (i : ι) (π₁ π₂ : C → (∀ i, A i) → ℝ) (s t : ℝ)
    (b a : A i) :
    Z G i (fun c α => s * π₁ c α + t * π₂ c α) b a = s * Z G i π₁ b a + t * Z G i π₂ b a := by
  unfold Z
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring

lemma t1_const_bic (G : Problem ι A C) (cstar : C) :
    IsChoiceMechanism (constMech (A := A) cstar) ∧ IsBIC G (constMech (A := A) cstar) := by
  refine ⟨⟨fun c s => by unfold constMech; split_ifs <;> norm_num, fun s => by simp [constMech]⟩, ?_⟩
  intro i a b
  simp [Z, constMech]

lemma t1_Z_cont (G : Problem ι A C) (i : ι) (b a : A i) :
    Continuous (fun π : C → (∀ i, A i) → ℝ => Z G i π b a) := by
  unfold Z
  fun_prop

lemma t1_V_cont (G : Problem ι A C) :
    Continuous (fun π : C → (∀ i, A i) → ℝ => V G π) := by
  apply continuous_pi
  intro k
  exact t1_Z_cont G k.1 k.2 k.2

theorem theorem1_core (G : Problem ι A C) :
    (FStar G).Nonempty ∧ Convex ℝ (FStar G) ∧ IsCompact (FStar G) ∧
      FStar G ⊆ F G := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨c⟩ := (inferInstance : Nonempty C)
    exact ⟨_, constMech c, (t1_const_bic G c).1, (t1_const_bic G c).2, rfl⟩
  · rintro x ⟨π₁, h1c, h1b, rfl⟩ y ⟨π₂, h2c, h2b, rfl⟩ s t hs ht hst
    refine ⟨fun c α => s * π₁ c α + t * π₂ c α, ⟨?_, ?_⟩, ?_, ?_⟩
    · intro c α
      have := h1c.1 c α
      have := h2c.1 c α
      positivity
    · intro α
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1c.2, h2c.2]
      linarith
    · intro i a b
      rw [t1_Z_comb, t1_Z_comb]
      have := h1b i a b
      have := h2b i a b
      nlinarith
    · funext k
      simp only [V, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact t1_Z_comb G k.1 π₁ π₂ s t k.2 k.2
  · have hM : IsCompact {π : C → (∀ i, A i) → ℝ | IsChoiceMechanism π ∧ IsBIC G π} := by
      have hbox : IsCompact (Set.pi Set.univ
          (fun _ : C => Set.pi Set.univ (fun _ : (∀ i, A i) => Set.Icc (0:ℝ) 1))) :=
        isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
      apply hbox.of_isClosed_subset
      · have e : {π : C → (∀ i, A i) → ℝ | IsChoiceMechanism π ∧ IsBIC G π} =
            (⋂ c, ⋂ s, {π : C → (∀ i, A i) → ℝ | 0 ≤ π c s}) ∩
            (⋂ s, {π : C → (∀ i, A i) → ℝ | ∑ c, π c s = 1}) ∩
            (⋂ i, ⋂ a : A i, ⋂ b : A i,
              {π : C → (∀ i, A i) → ℝ | Z G i π b a ≤ Z G i π a a}) := by
          ext π
          simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, IsChoiceMechanism,
            IsBIC, and_assoc]
        rw [e]
        refine IsClosed.inter (IsClosed.inter ?_ ?_) ?_
        · refine isClosed_iInter (fun c => isClosed_iInter (fun s => ?_))
          exact isClosed_le continuous_const (by fun_prop)
        · refine isClosed_iInter (fun s => ?_)
          exact isClosed_eq (by fun_prop) continuous_const
        · refine isClosed_iInter (fun i => isClosed_iInter (fun a => isClosed_iInter (fun b => ?_)))
          exact isClosed_le (t1_Z_cont G i b a) (t1_Z_cont G i a a)
      · rintro π ⟨hc, _⟩
        simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
        intro c s
        refine ⟨hc.1 c s, ?_⟩
        rw [← hc.2 s]
        exact Finset.single_le_sum (fun c' _ => hc.1 c' s) (Finset.mem_univ c)
    have := hM.image (t1_V_cont G)
    convert this using 1
    ext x
    simp only [FStar, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨π, h1, h2, h3⟩; exact ⟨π, ⟨h1, h2⟩, h3⟩
    · rintro ⟨π, ⟨h1, h2⟩, h3⟩; exact ⟨π, h1, h2, h3⟩
  · rintro x ⟨π, h1, _, h3⟩
    exact ⟨π, h1, h3⟩

end MyersonBargaining.NashSolution

open MyersonBargaining.NashSolution


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
    (G : Problem ι A C) :
    (FStar G).Nonempty ∧ Convex ℝ (FStar G) ∧ IsCompact (FStar G) ∧
      FStar G ⊆ F G := by
  exact theorem1_core G
