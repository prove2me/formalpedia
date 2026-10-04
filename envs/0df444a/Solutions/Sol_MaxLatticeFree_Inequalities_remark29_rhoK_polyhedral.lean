-- Prove2me | solution 1 for MaxLatticeFree.Inequalities.remark29_rhoK_polyhedral
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T18:55:38.728125+00:00
-- url     : https://prove2.me/submissions/89ba350b-ea59-41f8-a875-52039126e18b

import Mathlib
import Definitions.Def_MaxLatticeFree_Inequalities_RelaxationModel
import Definitions.Def_MaxLatticeFree_Inequalities_Polar

open scoped RealInnerProductSpace

set_option autoImplicit false

open MaxLatticeFree.Inequalities RealInnerProductSpace in
theorem solution {q t : ℕ} [NeZero t] (W : Submodule ℝ (EuclideanSpace ℝ (Fin q)))
    (K : Set (EuclideanSpace ℝ (Fin q))) (a : Fin t → EuclideanSpace ℝ (Fin q)) (ha : ∀ i, a i ∈ W)
    (hK : K = {r | r ∈ W ∧ ∀ i, ⟪a i, r⟫ ≤ 1})
    (h0 : (0 : EuclideanSpace ℝ (Fin q)) ∈ intRel (W : Set (EuclideanSpace ℝ (Fin q))) K)
    (htight : ∀ i, ∃ r ∈ K, ⟪a i, r⟫ = 1) :
    ∀ r : W, rhoK W K r = Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) := by
  intro r
  subst hK
  have hle : ∀ i, ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫ ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) :=
    fun i => Finset.le_sup' (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) (Finset.mem_univ i)
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫)
  generalize hMdef : Finset.univ.sup' Finset.univ_nonempty
    (fun i => ⟪a i, (r : EuclideanSpace ℝ (Fin q))⟫) = M at hle hj ⊢
  unfold rhoK
  apply IsGreatest.csSup_eq
  constructor
  · refine ⟨a j, ?_, ?_⟩
    · simp only [Khat, polarW, Set.mem_setOf_eq]
      refine ⟨⟨ha j, ?_⟩, ?_⟩
      · rintro x ⟨_, hx⟩
        rw [real_inner_comm]; exact hx j
      · obtain ⟨x, hx, hx1⟩ := htight j
        exact ⟨x, hx, by rw [real_inner_comm]; exact hx1⟩
    · simp only
      rw [real_inner_comm, hj]
  · rintro v ⟨y, hy, rfl⟩
    simp only [Khat, polarW, Set.mem_setOf_eq] at hy
    obtain ⟨⟨hyW, hypol⟩, x, ⟨hxW, hxa⟩, hxy⟩ := hy
    by_contra hcon
    push_neg at hcon
    have hs0 : (0 : ℝ) < 1 / (|M| + 1) := by positivity
    have hsM : 1 / (|M| + 1) * M ≤ 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith [le_abs_self M]
    set s : ℝ := 1 / (|M| + 1) with hs
    have hz : x + s • ((r : EuclideanSpace ℝ (Fin q)) - M • x) ∈
        {r | r ∈ W ∧ ∀ i, ⟪a i, r⟫ ≤ 1} := by
      refine ⟨W.add_mem hxW (W.smul_mem _ (W.sub_mem r.2 (W.smul_mem _ hxW))), fun i => ?_⟩
      simp only [inner_add_right, real_inner_smul_right, inner_sub_right]
      have h1 := hxa i
      have h2 := hle i
      nlinarith [mul_nonneg hs0.le (sub_nonneg.2 (hle i)),
        mul_nonneg (sub_nonneg.2 hsM) (sub_nonneg.2 (hxa i))]
    have hc := hypol _ hz
    simp only [inner_add_left, real_inner_smul_left, inner_sub_left] at hc
    rw [hxy] at hc
    nlinarith [mul_pos hs0 (sub_pos.2 hcon)]
