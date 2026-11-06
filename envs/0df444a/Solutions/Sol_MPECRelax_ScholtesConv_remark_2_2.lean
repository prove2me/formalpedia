-- Prove2me | solution 1 for MPECRelax.ScholtesConv.remark_2_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T19:52:53.186317+00:00
-- url     : https://prove2.me/submissions/5de30e4a-a90a-4b7e-aae8-d6857cb46212

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP

open scoped RealInnerProductSpace

open MPECRelax.ScholtesConv in
theorem solution {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (P : NLP n ι κ) (x : E n)
    (hx : P.Feasible x) :
    P.IsMFCQ x ↔ ¬ P.PosLinDep x (P.activeSet x) Set.univ := by
  classical
  set a : ι → E n := fun i => gradient (P.g i) x with ha
  set b : κ → E n := fun j => gradient (P.h j) x with hb
  set I : Set ι := P.activeSet x
  constructor
  · -- MFCQ ⇒ positive-linear independence
    rintro ⟨hLI, d, hd_act, hd_eq⟩ ⟨α, β, hα0, hαI, -, hne, hsum⟩
    have hin := congrArg (fun v => ⟪v, d⟫) hsum
    simp only [inner_add_left, sum_inner, inner_smul_left, inner_zero_left,
      RCLike.conj_to_real] at hin
    have h2 : ∑ j, β j * ⟪gradient (P.h j) x, d⟫ = 0 :=
      Finset.sum_eq_zero fun j _ => by rw [hd_eq j, mul_zero]
    have hnp : ∀ i, α i * ⟪gradient (P.g i) x, d⟫ ≤ 0 := fun i => by
      by_cases hi : i ∈ P.activeSet x
      · exact mul_nonpos_of_nonneg_of_nonpos (hα0 i hi) (hd_act i hi).le
      · rw [hαI i hi, zero_mul]
    have h1 : ∑ i, α i * ⟪gradient (P.g i) x, d⟫ = 0 := by linarith
    have hα : α = 0 := funext fun i => by
      by_cases hi : i ∈ P.activeSet x
      · have := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hnp i)).mp h1 i (Finset.mem_univ i)
        exact (mul_eq_zero.mp this).resolve_right (hd_act i hi).ne
      · exact hαI i hi
    rw [hα] at hsum hne
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, zero_add] at hsum
    have hβ := Fintype.linearIndependent_iff.mp hLI β hsum
    rcases hne with ⟨i, hi⟩ | ⟨j, hj⟩
    · exact hi rfl
    · exact hj (hβ j)
  · -- positive-linear independence ⇒ MFCQ
    intro hPLI
    refine ⟨?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro β hβ j
      by_contra hj
      exact hPLI ⟨0, β, by simp, by simp, by simp, Or.inr ⟨j, hj⟩, by simpa using hβ⟩
    · -- separation of the convex hull of the active gradients from the span of the others
      let S : Set (ι → ℝ) := {α | (∀ i, 0 ≤ α i) ∧ (∀ i ∉ I, α i = 0) ∧ ∑ i, α i = 1}
      let L : (ι → ℝ) → E n := fun α => ∑ i, α i • a i
      let K : Set (E n) := L '' S
      let C : Submodule ℝ (E n) := Submodule.span ℝ (Set.range b)
      have hSconv : Convex ℝ S := by
        rintro α ⟨h1, h2, h3⟩ α' ⟨h1', h2', h3'⟩ s s' hs hs' hss
        refine ⟨fun i => ?_, fun i hi => ?_, ?_⟩
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact add_nonneg (mul_nonneg hs (h1 i)) (mul_nonneg hs' (h1' i))
        · simp [h2 i hi, h2' i hi]
        · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
            ← Finset.mul_sum, h3, h3', mul_one, hss]
      have hSclosed : IsClosed S := by
        have e1 : IsClosed {α : ι → ℝ | ∀ i, 0 ≤ α i} := by
          simp only [Set.setOf_forall]
          exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
        have e2 : IsClosed {α : ι → ℝ | ∀ i ∉ I, α i = 0} := by
          simp only [Set.setOf_forall]
          exact isClosed_iInter fun i => isClosed_iInter fun _ =>
            isClosed_eq (continuous_apply i) continuous_const
        have e3 : IsClosed {α : ι → ℝ | ∑ i, α i = 1} :=
          isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
        convert (e1.inter e2).inter e3 using 1
        ext α; simp [S, and_assoc]
      have hSsub : S ⊆ Set.Icc 0 1 := by
        rintro α ⟨h1, -, h3⟩
        refine ⟨fun i => h1 i, fun i => ?_⟩
        have := Finset.single_le_sum (fun j _ => h1 j) (Finset.mem_univ i)
        simp only [Pi.one_apply]; linarith
      have hScomp : IsCompact S := isCompact_Icc.of_isClosed_subset hSclosed hSsub
      have hLlin : IsLinearMap ℝ L := by
        constructor
        · intro α β; simp [L, add_smul, Finset.sum_add_distrib]
        · intro c α; simp [L, Finset.smul_sum, smul_smul]
      have hLcont : Continuous L := by
        simp only [L]; fun_prop
      have hKconv : Convex ℝ K := hSconv.is_linear_image hLlin
      have hKcomp : IsCompact K := hScomp.image hLcont
      have hCconv : Convex ℝ (C : Set (E n)) := C.convex
      have hCclosed : IsClosed (C : Set (E n)) := C.closed_of_finiteDimensional
      have hdisj : Disjoint K (C : Set (E n)) := by
        rw [Set.disjoint_left]
        rintro y ⟨α, ⟨h1, h2, h3⟩, rfl⟩ hy
        obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hy
        apply hPLI
        refine ⟨α, -β, fun i _ => h1 i, h2, by simp, Or.inl ?_, ?_⟩
        · by_contra hcon
          push Not at hcon
          simp [hcon] at h3
        · simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
          change L α + -∑ j, β j • b j = 0
          rw [hβ]; simp [L]
      obtain ⟨f, u, v, hfu, huv, hvf⟩ :=
        geometric_hahn_banach_compact_closed hKconv hKcomp hCconv hCclosed hdisj
      have hv0 : v < 0 := by simpa using hvf 0 C.zero_mem
      have hfC : ∀ y ∈ C, f y = 0 := by
        intro y hy
        by_contra hne
        have := hvf (((v - 1) / f y) • y) (C.smul_mem _ hy)
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at this
        linarith
      refine ⟨(InnerProductSpace.toDual ℝ (E n)).symm f, fun i hi => ?_, fun j => ?_⟩
      · have hmem : a i ∈ K := ⟨Pi.single i 1, ⟨fun j => by
            by_cases h : j = i
            · subst h; simp
            · simp [Pi.single_apply, h], fun j hj => by
            have : j ≠ i := fun h => hj (h ▸ hi)
            simp [Pi.single_apply, this], by simp⟩, by simp [L]⟩
        have : f (gradient (P.g i) x) < u := hfu _ hmem
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
        linarith
      · have hmem : b j ∈ C := Submodule.subset_span ⟨j, rfl⟩
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
        exact hfC _ hmem
