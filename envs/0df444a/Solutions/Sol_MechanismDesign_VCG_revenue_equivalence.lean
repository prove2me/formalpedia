-- Prove2me | solution 1 for MechanismDesign.VCG.revenue_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:11:55.999983+00:00
-- url     : https://prove2.me/submissions/02e951cc-0056-4764-a1b2-b05c03aa00c0

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model



namespace MechanismDesign.VCG

open Set Filter Topology

lemma re_bracket (K : ℝ → ℝ → ℝ) (H : ℝ → ℝ)
    (hH : ∀ s ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1, K s r - K s s ≤ H r - H s) (m : ℕ) :
    let s : ℕ → ℝ := fun j => (j : ℝ) / ((m : ℝ) + 1)
    ∑ j ∈ Finset.range (m + 1), (K (s j) (s (j + 1)) - K (s j) (s j)) ≤ H 1 - H 0 ∧
      H 1 - H 0 ≤ ∑ j ∈ Finset.range (m + 1), (K (s (j + 1)) (s (j + 1)) - K (s (j + 1)) (s j)) := by
  intro s
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmem : ∀ j, j ≤ m + 1 → s j ∈ Icc (0:ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN]
    exact_mod_cast hj
  have htel : ∑ j ∈ Finset.range (m + 1), (H (s (j + 1)) - H (s j)) = H 1 - H 0 := by
    rw [Finset.sum_range_sub (fun j => H (s j))]
    simp only [s]
    congr 2
    · push_cast; field_simp
    · simp
  constructor
  · rw [← htel]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact hH _ (hmem j (by omega)) _ (hmem (j + 1) (by omega))
  · rw [← htel]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have := hH _ (hmem (j + 1) (by omega)) _ (hmem j (by omega))
    linarith

lemma re_conv_step (K : ℝ → ℝ → ℝ)
    (hconv : ∀ s ∈ Icc (0:ℝ) 1, ConvexOn ℝ (Icc (0:ℝ) 1) (K s)) (m : ℕ) (j : ℕ) (hj : j + 2 ≤ m + 1) :
    let s : ℕ → ℝ := fun j => (j : ℝ) / ((m : ℝ) + 1)
    K (s (j + 1)) (s (j + 1)) - K (s (j + 1)) (s j) ≤ K (s (j + 1)) (s (j + 2)) - K (s (j + 1)) (s (j + 1)) := by
  intro s
  have hN : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hmem : ∀ j, j ≤ m + 1 → s j ∈ Icc (0:ℝ) 1 := by
    intro j hj
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN]
    exact_mod_cast hj
  have hc := (hconv _ (hmem (j + 1) (by omega))).2 (hmem j (by omega)) (hmem (j + 2) (by omega))
    (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hmid : (1/2 : ℝ) • s j + (1/2 : ℝ) • s (j + 2) = s (j + 1) := by
    simp only [s, smul_eq_mul]; push_cast; field_simp; ring
  rw [hmid] at hc
  simp only [smul_eq_mul] at hc
  linarith

lemma re_real1d (K : ℝ → ℝ → ℝ) (H H' : ℝ → ℝ)
    (hconv : ∀ s ∈ Icc (0:ℝ) 1, ConvexOn ℝ (Icc (0:ℝ) 1) (K s))
    (hc0 : ContinuousWithinAt (K 0) (Icc 0 1) 0) (hc1 : ContinuousWithinAt (K 1) (Icc 0 1) 1)
    (hH : ∀ s ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1, K s r - K s s ≤ H r - H s)
    (hH' : ∀ s ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1, K s r - K s s ≤ H' r - H' s) :
    H 1 - H 0 = H' 1 - H' 0 := by
  -- error bound for each m
  have hbound : ∀ m : ℕ, |(H 1 - H 0) - (H' 1 - H' 0)| ≤
      (K 1 1 - K 1 ((m : ℝ) / ((m : ℝ) + 1))) - (K 0 (1 / ((m : ℝ) + 1)) - K 0 0) := by
    intro m
    obtain ⟨h1, h2⟩ := re_bracket K H hH m
    obtain ⟨h1', h2'⟩ := re_bracket K H' hH' m
    set s : ℕ → ℝ := fun j => (j : ℝ) / ((m : ℝ) + 1) with hs
    have hU : ∑ j ∈ Finset.range (m + 1), (K (s (j + 1)) (s (j + 1)) - K (s (j + 1)) (s j)) ≤
        ∑ j ∈ Finset.range (m + 1), (K (s j) (s (j + 1)) - K (s j) (s j))
          + (K (s (m + 1)) (s (m + 1)) - K (s (m + 1)) (s m)) - (K (s 0) (s 1) - K (s 0) (s 0)) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      have : ∑ j ∈ Finset.range m, (K (s (j + 1)) (s (j + 1)) - K (s (j + 1)) (s j)) ≤
          ∑ j ∈ Finset.range m, (K (s (j + 1)) (s (j + 1 + 1)) - K (s (j + 1)) (s (j + 1))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        exact re_conv_step K hconv m j (by omega)
      simp only [zero_add] at this ⊢
      linarith
    have hsm1 : s (m + 1) = 1 := by simp only [s]; push_cast; field_simp
    have hs0 : s 0 = 0 := by simp [s]
    have hs1 : s 1 = 1 / ((m : ℝ) + 1) := by simp [s]
    have hsm : s m = (m : ℝ) / ((m : ℝ) + 1) := rfl
    rw [hsm1, hs0, hs1, hsm] at hU
    rw [abs_le]
    constructor <;> linarith
  -- limits
  have ht0 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝[Icc 0 1] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall (fun m => ?_)⟩
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have ht1 : Tendsto (fun m : ℕ => (m : ℝ) / ((m : ℝ) + 1)) atTop (𝓝[Icc 0 1] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (1 : ℝ)
      simp only [sub_zero] at this
      refine this.congr (fun m => ?_)
      field_simp
      ring
    · refine Eventually.of_forall (fun m => ⟨by positivity, ?_⟩)
      rw [div_le_one (by positivity)]
      linarith
  have hlim : Tendsto (fun m : ℕ => (K 1 1 - K 1 ((m : ℝ) / ((m : ℝ) + 1))) -
      (K 0 (1 / ((m : ℝ) + 1)) - K 0 0)) atTop (𝓝 ((K 1 1 - K 1 1) - (K 0 0 - K 0 0))) := by
    apply Tendsto.sub
    · exact tendsto_const_nhds.sub (hc1.tendsto.comp ht1)
    · exact (hc0.tendsto.comp ht0).sub tendsto_const_nhds
  simp only [sub_self] at hlim
  have := ge_of_tendsto' hlim hbound
  have h0 : |(H 1 - H 0) - (H' 1 - H' 0)| = 0 := le_antisymm this (abs_nonneg _)
  rw [abs_eq_zero] at h0
  linarith

lemma re_agent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (S : Set E) (hS : Convex ℝ S)
    (F : S → E → ℝ) (hFc : ∀ y, ConvexOn ℝ S (F y)) (hFt : ∀ y, ContinuousOn (F y) S)
    (c c' : S → ℝ) (hIC : ∀ x y : S, F x x - c x ≥ F y x - c y)
    (hIC' : ∀ x y : S, F x x - c' x ≥ F y x - c' y) (x y : S) :
    c x - c' x = c y - c' y := by
  let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (x : E) (y : E)
  have hL : ∀ r ∈ Icc (0:ℝ) 1, L r ∈ S := fun r hr => hS.lineMap_mem x.2 y.2 hr
  let p : ℝ → S := fun s => if h : s ∈ Icc (0:ℝ) 1 then ⟨L s, hL s h⟩ else x
  have hp : ∀ s ∈ Icc (0:ℝ) 1, ((p s : S) : E) = L s := by
    intro s hs; simp only [p, dif_pos hs]
  have hp0 : p 0 = x := by
    apply Subtype.ext; rw [hp 0 ⟨le_rfl, zero_le_one⟩]; simp [L]
  have hp1 : p 1 = y := by
    apply Subtype.ext; rw [hp 1 ⟨zero_le_one, le_rfl⟩]; simp [L]
  let K : ℝ → ℝ → ℝ := fun s r => F (p s) (L r)
  have hconv : ∀ s ∈ Icc (0:ℝ) 1, ConvexOn ℝ (Icc (0:ℝ) 1) (K s) := by
    intro s _
    exact ((hFc (p s)).comp_affineMap L).subset (fun r hr => hL r hr) (convex_Icc 0 1)
  have hcont : ∀ s, ContinuousOn (K s) (Icc (0:ℝ) 1) := by
    intro s
    exact (hFt (p s)).comp AffineMap.lineMap_continuous.continuousOn (fun r hr => hL r hr)
  have hbr : ∀ (d : S → ℝ), (∀ x y : S, F x x - d x ≥ F y x - d y) →
      ∀ s ∈ Icc (0:ℝ) 1, ∀ r ∈ Icc (0:ℝ) 1,
        K s r - K s s ≤ (F (p r) (L r) - d (p r)) - (F (p s) (L s) - d (p s)) := by
    intro d hd s hs r hr
    have := hd (p r) (p s)
    rw [hp r hr] at this
    simp only [K]
    linarith
  have key := re_real1d K (fun s => F (p s) (L s) - c (p s)) (fun s => F (p s) (L s) - c' (p s))
    hconv ((hcont 0).continuousWithinAt ⟨le_rfl, zero_le_one⟩)
    ((hcont 1).continuousWithinAt ⟨zero_le_one, le_rfl⟩) (hbr c hIC) (hbr c' hIC')
  simp only [hp0, hp1] at key
  linarith

theorem revenue_equivalence_core {ι A : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    (u : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hconv : ∀ i a, ConvexOn ℝ (S i) (u i a))
    (hcont : ∀ i a, ContinuousOn (u i a) (S i))
    (M : DirectMechanism (fun i => ↥(S i)) A)
    (hM : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M)
    (t' : ι → (∀ i, ↥(S i)) → ℝ) :
    DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) ⟨M.q, t'⟩ ↔
      ∀ i : ι, ∃ τ : Others (fun i => ↥(S i)) i → ℝ,
        ∀ θ : ∀ j, ↥(S j), t' i θ = M.t i θ + τ (restrict θ i) := by
  constructor
  · intro ht' i
    classical
    refine ⟨fun r => if h : ∃ θ : ∀ j, ↥(S j), restrict θ i = r then
      t' i (Classical.choose h) - M.t i (Classical.choose h) else 0, fun θ => ?_⟩
    have h : ∃ θ' : ∀ j, ↥(S j), restrict θ' i = restrict θ i := ⟨θ, rfl⟩
    simp only [dif_pos h]
    set θ0 := Classical.choose h with hθ0
    have hspec : restrict θ0 i = restrict θ i := Classical.choose_spec h
    have hθ0' : Function.update θ i (θ0 i) = θ0 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp
      · rw [Function.update_of_ne hj]
        exact (congrFun hspec ⟨j, hj⟩).symm
    have IC : ∀ (t : ι → (∀ i, ↥(S i)) → ℝ),
        DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) ⟨M.q, t⟩ →
        ∀ x y : S i, u i (M.q (Function.update θ i x)) x - t i (Function.update θ i x) ≥
          u i (M.q (Function.update θ i y)) x - t i (Function.update θ i y) := by
      intro t ht x y
      have := ht (Function.update θ i x) i y
      simp only [Function.update_self, Function.update_idem] at this
      exact this
    have hM' : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) ⟨M.q, M.t⟩ := hM
    have key := re_agent (S i) (hS i) (fun y z => u i (M.q (Function.update θ i y)) z)
      (fun y => hconv i _) (fun y => hcont i _)
      (fun y => M.t i (Function.update θ i y)) (fun y => t' i (Function.update θ i y))
      (IC M.t hM') (IC t' ht') (θ i) (θ0 i)
    simp only [Function.update_eq_self, hθ0'] at key
    linarith
  · intro hτ θ i x
    obtain ⟨τ, hτi⟩ := hτ i
    have hr : restrict (Function.update θ i x) i = restrict θ i := by
      funext j
      simp only [restrict, Function.update_of_ne j.2]
    have := hM θ i x
    simp only at this ⊢
    rw [hτi θ, hτi (Function.update θ i x), hr]
    linarith

end MechanismDesign.VCG

open MechanismDesign.VCG


theorem solution {ι A : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℕ)
    (S : ∀ i, Set (EuclideanSpace ℝ (Fin (d i)))) (hS : ∀ i, Convex ℝ (S i))
    (u : ∀ i, A → EuclideanSpace ℝ (Fin (d i)) → ℝ)
    (hconv : ∀ i a, ConvexOn ℝ (S i) (u i a))
    (hcont : ∀ i a, ContinuousOn (u i a) (S i))
    (M : DirectMechanism (fun i => ↥(S i)) A)
    (hM : DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) M)
    (t' : ι → (∀ i, ↥(S i)) → ℝ) :
    DSIC (Θ := fun i => ↥(S i)) (fun i a x => u i a x) ⟨M.q, t'⟩ ↔
      ∀ i : ι, ∃ τ : Others (fun i => ↥(S i)) i → ℝ,
        ∀ θ : ∀ j, ↥(S j), t' i θ = M.t i θ + τ (restrict θ i) := by
  exact revenue_equivalence_core d S hS u hconv hcont M hM t'
