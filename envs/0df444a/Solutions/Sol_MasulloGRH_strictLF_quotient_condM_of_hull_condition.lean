-- Prove2me | solution 1 for MasulloGRH.strictLF_quotient_condM_of_hull_condition
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:03:18.082179+00:00
-- url     : https://prove2.me/submissions/58611dc2-2794-46c1-9362-fcdbd71c6d64

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

open MasulloGRH Topology Filter

universe u

namespace HullCondMAux

/-- The seminorm `c • p` for a real `c ≥ 0`. -/
noncomputable def sc {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) : Seminorm ℂ X :=
  let c' : NNReal := ⟨c, hc⟩
  c' • p

theorem sc_apply {X : Type*} [AddCommGroup X] [Module ℂ X] (c : ℝ) (hc : 0 ≤ c)
    (p : Seminorm ℂ X) (x : X) : sc c hc p x = c * p x := rfl

/-- A positively homogeneous function bounded by `C` on the open unit ball of a seminorm `s`
is bounded by `C * s`. -/
theorem homog_bound {X : Type*} [AddCommGroup X] [Module ℂ X] (s : Seminorm ℂ X) (f : X → ℝ)
    (hf : ∀ (c : ℝ) (x : X), 0 < c → f ((c : ℂ) • x) = c * f x) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x, s x < 1 → f x ≤ C) (x : X) : f x ≤ C * s x := by
  by_contra hlt
  rw [not_le] at hlt
  have hs0 : 0 ≤ s x := apply_nonneg s x
  have hdpos : 0 < f x - C * s x := by linarith
  have hC1 : 0 < C + 1 := by linarith
  have hεpos : 0 < (f x - C * s x) / (C + 1) := div_pos hdpos hC1
  set ε := (f x - C * s x) / (C + 1) with hε
  have hb : 0 < s x + ε := by linarith
  have hsx : s ((((s x + ε)⁻¹ : ℝ) : ℂ) • x) < 1 := by
    rw [map_smul_eq_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.2 hb.le),
      inv_mul_lt_iff₀ hb]
    linarith
  have h1 := h _ hsx
  rw [hf _ _ (inv_pos.2 hb), inv_mul_le_iff₀ hb] at h1
  have h3 : C * ε < f x - C * s x := by
    have : ε * (C + 1) = f x - C * s x := by
      rw [hε]; field_simp
    nlinarith
  nlinarith

/-- A `0`-neighbourhood of a locally convex space contains the open unit ball of a continuous
seminorm. -/
theorem exists_seminorm_ball_subset {X : Type u} [AddCommGroup X] [Module ℂ X]
    [t : TopologicalSpace X] (h : IsLocallyConvexTopology X t) {U : Set X}
    (hU : U ∈ 𝓝 (0 : X)) :
    ∃ p : Seminorm ℂ X, Continuous p ∧ ∀ x, p x < 1 → x ∈ U := by
  obtain ⟨ι, _, P, hP⟩ := h
  have hadd : IsTopologicalAddGroup X := hP.topologicalAddGroup
  have hsmul : ContinuousSMul ℂ X := hP.continuousSMul
  obtain ⟨⟨s, ρ⟩, hρ, hsub⟩ := hP.hasBasis_zero_ball.mem_iff.1 hU
  have hρ : 0 < ρ := hρ
  obtain ⟨p0, hp0⟩ : ∃ p : Seminorm ℂ X, p = s.sup P := ⟨_, rfl⟩
  have hsub : p0.ball 0 ρ ⊆ U := by rw [hp0]; exact hsub
  have hsc : Continuous p0 := by
    rw [hp0]
    exact Seminorm.continuous (r := ρ) (hP.hasBasis_zero_ball.mem_of_mem (i := (s, ρ)) hρ)
  refine ⟨sc ρ⁻¹ (inv_pos.2 hρ).le p0, ?_, ?_⟩
  · have : (fun x => sc ρ⁻¹ (inv_pos.2 hρ).le p0 x) = fun x => ρ⁻¹ * p0 x :=
      funext fun x => sc_apply _ _ _ _
    change Continuous (fun x => sc ρ⁻¹ (inv_pos.2 hρ).le p0 x)
    rw [this]
    exact continuous_const.mul hsc
  · intro x hx
    apply hsub
    rw [Seminorm.mem_ball_zero]
    rw [sc_apply, inv_mul_lt_iff₀ hρ] at hx
    simpa using hx


theorem lc_of_polynormable {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : @PolynormableSpace ℂ X _ _ _ t) : IsLocallyConvexTopology X t := by
  letI := t
  exact ⟨{p : Seminorm ℂ X // Continuous p},
    ⟨⟨0, continuous_const⟩⟩, fun p => p.1,
    PolynormableSpace.withSeminorms ℂ X⟩

theorem polynormable_of_lc {X : Type u} [AddCommGroup X] [Module ℂ X] (t : TopologicalSpace X)
    (h : IsLocallyConvexTopology X t) : @PolynormableSpace ℂ X _ _ _ t := by
  obtain ⟨ι, _, p, hp⟩ := h
  exact hp.toPolynormableSpace

/-- A `0`-neighbourhood `W` of a subspace `Y` (with the induced topology) of a locally convex
space contains the trace of `N + N` for a balanced convex `0`-neighbourhood `N` of the space. -/
theorem exists_nhds_add_subset {E : Type u} [AddCommGroup E] [Module ℂ E]
    [t : TopologicalSpace E] (hLC : IsLocallyConvexTopology E t) (Y : Submodule ℂ E)
    (W : Set Y) (hW : W ∈ 𝓝 (0 : Y)) :
    ∃ N : Set E, N ∈ 𝓝 (0 : E) ∧ Balanced ℂ N ∧ Convex ℝ N ∧
      ∀ a ∈ N, ∀ b ∈ N, ∀ h : a + b ∈ Y, (⟨a + b, h⟩ : Y) ∈ W := by
  obtain ⟨N', hN', hsub⟩ := (mem_nhds_subtype (Y : Set E) (0 : Y) W).1 hW
  have hN'' : N' ∈ 𝓝 (0 : E) := hN'
  obtain ⟨p, hpc, hp⟩ := exists_seminorm_ball_subset hLC hN''
  refine ⟨p.ball 0 (1 / 2), ?_, p.balanced_ball_zero _, p.convex_ball _ _, ?_⟩
  · have h1 : {x : E | p x < 1 / 2} ∈ 𝓝 (0 : E) :=
      (isOpen_lt hpc continuous_const).mem_nhds (by simp)
    refine Filter.mem_of_superset h1 fun x hx => ?_
    rw [Seminorm.mem_ball_zero]
    exact hx
  · intro a ha b hb h
    rw [Seminorm.mem_ball_zero] at ha hb
    apply hsub
    change a + b ∈ N'
    apply hp
    have := map_add_le_add p a b
    linarith

end HullCondMAux

open HullCondMAux in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n) (hX : ∀ n, IsFrechet (X n) ∧ IsNuclear (X n))
    (htop : ‹TopologicalSpace E› =
      sInf {t | IsLocallyConvexTopology E t ∧ ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hhull : ∀ W : ∀ k, Set (X k), (∀ k, W k ∈ nhds (0 : X k)) →
      ∃ O : ∀ k, Set (X k), (∀ k, O k ∈ nhds (0 : X k)) ∧
        ∀ v ∈ V, v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, Subtype.val '' O k)) →
          v ∈ convexHull ℝ (balancedHull ℂ (⋃ k, (Subtype.val '' W k) ∩ (V : Set E)))) :
    ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ nhds (0 : X n), ∀ k : ℕ, m ≤ k →
      ∀ W ∈ nhds (0 : X m), ∃ W' ∈ nhds (0 : X k),
        ∀ x ∈ U, ∀ y ∈ W', ((x : E) - (y : E)) ∈ V → ∃ w ∈ W, ((x : E) - (w : E)) ∈ V := by
  -- `E` is a locally convex topological vector space
  have hP : PolynormableSpace ℂ E := by
    rw [htop]
    exact PolynormableSpace.sInf fun t ht => polynormable_of_lc t ht.1
  have hLC : IsLocallyConvexTopology E ‹TopologicalSpace E› := lc_of_polynormable _ hP
  have hadd : IsTopologicalAddGroup E := (PolynormableSpace.withSeminorms ℂ E).topologicalAddGroup
  have hsmul : ContinuousSMul ℂ E := (PolynormableSpace.withSeminorms ℂ E).continuousSMul
  intro n
  by_contra hcon
  -- a countable basis of `0`-neighbourhoods of the metrizable space `X n`
  haveI : TopologicalSpace.MetrizableSpace (X n) := (hX n).1.2.2
  obtain ⟨Ub, hUb⟩ := (𝓝 (0 : X n)).exists_antitone_basis
  have hcon' : ∀ (j : ℕ) (U : Set (X n)), U ∈ 𝓝 (0 : X n) → ∃ k, n + j ≤ k ∧
      ∃ W ∈ 𝓝 (0 : X (n + j)), ∀ W' ∈ 𝓝 (0 : X k), ∃ x ∈ U, ∃ y ∈ W',
        ((x : E) - (y : E)) ∈ V ∧ ∀ w ∈ W, ((x : E) - (w : E)) ∉ V := by
    intro j U hU
    by_contra h
    apply hcon
    refine ⟨n + j, Nat.le_add_right n j, U, hU, fun k hk W hW => ?_⟩
    by_contra h2
    apply h
    refine ⟨k, hk, W, hW, fun W' hW' => ?_⟩
    by_contra h3
    apply h2
    refine ⟨W', hW', fun x hx y hy hxy => ?_⟩
    by_contra h4
    apply h3
    exact ⟨x, hx, y, hy, hxy, fun w hw hw' => h4 ⟨w, hw, hw'⟩⟩
  choose k hk W hW hbad using fun j : ℕ =>
    hcon' j (Ub j) (hUb.toHasBasis.mem_of_mem trivial)
  choose N hN0 hNbal hNconv hNW using fun j : ℕ =>
    exists_nhds_add_subset hLC (X (n + j)) (W j) (hW j)
  -- the diagonal family of neighbourhoods
  let Wt : ∀ i, Set (X i) := fun i => {z : X i | ∀ j, n + j ≤ i → (z : E) ∈ N j}
  have hWt : ∀ i, Wt i ∈ 𝓝 (0 : X i) := by
    intro i
    have h1 : (⋂ j ∈ Finset.range (i + 1), {z : X i | n + j ≤ i → (z : E) ∈ N j}) ∈
        𝓝 (0 : X i) := by
      refine (Filter.biInter_finset_mem (Finset.range (i + 1))).2 fun j _ => ?_
      by_cases hji : n + j ≤ i
      · have h2 : {z : X i | (z : E) ∈ N j} ∈ 𝓝 (0 : X i) :=
          continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hN0 j)
        exact Filter.mem_of_superset h2 fun z hz _ => hz
      · exact Filter.mem_of_superset Filter.univ_mem fun z _ h => absurd h hji
    refine Filter.mem_of_superset h1 fun z hz j hji => ?_
    have h3 := Set.mem_iInter₂.1 hz j (Finset.mem_range.2 (by omega))
    exact h3 hji
  obtain ⟨O, hO, hOV⟩ := hhull Wt hWt
  -- choose the level `j` with `Ub j ⊆ (1/2) • O n`
  have h2O : {x : X n | (2 : ℂ) • x ∈ O n} ∈ 𝓝 (0 : X n) :=
    (continuous_const_smul (2 : ℂ)).continuousAt.preimage_mem_nhds (by simpa using hO n)
  obtain ⟨j, -, hj⟩ := hUb.toHasBasis.mem_iff.1 h2O
  have hW' : {y : X (k j) | (2 : ℂ) • y ∈ O (k j) ∧ (y : E) ∈ N j} ∈ 𝓝 (0 : X (k j)) := by
    refine Filter.inter_mem ?_ ?_
    · exact (continuous_const_smul (2 : ℂ)).continuousAt.preimage_mem_nhds
        (by simpa using hO (k j))
    · exact continuous_subtype_val.continuousAt.preimage_mem_nhds (by simpa using hN0 j)
  obtain ⟨x, hxU, y, hyW', hxyV, hno⟩ := hbad j _ hW'
  -- `x - y` lies in the hull of the `O i`
  have hv : (x : E) - (y : E) ∈
      convexHull ℝ (balancedHull ℂ (⋃ i, Subtype.val '' O i)) := by
    have ha : (2 : ℂ) • (x : E) ∈ balancedHull ℂ (⋃ i, Subtype.val '' O i) :=
      subset_balancedHull ℂ (Set.mem_iUnion.2 ⟨n, ⟨(2 : ℂ) • x, hj hxU, rfl⟩⟩)
    have hb0 : (2 : ℂ) • (y : E) ∈ balancedHull ℂ (⋃ i, Subtype.val '' O i) :=
      subset_balancedHull ℂ (Set.mem_iUnion.2 ⟨k j, ⟨(2 : ℂ) • y, hyW'.1, rfl⟩⟩)
    have hb : (-1 : ℂ) • ((2 : ℂ) • (y : E)) ∈ balancedHull ℂ (⋃ i, Subtype.val '' O i) :=
      (balancedHull.balanced _).smul_mem (by simp) hb0
    have h1 := convex_convexHull ℝ _ (subset_convexHull ℝ _ ha) (subset_convexHull ℝ _ hb)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have e : (1 / 2 : ℝ) • ((2 : ℂ) • (x : E)) + (1 / 2 : ℝ) • ((-1 : ℂ) • ((2 : ℂ) • (y : E))) =
        (x : E) - (y : E) := by
      rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul, smul_smul]
      have h2 : ((1 / 2 : ℝ) : ℂ) * 2 = 1 := by push_cast; norm_num
      have h3 : ((1 / 2 : ℝ) : ℂ) * -1 * 2 = -1 := by push_cast; norm_num
      rw [h2, h3, one_smul, neg_one_smul, sub_eq_add_neg]
    rw [e] at h1
    exact h1
  have hv' := hOV _ hxyV hv
  -- the hull of the traces of the `Wt i` on `V` lies in `(V ∩ X (n+j)) + N j`
  let Z : Set E := {z | ∃ a : E, (a ∈ V ∧ a ∈ X (n + j)) ∧ ∃ b ∈ N j, z = a + b}
  have h0N : (0 : E) ∈ N j := mem_of_mem_nhds (hN0 j)
  have hZconv : Convex ℝ Z := by
    rintro _ ⟨a₁, ⟨ha₁V, ha₁X⟩, b₁, hb₁, rfl⟩ _ ⟨a₂, ⟨ha₂V, ha₂X⟩, b₂, hb₂, rfl⟩ s t hs ht hst
    refine ⟨s • a₁ + t • a₂, ⟨?_, ?_⟩, s • b₁ + t • b₂, hNconv j hb₁ hb₂ hs ht hst, ?_⟩
    · rw [← Complex.coe_smul, ← Complex.coe_smul]
      exact V.add_mem (V.smul_mem _ ha₁V) (V.smul_mem _ ha₂V)
    · rw [← Complex.coe_smul, ← Complex.coe_smul]
      exact (X (n + j)).add_mem ((X (n + j)).smul_mem _ ha₁X) ((X (n + j)).smul_mem _ ha₂X)
    · simp only [smul_add]
      abel
  have hZbal : Balanced ℂ Z := by
    intro c hc
    rintro _ ⟨_, ⟨a, ⟨haV, haX⟩, b, hb, rfl⟩, rfl⟩
    exact ⟨c • a, ⟨V.smul_mem _ haV, (X (n + j)).smul_mem _ haX⟩, c • b,
      (hNbal j).smul_mem hc hb, smul_add c a b⟩
  have hSZ : (⋃ i, (Subtype.val '' Wt i) ∩ (V : Set E)) ⊆ Z := by
    intro z hz
    obtain ⟨i, ⟨w, hw, rfl⟩, hzV⟩ := Set.mem_iUnion.1 hz
    by_cases hi : n + j ≤ i
    · exact ⟨0, ⟨V.zero_mem, (X (n + j)).zero_mem⟩, (w : E), hw j hi, by rw [zero_add]⟩
    · exact ⟨(w : E), ⟨hzV, hmono (by omega : i ≤ n + j) w.2⟩, 0, h0N, by rw [add_zero]⟩
  have hvZ : (x : E) - (y : E) ∈ Z :=
    convexHull_min (hZbal.balancedHull_subset_of_subset hSZ) hZconv hv'
  obtain ⟨a, ⟨haV, haX⟩, b, hb, hvab⟩ := hvZ
  -- the contradiction
  have hxX : (x : E) ∈ X (n + j) := hmono (Nat.le_add_right n j) x.2
  have hyb : (y : E) + b = (x : E) - a := by
    have : (x : E) = (y : E) + (a + b) := by rw [← hvab]; abel
    rw [this]; abel
  have hmem : (y : E) + b ∈ X (n + j) := by
    rw [hyb]
    exact (X (n + j)).sub_mem hxX haX
  have hwW : (⟨(y : E) + b, hmem⟩ : X (n + j)) ∈ W j := hNW j _ hyW'.2 _ hb hmem
  refine hno _ hwW ?_
  change (x : E) - ((y : E) + b) ∈ V
  rw [hyb]
  simpa using haV
