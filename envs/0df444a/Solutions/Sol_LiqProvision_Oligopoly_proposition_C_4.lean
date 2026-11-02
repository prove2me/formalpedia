-- Prove2me | solution 1 for LiqProvision.Oligopoly.proposition_C_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T23:25:49.353276+00:00
-- url     : https://prove2.me/submissions/863a1dad-00b1-40fd-ba1e-5cb4835fd4a8

import Mathlib

open Set Filter Topology Metric
open scoped NNReal

namespace LiqC4Aux

theorem clamp_lip (a b y₁ y₂ : ℝ) : |max a (min b y₁) - max a (min b y₂)| ≤ |y₁ - y₂| := by
  rw [max_comm a, max_comm a]
  refine (abs_max_sub_max_le_abs _ _ a).trans ?_
  have := abs_min_sub_min_le_max b y₁ b y₂
  simpa using this

/-- a positive quantity whose derivative is nonnegative while it is positive stays positive -/
theorem no_return (D D' : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) (hDc : ContinuousOn D (Icc a b))
    (hD : ∀ t ∈ Ioo a b, 0 < D t → HasDerivAt D (D' t) t ∧ 0 ≤ D' t) (ha : 0 < D a) :
    0 < D b := by
  by_contra hcon
  push Not at hcon
  set S := Icc a b ∩ D ⁻¹' Iic 0 with hS
  have hSc : IsClosed S := hDc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hSne : S.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hcon⟩
  have hSbdd : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  set ts := sInf S with hts
  have hts_mem : ts ∈ S := hSc.csInf_mem hSne hSbdd
  have hats : a < ts := by
    rcases hts_mem.1.1.lt_or_eq with h | h
    · exact h
    · exfalso; have := hts_mem.2; rw [← h] at this; simp at this; linarith
  have hpos : ∀ t ∈ Ico a ts, 0 < D t := by
    intro t ht
    by_contra hle
    push Not at hle
    have : t ∈ S := ⟨⟨ht.1, ht.2.le.trans hts_mem.1.2⟩, hle⟩
    have := csInf_le hSbdd this
    linarith [ht.2]
  have hmono : MonotoneOn D (Icc a ts) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc a ts)
      (hDc.mono (Icc_subset_Icc le_rfl hts_mem.1.2))
    · rw [interior_Icc]
      intro t ht
      exact (hD t ⟨ht.1, ht.2.trans_le hts_mem.1.2⟩ (hpos t ⟨ht.1.le, ht.2⟩)).1.differentiableAt
        |>.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have h := hD t ⟨ht.1, ht.2.trans_le hts_mem.1.2⟩ (hpos t ⟨ht.1.le, ht.2⟩)
      rw [h.1.deriv]; exact h.2
  have := hmono ⟨le_rfl, hats.le⟩ ⟨hats.le, le_rfl⟩ hats.le
  have h2 : D ts ≤ 0 := hts_mem.2
  linarith

/-- the core existence result on `[0, ∞)` -/
theorem core (v w v' w' : ℝ → ℝ) (α αy : ℝ → ℝ → ℝ)
    (hv : ∀ x, 0 ≤ x → HasDerivWithinAt v (v' x) (Ici 0) x)
    (hw : ∀ x, 0 ≤ x → HasDerivWithinAt w (w' x) (Ici 0) x)
    (hvw : ∀ x, 0 ≤ x → v x ≤ w x)
    (hα : ContinuousOn (Function.uncurry α) {q : ℝ × ℝ | q.1 ∈ Ici 0 ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1})
    (hαy : ContinuousOn (Function.uncurry αy)
      {q : ℝ × ℝ | q.1 ∈ Ici 0 ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1})
    (hαy' : ∀ x, 0 ≤ x → ∀ y, v x ≤ y → y ≤ w x →
      HasDerivWithinAt (α x) (αy x y) (Icc (v x) (w x)) y)
    (hwα : ∀ x, 0 ≤ x → w' x ≤ α x (w x)) (hvα : ∀ x, 0 ≤ x → α x (v x) ≤ v' x) :
    ∃ φ : ℝ → ℝ, (∀ x, 0 ≤ x → HasDerivWithinAt φ (α x (φ x)) (Ici 0) x) ∧
      ∀ x, 0 ≤ x → v x ≤ φ x ∧ φ x ≤ w x := by
  set R := {q : ℝ × ℝ | q.1 ∈ Ici 0 ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1} with hR
  have hvc : ContinuousOn v (Ici 0) := fun x hx => (hv x hx).continuousWithinAt
  have hwc : ContinuousOn w (Ici 0) := fun x hx => (hw x hx).continuousWithinAt
  set cl : ℝ → ℝ → ℝ := fun x y => max (v x) (min (w x) y) with hcl
  have hcl_mem : ∀ x, 0 ≤ x → ∀ y, v x ≤ cl x y ∧ cl x y ≤ w x := by
    intro x hx y
    exact ⟨le_max_left _ _, max_le (hvw x hx) (min_le_left _ _)⟩
  have hcl_id : ∀ x y, v x ≤ y → y ≤ w x → cl x y = y := by
    intro x y h1 h2
    simp only [hcl, min_eq_right h2, max_eq_right h1]
  have hcl_hi : ∀ x, 0 ≤ x → ∀ y, w x ≤ y → cl x y = w x := by
    intro x hx y h
    simp only [hcl, min_eq_left h, max_eq_right (hvw x hx)]
  have hcl_lo : ∀ x y, y ≤ v x → cl x y = v x := by
    intro x y h
    simp only [hcl]
    exact max_eq_left ((min_le_right _ _).trans h)
  set F : ℝ → ℝ → ℝ := fun t y => α t (cl t y) with hF
  have hFlo : ∀ x y, y ≤ v x → F x y = α x (v x) := by
    intro x y h; simp only [hF]; rw [hcl_lo x y h]
  have hFhi : ∀ x, 0 ≤ x → ∀ y, w x ≤ y → F x y = α x (w x) := by
    intro x hx y h; simp only [hF]; rw [hcl_hi x hx y h]
  -- uniform estimates on `[0, N]`
  have hest : ∀ N : ℕ, ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ t ∈ Icc (0:ℝ) N, ∀ y, |F t y| ≤ A) ∧
      (∀ t ∈ Icc (0:ℝ) N, ∀ y₁ y₂, |F t y₁ - F t y₂| ≤ B * |y₁ - y₂|) := by
    intro N
    set KN := (fun p : ℝ × ℝ => (p.1, v p.1 + p.2 * (w p.1 - v p.1))) ''
      (Icc (0:ℝ) N ×ˢ Icc (0:ℝ) 1) with hKN
    have hKNc : IsCompact KN := by
      apply (isCompact_Icc.prod isCompact_Icc).image_of_continuousOn
      apply ContinuousOn.prodMk continuousOn_fst
      have h1 : ContinuousOn (fun p : ℝ × ℝ => v p.1) (Icc (0:ℝ) N ×ˢ Icc (0:ℝ) 1) :=
        hvc.comp continuousOn_fst (fun p hp => (mem_Ici.2 hp.1.1))
      have h2 : ContinuousOn (fun p : ℝ × ℝ => w p.1) (Icc (0:ℝ) N ×ˢ Icc (0:ℝ) 1) :=
        hwc.comp continuousOn_fst (fun p hp => (mem_Ici.2 hp.1.1))
      exact h1.add (continuousOn_snd.mul (h2.sub h1))
    have hKNR : KN ⊆ R := by
      rintro _ ⟨⟨t, s⟩, ⟨ht, hs⟩, rfl⟩
      have h := hvw t ht.1
      refine ⟨ht.1, ?_, ?_⟩
      · simp only; nlinarith [hs.1]
      · simp only; nlinarith [hs.2]
    have hmemK : ∀ t ∈ Icc (0:ℝ) N, ∀ y, v t ≤ y → y ≤ w t → (t, y) ∈ KN := by
      intro t ht y h1 h2
      rcases (hvw t ht.1).lt_or_eq with hlt | heq
      · refine ⟨(t, (y - v t) / (w t - v t)), ⟨ht, ?_, ?_⟩, ?_⟩
        · exact div_nonneg (by linarith) (by linarith)
        · rw [div_le_one (by linarith)]; linarith
        · simp only; congr 1; field_simp; ring
      · refine ⟨(t, 0), ⟨ht, le_rfl, zero_le_one⟩, ?_⟩
        simp only [zero_mul, add_zero]; congr 1; linarith
    obtain ⟨A, hA⟩ := hKNc.exists_bound_of_continuousOn (hα.mono hKNR)
    obtain ⟨B, hB⟩ := hKNc.exists_bound_of_continuousOn (hαy.mono hKNR)
    refine ⟨max A 0, max B 0, le_max_right _ _, le_max_right _ _, ?_, ?_⟩
    · intro t ht y
      have := hA _ (hmemK t ht _ (hcl_mem t ht.1 y).1 (hcl_mem t ht.1 y).2)
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_left _ _)
    · intro t ht y₁ y₂
      have hlip : ∀ a ∈ Icc (v t) (w t), ∀ b ∈ Icc (v t) (w t),
          |α t a - α t b| ≤ max B 0 * |a - b| := by
        intro a ha b hb
        have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := α t) (f' := αy t)
          (s := Icc (v t) (w t)) (C := max B 0)
          (fun y hy => hαy' t ht.1 y hy.1 hy.2)
          (fun y hy => by
            have := hB _ (hmemK t ht y hy.1 hy.2)
            exact this.trans (le_max_left _ _))
          (convex_Icc _ _) hb ha
        simpa [Real.norm_eq_abs] using this
      have h1 := hlip _ ⟨(hcl_mem t ht.1 y₁).1, (hcl_mem t ht.1 y₁).2⟩ _
        ⟨(hcl_mem t ht.1 y₂).1, (hcl_mem t ht.1 y₂).2⟩
      exact h1.trans (mul_le_mul_of_nonneg_left (clamp_lip _ _ _ _) (le_max_right _ _))
  have hFcont : ∀ N : ℕ, ∀ y, ContinuousOn (fun t => F t y) (Icc (0:ℝ) N) := by
    intro N y
    have hv0 : ContinuousOn v (Icc (0:ℝ) N) := hvc.mono (fun t ht => mem_Ici.2 ht.1)
    have hw0 : ContinuousOn w (Icc (0:ℝ) N) := hwc.mono (fun t ht => mem_Ici.2 ht.1)
    have h1 : ContinuousOn (fun t => (t, cl t y)) (Icc (0:ℝ) N) := by
      apply ContinuousOn.prodMk continuousOn_id
      exact continuous_max.comp_continuousOn
        (hv0.prodMk (continuous_min.comp_continuousOn (hw0.prodMk continuousOn_const)))
    exact hα.comp h1 (fun t ht => ⟨ht.1, (hcl_mem t ht.1 y).1, (hcl_mem t ht.1 y).2⟩)
  -- solutions
  set Sol : ℕ → (ℝ → ℝ) → Prop := fun N φ =>
    ∀ t ∈ Icc (0:ℝ) N, HasDerivWithinAt φ (F t (φ t)) (Icc (0:ℝ) N) t with hSol
  have hexist : ∀ N : ℕ, ∀ t0 ∈ Icc (0:ℝ) N, ∀ c : ℝ, ∃ φ, φ t0 = c ∧ Sol N φ := by
    intro N t0 ht0 c
    obtain ⟨A, B, hA0, hB0, hA, hB⟩ := hest N
    set L : ℝ≥0 := ⟨A, hA0⟩
    set K : ℝ≥0 := ⟨B, hB0⟩
    set r : ℝ≥0 := ⟨|c|, abs_nonneg c⟩
    set Nn : ℝ≥0 := ⟨(N:ℝ), Nat.cast_nonneg N⟩
    have hPL : IsPicardLindelof F (tmin := 0) (tmax := N) ⟨t0, ht0⟩ 0 (r + L * Nn) r L K := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t ht
        apply LipschitzWith.lipschitzOnWith
        apply LipschitzWith.of_dist_le_mul
        intro y₁ y₂
        simp only [Real.dist_eq]
        exact hB t ht y₁ y₂
      · intro x _
        exact hFcont N x
      · intro t ht x _
        rw [Real.norm_eq_abs]; exact hA t ht x
      · have e : ((r + L * Nn : ℝ≥0) : ℝ) - (r : ℝ) = A * N := by
          show (|c| + A * N) - |c| = A * N; ring
        rw [e]
        have : max ((N:ℝ) - t0) (t0 - 0) ≤ N :=
          max_le (by linarith [ht0.1]) (by linarith [ht0.2])
        exact mul_le_mul_of_nonneg_left this hA0
    obtain ⟨φ, hφ0, hφ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (x := c) (by rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]; exact le_rfl)
    exact ⟨φ, hφ0, hφ⟩
  have hSol_cont : ∀ N φ, Sol N φ → ContinuousOn φ (Icc (0:ℝ) N) :=
    fun N φ h t ht => (h t ht).continuousWithinAt
  have hSol_Ici : ∀ N φ, Sol N φ → ∀ t ∈ Ico (0:ℝ) N,
      HasDerivWithinAt φ (F t (φ t)) (Ici t) t := by
    intro N φ h t ht
    apply (h t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    exact mem_of_superset (Icc_mem_nhdsGE ht.2) (Icc_subset_Icc ht.1 le_rfl)
  have hSol_mono : ∀ N M : ℕ, N ≤ M → ∀ φ, Sol M φ → Sol N φ := by
    intro N M hNM φ h t ht
    have hsub : Icc (0:ℝ) N ⊆ Icc (0:ℝ) M :=
      Icc_subset_Icc le_rfl (by exact_mod_cast hNM)
    exact (h t (hsub ht)).mono hsub
  have hLip : ∀ N : ℕ, ∃ K : ℝ≥0, ∀ t ∈ Icc (0:ℝ) N, LipschitzWith K (F t) := by
    intro N
    obtain ⟨A, B, hA0, hB0, hA, hB⟩ := hest N
    refine ⟨⟨B, hB0⟩, fun t ht => LipschitzWith.of_dist_le_mul fun y₁ y₂ => ?_⟩
    rw [Real.dist_eq, Real.dist_eq]; exact hB t ht y₁ y₂
  have huniq : ∀ N φ ψ, Sol N φ → Sol N ψ → φ 0 = ψ 0 → EqOn φ ψ (Icc (0:ℝ) N) := by
    intro N φ ψ hφ hψ h0
    obtain ⟨K, hK⟩ := hLip N
    exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => univ)
      (fun t ht => (hK t ⟨ht.1, ht.2.le⟩).lipschitzOnWith) (hSol_cont N φ hφ)
      (hSol_Ici N φ hφ) (fun _ _ => trivial) (hSol_cont N ψ hψ) (hSol_Ici N ψ hψ)
      (fun _ _ => trivial) h0
  -- trapping of backward solutions
  have htrap : ∀ N : ℕ, ∀ ψ, Sol N ψ → v N ≤ ψ N → ψ N ≤ w N →
      ∀ t ∈ Icc (0:ℝ) N, v t ≤ ψ t ∧ ψ t ≤ w t := by
    intro N ψ hψ h1 h2 t ht
    have hint : ∀ s ∈ Ioo t (N:ℝ), HasDerivAt ψ (F s (ψ s)) s := by
      intro s hs
      exact (hψ s ⟨ht.1.trans hs.1.le, hs.2.le⟩).hasDerivAt
        (Icc_mem_nhds (by linarith [ht.1, hs.1]) hs.2)
    constructor
    · by_contra hc
      push Not at hc
      have := no_return (fun s => v s - ψ s) (fun s => v' s - α s (v s)) ht.2
        ((hvc.mono (fun s hs => mem_Ici.2 (ht.1.trans hs.1))).sub
          ((hSol_cont N ψ hψ).mono (Icc_subset_Icc ht.1 le_rfl)))
        (fun s hs hpos => by
          have hs0 : 0 < s := by linarith [ht.1, hs.1]
          have hvd := (hv s hs0.le).hasDerivAt (Ici_mem_nhds hs0)
          have hψd := hint s hs
          rw [hFlo s (ψ s) (by simp at hpos; linarith)] at hψd
          exact ⟨hvd.sub hψd, by linarith [hvα s hs0.le]⟩)
        (by simp; linarith)
      simp at this; linarith
    · by_contra hc
      push Not at hc
      have := no_return (fun s => ψ s - w s) (fun s => α s (w s) - w' s) ht.2
        (((hSol_cont N ψ hψ).mono (Icc_subset_Icc ht.1 le_rfl)).sub
          (hwc.mono (fun s hs => mem_Ici.2 (ht.1.trans hs.1))))
        (fun s hs hpos => by
          have hs0 : 0 < s := by linarith [ht.1, hs.1]
          have hwd := (hw s hs0.le).hasDerivAt (Ici_mem_nhds hs0)
          have hψd := hint s hs
          rw [hFhi s hs0.le (ψ s) (by simp at hpos; linarith)] at hψd
          exact ⟨hψd.sub hwd, by linarith [hwα s hs0.le]⟩)
        (by simp; linarith)
      simp at this; linarith
  -- forward solutions and the nested sets of good initial values
  have hex0 : ∀ N : ℕ, ∀ c : ℝ, ∃ φ, φ 0 = c ∧ Sol N φ :=
    fun N c => hexist N 0 ⟨le_rfl, Nat.cast_nonneg N⟩ c
  choose sol hsol0 hsolS using hex0
  have hdep : ∀ N : ℕ, ∀ t ∈ Icc (0:ℝ) N, Continuous (fun c => sol N c t) := by
    intro N t ht
    obtain ⟨K, hK⟩ := hLip N
    have hb : ∀ c c', dist (sol N c t) (sol N c' t) ≤ dist c c' * Real.exp (K * (t - 0)) := by
      intro c c'
      exact dist_le_of_trajectories_ODE_of_mem (s := fun _ => univ)
        (fun s hs => (hK s ⟨hs.1, hs.2.le⟩).lipschitzOnWith) (hSol_cont N _ (hsolS N c))
        (hSol_Ici N _ (hsolS N c)) (fun _ _ => trivial) (hSol_cont N _ (hsolS N c'))
        (hSol_Ici N _ (hsolS N c')) (fun _ _ => trivial)
        (by rw [hsol0, hsol0]) t ht
    apply LipschitzWith.continuous (K := ⟨Real.exp (K * (t - 0)), (Real.exp_pos _).le⟩)
    apply LipschitzWith.of_dist_le_mul
    intro c c'
    rw [mul_comm]; exact hb c c'
  have hagree : ∀ N M : ℕ, N ≤ M → ∀ c, ∀ t ∈ Icc (0:ℝ) N, sol N c t = sol M c t := by
    intro N M hNM c t ht
    exact huniq N _ _ (hsolS N c) (hSol_mono N M hNM _ (hsolS M c))
      (by rw [hsol0, hsol0]) ht
  set C : ℕ → Set ℝ := fun N => Icc (v 0) (w 0) ∩
    ⋂ t ∈ Icc (0:ℝ) N, ({c | v t ≤ sol N c t} ∩ {c | sol N c t ≤ w t}) with hC
  have hCclosed : ∀ N, IsClosed (C N) := by
    intro N
    apply isClosed_Icc.inter
    apply isClosed_biInter
    intro t ht
    exact (isClosed_le continuous_const (hdep N t ht)).inter
      (isClosed_le (hdep N t ht) continuous_const)
  have hCsub : ∀ N, C (N + 1) ⊆ C N := by
    intro N c hc
    refine ⟨hc.1, ?_⟩
    simp only [mem_iInter]
    intro t ht
    have hc2 := hc.2
    simp only [mem_iInter] at hc2
    have h := hc2 t (Icc_subset_Icc le_rfl (by push_cast; linarith) ht)
    show v t ≤ sol N c t ∧ sol N c t ≤ w t
    rw [hagree N (N + 1) (Nat.le_succ N) c t ht]
    exact h
  have hCne : ∀ N, (C N).Nonempty := by
    intro N
    obtain ⟨ψ, hψN, hψ⟩ := hexist N N ⟨Nat.cast_nonneg N, le_rfl⟩ (v N)
    have htr := htrap N ψ hψ (by rw [hψN]) (by rw [hψN]; exact hvw N (Nat.cast_nonneg N))
    have h0 := htr 0 ⟨le_rfl, Nat.cast_nonneg N⟩
    refine ⟨ψ 0, h0, ?_⟩
    simp only [mem_iInter]
    intro t ht
    have heq := huniq N _ _ (hsolS N (ψ 0)) hψ (by rw [hsol0]) ht
    show v t ≤ sol N (ψ 0) t ∧ sol N (ψ 0) t ≤ w t
    rw [heq]
    exact ⟨(htr t ht).1, (htr t ht).2⟩
  have hC0c : IsCompact (C 0) := isCompact_Icc.of_isClosed_subset (hCclosed 0) inter_subset_left
  obtain ⟨cs, hcs⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed C hCsub
    hCne hC0c hCclosed
  simp only [mem_iInter] at hcs
  -- the global solution
  set φ : ℝ → ℝ := fun t => sol (⌊t⌋₊ + 1) cs t with hφ
  have hfl : ∀ t : ℝ, 0 ≤ t → t ∈ Icc (0:ℝ) ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    intro t ht
    refine ⟨ht, ?_⟩
    push_cast
    exact (Nat.lt_floor_add_one t).le
  have hbounds : ∀ t, 0 ≤ t → v t ≤ φ t ∧ φ t ≤ w t := by
    intro t ht
    have h := (hcs (⌊t⌋₊ + 1)).2
    simp only [mem_iInter] at h
    exact h t (hfl t ht)
  refine ⟨φ, fun t ht => ?_, hbounds⟩
  set M : ℕ := ⌊t⌋₊ + 2 with hM
  have htM : t < (M : ℝ) := by
    simp only [hM]; push_cast; linarith [Nat.lt_floor_add_one t]
  have heq : ∀ s, 0 ≤ s → s < t + 1 → φ s = sol M cs s := by
    intro s hs hst
    have hfs : ⌊s⌋₊ + 1 ≤ M := by
      have : ⌊s⌋₊ ≤ ⌊t + 1⌋₊ := Nat.floor_mono hst.le
      rw [Nat.floor_add_one ht] at this
      simp only [hM]; omega
    exact hagree _ M hfs cs s (hfl s hs)
  have hd := hsolS M cs t ⟨ht, htM.le⟩
  have hd' : HasDerivWithinAt (sol M cs) (F t (sol M cs t)) (Ici 0) t := by
    have : Icc (0:ℝ) M = Ici 0 ∩ Iic (M:ℝ) := (Ici_inter_Iic).symm
    rw [this] at hd
    exact (hasDerivWithinAt_inter (Iic_mem_nhds htM)).1 hd
  have hval : F t (sol M cs t) = α t (φ t) := by
    rw [← heq t ht (by linarith)]
    simp only [hF]
    rw [hcl_id t (φ t) (hbounds t ht).1 (hbounds t ht).2]
  rw [← hval]
  apply hd'.congr_of_eventuallyEq
  · filter_upwards [inter_mem_nhdsWithin (Ici (0:ℝ)) (Iio_mem_nhds (show t < t + 1 by linarith)),
      self_mem_nhdsWithin] with s hs hs0
    exact heq s hs0 hs.2
  · exact heq t ht (by linarith)

end LiqC4Aux

open LiqC4Aux in
theorem solution (I : Set ℝ) (v w : ℝ → ℝ) (α αy : ℝ → ℝ → ℝ)
    (hv : DifferentiableOn ℝ v I) (hw : DifferentiableOn ℝ w I) (hvw : ∀ x ∈ I, v x ≤ w x)
    (hα : ContinuousOn (Function.uncurry α) {q : ℝ × ℝ | q.1 ∈ I ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1})
    (hαy : ContinuousOn (Function.uncurry αy) {q : ℝ × ℝ | q.1 ∈ I ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1})
    (hαy' : ∀ x ∈ I, ∀ y, v x ≤ y → y ≤ w x →
      HasDerivWithinAt (α x) (αy x y) (Set.Icc (v x) (w x)) y)
    (hcase : (I = Set.Ici 0 ∧ ∀ x ∈ I,
        derivWithin w I x - α x (w x) ≤ 0 ∧ 0 ≤ derivWithin v I x - α x (v x)) ∨
      (I = Set.Iic 0 ∧ ∀ x ∈ I,
        derivWithin v I x - α x (v x) ≤ 0 ∧ 0 ≤ derivWithin w I x - α x (w x))) :
    ∃ φ : ℝ → ℝ, (∀ x ∈ I, HasDerivWithinAt φ (α x (φ x)) I x) ∧
      ∀ x ∈ I, v x ≤ φ x ∧ φ x ≤ w x := by
  rcases hcase with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
  · obtain ⟨φ, hφ, hb⟩ := core v w (fun x => derivWithin v (Ici 0) x)
      (fun x => derivWithin w (Ici 0) x) α αy
      (fun x hx => (hv x hx).hasDerivWithinAt) (fun x hx => (hw x hx).hasDerivWithinAt)
      hvw hα hαy hαy' (fun x hx => by linarith [(hc x hx).1])
      (fun x hx => by linarith [(hc x hx).2])
    exact ⟨φ, hφ, hb⟩
  · -- reflect
    set v₁ : ℝ → ℝ := fun x => v (-x)
    set w₁ : ℝ → ℝ := fun x => w (-x)
    set α₁ : ℝ → ℝ → ℝ := fun x y => -α (-x) y
    set αy₁ : ℝ → ℝ → ℝ := fun x y => -αy (-x) y
    have hmaps : MapsTo (fun y : ℝ => -y) (Ici 0) (Iic 0) := by
      intro y hy; show -y ≤ 0; have : (0:ℝ) ≤ y := hy; linarith
    have hv₁ : ∀ x, 0 ≤ x → HasDerivWithinAt v₁ (-derivWithin v (Iic 0) (-x)) (Ici 0) x := by
      intro x hx
      have h := (hv (-x) (by simp; linarith)).hasDerivWithinAt.comp x
        (hasDerivAt_neg x).hasDerivWithinAt hmaps
      rw [mul_neg_one] at h; exact h
    have hw₁ : ∀ x, 0 ≤ x → HasDerivWithinAt w₁ (-derivWithin w (Iic 0) (-x)) (Ici 0) x := by
      intro x hx
      have h := (hw (-x) (by simp; linarith)).hasDerivWithinAt.comp x
        (hasDerivAt_neg x).hasDerivWithinAt hmaps
      rw [mul_neg_one] at h; exact h
    have hR : MapsTo (fun q : ℝ × ℝ => (-q.1, q.2))
        {q : ℝ × ℝ | q.1 ∈ Ici 0 ∧ v₁ q.1 ≤ q.2 ∧ q.2 ≤ w₁ q.1}
        {q : ℝ × ℝ | q.1 ∈ Iic 0 ∧ v q.1 ≤ q.2 ∧ q.2 ≤ w q.1} := by
      rintro ⟨x, y⟩ ⟨hx, h1, h2⟩
      refine ⟨?_, h1, h2⟩
      simp only [mem_Ici, mem_Iic] at hx ⊢; linarith
    have hcont : Continuous (fun q : ℝ × ℝ => (-q.1, q.2)) := by fun_prop
    have hα₁ : ContinuousOn (Function.uncurry α₁)
        {q : ℝ × ℝ | q.1 ∈ Ici 0 ∧ v₁ q.1 ≤ q.2 ∧ q.2 ≤ w₁ q.1} := by
      have := (hα.comp hcont.continuousOn hR).neg
      refine this.congr (fun q _ => ?_)
      simp [α₁, Function.uncurry]
    have hαy₁ : ContinuousOn (Function.uncurry αy₁)
        {q : ℝ × ℝ | q.1 ∈ Ici 0 ∧ v₁ q.1 ≤ q.2 ∧ q.2 ≤ w₁ q.1} := by
      have := (hαy.comp hcont.continuousOn hR).neg
      refine this.congr (fun q _ => ?_)
      simp [αy₁, Function.uncurry]
    obtain ⟨φ₁, hφ₁, hb₁⟩ := core v₁ w₁ (fun x => -derivWithin v (Iic 0) (-x))
      (fun x => -derivWithin w (Iic 0) (-x)) α₁ αy₁ hv₁ hw₁
      (fun x hx => hvw (-x) (by simp; linarith)) hα₁ hαy₁
      (fun x hx y h1 h2 => (hαy' (-x) (by simp; linarith) y h1 h2).neg)
      (fun x hx => by
        have := (hc (-x) (by simp; linarith)).2
        simp only [α₁, w₁]; linarith)
      (fun x hx => by
        have := (hc (-x) (by simp; linarith)).1
        simp only [α₁, v₁]; linarith)
    refine ⟨fun x => φ₁ (-x), fun x hx => ?_, fun x hx => ?_⟩
    · have hx' : 0 ≤ -x := by simp at hx; linarith
      have h := (hφ₁ (-x) hx').comp x (hasDerivAt_neg x).hasDerivWithinAt
        (by intro y hy; show (0:ℝ) ≤ -y; have : y ≤ 0 := hy; linarith)
      simp only [α₁, neg_neg, mul_neg_one] at h
      exact h
    · have hx' : 0 ≤ -x := by simp at hx; linarith
      have := hb₁ (-x) hx'
      simpa [v₁, w₁] using this
