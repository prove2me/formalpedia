-- Prove2me | solution 1 for InhomMJPStrong.J1.eq_12_13
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T23:05:26.426201+00:00
-- url     : https://prove2.me/submissions/16d419cc-a145-43e1-bf74-9bf01c213635
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model
import Theorems.Thm_InhomMJPStrong_J1_superposition_poisson

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal
open InhomMJPStrong.J1

namespace J1Eq1213

/-! ### Counting functions -/

lemma count_finite (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (t : ℝ) :
    {l : ℕ | 1 ≤ l ∧ T l ≤ t}.Finite := by
  obtain ⟨L, hL⟩ := (hT.eventually_gt_atTop t).exists_forall_of_atTop
  refine (Set.finite_lt_nat L).subset fun l hl => ?_
  show l < L
  by_contra h
  push_neg at h
  have := hL l h
  exact absurd hl.2 (not_le.2 this)

lemma count_mono (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) : Monotone (count T) :=
  fun a b hab => Set.ncard_le_ncard (fun l hl => ⟨hl.1, hl.2.trans hab⟩) (count_finite T hT b)

lemma count_rc (T : ℕ → ℝ) (hT : Tendsto T atTop atTop) (t : ℝ) :
    ∀ᶠ u in 𝓝[≥] t, count T u = count T t := by
  obtain ⟨L, hL⟩ := (hT.eventually_gt_atTop (t + 1)).exists_forall_of_atTop
  have h1 : ∀ᶠ u in 𝓝[≥] t, u < t + 1 :=
    (eventually_lt_nhds (lt_add_one t)).filter_mono nhdsWithin_le_nhds
  have h2 : ∀ᶠ u in 𝓝[≥] t, ∀ l ∈ Finset.range L, (T l ≤ u ↔ T l ≤ t) := by
    refine (Finset.range L).eventually_all.2 fun l _ => ?_
    by_cases hl : T l ≤ t
    · exact eventually_nhdsWithin_of_forall fun u (hu : u ∈ Ici t) =>
        ⟨fun _ => hl, fun _ => hl.trans hu⟩
    · push_neg at hl
      filter_upwards [(eventually_lt_nhds hl).filter_mono nhdsWithin_le_nhds] with u hu
      exact ⟨fun h => absurd h (not_le.2 hu), fun h => absurd h (not_le.2 hl)⟩
  filter_upwards [h1, h2] with u hu1 hu2
  unfold count
  congr 1
  ext l
  simp only [mem_setOf_eq]
  by_cases hlL : l < L
  · rw [hu2 l (Finset.mem_range.2 hlL)]
  · push_neg at hlL
    have := hL l hlL
    constructor
    · rintro ⟨_, h⟩; linarith
    · rintro ⟨_, h⟩; linarith

/-! ### Generalised inverse of a counting function -/

lemma arrivalOf_zero (N : ℝ → ℕ) : arrivalOf N 0 = 0 := by
  unfold arrivalOf
  have : {t : ℝ | 0 ≤ t ∧ 0 ≤ N t} = Set.Ici 0 := by ext t; simp
  rw [this, csInf_Ici]

lemma N_eq_of_arrival (N : ℝ → ℕ) (hmono : Monotone N)
    (hrc : ∀ t, ∀ᶠ u in 𝓝[≥] t, N u = N t)
    (ha : StrictMono (arrivalOf N)) (l : ℕ) (t : ℝ)
    (h1 : arrivalOf N l ≤ t) (h2 : t < arrivalOf N (l + 1)) : N t = l := by
  have hbdd : ∀ j, BddBelow {t : ℝ | 0 ≤ t ∧ j ≤ N t} := fun j => ⟨0, fun t ht => ht.1⟩
  have ha0 : arrivalOf N 0 = 0 := arrivalOf_zero N
  have ht0 : 0 ≤ t := by
    have := ha.monotone (Nat.zero_le l); rw [ha0] at this; linarith
  apply le_antisymm
  · by_contra hc
    push_neg at hc
    have hmem : t ∈ {t : ℝ | 0 ≤ t ∧ l + 1 ≤ N t} := ⟨ht0, hc⟩
    have := csInf_le (hbdd (l + 1)) hmem
    exact absurd h2 (not_lt.2 this)
  · rcases Nat.eq_zero_or_pos l with hl0 | hlpos
    · rw [hl0]; exact Nat.zero_le _
    have hne : {t : ℝ | 0 ≤ t ∧ l ≤ N t}.Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have : arrivalOf N l = 0 := by unfold arrivalOf; rw [hemp, Real.sInf_empty]
      have := ha hlpos
      rw [ha0] at this; linarith
    have key : l ≤ N (arrivalOf N l) := by
      have hr := hrc (arrivalOf N l)
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hr
      obtain ⟨ε, hε, hball⟩ := hr
      obtain ⟨t', ht'S, ht'lt⟩ := exists_lt_of_csInf_lt hne (lt_add_of_pos_right (arrivalOf N l) hε)
      have ht'ge : arrivalOf N l ≤ t' := csInf_le (hbdd l) ht'S
      have hd : dist t' (arrivalOf N l) < ε := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith)]; unfold arrivalOf at ht'lt ⊢; linarith
      have := hball hd (mem_Ici.2 ht'ge)
      rw [← this]; exact ht'S.2
    exact key.trans (hmono h1)

/-! ### The time change -/

lemma count_eq (χ : ℕ → ℝ) (hχ : StrictMono χ) {l : ℕ} {t : ℝ} (h1 : χ l ≤ t)
    (h2 : t < χ (l + 1)) : count χ t = l := by
  unfold count
  have : {j : ℕ | 1 ≤ j ∧ χ j ≤ t} = ↑(Finset.Icc 1 l) := by
    ext j
    simp only [Set.mem_setOf_eq, Finset.coe_Icc, Set.mem_Icc]
    constructor
    · rintro ⟨hj1, hj2⟩
      refine ⟨hj1, ?_⟩
      have : χ j < χ (l + 1) := lt_of_le_of_lt hj2 h2
      have := hχ.lt_iff_lt.1 this
      omega
    · rintro ⟨hj1, hj2⟩
      exact ⟨hj1, le_trans (hχ.monotone hj2) h1⟩
  rw [this, Set.ncard_coe_finset, Nat.card_Icc]
  omega

/-- The affine piece of the time change on `[χ l, χ (l+1)]`. -/
noncomputable def piece (χ θ : ℕ → ℝ) (l : ℕ) (t : ℝ) : ℝ :=
  θ l + (t - χ l) * (θ (l + 1) - θ l) / (χ (l + 1) - χ l)

lemma piece_left (χ θ : ℕ → ℝ) (l : ℕ) : piece χ θ l (χ l) = θ l := by simp [piece]

lemma piece_right (χ θ : ℕ → ℝ) (hχ : StrictMono χ) (l : ℕ) :
    piece χ θ l (χ (l + 1)) = θ (l + 1) := by
  have : χ (l + 1) - χ l ≠ 0 := (sub_pos.2 (hχ (Nat.lt_succ_self l))).ne'
  unfold piece; field_simp; ring

lemma piece_continuous (χ θ : ℕ → ℝ) (l : ℕ) : Continuous (piece χ θ l) := by
  unfold piece; fun_prop

lemma piece_strictMono (χ θ : ℕ → ℝ) (hχ : StrictMono χ) (hθ : StrictMono θ) (l : ℕ) :
    StrictMono (piece χ θ l) := by
  intro a b hab
  have h1 : 0 < χ (l + 1) - χ l := sub_pos.2 (hχ (Nat.lt_succ_self l))
  have h2 : 0 < θ (l + 1) - θ l := sub_pos.2 (hθ (Nat.lt_succ_self l))
  unfold piece
  have : (a - χ l) * (θ (l + 1) - θ l) / (χ (l + 1) - χ l) <
      (b - χ l) * (θ (l + 1) - θ l) / (χ (l + 1) - χ l) := by
    apply div_lt_div_of_pos_right _ h1
    nlinarith
  linarith

lemma tc_piece (χ θ : ℕ → ℝ) (m : ℕ) (hχ : StrictMono χ) {l : ℕ} (hl : l < m) {t : ℝ}
    (h1 : χ l ≤ t) (h2 : t < χ (l + 1)) : timeChange χ θ m t = piece χ θ l t := by
  unfold timeChange
  rw [if_neg (not_le.2 (lt_of_lt_of_le h2 (hχ.monotone (by omega : l + 1 ≤ m))))]
  simp only
  rw [count_eq χ hχ h1 h2]
  rfl

lemma tc_tail (χ θ : ℕ → ℝ) (m : ℕ) {t : ℝ} (h : χ m ≤ t) :
    timeChange χ θ m t = θ m + (t - χ m) := by
  unfold timeChange; rw [if_pos h]

lemma tc_piece_closed (χ θ : ℕ → ℝ) (m : ℕ) (hχ : StrictMono χ) {l : ℕ} (hl : l < m) {t : ℝ}
    (h1 : χ l ≤ t) (h2 : t ≤ χ (l + 1)) : timeChange χ θ m t = piece χ θ l t := by
  rcases h2.lt_or_eq with h2 | h2
  · exact tc_piece χ θ m hχ hl h1 h2
  · subst h2
    rw [piece_right χ θ hχ l]
    by_cases hl1 : l + 1 = m
    · rw [tc_tail χ θ m (by rw [hl1]), hl1]; ring
    · rw [tc_piece χ θ m hχ (by omega : l + 1 < m) le_rfl (hχ (Nat.lt_succ_self _)),
        piece_left]

lemma tc_contOn_Icc (χ θ : ℕ → ℝ) (m : ℕ) (hχ : StrictMono χ) (hχ0 : χ 0 = 0) :
    ∀ j, j ≤ m → ContinuousOn (timeChange χ θ m) (Icc 0 (χ j)) := by
  intro j
  induction j with
  | zero => intro _; rw [hχ0, Icc_self]; exact continuousOn_singleton _ _
  | succ j ih =>
    intro hj
    have h0j : 0 ≤ χ j := by rw [← hχ0]; exact hχ.monotone (Nat.zero_le j)
    rw [← Icc_union_Icc_eq_Icc h0j (hχ.monotone (Nat.le_succ j))]
    refine (ih (by omega)).union_of_isClosed ?_ isClosed_Icc isClosed_Icc
    refine (piece_continuous χ θ j).continuousOn.congr fun t ht => ?_
    exact tc_piece_closed χ θ m hχ (by omega) ht.1 ht.2

lemma tc_contOn (χ θ : ℕ → ℝ) (m : ℕ) (hχ : StrictMono χ) (hχ0 : χ 0 = 0) :
    ContinuousOn (timeChange χ θ m) (Ici 0) := by
  have h0m : 0 ≤ χ m := by rw [← hχ0]; exact hχ.monotone (Nat.zero_le m)
  rw [← Icc_union_Ici_eq_Ici h0m]
  refine (tc_contOn_Icc χ θ m hχ hχ0 m le_rfl).union_of_isClosed ?_ isClosed_Icc isClosed_Ici
  have : Continuous (fun t : ℝ => θ m + (t - χ m)) := by fun_prop
  exact this.continuousOn.congr fun t ht => tc_tail χ θ m ht

lemma tc_smOn_Icc (χ θ : ℕ → ℝ) (m : ℕ) (hχ : StrictMono χ) (hθ : StrictMono θ)
    (hχ0 : χ 0 = 0) : ∀ j, j ≤ m → StrictMonoOn (timeChange χ θ m) (Icc 0 (χ j)) := by
  intro j
  induction j with
  | zero => intro _; rw [hχ0, Icc_self]; exact Set.subsingleton_singleton.strictMonoOn _
  | succ j ih =>
    intro hj
    have h0j : 0 ≤ χ j := by rw [← hχ0]; exact hχ.monotone (Nat.zero_le j)
    have hjj : χ j ≤ χ (j + 1) := hχ.monotone (Nat.le_succ j)
    rw [← Icc_union_Icc_eq_Icc h0j hjj]
    refine (ih (by omega)).union ?_ (isGreatest_Icc h0j) (isLeast_Icc hjj)
    intro a ha b hb hab
    rw [tc_piece_closed χ θ m hχ (by omega) ha.1 ha.2,
      tc_piece_closed χ θ m hχ (by omega) hb.1 hb.2]
    exact piece_strictMono χ θ hχ hθ j hab

lemma tc_smOn (χ θ : ℕ → ℝ) (m : ℕ) (hχ : StrictMono χ) (hθ : StrictMono θ)
    (hχ0 : χ 0 = 0) : StrictMonoOn (timeChange χ θ m) (Ici 0) := by
  have h0m : 0 ≤ χ m := by rw [← hχ0]; exact hχ.monotone (Nat.zero_le m)
  rw [← Icc_union_Ici_eq_Ici h0m]
  refine (tc_smOn_Icc χ θ m hχ hθ hχ0 m le_rfl).union ?_ (isGreatest_Icc h0m) isLeast_Ici
  intro a ha b hb hab
  rw [tc_tail χ θ m ha, tc_tail χ θ m hb]
  linarith

/-- Locating a nonnegative time below `χ m` in a grid interval. -/
lemma exists_interval (χ : ℕ → ℝ) (hχ0 : χ 0 = 0) (m : ℕ) {t : ℝ} (ht0 : 0 ≤ t)
    (htm : t < χ m) : ∃ l, l < m ∧ χ l ≤ t ∧ t < χ (l + 1) := by
  classical
  have hm : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    rw [this, hχ0] at htm; linarith
  have hex : ∃ j, t < χ (j + 1) := ⟨m - 1, by rw [Nat.sub_add_cancel hm]; exact htm⟩
  refine ⟨Nat.find hex, ?_, ?_, Nat.find_spec hex⟩
  · have := Nat.find_min' hex (show t < χ (m - 1 + 1) by rw [Nat.sub_add_cancel hm]; exact htm)
    omega
  · rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, hχ0]; exact ht0
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
      have := Nat.find_min hex (show j < Nat.find hex by omega)
      rw [hj]; exact not_lt.1 this

/-! ### Superposed counting functions -/

lemma supCount_mono (rate n : ℕ) (base : ℕ → ℝ) (extra : ℕ → ℕ → ℝ)
    (hb : Tendsto (arrival base) atTop atTop)
    (he : ∀ k ∈ Finset.Ioc rate n, Tendsto (arrival (extra k)) atTop atTop) :
    Monotone (supCount rate n base extra) := fun a b hab =>
  add_le_add (count_mono _ hb hab) (Finset.sum_le_sum fun k hk => count_mono _ (he k hk) hab)

lemma supCount_rc (rate n : ℕ) (base : ℕ → ℝ) (extra : ℕ → ℕ → ℝ)
    (hb : Tendsto (arrival base) atTop atTop)
    (he : ∀ k ∈ Finset.Ioc rate n, Tendsto (arrival (extra k)) atTop atTop) (t : ℝ) :
    ∀ᶠ u in 𝓝[≥] t, supCount rate n base extra u = supCount rate n base extra t := by
  filter_upwards [count_rc _ hb t,
    (Finset.Ioc rate n).eventually_all.2 fun k hk => count_rc _ (he k hk) t] with u h1 h2
  unfold supCount
  rw [h1, Finset.sum_congr rfl h2]

lemma base_const (rate n : ℕ) (base : ℕ → ℝ) (extra : ℕ → ℕ → ℝ)
    (hb : Tendsto (arrival base) atTop atTop)
    (he : ∀ k ∈ Finset.Ioc rate n, Tendsto (arrival (extra k)) atTop atTop) {t u : ℝ}
    (htu : t ≤ u) (heq : supCount rate n base extra t = supCount rate n base extra u) :
    count (arrival base) t = count (arrival base) u := by
  unfold supCount at heq
  have h1 := count_mono _ hb htu
  have h2 : ∑ k ∈ Finset.Ioc rate n, count (arrival (extra k)) t ≤
      ∑ k ∈ Finset.Ioc rate n, count (arrival (extra k)) u :=
    Finset.sum_le_sum fun k hk => count_mono _ (he k hk) htu
  omega

/-- The deterministic content of (12)–(13) for a fixed sample point. -/
lemma pathwise {p : ℕ} {Ω : Type*} (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ) (alpha : Fin p → ℝ)
    (X : Src → Ω → ℝ) (n : ℕ) (eps : ℝ) (ω : Ω)
    (hbN : Tendsto (arrival fun i => X (.gapN i) ω) atTop atTop)
    (hbM : Tendsto (arrival fun i => X (.gapM i) ω) atTop atTop)
    (heN : ∀ k ∈ Finset.Ioc (lam0 Lam) n, Tendsto (arrival fun i => X (.gapNh k i) ω) atTop atTop)
    (heM : ∀ k ∈ Finset.Ioc (lam0 Lam) n, Tendsto (arrival fun i => X (.gapMh k i) ω) atTop atTop)
    (hχ : StrictMono (chi (lam0 Lam) n X ω)) (hθ : StrictMono (theta (lam0 Lam) n X ω)) :
    let m := gridSize n eps
    let D : ℝ≥0 → ℝ := fun s =>
      timeChange (chi (lam0 Lam) n X ω) (theta (lam0 Lam) n X ω) m (s : ℝ)
    StrictMono D ∧ Continuous D ∧ D 0 = 0 ∧
    Tendsto D atTop atTop ∧
    ∀ s : ℝ≥0, (s : ℝ) < chi (lam0 Lam) n X ω m →
      procJn Lam alpha X n ω (Real.toNNReal (D s)) = procJ Lam alpha X ω s := by
  intro m D
  set χ := chi (lam0 Lam) n X ω with hχdef
  set θ := theta (lam0 Lam) n X ω with hθdef
  have hχ0 : χ 0 = 0 := arrivalOf_zero _
  have hθ0 : θ 0 = 0 := arrivalOf_zero _
  have hSM := tc_smOn χ θ m hχ hθ hχ0
  have hCO := tc_contOn χ θ m hχ hχ0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact hSM (show (0:ℝ) ≤ a from a.2) (show (0:ℝ) ≤ b from b.2) (NNReal.coe_lt_coe.2 hab)
  · exact hCO.comp_continuous continuous_subtype_val fun s => show (0:ℝ) ≤ s from s.2
  · show timeChange χ θ m ((0 : ℝ≥0) : ℝ) = 0
    rw [NNReal.coe_zero]
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [tc_tail χ θ m (by rw [hm0, hχ0]), hm0, hθ0, hχ0]; ring
    · rw [tc_piece χ θ m hχ hmpos (le_of_eq hχ0) (by rw [← hχ0]; exact hχ (Nat.lt_succ_self 0))]
      have := piece_left χ θ 0
      rw [hχ0, hθ0] at this
      exact this
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨Real.toNNReal (max (χ m) (b - θ m + χ m)), fun a ha => ?_⟩
    have ha' : max (χ m) (b - θ m + χ m) ≤ (a : ℝ) := by
      have := (Real.toNNReal_le_iff_le_coe).1 ha
      exact this
    show b ≤ timeChange χ θ m a
    rw [tc_tail χ θ m (le_trans (le_max_left _ _) ha')]
    have := le_trans (le_max_right _ _) ha'
    linarith
  · intro s hs
    have hmonoχ := supCount_mono (lam0 Lam) n _ _ hbN heN
    have hrcχ := supCount_rc (lam0 Lam) n _ _ hbN heN
    have hmonoθ := supCount_mono (lam0 Lam) n _ _ hbM heM
    have hrcθ := supCount_rc (lam0 Lam) n _ _ hbM heM
    obtain ⟨l, hlm, h1, h2⟩ := exists_interval χ hχ0 m s.2 hs
    have hDs : D s = piece χ θ l s := tc_piece χ θ m hχ hlm h1 h2
    have hlo : θ l ≤ D s := by
      rw [hDs, ← piece_left χ θ l]; exact (piece_strictMono χ θ hχ hθ l).monotone h1
    have hhi : D s < θ (l + 1) := by
      rw [hDs, ← piece_right χ θ hχ l]; exact piece_strictMono χ θ hχ hθ l h2
    have hDnn : 0 ≤ D s := by
      have := hθ.monotone (Nat.zero_le l); rw [hθ0] at this; linarith
    have hNθ := N_eq_of_arrival _ hmonoθ hrcθ hθ l (D s) hlo hhi
    have hNχs := N_eq_of_arrival _ hmonoχ hrcχ hχ l s h1 h2
    have hNχl := N_eq_of_arrival _ hmonoχ hrcχ hχ l (χ l) le_rfl (hχ (Nat.lt_succ_self l))
    have hbase := base_const (lam0 Lam) n _ _ hbN heN h1 (hNχl.trans hNχs.symm)
    have hχl0 : 0 ≤ χ l := by
      have := hχ.monotone (Nat.zero_le l); rw [hχ0] at this; exact this
    unfold procJn
    rw [Real.coe_toNNReal _ hDnn, hNθ]
    unfold procJ
    rw [Real.coe_toNNReal _ hχl0]
    exact congrArg _ hbase

/-! ### Probabilistic inputs -/

lemma gammaPDF_one_toReal (r x : ℝ) (hr : 0 < r) :
    (gammaPDF 1 r x).toReal = if 0 ≤ x then r * Real.exp (-(r * x)) else 0 := by
  rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg one_pos hr x), gammaPDFReal]
  simp only [Real.rpow_one, Real.Gamma_one, div_one, sub_self, Real.rpow_zero, mul_one]

lemma ae_ne_zero : ∀ᵐ x : ℝ, x ≠ 0 := by
  have : (volume : Measure ℝ) {0} = 0 := measure_singleton 0
  exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun x hx => by simpa using hx

lemma integrable_pow_exp {r : ℝ} (hr : 0 < r) (p : ℕ) :
    Integrable (fun x : ℝ => |x| ^ p) (expMeasure r) := by
  have hpdf : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff_integrable_smul' hpdf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (p : ℝ)) (p := 1) (b := r)
    (by have : (0:ℝ) ≤ p := Nat.cast_nonneg p
        linarith) one_pos hr
  have h2 : Integrable (Set.indicator (Ioi 0)
      (fun x : ℝ => r * (x ^ (p : ℝ) * Real.exp (-r * x ^ (1 : ℝ))))) volume :=
    (integrable_indicator_iff measurableSet_Ioi).2 (Integrable.const_mul h r)
  refine h2.congr ?_
  filter_upwards [ae_ne_zero] with x hx
  rw [gammaPDF_one_toReal r x hr, smul_eq_mul]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · rw [indicator_of_notMem (by simpa using hneg.le), if_neg (not_le.2 hneg), zero_mul]
  · rw [indicator_of_mem (mem_Ioi.2 hpos), if_pos hpos.le, Real.rpow_natCast, Real.rpow_one,
      abs_of_pos hpos]
    ring_nf

lemma integral_id_exp {r : ℝ} (hr : 0 < r) : ∫ x, x ∂(expMeasure r) = 1 / r := by
  have hpdf : Measurable (gammaPDF 1 r) := (measurable_gammaPDFReal 1 r).ennreal_ofReal
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hpdf
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have h1 : ∫ x : ℝ, (gammaPDF 1 r x).toReal • x =
      ∫ x : ℝ, Set.indicator (Ioi 0) (fun x : ℝ => r * (x ^ ((2:ℝ) - 1) * Real.exp (-(r * x)))) x := by
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with x hx
    rw [gammaPDF_one_toReal r x hr, smul_eq_mul]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · rw [indicator_of_notMem (by simpa using hneg.le), if_neg (not_le.2 hneg), zero_mul]
    · rw [indicator_of_mem (mem_Ioi.2 hpos), if_pos hpos.le]
      norm_num
      ring
  rw [h1, integral_indicator measurableSet_Ioi, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi two_pos hr, Real.Gamma_two]
  rw [Real.rpow_two]
  field_simp

lemma exp_Iic_zero {r : ℝ} (hr : 0 < r) : expMeasure r (Set.Iic 0) = 0 := by
  have := isProbabilityMeasure_expMeasure hr
  rw [← ofReal_cdf, cdf_expMeasure_eq hr]; simp

lemma ae_pos_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → ℝ} {r : ℝ}
    (hr : 0 < r) (h : HasLaw Y (expMeasure r) P) : ∀ᵐ ω ∂P, 0 < Y ω := by
  have : P (Y ⁻¹' Set.Iic 0) = 0 := by
    rw [← Measure.map_apply_of_aemeasurable h.aemeasurable measurableSet_Iic, h.map_eq,
      exp_Iic_zero hr]
  rw [ae_iff]
  simp only [not_lt]
  exact this


lemma div_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {r : ℝ}
    (hr : 0 < r) (g : ℕ → Ω → ℝ) (hind : iIndepFun g P)
    (hlaw : ∀ i, HasLaw (g i) (expMeasure r) P) :
    ∀ᵐ ω ∂P, Tendsto (arrival fun i => g i ω) atTop atTop := by
  have hint : Integrable (g 0) P := by
    have h1 : Integrable (fun x : ℝ => |x| ^ 1) (expMeasure r) := integrable_pow_exp hr 1
    have h2 : Integrable (fun x : ℝ => x) (expMeasure r) :=
      h1.mono' aestronglyMeasurable_id (ae_of_all _ fun x => by simp)
    rw [← (hlaw 0).map_eq] at h2
    exact (integrable_map_measure h2.aestronglyMeasurable (hlaw 0).aemeasurable).1 h2
  have hmean : P[g 0] = 1 / r := by rw [(hlaw 0).integral_eq, integral_id_exp hr]
  have hslln := strong_law_ae_real g hint (fun i j hij => hind.indepFun hij)
    (fun i => ⟨(hlaw i).aemeasurable, (hlaw 0).aemeasurable,
      by rw [(hlaw i).map_eq, (hlaw 0).map_eq]⟩)
  filter_upwards [hslln] with ω hω
  rw [hmean] at hω
  have hlt : 1 / (2 * r) < 1 / r := by
    apply one_div_lt_one_div_of_lt hr; linarith
  have hev : ∀ᶠ l : ℕ in atTop, 1 / (2 * r) ≤ (∑ i ∈ Finset.range l, g i ω) / l :=
    hω.eventually (le_mem_nhds hlt)
  have hlin : Tendsto (fun l : ℕ => (l : ℝ) * (1 / (2 * r))) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
  refine tendsto_atTop_mono' atTop ?_ hlin
  filter_upwards [hev, eventually_ge_atTop 1] with l hl hl1
  have hlpos : (0:ℝ) < l := by exact_mod_cast hl1
  unfold arrival
  rw [le_div_iff₀ hlpos] at hl
  linarith

section Indep

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {rate : ℕ} {X : Src → Ω → ℝ}

lemma indep_gapN (hX : IsUnifSetup rate X P) : iIndepFun (fun i ω => X (.gapN i) ω) P :=
  hX.indep.precomp (g := fun i : ℕ => (⟨Src.gapN i, trivial⟩ : {s // Relevant rate s}))
    (fun a b h => Src.gapN.inj (congrArg Subtype.val h))

lemma indep_gapM (hX : IsUnifSetup rate X P) : iIndepFun (fun i ω => X (.gapM i) ω) P :=
  hX.indep.precomp (g := fun i : ℕ => (⟨Src.gapM i, trivial⟩ : {s // Relevant rate s}))
    (fun a b h => Src.gapM.inj (congrArg Subtype.val h))

lemma indep_gapNh (hX : IsUnifSetup rate X P) (k : ℕ) (hk : rate < k) :
    iIndepFun (fun i ω => X (.gapNh k i) ω) P :=
  hX.indep.precomp (g := fun i : ℕ => (⟨Src.gapNh k i, hk⟩ : {s // Relevant rate s}))
    (fun a b h => (Src.gapNh.inj (congrArg Subtype.val h)).2)

lemma indep_gapMh (hX : IsUnifSetup rate X P) (k : ℕ) (hk : rate < k) :
    iIndepFun (fun i ω => X (.gapMh k i) ω) P :=
  hX.indep.precomp (g := fun i : ℕ => (⟨Src.gapMh k i, hk⟩ : {s // Relevant rate s}))
    (fun a b h => (Src.gapMh.inj (congrArg Subtype.val h)).2)

end Indep

end J1Eq1213

open J1Eq1213 in
theorem solution {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (n : ℕ) (hn : lam0 Lam ≤ n) (eps : ℝ) (heps : 0 < eps) :
    ∀ᵐ ω ∂P,
      let m := gridSize n eps
      let D : ℝ≥0 → ℝ := fun s =>
        timeChange (chi (lam0 Lam) n X ω) (theta (lam0 Lam) n X ω) m (s : ℝ)
      StrictMono D ∧ Continuous D ∧ D 0 = 0 ∧
      Tendsto D atTop atTop ∧
      ∀ s : ℝ≥0, (s : ℝ) < chi (lam0 Lam) n X ω m →
        procJn Lam alpha X n ω (Real.toNNReal (D s)) = procJ Lam alpha X ω s := by
  have hr : 1 ≤ lam0 Lam := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hPos).ne'
  have hrpos : (0:ℝ) < (lam0 Lam : ℝ) := by exact_mod_cast hr
  have hnpos : (0:ℝ) < n := by exact_mod_cast (le_trans hr hn)
  obtain ⟨-, hχl, -, hθl⟩ := superposition_poisson P X (lam0 Lam) n hr hn hX
  have hχsm : ∀ᵐ ω ∂P, StrictMono (chi (lam0 Lam) n X ω) := by
    filter_upwards [ae_all_iff.2 fun l => ae_pos_of_hasLaw hnpos (hχl l)] with ω hω
    exact strictMono_nat_of_lt_succ fun l => by linarith [hω l]
  have hθsm : ∀ᵐ ω ∂P, StrictMono (theta (lam0 Lam) n X ω) := by
    filter_upwards [ae_all_iff.2 fun l => ae_pos_of_hasLaw hnpos (hθl l)] with ω hω
    exact strictMono_nat_of_lt_succ fun l => by linarith [hω l]
  have hbN := div_ae hrpos _ (indep_gapN hX) hX.gapN
  have hbM := div_ae hrpos _ (indep_gapM hX) hX.gapM
  have heN : ∀ᵐ ω ∂P, ∀ k ∈ Finset.Ioc (lam0 Lam) n,
      Tendsto (arrival fun i => X (.gapNh k i) ω) atTop atTop := by
    have : ∀ k, ∀ᵐ ω ∂P, k ∈ Finset.Ioc (lam0 Lam) n →
        Tendsto (arrival fun i => X (.gapNh k i) ω) atTop atTop := fun k => by
      by_cases hk : lam0 Lam < k
      · filter_upwards [div_ae one_pos _ (indep_gapNh hX k hk) (hX.gapNh k hk)] with ω hω _
        exact hω
      · exact ae_of_all _ fun ω hk' => absurd (Finset.mem_Ioc.1 hk').1 hk
    filter_upwards [ae_all_iff.2 this] with ω hω k hk using hω k hk
  have heM : ∀ᵐ ω ∂P, ∀ k ∈ Finset.Ioc (lam0 Lam) n,
      Tendsto (arrival fun i => X (.gapMh k i) ω) atTop atTop := by
    have : ∀ k, ∀ᵐ ω ∂P, k ∈ Finset.Ioc (lam0 Lam) n →
        Tendsto (arrival fun i => X (.gapMh k i) ω) atTop atTop := fun k => by
      by_cases hk : lam0 Lam < k
      · filter_upwards [div_ae one_pos _ (indep_gapMh hX k hk) (hX.gapMh k hk)] with ω hω _
        exact hω
      · exact ae_of_all _ fun ω hk' => absurd (Finset.mem_Ioc.1 hk').1 hk
    filter_upwards [ae_all_iff.2 this] with ω hω k hk using hω k hk
  filter_upwards [hχsm, hθsm, hbN, hbM, heN, heM] with ω h1 h2 h3 h4 h5 h6
  exact pathwise Lam alpha X n eps ω h3 h4 h5 h6 h1 h2
