-- Prove2me | solution 1 for HeldKarp.Ascent.lemma_3_case_2
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T08:57:25.335658+00:00
-- url     : https://prove2.me/submissions/34c1267b-e42d-444a-a9c8-25160e612a34

import Mathlib.Tactic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Lattice
import Definitions.Def_HeldKarp_Ascent_oneTreeBound
open HeldKarp.Ascent
open scoped BigOperators
noncomputable section

private theorem weights_bdd {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ) :
    BddBelow {x : ℝ | ∃ G : SimpleGraph (Fin n), IsOneTree G ∧ x = lagrWeight c π G} := by
  classical
  apply (Set.finite_range (lagrWeight c π)).bddBelow.mono
  rintro x ⟨G, hG, rfl⟩
  exact ⟨G, rfl⟩

private theorem bound_le_lagr {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsOneTree G) : oneTreeBound c π ≤ lagrWeight c π G :=
  csInf_le (weights_bdd c π) ⟨G, hG, rfl⟩

private theorem min_lagr_eq {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) : oneTreeBound c π = lagrWeight c π G := by
  apply le_antisymm (bound_le_lagr c π G hG.1)
  unfold oneTreeBound
  refine le_csInf ?_ ?_
  · exact ⟨lagrWeight c π G, G, hG.1, rfl⟩
  · rintro x ⟨G', hG', rfl⟩
    exact hG.2 G' hG'

private theorem ascent_ineq {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (πbar π : Fin n → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c π G) :
    oneTreeBound c πbar - oneTreeBound c π ≤ ∑ i, (πbar i - π i) * degExcess G i := by
  have hb := bound_le_lagr c πbar G hG.1
  rw [min_lagr_eq c π G hG]
  unfold lagrWeight at hb ⊢
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  linarith

open Filter Topology
private theorem lagr_continuous {n : ℕ} (c : Sym2 (Fin n) → ℝ) (G : SimpleGraph (Fin n)) :
    Continuous (fun p : Fin n → ℝ => lagrWeight c p G) := by
  unfold lagrWeight
  fun_prop

private theorem bound_continuous {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsOneTree G) : Continuous (oneTreeBound c) := by
  classical
  let S := Finset.univ.filter (fun H : SimpleGraph (Fin n) => IsOneTree H)
  have hS : S.Nonempty := ⟨G, by simp [S, hG]⟩
  have heq (p : Fin n → ℝ) : oneTreeBound c p = S.inf' hS (fun H => lagrWeight c p H) := by
    apply le_antisymm
    · apply Finset.le_inf'
      intro H hH
      exact bound_le_lagr c p H (by simpa [S] using hH)
    · unfold oneTreeBound
      refine le_csInf ?_ ?_
      · exact ⟨lagrWeight c p G, G, hG, rfl⟩
      · rintro z ⟨H, hH, rfl⟩
        exact Finset.inf'_le _ (by simp [S, hH])
  simp_rw [show oneTreeBound c = fun p => S.inf' hS (fun H => lagrWeight c p H) from funext heq]
  exact Continuous.finset_inf'_apply hS (fun H _ => lagr_continuous c H)

private theorem feasible_iff_bound {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ)
    (G : SimpleGraph (Fin n)) (hG : IsOneTree G) (w : ℝ) (p : Fin n → ℝ) :
    p ∈ feasibleSet c w ↔ w ≤ oneTreeBound c p := by
  constructor
  · intro hp
    unfold oneTreeBound
    refine le_csInf ?_ ?_
    · exact ⟨lagrWeight c p G, G, hG, rfl⟩
    · rintro z ⟨H, hH, rfl⟩
      exact hp H hH
  · intro hp H hH
    exact hp.trans (bound_le_lagr c p H hH)

private theorem positive_degree_norm {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ)
    (p ps : Fin n → ℝ) (G : SimpleGraph (Fin n)) (hG : IsMinOneTree c p G)
    (hw : oneTreeBound c p < oneTreeBound c ps) : 0 < ∑ i, (degExcess G i)^2 := by
  have ha := ascent_ineq c ps p G hG
  have hnon : 0 ≤ ∑ i, (degExcess G i)^2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_contra hno
  have hz : (∑ i, (degExcess G i)^2) = 0 := le_antisymm (le_of_not_gt hno) hnon
  have hzero (i : Fin n) : degExcess G i = 0 := by
    have hi := Finset.single_le_sum (fun j _ => sq_nonneg (degExcess G j)) (Finset.mem_univ i)
    rw [hz] at hi
    nlinarith [sq_nonneg (degExcess G i)]
  simp only [hzero, mul_zero, Finset.sum_const_zero] at ha
  linarith

private theorem fejer_converges {d : ℕ} (A : Set (Fin d → ℝ)) (hA : (interior A).Nonempty)
    (y : ℕ → Fin d → ℝ) (hy : ∀ x ∈ A, Antitone (fun m => ∑ i, (y m i - x i) ^ 2)) :
    ∃ p : Fin d → ℝ, Tendsto y atTop (𝓝 p) := by
  classical
  obtain ⟨a, ha⟩ := hA
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp ha)
  let Q (x : Fin d → ℝ) (m : ℕ) := ∑ i, (y m i - x i)^2
  have hQ (x : Fin d → ℝ) (hx : x ∈ A) : Tendsto (Q x) atTop (𝓝 (⨅ m, Q x m)) := by
    apply tendsto_atTop_ciInf (hy x hx)
    exact ⟨0, by rintro _ ⟨m, rfl⟩; exact Finset.sum_nonneg fun i _ => sq_nonneg _⟩
  have haA : a ∈ A := interior_subset ha
  have hcoord (i : Fin d) : ∃ p : ℝ, Tendsto (fun m => y m i) atTop (𝓝 p) := by
    let x (j : Fin d) := a j + if j = i then r/2 else 0
    have hx : x ∈ A := by
      apply hball
      apply (dist_pi_lt_iff hr).2
      intro j
      dsimp [x]
      by_cases hji : j = i
      · simp [hji, Real.dist_eq, abs_of_pos hr]
        linarith
      · simp [hji, hr]
    have heq (m : ℕ) : Q x m - Q a m = -r * (y m i - a i) + (r/2)^2 := by
      change (∑ j, (y m j - x j)^2) - (∑ j, (y m j - a j)^2) = _
      rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
      · simp only [x, ite_true, ite_self, eq_self]
        ring
      · intro j _ hji
        simp [x, hji]
      · simp
    have hid (m : ℕ) : y m i = a i + ((r/2)^2 - (Q x m - Q a m))/r := by
      have hh := heq m
      field_simp [hr.ne']
      nlinarith
    have ht : Tendsto (fun m => a i + ((r/2)^2 - (Q x m - Q a m))/r) atTop
        (𝓝 (a i + ((r/2)^2 - ((⨅ m, Q x m) - (⨅ m, Q a m)))/r)) :=
      tendsto_const_nhds.add ((tendsto_const_nhds.sub ((hQ x hx).sub (hQ a haA))).div_const r)
    refine ⟨a i + ((r/2)^2 - ((⨅ m, Q x m) - (⨅ m, Q a m)))/r, ?_⟩
    simpa only [← hid] using ht
  choose p hp using hcoord
  exact ⟨p, tendsto_pi_nhds.mpr hp⟩

private theorem distance_step {n : ℕ} (ps p v : Fin n → ℝ) (t : ℝ) :
    (∑ i, (ps i - (p i+t*v i))^2) = (∑ i, (ps i-p i)^2) -
      2*t*(∑ i, (ps i-p i)*v i) + t^2*(∑ i, (v i)^2) := by
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem relaxed_convergence {n : ℕ} [NeZero n] (c : Sym2 (Fin n) → ℝ) (w : ℝ)
    (hw : ∃ ps : Fin n → ℝ, w < oneTreeBound c ps)
    (π : ℕ → Fin n → ℝ) (T : ℕ → SimpleGraph (Fin n)) (hT : ∀ m, IsMinOneTree c (π m) (T m))
    (lam : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε) (hlam : ∀ m, ε < lam m ∧ lam m ≤ 2)
    (hstep : ∀ m, π (m+1) = π m + (lam m * ((w-oneTreeBound c (π m))/(∑ i, (degExcess (T m) i)^2))) • degExcess (T m))
    (hout : ∀ m, π m ∉ feasibleSet c w) :
    ∃ p, Tendsto π atTop (𝓝 p) ∧ oneTreeBound c p = w ∧ p ∈ frontier (feasibleSet c w) := by
  classical
  obtain ⟨ps, hps⟩ := hw
  have hc := bound_continuous c (T 0) (hT 0).1
  have hlow (m : ℕ) : oneTreeBound c (π m) < w := by
    exact lt_of_not_ge fun h => hout m ((feasible_iff_bound c (T 0) (hT 0).1 w (π m)).mpr h)
  let v (m : ℕ) := ∑ i, (degExcess (T m) i)^2
  let gap (m : ℕ) := w-oneTreeBound c (π m)
  let t (m : ℕ) := lam m * (gap m/v m)
  have hv (m : ℕ) : 0 < v m := positive_degree_norm c (π m) ps (T m) (hT m) ((hlow m).trans hps)
  have hgap (m : ℕ) : 0 < gap m := sub_pos.mpr (hlow m)
  have ht (m : ℕ) : 0 < t m := mul_pos (hε.trans (hlam m).1) (div_pos (hgap m) (hv m))
  have htq (m : ℕ) : t m * v m = lam m * gap m := by dsimp [t]; field_simp [ne_of_gt (hv m)]
  have hA : (interior (feasibleSet c w)).Nonempty := by
    refine ⟨ps, mem_interior_iff_mem_nhds.mpr ?_⟩
    have hm := (isOpen_lt continuous_const hc).mem_nhds hps
    apply Filter.mem_of_superset hm
    intro p hp
    exact (feasible_iff_bound c (T 0) (hT 0).1 w p).mpr hp.le
  have hFejer : ∀ p ∈ feasibleSet c w, Antitone (fun m => ∑ i, (π m i-p i)^2) := by
    intro p hp
    apply antitone_nat_of_succ_le
    intro m
    have ha := ascent_ineq c p (π m) (T m) (hT m)
    have hp' := (feasible_iff_bound c (T 0) (hT 0).1 w p).mp hp
    have hdot : gap m ≤ ∑ i, (p i-π m i)*degExcess (T m) i := by dsimp [gap]; linarith
    have htub : t m * v m ≤ 2*gap m := by rw [htq]; exact mul_le_mul_of_nonneg_right (hlam m).2 (hgap m).le
    have hnon := mul_nonneg (ht m).le (show 0 ≤ 2*(∑ i, (p i-π m i)*degExcess (T m) i)-t m*v m by linarith)
    have he := distance_step p (π m) (degExcess (T m)) (t m)
    rw [hstep m]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp_rw [sub_sq_comm (π m _)]
    have he' : (∑ i, (π m i+t m*degExcess (T m) i-p i)^2) =
        (∑ i, (p i-π m i)^2) - 2*t m*(∑ i, (p i-π m i)*degExcess (T m) i) + (t m)^2*v m := by
      simpa only [sub_sq_comm] using he
    change (∑ i, (π m i+t m*degExcess (T m) i-p i)^2) ≤ _
    rw [he']
    nlinarith
  obtain ⟨p, hp⟩ := fejer_converges (feasibleSet c w) hA π hFejer
  have hvbdd : BddAbove (Set.range v) := by
    apply (Set.finite_range (fun G : SimpleGraph (Fin n) => ∑ i, (degExcess G i)^2)).bddAbove.mono
    rintro z ⟨m, rfl⟩
    exact ⟨T m, rfl⟩
  obtain ⟨V, hV⟩ := hvbdd
  have hVm (m : ℕ) : v m ≤ V := hV ⟨m, rfl⟩
  let dstep (m : ℕ) := ∑ i, (π (m+1) i-π m i)^2
  have hsq (m : ℕ) : dstep m * v m = (lam m)^2 * (gap m)^2 := by
    dsimp [dstep]
    rw [hstep m]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left, mul_pow]
    rw [← Finset.mul_sum]
    rw [← mul_pow]
    change (t m)^2*v m*v m = _
    nlinarith [sq_nonneg (t m * v m - lam m * gap m), congrArg (fun z : ℝ => z^2) (htq m)]
  have hineq (m : ℕ) : ε^2*(gap m)^2 ≤ dstep m*V := by
    have hl : ε^2 ≤ (lam m)^2 := by nlinarith [(hlam m).1]
    have hh := mul_le_mul_of_nonneg_right hl (sq_nonneg (gap m))
    rw [← hsq m] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hVm m) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hd : Tendsto dstep atTop (𝓝 0) := by
    have hh : Tendsto dstep atTop (𝓝 (∑ i : Fin n, (p i-p i)^2)) := by
      apply tendsto_finset_sum
      intro i _
      exact (((tendsto_pi_nhds.mp hp i).comp (tendsto_add_atTop_nat 1)).sub (tendsto_pi_nhds.mp hp i)).pow 2
    simpa using hh
  have hg : Tendsto gap atTop (𝓝 (w-oneTreeBound c p)) := tendsto_const_nhds.sub (hc.tendsto p |>.comp hp)
  have hz : ε^2*(w-oneTreeBound c p)^2 ≤ 0 := by
    have hh := le_of_tendsto_of_tendsto' (tendsto_const_nhds.mul (hg.pow 2)) (hd.mul_const V) hineq
    simpa using hh
  have he : oneTreeBound c p = w := by
    have hs : (w-oneTreeBound c p)^2 ≤ 0 := by
      by_contra hh
      exact (not_lt_of_ge hz) (mul_pos (sq_pos_of_pos hε) (lt_of_not_ge hh))
    nlinarith [sq_nonneg (w-oneTreeBound c p)]
  refine ⟨p, hp, he, ?_⟩
  rw [frontier_eq_closure_inter_closure]
  constructor
  · apply subset_closure
    exact (feasible_iff_bound c (T 0) (hT 0).1 w p).mpr he.ge
  · exact mem_closure_of_tendsto hp (Filter.Eventually.of_forall hout)

theorem _root_.solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) (c : Sym2 (Fin n) → ℝ) (wbar : ℝ)
    (hwbar : ∃ π' : Fin n → ℝ, wbar < oneTreeBound c π')
    (π : ℕ → Fin n → ℝ) (T : ℕ → SimpleGraph (Fin n)) (hT : ∀ m, IsMinOneTree c (π m) (T m))
    (hstep : ∀ m, π (m + 1) = π m + (2 * ((wbar - oneTreeBound c (π m)) /
      ∑ i, (degExcess (T m) i) ^ 2)) • degExcess (T m)) :
    ∃ l, π l ∈ feasibleSet c wbar := by
  classical
  by_contra hout
  push_neg at hout
  obtain ⟨p, hp, hpw, hpf⟩ := relaxed_convergence c wbar hwbar π T hT (fun _ => 2) 1
    (by norm_num) (by intro m; norm_num) hstep hout
  have hc := bound_continuous c (T 0) (hT 0).1
  have heach (G : SimpleGraph (Fin n)) : ∀ᶠ m in atTop, T m = G → lagrWeight c p G = wbar := by
    by_cases hG : lagrWeight c p G = wbar
    · exact Filter.Eventually.of_forall fun _ _ => hG
    have hlim : Tendsto (fun m => lagrWeight c (π m) G - oneTreeBound c (π m)) atTop
        (𝓝 (lagrWeight c p G - wbar)) := by
      simpa [hpw] using (((lagr_continuous c G).tendsto p).comp hp).sub ((hc.tendsto p).comp hp)
    have hne : lagrWeight c p G - wbar ≠ 0 := sub_ne_zero.mpr hG
    filter_upwards [hlim.eventually (eventually_ne_nhds hne)] with m hm hTG
    have he := min_lagr_eq c (π m) (T m) (hT m)
    rw [hTG] at he
    exact False.elim (hm (by rw [he, sub_self]))
  have hactive : ∀ᶠ m in atTop, lagrWeight c p (T m) = wbar := by
    filter_upwards [Filter.eventually_all.mpr heach] with m hm
    exact hm (T m) rfl
  obtain ⟨N, hN⟩ := eventually_atTop.mp hactive
  obtain ⟨ps, hps⟩ := hwbar
  let D (m : ℕ) := ∑ i, (p i-π m i)^2
  have hsame (m : ℕ) (hm : N ≤ m) : D (m+1) = D m := by
    have hw : oneTreeBound c (π m) < wbar := lt_of_not_ge fun h =>
      hout m ((feasible_iff_bound c (T 0) (hT 0).1 wbar (π m)).mpr h)
    have hv := positive_degree_norm c (π m) ps (T m) (hT m) (hw.trans hps)
    let q := ∑ i, (degExcess (T m) i)^2
    let gap := wbar-oneTreeBound c (π m)
    let t := 2*(gap/q)
    have hdot : ∑ i, (p i-π m i)*degExcess (T m) i = gap := by
      have hh := hN m hm
      have he := min_lagr_eq c (π m) (T m) (hT m)
      unfold lagrWeight at hh he
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      dsimp [gap]
      linarith
    have htq : t*q = 2*gap := by
      have hq : q ≠ 0 := ne_of_gt hv
      dsimp [t]
      field_simp [hq]
    dsimp only [D]
    rw [hstep m]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change (∑ i, (p i-(π m i+t*degExcess (T m) i))^2) = _
    rw [distance_step, hdot]
    change D m - 2*t*gap + t^2*q = D m
    nlinarith [congrArg (fun z : ℝ => t*z) htq]
  have hiter (k : ℕ) : D (N+k) = D N := by
    induction k with
    | zero => simp
    | succ k ih => simpa [Nat.add_assoc] using (hsame (N+k) (by omega)).trans ih
  have hd : Tendsto D atTop (𝓝 0) := by
    have hh : Tendsto D atTop (𝓝 (∑ i : Fin n, (p i-p i)^2)) := by
      apply tendsto_finset_sum
      intro i _
      exact (tendsto_const_nhds.sub (tendsto_pi_nhds.mp hp i)).pow 2
    simpa using hh
  have hev : D =ᶠ[atTop] (fun _ => D N) := by
    filter_upwards [eventually_ge_atTop N] with m hm
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    exact hiter k
  have hzero : D N = 0 := tendsto_nhds_unique tendsto_const_nhds (hd.congr' hev)
  have hpN : π N = p := by
    funext i
    have hi := Finset.single_le_sum (fun j _ => sq_nonneg (p j-π N j)) (Finset.mem_univ i)
    change (p i-π N i)^2 ≤ D N at hi
    rw [hzero] at hi
    nlinarith [sq_nonneg (p i-π N i)]
  apply hout N
  rw [hpN]
  exact (feasible_iff_bound c (T 0) (hT 0).1 wbar p).mpr hpw.ge
