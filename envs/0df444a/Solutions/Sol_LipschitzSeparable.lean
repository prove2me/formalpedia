-- Prove2me | solution 1 for LipschitzSeparable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:54:33.991009+00:00
-- url     : https://prove2.me/submissions/bf431870-a2ec-43a1-9856-9a51fa5a587c

import Definitions.Def_Tablet_ConeInterpolation
import Definitions.Def_Tablet_RationalCompatibleValues
import Definitions.Def_Tablet_LipschitzSeparable
import Theorems.Thm_ConeInterpolation
import Theorems.Thm_RationalCompatibleValues


set_option autoImplicit false
open scoped NNReal
open Filter Topology
theorem _root_.solution {E : Type*} [MetricSpace E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    ∃ (P : ℕ → E → ℝ) (B L : ℕ → ℝ≥0),
      (∀ n, (∀ x, |P n x| ≤ (B n : ℝ)) ∧ LipschitzWith (L n) (P n)) ∧
      ∀ (π : E → ℝ) (K : ℝ≥0), LipschitzWith K π →
        ∃ φ : ℕ → ℕ,
          (∀ k, LipschitzWith K (P (φ k))) ∧
          (∀ x, Tendsto (fun k => P (φ k) x) atTop (nhds (π x))) ∧
          (∀ M : ℝ≥0, (∀ x, |π x| ≤ (M : ℝ)) → ∀ k, ∀ x, |P (φ k) x| ≤ (M : ℝ)) := by
-- BODY
  rcases isEmpty_or_nonempty E with hE | hE
  · exact ⟨fun _ _ => 0, fun _ => 0, fun _ => 0,
      fun n => ⟨fun x => (IsEmpty.false x).elim, LipschitzWith.const' 0⟩,
      fun π K _ => ⟨id, fun k => LipschitzWith.const' 0, fun x => (IsEmpty.false x).elim,
        fun M _ k x => (IsEmpty.false x).elim⟩⟩
  obtain ⟨dseq, hdense⟩ := TopologicalSpace.exists_dense_seq E
  have hIdxNe : Nonempty (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ)) := ⟨⟨0, (fun _ => 0, 0, 0)⟩⟩
  obtain ⟨ix, hix⟩ := exists_surjective_nat (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ))
  set MM : (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ)) → ℝ := fun i => |((i.2.2.1 : ℚ) : ℝ)| with hMM
  set CC : (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ)) → ℝ≥0 :=
    fun i => Real.toNNReal ((i.2.2.2 : ℚ) : ℝ) with hCC
  set Gf : (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ)) → E → ℝ := fun i x =>
    max (-(MM i)) (min (MM i) (Finset.univ.sup' Finset.univ_nonempty
      (fun j : Fin (i.1 + 1) => ((i.2.1 j : ℚ) : ℝ) - ((CC i : ℝ≥0) : ℝ) * dist x (dseq j.val))))
    with hGf
  have hcone : ∀ i, LipschitzWith (CC i) (Gf i) ∧ (∀ x, |Gf i x| ≤ MM i) ∧
      ((∀ j j' : Fin (i.1 + 1), |((i.2.1 j : ℚ) : ℝ) - ((i.2.1 j' : ℚ) : ℝ)|
          ≤ ((CC i : ℝ≥0) : ℝ) * dist (dseq j.val) (dseq j'.val)) →
        (∀ j : Fin (i.1 + 1), |((i.2.1 j : ℚ) : ℝ)| ≤ MM i) →
        ∀ j : Fin (i.1 + 1), Gf i (dseq j.val) = ((i.2.1 j : ℚ) : ℝ)) := by
    intro i
    exact ConeInterpolation (fun j : Fin (i.1 + 1) => dseq j.val)
      (fun j => ((i.2.1 j : ℚ) : ℝ)) (MM i) (CC i) (abs_nonneg _) (Gf i) (fun x => rfl)
  refine ⟨fun n => Gf (ix n), fun n => Real.toNNReal (MM (ix n)), fun n => CC (ix n), ?_, ?_⟩
  · intro n
    refine ⟨?_, (hcone (ix n)).1⟩
    intro x
    rw [Real.coe_toNNReal _ (abs_nonneg _)]
    exact (hcone (ix n)).2.1 x
  · -- the main clause
    intro pi K hpi
    -- density transfer: pointwise convergence on the dense sequence upgrades to all of `E`
    have hgen : ∀ Q : ℕ → E → ℝ, (∀ k, LipschitzWith K (Q k)) →
        (∀ j : ℕ, Tendsto (fun k => Q k (dseq j)) atTop (nhds (pi (dseq j)))) →
        ∀ x, Tendsto (fun k => Q k x) atTop (nhds (pi x)) := by
      intro Q hQlip hQconv x
      rw [Metric.tendsto_atTop]
      intro eps heps
      obtain ⟨j, hj⟩ := (Metric.denseRange_iff.mp hdense) x (eps / (4 * ((K : ℝ) + 1)))
        (by positivity)
      obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hQconv j) (eps / 2) (by linarith)
      refine ⟨N, fun k hk => ?_⟩
      have h1 : dist (Q k x) (Q k (dseq j)) ≤ (K : ℝ) * dist x (dseq j) :=
        (hQlip k).dist_le_mul x (dseq j)
      have h2 : dist (pi (dseq j)) (pi x) ≤ (K : ℝ) * dist (dseq j) x := hpi.dist_le_mul _ _
      rw [dist_comm (dseq j) x] at h2
      have h3 : dist (Q k (dseq j)) (pi (dseq j)) < eps / 2 := hN k hk
      have h4 : dist (Q k x) (pi x)
          ≤ dist (Q k x) (Q k (dseq j)) + dist (Q k (dseq j)) (pi (dseq j))
            + dist (pi (dseq j)) (pi x) := by
        calc dist (Q k x) (pi x)
            ≤ dist (Q k x) (Q k (dseq j)) + dist (Q k (dseq j)) (pi x) := dist_triangle _ _ _
          _ ≤ dist (Q k x) (Q k (dseq j))
              + (dist (Q k (dseq j)) (pi (dseq j)) + dist (pi (dseq j)) (pi x)) := by
                gcongr; exact dist_triangle _ _ _
          _ = _ := by ring
      have ht : eps / (4 * ((K : ℝ) + 1)) * (4 * ((K : ℝ) + 1)) = eps :=
        div_mul_cancel₀ _ (by positivity)
      have htpos : (0:ℝ) < eps / (4 * ((K : ℝ) + 1)) := by positivity
      have hmul : (K : ℝ) * dist x (dseq j) ≤ (K : ℝ) * (eps / (4 * ((K : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left hj.le K.coe_nonneg
      have hfin : (K : ℝ) * (eps / (4 * ((K : ℝ) + 1))) ≤ eps / 4 := by
        nlinarith [K.coe_nonneg, ht, htpos]
      linarith
    -- the rounding map used for the rational data
    set rnd : ℝ → ℕ → ℚ := fun t k => ((⌊t * ((k : ℝ) + 1)⌋ : ℤ) : ℚ) / ((k : ℚ) + 1) with hrnd
    have hrndcast : ∀ (t : ℝ) (k : ℕ),
        ((rnd t k : ℚ) : ℝ) = (⌊t * ((k : ℝ) + 1)⌋ : ℝ) / ((k : ℝ) + 1) := by
      intro t k; rw [hrnd]; push_cast; ring
    have hrndle : ∀ (t : ℝ) (k : ℕ), ((rnd t k : ℚ) : ℝ) ≤ t := by
      intro t k
      have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
      rw [hrndcast, div_le_iff₀ hk]
      exact Int.floor_le _
    have hrndnn : ∀ (t : ℝ) (k : ℕ), 0 ≤ t → 0 ≤ ((rnd t k : ℚ) : ℝ) := by
      intro t k ht
      have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
      rw [hrndcast]
      have : (0:ℤ) ≤ ⌊t * ((k : ℝ) + 1)⌋ := Int.floor_nonneg.mpr (by positivity)
      have : (0:ℝ) ≤ (⌊t * ((k : ℝ) + 1)⌋ : ℝ) := by exact_mod_cast this
      positivity
    have hrndtend : ∀ t : ℝ, Tendsto (fun k : ℕ => ((rnd t k : ℚ) : ℝ)) atTop (nhds t) := by
      intro t
      have hb : ∀ k : ℕ, ‖((rnd t k : ℚ) : ℝ) - t‖ ≤ 1 / ((k : ℝ) + 1) := by
        intro k
        have hk : (0:ℝ) < (k : ℝ) + 1 := by positivity
        have h1 : (⌊t * ((k : ℝ) + 1)⌋ : ℝ) ≤ t * ((k : ℝ) + 1) := Int.floor_le _
        have h2 : t * ((k : ℝ) + 1) < (⌊t * ((k : ℝ) + 1)⌋ : ℝ) + 1 := Int.lt_floor_add_one _
        rw [Real.norm_eq_abs, hrndcast]
        have hrw : (⌊t * ((k : ℝ) + 1)⌋ : ℝ) / ((k : ℝ) + 1) - t
            = ((⌊t * ((k : ℝ) + 1)⌋ : ℝ) - t * ((k : ℝ) + 1)) / ((k : ℝ) + 1) := by field_simp
        rw [hrw, abs_div, abs_of_pos hk]
        gcongr
        rw [abs_le]; constructor <;> linarith
      have h0 := squeeze_zero_norm hb tendsto_one_div_add_atTop_nhds_zero_nat
      have := h0.add_const t
      simpa using this
    by_cases hconst : ∀ x y : E, pi x = pi y
    · -- Case A: `pi` is constant.
      obtain ⟨x0⟩ := hE
      set y : ℝ := pi x0 with hy
      set a : ℕ → ℚ := fun k => max (-(rnd |y| k)) (min (rnd |y| k) (rnd y k)) with ha
      have hacast : ∀ k, ((a k : ℚ) : ℝ)
          = max (-((rnd |y| k : ℚ) : ℝ)) (min ((rnd |y| k : ℚ) : ℝ) ((rnd y k : ℚ) : ℝ)) := by
        intro k; rw [ha]; push_cast; ring
      have haabs : ∀ k, |((a k : ℚ) : ℝ)| ≤ |y| := by
        intro k
        have h0 : 0 ≤ ((rnd |y| k : ℚ) : ℝ) := hrndnn _ _ (abs_nonneg _)
        have h1 : ((rnd |y| k : ℚ) : ℝ) ≤ |y| := hrndle _ _
        rw [hacast, abs_le]
        constructor
        · exact le_trans (by linarith) (le_max_left _ _)
        · exact le_trans (max_le (by linarith) (min_le_left _ _)) h1
      have hatend : Tendsto (fun k => ((a k : ℚ) : ℝ)) atTop (nhds y) := by
        have h1 := (hrndtend |y|).neg
        have h2 := (hrndtend |y|).min (hrndtend y)
        have h3 := h1.max h2
        have hval : max (-|y|) (min |y| y) = y := by
          rw [min_eq_right (le_abs_self y), max_eq_right (neg_abs_le y)]
        rw [hval] at h3
        exact h3.congr (fun k => (hacast k).symm)
      -- the corresponding family members are the constant functions with value `a k`
      set ikA : ℕ → (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ)) :=
        fun k => ⟨0, (fun _ => a k, |a k|, 0)⟩ with hikA
      have hCC0 : ∀ k, CC (ikA k) = 0 := by
        intro k; rw [hCC, hikA]; norm_num
      have hMMA : ∀ k, MM (ikA k) = |((a k : ℚ) : ℝ)| := by
        intro k; rw [hMM, hikA]; push_cast; rw [abs_abs]
      have hGconst : ∀ (k : ℕ) (x : E), Gf (ikA k) x = ((a k : ℚ) : ℝ) := by
        intro k x
        have hlip : LipschitzWith (CC (ikA k)) (Gf (ikA k)) := (hcone (ikA k)).1
        rw [hCC0 k] at hlip
        have hd : dist (Gf (ikA k) x) (Gf (ikA k) (dseq ((0 : Fin ((ikA k).1 + 1)).val))) ≤ 0 := by
          have := hlip.dist_le_mul x (dseq ((0 : Fin ((ikA k).1 + 1)).val))
          simpa using this
        rw [dist_le_zero.mp hd]
        refine (hcone (ikA k)).2.2 ?_ ?_ 0
        · intro j j'
          have : ((ikA k).2.1 j : ℚ) = ((ikA k).2.1 j' : ℚ) := rfl
          rw [this, sub_self, abs_zero, hCC0 k]
          positivity
        · intro j
          rw [hMMA k]
      refine ⟨fun k => (hix (ikA k)).choose, ?_, ?_, ?_⟩
      · intro k
        dsimp only
        rw [(hix (ikA k)).choose_spec]
        have hlip : LipschitzWith (CC (ikA k)) (Gf (ikA k)) := (hcone (ikA k)).1
        rw [hCC0 k] at hlip
        exact hlip.weaken (by simp)
      · intro x
        have hpx : pi x = y := hconst x x0
        rw [hpx]
        refine hatend.congr (fun k => ?_)
        dsimp only
        rw [(hix (ikA k)).choose_spec, hGconst k x]
      · intro M hM k x
        dsimp only
        rw [(hix (ikA k)).choose_spec, hGconst k x]
        exact le_trans (haabs k) (hM x0)
    · -- Case B: `pi` is not constant.
      classical
      obtain ⟨x0, hx0⟩ := not_forall.mp hconst
      obtain ⟨y0, hy0⟩ := not_forall.mp hx0
      set A : ℝ := max |pi x0| |pi y0| with hA
      have hApos : 0 < A := by
        rcases lt_or_ge 0 A with h | h
        · exact h
        · exfalso
          have h1 : |pi x0| ≤ 0 := le_trans (le_max_left _ _) h
          have h2 : |pi y0| ≤ 0 := le_trans (le_max_right _ _) h
          have e1 : pi x0 = 0 := abs_eq_zero.mp (le_antisymm h1 (abs_nonneg _))
          have e2 : pi y0 = 0 := abs_eq_zero.mp (le_antisymm h2 (abs_nonneg _))
          exact hy0 (by rw [e1, e2])
      have hKpos : 0 < (K : ℝ) := by
        rcases lt_or_ge 0 (K : ℝ) with h | h
        · exact h
        · exfalso
          have hK0 : (K : ℝ) = 0 := le_antisymm h K.coe_nonneg
          have hdd := hpi.dist_le_mul x0 y0
          rw [Real.dist_eq, hK0, zero_mul] at hdd
          have hz : |pi x0 - pi y0| = 0 := le_antisymm hdd (abs_nonneg _)
          exact hy0 (sub_eq_zero.mp (abs_eq_zero.mp hz))
      have hAM : ∀ M : ℝ≥0, (∀ x, |pi x| ≤ (M : ℝ)) → A ≤ (M : ℝ) :=
        fun M hM => max_le (hM x0) (hM y0)
      -- the minimal separation of the first `k+1` sample points
      set rr : ℕ → ℝ := fun k => Finset.inf' (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1)))
        Finset.univ_nonempty
        (fun p => if dseq p.1.val = dseq p.2.val then 1 else dist (dseq p.1.val) (dseq p.2.val))
        with hrr
      have hrrpos : ∀ k, 0 < rr k := by
        intro k
        rw [hrr]
        refine (Finset.lt_inf'_iff _).mpr (fun p _ => ?_)
        by_cases h : dseq p.1.val = dseq p.2.val
        · rw [if_pos h]; norm_num
        · rw [if_neg h]; exact dist_pos.mpr h
      have hrrsep : ∀ (k : ℕ) (j j' : Fin (k + 1)), dseq j.val ≠ dseq j'.val →
          rr k ≤ dist (dseq j.val) (dseq j'.val) := by
        intro k j j' h
        have hmem := Finset.inf'_le
          (s := (Finset.univ : Finset (Fin (k + 1) × Fin (k + 1))))
          (fun p => if dseq p.1.val = dseq p.2.val then 1 else dist (dseq p.1.val) (dseq p.2.val))
          (Finset.mem_univ (j, j'))
        rw [if_neg h] at hmem
        exact hmem
      set epsk : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 2) with hepsk
      have heps0 : ∀ k, 0 < epsk k := by intro k; rw [hepsk]; positivity
      have heps1 : ∀ k, epsk k < 1 := by
        intro k
        rw [hepsk, div_lt_one (by positivity)]
        have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      set delk : ℕ → ℝ := fun k => epsk k * min A (rr k * (K : ℝ) / 4) with hdelk
      have hdel0 : ∀ k, 0 < delk k := by
        intro k
        rw [hdelk]
        have hm : 0 < min A (rr k * (K : ℝ) / 4) :=
          lt_min hApos (div_pos (mul_pos (hrrpos k) hKpos) (by norm_num))
        exact mul_pos (heps0 k) hm
      have hdelA : ∀ k, delk k ≤ epsk k * A := by
        intro k
        rw [hdelk]
        exact mul_le_mul_of_nonneg_left (min_le_left _ _) (heps0 k).le
      have hdelr : ∀ k, delk k ≤ epsk k * rr k * (K : ℝ) / 4 := by
        intro k
        have h := mul_le_mul_of_nonneg_left (min_le_right A (rr k * (K : ℝ) / 4)) (heps0 k).le
        rw [hdelk]
        calc epsk k * min A (rr k * (K : ℝ) / 4) ≤ epsk k * (rr k * (K : ℝ) / 4) := h
          _ = epsk k * rr k * (K : ℝ) / 4 := by ring
      have hstep : ∀ k : ℕ, ∃ (c : Fin (k + 1) → ℚ) (C : ℚ),
          (1 - epsk k / 2) * (K : ℝ) ≤ (C : ℝ) ∧ (C : ℝ) ≤ (K : ℝ) ∧
          (∀ j, |(c j : ℝ) - (1 - epsk k) * pi (dseq j.val)| ≤ delk k) ∧
          (∀ j j', |(c j : ℝ) - (c j' : ℝ)| ≤ (C : ℝ) * dist (dseq j.val) (dseq j'.val)) := by
        intro k
        exact RationalCompatibleValues pi K hpi hKpos (fun j : Fin (k + 1) => dseq j.val)
          (epsk k) (rr k) (delk k) (heps0 k) (heps1 k) (hrrpos k) (hrrsep k) (hdel0 k) (hdelr k)
      choose cf Cf hC1 hC2 hC3 hC4 using hstep
      set Mk : ℕ → ℚ := fun k => Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (k + 1) => |cf k j|) with hMk
      have hMkge : ∀ (k : ℕ) (j : Fin (k + 1)), |cf k j| ≤ Mk k := by
        intro k j
        rw [hMk]
        exact Finset.le_sup' (fun j : Fin (k + 1) => |cf k j|) (Finset.mem_univ j)
      have hMk0 : ∀ k, (0 : ℚ) ≤ Mk k := fun k => le_trans (abs_nonneg _) (hMkge k 0)
      set ikB : ℕ → (Σ l : ℕ, ((Fin (l + 1) → ℚ) × ℚ × ℚ)) :=
        fun k => ⟨k, (cf k, Mk k, Cf k)⟩ with hikB
      have hMMB : ∀ k, MM (ikB k) = ((Mk k : ℚ) : ℝ) := by
        intro k; rw [hMM]; exact abs_of_nonneg (by exact_mod_cast hMk0 k)
      have hCfnn : ∀ k, (0 : ℝ) ≤ ((Cf k : ℚ) : ℝ) := by
        intro k
        have h1 := hC1 k
        have h2 := heps1 k
        have h3 := heps0 k
        nlinarith [hKpos]
      have hCCB : ∀ k, ((CC (ikB k) : ℝ≥0) : ℝ) = ((Cf k : ℚ) : ℝ) := by
        intro k; rw [hCC]; exact Real.coe_toNNReal _ (hCfnn k)
      have hCCle : ∀ k, CC (ikB k) ≤ K := by
        intro k; rw [hCC]; exact Real.toNNReal_le_iff_le_coe.mpr (hC2 k)
      have hGlip : ∀ k, LipschitzWith K (Gf (ikB k)) :=
        fun k => ((hcone (ikB k)).1).weaken (hCCle k)
      have hGbd : ∀ (k : ℕ) (x : E), |Gf (ikB k) x| ≤ ((Mk k : ℚ) : ℝ) := by
        intro k x; rw [← hMMB k]; exact (hcone (ikB k)).2.1 x
      have hGval : ∀ (k : ℕ) (j : Fin (k + 1)),
          Gf (ikB k) (dseq j.val) = ((cf k j : ℚ) : ℝ) := by
        intro k
        refine (hcone (ikB k)).2.2 ?_ ?_
        · intro j j'
          rw [hCCB k]
          exact hC4 k j j'
        · intro j
          rw [hMMB k]
          calc |((cf k j : ℚ) : ℝ)| = ((|cf k j| : ℚ) : ℝ) := by push_cast; ring
            _ ≤ ((Mk k : ℚ) : ℝ) := by exact_mod_cast hMkge k j
      have hdenseconv : ∀ j : ℕ,
          Tendsto (fun k => Gf (ikB k) (dseq j)) atTop (nhds (pi (dseq j))) := by
        intro j
        rw [Metric.tendsto_atTop]
        intro ep hep
        obtain ⟨N0, hN0⟩ := exists_nat_gt ((A + |pi (dseq j)|) / ep)
        refine ⟨max N0 j, fun k hk => ?_⟩
        have hkj : j ≤ k := le_trans (le_max_right _ _) hk
        have hkN : N0 ≤ k := le_trans (le_max_left _ _) hk
        have hjlt : j < k + 1 := by omega
        have hv : Gf (ikB k) (dseq j) = ((cf k ⟨j, hjlt⟩ : ℚ) : ℝ) := hGval k ⟨j, hjlt⟩
        rw [Real.dist_eq, hv]
        have h3 := hC3 k ⟨j, hjlt⟩
        have hsp := abs_sub_le (((cf k ⟨j, hjlt⟩ : ℚ) : ℝ))
          ((1 - epsk k) * pi (dseq j)) (pi (dseq j))
        have he : |(1 - epsk k) * pi (dseq j) - pi (dseq j)| = epsk k * |pi (dseq j)| := by
          have hr : (1 - epsk k) * pi (dseq j) - pi (dseq j) = -(epsk k * pi (dseq j)) := by ring
          rw [hr, abs_neg, abs_mul, abs_of_pos (heps0 k)]
        have hfin : epsk k * (A + |pi (dseq j)|) < ep := by
          have hcast : ((N0 : ℝ)) ≤ (k : ℝ) := by exact_mod_cast hkN
          have hk2 : (A + |pi (dseq j)|) / ep < (k : ℝ) + 2 := by linarith
          have hden : (0 : ℝ) < (k : ℝ) + 2 := by positivity
          rw [div_lt_iff₀ hep] at hk2
          rw [hepsk, div_mul_eq_mul_div, div_lt_iff₀ hden]
          linarith
        have hA1 := hdelA k
        have hp : (0:ℝ) ≤ |pi (dseq j)| := abs_nonneg _
        nlinarith [h3, hsp, he.le, he.ge, hA1, hfin, (heps0 k).le]
      refine ⟨fun k => (hix (ikB k)).choose, ?_, ?_, ?_⟩
      · intro k
        dsimp only
        rw [(hix (ikB k)).choose_spec]
        exact hGlip k
      · intro x
        have hconv := hgen (fun k => Gf (ikB k)) hGlip hdenseconv x
        refine hconv.congr (fun k => ?_)
        dsimp only
        rw [(hix (ikB k)).choose_spec]
      · intro M hM k x
        dsimp only
        rw [(hix (ikB k)).choose_spec]
        refine le_trans (hGbd k x) ?_
        obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup'
          (Finset.univ_nonempty (α := Fin (k + 1))) (fun j : Fin (k + 1) => |cf k j|)
        have hMkeq : Mk k = |cf k j| := by rw [hMk]; exact hj
        have hMkj : ((Mk k : ℚ) : ℝ) = |((cf k j : ℚ) : ℝ)| := by
          rw [hMkeq]; push_cast; ring
        rw [hMkj]
        have h3 := hC3 k j
        have hAle := hAM M hM
        have hdA := hdelA k
        have hpj : |pi (dseq j.val)| ≤ (M : ℝ) := hM _
        have habs : |((cf k j : ℚ) : ℝ)|
            ≤ |((cf k j : ℚ) : ℝ) - (1 - epsk k) * pi (dseq j.val)|
              + |(1 - epsk k) * pi (dseq j.val)| := by
          have hx := abs_sub_abs_le_abs_sub (((cf k j : ℚ) : ℝ)) ((1 - epsk k) * pi (dseq j.val))
          linarith [abs_nonneg (((cf k j : ℚ) : ℝ) - (1 - epsk k) * pi (dseq j.val))]
        have hmul : |(1 - epsk k) * pi (dseq j.val)| = (1 - epsk k) * |pi (dseq j.val)| := by
          rw [abs_mul, abs_of_nonneg (by linarith [heps1 k] : (0:ℝ) ≤ 1 - epsk k)]
        nlinarith [h3, habs, hmul.le, hmul.ge, hdA, hAle, hpj, (heps0 k).le, (heps1 k).le]
