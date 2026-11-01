-- Prove2me | solution 1 for InhomMJPStrong.J1.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T22:33:13.039097+00:00
-- url     : https://prove2.me/submissions/ccb37513-c7e4-46b6-bca8-b25dd96410e7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_InhomMJPStrong_J1_Model
import Theorems.Thm_InhomMJPStrong_J1_lemma_1
import Theorems.Thm_InhomMJPStrong_J1_eq_17
import Theorems.Thm_InhomMJPStrong_J1_eq_12_13
import Theorems.Thm_InhomMJPStrong_J1_eq_14
import Theorems.Thm_InhomMJPStrong_J1_superposition_poisson

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics
open scoped NNReal ENNReal
open InhomMJPStrong.J1

namespace J1Thm3Red

lemma exists_homeo (f : ℝ≥0 → ℝ) (hm : StrictMono f) (hc : Continuous f) (h0 : f 0 = 0)
    (ht : Tendsto f atTop atTop) :
    ∃ D : ℝ≥0 ≃ₜ ℝ≥0, ∀ s, (D s : ℝ) = f s := by
  have hnn : ∀ s, 0 ≤ f s := fun s => h0 ▸ hm.monotone ((zero_le : (0:ℝ≥0) ≤ s))
  let g : ℝ≥0 → ℝ≥0 := fun s => ⟨f s, hnn s⟩
  have gm : StrictMono g := fun a b h => by
    show (⟨f a, hnn a⟩ : ℝ≥0) < ⟨f b, hnn b⟩
    exact_mod_cast hm h
  have gs : Function.Surjective g := by
    intro y
    obtain ⟨b, hb⟩ := (ht.eventually_ge_atTop (y:ℝ)).exists
    have hy : (y:ℝ) ∈ Set.Icc (f 0) (f b) := ⟨by simp [h0], hb⟩
    obtain ⟨s, -, hs⟩ := intermediate_value_Icc (zero_le : (0:ℝ≥0) ≤ b) hc.continuousOn hy
    exact ⟨s, NNReal.eq hs⟩
  exact ⟨(StrictMono.orderIsoOfSurjective g gm gs).toHomeomorph, fun s => rfl⟩

lemma tsum_tail (n : ℕ) :
    ∑' k : ℕ, (if n ≤ k then (2⁻¹ : ℝ≥0∞) ^ (k + 1) else 0) = (2⁻¹ : ℝ≥0∞) ^ n := by
  let f : ℕ → ℝ≥0∞ := fun k => if n ≤ k then (2⁻¹ : ℝ≥0∞) ^ (k + 1) else 0
  have key : (∑ i ∈ Finset.range n, f i) + ∑' i, f (i + n) = ∑' i, f i :=
    Summable.sum_add_tsum_nat_add' ENNReal.summable
  show ∑' i, f i = _
  rw [← key]
  have h0 : ∑ i ∈ Finset.range n, f i = 0 :=
    Finset.sum_eq_zero fun i hi => by simp [f, Finset.mem_range.1 hi]
  rw [h0, zero_add]
  have h1 : ∀ j : ℕ, f (j + n) = (2⁻¹ : ℝ≥0∞) ^ (n + 1) * (2⁻¹) ^ j := fun j => by
    simp only [f]
    rw [if_pos (by omega), ← pow_add]; ring_nf
  simp_rw [h1]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv, pow_succ,
    mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), mul_one]

lemma dJ1_le {p : ℕ} (c : ℕ → ℝ) (y z : ℝ≥0 → Option (Fin p)) (D : ℝ≥0 ≃ₜ ℝ≥0) (T G : ℝ)
    (n : ℕ)
    (hagree : ∀ s : ℝ≥0, (s:ℝ) < T → y (D s) = z s)
    (hc : ∀ k, k + 1 ≤ n → c (k+1) < T)
    (hG : ∀ s : ℝ≥0, |(D s : ℝ) - s| ≤ G) :
    dJ1 c y z ≤ max ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.ofReal G) := by
  refine (iInf_le _ D).trans (max_le_max ?_ ?_)
  · calc ∑' k, (2⁻¹:ℝ≥0∞)^(k+1) * ⨆ (s : ℝ≥0) (_ : (s:ℝ) ≤ c (k+1)),
            (if y (D s) = z s then (0:ℝ≥0∞) else 1)
        ≤ ∑' k : ℕ, (if n ≤ k then (2⁻¹:ℝ≥0∞)^(k+1) else 0) := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          split_ifs with hk
          · calc _ ≤ (2⁻¹:ℝ≥0∞)^(k+1) * 1 := by
                    gcongr
                    refine iSup₂_le fun s _ => ?_
                    split_ifs <;> simp
              _ = _ := mul_one _
          · have : ⨆ (s : ℝ≥0) (_ : (s:ℝ) ≤ c (k+1)),
                (if y (D s) = z s then (0:ℝ≥0∞) else 1) = 0 := by
              refine le_antisymm (iSup₂_le fun s hs => ?_) zero_le
              rw [if_pos (hagree s (lt_of_le_of_lt hs (hc k (by omega))))]
            rw [this, mul_zero]
      _ = (2⁻¹)^n := tsum_tail n
  · refine iSup_le fun s => ?_
    rw [edist_dist, NNReal.dist_eq]
    exact ENNReal.ofReal_le_ofReal (hG s)


lemma arrivalOf_zero (N : ℝ → ℕ) : arrivalOf N 0 = 0 := by
  unfold arrivalOf
  have : {t : ℝ | 0 ≤ t ∧ 0 ≤ N t} = Set.Ici 0 := by ext t; simp
  rw [this, csInf_Ici]

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

lemma le_maxGap (T U : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) : |T m - U m| ≤ maxGap T U m := by
  have hne : (Finset.Icc 1 m).Nonempty := ⟨m, Finset.mem_Icc.2 ⟨hm, le_rfl⟩⟩
  rw [maxGap, dif_pos hne]
  exact Finset.le_sup' (fun l => |T l - U l|) (Finset.mem_Icc.2 ⟨hm, le_rfl⟩)

lemma rate_tendsto {eps : ℝ} (heps1 : eps < 1) :
    Tendsto (fun n : ℕ => Real.log (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2 - eps / 2) (by linarith)).tendsto_div_nhds_zero
  have h2 := h.comp tendsto_natCast_atTop_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp]
  rw [show (-(1 : ℝ) / 2 + eps / 2) = -(1 / 2 - eps / 2) by ring, Real.rpow_neg hpos.le, div_eq_mul_inv]

/-- The scale sequence used in the metric. -/
noncomputable def cseq (eps : ℝ) (k : ℕ) : ℝ := max 0 ((k : ℝ) ^ eps - 2)

lemma half_pow_lt (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (n : ℕ) (hn : 3 ≤ n) :
    (2⁻¹ : ℝ≥0∞) ^ n <
      ENNReal.ofReal (3 * kappa q eps * Real.log (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hk : 4 ≤ kappa q eps := by
    unfold kappa
    have : 1 ≤ Real.exp (1 / 2 + eps / 2 + 2 * q) := Real.one_le_exp (by linarith)
    linarith
  have hlog : 1 ≤ Real.log (n : ℝ) := by
    rw [Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  have hpow : (n : ℝ) ^ (-(1 : ℝ)) ≤ (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  rw [Real.rpow_neg_one] at hpow
  have h2n : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hhalf : ((2 : ℝ)⁻¹) ^ n ≤ (n : ℝ)⁻¹ := by
    rw [inv_pow]; exact inv_anti₀ hnpos h2n
  have hinvpos : 0 < (n : ℝ)⁻¹ := inv_pos.2 hnpos
  have hrhs : 12 * (n : ℝ)⁻¹ ≤ 3 * kappa q eps * Real.log (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) := by
    have h1 : (12 : ℝ) ≤ 3 * kappa q eps * Real.log n := by nlinarith
    calc 12 * (n : ℝ)⁻¹ ≤ (3 * kappa q eps * Real.log n) * (n : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 hinvpos.le
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by nlinarith)
  rw [show (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal (((2 : ℝ)⁻¹) ^ n) by
    rw [ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]; simp]
  rw [ENNReal.ofReal_lt_ofReal_iff (by linarith)]
  linarith

lemma key {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    (fun n : ℕ =>
        (P {ω | ENNReal.ofReal
          (3 * kappa q eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) ≤
          dJ1 (cseq eps) (procJn Lam alpha X n ω) (procJ Lam alpha X ω)}).toReal)
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) := by
  have hL := lemma_1 hp Lam hLam hBound hPos alpha hAlpha P X hX q eps hq heps heps1
  have h17 := eq_17 hp Lam hLam hBound hPos alpha hAlpha P X hX q eps hq heps heps1
  dsimp only at h17
  obtain ⟨hEq, hO⟩ := h17
  have hr : 1 ≤ lam0 Lam := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hPos).ne'
  -- eventual facts
  have hβ : ∀ᶠ n : ℕ in atTop, 2 * Real.exp (1 / 2 + eps / 2 + 2 * q) * Real.log (n : ℝ) *
        (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) ≤ 1 := by
    have := (rate_tendsto heps1).const_mul (2 * Real.exp (1 / 2 + eps / 2 + 2 * q))
    rw [mul_zero] at this
    filter_upwards [this.eventually (ge_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
    simpa [mul_assoc] using hn
  have hpow2 : ∀ᶠ n : ℕ in atTop, (2 : ℝ) ≤ (n : ℝ) ^ eps :=
    ((tendsto_rpow_atTop heps).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  refine Asymptotics.IsBigO.trans_isLittleO ?_ (hO.add hL)
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [eventually_ge_atTop (max (lam0 Lam) 3), hβ, hpow2] with n hn hβn hpn
  have hn1 : lam0 Lam ≤ n := le_trans (le_max_left _ _) hn
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnpos : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1r : (1:ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg), one_mul,
    ← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) ?_
  rw [hEq n hn1]
  have hgood := eq_12_13 hp Lam hLam hBound hPos alpha hAlpha P X hX n hn1 eps heps
  have hsm : ∀ᵐ ω ∂P, StrictMono (chi (lam0 Lam) n X ω) := by
    obtain ⟨-, h2, -, -⟩ := superposition_poisson P X (lam0 Lam) n hr hn1 hX
    have := ae_all_iff.2 fun l => ae_pos_of_hasLaw hnpos (h2 l)
    filter_upwards [this] with ω hω
    exact strictMono_nat_of_lt_succ fun l => by linarith [hω l]
  refine (measure_mono_ae ?_).trans (measure_union_le _ _)
  filter_upwards [hgood, hsm] with ω hg hsmω
  intro hS
  refine Classical.byContradiction fun hcon => ?_
  have hc1 := fun h => hcon (Or.inl h)
  have hc2 := fun h => hcon (Or.inr h)
  simp only [Set.mem_setOf_eq, imp_false, not_le] at hc1 hc2
  dsimp only at hg
  obtain ⟨hD1, hD2, hD3, hD4, hD5⟩ := hg
  set m := gridSize n eps with hm
  set χ := chi (lam0 Lam) n X ω with hχ
  set θ := theta (lam0 Lam) n X ω with hθ
  have hm1 : 1 ≤ m := by
    apply Nat.le_floor
    have : (1:ℝ) ≤ (n:ℝ) ^ (1 + eps) := Real.one_le_rpow hn1r (by linarith)
    simpa using this
  obtain ⟨Dh, hDh⟩ := exists_homeo _ hD1 hD2 hD3 hD4
  -- χ m exceeds c n
  have hcn : cseq eps n = (n:ℝ) ^ eps - 2 := by
    unfold cseq; exact max_eq_right (by linarith)
  have hmn : (n:ℝ) ^ eps - 1 ≤ (m:ℝ) / n := by
    have h1 : (n:ℝ) ^ (1 + eps) - 1 < m := Nat.sub_one_lt_floor _
    rw [Real.rpow_add hnpos, Real.rpow_one] at h1
    rw [le_div_iff₀ hnpos]
    nlinarith
  have hχm : cseq eps n < χ m := by
    have h1 := le_maxGap χ (fun l => (l : ℝ) / (n : ℝ)) hm1
    have h2 := abs_sub_lt_iff.1 (lt_of_le_of_lt h1 (lt_of_lt_of_le hc1 hβn))
    rw [hcn]; linarith [h2.2]
  have hG : ∀ s : ℝ≥0, |(Dh s : ℝ) - s| ≤ maxGap θ χ m := by
    intro s
    rw [hDh s]
    exact (eq_14 χ θ m (arrivalOf_zero _) (arrivalOf_zero _) hsmω hm1).2
      ⟨(s:ℝ), Set.mem_Ici.2 s.2, rfl⟩
  have hle := dJ1_le (cseq eps) (procJn Lam alpha X n ω) (procJ Lam alpha X ω) Dh (χ m)
    (maxGap θ χ m) n
    (fun s hs => by
      have : Dh s = Real.toNNReal (timeChange χ θ m (s:ℝ)) := by
        rw [← hDh s, Real.toNNReal_coe]
      rw [this]; exact hD5 s hs)
    (fun k hk => by
      refine lt_of_le_of_lt ?_ hχm
      unfold cseq
      refine max_le_max le_rfl (sub_le_sub_right ?_ _)
      exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hk) heps.le)
    hG
  have hlt : max ((2⁻¹ : ℝ≥0∞) ^ n) (ENNReal.ofReal (maxGap θ χ m)) <
      ENNReal.ofReal (3 * kappa q eps * Real.log (n : ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) := by
    refine max_lt (half_pow_lt q eps hq heps n hn3) ?_
    have hk : 0 < kappa q eps := by unfold kappa; positivity
    have hlog : 0 < Real.log (n:ℝ) := Real.log_pos (by norm_cast; omega)
    have hr' : 0 < (n:ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) := Real.rpow_pos_of_pos hnpos _
    have hpos3 : 0 < kappa q eps * Real.log (n:ℝ) * (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2) := by positivity
    rw [ENNReal.ofReal_lt_ofReal_iff (by nlinarith)]
    linarith
  exact absurd (lt_of_le_of_lt (le_trans hS hle) hlt) (lt_irrefl _)

end J1Thm3Red

open J1Thm3Red in
theorem solution {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hp : 1 ≤ p) (Lam : ℝ → Matrix (Fin p) (Fin p) ℝ)
    (hLam : IsIntensityFn Lam) (hBound : Condition1 Lam)
    (hPos : 0 < sSup {x : ℝ | ∃ i t, 0 ≤ t ∧ x = |Lam t i i|})
    (alpha : Fin p → ℝ) (hAlpha : (∀ i, 0 ≤ alpha i) ∧ ∑ i, alpha i = 1)
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Src → Ω → ℝ) (hX : IsUnifSetup (lam0 Lam) X P)
    (q eps : ℝ) (hq : 0 < q) (heps : 0 < eps) (heps1 : eps < 1) :
    ∃ c : ℕ → ℝ,
      (∀ k, 0 ≤ c k) ∧ Tendsto c atTop atTop ∧
      (fun n : ℕ =>
        (P {ω | ENNReal.ofReal
          (3 * kappa q eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) ≤
          dJ1 c (procJn Lam alpha X n ω) (procJ Lam alpha X ω)}).toReal)
        =o[atTop] (fun n : ℕ => (n : ℝ) ^ (-q)) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun n : ℕ => dJ1 c (procJn Lam alpha X n ω) (procJ Lam alpha X ω))
          atTop (𝓝 0)) := by
  refine ⟨cseq eps, fun k => le_max_left _ _, ?_,
    key hp Lam hLam hBound hPos alpha hAlpha P X hX q eps hq heps heps1, ?_⟩
  · refine tendsto_atTop_mono (fun k => le_max_right _ _) ?_
    exact tendsto_atTop_add_const_right _ (-2)
      ((tendsto_rpow_atTop heps).comp tendsto_natCast_atTop_atTop)
  · have h2 := key hp Lam hLam hBound hPos alpha hAlpha P X hX 2 eps (by norm_num) heps heps1
    have hsum := summable_of_isBigO_nat
      (Real.summable_nat_rpow.2 (by norm_num : -(2:ℝ) < -1)) h2.isBigO
    have hne : ∑' n : ℕ, P {ω | ENNReal.ofReal
          (3 * kappa 2 eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) ≤
          dJ1 (cseq eps) (procJn Lam alpha X n ω) (procJ Lam alpha X ω)} ≠ ∞ := by
      have : ∀ n : ℕ, P {ω | ENNReal.ofReal
          (3 * kappa 2 eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) ≤
          dJ1 (cseq eps) (procJn Lam alpha X n ω) (procJ Lam alpha X ω)} =
          ENNReal.ofReal ((P {ω | ENNReal.ofReal
          (3 * kappa 2 eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2)) ≤
          dJ1 (cseq eps) (procJn Lam alpha X n ω) (procJ Lam alpha X ω)}).toReal) :=
        fun n => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      rw [tsum_congr this]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => ENNReal.toReal_nonneg) hsum]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hne] with ω hω
    have hr0 : Tendsto (fun n : ℕ => ENNReal.ofReal (3 * kappa 2 eps * Real.log (n : ℝ) *
            (n : ℝ) ^ (-(1 : ℝ) / 2 + eps / 2))) atTop (𝓝 0) := by
      have := (rate_tendsto heps1).const_mul (3 * kappa 2 eps)
      rw [mul_zero] at this
      have h3 := ENNReal.tendsto_ofReal this
      rw [ENNReal.ofReal_zero] at h3
      simpa [mul_assoc] using h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hr0
      (Eventually.of_forall fun n => zero_le) ?_
    filter_upwards [hω] with n hn
    simp only [not_le] at hn
    exact hn.le
