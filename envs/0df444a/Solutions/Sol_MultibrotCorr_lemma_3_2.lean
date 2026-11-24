-- Prove2me | solution 1 for MultibrotCorr.lemma_3_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T14:21:11.552881+00:00
-- url     : https://prove2.me/submissions/5ada3d77-8e6c-42e2-9a74-0ac2fbeb71f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_mcorr_branches
import Theorems.Thm_MultibrotCorr_theorem_D

open Set Filter Topology Finset

namespace MultibrotCorr

lemma roots_sep (q : ℕ) (hq : 0 < q) :
    ∃ s : ℝ, 0 < s ∧ ∀ ζ : ℂ, ζ ^ q = 1 → ζ ≠ 1 → s ≤ ‖ζ - 1‖ := by
  classical
  let R := (Polynomial.nthRootsFinset q (1:ℂ)).erase 1
  by_cases hR : R.Nonempty
  · obtain ⟨x, hx, hmin⟩ := R.exists_min_image (fun ζ => ‖ζ - 1‖) hR
    refine ⟨‖x - 1‖, ?_, ?_⟩
    · have := Finset.mem_erase.1 hx
      exact norm_pos_iff.2 (sub_ne_zero.2 this.1)
    · intro ζ h1 h2
      apply hmin
      simp [R, Polynomial.mem_nthRootsFinset hq, h1, h2]
  · refine ⟨1, one_pos, ?_⟩
    intro ζ h1 h2
    exfalso
    apply hR
    exact ⟨ζ, by simp [R, Polynomial.mem_nthRootsFinset hq, h1, h2]⟩

lemma orbit_growth (e : UnicriticalExponent) (C : ℝ) (c : ℂ) (hc : ‖c‖ ≤ C) (u v : ℂ)
    (huv : v ∈ unicriticalCorr e.p e.q c u) (hu : max C (3 ^ e.q) < ‖u‖) :
    2 * ‖u‖ ≤ ‖v‖ := by
  by_contra hlt
  push Not at hlt
  have hx : max C (3 ^ e.q) < ‖u‖ := hu
  have hC : C ≤ ‖u‖ := le_trans (le_max_left _ _) hx.le
  have h3 : (3:ℝ) ^ e.q < ‖u‖ := lt_of_le_of_lt (le_max_right _ _) hx
  have h1 : (1:ℝ) ≤ 3 ^ e.q := one_le_pow₀ (by norm_num)
  have hx1 : 1 < ‖u‖ := lt_of_le_of_lt h1 h3
  have hrel : ‖v - c‖ ^ e.q = ‖u‖ ^ e.p := by
    have := congrArg norm huv
    simpa [norm_pow] using this
  have hvc : ‖v - c‖ ≤ 3 * ‖u‖ := by
    have := norm_sub_le v c
    linarith
  have hle : ‖u‖ ^ e.p ≤ (3 * ‖u‖) ^ e.q := by
    rw [← hrel]
    exact pow_le_pow_left₀ (norm_nonneg _) hvc _
  obtain ⟨d, hd⟩ : ∃ d, e.p = e.q + (d + 1) := ⟨e.p - e.q - 1, by have := e.hpq; omega⟩
  rw [hd, mul_pow, pow_add] at hle
  have hpos : 0 < ‖u‖ ^ e.q := by positivity
  have : ‖u‖ ^ (d + 1) ≤ 3 ^ e.q := by
    have h' : ‖u‖ ^ e.q * ‖u‖ ^ (d + 1) ≤ ‖u‖ ^ e.q * 3 ^ e.q := by
      calc _ ≤ _ := hle
        _ = _ := by ring
    exact le_of_mul_le_mul_left h' hpos
  have : ‖u‖ ≤ ‖u‖ ^ (d + 1) := by
    calc ‖u‖ = ‖u‖ ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ hx1.le (by omega)
  linarith

lemma orbit_bound (e : UnicriticalExponent) (C : ℝ) :
    ∃ M : ℝ, ∀ c : ℂ, ‖c‖ ≤ C → ∀ w : ℕ → ℂ,
      (∀ i, w (i + 1) ∈ unicriticalCorr e.p e.q c (w i)) → (∃ R, ∀ i, ‖w i‖ ≤ R) →
      ∀ i, ‖w i‖ ≤ M := by
  refine ⟨max C (3 ^ e.q), ?_⟩
  intro c hc w hw ⟨R, hR⟩ i
  by_contra hlt
  push Not at hlt
  have key : ∀ k, max C (3 ^ e.q) < ‖w (i + k)‖ ∧ 2 ^ k * ‖w i‖ ≤ ‖w (i + k)‖ := by
    intro k
    induction k with
    | zero => exact ⟨by simpa using hlt, by simp⟩
    | succ k ih =>
      have hg := orbit_growth e C c hc _ _ (hw (i + k)) ih.1
      have h0 : 0 ≤ ‖w (i + k)‖ := norm_nonneg _
      have : i + (k + 1) = (i + k) + 1 := by ring
      rw [this]
      refine ⟨by linarith [ih.1], ?_⟩
      rw [pow_succ]
      nlinarith [ih.2]
  have hpos : 0 < ‖w i‖ := by
    have := le_max_right C ((3:ℝ) ^ e.q)
    have h1 : (1:ℝ) ≤ 3 ^ e.q := one_le_pow₀ (by norm_num)
    linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (R / ‖w i‖) (by norm_num : (1:ℝ) < 2)
  have h1 := (key k).2
  have h2 := hR (i + k)
  rw [div_lt_iff₀ hpos] at hk
  linarith


def redIdx (ℓ n j : ℕ) : ℕ := if j < ℓ then j else ℓ + (j - ℓ) % n

lemma redIdx_lt (ℓ n j : ℕ) (hn : 0 < n) : redIdx ℓ n j < ℓ + n := by
  unfold redIdx
  split_ifs with h
  · omega
  · have := Nat.mod_lt (j - ℓ) hn
    omega

lemma redIdx_shift (ℓ n : ℕ) (f : ℕ → ℂ) (hper : ∀ j ≥ ℓ, f (j + n) = f j) (j i : ℕ) :
    f (j + i) = f (redIdx ℓ n j + i) := by
  have hk : ∀ k m, ℓ ≤ m → f (m + k * n) = f m := by
    intro k
    induction k with
    | zero => intro m _; simp
    | succ k ih =>
      intro m hm
      have : m + (k + 1) * n = (m + k * n) + n := by ring
      rw [this, hper _ (by omega), ih m hm]
  unfold redIdx
  split_ifs with h
  · rfl
  · have hd := Nat.div_add_mod (j - ℓ) n
    have : j + i = (ℓ + (j - ℓ) % n + i) + ((j - ℓ) / n) * n := by
      have : n * ((j - ℓ) / n) = ((j - ℓ) / n) * n := mul_comm _ _
      omega
    rw [this, hk _ _ (by omega)]

lemma uniq_orbit (e : UnicriticalExponent) (a : ℂ) (ℓ n : ℕ) (z : ℕ → ℂ) (zz : ℕ → ℂ → ℂ)
    (hn : 0 < n)
    (hzne : ∀ j, z j ≠ 0)
    (hzrel : ∀ j, z (j + 1) ∈ unicriticalCorr e.p e.q a (z j))
    (hzorb : IsForwardOrbit e a 0 (zeroOrbit z))
    (hzbdd : ∃ R, ∀ j, ‖zeroOrbit z j‖ ≤ R)
    (hzuniq : ∀ w, IsForwardOrbit e a 0 w → (∃ R, ∀ j, ‖w j‖ ≤ R) → w = zeroOrbit z)
    (hcont : ∀ j, ContinuousAt (zz j) a) (hza : ∀ j, zz j a = z j)
    (hev : ∀ᶠ c in 𝓝 a, (∀ j, zz (j + 1) c ∈ unicriticalCorr e.p e.q c (zz j c)) ∧
      ∀ j ≥ ℓ, zz (j + n) c = zz j c) :
    ∀ᶠ c in 𝓝 a, ∀ w, IsForwardOrbit e c (zz 0 c) w → (∃ R, ∀ j, ‖w j‖ ≤ R) →
      w = fun j => zz j c := by
  classical
  obtain ⟨M, hM⟩ := orbit_bound e (‖a‖ + 1)
  by_contra hcon
  have hfreq := Filter.not_eventually.1 hcon
  have hball : ∀ᶠ c in 𝓝 a, ‖c‖ ≤ ‖a‖ + 1 := by
    filter_upwards [Metric.ball_mem_nhds a one_pos] with c hc
    rw [Metric.mem_ball, dist_eq_norm] at hc
    calc ‖c‖ = ‖a + (c - a)‖ := by simp
      _ ≤ ‖a‖ + ‖c - a‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  obtain ⟨c, hct, hcp⟩ := exists_seq_forall_of_frequently (hfreq.and_eventually (hev.and hball))
  have hbad : ∀ k, ∃ w, IsForwardOrbit e (c k) (zz 0 (c k)) w ∧ (∃ R, ∀ j, ‖w j‖ ≤ R) ∧
      w ≠ fun j => zz j (c k) := by
    intro k
    have := (hcp k).1
    push Not at this
    exact this
  choose w hw1 hw2 hw3 using hbad
  have hex : ∀ k, ∃ j, w k j ≠ zz j (c k) := by
    intro k
    by_contra h
    push Not at h
    exact hw3 k (funext h)
  let m : ℕ → ℕ := fun k => Nat.find (hex k)
  have hm_spec : ∀ k, w k (m k) ≠ zz (m k) (c k) := fun k => Nat.find_spec (hex k)
  have hm_min : ∀ k j, j < m k → w k j = zz j (c k) := by
    intro k j hj
    have := Nat.find_min (hex k) hj
    simpa using this
  have hm_pos : ∀ k, 0 < m k := by
    intro k
    rcases Nat.eq_zero_or_pos (m k) with h | h
    · exfalso
      apply hm_spec k
      rw [h]
      exact (hw1 k).1
    · exact h
  let t : ℕ → ℕ := fun k => m k - 1
  have ht : ∀ k, m k = t k + 1 := fun k => by have := hm_pos k; show m k = m k - 1 + 1; omega
  have hper : ∀ k, ∀ j ≥ ℓ, zz (j + n) (c k) = zz j (c k) := fun k => (hcp k).2.1.2
  have hrel : ∀ k j, zz (j + 1) (c k) ∈ unicriticalCorr e.p e.q (c k) (zz j (c k)) :=
    fun k => (hcp k).2.1.1
  have hbd : ∀ k j, ‖w k j‖ ≤ M := fun k j =>
    hM (c k) (hcp k).2.2 (w k) (hw1 k).2 (hw2 k) j
  let s : ℕ → ℕ := fun k => redIdx ℓ n (t k)
  have hs_lt : ∀ k, s k < ℓ + n := fun k => redIdx_lt ℓ n _ hn
  let u : ℕ → ℕ → ℂ := fun k j => w k (t k + j)
  have hu_zz : ∀ k, u k 0 = zz (s k) (c k) := by
    intro k
    have h1 : w k (t k) = zz (t k) (c k) := hm_min k _ (by have := ht k; omega)
    have h2 := redIdx_shift ℓ n (fun j => zz j (c k)) (hper k) (t k) 0
    simp only [add_zero] at h2
    show w k (t k + 0) = _
    simp only [add_zero]
    rw [h1, h2]
  have hu_bad : ∀ k, u k 1 ≠ zz (s k + 1) (c k) := by
    intro k
    have h2 := redIdx_shift ℓ n (fun j => zz j (c k)) (hper k) (t k) 1
    have h3 := hm_spec k
    rw [ht k] at h3
    show w k (t k + 1) ≠ _
    rw [← h2]
    exact h3
  have hu_rel : ∀ k j, u k (j + 1) ∈ unicriticalCorr e.p e.q (c k) (u k j) :=
    fun k j => (hw1 k).2 (t k + j)
  have hv_rel : ∀ k, zz (s k + 1) (c k) ∈ unicriticalCorr e.p e.q (c k) (u k 0) := by
    intro k
    have h2 := redIdx_shift ℓ n (fun j => zz j (c k)) (hper k) (t k) 1
    have := hrel k (s k)
    rw [← hu_zz k] at this
    exact this
  -- compactness
  have hK : IsCompact ((Set.pi univ fun _ : ℕ => Metric.closedBall (0:ℂ) M) ×ˢ
      (univ : Set (Fin (ℓ + n)))) :=
    (isCompact_univ_pi (fun _ => isCompact_closedBall 0 M)).prod isCompact_univ
  obtain ⟨L, hLK, ψ, hψ, hL⟩ := hK.tendsto_subseq
    (x := fun k => (u k, (⟨s k, hs_lt k⟩ : Fin (ℓ + n))))
    (fun k => ⟨fun j _ => by simpa using hbd k (t k + j), mem_univ _⟩)
  have hu : ∀ j, Tendsto (fun k => u (ψ k) j) atTop (𝓝 (L.1 j)) := fun j =>
    ((continuous_apply j).tendsto L.1).comp ((continuous_fst.tendsto L).comp hL)
  have hs : ∀ᶠ k in atTop, s (ψ k) = (L.2 : ℕ) := by
    have h := (continuous_snd.tendsto L).comp hL
    rw [nhds_discrete] at h
    filter_upwards [tendsto_pure.1 h] with k hk
    have := congrArg Fin.val hk
    simpa using this
  set S : ℕ := (L.2 : ℕ) with hS
  have hct' : Tendsto (fun k => c (ψ k)) atTop (𝓝 a) := hct.comp hψ.tendsto_atTop
  have hzz_lim : ∀ j, Tendsto (fun k => zz j (c (ψ k))) atTop (𝓝 (z j)) := fun j => by
    have := (hcont j).tendsto.comp hct'
    rwa [hza j] at this
  have hL0 : L.1 0 = z S := by
    refine tendsto_nhds_unique (hu 0) ?_
    refine (hzz_lim S).congr' ?_
    filter_upwards [hs] with k hk
    rw [hu_zz, hk]
  have hLrel : ∀ j, (L.1 (j + 1) - a) ^ e.q = (L.1 j) ^ e.p := by
    intro j
    have h1 := ((hu (j + 1)).sub hct').pow e.q
    have h2 := (hu j).pow e.p
    refine tendsto_nhds_unique h1 ?_
    refine h2.congr' ?_
    filter_upwards with k
    exact (hu_rel (ψ k) j).symm
  have hLb : ∀ j, ‖L.1 j‖ ≤ M := by
    intro j
    have := hLK.1 j (mem_univ _)
    simpa using this
  have hzS : (z (S + 1) - a) ^ e.q = (z S) ^ e.p := hzrel S
  have hzSne : z (S + 1) - a ≠ 0 := by
    intro h
    rw [h, zero_pow (by have := e.hq; omega)] at hzS
    exact hzne S (pow_eq_zero_iff (by have := e.hpq; have := e.hq; omega) |>.1 hzS.symm)
  obtain ⟨s0, hs0, hsep⟩ := roots_sep e.q e.hq
  have hsepk : ∀ k, s0 * ‖zz (s k + 1) (c k) - c k‖ ≤ ‖u k 1 - zz (s k + 1) (c k)‖ := by
    intro k
    set X := u k 1 - c k with hX
    set Y := zz (s k + 1) (c k) - c k with hY
    have hXq : X ^ e.q = (u k 0) ^ e.p := hu_rel k 0
    have hYq : Y ^ e.q = (u k 0) ^ e.p := hv_rel k
    have hne : X ≠ Y := by
      intro h
      apply hu_bad k
      have : u k 1 - c k = zz (s k + 1) (c k) - c k := h
      exact sub_left_injective this
    have hY0 : Y ≠ 0 := by
      intro h
      apply hne
      have : X ^ e.q = 0 := by rw [hXq, ← hYq, h, zero_pow (by have := e.hq; omega)]
      rw [h]
      exact pow_eq_zero_iff (by have := e.hq; omega) |>.1 this
    have hζ : (X / Y) ^ e.q = 1 := by
      rw [div_pow, hXq, hYq]
      exact div_self (by rw [← hYq]; exact pow_ne_zero _ hY0)
    have hζ1 : X / Y ≠ 1 := by
      intro h
      apply hne
      rwa [div_eq_one_iff_eq hY0] at h
    have := hsep _ hζ hζ1
    have hnorm : ‖X / Y - 1‖ = ‖X - Y‖ / ‖Y‖ := by
      rw [← norm_div]
      congr 1
      field_simp
    rw [hnorm, le_div_iff₀ (norm_pos_iff.2 hY0)] at this
    have e2 : X - Y = u k 1 - zz (s k + 1) (c k) := by rw [hX, hY]; ring
    rw [e2] at this
    linarith
  have hlim_sep : s0 * ‖z (S + 1) - a‖ ≤ ‖L.1 1 - z (S + 1)‖ := by
    have h1 : Tendsto (fun k => s0 * ‖zz (s (ψ k) + 1) (c (ψ k)) - c (ψ k)‖) atTop
        (𝓝 (s0 * ‖z (S + 1) - a‖)) := by
      have := ((hzz_lim (S + 1)).sub hct').norm.const_mul s0
      refine this.congr' ?_
      filter_upwards [hs] with k hk
      rw [hk]
    have h2 : Tendsto (fun k => ‖u (ψ k) 1 - zz (s (ψ k) + 1) (c (ψ k))‖) atTop
        (𝓝 ‖L.1 1 - z (S + 1)‖) := by
      have := ((hu 1).sub (hzz_lim (S + 1))).norm
      refine this.congr' ?_
      filter_upwards [hs] with k hk
      rw [hk]
    exact le_of_tendsto_of_tendsto h1 h2 (Eventually.of_forall fun k => hsepk (ψ k))
  have hL1 : L.1 1 ≠ z (S + 1) := by
    intro h
    rw [h, sub_self, norm_zero] at hlim_sep
    have := mul_pos hs0 (norm_pos_iff.2 hzSne)
    linarith
  -- build the glued orbit
  let y : ℕ → ℂ := fun i => if i ≤ S + 1 then zeroOrbit z i else L.1 (i - (S + 1))
  have hy0 : zeroOrbit z (S + 1) = L.1 0 := by rw [hL0]; rfl
  have hyorb : IsForwardOrbit e a 0 y := by
    refine ⟨by simp [y, zeroOrbit], ?_⟩
    intro i
    by_cases h1 : i + 1 ≤ S + 1
    · have h2 : i ≤ S + 1 := by omega
      simp only [y, if_pos h1, if_pos h2]
      exact hzorb.2 i
    · by_cases h3 : i = S + 1
      · subst h3
        simp only [y, if_neg h1, if_pos le_rfl]
        have : S + 1 + 1 - (S + 1) = 0 + 1 := by omega
        rw [this, hy0]
        exact hLrel 0
      · have h2 : ¬ i ≤ S + 1 := by omega
        simp only [y, if_neg h1, if_neg h2]
        have : i + 1 - (S + 1) = (i - (S + 1)) + 1 := by omega
        rw [this]
        exact hLrel _
  have hybdd : ∃ R, ∀ j, ‖y j‖ ≤ R := by
    obtain ⟨R, hR⟩ := hzbdd
    refine ⟨max R M, fun j => ?_⟩
    simp only [y]
    split_ifs
    · exact le_trans (hR j) (le_max_left _ _)
    · exact le_trans (hLb _) (le_max_right _ _)
  have hyeq := congrFun (hzuniq y hyorb hybdd) (S + 2)
  simp only [y] at hyeq
  rw [if_neg (by omega)] at hyeq
  have : S + 2 - (S + 1) = 1 := by omega
  rw [this] at hyeq
  exact hL1 hyeq


noncomputable def Qf (φ : ℕ → ℂ → ℂ) : ℕ → ℂ → ℂ → ℂ
  | 0 => fun _ w => w
  | (j + 1) => fun c w => φ j (Qf φ j c w) + c

lemma perturbedComp_zero_eq (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ) (j : ℕ) (c : ℂ) :
    perturbedComp e φ 0 j c = Qf φ j c := by
  induction j with
  | zero => funext w; simp [perturbedComp, Qf]
  | succ j ih =>
    funext w
    have h := congrFun ih w
    simp only [perturbedComp] at h ⊢
    rw [List.range_succ, List.foldl_append]
    simp [Qf, ← h]

lemma phi_hasDerivAt (e : UnicriticalExponent) (a : ℂ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ)
    (U : ℕ → Set ℂ) (j : ℕ)
    (hbr : IsOpen (U j) ∧ z j ∈ U j ∧ IsUnivalentBranch e 0 (U j) (φ j) ∧ φ j (z j) + a = z (j + 1))
    (hzne : z j ≠ 0) (hrel : z (j + 1) ∈ unicriticalCorr e.p e.q a (z j)) :
    HasDerivAt (φ j) (branchDerivFactor e a (z j) (z (j + 1))) (z j) := by
  obtain ⟨hU, hzU, ⟨-, hdiff, -, hpow⟩, hval⟩ := hbr
  have hd : DifferentiableAt ℂ (φ j) (z j) := (hdiff _ hzU).differentiableAt (hU.mem_nhds hzU)
  have hq := e.hq
  have hpq := e.hpq
  have hne : z (j + 1) - a ≠ 0 := by
    intro h
    have h2 : (z (j + 1) - a) ^ e.q = (z j) ^ e.p := hrel
    rw [h, zero_pow (by omega)] at h2
    exact hzne (pow_eq_zero_iff (by omega) |>.1 h2.symm)
  have hφz : φ j (z j) = z (j + 1) - a := by rw [← hval]; ring
  have h1 : HasDerivAt (fun w => (φ j w) ^ e.q) ((e.q : ℂ) * (φ j (z j)) ^ (e.q - 1) *
      deriv (φ j) (z j)) (z j) := hd.hasDerivAt.pow e.q
  have h2 : HasDerivAt (fun w : ℂ => w ^ e.p) ((e.p : ℂ) * (z j) ^ (e.p - 1)) (z j) := by
    simpa using hasDerivAt_pow e.p (z j)
  have h3 : (fun w => (φ j w) ^ e.q) =ᶠ[𝓝 (z j)] fun w : ℂ => w ^ e.p := by
    filter_upwards [hU.mem_nhds hzU] with w hw
    simpa using hpow w hw
  have h4 := h1.unique (h2.congr_of_eventuallyEq h3)
  rw [hφz] at h4
  have hderiv : deriv (φ j) (z j) = branchDerivFactor e a (z j) (z (j + 1)) := by
    unfold branchDerivFactor
    have hq0 : (e.q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
    have hpow0 : (z (j + 1) - a) ^ (e.q - 1) ≠ 0 := pow_ne_zero _ hne
    field_simp
    linear_combination h4
  rw [← hderiv]
  exact hd.hasDerivAt

lemma Qf_ev (a : ℂ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (hz0 : z 0 = a)
    (hbr : ∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ DifferentiableOn ℂ (φ j) (U j) ∧
      φ j (z j) + a = z (j + 1)) :
    ∀ j, Qf φ j a a = z j ∧ ∀ᶠ p in 𝓝 (a, a),
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ j p.1 p.2) p ∧ Qf φ j p.1 p.2 ∈ U j := by
  intro j
  induction j with
  | zero =>
    refine ⟨by simp [Qf, hz0], ?_⟩
    have hm : (a, a).2 ∈ U 0 := by simpa [hz0] using (hbr 0).2.1
    filter_upwards [continuousAt_snd.eventually_mem ((hbr 0).1.mem_nhds hm)] with p hp
    exact ⟨contDiffAt_snd, hp⟩
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    obtain ⟨hU, hzU, hdiff, hval⟩ := hbr j
    have step : ∀ p : ℂ × ℂ, ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ j p.1 p.2) p →
        Qf φ j p.1 p.2 ∈ U j →
        ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ (j + 1) p.1 p.2) p := by
      intro p h1 h2
      have hφ : ContDiffAt ℂ 1 (φ j) (Qf φ j p.1 p.2) :=
        (hdiff.contDiffOn hU).contDiffAt (hU.mem_nhds h2)
      exact (hφ.comp p h1).add contDiffAt_fst
    have hval' : Qf φ (j + 1) a a = z (j + 1) := by
      show φ j (Qf φ j a a) + a = _
      rw [ih1, hval]
    refine ⟨hval', ?_⟩
    have hc : ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ (j + 1) p.1 p.2) (a, a) :=
      step _ ih2.self_of_nhds.1 ih2.self_of_nhds.2
    have hm : Qf φ (j + 1) (a, a).1 (a, a).2 ∈ U (j + 1) := by
      show Qf φ (j + 1) a a ∈ _
      rw [hval']; exact (hbr (j + 1)).2.1
    have hmem := hc.continuousAt.eventually_mem ((hbr (j + 1)).1.mem_nhds hm)
    filter_upwards [ih2, hmem] with p hp hp2
    exact ⟨step p hp.1 hp.2, hp2⟩

lemma Qf_hasDerivAt (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
    (hbr : ∀ j, IsOpen (U j) ∧ DifferentiableOn ℂ (φ j) (U j)) (c w : ℂ) :
    ∀ j, (∀ i < j, Qf φ i c w ∈ U i) →
      HasDerivAt (Qf φ j c) (∏ i ∈ Finset.range j, deriv (φ i) (Qf φ i c w)) w := by
  intro j
  induction j with
  | zero => intro _; simpa [Qf] using hasDerivAt_id' w
  | succ j ih =>
    intro h
    have ih' := ih (fun i hi => h i (by omega))
    have hm := h j (by omega)
    have hφ : HasDerivAt (φ j) (deriv (φ j) (Qf φ j c w)) (Qf φ j c w) :=
      (((hbr j).2 _ hm).differentiableAt ((hbr j).1.mem_nhds hm)).hasDerivAt
    have := (hφ.comp w ih').add_const c
    rw [Finset.prod_range_succ, mul_comm]
    exact this

lemma Dd_cont (e : UnicriticalExponent) (a : ℂ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
    (hz0 : z 0 = a) (hzne : ∀ j, z j ≠ 0)
    (hzrel : ∀ j, z (j + 1) ∈ unicriticalCorr e.p e.q a (z j))
    (hbr : ∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ IsUnivalentBranch e 0 (U j) (φ j) ∧
      φ j (z j) + a = z (j + 1)) :
    ∀ j, ContinuousAt (fun p : ℂ × ℂ => ∏ i ∈ Finset.range j, deriv (φ i) (Qf φ i p.1 p.2))
      (a, a) ∧
      (∏ i ∈ Finset.range j, deriv (φ i) (Qf φ i a a)) =
        ∏ i ∈ Finset.range j, branchDerivFactor e a (z i) (z (i + 1)) := by
  have hbr' : ∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ DifferentiableOn ℂ (φ j) (U j) ∧
      φ j (z j) + a = z (j + 1) := fun j =>
    ⟨(hbr j).1, (hbr j).2.1, (hbr j).2.2.1.2.1, (hbr j).2.2.2⟩
  have hev := Qf_ev a z φ U hz0 hbr'
  have hder : ∀ i, deriv (φ i) (z i) = branchDerivFactor e a (z i) (z (i + 1)) := fun i =>
    (phi_hasDerivAt e a z φ U i (hbr i) (hzne i) (hzrel i)).deriv
  intro j
  induction j with
  | zero => simp [continuousAt_const]
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcont_i : ContinuousAt (fun p : ℂ × ℂ => deriv (φ j) (Qf φ j p.1 p.2)) (a, a) := by
      have hA : AnalyticAt ℂ (φ j) (z j) :=
        DifferentiableOn.analyticAt (hbr' j).2.2.1 ((hbr' j).1.mem_nhds (hbr' j).2.1)
      have hc1 : ContinuousAt (deriv (φ j)) (Qf φ j (a, a).1 (a, a).2) := by
        show ContinuousAt (deriv (φ j)) (Qf φ j a a)
        rw [(hev j).1]
        exact hA.deriv.continuousAt
      exact hc1.comp (f := fun p : ℂ × ℂ => Qf φ j p.1 p.2) (x := (a, a))
        (hev j).2.self_of_nhds.1.continuousAt
    refine ⟨?_, ?_⟩
    · simp only [Finset.prod_range_succ]
      exact ih1.mul hcont_i
    · rw [Finset.prod_range_succ, Finset.prod_range_succ, ih2, (hev j).1, hder]


lemma T_decomp (T : ℂ × ℂ →L[ℂ] ℂ) (x y : ℂ) : T (x, y) = T (x, 0) + y * T (0, 1) := by
  have : (x, y) = (x, (0:ℂ)) + y • ((0:ℂ), (1:ℂ)) := by ext <;> simp
  rw [this, map_add, map_smul]
  simp

noncomputable def mkEquiv (T : ℂ × ℂ →L[ℂ] ℂ) (hT : T (0, 1) ≠ 0) : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
  ContinuousLinearEquiv.equivOfInverse
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod T)
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod ((T (0, 1))⁻¹ • ((ContinuousLinearMap.snd ℂ ℂ ℂ) -
      T.comp ((ContinuousLinearMap.inl ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ ℂ ℂ)))))
    (fun p => by
      obtain ⟨x, y⟩ := p
      have := T_decomp T x y
      ext
      · simp
      · simp [this]
        field_simp)
    (fun p => by
      obtain ⟨x, y⟩ := p
      have := T_decomp T x ((T (0, 1))⁻¹ * (y - T (x, 0)))
      ext
      · simp
      · simp
        rw [this]
        field_simp
        ring)

lemma mkEquiv_coe (T : ℂ × ℂ →L[ℂ] ℂ) (hT : T (0, 1) ≠ 0) :
    ((mkEquiv T hT : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) =
      (ContinuousLinearMap.fst ℂ ℂ ℂ).prod T := rfl

lemma ift_abstract (F : ℂ × ℂ → ℂ) (a : ℂ)
    (hF : ∀ᶠ p in 𝓝 (a, a), ContDiffAt ℂ 1 F p) (hF0 : F (a, a) = 0)
    (hB : fderiv ℂ F (a, a) (0, 1) ≠ 0) :
    ∃ ξ : ℂ → ℂ, ξ a = a ∧ ContinuousAt ξ a ∧
      ∀ᶠ c in 𝓝 a, F (c, ξ c) = 0 ∧ DifferentiableAt ℂ ξ c := by
  have hFa : ContDiffAt ℂ 1 F (a, a) := hF.self_of_nhds
  have hΦ : ∀ p, ContDiffAt ℂ 1 F p →
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ => (p.1, F p)) p ∧
      HasFDerivAt (fun p : ℂ × ℂ => (p.1, F p))
        ((ContinuousLinearMap.fst ℂ ℂ ℂ).prod (fderiv ℂ F p)) p := by
    intro p hp
    exact ⟨contDiffAt_fst.prodMk hp,
      (hasFDerivAt_fst).prodMk (hp.differentiableAt (by norm_num)).hasFDerivAt⟩
  set Φ : ℂ × ℂ → ℂ × ℂ := fun p => (p.1, F p) with hΦdef
  have hf' : HasFDerivAt Φ ((mkEquiv (fderiv ℂ F (a, a)) hB : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) :
      (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (a, a) := by
    rw [mkEquiv_coe]; exact (hΦ _ hFa).2
  set H := (hΦ _ hFa).1.toOpenPartialHomeomorph Φ hf' (by norm_num) with hH
  have hHc : (H : ℂ × ℂ → ℂ × ℂ) = Φ := rfl
  have hsrc : (a, a) ∈ H.source := (hΦ _ hFa).1.mem_toOpenPartialHomeomorph_source hf' (by norm_num)
  have hHa : H (a, a) = (a, 0) := by rw [hHc]; simp [Φ, hF0]
  have htgt : (a, 0) ∈ H.target := by
    rw [← hHa]; exact H.map_source hsrc
  have hsymm_a : H.symm (a, 0) = (a, a) := by
    rw [← hHa]; exact H.left_inv hsrc
  have hcurve : ContinuousAt (fun c : ℂ => (c, (0:ℂ))) a := by fun_prop
  have hev_t : ∀ᶠ c in 𝓝 a, (c, (0:ℂ)) ∈ H.target :=
    hcurve.eventually_mem (H.open_target.mem_nhds htgt)
  have hsymm_cont : ContinuousAt H.symm (a, 0) := H.continuousAt_symm htgt
  have hBcont : ContinuousAt (fun p : ℂ × ℂ => fderiv ℂ F p (0, 1)) (a, a) := by
    have := hFa.fderiv_right (m := 0) (by norm_num)
    exact this.continuousAt.clm_apply continuousAt_const
  have hN : ∀ᶠ p in 𝓝 (a, a), ContDiffAt ℂ 1 F p ∧ fderiv ℂ F p (0, 1) ≠ 0 :=
    hF.and (hBcont.eventually_ne hB)
  have hN2 : ∀ᶠ c in 𝓝 a, H.symm (c, 0) ∈ {p | ContDiffAt ℂ 1 F p ∧ fderiv ℂ F p (0, 1) ≠ 0} := by
    have h1 : ContinuousAt (fun c : ℂ => H.symm (c, 0)) a := by
      have : ContinuousAt H.symm ((fun c : ℂ => (c, (0:ℂ))) a) := hsymm_cont
      exact ContinuousAt.comp (f := fun c : ℂ => (c, (0:ℂ))) (x := a) this hcurve
    have h2 : {p : ℂ × ℂ | ContDiffAt ℂ 1 F p ∧ fderiv ℂ F p (0, 1) ≠ 0} ∈
        𝓝 (H.symm ((fun c : ℂ => (c, (0:ℂ))) a)) := by
      show _ ∈ 𝓝 (H.symm (a, 0))
      rw [hsymm_a]; exact hN
    exact h1.eventually_mem h2
  refine ⟨fun c => (H.symm (c, 0)).2, ?_, ?_, ?_⟩
  · simp [hsymm_a]
  · exact continuousAt_snd.comp (ContinuousAt.comp (f := fun c : ℂ => (c, (0:ℂ))) (x := a) hsymm_cont hcurve)
  · filter_upwards [hev_t, hN2] with c hct hcN
    have hb : H.symm (c, 0) ∈ H.source := H.map_target hct
    have hHb : H (H.symm (c, 0)) = (c, 0) := H.right_inv hct
    rw [hHc] at hHb
    have hb1 : (H.symm (c, 0)).1 = c := congrArg Prod.fst hHb
    have hb2 : F (H.symm (c, 0)) = 0 := congrArg Prod.snd hHb
    refine ⟨?_, ?_⟩
    · have : ((H.symm (c, 0)).1, (H.symm (c, 0)).2) = (c, (H.symm (c, 0)).2) := by rw [hb1]
      simp only [← this]
      exact hb2
    · obtain ⟨hcd, hcB⟩ := hcN
      have hf'b : HasFDerivAt H ((mkEquiv (fderiv ℂ F (H.symm (c, 0))) hcB :
          (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ)) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (H.symm (c, 0)) := by
        rw [mkEquiv_coe, hHc]; exact (hΦ _ hcd).2
      have hsm : ContDiffAt ℂ 1 H.symm (c, 0) :=
        H.contDiffAt_symm hct hf'b (by rw [hHc]; exact (hΦ _ hcd).1)
      have hd : DifferentiableAt ℂ H.symm (c, 0) := hsm.differentiableAt (by norm_num)
      have hcd' : DifferentiableAt ℂ (fun c : ℂ => (c, (0:ℂ))) c := by fun_prop
      exact differentiableAt_snd.comp c (hd.comp c hcd')


lemma redIdx_zero (ℓ n : ℕ) (hℓ : 0 < ℓ) : redIdx ℓ n 0 = 0 := by simp [redIdx, hℓ]

lemma redIdx_ell (ℓ n : ℕ) : redIdx ℓ n ℓ = ℓ := by simp [redIdx]

lemma redIdx_succ (ℓ n j : ℕ) (hn : 0 < n) :
    redIdx ℓ n (j + 1) = redIdx ℓ n j + 1 ∨
      (redIdx ℓ n j + 1 = ℓ + n ∧ redIdx ℓ n (j + 1) = ℓ) := by
  unfold redIdx
  by_cases h1 : j + 1 < ℓ
  · left; simp [h1, show j < ℓ by omega]
  · by_cases h2 : j < ℓ
    · left
      have : j + 1 = ℓ := by omega
      simp [h1, h2, this]
    · have hm : (j + 1 - ℓ) % n = ((j - ℓ) % n + 1) % n := by
        rw [Nat.mod_add_mod]; congr 1; omega
      have hr := Nat.mod_lt (j - ℓ) hn
      simp only [h1, h2, if_false]
      rw [hm]
      by_cases h3 : (j - ℓ) % n + 1 < n
      · left; rw [Nat.mod_eq_of_lt h3]; omega
      · right
        have h4 : (j - ℓ) % n + 1 = n := by omega
        rw [h4, Nat.mod_self]
        omega

lemma redIdx_add_period (ℓ n j : ℕ) (hj : ℓ ≤ j) : redIdx ℓ n (j + n) = redIdx ℓ n j := by
  unfold redIdx
  have h1 : ¬ j + n < ℓ := by omega
  have h2 : ¬ j < ℓ := by omega
  simp only [h1, h2, if_false]
  have : j + n - ℓ = (j - ℓ) + n := by omega
  rw [this, Nat.add_mod_right]

structure DH (e : UnicriticalExponent) (a : ℂ) (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ)
    (U : ℕ → Set ℂ) : Prop where
  hℓ : 1 ≤ ℓ
  hn : 0 < n
  hz0 : z 0 = a
  hzrel : ∀ j, z (j + 1) ∈ unicriticalCorr e.p e.q a (z j)
  hzne : ∀ j, z j ≠ 0
  hbr : ∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ IsUnivalentBranch e 0 (U j) (φ j) ∧
    φ j (z j) + a = z (j + 1)
  hzorb : IsForwardOrbit e a 0 (zeroOrbit z)
  hbdd : ∃ R, ∀ j, ‖zeroOrbit z j‖ ≤ R
  huniq : ∀ w, IsForwardOrbit e a 0 w → (∃ R, ∀ j, ‖w j‖ ≤ R) → w = zeroOrbit z
  hzper : ∀ j ≥ ℓ, z (j + n) = z j
  hrep : IsRepellingCycle e a n (fun j => z (ℓ + j))

lemma DH_of_data (e : UnicriticalExponent) (a : ℂ) (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ)
    (U : ℕ → Set ℂ) (h : IsMisiurewiczOrbitData e a ℓ n z φ U) : DH e a ℓ n z φ U := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -, h11, -, -, -, h15⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h11, h15⟩

lemma bdf_ne_zero (e : UnicriticalExponent) (a x y : ℂ) (hx : x ≠ 0)
    (hrel : y ∈ unicriticalCorr e.p e.q a x) : branchDerivFactor e a x y ≠ 0 := by
  have hq := e.hq
  have hpq := e.hpq
  have hne : y - a ≠ 0 := by
    intro h
    have h2 : (y - a) ^ e.q = x ^ e.p := hrel
    rw [h, zero_pow (by omega)] at h2
    exact hx (pow_eq_zero_iff (by omega) |>.1 h2.symm)
  unfold branchDerivFactor
  have : (e.p : ℂ) ≠ 0 := by exact_mod_cast (by omega : e.p ≠ 0)
  have : (e.q : ℂ) ≠ 0 := by exact_mod_cast (by omega : e.q ≠ 0)
  positivity

lemma fderiv_apply_inr (F : ℂ × ℂ → ℂ) (p : ℂ × ℂ) (hF : DifferentiableAt ℂ F p) :
    HasDerivAt (fun w => F (p.1, w)) (fderiv ℂ F p (0, 1)) p.2 := by
  have h1 : HasDerivAt (fun w : ℂ => (p.1, w)) ((0:ℂ), (1:ℂ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id' p.2)
  exact hF.hasFDerivAt.comp_hasDerivAt p.2 h1

lemma exists_xi (e : UnicriticalExponent) (a : ℂ) (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ)
    (U : ℕ → Set ℂ) (h : DH e a ℓ n z φ U) :
    ∃ ξ : ℂ → ℂ, ξ a = a ∧ ContinuousAt ξ a ∧
      ∀ᶠ c in 𝓝 a, Qf φ (ℓ + n) c (ξ c) = Qf φ ℓ c (ξ c) ∧ DifferentiableAt ℂ ξ c := by
  have hbr' : ∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ DifferentiableOn ℂ (φ j) (U j) ∧
      φ j (z j) + a = z (j + 1) := fun j =>
    ⟨(h.hbr j).1, (h.hbr j).2.1, (h.hbr j).2.2.1.2.1, (h.hbr j).2.2.2⟩
  have hev := Qf_ev a z φ U h.hz0 hbr'
  have hEv : ∀ᶠ p in 𝓝 (a, a), ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ (ℓ + n) p.1 p.2) p ∧
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ ℓ p.1 p.2) p :=
    ((hev (ℓ + n)).2.and (hev ℓ).2).mono fun p hp => ⟨hp.1.1, hp.2.1⟩
  set F : ℂ × ℂ → ℂ := fun p => Qf φ (ℓ + n) p.1 p.2 - Qf φ ℓ p.1 p.2 with hFdef
  have hF : ∀ᶠ p in 𝓝 (a, a), ContDiffAt ℂ 1 F p := hEv.mono fun p hp => hp.1.sub hp.2
  have hF0 : F (a, a) = 0 := by
    simp only [hFdef, (hev (ℓ + n)).1, (hev ℓ).1]
    rw [h.hzper ℓ le_rfl]; ring
  -- derivative in w
  have hderiv := Dd_cont e a z φ U h.hz0 h.hzne h.hzrel h.hbr
  have hFd : DifferentiableAt ℂ F (a, a) := (hF.self_of_nhds.differentiableAt (by norm_num))
  have hmemU : ∀ i, Qf φ i a a ∈ U i := fun i => by rw [(hev i).1]; exact (h.hbr i).2.1
  have hdw := fderiv_apply_inr F (a, a) hFd
  have hdw2 : HasDerivAt (fun w => F (a, w))
      ((∏ i ∈ Finset.range (ℓ + n), deriv (φ i) (Qf φ i a a)) -
        ∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i a a)) a := by
    have hU' : ∀ j, IsOpen (U j) ∧ DifferentiableOn ℂ (φ j) (U j) := fun j =>
      ⟨(h.hbr j).1, (h.hbr j).2.2.1.2.1⟩
    exact (Qf_hasDerivAt φ U hU' a a (ℓ + n) (fun i _ => hmemU i)).sub
      (Qf_hasDerivAt φ U hU' a a ℓ (fun i _ => hmemU i))
  have hBeq := hdw.unique hdw2
  have hB : fderiv ℂ F (a, a) (0, 1) ≠ 0 := by
    rw [hBeq, (hderiv (ℓ + n)).2, (hderiv ℓ).2, Finset.prod_range_add]
    have hA : ∏ i ∈ Finset.range ℓ, branchDerivFactor e a (z i) (z (i + 1)) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => bdf_ne_zero e a _ _ (h.hzne i) (h.hzrel i)
    have hlam : ‖∏ i ∈ Finset.range n, branchDerivFactor e a (z (ℓ + i)) (z (ℓ + i + 1))‖ > 1 :=
      h.hrep.2.2
    have hlam1 : ∏ i ∈ Finset.range n, branchDerivFactor e a (z (ℓ + i)) (z (ℓ + i + 1)) ≠ 1 := by
      intro h1; rw [h1] at hlam; simp at hlam
    intro h0
    apply hlam1
    have : (∏ i ∈ Finset.range ℓ, branchDerivFactor e a (z i) (z (i + 1))) *
        (∏ x ∈ Finset.range n, branchDerivFactor e a (z (ℓ + x)) (z (ℓ + x + 1)) - 1) = 0 := by
      rw [← h0]; ring
    rcases mul_eq_zero.1 this with h2 | h2
    · exact absurd h2 hA
    · exact sub_eq_zero.1 h2
  obtain ⟨ξ, h1, h2, h3⟩ := ift_abstract F a hF hF0 hB
  exact ⟨ξ, h1, h2, h3.mono fun c hc => ⟨sub_eq_zero.1 hc.1, hc.2⟩⟩


lemma rel_sub_ne (e : UnicriticalExponent) (c x y : ℂ) (hx : x ≠ 0)
    (hrel : y ∈ unicriticalCorr e.p e.q c x) : y - c ≠ 0 := by
  have hq := e.hq
  have hpq := e.hpq
  intro h
  have h2 : (y - c) ^ e.q = x ^ e.p := hrel
  rw [h, zero_pow (by omega)] at h2
  exact hx (pow_eq_zero_iff (by omega) |>.1 h2.symm)

lemma cm_cont (e : UnicriticalExponent) (a : ℂ) (y : ℕ → ℂ → ℂ)
    (hy : ∀ j, ContinuousAt (y j) a) (hden : ∀ j, y (j + 1) a - a ≠ 0) (m : ℕ) :
    ContinuousAt (fun c => ∏ i ∈ Finset.range m, branchDerivFactor e c (y i c) (y (i + 1) c)) a := by
  induction m with
  | zero => simpa using continuousAt_const
  | succ m ih =>
    simp only [Finset.prod_range_succ]
    refine ih.mul ?_
    unfold branchDerivFactor
    exact (continuousAt_const.mul ((hy m).pow _)).div
      (((hy (m + 1)).sub continuousAt_id).pow _) (pow_ne_zero _ (hden m))

lemma cm_diff (e : UnicriticalExponent) (c : ℂ) (y : ℕ → ℂ → ℂ)
    (hy : ∀ j, DifferentiableAt ℂ (y j) c) (hden : ∀ j, y (j + 1) c - c ≠ 0) (m : ℕ) :
    DifferentiableAt ℂ
      (fun c => ∏ i ∈ Finset.range m, branchDerivFactor e c (y i c) (y (i + 1) c)) c := by
  induction m with
  | zero => simpa using differentiableAt_const _
  | succ m ih =>
    simp only [Finset.prod_range_succ]
    refine ih.mul ?_
    unfold branchDerivFactor
    exact ((differentiableAt_const _).mul ((hy m).pow _)).div
      (((hy (m + 1)).sub differentiableAt_id).pow _) (pow_ne_zero _ (hden m))

lemma Qstep (e : UnicriticalExponent) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (c x : ℂ) (i : ℕ)
    (hb : IsUnivalentBranch e 0 (U i) (φ i)) (hx : x ∈ U i) :
    φ i x + c ∈ unicriticalCorr e.p e.q c x := by
  have := hb.2.2.2 x hx
  simpa [unicriticalCorr] using this

lemma zz_rel_of (e : UnicriticalExponent) (ℓ n : ℕ) (hn : 0 < n) (φ : ℕ → ℂ → ℂ)
    (U : ℕ → Set ℂ)
    (hb : ∀ i, IsUnivalentBranch e 0 (U i) (φ i)) (c ξc : ℂ)
    (hU : ∀ i < ℓ + n, Qf φ i c ξc ∈ U i)
    (hF : Qf φ (ℓ + n) c ξc = Qf φ ℓ c ξc) (j : ℕ) :
    Qf φ (redIdx ℓ n (j + 1)) c ξc ∈ unicriticalCorr e.p e.q c (Qf φ (redIdx ℓ n j) c ξc) := by
  have hstep : ∀ i < ℓ + n, Qf φ (i + 1) c ξc ∈ unicriticalCorr e.p e.q c (Qf φ i c ξc) :=
    fun i hi => Qstep e φ U c _ i (hb i) (hU i hi)
  have hlt := redIdx_lt ℓ n j hn
  rcases redIdx_succ ℓ n j hn with h1 | ⟨h2, h3⟩
  · rw [h1]; exact hstep _ hlt
  · have : Qf φ ℓ c ξc = Qf φ (redIdx ℓ n j + 1) c ξc := by rw [h2, hF]
    rw [h3, this]
    exact hstep _ hlt

lemma inj_of (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ) (ℓ : ℕ) (a A : ℂ) (r : ℝ) (hA : A ≠ 0)
    (hbr : ∀ j, IsOpen (U j) ∧ DifferentiableOn ℂ (φ j) (U j))
    (hP : ∀ c ∈ Metric.ball a r, ∀ w ∈ Metric.ball a r,
      (∀ i < ℓ, Qf φ i c w ∈ U i) ∧
      ‖(∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c w)) - A‖ < ‖A‖ / 2)
    (c : ℂ) (hc : c ∈ Metric.ball a r) :
    Set.InjOn (Qf φ ℓ c) (Metric.ball a r) ∧ DifferentiableOn ℂ (Qf φ ℓ c) (Metric.ball a r) := by
  have hd : ∀ w ∈ Metric.ball a r, HasDerivAt (Qf φ ℓ c)
      (∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c w)) w := fun w hw =>
    Qf_hasDerivAt φ U hbr c w ℓ (hP c hc w hw).1
  refine ⟨?_, fun w hw => (hd w hw).differentiableAt.differentiableWithinAt⟩
  intro w hw w' hw' heq
  have hf : ∀ x ∈ Metric.ball a r, HasDerivWithinAt (fun x => Qf φ ℓ c x - A * x)
      ((∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c x)) - A) (Metric.ball a r) x := by
    intro x hx
    have h1 := (hd x hx).sub ((hasDerivAt_id' x).const_mul A)
    have h2 : (∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c x)) - A =
        (∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c x)) - A * 1 := by ring
    rw [h2]
    exact h1.hasDerivWithinAt
  have hb : ∀ x ∈ Metric.ball a r,
      ‖(∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c x)) - A‖ ≤ ‖A‖ / 2 :=
    fun x hx => (hP c hc x hx).2.le
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hb (convex_ball a r) hw hw'
  simp only [heq] at this
  have h2 : ‖A * (w - w')‖ ≤ ‖A‖ / 2 * ‖w' - w‖ := by
    have : (Qf φ ℓ c w' - A * w') - (Qf φ ℓ c w' - A * w) = A * (w - w') := by ring
    rw [← this]; exact_mod_cast ‹_›
  rw [norm_mul, norm_sub_rev w' w] at h2
  have hpos : 0 < ‖A‖ := norm_pos_iff.2 hA
  have : ‖w - w'‖ ≤ 0 := by nlinarith [norm_nonneg (w - w')]
  exact sub_eq_zero.1 (norm_le_zero_iff.1 this)


lemma motion_exists (e : UnicriticalExponent) (a : ℂ) (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ)
    (U : ℕ → Set ℂ) (h : DH e a ℓ n z φ U) :
    ∃ (W : Set ℂ) (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ),
      IsMisiurewiczMotion e a ℓ n z φ U W zz lam := by
  classical
  have hbr' : ∀ j, IsOpen (U j) ∧ z j ∈ U j ∧ DifferentiableOn ℂ (φ j) (U j) ∧
      φ j (z j) + a = z (j + 1) := fun j =>
    ⟨(h.hbr j).1, (h.hbr j).2.1, (h.hbr j).2.2.1.2.1, (h.hbr j).2.2.2⟩
  have hbrU : ∀ j, IsOpen (U j) ∧ DifferentiableOn ℂ (φ j) (U j) := fun j =>
    ⟨(h.hbr j).1, (h.hbr j).2.2.1.2.1⟩
  have hbU : ∀ j, IsUnivalentBranch e 0 (U j) (φ j) := fun j => (h.hbr j).2.2.1
  have hev := Qf_ev a z φ U h.hz0 hbr'
  obtain ⟨ξ, hξa, hξc, hξ⟩ := exists_xi e a ℓ n z φ U h
  have hn := h.hn
  have hℓ : 0 < ℓ := h.hℓ
  let zz : ℕ → ℂ → ℂ := fun j c => Qf φ (redIdx ℓ n j) c (ξ c)
  let lam : ℂ → ℂ := fun c => cycleMultiplier e c n (fun j => zz (ℓ + j) c)
  have hT : Tendsto (fun c => (c, ξ c)) (𝓝 a) (𝓝 (a, a)) := by
    have := (continuousAt_id.prodMk hξc).tendsto
    simpa [hξa] using this
  have hE : ∀ᶠ p in 𝓝 (a, a), ∀ i ∈ Finset.range (ℓ + n + 1),
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ i p.1 p.2) p ∧ Qf φ i p.1 p.2 ∈ U i :=
    (Filter.eventually_all_finset _).2 fun i _ => (hev i).2
  have hE' : ∀ᶠ c in 𝓝 a, ∀ i ∈ Finset.range (ℓ + n + 1),
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ i p.1 p.2) (c, ξ c) ∧ Qf φ i c (ξ c) ∈ U i :=
    hT.eventually hE
  have hQc : ∀ i, ContinuousAt (fun c => Qf φ i c (ξ c)) a := by
    intro i
    have h1 : ContinuousAt (fun p : ℂ × ℂ => Qf φ i p.1 p.2) (a, a) :=
      (hev i).2.self_of_nhds.1.continuousAt
    have := h1.tendsto.comp hT
    unfold ContinuousAt
    show Tendsto _ _ (𝓝 (Qf φ i a (ξ a)))
    rw [hξa]
    exact this
  have hza : ∀ j, zz j a = z j := by
    intro j
    show Qf φ (redIdx ℓ n j) a (ξ a) = z j
    rw [hξa, (hev _).1]
    have := redIdx_shift ℓ n z h.hzper j 0
    simp only [add_zero] at this
    exact this.symm
  have hzzc : ∀ j, ContinuousAt (zz j) a := fun j => hQc _
  -- relation and periodicity near a
  have hrel_ev : ∀ᶠ c in 𝓝 a, (∀ j, zz (j + 1) c ∈ unicriticalCorr e.p e.q c (zz j c)) ∧
      ∀ j ≥ ℓ, zz (j + n) c = zz j c := by
    filter_upwards [hξ, hE'] with c hc1 hc2
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · exact zz_rel_of e ℓ n hn φ U hbU c (ξ c)
        (fun i hi => (hc2 i (Finset.mem_range.2 (by omega))).2) hc1.1 j
    · show Qf φ (redIdx ℓ n (j + n)) c (ξ c) = Qf φ (redIdx ℓ n j) c (ξ c)
      rw [redIdx_add_period ℓ n j hj]
  have huniq_ev := uniq_orbit e a ℓ n z zz hn h.hzne h.hzrel h.hzorb h.hbdd h.huniq hzzc hza
    hrel_ev
  -- nonvanishing
  have hnz : ∀ᶠ c in 𝓝 a, ∀ i ∈ Finset.range (ℓ + n), Qf φ i c (ξ c) ≠ 0 := by
    refine (Filter.eventually_all_finset _).2 fun i _ => ?_
    have h1 : Qf φ i a (ξ a) = z i := by rw [hξa]; exact (hev i).1
    exact (hQc i).eventually_ne (by rw [h1]; exact h.hzne i)
  -- multiplier
  have hden : ∀ j, (fun j c => zz (ℓ + j) c) (j + 1) a - a ≠ 0 := by
    intro j
    show zz (ℓ + (j + 1)) a - a ≠ 0
    rw [hza]
    exact rel_sub_ne e a _ _ (h.hzne _) (h.hzrel (ℓ + j))
  have hlamc : ContinuousAt lam a :=
    cm_cont e a (fun j c => zz (ℓ + j) c) (fun j => hzzc (ℓ + j)) hden n
  have hlama : lam a = cycleMultiplier e a n (fun j => z (ℓ + j)) := by
    simp only [lam, hza]
  have hmult : ∀ᶠ c in 𝓝 a, 1 < ‖lam c‖ := by
    refine (continuousAt_const.eventually_lt hlamc.norm ?_)
    rw [hlama]; exact h.hrep.2.2
  -- the ball on which the branches are well behaved
  have hderiv := Dd_cont e a z φ U h.hz0 h.hzne h.hzrel h.hbr ℓ
  set A : ℂ := ∏ i ∈ Finset.range ℓ, branchDerivFactor e a (z i) (z (i + 1)) with hAdef
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => bdf_ne_zero e a _ _ (h.hzne i) (h.hzrel i)
  have hApos : 0 < ‖A‖ / 2 := by have := norm_pos_iff.2 hA; linarith
  have hPev : ∀ᶠ p in 𝓝 (a, a), (∀ i ∈ Finset.range (ℓ + n + 1),
      ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ i p.1 p.2) p ∧ Qf φ i p.1 p.2 ∈ U i) ∧
      ‖(∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i p.1 p.2)) - A‖ < ‖A‖ / 2 := by
    refine hE.and ?_
    have := hderiv.1.tendsto.eventually (Metric.ball_mem_nhds _ hApos)
    filter_upwards [this] with p hp
    rw [hderiv.2] at hp
    simpa [dist_eq_norm] using hp
  obtain ⟨ε, hε, hPε⟩ := Metric.eventually_nhds_iff.1 hPev
  have hPball : ∀ c ∈ Metric.ball a ε, ∀ w ∈ Metric.ball a ε,
      (∀ i ∈ Finset.range (ℓ + n + 1),
        ContDiffAt ℂ 1 (fun p : ℂ × ℂ => Qf φ i p.1 p.2) (c, w) ∧ Qf φ i c w ∈ U i) ∧
      ‖(∏ i ∈ Finset.range ℓ, deriv (φ i) (Qf φ i c w)) - A‖ < ‖A‖ / 2 := by
    intro c hc w hw
    apply hPε
    rw [Prod.dist_eq]
    simp only [Metric.mem_ball] at hc hw
    exact max_lt hc hw
  have hξball : ∀ᶠ c in 𝓝 a, ξ c ∈ Metric.ball a ε := by
    have := hξc.tendsto
    rw [hξa] at this
    exact this.eventually (Metric.ball_mem_nhds a hε)
  have hall := hξ.and (hE'.and (hnz.and (hmult.and (huniq_ev.and hξball))))
  obtain ⟨δ, hδ, hallδ⟩ := Metric.eventually_nhds_iff.1 hall
  set r := min ε δ with hr
  have hrε : r ≤ ε := min_le_left _ _
  have hrδ : r ≤ δ := min_le_right _ _
  have hrpos : 0 < r := lt_min hε hδ
  have hWε : Metric.ball a r ⊆ Metric.ball a ε := Metric.ball_subset_ball hrε
  have hgood : ∀ c ∈ Metric.ball a r, _ := fun c hc =>
    @hallδ c (lt_of_lt_of_le (by simpa [dist_eq_norm] using hc) hrδ)
  have hinj : ∀ c ∈ Metric.ball a r, Set.InjOn (Qf φ ℓ c) (Metric.ball a ε) ∧
      DifferentiableOn ℂ (Qf φ ℓ c) (Metric.ball a ε) := fun c hc =>
    inj_of φ U ℓ a A ε hA hbrU (fun c hc w hw =>
      ⟨fun i hi => ((hPball c hc w hw).1 i (Finset.mem_range.2 (by omega))).2,
        (hPball c hc w hw).2⟩) c (hWε hc)
  have hzzd : ∀ j, ∀ c ∈ Metric.ball a r, DifferentiableAt ℂ (zz j) c := by
    intro j c hc
    obtain ⟨hc1, hc2, -⟩ := hgood c hc
    have hq := (hc2 (redIdx ℓ n j) (Finset.mem_range.2 (by have := redIdx_lt ℓ n j hn; omega))).1
    have hq' : DifferentiableAt ℂ (fun p : ℂ × ℂ => Qf φ (redIdx ℓ n j) p.1 p.2) (c, ξ c) :=
      hq.differentiableAt (by norm_num)
    exact hq'.comp c (differentiableAt_id.prodMk hc1.2)
  have hrelW : ∀ c ∈ Metric.ball a r, ∀ j,
      zz (j + 1) c ∈ unicriticalCorr e.p e.q c (zz j c) := by
    intro c hc j
    obtain ⟨hc1, hc2, -⟩ := hgood c hc
    exact zz_rel_of e ℓ n hn φ U hbU c (ξ c)
      (fun i hi => (hc2 i (Finset.mem_range.2 (by omega))).2) hc1.1 j
  have hperW : ∀ c ∈ Metric.ball a r, ∀ j ≥ ℓ, zz (j + n) c = zz j c := by
    intro c hc j hj
    show Qf φ (redIdx ℓ n (j + n)) c (ξ c) = Qf φ (redIdx ℓ n j) c (ξ c)
    rw [redIdx_add_period ℓ n j hj]
  have hnzW : ∀ c ∈ Metric.ball a r, ∀ j, zz j c ≠ 0 := by
    intro c hc j
    obtain ⟨-, -, hc3, -⟩ := hgood c hc
    exact hc3 _ (Finset.mem_range.2 (redIdx_lt ℓ n j hn))
  refine ⟨Metric.ball a r, zz, lam, Metric.isOpen_ball, Metric.mem_ball_self hrpos, ?_, hza, hrelW,
    ?_, hperW, ?_, fun c _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro j c hc
    exact (hzzd j c hc).differentiableWithinAt
  · intro c hc
    exact (hgood c hc).2.2.2.2.1
  · intro c hc
    refine ⟨⟨hn, fun i => ?_, fun i => hrelW c hc (ℓ + i)⟩, fun i => hnzW c hc _, ?_⟩
    · show zz (ℓ + (i + n)) c = zz (ℓ + i) c
      have := hperW c hc (ℓ + i) (by omega)
      rwa [show ℓ + i + n = ℓ + (i + n) by ring] at this
    · exact (hgood c hc).2.2.2.1
  · intro c hc
    have hc' := hc
    have hd : DifferentiableAt ℂ lam c := by
      refine cm_diff e c (fun j c => zz (ℓ + j) c) (fun j => hzzd (ℓ + j) c hc) (fun j => ?_) n
      exact rel_sub_ne e c _ _ (hnzW c hc _) (hrelW c hc (ℓ + j))
    exact hd.differentiableWithinAt
  · intro c hc
    rw [perturbedComp_zero_eq]
    show Qf φ ℓ c (Qf φ (redIdx ℓ n 0) c (ξ c)) = Qf φ (redIdx ℓ n ℓ) c (ξ c)
    rw [redIdx_zero ℓ n hℓ, redIdx_ell]
    rfl
  · intro c hc
    simp only [perturbedComp_zero_eq]
    exact ⟨(hinj c hc).1.mono hWε, (hinj c hc).2.mono hWε⟩
  · intro c hc w hw hweq
    simp only [perturbedComp_zero_eq] at hweq
    have hξc' : ξ c ∈ Metric.ball a ε := (hgood c hc).2.2.2.2.2
    have h2 : Qf φ ℓ c w = Qf φ ℓ c (ξ c) := by
      rw [hweq]
      show Qf φ (redIdx ℓ n ℓ) c (ξ c) = _
      rw [redIdx_ell]
    have := (hinj c hc).1 (hWε hw) hξc' h2
    rw [this]
    show ξ c = Qf φ (redIdx ℓ n 0) c (ξ c)
    rw [redIdx_zero ℓ n hℓ]
    rfl
  · intro p hp
    simp only [perturbedComp_zero_eq]
    have hc := hp.1
    have hw := hp.2
    have := ((hPball p.1 (hWε hc) p.2 (hWε hw)).1 ℓ
      (Finset.mem_range.2 (by omega))).1
    exact (this.differentiableAt (by norm_num)).differentiableWithinAt

end MultibrotCorr

open MultibrotCorr in
theorem solution (e : UnicriticalExponent) (a : ℂ) (ha : IsMisiurewicz e a) :
    ∃ (ℓ n : ℕ) (z : ℕ → ℂ) (φ : ℕ → ℂ → ℂ) (U : ℕ → Set ℂ)
      (W : Set ℂ) (zz : ℕ → ℂ → ℂ) (lam : ℂ → ℂ),
      IsMisiurewiczOrbitData e a ℓ n z φ U ∧
      IsMisiurewiczMotion e a ℓ n z φ U W zz lam := by
  obtain ⟨⟨ℓ, n, z, φ, U, hd⟩, -, -⟩ := theorem_D e a ha
  obtain ⟨W, zz, lam, hm⟩ := motion_exists e a ℓ n z φ U (DH_of_data e a ℓ n z φ U hd)
  exact ⟨ℓ, n, z, φ, U, W, zz, lam, hd, hm⟩
