-- Prove2me | solution 1 for MMDarkPool.Exchange.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-02T02:03:56.348066+00:00
-- url     : https://prove2.me/submissions/a9f10c27-2730-4280-b3b5-b2750db81805

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Model


open Set Filter Topology

namespace MMDPAux

lemma super_antitone (G : ℝ → ℝ) (c d : ℝ) (hcd : c < d)
    (hG : ContinuousOn G (Icc c d))
    (hsup : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ∀ t0 ∈ Ioo c d,
      IsLocalMin (fun t => G t - ψ t) t0 → deriv ψ t0 ≤ 0) :
    G d ≤ G c := by
  by_contra hlt
  push_neg at hlt
  set ε := (G d - G c) / 4 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hπ := Real.pi_gt_three
  have hπ4 := Real.pi_lt_four
  have hcont : ContinuousWithinAt G (Icc c d) c := hG c ⟨le_refl _, hcd.le⟩
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hδG⟩ := hcont (ε * (Real.pi / 4)) (by positivity)
  set t1 := c + min (δ / 2) ((d - c) / 2) with ht1
  have hm1 : 0 < min (δ / 2) ((d - c) / 2) := lt_min (by linarith) (by linarith)
  have hm2 : min (δ / 2) ((d - c) / 2) ≤ δ / 2 := min_le_left _ _
  have hm3 : min (δ / 2) ((d - c) / 2) ≤ (d - c) / 2 := min_le_right _ _
  have ht1c : c < t1 := by rw [ht1]; linarith
  have ht1d : t1 < d := by rw [ht1]; linarith
  have hGt1 : G t1 < G c + ε * (Real.pi / 4) := by
    have := hδG (x := t1) ⟨ht1c.le, ht1d.le⟩ (by
      rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
    rw [Real.dist_eq] at this
    have := (abs_lt.mp this).2
    linarith
  set K := 1 / (t1 - c) with hK
  have hKpos : 0 < K := by rw [hK]; apply div_pos one_pos; linarith
  set ψ : ℝ → ℝ := fun t => ε * Real.arctan (K * (t - c)) with hψ
  have hψc : ContDiff ℝ 1 ψ :=
    contDiff_const.mul (Real.contDiff_arctan.comp (contDiff_const.mul (contDiff_id.sub contDiff_const)))
  have hψd : ∀ t, HasDerivAt ψ (ε * (1 / (1 + (K * (t - c)) ^ 2) * (K * 1))) t := by
    intro t
    have h1 : HasDerivAt (fun t => K * (t - c)) (K * 1) t :=
      ((hasDerivAt_id t).sub_const c).const_mul K
    exact (h1.arctan).const_mul ε
  set g := fun t => G t - ψ t with hg
  have hgc : ContinuousOn g (Icc c d) := hG.sub (hψc.continuous.continuousOn)
  obtain ⟨t0, ht0, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hcd.le) hgc
  have hgt1 : g t1 < g c := by
    simp only [hg, hψ]
    have : K * (t1 - c) = 1 := by rw [hK]; field_simp [show t1 - c ≠ 0 by linarith]
    rw [this, Real.arctan_one]
    simp
    linarith
  have hgd : g c < g d := by
    simp only [hg, hψ]
    have := Real.arctan_lt_pi_div_two (K * (d - c))
    simp
    nlinarith
  have hle1 := hmin (show t1 ∈ Icc c d from ⟨ht1c.le, ht1d.le⟩)
  have hle2 := hmin (show d ∈ Icc c d from ⟨hcd.le, le_refl _⟩)
  simp only [mem_ofPred_eq] at hle1 hle2
  have ht0c : t0 ≠ c := by rintro rfl; linarith
  have ht0d : t0 ≠ d := by rintro rfl; linarith
  have ht0' : t0 ∈ Ioo c d := ⟨lt_of_le_of_ne ht0.1 (Ne.symm ht0c), lt_of_le_of_ne ht0.2 ht0d⟩
  have hloc : IsLocalMin g t0 := hmin.isLocalMin (Icc_mem_nhds ht0'.1 ht0'.2)
  have := hsup ψ hψc t0 ht0' hloc
  rw [(hψd t0).deriv] at this
  have : 0 < ε * (1 / (1 + (K * (t0 - c)) ^ 2) * (K * 1)) := by positivity
  linarith

lemma visc_to_classical (y F : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hy : ContinuousOn y (Icc a b)) (hF : ContinuousOn F (Icc a b))
    (hsub : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∀ t0 ∈ Ioo a b,
      IsLocalMax (fun t => y t - φ t) t0 → 0 ≤ deriv φ t0 + F t0)
    (hsup : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → ∀ t0 ∈ Ioo a b,
      IsLocalMin (fun t => y t - φ t) t0 → deriv φ t0 + F t0 ≤ 0) :
    ∀ t ∈ Icc a b, HasDerivWithinAt y (-F t) (Icc a b) t := by
  set Ft : ℝ → ℝ := fun t => F (projIcc a b hab.le t) with hFt
  have hFtc : Continuous Ft := hF.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc a b hab.le t).2)
  have hFt_eq : ∀ t ∈ Icc a b, Ft t = F t := by
    intro t ht; simp only [hFt, projIcc_of_mem hab.le ht]
  set I : ℝ → ℝ := fun t => ∫ s in a..t, Ft s with hI
  have hId : ∀ t, HasDerivAt I (Ft t) t := fun t => (hFtc.integral_hasStrictDerivAt a t).hasDerivAt
  have hIderiv : deriv I = Ft := funext fun t => (hId t).deriv
  have hIc : ContDiff ℝ 1 I := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun t => (hId t).differentiableAt, by rw [hIderiv]; exact hFtc⟩
  set G : ℝ → ℝ := fun t => y t + I t with hG
  have hGc : ContinuousOn G (Icc a b) := hy.add (hIc.continuous.continuousOn)
  have key : ∀ c d, a < c → c < d → d < b → G c = G d := by
    intro c d hac hcd hdb
    have hsub' : Icc c d ⊆ Icc a b := Icc_subset_Icc hac.le hdb.le
    have hsub'' : Ioo c d ⊆ Ioo a b := Ioo_subset_Ioo hac.le hdb.le
    have h1 : G d ≤ G c := by
      apply super_antitone G c d hcd (hGc.mono hsub')
      intro ψ hψ t0 ht0 hloc
      have hφ : ContDiff ℝ 1 (fun t => ψ t - I t) := hψ.sub hIc
      have hloc' : IsLocalMin (fun t => y t - (ψ t - I t)) t0 := by
        convert hloc using 2; simp only [hG]; ring
      have := hsup _ hφ t0 (hsub'' ht0) hloc'
      have hd : deriv (fun t => ψ t - I t) t0 = deriv ψ t0 - Ft t0 := by
        exact ((hψ.differentiable one_ne_zero t0).hasDerivAt.sub (hId t0)).deriv
      rw [hd, hFt_eq t0 (Ioo_subset_Icc_self (hsub'' ht0))] at this
      linarith
    have h2 : (fun t => -G t) d ≤ (fun t => -G t) c := by
      apply super_antitone (fun t => -G t) c d hcd ((hGc.mono hsub').neg)
      intro ψ hψ t0 ht0 hloc
      have hφ : ContDiff ℝ 1 (fun t => -ψ t - I t) := hψ.neg.sub hIc
      have hloc' : IsLocalMax (fun t => y t - (-ψ t - I t)) t0 := by
        unfold IsLocalMin IsMinFilter at hloc
        unfold IsLocalMax IsMaxFilter
        filter_upwards [hloc] with s hs
        simp only [hG] at hs ⊢
        linarith
      have := hsub _ hφ t0 (hsub'' ht0) hloc'
      have hd : deriv (fun t => -ψ t - I t) t0 = -deriv ψ t0 - Ft t0 := by
        exact ((hψ.differentiable one_ne_zero t0).hasDerivAt.neg.sub (hId t0)).deriv
      rw [hd, hFt_eq t0 (Ioo_subset_Icc_self (hsub'' ht0))] at this
      linarith
    simp only at h2
    linarith
  have hconst : ∀ t ∈ Icc a b, G t = G b := by
    have hmid : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have heq : EqOn G (fun _ => G ((a + b) / 2)) (Ioo a b) := by
      intro s hs
      rcases lt_trichotomy s ((a + b) / 2) with h | h | h
      · exact key s _ hs.1 h hmid.2
      · rw [h]
      · exact (key _ s hmid.1 h hs.2).symm
    have heq' := heq.of_subset_closure hGc continuousOn_const Ioo_subset_Icc_self
      (by rw [closure_Ioo hab.ne])
    intro t ht
    rw [heq' ht, heq' ⟨hab.le, le_refl b⟩]
  intro t ht
  have hd : HasDerivWithinAt (fun s => G b - I s) (-Ft t) (Icc a b) t :=
    ((hId t).const_sub (G b)).hasDerivWithinAt
  rw [hFt_eq t ht] at hd
  apply hd.congr
  · intro s hs
    have := hconst s hs
    simp only [hG] at this ⊢
    linarith
  · have := hconst t ht
    simp only [hG] at this ⊢
    linarith

end MMDPAux


open Set Filter Topology MMDarkPool.Exchange

namespace MMDPAux

lemma jump_mem_grid {P : Params} {q : ℤ} (hq : q ∈ Grid P) {L : Vol} (hL : Admissible P q L)
    (i : Side) (j : Pool) : q - phiSide i * (L i j : ℤ) ∈ Grid P := by
  obtain ⟨_, _, h1, h2⟩ := hL
  simp only [Grid, Set.mem_setOf_eq] at hq ⊢
  cases i <;> cases j <;> simp [phiSide] <;> omega

lemma Ia_nonneg (L : Vol) : 0 ≤ Ia L := by
  unfold Ia; split_ifs <;> positivity

lemma Ib_nonneg (L : Vol) : 0 ≤ Ib L := by
  unfold Ib; split_ifs <;> positivity

lemma Ia_add_Ib_le (L : Vol) : Ia L + Ib L ≤ 1 := by
  unfold Ia Ib
  split_ifs with h
  · norm_num
  · have : (0 : ℝ) < (L Side.a Pool.l : ℝ) + (L Side.b Pool.l : ℝ) := by
      have : (0 : ℕ) < L Side.a Pool.l + L Side.b Pool.l := Nat.pos_of_ne_zero h
      exact_mod_cast this
    rw [← add_div, div_self this.ne']

lemma psi_nonneg (i : Side) (j : Pool) (L : Vol) : 0 ≤ psi i j L := by
  cases i <;> cases j <;> simp [psi, Ia_nonneg, Ib_nonneg]

lemma phiD_nonneg (i : Side) (κ : MMDarkPool.Exchange.Lat) (L : Vol) : 0 ≤ phiD i κ L := by
  cases i <;> cases κ <;> simp [phiD, Ia_nonneg, Ib_nonneg]

lemma Lat_sum (f : MMDarkPool.Exchange.Lat → ℝ) : ∑ κ : MMDarkPool.Exchange.Lat, f κ = f Lat.lat + f Lat.nonlat := by
  apply Fintype.sum_eq_add Lat.lat Lat.nonlat (by decide)
  intro x hx; cases x <;> simp at hx

lemma sum_phiD_le (i : Side) (L : Vol) : ∑ κ : MMDarkPool.Exchange.Lat, phiD i κ L ≤ 1 := by
  rw [Lat_sum]
  cases i <;> simp [phiD] <;> linarith [Ia_add_Ib_le L]

/-- intensity bound -/
def Lam (P : Params) : ℝ := P.ε + P.A Pool.l + P.A Pool.d

lemma lam_nonneg {P : Params} (hP : Standing P) (i : Side) (j : Pool) (L : Vol) :
    0 ≤ lam P i j L := by
  obtain ⟨_, _, _, _, _, hε, hA, _⟩ := hP
  unfold lam; split_ifs
  · exact hε.le
  · exact mul_nonneg (hA j).1.le (Real.exp_pos _).le

lemma lam_le {P : Params} (hP : Standing P) (i : Side) (j : Pool) (L : Vol) :
    lam P i j L ≤ Lam P := by
  obtain ⟨_, _, hσ, _, _, hε, hA, _⟩ := hP
  unfold lam Lam; split_ifs
  · linarith [(hA Pool.l).1, (hA Pool.d).1]
  · have he : Real.exp (-(P.θ j / P.σ) * psi i j L) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ P.θ j / P.σ := div_nonneg (hA j).2.le hσ.le
      nlinarith [psi_nonneg i j L]
    have h1 : P.A j * Real.exp (-(P.θ j / P.σ) * psi i j L) ≤ P.A j :=
      mul_le_of_le_one_right (hA j).1.le he
    cases j <;> linarith [(hA Pool.l).1, (hA Pool.d).1]

lemma lamK_nonneg {P : Params} (hP : Standing P) (q : ℤ) (i : Side) (j : Pool) (k : ℕ) (L : Vol) :
    0 ≤ lamK P q i j k L := by
  unfold lamK; split_ifs
  · exact lam_nonneg hP i j L
  · exact le_rfl

lemma lamK_le {P : Params} (hP : Standing P) (q : ℤ) (i : Side) (j : Pool) (k : ℕ) (L : Vol) :
    lamK P q i j k L ≤ Lam P := by
  unfold lamK; split_ifs
  · exact lam_le hP i j L
  · obtain ⟨_, _, _, _, _, hε, hA, _⟩ := hP
    unfold Lam; linarith [(hA Pool.l).1, (hA Pool.d).1]

lemma lamK_ne_zero {P : Params} {q : ℤ} {i : Side} {j : Pool} {k : ℕ} {L : Vol}
    (h : lamK P q i j k L ≠ 0) : L i j = k := by
  unfold lamK at h; split_ifs at h with h'
  · exact h'.2
  · exact absurd rfl h

lemma Ecal_le {P : Params} (hP : Standing P) (L : Vol) (i : Side) (j : Pool) (zk : ℝ) (q : ℤ) :
    Ecal P L i j zk q ≤ 1 / P.γ := by
  obtain ⟨_, _, _, hγ, _⟩ := hP
  have hg : 0 < 1 / P.γ := by positivity
  cases j
  · simp only [Ecal]
    apply mul_le_of_le_one_right hg.le
    linarith [Real.exp_pos (-P.γ * litGain P L zk q i)]
  · simp only [Ecal]
    apply mul_le_of_le_one_right hg.le
    calc ∑ κ : MMDarkPool.Exchange.Lat, (1 - Real.exp (-P.γ * darkGain P L zk q i κ)) * phiD i κ L
        ≤ ∑ κ : MMDarkPool.Exchange.Lat, phiD i κ L := by
          apply Finset.sum_le_sum; intro κ _
          have := phiD_nonneg i κ L
          have := Real.exp_pos (-P.γ * darkGain P L zk q i κ)
          nlinarith
      _ ≤ 1 := sum_phiD_le i L

noncomputable def D0 (P : Params) : ℝ := ∑ _i : Side, ∑ j : Pool, ∑ _k : {k : ℕ // k ∈ P.V j}, Lam P * (1 + P.η / P.γ)

lemma Lam_nonneg {P : Params} (hP : Standing P) : 0 ≤ Lam P := by
  obtain ⟨_, _, _, _, _, hε, hA, _⟩ := hP
  unfold Lam; linarith [(hA Pool.l).1, (hA Pool.d).1]

lemma D0_nonneg {P : Params} (hP : Standing P) : 0 ≤ D0 P := by
  have hL := Lam_nonneg hP
  obtain ⟨_, _, _, hγ, hη, _⟩ := hP
  unfold D0
  apply Finset.sum_nonneg; intro i _
  apply Finset.sum_nonneg; intro j _
  apply Finset.sum_nonneg; intro k _
  have : 0 ≤ P.η / P.γ := div_nonneg hη.le hγ.le
  exact mul_nonneg hL (by linarith)

lemma Ucal_le {P : Params} (hP : Standing P) {Lstar : Inc P → ℤ → Vol}
    (hL : IsBestResponse P Lstar) {q : ℤ} (hq : q ∈ Grid P) (w : ℤ → ℝ)
    (hw : ∀ r ∈ Grid P, w r < 0) (x : ℝ × Inc P) :
    Ucal P Lstar x q w ≤ D0 P * (-w q) := by
  have hLam := Lam_nonneg hP
  have hP' := hP
  obtain ⟨_, _, hσ, hγ, hη, _⟩ := hP'
  have hwq := hw q hq
  have hadm := (hL q hq x.2).1
  unfold Ucal D0
  simp only [Finset.sum_mul]
  have h1 : w q * ((P.η / 2) * P.σ ^ 2 * P.γ * (x.1 + (q : ℝ)) ^ 2 +
      (P.η ^ 2 * P.σ ^ 2 / 2) * x.1 ^ 2) ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg hwq.le
    have a1 : 0 ≤ (P.η / 2) * P.σ ^ 2 * P.γ * (x.1 + (q : ℝ)) ^ 2 := by positivity
    have a2 : 0 ≤ (P.η ^ 2 * P.σ ^ 2 / 2) * x.1 ^ 2 := by positivity
    linarith
  have h2 : ∑ i : Side, ∑ j : Pool, ∑ k : {k : ℕ // k ∈ P.V j},
      lamK P q i j k.1 (Lstar x.2 q) *
        (Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * w (q - phiSide i * (k.1 : ℤ)) -
          w q * (1 + P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q))
      ≤ ∑ i : Side, ∑ j : Pool, ∑ k : {k : ℕ // k ∈ P.V j}, Lam P * (1 + P.η / P.γ) * (-w q) := by
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    apply Finset.sum_le_sum; intro k _
    have hX : 0 ≤ -w q * (1 + P.η / P.γ) := by
      have : 0 ≤ P.η / P.γ := div_nonneg hη.le hγ.le
      apply mul_nonneg (by linarith); linarith
    by_cases h0 : lamK P q i j k.1 (Lstar x.2 q) = 0
    · rw [h0, zero_mul]
      have : 0 ≤ Lam P * (1 + P.η / P.γ) * (-w q) := by
        rw [mul_assoc, mul_comm (1 + P.η / P.γ)]; exact mul_nonneg hLam hX
      exact this
    · have hk := lamK_ne_zero h0
      have hq' : q - phiSide i * (k.1 : ℤ) ∈ Grid P := by
        have := jump_mem_grid hq hadm i j
        rw [hk] at this; exact this
      have hwq' := hw _ hq'
      have he := Real.exp_pos (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j))
      have hE := Ecal_le hP (Lstar x.2 q) i j (x.2 i j k) q
      have hEη : P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q ≤ P.η / P.γ := by
        have := mul_le_mul_of_nonneg_left hE hη.le
        rw [mul_one_div] at this; exact this
      have hbr : Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * w (q - phiSide i * (k.1 : ℤ)) -
          w q * (1 + P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q) ≤ -w q * (1 + P.η / P.γ) := by
        have : Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * w (q - phiSide i * (k.1 : ℤ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos he.le hwq'.le
        nlinarith
      have hl0 := lamK_nonneg hP q i j k.1 (Lstar x.2 q)
      have hl1 := lamK_le hP q i j k.1 (Lstar x.2 q)
      calc lamK P q i j k.1 (Lstar x.2 q) * _ ≤ lamK P q i j k.1 (Lstar x.2 q) * (-w q * (1 + P.η / P.γ)) :=
            mul_le_mul_of_nonneg_left hbr hl0
        _ ≤ Lam P * (-w q * (1 + P.η / P.γ)) := mul_le_mul_of_nonneg_right hl1 hX
        _ = Lam P * (1 + P.η / P.γ) * (-w q) := by ring
  linarith

lemma Ucal_congr {P : Params} {Lstar : Inc P → ℤ → Vol}
    (hL : IsBestResponse P Lstar) {q : ℤ} (hq : q ∈ Grid P) (w w' : ℤ → ℝ)
    (h : ∀ r ∈ Grid P, w r = w' r) (x : ℝ × Inc P) :
    Ucal P Lstar x q w = Ucal P Lstar x q w' := by
  have hadm := (hL q hq x.2).1
  unfold Ucal
  rw [h q hq]
  congr 1
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  by_cases h0 : lamK P q i j k.1 (Lstar x.2 q) = 0
  · rw [h0, zero_mul, zero_mul]
  · have hk := lamK_ne_zero h0
    have hq' : q - phiSide i * (k.1 : ℤ) ∈ Grid P := by
      have := jump_mem_grid hq hadm i j
      rw [hk] at this; exact this
    rw [h _ hq']

lemma Ucal_lin {P : Params} (Lstar : Inc P → ℤ → Vol) (x : ℝ × Inc P) (q : ℤ) (w w' : ℤ → ℝ) (a b : ℝ) :
    Ucal P Lstar x q (fun r => a * w r + b * w' r) = a * Ucal P Lstar x q w + b * Ucal P Lstar x q w' := by
  have : ∀ i j (k : {k : ℕ // k ∈ P.V j}),
      lamK P q i j k.1 (Lstar x.2 q) *
        (Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * (a * w (q - phiSide i * (k.1 : ℤ)) + b * w' (q - phiSide i * (k.1 : ℤ))) -
          (a * w q + b * w' q) * (1 + P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q))
      = a * (lamK P q i j k.1 (Lstar x.2 q) *
        (Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * w (q - phiSide i * (k.1 : ℤ)) -
          w q * (1 + P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q))) +
        b * (lamK P q i j k.1 (Lstar x.2 q) *
        (Real.exp (P.η * (x.2 i j k - (k.1 : ℝ) * P.c j)) * w' (q - phiSide i * (k.1 : ℤ)) -
          w' q * (1 + P.η * Ecal P (Lstar x.2 q) i j (x.2 i j k) q))) := by
    intros; ring
  unfold Ucal
  simp only [this]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end MMDPAux


open Set Filter Topology MMDarkPool.Exchange Metric

namespace MMDPAux

abbrev Idx (P : Params) := {q : ℤ // q ∈ Finset.Icc (-(P.qbar:ℤ)) (P.qbar:ℤ)}

lemma idx_grid {P : Params} (i : Idx P) : (i : ℤ) ∈ Grid P := by
  have := Finset.mem_Icc.mp i.2
  exact this

lemma grid_idx {P : Params} {q : ℤ} (hq : q ∈ Grid P) :
    q ∈ Finset.Icc (-(P.qbar:ℤ)) (P.qbar:ℤ) := Finset.mem_Icc.mpr hq

noncomputable def ext {P : Params} (u : Idx P → ℝ) : ℤ → ℝ :=
  fun q => if h : q ∈ Finset.Icc (-(P.qbar:ℤ)) (P.qbar:ℤ) then u ⟨q, h⟩ else 0

lemma ext_apply {P : Params} (u : Idx P → ℝ) (i : Idx P) : ext u i = u i := by
  simp [ext, i.2]

lemma ext_lin {P : Params} (u v : Idx P → ℝ) (a b : ℝ) :
    ext (a • u + b • v) = fun r => a * ext u r + b * ext v r := by
  funext r; unfold ext; split_ifs <;> simp

def cone (P : Params) : Set (Idx P → ℝ) := Set.univ.pi (fun _ => Set.Iio (0:ℝ))

lemma ext_neg {P : Params} {u : Idx P → ℝ} (hu : u ∈ cone P) : ∀ r ∈ Grid P, ext u r < 0 := by
  intro r hr
  have := grid_idx hr
  simp only [ext, this, dite_true]
  exact hu _ (mem_univ _)

noncomputable def hH (P : Params) (Lstar : Inc P → ℤ → Vol) (i : Idx P) (u : Idx P → ℝ) : ℝ :=
  ⨆ x : ℝ × Inc P, Ucal P Lstar x i (ext u)

noncomputable def ell (P : Params) (Lstar : Inc P → ℤ → Vol) (i : Idx P) :
    (Idx P → ℝ) →ₗ[ℝ] ℝ where
  toFun u := Ucal P Lstar 0 i (ext u)
  map_add' u v := by
    have := Ucal_lin Lstar 0 (i:ℤ) (ext u) (ext v) 1 1
    rw [show ext (u + v) = fun r => 1 * ext u r + 1 * ext v r by rw [← ext_lin]; simp]
    simpa using this
  map_smul' c u := by
    have := Ucal_lin Lstar 0 (i:ℤ) (ext u) (ext u) c 0
    rw [show ext (c • u) = fun r => c * ext u r + 0 * ext u r by rw [← ext_lin]; simp]
    simpa using this

noncomputable def D1 (P : Params) (Lstar : Inc P → ℤ → Vol) : ℝ :=
  ∑ i : Idx P, ‖LinearMap.toContinuousLinearMap (ell P Lstar i)‖

lemma D1_nonneg (P : Params) (Lstar : Inc P → ℤ → Vol) : 0 ≤ D1 P Lstar :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma U0_ge (P : Params) (Lstar : Inc P → ℤ → Vol) (i : Idx P) (u : Idx P → ℝ) :
    -(D1 P Lstar * ‖u‖) ≤ Ucal P Lstar 0 i (ext u) := by
  have h := (LinearMap.toContinuousLinearMap (ell P Lstar i)).le_opNorm u
  have he : (LinearMap.toContinuousLinearMap (ell P Lstar i)) u = Ucal P Lstar 0 i (ext u) := rfl
  rw [he, Real.norm_eq_abs] at h
  have hs : ‖LinearMap.toContinuousLinearMap (ell P Lstar i)‖ ≤ D1 P Lstar :=
    Finset.single_le_sum (f := fun j => ‖LinearMap.toContinuousLinearMap (ell P Lstar j)‖)
      (fun j _ => norm_nonneg _) (Finset.mem_univ i)
  have := neg_abs_le (Ucal P Lstar 0 i (ext u))
  have := mul_le_mul_of_nonneg_right hs (norm_nonneg u)
  linarith

section
variable {P : Params} (hP : Standing P) {Lstar : Inc P → ℤ → Vol} (hL : IsBestResponse P Lstar)
include hP hL

lemma bdd_U {u : Idx P → ℝ} (hu : u ∈ cone P) (i : Idx P) :
    BddAbove (range fun x => Ucal P Lstar x i (ext u)) := by
  refine ⟨D0 P * (-u i), ?_⟩
  rintro _ ⟨x, rfl⟩
  have := Ucal_le hP hL (idx_grid i) (ext u) (ext_neg hu) x
  rwa [ext_apply] at this

lemma hH_le {u : Idx P → ℝ} (hu : u ∈ cone P) (i : Idx P) : hH P Lstar i u ≤ D0 P * (-u i) := by
  apply ciSup_le; intro x
  have := Ucal_le hP hL (idx_grid i) (ext u) (ext_neg hu) x
  rwa [ext_apply] at this

lemma U_le_hH {u : Idx P → ℝ} (hu : u ∈ cone P) (i : Idx P) (x : ℝ × Inc P) :
    Ucal P Lstar x i (ext u) ≤ hH P Lstar i u := le_ciSup (bdd_U hP hL hu i) x

lemma hH_ge {u : Idx P → ℝ} (hu : u ∈ cone P) (i : Idx P) : -(D1 P Lstar * ‖u‖) ≤ hH P Lstar i u :=
  (U0_ge P Lstar i u).trans (U_le_hH hP hL hu i 0)

lemma Hcal_eq {u : Idx P → ℝ} (hu : u ∈ cone P) (i : Idx P) :
    Hcal P Lstar i (ext u) = (hH P Lstar i u : EReal) := by
  unfold Hcal hH
  exact (Monotone.map_ciSup_of_continuousAt continuous_coe_real_ereal.continuousAt
    (fun a b h => EReal.coe_le_coe_iff.mpr h) (bdd_U hP hL hu i)).symm

lemma hH_convex (i : Idx P) : ConvexOn ℝ (cone P) (hH P Lstar i) := by
  refine ⟨convex_pi (fun _ _ => convex_Iio 0), ?_⟩
  intro u hu v hv a b ha hb hab
  simp only [smul_eq_mul]
  apply ciSup_le; intro x
  rw [ext_lin, Ucal_lin]
  have h1 := U_le_hH hP hL hu i x
  have h2 := U_le_hH hP hL hv i x
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

lemma lip_box (c ρ r : ℝ) (hρ : 0 ≤ ρ) (hρr : ρ < r) (hcr : c + r ≤ 0) :
    ∃ K : NNReal, ∀ i, LipschitzOnWith K (hH P Lstar i) (closedBall (fun _ => c) ρ) := by
  set c0 : Idx P → ℝ := fun _ => c with hc0
  have hr : 0 < r := by linarith
  have hball : ball c0 r ⊆ cone P := by
    intro u hu
    rw [mem_ball, dist_pi_lt_iff hr] at hu
    intro j _
    have := hu j
    rw [Real.dist_eq] at this
    simp only [Set.mem_Iio]
    have := (abs_lt.mp this).2
    simp only [hc0] at this
    linarith
  have hc0n : ‖c0‖ ≤ |c| := by
    rw [pi_norm_le_iff_of_nonneg (abs_nonneg c)]
    intro j; simp [hc0]
  have : ∀ i, ∃ K : NNReal, LipschitzOnWith K (hH P Lstar i) (closedBall c0 ρ) := by
    intro i
    have hconv := (hH_convex hP hL i).subset hball (convex_ball _ _)
    have hbd : Bornology.IsBounded (hH P Lstar i '' ball c0 r) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨(D0 P + D1 P Lstar) * (|c| + r), ?_⟩
      rintro _ ⟨u, hu, rfl⟩
      have hu' := hball hu
      have hn : ‖u‖ ≤ |c| + r := by
        have h1 : ‖u‖ ≤ ‖c0‖ + dist u c0 := by
          have := norm_le_insert' u c0
          rw [dist_eq_norm]; linarith
        rw [mem_ball] at hu
        linarith
      have hui : |u i| ≤ ‖u‖ := by
        have := norm_le_pi_norm u i
        rwa [Real.norm_eq_abs] at this
      have h1 := hH_le hP hL hu' i
      have h2 := hH_ge hP hL hu' i
      have hD0 := D0_nonneg hP
      have hD1 := D1_nonneg P Lstar
      have hnu := norm_nonneg u
      rw [Real.norm_eq_abs, abs_le]
      have hneg : -u i ≤ |u i| := neg_le_abs (u i)
      constructor
      · nlinarith
      · nlinarith
    obtain ⟨K, hK⟩ := hconv.exists_lipschitzOnWith_of_isBounded (r' := (ρ + r) / 2) (by linarith) hbd
    exact ⟨K, hK.mono (closedBall_subset_ball (by linarith))⟩
  choose K hK using this
  refine ⟨∑ i, K i, fun i => (hK i).weaken ?_⟩
  exact Finset.single_le_sum (f := K) (fun _ _ => zero_le) (Finset.mem_univ i)

end

end MMDPAux


open Set Filter Topology MMDarkPool.Exchange Metric

namespace MMDPAux

def Box (P : Params) (r0 Rb : ℝ) : Set (Idx P → ℝ) := {u | ∀ j, -(2 * Rb) ≤ u j ∧ u j ≤ -(r0 / 2)}

lemma Box_sub_cone {P : Params} {r0 Rb : ℝ} (hr0 : 0 < r0) : Box P r0 Rb ⊆ cone P := by
  intro u hu j _
  simp only [Set.mem_Iio]
  linarith [(hu j).2]

lemma Box_eq_ball {P : Params} {r0 Rb : ℝ} (hρ : 0 ≤ Rb - r0 / 4) :
    Box P r0 Rb = closedBall (fun _ => -(Rb + r0 / 4)) (Rb - r0 / 4) := by
  ext u
  rw [mem_closedBall, dist_pi_le_iff hρ]
  simp only [Box, mem_setOf_eq, Real.dist_eq, abs_le]
  constructor
  · intro h j; constructor <;> linarith [(h j).1, (h j).2]
  · intro h j; constructor <;> linarith [(h j).1, (h j).2]

lemma Box_norm {P : Params} {r0 Rb : ℝ} (hr0 : 0 < r0) (hRb : 0 ≤ Rb) {u : Idx P → ℝ}
    (hu : u ∈ Box P r0 Rb) : ‖u‖ ≤ 2 * Rb := by
  rw [pi_norm_le_iff_of_nonneg (by linarith)]
  intro j
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [(hu j).1, (hu j).2]

section
variable {P : Params} (hP : Standing P) {Lstar : Inc P → ℤ → Vol} (hL : IsBestResponse P Lstar)
include hP hL

lemma lip_Box {r0 Rb : ℝ} (hr0 : 0 < r0) (hRb : r0 / 4 ≤ Rb) :
    ∃ K : NNReal, ∀ i, LipschitzOnWith K (hH P Lstar i) (Box P r0 Rb) := by
  obtain ⟨K, hK⟩ := lip_box hP hL (-(Rb + r0 / 4)) (Rb - r0 / 4) (Rb + r0 / 8)
    (by linarith) (by linarith) (by linarith)
  exact ⟨K, fun i => by rw [Box_eq_ball (by linarith)]; exact hK i⟩

lemma abs_hH_le {u : Idx P → ℝ} (hu : u ∈ cone P) (i : Idx P) :
    |hH P Lstar i u| ≤ (D0 P + D1 P Lstar) * ‖u‖ := by
  have h1 := hH_le hP hL hu i
  have h2 := hH_ge hP hL hu i
  have hui : |u i| ≤ ‖u‖ := by
    have := norm_le_pi_norm u i
    rwa [Real.norm_eq_abs] at this
  have hneg : -u i ≤ |u i| := neg_le_abs (u i)
  have hD0 := D0_nonneg hP
  have hD1 := D1_nonneg P Lstar
  have hnu := norm_nonneg u
  rw [abs_le]
  constructor
  · nlinarith
  · nlinarith

end

/-- clamp into the box -/
noncomputable def clampB (r0 Rb : ℝ) (x : ℝ) : ℝ := max (-(2 * Rb)) (min (-(r0 / 2)) x)

lemma clampB_lip (r0 Rb x y : ℝ) : |clampB r0 Rb x - clampB r0 Rb y| ≤ |x - y| := by
  unfold clampB
  have h1 := abs_max_sub_max_le_max (-(2 * Rb)) (min (-(r0 / 2)) x) (-(2 * Rb)) (min (-(r0 / 2)) y)
  have h2 := abs_min_sub_min_le_max (-(r0 / 2)) x (-(r0 / 2)) y
  simp only [sub_self, abs_zero] at h1 h2
  have h3 : max 0 |x - y| = |x - y| := max_eq_right (abs_nonneg _)
  rw [h3] at h2
  have h4 : max 0 |min (-(r0 / 2)) x - min (-(r0 / 2)) y| = |min (-(r0 / 2)) x - min (-(r0 / 2)) y| :=
    max_eq_right (abs_nonneg _)
  rw [h4] at h1
  linarith

lemma clampB_mem (r0 Rb x : ℝ) (h : r0 / 2 ≤ 2 * Rb) :
    -(2 * Rb) ≤ clampB r0 Rb x ∧ clampB r0 Rb x ≤ -(r0 / 2) := by
  unfold clampB
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma clampB_of {r0 Rb x : ℝ} (h1 : -(2 * Rb) ≤ x) (h2 : x ≤ -(r0 / 2)) : clampB r0 Rb x = x := by
  unfold clampB
  rw [min_eq_right h2, max_eq_right h1]

lemma clampB_abs {r0 Rb x : ℝ} (h0 : 0 ≤ r0) (h1 : r0 ≤ 2) (hR : r0 / 2 ≤ 2 * Rb) :
    |clampB r0 Rb x| ≤ |x| + 1 := by
  unfold clampB
  rw [abs_le]
  constructor
  · apply le_max_of_le_right
    apply le_min
    · linarith [abs_nonneg x]
    · linarith [neg_abs_le x]
  · apply max_le
    · linarith [abs_nonneg x]
    · exact (min_le_left _ _).trans (by linarith [abs_nonneg x])

noncomputable def clampV {P : Params} (r0 Rb : ℝ) (u : Idx P → ℝ) : Idx P → ℝ := fun j => clampB r0 Rb (u j)

lemma clampV_mem {P : Params} {r0 Rb : ℝ} (h : r0 / 2 ≤ 2 * Rb) (u : Idx P → ℝ) :
    clampV r0 Rb u ∈ Box P r0 Rb := fun j => clampB_mem r0 Rb (u j) h

lemma clampV_dist {P : Params} (r0 Rb : ℝ) (u v : Idx P → ℝ) :
    dist (clampV r0 Rb u) (clampV r0 Rb v) ≤ dist u v := by
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  rw [Real.dist_eq]
  exact (clampB_lip r0 Rb (u j) (v j)).trans (by rw [← Real.dist_eq]; exact dist_le_pi_dist u v j)

lemma clampV_norm {P : Params} {r0 Rb : ℝ} (h0 : 0 ≤ r0) (h1 : r0 ≤ 2) (hR : r0 / 2 ≤ 2 * Rb)
    (u : Idx P → ℝ) : ‖clampV r0 Rb u‖ ≤ ‖u‖ + 1 := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro j
  rw [Real.norm_eq_abs]
  have := norm_le_pi_norm u j
  rw [Real.norm_eq_abs] at this
  exact (clampB_abs (x := u j) h0 h1 hR).trans (by linarith)

lemma clampV_of {P : Params} {r0 Rb : ℝ} {u : Idx P → ℝ} (hu : u ∈ Box P r0 Rb) :
    clampV r0 Rb u = u := funext fun j => clampB_of (hu j).1 (hu j).2

end MMDPAux


open Set Filter Topology MMDarkPool.Exchange Metric

namespace MMDPAux

lemma exists_traj {P : Params} (hP : Standing P) {Lstar : Inc P → ℤ → Vol}
    (hL : IsBestResponse P Lstar) :
    ∃ (r0 Rb : ℝ) (α : ℝ → Idx P → ℝ), 0 < r0 ∧ r0 ≤ 1 / 2 ∧ 1 ≤ Rb ∧
      α 0 = (fun _ => -1) ∧
      (∀ t ∈ Icc 0 P.T, HasDerivWithinAt α (fun i => hH P Lstar i (α t)) (Icc 0 P.T) t) ∧
      (∀ t ∈ Icc 0 P.T, ∀ i, -Rb ≤ α t i ∧ α t i ≤ -r0) := by
  have hT : 0 < P.T := hP.1
  set C := D0 P + D1 P Lstar with hCdef
  have hC : 0 ≤ C := add_nonneg (D0_nonneg hP) (D1_nonneg P Lstar)
  have hD0 := D0_nonneg hP
  set r0 := Real.exp (-(D0 P + 1) * P.T) / 2 with hr0def
  have hr0 : 0 < r0 := by positivity
  have hexpT : Real.exp (-(D0 P + 1) * P.T) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have hr0' : r0 ≤ 1 / 2 := by rw [hr0def]; linarith
  set Rb := max (gronwallBound 1 C C P.T) 1 with hRbdef
  have hRb : 1 ≤ Rb := le_max_right _ _
  have hR2 : r0 / 2 ≤ 2 * Rb := by linarith
  obtain ⟨K, hK⟩ := lip_Box hP hL hr0 (by linarith : r0 / 4 ≤ Rb)
  set Fv : (Idx P → ℝ) → (Idx P → ℝ) := fun u i => hH P Lstar i (clampV r0 Rb u) with hFv
  have hFlip : LipschitzWith K Fv := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_pi_le_iff (by positivity)]
    intro i
    have := (hK i).dist_le_mul _ (clampV_mem hR2 u) _ (clampV_mem hR2 v)
    exact this.trans (mul_le_mul_of_nonneg_left (clampV_dist _ _ u v) K.2)
  set Lb := C * (2 * Rb) with hLb
  have hLb0 : 0 ≤ Lb := by positivity
  have hcl : ∀ u : Idx P → ℝ, clampV r0 Rb u ∈ cone P := fun u =>
    Box_sub_cone hr0 (clampV_mem hR2 u)
  have hFbd : ∀ u, ‖Fv u‖ ≤ Lb := by
    intro u
    rw [pi_norm_le_iff_of_nonneg hLb0]
    intro i
    rw [Real.norm_eq_abs]
    have h1 := abs_hH_le hP hL (hcl u) i
    have h2 := Box_norm hr0 (by linarith) (clampV_mem hR2 u)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hC)
  have hFgr : ∀ u, ‖Fv u‖ ≤ C * ‖u‖ + C := by
    intro u
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    rw [Real.norm_eq_abs]
    have h1 := abs_hH_le hP hL (hcl u) i
    have h2 := clampV_norm (P := P) hr0.le (by linarith) hR2 u
    calc _ ≤ C * ‖clampV r0 Rb u‖ := h1
      _ ≤ C * (‖u‖ + 1) := mul_le_mul_of_nonneg_left h2 hC
      _ = C * ‖u‖ + C := by ring
  have hPL : IsPicardLindelof (fun _ => Fv) (tmin := 0) (tmax := P.T) ⟨0, ⟨le_rfl, hT.le⟩⟩
      (fun _ => (-1 : ℝ)) ⟨Lb * P.T, by positivity⟩ 0 ⟨Lb, hLb0⟩ K := by
    refine ⟨fun _ _ => hFlip.lipschitzOnWith, fun _ _ => continuousOn_const,
      fun _ _ x _ => hFbd x, ?_⟩
    show Lb * max (P.T - 0) (0 - 0) ≤ Lb * P.T - 0
    rw [sub_zero, sub_self, sub_zero, max_eq_left hT.le]
  obtain ⟨α, hα0, hα⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt (mem_closedBall_self le_rfl)
  simp only at hα0
  have hαc : ContinuousOn α (Icc 0 P.T) := fun t ht => (hα t ht).continuousWithinAt
  have hαR : ∀ t ∈ Icc 0 P.T, HasDerivWithinAt α (Fv (α t)) (Ici t) t → True := fun _ _ _ => trivial
  -- Gronwall bound on the norm
  have hgr : ∀ t ∈ Icc 0 P.T, ‖α t‖ ≤ Rb := by
    have := norm_le_gronwallBound_of_norm_deriv_right_le (f := α) (f' := fun t => Fv (α t))
      (δ := 1) (K := C) (ε := C) (a := 0) (b := P.T) hαc
      (fun x hx => (hα x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1)))
      (by rw [hα0, pi_norm_le_iff_of_nonneg zero_le_one]; intro; simp)
      (fun x _ => hFgr (α x))
    intro t ht
    have h1 := this t ht
    rw [sub_zero] at h1
    have h2 := gronwallBound_mono (δ := 1) (K := C) (ε := C) zero_le_one hC hC ht.2
    exact h1.trans (h2.trans (le_max_left _ _))
  -- upper barrier
  have hup : ∀ i, ∀ t ∈ Icc 0 P.T, α t i ≤ -Real.exp (-(D0 P + 1) * t) / 2 := by
    intro i t ht
    refine image_le_of_deriv_right_lt_deriv_boundary (a := 0) (b := P.T) (f := fun t => α t i)
      (f' := fun t => Fv (α t) i) (B := fun t => -Real.exp (-(D0 P + 1) * t) / 2)
      (B' := fun t => (D0 P + 1) * Real.exp (-(D0 P + 1) * t) / 2) ?_ ?_ ?_ ?_ ?_ ht
    · exact (continuous_apply i).comp_continuousOn hαc
    · intro x hx
      have := (hα x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
        (mem_of_superset (Icc_mem_nhdsGE hx.2) (Icc_subset_Icc_left hx.1))
      exact hasDerivWithinAt_pi.1 this i
    · simp [hα0]; norm_num
    · intro x
      have h1 : HasDerivAt (fun y => -(D0 P + 1) * y) (-(D0 P + 1)) x := by
        simpa using (hasDerivAt_id x).const_mul (-(D0 P + 1))
      exact (h1.exp.neg.div_const 2).congr_deriv (by ring)
    · intro x hx hxeq
      beta_reduce at hxeq ⊢
      have hxe : Real.exp (-(D0 P + 1) * x) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hx.1]
      have hxe2 : Real.exp (-(D0 P + 1) * P.T) ≤ Real.exp (-(D0 P + 1) * x) := by
        apply Real.exp_le_exp.mpr; nlinarith [hx.2]
      have hpos := Real.exp_pos (-(D0 P + 1) * x)
      have hcl_eq : clampV r0 Rb (α x) i = α x i := by
        unfold clampV
        apply clampB_of
        · rw [hxeq]; linarith
        · rw [hxeq]; rw [hr0def]; linarith
      have h1 := hH_le hP hL (hcl (α x)) i
      rw [hcl_eq, hxeq] at h1
      simp only [hFv]
      nlinarith
  refine ⟨r0, Rb, α, hr0, hr0', hRb, hα0, ?_, ?_⟩
  · have hbox : ∀ t ∈ Icc 0 P.T, α t ∈ Box P r0 Rb := by
      intro t ht j
      have h1 := hup j t ht
      have h2 := hgr t ht
      have h3 : |α t j| ≤ ‖α t‖ := by
        have := norm_le_pi_norm (α t) j; rwa [Real.norm_eq_abs] at this
      have hxe2 : Real.exp (-(D0 P + 1) * P.T) ≤ Real.exp (-(D0 P + 1) * t) := by
        apply Real.exp_le_exp.mpr; nlinarith [ht.2]
      constructor
      · linarith [neg_abs_le (α t j)]
      · rw [hr0def] at *; linarith
    intro t ht
    have := hα t ht
    have heq : Fv (α t) = fun i => hH P Lstar i (α t) := by
      simp only [hFv, clampV_of (hbox t ht)]
    rwa [heq] at this
  · intro t ht j
    have h1 := hup j t ht
    have h2 := hgr t ht
    have h3 : |α t j| ≤ ‖α t‖ := by
      have := norm_le_pi_norm (α t) j; rwa [Real.norm_eq_abs] at this
    have hxe2 : Real.exp (-(D0 P + 1) * P.T) ≤ Real.exp (-(D0 P + 1) * t) := by
      apply Real.exp_le_exp.mpr; nlinarith [ht.2]
    constructor
    · linarith [neg_abs_le (α t j)]
    · rw [hr0def]; linarith

end MMDPAux


open Set Filter Topology MMDarkPool.Exchange Metric

namespace MMDPAux

lemma Hcal_congr {P : Params} {Lstar : Inc P → ℤ → Vol} (hL : IsBestResponse P Lstar) {q : ℤ}
    (hq : q ∈ Grid P) (w w' : ℤ → ℝ) (h : ∀ r ∈ Grid P, w r = w' r) :
    Hcal P Lstar q w = Hcal P Lstar q w' := by
  unfold Hcal
  congr 1
  funext x
  rw [Ucal_congr hL hq w w' h x]

lemma ext_idx {P : Params} (u : Idx P → ℝ) {q : ℤ} (hq : q ∈ Grid P) :
    ext u q = u ⟨q, grid_idx hq⟩ := by
  simp [ext, grid_idx hq]

lemma uniq {P : Params} (hP : Standing P) {Lstar : Inc P → ℤ → Vol} (hL : IsBestResponse P Lstar)
    {r0 Rb : ℝ} (hr0 : 0 < r0) (hr0' : r0 ≤ 1 / 2) (hRb : 1 ≤ Rb) (V : ℝ → Idx P → ℝ)
    (hVc : ContinuousOn V (Icc 0 P.T))
    (hVd : ∀ t ∈ Icc 0 P.T, HasDerivWithinAt V (fun i => -hH P Lstar i (V t)) (Icc 0 P.T) t)
    (hVb : ∀ t ∈ Icc 0 P.T, ∀ j, -Rb ≤ V t j ∧ V t j ≤ -r0) (hVT : V P.T = fun _ => -1)
    (w : ℝ → ℤ → ℝ) (hw : IsViscositySolution P Lstar w) :
    ∀ t ∈ Icc 0 P.T, ∀ i : Idx P, w t i = V t i := by
  have hT : 0 < P.T := hP.1
  obtain ⟨K, hK⟩ := lip_Box hP hL hr0 (by linarith : r0 / 4 ≤ Rb)
  set W : ℝ → Idx P → ℝ := fun t i => w t i with hWdef
  have hWc : ContinuousOn W (Icc 0 P.T) := continuousOn_pi.2 fun i => (hw i (idx_grid i)).1
  have hWT : W P.T = V P.T := by
    funext i; simp only [hWdef, hVT, (hw i (idx_grid i)).2.1]
  have hHW : ∀ t, W t ∈ cone P → ∀ i : Idx P,
      Hcal P Lstar (i : ℤ) (w t) = (hH P Lstar i (W t) : EReal) := by
    intro t hc i
    rw [Hcal_congr hL (idx_grid i) (w t) (ext (W t)) (fun r hr => by rw [ext_idx _ hr])]
    exact Hcal_eq hP hL hc i
  set S := {t | t ∈ Icc 0 P.T ∧ ∀ s ∈ Icc t P.T, W s = V s} with hSdef
  have hTS : P.T ∈ S := ⟨⟨hT.le, le_rfl⟩, fun s hs => by rw [le_antisymm hs.2 hs.1]; exact hWT⟩
  have hSne : S.Nonempty := ⟨_, hTS⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  set ts := sInf S with htsdef
  have hts0 : 0 ≤ ts := le_csInf hSne (fun t ht => ht.1.1)
  have htsT : ts ≤ P.T := csInf_le hSbdd hTS
  have hgt : ∀ s ∈ Ioc ts P.T, W s = V s := by
    intro s hs
    obtain ⟨t, htS, hts⟩ := exists_lt_of_csInf_lt hSne hs.1
    exact htS.2 s ⟨hts.le, hs.2⟩
  have htsS : ts ∈ S := by
    refine ⟨⟨hts0, htsT⟩, fun s hs => ?_⟩
    rcases eq_or_lt_of_le hs.1 with h | h
    · rcases eq_or_lt_of_le htsT with h' | h'
      · rw [← h, h']; exact hWT
      · have heq : EqOn W V (Icc ts P.T) :=
          (show EqOn W V (Ioc ts P.T) from hgt).of_subset_closure
            (hWc.mono (Icc_subset_Icc_left hts0)) (hVc.mono (Icc_subset_Icc_left hts0))
            Ioc_subset_Icc_self (by rw [closure_Ioc h'.ne])
        exact heq hs
    · exact hgt s ⟨h, hs.2⟩
  have hts_eq : ts = 0 := by
    by_contra hne
    have htspos : 0 < ts := lt_of_le_of_ne hts0 (Ne.symm hne)
    have hWts : W ts = V ts := htsS.2 ts ⟨le_rfl, htsT⟩
    have htsI : ts ∈ Icc 0 P.T := ⟨hts0, htsT⟩
    obtain ⟨δ, hδ, hδW⟩ := Metric.continuousWithinAt_iff.1 (hWc ts htsI) (r0 / 2) (by linarith)
    set t1 := ts - min (δ / 2) (ts / 2) with ht1def
    have hm1 : 0 < min (δ / 2) (ts / 2) := lt_min (by linarith) (by linarith)
    have hm2 := min_le_left (δ / 2) (ts / 2)
    have hm3 := min_le_right (δ / 2) (ts / 2)
    have ht1pos : 0 < t1 := by linarith
    have ht1ts : t1 < ts := by linarith
    have hsubI : Icc t1 ts ⊆ Icc 0 P.T := Icc_subset_Icc ht1pos.le htsT
    have hWbox : ∀ t ∈ Icc t1 ts, W t ∈ Box P r0 Rb := by
      intro t ht j
      have hd := hδW (hsubI ht) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
      have hdj : dist (W t j) (W ts j) < r0 / 2 := lt_of_le_of_lt (dist_le_pi_dist _ _ j) hd
      rw [hWts, Real.dist_eq, abs_lt] at hdj
      have := hVb ts htsI j
      constructor <;> linarith [hdj.1, hdj.2, this.1, this.2]
    have hVbox : ∀ t ∈ Icc 0 P.T, V t ∈ Box P r0 Rb := fun t ht j =>
      ⟨by linarith [(hVb t ht j).1], by linarith [(hVb t ht j).2]⟩
    have hWd : ∀ t ∈ Icc t1 ts,
        HasDerivWithinAt W (fun i => -hH P Lstar i (W t)) (Icc t1 ts) t := by
      intro t ht
      rw [hasDerivWithinAt_pi]
      intro i
      have hwi := hw i (idx_grid i)
      refine visc_to_classical (fun t => w t i) (fun t => hH P Lstar i (W t)) t1 ts ht1ts
        (hwi.1.mono hsubI) ?_ ?_ ?_ t ht
      · exact (hK i).continuousOn.comp (hWc.mono hsubI) (fun t ht => hWbox t ht)
      · intro φ hφ t0 ht0 hmax
        have ht0' : t0 ∈ Ioo 0 P.T := ⟨by linarith [ht0.1], by linarith [ht0.2]⟩
        have h := hwi.2.2.1 φ hφ t0 ht0' hmax
        rw [hHW t0 (Box_sub_cone hr0 (hWbox t0 (Ioo_subset_Icc_self ht0))) i, ← EReal.coe_add] at h
        exact_mod_cast h
      · intro φ hφ t0 ht0 hmin
        have ht0' : t0 ∈ Ioo 0 P.T := ⟨by linarith [ht0.1], by linarith [ht0.2]⟩
        have h := hwi.2.2.2 φ hφ t0 ht0' hmin
        rw [hHW t0 (Box_sub_cone hr0 (hWbox t0 (Ioo_subset_Icc_self ht0))) i, ← EReal.coe_add] at h
        exact_mod_cast h
    have hEq : EqOn W V (Icc t1 ts) := by
      apply ODE_solution_unique_of_mem_Icc_left (v := fun _ u => fun i => -hH P Lstar i u)
        (s := fun _ => Box P r0 Rb) (K := K)
      · intro t _
        apply LipschitzOnWith.of_dist_le_mul
        intro u hu u' hu'
        rw [dist_pi_le_iff (by positivity)]
        intro i
        rw [dist_neg_neg]
        exact (hK i).dist_le_mul u hu u' hu'
      · exact hWc.mono hsubI
      · intro t ht
        exact (hWd t (Ioc_subset_Icc_self ht)).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨ht.1, ht.2⟩)
      · intro t ht; exact hWbox t (Ioc_subset_Icc_self ht)
      · exact hVc.mono hsubI
      · intro t ht
        exact (hVd t (hsubI (Ioc_subset_Icc_self ht))).mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLE_of_mem ⟨by linarith [ht.1], le_trans ht.2 htsT⟩)
      · intro t ht; exact hVbox t (hsubI (Ioc_subset_Icc_self ht))
      · exact hWts
    have ht1S : t1 ∈ S := ⟨⟨ht1pos.le, by linarith⟩, fun s hs => by
      rcases le_or_gt s ts with h | h
      · exact hEq ⟨hs.1, h⟩
      · exact htsS.2 s ⟨h.le, hs.2⟩⟩
    have := csInf_le hSbdd ht1S
    linarith
  intro t ht i
  have := htsS.2 t (by rw [hts_eq]; exact ht)
  exact congrFun this i

end MMDPAux

open MMDPAux in
theorem solution (P : Params) (hP : Standing P) (Lstar : Inc P → ℤ → Vol) (hL : IsBestResponse P Lstar) : ∃ v : ℝ → ℤ → ℝ, IsViscositySolution P Lstar v ∧ ∀ w : ℝ → ℤ → ℝ, IsViscositySolution P Lstar w → ∀ t ∈ Set.Icc 0 P.T, ∀ q ∈ Grid P, w t q = v t q := by
  obtain ⟨r0, Rb, α, hr0, hr0', hRb, hα0, hα, hαb⟩ := exists_traj hP hL
  have hT : 0 < P.T := hP.1
  have hbox : ∀ t ∈ Icc 0 P.T, α t ∈ Box P r0 Rb := fun t ht j =>
    ⟨by linarith [(hαb t ht j).1], by linarith [(hαb t ht j).2]⟩
  have hαc : ContinuousOn α (Icc 0 P.T) := fun t ht => (hα t ht).continuousWithinAt
  have hmaps : MapsTo (fun t => P.T - t) (Icc 0 P.T) (Icc 0 P.T) :=
    fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩
  set V : ℝ → Idx P → ℝ := fun t => α (P.T - t) with hV
  have hVc : ContinuousOn V (Icc 0 P.T) := hαc.comp (continuousOn_const.sub continuousOn_id) hmaps
  have hVb : ∀ t ∈ Icc 0 P.T, ∀ j, -Rb ≤ V t j ∧ V t j ≤ -r0 := fun t ht j => hαb _ (hmaps ht) j
  have hVcone : ∀ t ∈ Icc 0 P.T, V t ∈ cone P := fun t ht => Box_sub_cone hr0 (hbox _ (hmaps ht))
  have hVd : ∀ t ∈ Icc 0 P.T,
      HasDerivWithinAt V (fun i => -hH P Lstar i (V t)) (Icc 0 P.T) t := by
    intro t ht
    have h1 := (hα (P.T - t) (hmaps ht)).scomp t
      ((hasDerivAt_id t).const_sub P.T).hasDerivWithinAt hmaps
    exact h1.congr_deriv (by funext i; simp [hV])
  have hVT : V P.T = fun _ => -1 := by simp [hV, hα0]
  refine ⟨fun t => ext (V t), ?_, ?_⟩
  · intro q hq
    set i : Idx P := ⟨q, grid_idx hq⟩ with hi
    have hvq : ∀ t, ext (V t) q = V t i := fun t => ext_idx _ hq
    have hderiv : ∀ t0 ∈ Ioo 0 P.T, ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ →
        HasDerivAt (fun t => ext (V t) q - φ t) (-hH P Lstar i (V t0) - deriv φ t0) t0 := by
      intro t0 ht0 φ hφ
      have hd := (hasDerivWithinAt_pi.1 (hVd t0 (Ioo_subset_Icc_self ht0)) i).hasDerivAt
        (Icc_mem_nhds ht0.1 ht0.2)
      have hφd : HasDerivAt φ (deriv φ t0) t0 := (hφ.differentiable one_ne_zero t0).hasDerivAt
      have := hd.sub hφd
      simp only [hvq]
      exact this
    have hHc : ∀ t0 ∈ Ioo 0 P.T, Hcal P Lstar q (ext (V t0)) = (hH P Lstar i (V t0) : EReal) :=
      fun t0 ht0 => Hcal_eq hP hL (hVcone t0 (Ioo_subset_Icc_self ht0)) i
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [hvq]; exact (continuous_apply i).comp_continuousOn hVc
    · show ext (V P.T) q = -1
      rw [hvq, hVT]
    · intro φ hφ t0 ht0 hmax
      have hz := hmax.hasDerivAt_eq_zero (hderiv t0 ht0 φ hφ)
      rw [hHc t0 ht0, ← EReal.coe_add]
      have : deriv φ t0 + hH P Lstar i (V t0) = 0 := by linarith
      rw [this]; simp
    · intro φ hφ t0 ht0 hmin
      have hz := hmin.hasDerivAt_eq_zero (hderiv t0 ht0 φ hφ)
      rw [hHc t0 ht0, ← EReal.coe_add]
      have : deriv φ t0 + hH P Lstar i (V t0) = 0 := by linarith
      rw [this]; simp
  · intro w hw t ht q hq
    have := uniq hP hL hr0 hr0' hRb V hVc hVd hVb hVT w hw t ht ⟨q, grid_idx hq⟩
    show w t q = ext (V t) q
    rw [ext_idx _ hq]
    exact this
