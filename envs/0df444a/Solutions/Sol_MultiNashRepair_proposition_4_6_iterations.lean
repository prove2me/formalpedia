-- Prove2me | solution 1 for MultiNashRepair.proposition_4_6_iterations
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:58:46.625808+00:00
-- url     : https://prove2.me/submissions/89816fe0-823c-4810-9383-bcfae3c6f426

import Mathlib
import Definitions.Def_NashAmplification_Filtering_Model
import Definitions.Def_MultiNashRepair_IDRH
import Theorems.Thm_MultiNashRepair_controls_5_7
import Theorems.Thm_MultiNashRepair_lemma_5_11
import Theorems.Thm_MultiNashRepair_lemma_5_1
import Theorems.Thm_MultiNashRepair_lemma_5_6
import Theorems.Thm_MultiNashRepair_lemma_5_12
import Theorems.Thm_MultiNashRepair_theorem_5_8
import Theorems.Thm_MultiNashRepair_proposition_4_5_of_one_lt_sigma

open NashAmplification.Filtering (Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair

theorem MNR46_weierstrass {ι : Type*} [DecidableEq ι] (S : Finset ι) (t : ι → ℝ)
    (h0 : ∀ k, 0 ≤ t k) (h1 : ∀ k, t k ≤ 1) : 1 - ∑ k ∈ S, t k ≤ ∏ k ∈ S, (1 - t k) := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have hS : 0 ≤ ∑ k ∈ S, t k := Finset.sum_nonneg (fun k _ => h0 k)
    have := mul_le_mul_of_nonneg_left ih (by linarith [h1 a] : (0:ℝ) ≤ 1 - t a)
    nlinarith only [this, mul_nonneg (h0 a) hS]

theorem MNR46_phihat (k : Knobs) (d ς H : ℝ) :
    k.Phihat d ς H = (ς - k.G0 + 2 * d) / H + (1 - k.au) * Real.log (H / k.f0)
      + k.au * Real.log (1 + k.Q * H) := by
  simp only [Knobs.Phihat, Knobs.Phiu, Knobs.Fu]; ring

set_option maxHeartbeats 16000000 in
theorem solution (σ : ℚ) (hσ1 : 1 < σ) (hσ2 : (σ : ℝ) < sigmaStar) (ctrl : Controls σ) :
    ∃ N0 : ℕ, ∀ (m : ℕ) (n : Fin m → ℕ) (u : Utility n), ctrl.m0 ≤ m → (∀ i, 0 < n i) →
      BoundedGame u → ∀ (k : ℕ) (s : State n), Reach ctrl u k s → k ≤ N0 := by
  -- constants
  have hdq : (0:ℚ) < ctrl.d := ctrl.d_pos
  have hd : (0:ℝ) < ctrl.d := by exact_mod_cast hdq
  have huq : ctrl.u = 1/2 * min (1/144) (ctrl.d/100) := rfl
  have hηq : ctrl.η = 1/2 * min (1/4) (ctrl.d/24) := rfl
  have hu0q : (0:ℚ) < ctrl.u := by
    rw [huq]; have := lt_min (by norm_num : (0:ℚ) < 1/144) (by positivity : (0:ℚ) < ctrl.d/100)
    linarith
  have hu1q : ctrl.u ≤ 1/288 := by
    rw [huq]; have := min_le_left (1/144 : ℚ) (ctrl.d/100); linarith
  have hudq : ctrl.u ≤ ctrl.d/200 := by
    rw [huq]; have := min_le_right (1/144 : ℚ) (ctrl.d/100); linarith
  have hη0q : (0:ℚ) < ctrl.η := by
    rw [hηq]; have := lt_min (by norm_num : (0:ℚ) < 1/4) (by positivity : (0:ℚ) < ctrl.d/24); linarith
  have hη1q : ctrl.η ≤ 1/8 := by rw [hηq]; have := min_le_left (1/4 : ℚ) (ctrl.d/24); linarith
  have hηdq : ctrl.η ≤ ctrl.d/48 := by rw [hηq]; have := min_le_right (1/4 : ℚ) (ctrl.d/24); linarith
  have hu0 : (0:ℝ) < ctrl.u := by exact_mod_cast hu0q
  have hu1 : (ctrl.u:ℝ) ≤ 1/288 := by
    have := (Rat.cast_le (K := ℝ)).mpr hu1q; push_cast at this; exact this
  have hud : (ctrl.u:ℝ) ≤ ctrl.d/200 := by exact_mod_cast hudq
  have hη0 : (0:ℝ) < ctrl.η := by exact_mod_cast hη0q
  have hη1 : (ctrl.η:ℝ) ≤ 1/8 := by
    have := (Rat.cast_le (K := ℝ)).mpr hη1q; push_cast at this; exact this
  have hηd : (ctrl.η:ℝ) ≤ ctrl.d/48 := by exact_mod_cast hηdq
  have hf1 : (7/12:ℝ) ≤ ctrl.f0 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_ge; push_cast at this; exact this
  have hf2 : (ctrl.f0:ℝ) ≤ 3/5 := by
    have := (Rat.cast_le (K := ℝ)).mpr ctrl.f0_le; push_cast at this; exact this
  have hF0 : (0:ℝ) < ctrl.f0 := by linarith
  have hσ1r : (1:ℝ) < σ := by exact_mod_cast hσ1
  have hσ2' : (σ:ℝ) < 2 := lt_trans hσ2 MultiNashRepair.theorem_5_8.2.2.1.2.1
  set k := ctrl.knobs with hk
  have hC := MultiNashRepair.controls_5_7 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  dsimp only at hC
  have hQ1 : 1 < k.Q := hC.1.2.2.1
  have hau0 : 0 < k.au := hC.1.2.2.2.2.1
  have hau1 : k.au < 1 := hC.1.2.2.2.2.2.1
  have hL0f : k.L0 < ctrl.f0 := hC.1.2.2.2.2.2.2.1
  have hQL0 : k.Q * k.L0 < k.c := hC.1.2.2.2.2.2.2.2
  have hc : k.c = 1 - ctrl.u + (ctrl.u:ℝ)^2/2 - (ctrl.u:ℝ)^3 := rfl
  have hcpos : 0 < k.c := by rw [hc]; nlinarith only [hu0, hu1]
  have hc1 : k.c < 1 := by rw [hc]; nlinarith only [hu0, hu1]
  have htpos : 0 < k.t := by show 0 < (ctrl.f0:ℝ) * ctrl.u; positivity
  have hL0pos : 0 < k.L0 := by
    show 0 < k.c * k.t / (1 - k.c); exact div_pos (mul_pos hcpos htpos) (by linarith)
  have h511' := MultiNashRepair.lemma_5_11 (ctrl.f0:ℝ) (ctrl.u:ℝ) hf1 hf2 hu0 (by linarith)
  dsimp only at h511'
  have hG0lo : 1/(ctrl.f0:ℝ) - 32 * ctrl.u ≤ k.G0 := by
    have h := h511'.2.2 0 le_rfl (hL0pos.le : (0:ℝ) ≤ k.L0)
    rw [h511'.1] at h
    have e : Kf (ctrl.f0) 0 = 1/(ctrl.f0:ℝ) := by
      unfold Kf; rw [div_eq_div_iff (by positivity) (by positivity)]; ring
    rw [e] at h
    have h2 : |k.G0 - 1/(ctrl.f0:ℝ)| ≤ 32 * ctrl.u := h
    linarith [(abs_le.mp h2).1]
  have hfinv := ctrl.f0_inv
  have hG0big : (σ:ℝ) + 2 * ctrl.d < k.G0 := by linarith
  -- numerical constants of the bound
  set δA : ℝ := 4 * ctrl.η * ctrl.d with hδA
  have hδApos : 0 < δA := by positivity
  set KA : ℝ := ((σ:ℝ) - 1) / δA + 1 with hKA
  set Φmin : ℝ := k.Phihat ctrl.d (-1) (k.c * (0 + k.t)) with hΦmin
  set κ : ℝ := min ((ctrl.η:ℝ) * ctrl.d / 2) (3 * (ctrl.d:ℝ) * (1 - k.c)) / k.L0 with hκ
  have hκ0 : 0 < κ := by
    apply div_pos _ hL0pos
    exact lt_min (by positivity) (by nlinarith only [hd, hc1])
  refine ⟨Nat.ceil (1 + KA + max 0 ((1 - Φmin) / κ)), ?_⟩
  intro m n u hm hn hu
  have hm0 : (ctrl.m0:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0:ℝ) < m := by
    have h1 := ctrl.m0_ge_d
    have : (0:ℝ) < 66 / (ctrl.d:ℝ) := by positivity
    linarith
  have hm1 : 1 ≤ m := by exact_mod_cast (show (0:ℕ) < m by exact_mod_cast hmpos)
  have hE1 : 120 * (ctrl.u:ℝ) / m ≤ 1 := by
    rw [div_le_one hmpos]
    have : (1:ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  -- the potential upper bound on nonterminal states
  have hΦmax : ∀ (ς H : ℝ), ς < σ → 0 < H → H ≤ k.L0 → k.Phihat ctrl.d ς H ≤ 1 := by
    intro ς H hς hH0 hHL
    rw [MNR46_phihat]
    have h1 : (ς - k.G0 + 2 * ctrl.d) / H ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hH0.le
    have h2 : Real.log (H / k.f0) ≤ 0 := by
      apply Real.log_nonpos (by positivity)
      rw [div_le_one (by show (0:ℝ) < (ctrl.f0:ℝ); exact hF0)]
      show H ≤ ctrl.f0; linarith
    have h3 : Real.log (1 + k.Q * H) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by nlinarith only [hQ1, hH0] : (0:ℝ) < 1 + k.Q * H)
      have : k.Q * H ≤ k.Q * k.L0 := mul_le_mul_of_nonneg_left hHL (by linarith)
      linarith
    have k1 := mul_nonpos_of_nonneg_of_nonpos (by linarith : (0:ℝ) ≤ 1 - k.au) h2
    have k2 := mul_le_mul_of_nonneg_left h3 hau0.le
    linarith
  -- the invariant along runs
  have hinv : ∀ (j : ℕ) (s : State n), Reach ctrl u j s →
      (s.H = 0 ∧ 1 + δA * j ≤ scaled u s.x) ∨
      (0 < s.H ∧ Φmin + κ * ((j:ℝ) - KA) ≤ k.Phihat ctrl.d (scaled u s.x) s.H) := by
    intro j s hs
    induction hs with
    | init h0 =>
      left; obtain ⟨-, -, hsc, -, hH, -⟩ := h0
      exact ⟨hH, by simp; exact hsc⟩
    | @step j s s' hr hst ih =>
      have h512 := MultiNashRepair.lemma_5_12 ctrl hm hn u hu hr
      dsimp only at h512
      obtain ⟨⟨hx, -, hg, hI1, hH⟩, ⟨hh0, hHnn, hHL, hv⟩, hI3, hI4, hmu, -, hpos⟩ := h512
      have hst' := hst
      obtain ⟨hterm, hd' | hr'⟩ := hst
      · -- descent
        have hμ := hmu hterm
        obtain ⟨hpass, z, ⟨hzf, hzopt⟩, -, rfl⟩ := hd'
        have hobj : lpObj u s.x ctrl.η z ≤ Reg u s.x - ctrl.η * ctrl.mu (scaled u s.x) s.H / m := by
          rw [hzopt]; exact hpass
        have h51 := (MultiNashRepair.lemma_5_1 hm1 hn u hu s.x hx ctrl.η (ctrl.mu (scaled u s.x) s.H)
          hη0 (by linarith) (by linarith)).1 z hzf hobj
        dsimp only at h51
        obtain ⟨ha1, ha2, -⟩ := h51
        have hςσ : scaled u s.x < (σ:ℝ) := lt_of_not_ge hterm
        set ς := scaled u s.x with hςdef
        set μ := ctrl.mu ς s.H with hμdef
        set Z := ∑ j, ∑ b, z j b with hZ
        set P := descentFactor ctrl.η z with hP
        have hZ0 : 0 ≤ Z := Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun b _ => hzf.1 j b))
        have hZ1 : Z ≤ 1 := hzf.2
        have hcf : ∀ j, 0 ≤ (ctrl.η:ℝ) * ∑ b, z j b ∧ (ctrl.η:ℝ) * ∑ b, z j b ≤ 1 := fun j => by
          have hZj : ∑ b, z j b ≤ 1 := by
            have h1 : ∑ b, z j b ≤ ∑ k, ∑ b, z k b :=
              Finset.single_le_sum (f := fun k => ∑ b, z k b)
                (fun k _ => Finset.sum_nonneg (fun b _ => hzf.1 k b)) (mem_univ j)
            linarith [hzf.2]
          have hZj0 : 0 ≤ ∑ b, z j b := Finset.sum_nonneg (fun b _ => hzf.1 j b)
          exact ⟨mul_nonneg hη0.le hZj0, by nlinarith only [hZj, hZj0, hη0, hη1]⟩
        have hPlo : 1 - ctrl.η * Z ≤ P := by
          have := MNR46_weierstrass univ (fun j => (ctrl.η:ℝ) * ∑ b, z j b) (fun j => (hcf j).1)
            (fun j => (hcf j).2)
          rw [hZ, Finset.mul_sum]; exact this
        have hPhi : P ≤ 1 := Finset.prod_le_one (fun j _ => by linarith [(hcf j).2])
          (fun j _ => by linarith [(hcf j).1])
        rcases ih with ⟨hH0, hsc⟩ | ⟨hHp, hΦ⟩
        · left
          refine ⟨by show P * s.H = 0; rw [hH0, mul_zero], ?_⟩
          show 1 + δA * ((j + 1 : ℕ) : ℝ) ≤ scaled u (descentProfile s.x ctrl.η z)
          have hstep : ς + δA ≤ ς + ctrl.η * μ - ctrl.η ^ 2 * (ς + μ) := by
            have hς0 : 0 ≤ ς := by linarith [mul_nonneg hδApos.le (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
            have k1 : ctrl.η * ς ≤ ctrl.d / 24 := by nlinarith only [hηd, hςσ, hσ2', hς0, hη0]
            have k2 : ctrl.η * μ ≥ ctrl.η * (5 * ctrl.d) := mul_le_mul_of_nonneg_left hμ.le hη0.le
            have k3 : ctrl.η ^ 2 * μ ≤ ctrl.η * (μ / 8) := by
              have : ctrl.η ^ 2 * μ = ctrl.η * (ctrl.η * μ) := by ring
              rw [this]; apply mul_le_mul_of_nonneg_left _ hη0.le
              nlinarith only [hη1, hμ, hd]
            rw [hδA]; nlinarith only [k1, k2, k3, hη0, hd, hμ]
          push_cast; nlinarith only [ha1, ha2, hstep, hsc]
        · right
          have h45 := MultiNashRepair.proposition_4_5_of_one_lt_sigma ctrl hσ1 hm ς s.H hHp hHL hςσ
          dsimp only at h45
          have hprog := h45.1 Z P (scaled u (descentProfile s.x ctrl.η z)) (P * s.H) hZ0 hZ1 hPlo hPhi
            ha1 rfl
          refine ⟨by show 0 < P * s.H; exact mul_pos (by
            exact Finset.prod_pos (fun j _ => by
              have := (hcf j).2
              have hlt : (ctrl.η:ℝ) * ∑ b, z j b < 1 := by
                have hZj : ∑ b, z j b ≤ 1 := by
                  have h1 : ∑ b, z j b ≤ ∑ k, ∑ b, z k b :=
                    Finset.single_le_sum (f := fun k => ∑ b, z k b)
                      (fun k _ => Finset.sum_nonneg (fun b _ => hzf.1 k b)) (mem_univ j)
                  linarith [hzf.2]
                have hZj0 : 0 ≤ ∑ b, z j b := Finset.sum_nonneg (fun b _ => hzf.1 j b)
                nlinarith only [hZj, hZj0, hη0, hη1]
              linarith)) hHp, ?_⟩
          show Φmin + κ * (((j+1 : ℕ) : ℝ) - KA) ≤ k.Phihat ctrl.d (scaled u (descentProfile s.x ctrl.η z)) (P * s.H)
          have hgain : κ ≤ k.Phihat ctrl.d (scaled u (descentProfile s.x ctrl.η z)) (P * s.H)
              - k.Phihat ctrl.d ς s.H := by
            rw [hκ, div_le_iff₀ hL0pos]
            have h1 : min ((ctrl.η:ℝ) * ctrl.d / 2) (3 * (ctrl.d:ℝ) * (1 - k.c)) ≤ (ctrl.η:ℝ) * ctrl.d / 2 := min_le_left _ _
            have hX : 0 ≤ k.Phihat ctrl.d (scaled u (descentProfile s.x ctrl.η z)) (P * s.H)
                - k.Phihat ctrl.d ς s.H := by
              by_contra hneg; push Not at hneg
              have := mul_neg_of_pos_of_neg hHp hneg
              linarith [mul_pos hη0 hd]
            nlinarith only [hprog, h1, hX, hHL, mul_le_mul_of_nonneg_right hHL hX]
          push_cast; nlinarith only [hgain, hΦ]
      · -- repair
        have hμ := hmu hterm
        obtain ⟨hfail, w, α, arev, acor, hw, -, hrev, hfwd, rfl⟩ := hr'
        have h56 := MultiNashRepair.lemma_5_6 ctrl hm hn u hu s hx hterm
          (fun g hgm => ⟨(hg g hgm).1, (hg g hgm).2.2.1, (hg g hgm).2.2.2⟩) hI1 hH ⟨hh0, hHL, hv⟩ hI3 hI4
          hfail w α arev acor hw hrev hfwd
        dsimp only at h56
        obtain ⟨hE0, hEu, -, -, hsc'⟩ := h56
        have hςσ : scaled u s.x < (σ:ℝ) := lt_of_not_ge hterm
        right
        refine ⟨by show 0 < k.c * (s.H + k.t); exact mul_pos hcpos (by linarith), ?_⟩
        rcases ih with ⟨hH0, hsc⟩ | ⟨hHp, hΦ⟩
        · -- first repair: the potential starts at least at Φmin
          have hςnn : 0 ≤ scaled u s.x := by linarith [mul_nonneg hδApos.le (Nat.cast_nonneg j : (0:ℝ) ≤ j)]
          have hD0 : 0 ≤ k.Dsh s.H := by
            show 0 ≤ k.beta * (k.G0 + k.Q * s.H)
            rw [hH0, mul_zero, add_zero]
            have hβ : 0 < k.beta := by
              show 0 < k.c * k.t * (1 + k.u0)
              have : 0 < 1 + k.u0 := by
                show 0 < 1 + ((ctrl.u:ℝ) - (ctrl.u:ℝ)^2); nlinarith only [hu0, hu1]
              positivity
            exact mul_nonneg hβ.le (by linarith)
          have hς' : -1 ≤ scaled u (repairState k u s w arev acor).x := by
            have : 0 ≤ k.c * scaled u s.x := mul_nonneg hcpos.le hςnn
            linarith
          have hmono : Φmin ≤ k.Phihat ctrl.d (scaled u (repairState k u s w arev acor).x)
              (repairState k u s w arev acor).H := by
            show k.Phihat ctrl.d (-1) (k.c * (0 + k.t)) ≤ k.Phihat ctrl.d _ (k.c * (s.H + k.t))
            rw [hH0, MNR46_phihat, MNR46_phihat]
            have hpos' : 0 < k.c * (0 + k.t) := by positivity
            have := div_le_div_of_nonneg_right (by linarith : (-1:ℝ) - k.G0 + 2 * ctrl.d
              ≤ scaled u (repairState k u s w arev acor).x - k.G0 + 2 * ctrl.d) hpos'.le
            linarith
          have hjK : ((j+1 : ℕ) : ℝ) ≤ KA := by
            have h1 : δA * j < (σ:ℝ) - 1 := by linarith
            have h2 : (j:ℝ) ≤ ((σ:ℝ) - 1) / δA := by rw [le_div_iff₀ hδApos]; nlinarith only [h1]
            rw [hKA]; push_cast; linarith
          have : κ * (((j+1 : ℕ) : ℝ) - KA) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hκ0.le (by linarith)
          linarith
        · have h45 := MultiNashRepair.proposition_4_5_of_one_lt_sigma ctrl hσ1 hm (scaled u s.x) s.H
            hHp hHL hςσ
          dsimp only at h45
          have hprog := h45.2.1 (rEtot k u s w arev) (scaled u (repairState k u s w arev acor).x)
            (k.c * (s.H + k.t)) hE0 hEu hsc' rfl
          have hgain : κ ≤ k.Phihat ctrl.d (scaled u (repairState k u s w arev acor).x)
              (repairState k u s w arev acor).H - k.Phihat ctrl.d (scaled u s.x) s.H := by
            show κ ≤ k.Phihat ctrl.d _ (k.c * (s.H + k.t)) - _
            rw [hκ, div_le_iff₀ hL0pos]
            have h1 : min ((ctrl.η:ℝ) * ctrl.d / 2) (3 * (ctrl.d:ℝ) * (1 - k.c)) ≤ 3 * (ctrl.d:ℝ) * (1 - k.c) := min_le_right _ _
            have hX : 0 ≤ k.Phihat ctrl.d (scaled u (repairState k u s w arev acor).x) (k.c * (s.H + k.t))
                - k.Phihat ctrl.d (scaled u s.x) s.H := by
              by_contra hneg; push Not at hneg
              have := mul_neg_of_pos_of_neg hHp hneg
              have : 0 < 3 * ctrl.d * (1 - k.c) := by nlinarith only [hd, hc1]
              linarith
            nlinarith only [hprog, h1, hX, hHL, mul_le_mul_of_nonneg_right hHL hX]
          push_cast; nlinarith only [hgain, hΦ]
  -- the bound
  intro j s hs
  cases hs with
  | init _ => exact Nat.zero_le _
  | @step j0 s0 _ hr hst =>
    have h512 := MultiNashRepair.lemma_5_12 ctrl hm hn u hu hr
    dsimp only at h512
    obtain ⟨-, ⟨-, -, hHL, -⟩, -⟩ := h512
    have hςσ : scaled u s0.x < (σ:ℝ) := lt_of_not_ge hst.1
    have hj : ((j0 + 1 : ℕ) : ℝ) ≤ 1 + KA + max 0 ((1 - Φmin) / κ) := by
      rcases hinv j0 s0 hr with ⟨-, hsc⟩ | ⟨hHp, hΦ⟩
      · have : δA * j0 < (σ:ℝ) - 1 := by linarith
        have h2 : (j0:ℝ) ≤ ((σ:ℝ) - 1) / δA := by rw [le_div_iff₀ hδApos]; nlinarith only [this]
        push_cast
        have := le_max_left 0 ((1 - Φmin) / κ)
        rw [hKA]; linarith
      · have hub := hΦmax (scaled u s0.x) s0.H hςσ hHp hHL
        have h2 : (j0:ℝ) - KA ≤ (1 - Φmin) / κ := by rw [le_div_iff₀ hκ0]; nlinarith only [hΦ, hub]
        have := le_max_right 0 ((1 - Φmin) / κ)
        push_cast; linarith
    have := Nat.le_ceil (1 + KA + max 0 ((1 - Φmin) / κ))
    exact_mod_cast le_trans hj this
