-- Prove2me | solution 1 for MultiNashRepair.theorem_1_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T01:49:29.726803+00:00
-- url     : https://prove2.me/submissions/776545db-8e8b-4a02-908a-164fc3da8c37
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_NashAmplification_Filtering_Encoding
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_MultiNashRepair_ScalarCertificate
import Theorems.Thm_MultiNashRepair_proposition_4_6
import Theorems.Thm_MultiNashRepair_lemma_5_12
import Theorems.Thm_MultiNashRepair_theorem_5_8
import Theorems.Thm_MultiNashRepair_lemma_5_9

open OnlineCRS.Combine (Sym)
open NashAmplification.Filtering (Table RawProfile encGame encProfile Mixed Utility Tuple BoundedGame)
open Finset
open MultiNashRepair

theorem MNRM_panti (a b : ℝ) (ha : 1 ≤ a) (hab : a < b) (hb : b ≤ 2) : sigmaPoly b < sigmaPoly a := by
  have key : sigmaPoly a - sigmaPoly b = (b - a) * (19*(a+b) - 27 - (a^2+a*b+b^2)) := by
    unfold sigmaPoly; ring
  have ha2 : a ≤ 2 := by linarith
  have hb1 : 1 ≤ b := by linarith
  have : 0 < 19*(a+b) - 27 - (a^2+a*b+b^2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr ha2),
      mul_nonneg (sub_nonneg.mpr hb1) (sub_nonneg.mpr hb),
      mul_nonneg (sub_nonneg.mpr ha2) (by linarith : (0:ℝ) ≤ b)]
  nlinarith [mul_pos (sub_pos.mpr hab) this]

theorem MNRM_gap (σ : ℝ) (h1 : 1 < σ) (h2 : σ < sigmaStar) :
    0 < sigmaPoly σ ∧ sigmaPoly σ ≤ 37 * (sigmaStar - σ) := by
  obtain ⟨-, -, ⟨-, hs2, hP0, -⟩, -⟩ := MultiNashRepair.theorem_5_8
  constructor
  · have := MNRM_panti σ sigmaStar h1.le h2 hs2.le; linarith
  · have key : sigmaPoly σ - sigmaPoly sigmaStar
        = (sigmaStar - σ) * (19*(σ+sigmaStar) - 27 - (σ^2+σ*sigmaStar+sigmaStar^2)) := by
      unfold sigmaPoly; ring
    rw [hP0] at key
    have hb : 19*(σ+sigmaStar) - 27 - (σ^2+σ*sigmaStar+sigmaStar^2) ≤ 37 := by
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ σ - 1) (by linarith : (0:ℝ) ≤ sigmaStar - 1)]
    have := mul_le_mul_of_nonneg_left hb (by linarith : (0:ℝ) ≤ sigmaStar - σ)
    linarith

theorem MNRM_f0 (τ : ℝ) (hτ : τ < sigmaStar) : ∃ f0 : ℚ, 7/12 ≤ f0 ∧ f0 ≤ 3/5 ∧ τ < U f0 := by
  obtain ⟨⟨hf1, hf2, -⟩, -, -, -, -, ⟨hG, huniq, -⟩⟩ := MultiNashRepair.theorem_5_8
  obtain ⟨f, hf, hUf⟩ := hG.1
  have hfeq : f = fStar := huniq f hf hUf
  rw [hfeq] at hUf
  have hs3 : 1 / Real.sqrt 3 < 7 / 12 := by
    rw [div_lt_iff₀ (by positivity)]
    have : (7/12 * Real.sqrt 3)^2 = 49/48 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
    nlinarith [Real.sqrt_nonneg 3]
  have hfs0 : fStar ≠ 0 := by linarith
  set g : ℝ → ℝ := fun f => 5 - 4 * f - 1 / f + 2 * (1 - f) * Real.sqrt (4 - 2 / f) with hg
  have hgc : ContinuousAt g fStar := by
    simp only [hg]; fun_prop (disch := assumption)
  have hgs : g fStar = sigmaStar := by
    rw [← hUf, (MultiNashRepair.lemma_5_9).2.2.1 fStar (by linarith) (by linarith)]
  have hev1 : ∀ᶠ f in nhds fStar, τ < g f :=
    hgc.eventually (lt_mem_nhds (by rw [hgs]; exact hτ))
  have hev2 : ∀ᶠ f in nhds fStar, f ∈ Set.Ioo (7/12 : ℝ) (3/5) := Ioo_mem_nhds hf1 hf2
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show fStar - ε / 2 < fStar + ε / 2 by linarith)
  have hd : dist (q : ℝ) fStar < ε := by
    rw [Real.dist_eq, abs_lt]; constructor <;> linarith
  obtain ⟨hτq, hq⟩ := hball hd
  refine ⟨q, ?_, ?_, ?_⟩
  · have := hq.1.le
    have h' : ((7/12 : ℚ) : ℝ) ≤ (q : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  · have := hq.2.le
    have h' : (q : ℝ) ≤ ((3/5 : ℚ) : ℝ) := by push_cast; linarith
    exact_mod_cast h'
  · rw [(MultiNashRepair.lemma_5_9).2.2.1 q (by linarith [hq.1]) (by linarith [hq.2])]
    exact hτq

def MNRM_m0 (b : ℕ) : ℕ :=
  4000 * ((144 + 59200 * ((b+1)*(b+1)*(b+1))) * (144 + 59200 * ((b+1)*(b+1)*(b+1))))
    + 236800 * ((b+1)*(b+1)*(b+1))

theorem MNRM_m0_prim : Primrec MNRM_m0 := by
  have h1 : Primrec (fun b : ℕ => b + 1) := Primrec.succ
  have hB : Primrec (fun b : ℕ => (b+1)*(b+1)*(b+1)) :=
    Primrec.nat_mul.comp (Primrec.nat_mul.comp h1 h1) h1
  have hC : Primrec (fun b : ℕ => 144 + 59200 * ((b+1)*(b+1)*(b+1))) :=
    Primrec.nat_add.comp (Primrec.const 144) (Primrec.nat_mul.comp (Primrec.const 59200) hB)
  have hD : Primrec (fun b : ℕ => 4000 * ((144 + 59200 * ((b+1)*(b+1)*(b+1))) *
      (144 + 59200 * ((b+1)*(b+1)*(b+1))))) :=
    Primrec.nat_mul.comp (Primrec.const 4000) (Primrec.nat_mul.comp hC hC)
  exact Primrec.nat_add.comp hD (Primrec.nat_mul.comp (Primrec.const 236800) hB)

theorem MNRM_controls (a b : ℕ) (h1 : 1 < ((a + 1 : ℚ) / (b + 1)))
    (h2 : (((a + 1 : ℚ) / (b + 1) : ℚ) : ℝ) < sigmaStar) :
    ∃ ctrl : Controls ((a + 1 : ℚ) / (b + 1)), ctrl.m0 = MNRM_m0 b := by
  set σ : ℚ := (a + 1 : ℚ) / (b + 1) with hσ
  have h1r : (1:ℝ) < (σ:ℝ) := by exact_mod_cast h1
  obtain ⟨hp0, hgap⟩ := MNRM_gap (σ:ℝ) h1r h2
  set dq : ℚ := (σ ^ 3 - 19 * σ ^ 2 + 27 * σ + 1) / 592 with hdq
  have hdr : (dq : ℝ) = sigmaPoly (σ:ℝ) / 592 := by
    rw [hdq]; unfold sigmaPoly; push_cast; ring
  have hd0 : (0:ℝ) < dq := by rw [hdr]; positivity
  have hdq0 : (0:ℚ) < dq := by exact_mod_cast hd0
  -- the integer numerator
  set B : ℝ := ((b:ℝ) + 1) ^ 3 with hB
  have hBpos : 0 < B := by positivity
  have hpB : 1 ≤ sigmaPoly (σ:ℝ) * B := by
    have e : sigmaPoly (σ:ℝ) * B = (((a+1)^3 - 19*(a+1)^2*(b+1) + 27*(a+1)*(b+1)^2 + (b+1)^3 : ℤ) : ℝ) := by
      rw [hB, hσ]; unfold sigmaPoly; push_cast; field_simp
    rw [e]
    have hpos : (0:ℝ) < (((a+1)^3 - 19*(a+1)^2*(b+1) + 27*(a+1)*(b+1)^2 + (b+1)^3 : ℤ) : ℝ) := by
      rw [← e]; positivity
    have : (0:ℤ) < (a+1)^3 - 19*(a+1)^2*(b+1) + 27*(a+1)*(b+1)^2 + (b+1)^3 := by exact_mod_cast hpos
    have : (1:ℤ) ≤ (a+1)^3 - 19*(a+1)^2*(b+1) + 27*(a+1)*(b+1)^2 + (b+1)^3 := this
    exact_mod_cast this
  have hinvd : 1 / (dq:ℝ) ≤ 592 * B := by
    rw [hdr, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith only [hpB, hBpos]
  -- σ + 8d < σ⋆ and σ + 7d < σ⋆
  have h8 : (σ:ℝ) + 8 * dq < sigmaStar := by rw [hdr]; nlinarith only [hgap, hp0, h2]
  have h7 : (σ:ℝ) + 7 * dq < sigmaStar := by linarith
  obtain ⟨f0, hf1, hf2, hfU⟩ := MNRM_f0 ((σ:ℝ) + 7 * dq) h7
  have hσ53 : sigmaStar < 5/3 := by
    obtain ⟨-, -, ⟨hs1, hs2, hP0, -⟩, -⟩ := MultiNashRepair.theorem_5_8
    by_contra hc; push Not at hc
    rcases eq_or_lt_of_le hc with h | h
    · have : sigmaPoly (5/3) = 0 := by rw [h]; exact hP0
      unfold sigmaPoly at this; norm_num at this
    · have := MNRM_panti (5/3) sigmaStar (by norm_num) h hs2.le
      rw [hP0] at this; unfold sigmaPoly at this; norm_num at this
  have hf0r : (f0:ℝ) ≤ 3/5 := by
    have : (f0 : ℝ) ≤ ((3/5 : ℚ) : ℝ) := by exact_mod_cast hf2
    push_cast at this; exact this
  have hf0p : (0:ℝ) < f0 := by
    have : ((7/12 : ℚ) : ℝ) ≤ (f0 : ℝ) := by exact_mod_cast hf1
    push_cast at this; linarith
  have hinvf : (σ:ℝ) + 7 * dq < 1 / (f0:ℝ) := by
    have : (5:ℝ)/3 ≤ 1 / (f0:ℝ) := by rw [le_div_iff₀ hf0p]; linarith
    linarith
  -- m0 bounds
  have hM0 : ((MNRM_m0 b : ℕ) : ℝ) = 4000 * ((144 + 59200 * B) * (144 + 59200 * B)) + 236800 * B := by
    unfold MNRM_m0; push_cast; rw [hB]; ring
  have hge_d : 400 / (dq:ℝ) ≤ MNRM_m0 b := by
    rw [hM0]
    have : 400 / (dq:ℝ) = 400 * (1 / (dq:ℝ)) := by ring
    rw [this]; nlinarith only [hinvd, hBpos]
  have hge_d66 : 66 / (dq:ℝ) ≤ MNRM_m0 b := by
    have : 66 / (dq:ℝ) ≤ 400 / (dq:ℝ) := div_le_div_of_nonneg_right (by norm_num) hd0.le
    linarith
  have hge_u : 1000 / (((uOf dq : ℚ) : ℝ))^2 ≤ MNRM_m0 b := by
    rw [hM0]
    have hu : ((uOf dq : ℚ) : ℝ) = 1/2 * min (1/144) ((dq:ℝ)/100) := by
      unfold uOf; push_cast; rfl
    rw [hu]
    rcases le_total (1/144 : ℝ) ((dq:ℝ)/100) with h | h
    · rw [min_eq_left h]
      norm_num
      nlinarith only [hBpos, mul_pos hBpos hBpos]
    · rw [min_eq_right h]
      have e : 1000 / (1/2 * ((dq:ℝ)/100))^2 = 40000000 * (1 / (dq:ℝ))^2 := by
        field_simp; ring
      rw [e]
      have k1 : (1 / (dq:ℝ))^2 ≤ (592 * B)^2 := by
        have : 0 ≤ 1 / (dq:ℝ) := by positivity
        exact pow_le_pow_left₀ this hinvd 2
      nlinarith only [k1, hBpos, mul_pos hBpos hBpos]
  exact ⟨⟨dq, hdq0, by exact_mod_cast h8, f0, hf1, hf2, by exact_mod_cast hfU,
    by exact_mod_cast hinvf, MNRM_m0 b, hge_d66, hge_u, hge_d⟩, rfl⟩

theorem MNRM_pp_update {m : ℕ} {n : Fin m → ℕ} (y : Mixed n) (j : Fin m)
    (w : Fin (n j) → ℝ) (s : Tuple n) :
    AGT.profileProb (Function.update y j w) s = w (s j) * ∏ k ∈ univ.erase j, y k (s k) := by
  unfold AGT.profileProb
  rw [← Finset.mul_prod_erase univ _ (mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (ne_of_mem_erase hk)]

theorem MNRM_ep_lin {m : ℕ} {n : Fin m → ℕ} (u : Utility n) (y : Mixed n) (j : Fin m)
    (z : Fin (n j) → ℝ) (i : Fin m) :
    AGT.expectedPayoff u (Function.update y j z) i
      = ∑ b, z b * AGT.expectedPayoff u (Function.update y j (ePure b)) i := by
  unfold AGT.expectedPayoff
  simp only [MNRM_pp_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  have : z (s j) = ∑ b, z b * (ePure b) (s j) := by
    simp [ePure, DGPNash.WellSupported.pureStrategy]
  rw [this, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _; ring

theorem MNRM_eps {m : ℕ} {n : Fin m → ℕ} (hm1 : 1 ≤ m) (u : Utility n) (x : Mixed n)
    (hx : AGT.IsMixedProfile x) (σ : ℝ) (hT : σ ≤ scaled u x) :
    DGPNash.WellSupported.IsEpsApproxNash u x (1 - σ / m) := by
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm1
  refine ⟨hx, fun p y hy => ?_⟩
  have hReg : Reg u x ≤ 1 - σ / m := by
    have : scaled u x = (m:ℝ) * (1 - Reg u x) := rfl
    rw [this] at hT
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ hmpos]; linarith
  have hg : ∀ a, AGT.expectedPayoff u (Function.update x p (ePure a)) p ≤ AGT.expectedPayoff u x p + Reg u x := by
    intro a
    have h1 : gain u x p a ≤ regret u x p := le_ciSup (f := fun a => gain u x p a) (Set.finite_range _).bddAbove a
    have h2 : regret u x p ≤ Reg u x := le_ciSup (f := fun i => regret u x i) (Set.finite_range _).bddAbove p
    have : gain u x p a = AGT.expectedPayoff u (Function.update x p (ePure a)) p - AGT.expectedPayoff u x p := rfl
    linarith
  rw [MNRM_ep_lin u x p y p]
  have : ∑ b, y b * AGT.expectedPayoff u (Function.update x p (ePure b)) p
      ≤ ∑ b, y b * (AGT.expectedPayoff u x p + Reg u x) :=
    Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hg b) (hy.1 b))
  rw [← Finset.sum_mul, hy.2, one_mul] at this
  linarith

theorem MNRM_counts_pos {m : ℕ} (G : Table m) : ∀ i, 0 < G.counts i := by
  intro i
  unfold Table.counts
  have hi : i.val < G.sizes.length := by rw [G.sizes_length]; exact i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  exact G.sizes_pos _ (List.getElem_mem hi)

theorem MNRM_bounded {m : ℕ} (G : Table m) : BoundedGame G.utility := by
  intro r a
  unfold Table.utility
  have hval : ∀ q : NashAmplification.Filtering.RawRat, q.num ≤ q.den → q.value ∈ Set.Icc (0:ℝ) 1 := by
    intro q hq
    unfold NashAmplification.Filtering.RawRat.value
    have hd : (0:ℝ) < q.den := by exact_mod_cast q.den_pos
    constructor
    · positivity
    · rw [div_le_one hd]; exact_mod_cast hq
  rw [List.getD_eq_getElem?_getD]
  rcases h : G.entries[r.val * G.sizes.prod + NashAmplification.Filtering.tupleRank a]? with _ | q
  · simp only [Option.getD_none]
    exact hval _ (by simp [NashAmplification.Filtering.zeroRat])
  · simp only [Option.getD_some]
    exact hval q (G.bounded q (List.mem_of_getElem? h))

theorem solution :
    ∃ m0 : ℕ → ℕ → ℕ, Computable₂ m0 ∧
      ∀ a b : ℕ, let σ : ℚ := (a + 1) / (b + 1)
        1 < σ → (σ : ℝ) < sigmaStar →
        ∃ (M : Turing.TM2ComputableAux Sym Sym) (c : ℕ),
          ∀ m : ℕ, m0 a b ≤ m → ∀ G : Table m,
            ∃ x : RawProfile m, x.sizes = G.sizes ∧
              CFLOutliers.OutputsWithin M (encGame G) (encProfile x) (c * ((encGame G).length + 2) ^ c) ∧
              DGPNash.WellSupported.IsEpsApproxNash G.utility (x.on G.counts)
                (1 - (σ : ℝ) / m) := by
  refine ⟨fun _ b => MNRM_m0 b, (MNRM_m0_prim.comp Primrec.snd).to_comp, ?_⟩
  intro a b σ h1 h2
  obtain ⟨ctrl, hctrl⟩ := MNRM_controls a b h1 h2
  obtain ⟨M, c, hM⟩ := (MultiNashRepair.proposition_4_6 σ h1 h2 ctrl).2
  refine ⟨M, c, fun m hm G => ?_⟩
  have hm1 : 1 ≤ m := by
    have : 1 ≤ MNRM_m0 b := Nat.succ_le_of_lt (by unfold MNRM_m0; positivity)
    exact le_trans this hm
  obtain ⟨x, hxs, hout, hID⟩ := hM m hm1 G
  refine ⟨x, hxs, hout, ?_⟩
  rcases hID with ⟨hlt, -⟩ | ⟨hge, k, s, hreach, hterm, hsx⟩
  · exfalso; rw [hctrl] at hlt; exact absurd hm (not_le.mpr hlt)
  · have h512 := MultiNashRepair.lemma_5_12 ctrl hge (MNRM_counts_pos G) G.utility (MNRM_bounded G) hreach
    dsimp only at h512
    have hmix : AGT.IsMixedProfile s.x := h512.1.1
    rw [← hsx]
    exact MNRM_eps hm1 G.utility s.x hmix (σ:ℝ) hterm
