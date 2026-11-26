-- Prove2me | solution 1 for GeodesicSampledCurrent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:18.278797+00:00
-- url     : https://prove2.me/submissions/a0d94174-b2a7-48fb-95f1-0e9f860f3f1b

import Definitions.Def_Tablet_curveSampling
import Definitions.Def_Tablet_curveCurrent
import Definitions.Def_Tablet_CurrentChordEstimate
import Definitions.Def_Tablet_CurrentConcatAdditive
import Definitions.Def_Tablet_CurrentResolutionAdditive
import Definitions.Def_Tablet_CurveLipschitz
import Definitions.Def_Tablet_RestrictCurrentFormula
import Definitions.Def_Tablet_curveRestrict
import Definitions.Def_Tablet_GeodesicSampledCurrent
import Theorems.Thm_CurrentChordEstimate
import Theorems.Thm_CurrentConcatAdditive
import Theorems.Thm_CurrentResolutionAdditive
import Theorems.Thm_CurveLipschitz
import Theorems.Thm_RestrictCurrentFormula


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] (GP : GeodesicPairing E) (γ : Curve E)
    (δ : ℝ) (hδ0 : 0 < δ) (hδlen : δ < γ.len) (ω : Form1 E) :
    (curveSampling GP γ δ hδ0 hδlen).len ≤ γ.len ∧
      |curveCurrent (curveSampling GP γ δ hδ0 hδlen) ω - curveCurrent γ ω|
        ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ * γ.len := by
-- BODY
  -- ## Reconstruct the definition of `curveSampling`.
  have concat_end : ∀ (a b : Curve E) (h : a.toFun a.len = b.toFun 0),
      (curveConcat a b h).toFun (curveConcat a b h).len = b.toFun b.len := by
    intro a b h
    show (if a.len + b.len ≤ a.len then a.toFun (a.len + b.len)
          else b.toFun (a.len + b.len - a.len)) = b.toFun b.len
    rcases eq_or_lt_of_le b.len_nonneg with hb0 | hbpos
    · have hb0' : b.len = 0 := hb0.symm
      rw [if_pos (by linarith)]
      simpa [hb0'] using h
    · rw [if_neg (by linarith)]
      congr 1
      ring
  let s : ℕ → ℝ := fun j => min ((j : ℝ) * δ) γ.len
  let aux : (n : ℕ) → {c : Curve E // c.toFun c.len = γ.toFun (s (n + 1))} := fun n =>
    Nat.rec
      (motive := fun n => {c : Curve E // c.toFun c.len = γ.toFun (s (n + 1))})
      ⟨GP.G (γ.toFun (s 0)) (γ.toFun (s 1)), GP.end_eq _ _⟩
      (fun n ih =>
        ⟨curveConcat ih.1 (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2))))
            (by rw [ih.2]; exact (GP.start_eq _ _).symm),
          by rw [concat_end]; exact GP.end_eq _ _⟩)
      n
  have hsamp : curveSampling GP γ δ hδ0 hδlen = (aux (⌈γ.len / δ⌉₊ - 1)).1 := rfl
  have hbase : (aux 0).1 = GP.G (γ.toFun (s 0)) (γ.toFun (s 1)) := rfl
  have hconcat : ∀ n : ℕ, (aux n).1.toFun (aux n).1.len
      = (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2)))).toFun 0 := by
    intro n
    rw [(aux n).2, GP.start_eq]
  have hrec : ∀ n : ℕ, (aux (n + 1)).1
      = curveConcat (aux n).1 (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2)))) (hconcat n) :=
    fun n => rfl
  -- ## Elementary facts about the sample points `s j = min (j δ, len γ)`.
  have hL0 : (0:ℝ) < γ.len := lt_trans hδ0 hδlen
  have hsnn : ∀ j : ℕ, (0:ℝ) ≤ s j := fun j =>
    le_min (mul_nonneg (Nat.cast_nonneg j) hδ0.le) γ.len_nonneg
  have hsle : ∀ j : ℕ, s j ≤ γ.len := fun j => min_le_right _ _
  have hs0 : s 0 = 0 := by
    show min (((0:ℕ) : ℝ) * δ) γ.len = 0
    rw [Nat.cast_zero, zero_mul, min_eq_left γ.len_nonneg]
  have hmonoS : Monotone s := by
    intro a b hab
    have hab' : ((a : ℝ)) ≤ (b : ℝ) := by exact_mod_cast hab
    exact min_le_min (mul_le_mul_of_nonneg_right hab' hδ0.le) le_rfl
  have hmle : ∀ j : ℕ, s j ≤ s (j + 1) := fun j => hmonoS (Nat.le_succ j)
  have hsdiff : ∀ j : ℕ, s (j + 1) - s j ≤ δ := by
    intro j
    have hcast : (((j + 1 : ℕ)) : ℝ) * δ = (j : ℝ) * δ + δ := by push_cast; ring
    have h1 : s (j + 1) ≤ (j : ℝ) * δ + δ := by
      refine le_trans (min_le_left _ _) ?_
      rw [hcast]
    have h2 : s (j + 1) ≤ γ.len := hsle (j + 1)
    rcases le_total ((j : ℝ) * δ) γ.len with h | h
    · have : s j = (j : ℝ) * δ := min_eq_left h
      rw [this]; linarith
    · have : s j = γ.len := min_eq_right h
      rw [this]; linarith
  have hge : γ.len ≤ ((⌈γ.len / δ⌉₊ : ℕ) : ℝ) * δ := by
    have := Nat.le_ceil (γ.len / δ)
    rwa [div_le_iff₀ hδ0] at this
  have hsK : s ⌈γ.len / δ⌉₊ = γ.len := min_eq_right hge
  have hceil : 0 < ⌈γ.len / δ⌉₊ := Nat.ceil_pos.mpr (div_pos hL0 hδ0)
  have hsub : (⌈γ.len / δ⌉₊ - 1) + 1 = ⌈γ.len / δ⌉₊ := Nat.succ_pred_eq_of_pos hceil
  have hnn : (0:ℝ) ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) :=
    mul_nonneg ω.fLip.coe_nonneg ω.piLip.coe_nonneg
  -- ## Chord estimate in endpoint form.
  have hchord : ∀ (σ : Curve E) (x y : E), σ.toFun 0 = x → σ.toFun σ.len = y →
      |curveCurrent σ ω - ω.f x * (ω.pi y - ω.pi x)|
        ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * σ.len ^ 2 / 2 := by
    intro σ x y hx hy
    have h := CurrentChordEstimate σ ω 0 le_rfl σ.len_nonneg
    rw [hx, hy] at h
    exact h
  -- ## Endpoint / length data for the restrictions `γ|_{[a,b]}`.
  have hrestr : ∀ (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ γ.len),
      (curveRestrict γ a b ha hab hb).len = b - a
      ∧ (curveRestrict γ a b ha hab hb).toFun 0 = γ.toFun a
      ∧ (curveRestrict γ a b ha hab hb).toFun (curveRestrict γ a b ha hab hb).len
          = γ.toFun b := by
    intro a b ha hab hb
    have hba : (0:ℝ) ≤ b - a := by linarith
    refine ⟨rfl, ?_, ?_⟩
    · show γ.toFun (a + min (b - a) (max 0 0)) = γ.toFun a
      rw [max_self, min_eq_right hba, add_zero]
    · show γ.toFun (a + min (b - a) (max 0 (b - a))) = γ.toFun b
      rw [max_eq_right hba, min_self]
      congr 1
      ring
  -- ## Per-piece comparison: the geodesic `G_j` against the restriction `η_j`.
  have hstep : ∀ j : ℕ,
      |curveCurrent (GP.G (γ.toFun (s j)) (γ.toFun (s (j + 1)))) ω
          - ∫ t in (s j)..(s (j + 1)), ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t|
        ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ * (s (j + 1) - s j) := by
    intro j
    have hd0 : (0:ℝ) ≤ s (j + 1) - s j := by linarith [hmle j]
    have hdδ : s (j + 1) - s j ≤ δ := hsdiff j
    obtain ⟨hRlen, hRstart, hRend⟩ := hrestr (s j) (s (j + 1)) (hsnn j) (hmle j) (hsle (j + 1))
    have hRcur : curveCurrent
        (curveRestrict γ (s j) (s (j + 1)) (hsnn j) (hmle j) (hsle (j + 1))) ω
          = ∫ t in (s j)..(s (j + 1)), ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t :=
      RestrictCurrentFormula γ (s j) (s (j + 1)) (hsnn j) (hmle j) (hsle (j + 1)) ω
    have hE := hchord _ _ _ hRstart hRend
    rw [hRcur, hRlen] at hE
    have hG := hchord (GP.G (γ.toFun (s j)) (γ.toFun (s (j + 1))))
      (γ.toFun (s j)) (γ.toFun (s (j + 1))) (GP.start_eq _ _) (GP.end_eq _ _)
    have hGlen : (GP.G (γ.toFun (s j)) (γ.toFun (s (j + 1)))).len ≤ s (j + 1) - s j := by
      rw [GP.len_eq]
      have hlip : dist (γ.toFun (s j)) (γ.toFun (s (j + 1))) ≤ |s j - s (j + 1)| := by
        simpa [Real.dist_eq] using (CurveLipschitz γ).dist_le_mul (s j) (s (j + 1))
      calc dist (γ.toFun (s j)) (γ.toFun (s (j + 1))) ≤ |s j - s (j + 1)| := hlip
        _ = s (j + 1) - s j := by rw [abs_sub_comm, abs_of_nonneg hd0]
    have hGnn : (0:ℝ) ≤ (GP.G (γ.toFun (s j)) (γ.toFun (s (j + 1)))).len :=
      Curve.len_nonneg _
    have hsq : (GP.G (γ.toFun (s j)) (γ.toFun (s (j + 1)))).len ^ 2 + (s (j + 1) - s j) ^ 2
        ≤ 2 * δ * (s (j + 1) - s j) := by nlinarith
    have hkey := mul_le_mul_of_nonneg_left hsq hnn
    rw [abs_le] at hG hE ⊢
    constructor
    · linarith [hG.1, hG.2, hE.1, hE.2]
    · linarith [hG.1, hG.2, hE.1, hE.2]
  -- ## The `γ` side: resolution additivity at the sample points.
  have hgamma : curveCurrent γ ω
      = ∑ i ∈ Finset.range ⌈γ.len / δ⌉₊,
          ∫ t in (s i)..(s (i + 1)), ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t :=
    CurrentResolutionAdditive γ ω ⌈γ.len / δ⌉₊ s (hmonoS.monotoneOn _) hs0 hsK
  -- ## The induction over the `k`-fold concatenation.
  have key : ∀ n : ℕ, (aux n).1.len ≤ s (n + 1)
      ∧ |curveCurrent (aux n).1 ω
          - ∑ j ∈ Finset.range (n + 1),
              ∫ t in (s j)..(s (j + 1)), ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t|
        ≤ (ω.fLip : ℝ) * (ω.piLip : ℝ) * δ * s (n + 1) := by
    intro n
    induction n with
    | zero =>
        constructor
        · rw [hbase, GP.len_eq]
          have hd0 : (0:ℝ) ≤ s 1 - s 0 := by linarith [hmle 0]
          have hlip : dist (γ.toFun (s 0)) (γ.toFun (s 1)) ≤ |s 0 - s 1| := by
            simpa [Real.dist_eq] using (CurveLipschitz γ).dist_le_mul (s 0) (s 1)
          rw [abs_sub_comm, abs_of_nonneg hd0] at hlip
          linarith [hs0 ▸ hlip]
        · rw [hbase, Finset.sum_range_one]
          have h := hstep 0
          have he : s (0 + 1) - s 0 = s (0 + 1) := by rw [hs0, sub_zero]
          rw [he] at h
          exact h
    | succ n ih =>
        obtain ⟨ihlen, ihcur⟩ := ih
        have hd0 : (0:ℝ) ≤ s (n + 2) - s (n + 1) := by linarith [hmle (n + 1)]
        have hGlen : (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2)))).len
            ≤ s (n + 2) - s (n + 1) := by
          rw [GP.len_eq]
          have hlip : dist (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2)))
              ≤ |s (n + 1) - s (n + 2)| := by
            simpa [Real.dist_eq] using
              (CurveLipschitz γ).dist_le_mul (s (n + 1)) (s (n + 2))
          rw [abs_sub_comm, abs_of_nonneg hd0] at hlip
          exact hlip
        constructor
        · rw [hrec n]
          show (aux n).1.len + (GP.G (γ.toFun (s (n + 1))) (γ.toFun (s (n + 2)))).len
            ≤ s (n + 1 + 1)
          linarith
        · rw [hrec n, CurrentConcatAdditive, Finset.sum_range_succ]
          have h := hstep (n + 1)
          rw [abs_le] at ihcur h ⊢
          constructor
          · linarith [ihcur.1, ihcur.2, h.1, h.2]
          · linarith [ihcur.1, ihcur.2, h.1, h.2]
  -- ## Assemble.
  obtain ⟨klen, kcur⟩ := key (⌈γ.len / δ⌉₊ - 1)
  have hsK' : s (⌈γ.len / δ⌉₊ - 1 + 1) = γ.len := by rw [hsub]; exact hsK
  have hsum : ∑ j ∈ Finset.range (⌈γ.len / δ⌉₊ - 1 + 1),
      ∫ t in (s j)..(s (j + 1)), ω.f (γ.toFun t) * deriv (ω.pi ∘ γ.toFun) t
        = curveCurrent γ ω := by rw [hsub]; exact hgamma.symm
  refine ⟨?_, ?_⟩
  · rw [hsamp]
    exact klen.trans hsK'.le
  · rw [hsamp, ← hsum]
    refine kcur.trans (le_of_eq ?_)
    rw [hsK']
