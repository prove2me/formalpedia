-- Prove2me | solution 1 for HDXHitting.lemma_3_2_one_sided
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T07:07:53.173931+00:00
-- url     : https://prove2.me/submissions/81e24462-6262-465c-93bd-406f135de343

import Mathlib
import Definitions.Def_HDXHitting_IsTopDist
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit
import Definitions.Def_HDXHitting_linkWeight
import Definitions.Def_HDXHitting_IsOneSidedHDX
import Definitions.Def_HDXHitting_cMax
import Theorems.Thm_HDXHitting_eq_4
import Theorems.Thm_HDXHitting_cmax_lipschitz

section
set_option autoImplicit false
namespace HDXHitting.Dev.OS
open HDXHitting

theorem left_mono (ψ : ℝ → ℝ) (y : ℝ) (hy : 0 < y) (hcont : ContinuousOn ψ (Set.Icc 0 y))
    (hloc : ∀ u ∈ Set.Ioc 0 y, ∃ s₀ > 0, ∀ s, 0 < s → s < s₀ → ψ (u - s) ≤ ψ u) :
    ψ 0 ≤ ψ y := by
  by_contra h
  push Not at h
  have hTcl : IsClosed (Set.Icc 0 y ∩ ψ ⁻¹' Set.Iic (ψ y)) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  set T : Set ℝ := Set.Icc 0 y ∩ ψ ⁻¹' Set.Iic (ψ y) with hT
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset hTcl Set.inter_subset_left
  have hyT : y ∈ T := ⟨⟨hy.le, le_rfl⟩, by simp⟩
  have hne : T.Nonempty := ⟨y, hyT⟩
  have hz := hTc.sInf_mem hne
  set z := sInf T with hzdef
  have hbdd : BddBelow T := hTc.bddBelow
  have hz0 : 0 < z := by
    rcases hz.1.1.eq_or_lt with h0 | h0
    · exfalso
      have := hz.2
      simp only [Set.mem_preimage, Set.mem_Iic] at this
      rw [← h0] at this
      linarith
    · exact h0
  have hzy : z ≤ y := hz.1.2
  obtain ⟨s₀, hs₀, hs⟩ := hloc z ⟨hz0, hzy⟩
  set s := min (s₀ / 2) (z / 2) with hsdef
  have hs0 : 0 < s := lt_min (by linarith) (by linarith)
  have hs1 : s < s₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hs2 : s ≤ z / 2 := min_le_right _ _
  have hmem : z - s ∈ T := by
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    simp only [Set.mem_preimage, Set.mem_Iic]
    exact (hs s hs0 hs1).trans hz.2
  have := csInf_le hbdd hmem
  linarith

theorem analysis (c G g : ℝ → ℝ) (hc : ContinuousOn c (Set.Icc 0 1))
    (hG : ∀ x, HasDerivAt G (g x) x) (hc0 : c 0 ≤ G 0)
    (hloc : ∀ μ, 0 < μ → μ < 1 → ∃ s₀ > 0, ∀ s, 0 < s → s < s₀ → c μ ≤ c (μ - s) + s * g μ)
    (y : ℝ) (hy0 : 0 < y) (hy1 : y < 1) : c y ≤ G y := by
  have key : ∀ δ : ℝ, 0 < δ → c y ≤ G y + δ * y := by
    intro δ hδ
    set ψ : ℝ → ℝ := fun x => G x - c x + δ * x with hψ
    have hcont : ContinuousOn ψ (Set.Icc 0 y) := by
      have h1 : Continuous G := continuous_iff_continuousAt.mpr (fun x => (hG x).continuousAt)
      have h2 : ContinuousOn c (Set.Icc 0 y) :=
        hc.mono (Set.Icc_subset_Icc le_rfl hy1.le)
      exact ((h1.continuousOn.sub h2).add (continuous_const.mul continuous_id).continuousOn)
    have hl : ∀ u ∈ Set.Ioc 0 y, ∃ s₀ > 0, ∀ s, 0 < s → s < s₀ → ψ (u - s) ≤ ψ u := by
      intro u hu
      obtain ⟨s₁, hs₁, hs₁'⟩ := hloc u hu.1 (lt_of_le_of_lt hu.2 hy1)
      have hd := (hasDerivAt_iff_isLittleO.mp (hG u)).def hδ
      obtain ⟨η, hη, hη'⟩ := Metric.eventually_nhds_iff.mp hd
      refine ⟨min s₁ η, lt_min hs₁ hη, ?_⟩
      intro s hs hs'
      have h1 := hs₁' s hs (lt_of_lt_of_le hs' (min_le_left _ _))
      have h2 := hη' (y := u - s) (by
        rw [Real.dist_eq]; simp only [sub_sub_cancel_left, abs_neg, abs_of_pos hs]
        exact lt_of_lt_of_le hs' (min_le_right _ _))
      simp only [Real.norm_eq_abs, smul_eq_mul, sub_sub_cancel_left, abs_neg, abs_of_pos hs] at h2
      have h3 := (abs_le.mp h2).2
      simp only [hψ]
      nlinarith
    have := left_mono ψ y hy0 hcont hl
    simp only [hψ] at this
    nlinarith
  by_contra hcon
  push Not at hcon
  have := key ((c y - G y) / (2 * y)) (by apply div_pos <;> linarith)
  have e : (c y - G y) / (2 * y) * y = (c y - G y) / 2 := by field_simp
  rw [e] at this
  linarith

theorem hit_le_one {V : Type*} [Fintype V] (d : ℕ) (p : Finset V → ℝ) (hp : IsTopDist d p)
    (g : V → ℝ) (hg : ∀ v, 0 ≤ g v ∧ g v ≤ 1) : hit p g ≤ 1 := by
  unfold hit
  calc ∑ σ, p σ * ∏ v ∈ σ, g v ≤ ∑ σ, p σ * 1 := by
        apply Finset.sum_le_sum
        intro σ _
        apply mul_le_mul_of_nonneg_left _ (hp.1 σ)
        exact Finset.prod_le_one (fun v _ => (hg v).1) (fun v _ => (hg v).2)
    _ = 1 := by simp [hp.2.2]

theorem hit_mean_one {V : Type*} [Fintype V] [DecidableEq V] (p : Finset V → ℝ)
    (hp : IsTopDist 1 p) (f : V → ℝ) : hit p f = mean 1 p f := by
  unfold hit mean vertexMeasure
  have h1 : ∀ σ : Finset V, p σ * ∏ v ∈ σ, f v = p σ * ∑ v ∈ σ, f v := by
    intro σ
    by_cases h : p σ = 0
    · simp [h]
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (hp.2.1 σ h)
      simp
  simp_rw [h1]
  simp only [Nat.cast_one, div_one, one_mul, Finset.sum_mul, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  simp_rw [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  have : Finset.univ.filter (fun v : V => v ∈ σ) = σ := by ext; simp
  rw [this]

theorem mean_le_one {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    mean d p f ≤ 1 := by
  have hsum : ∑ v, vertexMeasure d p v = 1 := by
    unfold vertexMeasure
    rw [← Finset.mul_sum]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    have : ∀ σ : Finset V, (∑ u : V, if u ∈ σ then p σ else 0) = d * p σ := by
      intro σ
      by_cases h : p σ = 0
      · simp [h]
      · rw [← Finset.sum_filter, Finset.sum_const]
        have : Finset.univ.filter (fun u : V => u ∈ σ) = σ := by ext; simp
        rw [this, hp.2.1 σ h]
        simp
    simp_rw [this, ← Finset.mul_sum, hp.2.2, mul_one]
    have : (d : ℝ) ≠ 0 := by
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd
      intro h; linarith
    field_simp
  calc mean d p f = ∑ v, vertexMeasure d p v * f v := rfl
    _ ≤ ∑ v, vertexMeasure d p v * 1 := by
        apply Finset.sum_le_sum
        intro v _
        apply mul_le_mul_of_nonneg_left (hf v).2
        unfold vertexMeasure
        exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun σ _ => hp.1 σ))
    _ = 1 := by simp [hsum]

theorem hit_zero {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1)
    (hm : mean d p f = 0) : hit p f = 0 := by
  have hnn : ∀ v, 0 ≤ vertexMeasure d p v * f v := by
    intro v
    apply mul_nonneg _ (hf v).1
    unfold vertexMeasure
    exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun σ _ => hp.1 σ))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ => hnn v)).mp hm
  unfold hit
  apply Finset.sum_eq_zero
  intro σ _
  by_cases h : p σ = 0
  · simp [h]
  · have hc : σ.card = d := hp.2.1 σ h
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < σ.card)
    have hppos : 0 < p σ := lt_of_le_of_ne (hp.1 σ) (Ne.symm h)
    have hπ : 0 < vertexMeasure d p v := by
      unfold vertexMeasure
      apply mul_pos (by have : (0 : ℝ) < d := by exact_mod_cast hd
                        positivity)
      calc 0 < p σ := hppos
        _ ≤ _ := Finset.single_le_sum (f := p) (fun σ _ => hp.1 σ)
              (Finset.mem_filter.mpr ⟨Finset.mem_univ σ, hv⟩)
    have := hz v (Finset.mem_univ v)
    have hf0 : f v = 0 := by
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hπ.ne'
      · exact h'
    rw [Finset.prod_eq_zero hv hf0, mul_zero]

end HDXHitting.Dev.OS
namespace HDXHitting
open HDXHitting.Dev.OS in
theorem chk_lemma_3_2_one_sided {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd : 1 ≤ d)
    (p : Finset V → ℝ) (hp : IsTopDist d p) (lam : ℝ) (hlam : 0 ≤ lam)
    (hX : IsOneSidedHDX d p lam) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    hit p f ≤ mean d p f * (mean d p f + d * lam) ^ (d - 1) := by
  induction d, hd using Nat.le_induction generalizing p f with
  | base =>
    rw [hit_mean_one p hp f]
    simp
  | succ e he IH =>
    have hc := HDXHitting.cmax_lipschitz (e + 1) (by omega) p hp
    have hcast : (((e + 1 : ℕ) : ℝ)) = (e : ℝ) + 1 := by push_cast; ring
    set D : ℝ := ((e + 1 : ℕ) : ℝ) with hD
    have heq4 := HDXHitting.eq_4 (V := V) (e + 1) (by omega) p hp lam hlam hX
      (fun p' hp' hX' g hg => IH p' hp' hX' g hg)
    set G : ℝ → ℝ := fun x => x * (x + D * lam) ^ e with hG
    set g : ℝ → ℝ := fun x => D * (x + lam) * (x + D * lam) ^ (e - 1) with hg
    have hder : ∀ x, HasDerivAt G (g x) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => x + D * lam) 1 x := (hasDerivAt_id x).add_const _
      have h2 := h1.pow e
      have h3 := (hasDerivAt_id x).mul h2
      have h4 : HasDerivAt G (1 * ((fun x : ℝ => x + D * lam) ^ e) x + id x * (↑e * (x + D * lam) ^ (e - 1) * 1)) x := h3
      refine h4.congr_deriv ?_
      simp only [hg, id, Pi.pow_apply]
      obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
      simp only [Nat.add_sub_cancel, hD]
      push_cast
      ring
    have hcont : ContinuousOn (cMax (e + 1) p) (Set.Icc 0 1) := by
      have : LipschitzOnWith ((e + 1 : ℕ) : NNReal) (cMax (e + 1) p) (Set.Icc 0 1) := by
        apply LipschitzOnWith.of_dist_le_mul
        intro x hx y hy
        rw [Real.dist_eq, Real.dist_eq]
        have := hc.2 x y hx.1 hx.2 hy.1 hy.2
        rw [hcast] at this
        simpa using this
      exact this.continuousOn
    have hc0 : cMax (e + 1) p 0 ≤ G 0 := by
      obtain ⟨f0, hf0, hm0, hh0⟩ := hc.1 0 le_rfl zero_le_one
      rw [← hh0, hit_zero (e + 1) (by omega) p hp f0 hf0 hm0]
      simp [hG]
    have hloc : ∀ μ, 0 < μ → μ < 1 → ∃ s₀ > 0, ∀ s, 0 < s → s < s₀ →
        cMax (e + 1) p μ ≤ cMax (e + 1) p (μ - s) + s * g μ := by
      intro μ h0 h1
      obtain ⟨s₀, hs₀, hs⟩ := heq4 μ h0 h1
      refine ⟨s₀, hs₀, fun s hs0 hs1 => ?_⟩
      have := hs s hs0 hs1
      simpa [hg, hD] using this
    have hbd : ∀ μ, hit p f ≤ cMax (e + 1) p μ ∨ mean (e + 1) p f ≠ μ := by
      intro μ
      by_cases hm : mean (e + 1) p f = μ
      · left
        unfold cMax
        apply le_csSup
        · refine ⟨1, ?_⟩
          rintro _ ⟨h, ⟨hh, _⟩, rfl⟩
          exact hit_le_one (e + 1) p hp h hh
        · exact ⟨f, ⟨hf, hm⟩, rfl⟩
      · right; exact hm
    have hfm := (hbd (mean (e + 1) p f)).resolve_right (by simp)
    -- mean in [0,1]
    have hm0 : 0 ≤ mean (e + 1) p f := by
      unfold mean vertexMeasure
      apply Finset.sum_nonneg
      intro v _
      exact mul_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg (fun σ _ => hp.1 σ))) (hf v).1
    have hm1 : mean (e + 1) p f ≤ 1 := by
      exact mean_le_one (e + 1) (by omega) p hp f hf
    show hit p f ≤ mean (e + 1) p f * (mean (e + 1) p f + ((e + 1 : ℕ) : ℝ) * lam) ^ (e + 1 - 1)
    rcases hm0.eq_or_lt with h0 | h0
    · have : hit p f = 0 := hit_zero (e + 1) (by omega) p hp f hf h0.symm
      rw [this, ← h0]; simp
    · rcases hm1.eq_or_lt with h1 | h1
      · -- mean = 1
        have hle : cMax (e + 1) p 1 ≤ 1 := by
          unfold cMax
          apply csSup_le
          · obtain ⟨f1, hf1, hm1', hh1⟩ := hc.1 1 zero_le_one le_rfl
            exact ⟨hit p f1, f1, ⟨hf1, hm1'⟩, rfl⟩
          · rintro _ ⟨h, ⟨hh, _⟩, rfl⟩
            exact hit_le_one (e + 1) p hp h hh
        rw [h1] at hfm ⊢
        have : (1 : ℝ) ≤ (1 + ((e + 1 : ℕ) : ℝ) * lam) ^ (e + 1 - 1) :=
          one_le_pow₀ (by have : (0 : ℝ) ≤ ((e + 1 : ℕ) : ℝ) * lam := by positivity
                          linarith)
        linarith
      · have := analysis (cMax (e + 1) p) G g hcont hder hc0 hloc _ h0 h1
        refine hfm.trans (this.trans ?_)
        simp only [hG, hD, Nat.add_sub_cancel]
        exact le_rfl

end HDXHitting
end

theorem solution : type_of% @HDXHitting.chk_lemma_3_2_one_sided := @HDXHitting.chk_lemma_3_2_one_sided
