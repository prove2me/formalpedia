-- Prove2me | solution 1 for MultimodalPricing.Regret.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T08:51:56.920611+00:00
-- url     : https://prove2.me/submissions/71237c9d-9b72-4873-a8a2-803d20989217

import Mathlib
import Definitions.Def_MultimodalPricing_Regret_Smooth

open MultimodalPricing.Regret
namespace MPT

lemma poly_deriv (c : ℕ → ℝ) (a x : ℝ) (d : ℕ) :
    HasDerivAt (fun y => ∑ r ∈ Finset.range (d+1), c r * (y - a)^r)
      (∑ r ∈ Finset.range d, c (r+1) * ((r:ℝ)+1) * (x-a)^r) x := by
  have h : ∀ r ∈ Finset.range (d+1), HasDerivAt (fun y => c r * (y-a)^r)
      (c r * ((r:ℝ) * (x-a)^(r-1) * 1)) x := by
    intro r _
    exact (((hasDerivAt_id x).sub_const a).pow r).const_mul (c r)
  have := HasDerivAt.fun_sum h
  refine this.congr_deriv ?_
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel, mul_one]
  ring

lemma rem_bound {k : ℕ} {C a b : ℝ} {g : ℕ → ℝ → ℝ} (hab : a ≤ b) (hC : 0 ≤ C)
    (hder : ∀ q, q + 1 < k → ∀ p ∈ Set.Icc a b, HasDerivWithinAt (g q) (g (q+1) p) (Set.Icc a b) p)
    (hlip : ∀ p ∈ Set.Icc a b, ∀ p' ∈ Set.Icc a b, |g (k-1) p - g (k-1) p'| ≤ C * |p - p'|) :
    ∀ d, 1 ≤ d → d ≤ k → ∀ p ∈ Set.Icc a b,
      |g (k-d) p - ∑ r ∈ Finset.range d, g (k-d+r) a / (r.factorial : ℝ) * (p-a)^r|
        ≤ C * (p-a)^d / (d.factorial : ℝ) := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro hk p hp
    have := hlip p hp a ⟨le_rfl, hab⟩
    have h1 : |p - a| = p - a := abs_of_nonneg (by linarith [hp.1])
    simp only [Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one, div_one,
      pow_zero, mul_one, add_zero, Nat.factorial_one, pow_one]
    rw [h1] at this
    simpa using this
  | succ d hd ih =>
    intro hdk p hp
    have ih' := ih (by omega)
    have hqk : k - (d+1) + 1 < k := by omega
    have hq1 : k - d = k - (d+1) + 1 := by omega
    rw [hq1] at ih'
    generalize k - (d+1) = q at *
    set F : ℝ → ℝ := fun x => g q x - ∑ r ∈ Finset.range (d+1), g (q+r) a / (r.factorial : ℝ) * (x-a)^r with hFdef
    set G : ℝ → ℝ := fun x => g (q+1) x - ∑ r ∈ Finset.range d, g (q+1+r) a / (r.factorial : ℝ) * (x-a)^r with hGdef
    have hF : ∀ x ∈ Set.Icc a b, HasDerivWithinAt F (G x) (Set.Icc a b) x := by
      intro x hx
      have h1 := hder q hqk x hx
      have h2 := (poly_deriv (fun r => g (q+r) a / (r.factorial : ℝ)) a x d).hasDerivWithinAt (s := Set.Icc a b)
      have h3 := h1.sub h2
      refine h3.congr_deriv ?_
      simp only [hGdef]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Nat.factorial_succ]
      have : (r.factorial : ℝ) ≠ 0 := by positivity
      push_cast
      rw [show q + (r+1) = q + 1 + r by ring]
      field_simp
    have hpa : a ≤ p := hp.1
    have hcont : ContinuousOn F (Set.Icc a p) := fun x hx =>
      (hF x ⟨hx.1, hx.2.trans hp.2⟩).continuousWithinAt.mono (Set.Icc_subset_Icc_right hp.2)
    have hFa : F a = 0 := by
      simp only [hFdef]
      rw [Finset.sum_range_succ']
      simp
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := F) (f' := G) (a := a) (b := p)
      hcont
      (fun x hx => (hF x ⟨hx.1, hx.2.le.trans hp.2⟩).mono_of_mem_nhdsWithin
        (Filter.mem_of_superset (Icc_mem_nhdsGE (lt_of_lt_of_le hx.2 hp.2)) (Set.Icc_subset_Icc_left hx.1)))
      (B := fun x => C * (x-a)^(d+1) / ((d+1).factorial : ℝ))
      (B' := fun x => C * (x-a)^d / (d.factorial : ℝ))
      (by rw [hFa]; simp)
      (fun x => by
        have h := (((hasDerivAt_id x).sub_const a).pow (d+1)).const_mul (C / ((d+1).factorial : ℝ))
        have e : (fun x => C * (x-a)^(d+1) / ((d+1).factorial : ℝ)) =
            fun x => C / ((d+1).factorial : ℝ) * (id x - a)^(d+1) := by
          ext y; simp only [id]; ring
        rw [e]
        refine h.congr_deriv ?_
        rw [Nat.factorial_succ]
        have : (d.factorial : ℝ) ≠ 0 := by positivity
        push_cast
        simp only [id, mul_one]
        field_simp)
      (by
        intro x hx
        have := ih' x ⟨hx.1, hx.2.le.trans hp.2⟩
        rw [Real.norm_eq_abs]
        exact this)
    have := key ⟨hpa, le_rfl⟩
    rw [Real.norm_eq_abs] at this
    exact this

end MPT

theorem solution
    (k : ℕ) (C pmin pmax a b : ℝ) (f : ℝ → ℝ)
    (hf : Smooth k C pmin pmax f)
    (hab : a ≤ b) (hleft : pmin ≤ a) (hright : b ≤ pmax) (hwidth : b - a ≤ 1) :
    ∃ c : Fin k → ℝ,
      (∀ q : Fin k, |c q| * (q.val.factorial : ℝ) ≤ C) ∧
      ∀ p ∈ Set.Icc a b, |f p - localPolynomial k a c p| ≤ C * (b - a) ^ k := by
  obtain ⟨hk1, hC, hpq, hrange, g, hg0, hder, hbd, hlip⟩ := hf
  have hsub : Set.Icc a b ⊆ Set.Icc pmin pmax := Set.Icc_subset_Icc hleft hright
  refine ⟨fun q => g q.val a / (q.val.factorial : ℝ), ?_, ?_⟩
  · intro q
    have hq := hbd q.val q.isLt a ⟨hleft, hab.trans hright⟩
    have : (q.val.factorial : ℝ) ≠ 0 := by positivity
    rw [abs_div, Nat.abs_cast, div_mul_cancel₀ _ this]
    exact hq
  · intro p hp
    have key := MPT.rem_bound (k := k) (C := C) (a := a) (b := b) (g := g) hab hC.le
      (fun q hq p hp => (hder q hq p (hsub hp)).mono hsub)
      (fun p hp p' hp' => hlip p (hsub hp) p' (hsub hp')) k hk1 le_rfl p hp
    rw [Nat.sub_self] at key
    have hloc : localPolynomial k a (fun q => g q.val a / (q.val.factorial : ℝ)) p =
        ∑ r ∈ Finset.range k, g (0 + r) a / (r.factorial : ℝ) * (p - a)^r := by
      unfold localPolynomial
      rw [Finset.sum_range (fun r => g (0 + r) a / (r.factorial : ℝ) * (p - a)^r)]
      simp
    rw [hloc, ← hg0 p (hsub hp)]
    refine key.trans ?_
    have h1 : (p - a) ^ k ≤ (b - a) ^ k := pow_le_pow_left₀ (by linarith [hp.1]) (by linarith [hp.2]) k
    have h2 : (1 : ℝ) ≤ (k.factorial : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
    rw [div_le_iff₀ (by linarith)]
    calc C * (p - a) ^ k ≤ C * (b - a) ^ k * 1 := by nlinarith
      _ ≤ C * (b - a) ^ k * (k.factorial : ℝ) := by
          apply mul_le_mul_of_nonneg_left h2
          have : 0 ≤ b - a := by linarith
          positivity
