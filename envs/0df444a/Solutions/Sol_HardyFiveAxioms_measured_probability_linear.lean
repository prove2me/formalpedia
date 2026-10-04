-- Prove2me | solution 1 for HardyFiveAxioms.measured_probability_linear
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T08:17:41.036752+00:00
-- url     : https://prove2.me/submissions/0d1036bb-6cf1-4065-9ad1-24739a5defaf

import Mathlib

set_option autoImplicit false

namespace D783626f

lemma homog_le {K : ℕ} (S : Set (Fin K → ℝ)) (h0 : (0 : Fin K → ℝ) ∈ S)
    (f : (Fin K → ℝ) → ℝ) (hf0 : f 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • pA + (1 - t) • pB) = t * f pA + (1 - t) * f pB)
    {c d : ℝ} {p q : Fin K → ℝ} (hq : q ∈ S) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hdc : d ≤ c) (h : c • p = d • q) : c * f p = d * f q := by
  rcases hc.lt_or_eq with hc' | hc'
  · have hpq : (d / c) • q + (1 - d / c) • (0 : Fin K → ℝ) = p := by
      rw [smul_zero, add_zero, div_eq_inv_mul, mul_smul, ← h, smul_smul,
        inv_mul_cancel₀ hc'.ne', one_smul]
    have := hmix q hq 0 h0 (d / c) (div_nonneg hd hc) ((div_le_one hc').2 hdc)
    rw [hpq, hf0, mul_zero, add_zero] at this
    rw [this]; field_simp
  · subst hc'
    have : d = 0 := le_antisymm hdc hd
    simp [this]

lemma homog {K : ℕ} (S : Set (Fin K → ℝ)) (h0 : (0 : Fin K → ℝ) ∈ S)
    (f : (Fin K → ℝ) → ℝ) (hf0 : f 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • pA + (1 - t) • pB) = t * f pA + (1 - t) * f pB)
    {c d : ℝ} {p q : Fin K → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h : c • p = d • q) : c * f p = d * f q := by
  rcases le_total d c with hdc | hcd
  · exact homog_le S h0 f hf0 hmix hq hc hd hdc h
  · exact (homog_le S h0 f hf0 hmix hp hd hc hcd h.symm).symm

lemma cone_add {K : ℕ} (S : Set (Fin K → ℝ)) (hS : Convex ℝ S)
    (f : (Fin K → ℝ) → ℝ)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • pA + (1 - t) • pB) = t * f pA + (1 - t) * f pB)
    {c d : ℝ} {p q : Fin K → ℝ} (hp : p ∈ S) (hq : q ∈ S) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    ∃ e : ℝ, 0 ≤ e ∧ ∃ r ∈ S,
      ((c • p, c * f p) : (Fin K → ℝ) × ℝ) + (d • q, d * f q) = (e • r, e * f r) := by
  rcases (add_nonneg hc hd).lt_or_eq with he | he
  · set e := c + d with hedef
    have ht0 : 0 ≤ c / e := div_nonneg hc he.le
    have ht1 : c / e ≤ 1 := (div_le_one he).2 (by linarith)
    have hr : (c / e) • p + (1 - c / e) • q ∈ S :=
      hS hp hq ht0 (by linarith) (by ring)
    refine ⟨e, he.le, _, hr, ?_⟩
    rw [hmix p hp q hq _ ht0 ht1]
    have h1 : e * (c / e) = c := by field_simp
    have h2 : e * (1 - c / e) = d := by field_simp; linarith
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_add, smul_add, smul_smul, h1, h2]
    · simp only [Prod.snd_add, mul_add, ← mul_assoc, h1, h2]
  · have hc0 : c = 0 := by linarith
    have hd0 : d = 0 := by linarith
    refine ⟨0, le_rfl, p, hp, ?_⟩
    simp [hc0, hd0]

end D783626f

theorem solution {K : ℕ} (S : Set (Fin K → ℝ)) (hS : Convex ℝ S)
    (h0 : (0 : Fin K → ℝ) ∈ S) (f : (Fin K → ℝ) → ℝ) (hf0 : f 0 = 0)
    (hmix : ∀ pA ∈ S, ∀ pB ∈ S, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f (t • pA + (1 - t) • pB) = t * f pA + (1 - t) * f pB) :
    ∃ r : Fin K → ℝ, ∀ p ∈ S, f p = ∑ k, r k * p k := by
  classical
  let Kc : Set ((Fin K → ℝ) × ℝ) :=
    {x | ∃ c : ℝ, 0 ≤ c ∧ ∃ p ∈ S, x = (c • p, c * f p)}
  let G : Set ((Fin K → ℝ) × ℝ) := (fun p => (p, f p)) '' S
  let W : Submodule ℝ ((Fin K → ℝ) × ℝ) := Submodule.span ℝ G
  have hKadd : ∀ x ∈ Kc, ∀ y ∈ Kc, x + y ∈ Kc := by
    rintro _ ⟨c, hc, p, hp, rfl⟩ _ ⟨d, hd, q, hq, rfl⟩
    obtain ⟨e, he, r, hr, h⟩ := D783626f.cone_add S hS f hmix hp hq hc hd
    exact ⟨e, he, r, hr, h⟩
  have hKsmul : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ Kc, a • x ∈ Kc := by
    rintro a ha _ ⟨c, hc, p, hp, rfl⟩
    refine ⟨a * c, mul_nonneg ha hc, p, hp, ?_⟩
    refine Prod.ext ?_ ?_
    · simp [smul_smul]
    · simp [mul_assoc]
  have hK0 : (0 : (Fin K → ℝ) × ℝ) ∈ Kc := ⟨0, le_rfl, 0, h0, by ext <;> simp⟩
  have hspan : ∀ x ∈ W, ∃ a ∈ Kc, ∃ b ∈ Kc, x = a - b := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, hp, rfl⟩ := hx
      exact ⟨(p, f p), ⟨1, zero_le_one, p, hp, by ext <;> simp⟩, 0, hK0, by simp⟩
    | zero => exact ⟨0, hK0, 0, hK0, by simp⟩
    | add x y _ _ ihx ihy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ihx
      obtain ⟨a', ha', b', hb', rfl⟩ := ihy
      exact ⟨a + a', hKadd _ ha _ ha', b + b', hKadd _ hb _ hb', by abel⟩
    | smul r x _ ih =>
      obtain ⟨a, ha, b, hb, rfl⟩ := ih
      rcases le_total 0 r with hr | hr
      · exact ⟨r • a, hKsmul r hr a ha, r • b, hKsmul r hr b hb, by rw [smul_sub]⟩
      · refine ⟨(-r) • b, hKsmul _ (by linarith) b hb, (-r) • a,
          hKsmul _ (by linarith) a ha, ?_⟩
        rw [smul_sub, neg_smul, neg_smul]; abel
  have hnot : ((0 : Fin K → ℝ), (1 : ℝ)) ∉ W := by
    intro hmem
    obtain ⟨_, ⟨c, hc, p, hp, rfl⟩, _, ⟨d, hd, q, hq, rfl⟩, h⟩ := hspan _ hmem
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    have hcd : c • p = d • q := (sub_eq_zero.1 h1.symm)
    have := D783626f.homog S h0 f hf0 hmix hp hq hc hd hcd
    linarith
  obtain ⟨φ, hφ1, hφW⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hφG : ∀ p ∈ S, φ (p, f p) = 0 := by
    intro p hp
    have hm : φ (p, f p) ∈ W.map φ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨p, hp, rfl⟩)
    rw [hφW] at hm
    exact (Submodule.mem_bot ℝ).1 hm
  set c := φ ((0 : Fin K → ℝ), (1 : ℝ)) with hcdef
  let ψ : (Fin K → ℝ) →ₗ[ℝ] ℝ := φ.comp (LinearMap.inl ℝ (Fin K → ℝ) ℝ)
  have hsplit : ∀ p : Fin K → ℝ, ∀ y : ℝ, φ (p, y) = ψ p + y * c := by
    intro p y
    have : ((p, y) : (Fin K → ℝ) × ℝ) = (p, 0) + y • ((0 : Fin K → ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  refine ⟨fun k => -(ψ fun j => if k = j then 1 else 0) / c, ?_⟩
  intro p hp
  have h := hφG p hp
  rw [hsplit] at h
  have hfp : f p = -ψ p / c := by
    field_simp; linarith
  rw [hfp, LinearMap.pi_apply_eq_sum_univ ψ p, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [smul_eq_mul]
  ring
