-- Prove2me | solution 1 for MasulloGRH.exists_state_nonpos_on_cone
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:01:16.963662+00:00
-- url     : https://prove2.me/submissions/d94fb823-889d-4649-ba41-480d59c4062c

import Mathlib

set_option autoImplicit false

theorem solution (X : Type*) (S : Set X) (hS : S.Nonempty)
    (K : Set (X → ℝ)) (hadd : ∀ φ ∈ K, ∀ ψ ∈ K, φ + ψ ∈ K)
    (hsmul : ∀ r : ℝ, 0 ≤ r → ∀ φ ∈ K, r • φ ∈ K)
    (hbdd : ∀ φ ∈ K, ∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M)
    (hinf : ∀ φ ∈ K, ∀ ε : ℝ, 0 < ε → ∃ t ∈ S, φ t ≤ ε) :
    ∃ Λ : (X → ℝ) → ℝ,
      (∀ φ ψ : X → ℝ, (∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) → (∃ M : ℝ, ∀ t ∈ S, |ψ t| ≤ M) →
        Λ (φ + ψ) = Λ φ + Λ ψ) ∧
      (∀ (r : ℝ) (φ : X → ℝ), (∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) → Λ (r • φ) = r * Λ φ) ∧
      (∀ φ ψ : X → ℝ, (∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M) → (∃ M : ℝ, ∀ t ∈ S, |ψ t| ≤ M) →
        (∀ t ∈ S, φ t ≤ ψ t) → Λ φ ≤ Λ ψ) ∧
      Λ (fun _ => 1) = 1 ∧ ∀ φ ∈ K, Λ φ ≤ 0 := by
  classical
  obtain ⟨t0, ht0⟩ := hS
  -- the space of functions bounded on S
  let B : Submodule ℝ (X → ℝ) :=
    { carrier := {φ | ∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M}
      add_mem' := by
        rintro φ ψ ⟨M, hM⟩ ⟨N, hN⟩
        refine ⟨M + N, fun t ht => ?_⟩
        simp only [Pi.add_apply]
        exact (abs_add_le _ _).trans (add_le_add (hM t ht) (hN t ht))
      zero_mem' := ⟨0, fun t _ => by simp⟩
      smul_mem' := by
        rintro c φ ⟨M, hM⟩
        refine ⟨|c| * M, fun t ht => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg c) }
  have memB : ∀ φ : X → ℝ, φ ∈ B ↔ ∃ M : ℝ, ∀ t ∈ S, |φ t| ≤ M := fun _ => Iff.rfl
  -- the cone P - K₀
  let s : PointedCone ℝ B :=
    { carrier := {φ | ∃ k : X → ℝ, (k = 0 ∨ k ∈ K) ∧ ∀ t ∈ S, -k t ≤ (φ : X → ℝ) t}
      add_mem' := by
        rintro φ ψ ⟨k, hk, hkφ⟩ ⟨l, hl, hlψ⟩
        refine ⟨k + l, ?_, fun t ht => ?_⟩
        · rcases hk with rfl | hk
          · simpa using hl
          · rcases hl with rfl | hl
            · simpa using Or.inr hk
            · exact Or.inr (hadd k hk l hl)
        · have := hkφ t ht; have := hlψ t ht
          simp only [Pi.add_apply, Submodule.coe_add]; linarith
      zero_mem' := ⟨0, Or.inl rfl, fun t _ => by simp⟩
      smul_mem' := by
        rintro ⟨c, hc⟩ φ ⟨k, hk, hkφ⟩
        refine ⟨c • k, ?_, fun t ht => ?_⟩
        · rcases hk with rfl | hk
          · exact Or.inl (smul_zero c)
          · exact Or.inr (hsmul c hc k hk)
        · have := hkφ t ht
          have h2 : ((⟨c, hc⟩ : {c : ℝ // 0 ≤ c}) • φ : B) = (c • φ : B) := rfl
          rw [h2]
          simp only [Pi.smul_apply, smul_eq_mul, Submodule.coe_smul]
          nlinarith }
  let one : B := ⟨fun _ => 1, ⟨1, fun t _ => by simp⟩⟩
  have H : ∀ c : ℝ, c • one = 0 → c • (1 : ℝ) = 0 := by
    intro c hc
    have := congrArg (fun φ : B => (φ : X → ℝ) t0) hc
    simpa [one] using this
  let f : B →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' one 1 H
  have hf : ∀ (c : ℝ) (h), f ⟨c • one, h⟩ = c := by
    intro c h
    have := LinearPMap.mkSpanSingleton'_apply one (1 : ℝ) H c h
    simp only [smul_eq_mul, mul_one] at this
    exact this
  have nonneg : ∀ x : f.domain, (x : B) ∈ s → 0 ≤ f x := by
    rintro ⟨x, hx⟩ hxs
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    rw [hf]
    obtain ⟨k, hk, hkc⟩ := hxs
    have hkc' : ∀ t ∈ S, -k t ≤ c := by
      intro t ht; simpa [one] using hkc t ht
    rcases hk with rfl | hk
    · simpa using hkc' t0 ht0
    · by_contra hneg
      push Not at hneg
      obtain ⟨t, ht, hkt⟩ := hinf k hk (-c / 2) (by linarith)
      have := hkc' t ht
      linarith
  have dense : ∀ y : B, ∃ x : f.domain, (x : B) + y ∈ s := by
    rintro ⟨y, M, hM⟩
    refine ⟨⟨M • one, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self one)⟩, 0,
      Or.inl rfl, fun t ht => ?_⟩
    have := (abs_le.mp (hM t ht)).1
    simp [one]; linarith
  obtain ⟨g, hgf, hgs⟩ := riesz_extension s f nonneg dense
  let Λ : (X → ℝ) → ℝ := fun φ => if h : φ ∈ B then g ⟨φ, h⟩ else 0
  have hΛ : ∀ φ (h : φ ∈ B), Λ φ = g ⟨φ, h⟩ := fun φ h => dif_pos h
  refine ⟨Λ, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ ψ hφ hψ
    rw [hΛ φ hφ, hΛ ψ hψ, hΛ (φ + ψ) (B.add_mem hφ hψ), ← map_add]; rfl
  · intro r φ hφ
    rw [hΛ φ hφ, hΛ (r • φ) (B.smul_mem r hφ), ← smul_eq_mul, ← map_smul]; rfl
  · intro φ ψ hφ hψ hle
    rw [hΛ φ hφ, hΛ ψ hψ, ← sub_nonneg, ← map_sub]
    apply hgs
    refine ⟨0, Or.inl rfl, fun t ht => ?_⟩
    have := hle t ht
    simp; linarith
  · rw [hΛ _ one.2]
    have := hgf ⟨one, Submodule.mem_span_singleton_self one⟩
    rw [show (⟨fun _ => 1, one.2⟩ : B) = one from rfl, this]
    have h1 := hf 1 (by rw [one_smul]; exact Submodule.mem_span_singleton_self one)
    simpa using h1
  · intro φ hφ
    have hφB : φ ∈ B := hbdd φ hφ
    rw [hΛ φ hφB]
    have h1 := hgs (-⟨φ, hφB⟩) ⟨φ, Or.inr hφ, fun t _ => by simp⟩
    rw [map_neg] at h1
    linarith
