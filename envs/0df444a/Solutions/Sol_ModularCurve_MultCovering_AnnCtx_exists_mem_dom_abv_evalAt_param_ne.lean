-- Prove2me | solution 1 for ModularCurve.MultCovering.AnnCtx.exists_mem_dom_abv_evalAt_param_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/68bc8822-f9ce-578c-b6ae-3044a8cc6d61

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringAnnuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem solution
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) p]
    {Γ : ChartCtx p A} (Δ : AnnCtx Γ) (e : Fin (mAnnuli p))
    (μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ) (hμA : ∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) :
    ∃ Q₁ ∈ (Δ.annIn e).dom, ∃ Q₂ ∈ (Δ.annIn e).dom,
      μ (Q₁.evalAt (Δ.annIn e).param) ≠ μ (Q₂.evalAt (Δ.annIn e).param) := by
  set An := Δ.annIn e with hAn
  set π : ↥A := An.modulus with hπ
  have hπ0 : ((π : ↥A) : AlgebraicClosure ℚ) ≠ 0 := Δ.modulus_ne_zero e
  have hπm : π ∈ IsLocalRing.maximalIdeal ↥A := An.modulus_mem

  have hμπ0 : 0 < μ (π : AlgebraicClosure ℚ) := μ.pos hπ0

  have key : ∀ x : AlgebraicClosure ℚ, x ≠ 0 → (μ x < 1 ↔ ∃ h : x ∈ A, (⟨x, h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) := by
    intro x hx0
    constructor
    · intro hlt
      have hxA : x ∈ A := (hμA x).mpr hlt.le
      refine ⟨hxA, ?_⟩
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      obtain ⟨u, hu⟩ := hu
      have hinvA : x⁻¹ ∈ A := by
        have h1 : (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = x⁻¹ := by
          have h3 : x * (((u⁻¹ : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) = 1 := by
            have h4 : ((u : ↥A) : AlgebraicClosure ℚ) = x := by rw [hu]
            rw [← h4, ← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
          exact eq_inv_of_mul_eq_one_right h3
        rw [← h1]; exact ((u⁻¹ : (↥A)ˣ) : ↥A).2
      have h2 : μ x⁻¹ ≤ 1 := (hμA _).mp hinvA
      rw [map_inv₀] at h2
      have : 1 < (μ x)⁻¹ := one_lt_inv_iff₀.mpr ⟨μ.pos hx0, hlt⟩
      linarith
    · rintro ⟨hxA, hxm⟩
      by_contra hge
      push_neg at hge
      have hle : μ x ≤ 1 := (hμA x).mp hxA
      have heq : μ x = 1 := le_antisymm hle hge
      have hinvA : x⁻¹ ∈ A := (hμA _).mpr (by rw [map_inv₀, heq, inv_one])
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hxm
      apply hxm
      exact ⟨⟨⟨x, hxA⟩, ⟨x⁻¹, hinvA⟩, Subtype.ext (mul_inv_cancel₀ hx0), Subtype.ext (inv_mul_cancel₀ hx0)⟩, rfl⟩
  have hμπ1 : μ (π : AlgebraicClosure ℚ) < 1 := (key _ hπ0).mpr ⟨π.2, by simpa using hπm⟩

  obtain ⟨c₁, hc₁⟩ := IsAlgClosed.exists_pow_nat_eq ((π : ↥A) : AlgebraicClosure ℚ) (by norm_num : 0 < 2)
  obtain ⟨c₂, hc₂⟩ := IsAlgClosed.exists_pow_nat_eq ((π : ↥A) : AlgebraicClosure ℚ) (by norm_num : 0 < 3)
  have hc₁0 : c₁ ≠ 0 := by intro h; apply hπ0; rw [← hc₁, h, zero_pow two_ne_zero]
  have hc₂0 : c₂ ≠ 0 := by intro h; apply hπ0; rw [← hc₂, h, zero_pow three_ne_zero]
  have hμ₁ : μ c₁ ^ 2 = μ (π : AlgebraicClosure ℚ) := by rw [← map_pow, hc₁]
  have hμ₂ : μ c₂ ^ 3 = μ (π : AlgebraicClosure ℚ) := by rw [← map_pow, hc₂]
  have hμc₁ : μ c₁ < 1 := by
    by_contra h; push_neg at h
    have : (1 : ℝ) ≤ μ c₁ ^ 2 := one_le_pow₀ h
    linarith
  have hμc₂ : μ c₂ < 1 := by
    by_contra h; push_neg at h
    have : (1 : ℝ) ≤ μ c₂ ^ 3 := one_le_pow₀ h
    linarith
  obtain ⟨hc₁A, hc₁m⟩ := (key c₁ hc₁0).mp hμc₁
  obtain ⟨hc₂A, hc₂m⟩ := (key c₂ hc₂0).mp hμc₂

  have hadm₁ : ∃ m ∈ IsLocalRing.maximalIdeal ↥A, ((π : ↥A) : AlgebraicClosure ℚ) = ((⟨c₁, hc₁A⟩ : ↥A) : AlgebraicClosure ℚ) * m :=
    ⟨⟨c₁, hc₁A⟩, hc₁m, by rw [← hc₁]; simp [pow_two]⟩
  have hadm₂ : ∃ m ∈ IsLocalRing.maximalIdeal ↥A, ((π : ↥A) : AlgebraicClosure ℚ) = ((⟨c₂, hc₂A⟩ : ↥A) : AlgebraicClosure ℚ) * m :=
    ⟨⟨c₂, hc₂A⟩ * ⟨c₂, hc₂A⟩, Ideal.mul_mem_left _ _ hc₂m, by rw [← hc₂]; simp [pow_succ, mul_assoc]⟩
  obtain ⟨Q₁, ⟨hQ₁, hQ₁v⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₁, hc₁A⟩ hc₁m hc₁0 hadm₁
  obtain ⟨Q₂, ⟨hQ₂, hQ₂v⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c₂, hc₂A⟩ hc₂m hc₂0 hadm₂
  refine ⟨Q₁, hQ₁, Q₂, hQ₂, ?_⟩
  rw [hQ₁v, hQ₂v]
  show μ c₁ ≠ μ c₂
  intro heq

  have t2 : μ c₁ ^ 2 = μ c₁ ^ 3 := by rw [hμ₁, heq, hμ₂]
  have ht0 : 0 < μ c₁ := μ.pos hc₁0
  have : μ c₁ ^ 2 * (1 - μ c₁) = 0 := by ring_nf; linarith [t2]
  rcases mul_eq_zero.mp this with h | h
  · exact (pow_ne_zero 2 ht0.ne') h
  · have : μ c₁ = 1 := by linarith
    exact (lt_irrefl (1:ℝ)) (this ▸ hμc₁)

end S_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne
end P2MW
export P2MW.S_ModularCurve_MultCovering_AnnCtx_exists_mem_dom_abv_evalAt_param_ne (solution)
