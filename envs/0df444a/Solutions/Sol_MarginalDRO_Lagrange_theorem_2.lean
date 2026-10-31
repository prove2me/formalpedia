-- Prove2me | solution 1 for MarginalDRO.Lagrange.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T09:52:35.629733+00:00
-- url     : https://prove2.me/submissions/aa44ecea-ed6f-4e55-ad96-ab5871795560

import Mathlib
import Definitions.Def_MarginalDRO_Lagrange_Model
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_kantorovich
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_lower
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_upper
import Theorems.Thm_MarginalDRO_Lagrange_sec_3_1_measurable_selection
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_minimax
import Theorems.Thm_MarginalDRO_Lagrange_proof_thm2_dual_attained

open MeasureTheory ProbabilityTheory
open MarginalDRO.Lagrange

theorem solution {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hvar : ∀ i, MemLp id 2 (μ i)) (𝒳 : Finset (Fin n → ℝ)) (h𝒳 : 𝒳.Nonempty) :
    ∃ v : ℝ,
      IsGreatest {s | ∃ θ ∈ frechetClass μ, s = ∫ c, Z 𝒳 h𝒳 c ∂θ} v ∧
      (∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i, ∃ m : ℝ,
        IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} m) ∧
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳, ∃ γ : Fin n → Measure (ℝ × ℝ),
        (∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) ∧ s = ∑ i, ∫ p, p.1 * p.2 ∂(γ i)} v ∧
      IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳,
        IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) s} v ∧
      IsLeast {s | ∃ ψ : Fin n → ℝ → ℝ,
        IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s} v := by
  classical
  obtain ⟨v, hv4, hvglb⟩ := proof_thm2_minimax μ hvar 𝒳 h𝒳
  obtain ⟨ψs, s, hsLUB, hsmin⟩ := proof_thm2_dual_attained μ hvar 𝒳 h𝒳
  have hleast : IsLeast {s | ∃ ψ : Fin n → ℝ → ℝ,
      IsLUB ((fun ν => lagrangian μ 𝒳 h𝒳 ψ ν) '' stdSimplex ℝ 𝒳) s} s :=
    ⟨⟨ψs, hsLUB⟩, fun s' ⟨ψ, h⟩ => hsmin ψ s' h⟩
  have hsv : s = v := hleast.isGLB.unique hvglb
  subst hsv
  -- coupling values
  set cv : (𝒳 → ℝ) → Fin n → ℝ := fun ν i => couplingValue (μ i) (margMeasure 𝒳 ν i) with hcv
  have hK : ∀ ν ∈ stdSimplex ℝ 𝒳, ∀ i,
      IsGreatest {s | ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν i), s = ∫ p, p.1 * p.2 ∂γ} (cv ν i) ∧
      IsGLB (Set.range fun ψ : ℝ → ℝ =>
        ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i)) (cv ν i) := by
    intro ν hν i
    obtain ⟨m, h1, _, h3⟩ := proof_thm2_kantorovich μ hvar 𝒳 h𝒳 ν hν i
    have : cv ν i = m := h1.csSup_eq
    rw [this]; exact ⟨h1, h3⟩
  -- the GLB of the Lagrangian is the sum of coupling values
  have hL : ∀ ν ∈ stdSimplex ℝ 𝒳,
      IsGLB (Set.range fun ψ : Fin n → ℝ → ℝ => lagrangian μ 𝒳 h𝒳 ψ ν) (∑ i, cv ν i) := by
    intro ν hν
    set f : Fin n → (ℝ → ℝ) → ℝ := fun i ψ =>
      ∑ x : 𝒳, ν x * ψ ((x : Fin n → ℝ) i) + ∫ c, conj 𝒳 h𝒳 ψ i c ∂(μ i) with hf
    have hLf : ∀ ψ : Fin n → ℝ → ℝ, lagrangian μ 𝒳 h𝒳 ψ ν = ∑ i, f i (ψ i) := fun ψ => rfl
    constructor
    · rintro _ ⟨ψ, rfl⟩
      simp only [hLf]
      exact Finset.sum_le_sum fun i _ => (hK ν hν i).2.1 ⟨ψ i, rfl⟩
    · intro b hb
      by_contra hcon'
      have hcon : ∑ i, cv ν i < b := not_le.mp hcon'
      set ε := (b - ∑ i, cv ν i) / (n + 1) with hε
      have hεpos : 0 < ε := div_pos (by linarith) (by positivity)
      have hex : ∀ i, ∃ ψi : ℝ → ℝ, f i ψi < cv ν i + ε := by
        intro i
        obtain ⟨_, ⟨ψi, rfl⟩, h⟩ := ((hK ν hν i).2).exists_between (by linarith : cv ν i < cv ν i + ε)
        exact ⟨ψi, h.2⟩
      choose ψ hψ using hex
      have h1 := hb ⟨ψ, rfl⟩
      simp only [hLf] at h1
      have h2 : ∑ i, f i (ψ i) ≤ ∑ i, (cv ν i + ε) := Finset.sum_le_sum fun i _ => (hψ i).le
      have h2' : ∑ i, (cv ν i + ε) = ∑ i, cv ν i + n * ε := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
      have h3 : (n : ℝ) * ε < b - ∑ i, cv ν i := by
        rw [hε, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
  -- v is the max of ν ↦ ∑ cv ν
  obtain ⟨⟨ν0, hν0, hν0glb⟩, hvub⟩ := hv4
  have hv0 : ∑ i, cv ν0 i = s := (hL ν0 hν0).unique hν0glb
  have hle : ∀ ν ∈ stdSimplex ℝ 𝒳, ∑ i, cv ν i ≤ s := fun ν hν => hvub ⟨ν, hν, hL ν hν⟩
  have h3 : IsGreatest {s | ∃ ν ∈ stdSimplex ℝ 𝒳, ∃ γ : Fin n → Measure (ℝ × ℝ),
      (∀ i, γ i ∈ couplings (μ i) (margMeasure 𝒳 ν i)) ∧ s = ∑ i, ∫ p, p.1 * p.2 ∂(γ i)} s := by
    constructor
    · have hex : ∀ i, ∃ γ ∈ couplings (μ i) (margMeasure 𝒳 ν0 i),
          cv ν0 i = ∫ p, p.1 * p.2 ∂γ := fun i => (hK ν0 hν0 i).1.1
      choose γ hγ hγv using hex
      exact ⟨ν0, hν0, γ, hγ, by rw [← hv0]; exact Finset.sum_congr rfl fun i _ => hγv i⟩
    · rintro _ ⟨ν, hν, γ, hγ, rfl⟩
      refine le_trans (Finset.sum_le_sum fun i _ => (hK ν hν i).1.2 ⟨γ i, hγ i, rfl⟩) (hle ν hν)
  refine ⟨s, ?_, fun ν hν i => ⟨_, (hK ν hν i).1⟩, h3, ⟨⟨ν0, hν0, hν0glb⟩, hvub⟩, hleast⟩
  -- (1)
  have hub1 : ∀ θ ∈ frechetClass μ, ∫ c, Z 𝒳 h𝒳 c ∂θ ≤ s := by
    intro θ hθ
    obtain ⟨xs, hxm, hxs⟩ := sec_3_1_measurable_selection 𝒳 h𝒳
    obtain ⟨hνs, hγs, heq⟩ := proof_thm2_upper μ hvar 𝒳 h𝒳 θ hθ xs hxm (fun c => (hxs c).1)
      (fun c => (hxs c).2)
    rw [heq]
    exact h3.2 ⟨_, hνs, _, hγs, rfl⟩
  constructor
  · obtain ⟨ν, hν, γ, hγ, hsv⟩ := h3.1
    obtain ⟨θ, hθ, hθle⟩ := proof_thm2_lower μ hvar 𝒳 h𝒳 ν hν γ hγ
    exact ⟨θ, hθ, le_antisymm (hsv ▸ hθle) (hub1 θ hθ)⟩
  · rintro _ ⟨θ, hθ, rfl⟩; exact hub1 θ hθ
