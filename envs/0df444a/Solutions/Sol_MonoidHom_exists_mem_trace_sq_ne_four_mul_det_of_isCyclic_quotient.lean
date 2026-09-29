-- Prove2me | solution 1 for MonoidHom.exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/e5859abd-e905-58d6-8a4e-b629758b4df0

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient

namespace TWCliffordSeed

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

local notation "M₂" => Matrix (Fin 2) (Fin 2) 𝕜

theorem mul_self_eq (M : M₂) : M * M = M.trace • M - M.det • (1 : M₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem trace_mul_self (M : M₂) : (M * M).trace = M.trace ^ 2 - 2 * M.det := by
  rw [mul_self_eq, trace_sub, trace_smul, trace_smul, trace_one, smul_eq_mul, smul_eq_mul]
  simp
  ring

theorem trace_mul_self_mul (A B : M₂) :
    (A * A * B).trace = A.trace * (A * B).trace - A.det * B.trace := by
  rw [mul_self_eq, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, trace_sub, trace_smul,
    trace_smul, smul_eq_mul, smul_eq_mul]

theorem two_mul_eq_of_discs {t₁ t₂ d₁ d₂ T : 𝕜} (h2 : (2 : 𝕜) ≠ 0)
    (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0)
    (h₁ : t₁ ^ 2 = 4 * d₁) (h₂ : t₂ ^ 2 = 4 * d₂)
    (h₃ : T ^ 2 = 4 * (d₁ * d₂))
    (h₄ : (t₁ * T - d₁ * t₂) ^ 2 = 4 * (d₁ * d₁ * d₂)) :
    2 * T = t₁ * t₂ := by
  have h4 : (4 : 𝕜) ≠ 0 := by
    have : (4 : 𝕜) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  have ht₁ : t₁ ≠ 0 := by
    rintro rfl
    apply hd₁
    have : (4 : 𝕜) * d₁ = 0 := by rw [← h₁]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h4
    · exact h
  have ht₂ : t₂ ≠ 0 := by
    rintro rfl
    apply hd₂
    have : (4 : 𝕜) * d₂ = 0 := by rw [← h₂]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h4
    · exact h
  have hA : (2 * T - t₁ * t₂) * (2 * T + t₁ * t₂) = 0 := by
    linear_combination 4 * h₃ - t₂ ^ 2 * h₁ - 4 * d₁ * h₂
  have hB : t₁ ^ 2 * (T * (2 * T - t₁ * t₂)) = 0 := by
    linear_combination 2 * h₄ - t₁ * t₂ * T * h₁ - 2 * d₁ ^ 2 * h₂
  have hB' : T * (2 * T - t₁ * t₂) = 0 := by
    rcases mul_eq_zero.mp hB with h | h
    · exact absurd (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h) ht₁
    · exact h
  by_contra hne
  have hne' : 2 * T - t₁ * t₂ ≠ 0 := sub_ne_zero.mpr hne
  have hT : T = 0 := by
    rcases mul_eq_zero.mp hB' with h | h
    · exact h
    · exact absurd h hne'
  have hsum : 2 * T + t₁ * t₂ = 0 := by
    rcases mul_eq_zero.mp hA with h | h
    · exact absurd h hne'
    · exact h
  rw [hT, mul_zero, zero_add] at hsum
  rcases mul_eq_zero.mp hsum with h | h
  · exact ht₁ h
  · exact ht₂ h

theorem nilPart_mul_self (h2 : (2 : 𝕜) ≠ 0) (M : M₂) (hdisc : M.trace ^ 2 = 4 * M.det) :
    (M - (M.trace / 2) • (1 : M₂)) * (M - (M.trace / 2) • (1 : M₂)) = 0 := by
  set l := M.trace / 2 with hl
  have ht : M.trace = 2 * l := by rw [hl]; field_simp
  have hd : M.det = l * l := by
    have h4 : (4 : 𝕜) ≠ 0 := by
      have : (4 : 𝕜) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero h2 h2
    apply mul_left_cancel₀ h4
    rw [← hdisc, ht]; ring
  have hM : M * M = (2 * l) • M - (l * l) • (1 : M₂) := by rw [mul_self_eq, ht, hd]
  rw [sub_mul, mul_sub, mul_sub, hM]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
  module

theorem trace_nilPart (h2 : (2 : 𝕜) ≠ 0) (M : M₂) :
    (M - (M.trace / 2) • (1 : M₂)).trace = 0 := by
  rw [trace_sub, trace_smul, trace_one, smul_eq_mul]
  simp
  field_simp
  ring

theorem det_eq_zero_of_mul_self_eq_zero (n : M₂) (hn : n * n = 0) : n.det = 0 := by
  have : n.det * n.det = 0 := by rw [← det_mul, hn, det_zero]
  exact mul_self_eq_zero.mp this

theorem trace_eq_zero_of_trace_mul_self (Y : M₂) (hdet : Y.det = 0) (htr : (Y * Y).trace = 0) :
    Y.trace = 0 := by
  rw [trace_mul_self, hdet, mul_zero, sub_zero] at htr
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp htr

variable {G : Type*} [Group G]

theorem map_mul_map_inv (ρ : G →* M₂) (g : G) : ρ g * ρ g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem map_inv_mul_map (ρ : G →* M₂) (g : G) : ρ g⁻¹ * ρ g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem det_map_ne_zero (ρ : G →* M₂) (g : G) : (ρ g).det ≠ 0 := by
  intro h
  have : (ρ g * ρ g⁻¹).det = 1 := by rw [map_mul_map_inv, det_one]
  rw [det_mul, h, zero_mul] at this
  exact zero_ne_one this

def unitOf (ρ : G →* M₂) (g : G) : (M₂)ˣ :=
  ⟨ρ g, ρ g⁻¹, map_mul_map_inv ρ g, map_inv_mul_map ρ g⟩

theorem commute_map_inv (ρ : G →* M₂) {g : G} {Y : M₂} (h : Commute (ρ g) Y) :
    Commute (ρ g⁻¹) Y := by
  have := Commute.units_inv_left (u := unitOf ρ g) h
  exact this

def commSubgroup (ρ : G →* M₂) (Y : M₂) : Subgroup G where
  carrier := {g | Commute (ρ g) Y}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact Commute.one_left Y
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_mul] at *
    exact Commute.mul_left ha hb
  inv_mem' := by
    intro a ha
    exact commute_map_inv ρ ha

def traceOrth (n : M₂) : Submodule 𝕜 M₂ where
  carrier := {X | (X * n).trace = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [add_mul, trace_add, ha, hb, add_zero]
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq] at *
    rw [smul_mul_assoc, trace_smul, hx, smul_zero]

theorem exists_mem_trace_sq_ne (h2 : (2 : 𝕜) ≠ 0) (ρ : G →* M₂)
    (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    ∃ σ ∈ N, (ρ σ).trace ^ 2 ≠ 4 * (ρ σ).det := by
  by_contra hcon
  push Not at hcon

  have hall : ∀ (W : Submodule 𝕜 M₂), (∀ g, ρ g ∈ W) → ∀ X : M₂, X ∈ W := by
    intro W hW X
    have hle : Submodule.span 𝕜 (Set.range ρ) ≤ W := Submodule.span_le.mpr (by
      rintro _ ⟨g, rfl⟩; exact hW g)
    rw [hρ] at hle
    exact hle Submodule.mem_top
  by_cases hsc : ∀ σ ∈ N, ∃ c : 𝕜, ρ σ = c • (1 : M₂)
  ·

    obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := G ⧸ N)
    obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x

    obtain ⟨Y, hYns, hYc⟩ : ∃ Y : M₂, Y ∉ Set.range (Matrix.scalar (Fin 2)) ∧ Commute (ρ g₀) Y := by
      by_cases h : ρ g₀ ∈ Set.range (Matrix.scalar (Fin 2))
      · obtain ⟨c, hc⟩ := h
        refine ⟨Matrix.single 0 1 1, ?_, ?_⟩
        · rintro ⟨c', hc'⟩
          have := congrFun (congrFun hc' 0) 1
          simp at this
        · rw [← hc]
          exact Matrix.scalar_commute c (fun r' => Commute.all c r') _
      · exact ⟨ρ g₀, h, Commute.refl _⟩

    have hcomm : ∀ g : G, Commute (ρ g) Y := by
      intro g
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx (g : G ⧸ N))
      have hmem : (g₀ ^ k)⁻¹ * g ∈ N := by
        rw [← QuotientGroup.eq, QuotientGroup.mk_zpow]
        exact hk
      have hg : g = g₀ ^ k * ((g₀ ^ k)⁻¹ * g) := by group
      have h1 : g₀ ∈ commSubgroup ρ Y := hYc
      have h2' : (g₀ ^ k)⁻¹ * g ∈ commSubgroup ρ Y := by
        obtain ⟨c, hc⟩ := hsc _ hmem
        show Commute (ρ ((g₀ ^ k)⁻¹ * g)) Y
        rw [hc]
        exact (Commute.one_left Y).smul_left c
      have : g ∈ commSubgroup ρ Y := by
        rw [hg]
        exact (commSubgroup ρ Y).mul_mem ((commSubgroup ρ Y).zpow_mem h1 k) h2'
      exact this

    have hallc : ∀ X : M₂, Commute X Y := by
      intro X
      have := hall (Subalgebra.toSubmodule (Subalgebra.centralizer 𝕜 ({Y} : Set M₂)))
        (fun g => by
          rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
          intro y hy
          rw [Set.mem_singleton_iff] at hy
          subst hy
          exact (hcomm g).symm.eq) X
      rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at this
      exact (Commute.symm (this Y (Set.mem_singleton Y)) : Commute X Y)
    exact hYns (Matrix.mem_range_scalar_of_commute_single (fun i j _ => hallc _))
  ·

    push Not at hsc
    obtain ⟨σ₀, hσ₀N, hσ₀⟩ := hsc

    have hP : ∀ σ ∈ N, ∀ τ ∈ N,
        2 * (ρ σ * ρ τ).trace = (ρ σ).trace * (ρ τ).trace := by
      intro σ hσ τ hτ
      have h₃ := hcon (σ * τ) (N.mul_mem hσ hτ)
      have h₄ := hcon (σ * σ * τ) (N.mul_mem (N.mul_mem hσ hσ) hτ)
      rw [map_mul, det_mul] at h₃
      rw [map_mul, map_mul, det_mul, det_mul, trace_mul_self_mul] at h₄
      exact two_mul_eq_of_discs h2 (det_map_ne_zero ρ σ) (det_map_ne_zero ρ τ)
        (hcon σ hσ) (hcon τ hτ) h₃ h₄
    set M₀ := ρ σ₀ with hM₀def
    set l := M₀.trace / 2 with hl
    set n₀ : M₂ := M₀ - l • (1 : M₂) with hn₀
    have hM₀ : M₀ = l • (1 : M₂) + n₀ := by rw [hn₀]; abel
    have ht₀ : M₀.trace = 2 * l := by rw [hl]; field_simp
    have hn₀sq : n₀ * n₀ = 0 := nilPart_mul_self h2 M₀ (hcon σ₀ hσ₀N)
    have hn₀tr : n₀.trace = 0 := trace_nilPart h2 M₀
    have hn₀ne : n₀ ≠ 0 := by
      intro h
      apply hσ₀ l
      rw [← sub_eq_zero]
      exact h
    clear_value n₀ l M₀

    have hkey : ∀ g : G, (ρ g * n₀).trace = 0 := by
      intro g
      set m := ρ g with hm
      set m' := ρ g⁻¹ with hm'
      have hmm' : m * m' = 1 := map_mul_map_inv ρ g
      have hm'm : m' * m = 1 := map_inv_mul_map ρ g
      clear_value m m'

      have hconj : g * σ₀ * g⁻¹ ∈ N := Subgroup.Normal.conj_mem inferInstance σ₀ hσ₀N g
      have hPc := hP _ hconj σ₀ hσ₀N
      have hρc : ρ (g * σ₀ * g⁻¹) = m * M₀ * m' := by rw [map_mul, map_mul, ← hM₀def, hm, hm']
      have htrc : (ρ (g * σ₀ * g⁻¹)).trace = M₀.trace := by
        rw [hρc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, hm'm, mul_one]
      rw [htrc, hρc, ← hM₀def] at hPc

      have hexp : m * M₀ * m' * M₀ =
          (l * l) • (m * m') + l • (m * m' * n₀) + l • (m * n₀ * m') + m * n₀ * m' * n₀ := by
        rw [hM₀]
        simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, smul_add, smul_smul]
        abel
      have htr1 : (m * m' * n₀).trace = 0 := by rw [hmm', one_mul, hn₀tr]
      have htr2 : (m * n₀ * m').trace = 0 := by
        rw [trace_mul_comm, ← Matrix.mul_assoc, hm'm, one_mul, hn₀tr]
      have htr3 : (m * n₀ * m' * n₀).trace = 0 := by
        have h := hPc
        rw [hexp, trace_add, trace_add, trace_add, trace_smul, trace_smul, trace_smul, htr1, htr2,
          hmm', trace_one, ht₀] at h
        simp at h

        have h' : (2 : 𝕜) * (m * n₀ * m' * n₀).trace = 0 := by linear_combination h
        rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' h2
        · exact h''

      have hadj : m.det • m' = m.trace • (1 : M₂) - m := by
        have h1 : m * (m.trace • (1 : M₂) - m) = m.det • (1 : M₂) := by
          rw [mul_sub, mul_smul_comm, mul_one, mul_self_eq]; abel
        calc m.det • m' = m' * (m.det • (1 : M₂)) := by rw [mul_smul_comm, mul_one]
          _ = m' * (m * (m.trace • (1 : M₂) - m)) := by rw [h1]
          _ = m.trace • (1 : M₂) - m := by rw [← Matrix.mul_assoc, hm'm, one_mul]
      have hsq : ((m * n₀) * (m * n₀)).trace = 0 := by
        have : m.det • (m * n₀ * m' * n₀) = - ((m * n₀) * (m * n₀)) := by
          calc m.det • (m * n₀ * m' * n₀) = m * n₀ * (m.det • m') * n₀ := by
                rw [mul_smul_comm, smul_mul_assoc]
            _ = m * n₀ * (m.trace • (1 : M₂) - m) * n₀ := by rw [hadj]
            _ = m.trace • (m * (n₀ * n₀)) - (m * n₀) * (m * n₀) := by
                rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc]
                simp only [Matrix.mul_assoc]
            _ = - ((m * n₀) * (m * n₀)) := by rw [hn₀sq, Matrix.mul_zero, smul_zero, zero_sub]
        have h := congrArg Matrix.trace this
        rw [trace_smul, htr3, smul_zero, trace_neg] at h
        exact neg_eq_zero.mp h.symm
      have hdet : (m * n₀).det = 0 := by
        rw [det_mul, det_eq_zero_of_mul_self_eq_zero n₀ hn₀sq, mul_zero]
      exact trace_eq_zero_of_trace_mul_self (m * n₀) hdet hsq

    have hallX : ∀ X : M₂, (X * n₀).trace = 0 := fun X => hall (traceOrth n₀) hkey X
    apply hn₀ne
    ext i j
    have := hallX (Matrix.single j i 1)
    rw [trace_single_mul, one_smul] at this
    simpa using this

end TWCliffordSeed

theorem solution
    {G : Type*} [Group G] {𝕜 : Type*} [Field 𝕜] (h2 : (2 : 𝕜) ≠ 0)
    (ρ : G →* Matrix (Fin 2) (Fin 2) 𝕜)
    (hρ : Submodule.span 𝕜 (Set.range ρ) = ⊤)
    (N : Subgroup G) [N.Normal] [IsCyclic (G ⧸ N)] :
    ∃ σ ∈ N, (ρ σ).trace ^ 2 ≠ 4 * (ρ σ).det :=
  TWCliffordSeed.exists_mem_trace_sq_ne h2 ρ hρ N

end S_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient
end P2MW
export P2MW.S_MonoidHom_exists_mem_trace_sq_ne_four_mul_det_of_isCyclic_quotient (solution)
