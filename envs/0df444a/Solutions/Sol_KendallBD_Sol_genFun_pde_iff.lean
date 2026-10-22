-- Prove2me | solution 1 for KendallBD.Sol.genFun_pde_iff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:55:57.792171+00:00
-- url     : https://prove2.me/submissions/e85bf78a-948c-4f57-a3f4-316f0f5e1000

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

set_option autoImplicit false
open Filter
open scoped Topology
open KendallBD.Sol

theorem solution (lam mu ξ η : ℝ → ℝ) (t ξ' η' : ℝ)
    (hξ : HasDerivAt ξ ξ' t) (hη : HasDerivAt η η' t) :
    (∀ z : ℝ, η t * z ≠ 1 → ∀ a b : ℝ,
      HasDerivAt (fun s => genFun (ξ s) (η s) z) a t →
      HasDerivAt (fun y => genFun (ξ t) (η t) y) b z →
      a = (z - 1) * (lam t * z - mu t) * b) ↔
    ((η t * ξ' - ξ t * η') + η' = lam t * (1 - ξ t) * (1 - η t) ∧
      ξ' = mu t * (1 - ξ t) * (1 - η t)) := by
  obtain ⟨P, hPdef⟩ : ∃ P : ℝ → ℝ, ∀ z, P z =
      ((η t * ξ' - ξ t * η' + η') - lam t * ((1 - ξ t) * (1 - η t))) * z ^ 2
      - (ξ' + (η t * ξ' - ξ t * η' + η') - (lam t + mu t) * ((1 - ξ t) * (1 - η t))) * z
      + (ξ' - mu t * ((1 - ξ t) * (1 - η t))) := ⟨_, fun _ => rfl⟩
  have key : ∀ z : ℝ, η t * z ≠ 1 → ∃ a b : ℝ,
      HasDerivAt (fun s => genFun (ξ s) (η s) z) a t ∧
      HasDerivAt (fun y => genFun (ξ t) (η t) y) b z ∧
      (a = (z - 1) * (lam t * z - mu t) * b ↔ P z = 0) := by
    intro z hz
    have hD : 1 - η t * z ≠ 0 := fun h => hz (by linarith)
    have hNum_t : HasDerivAt (fun s => ξ s + (1 - ξ s - η s) * z)
        (ξ' + (0 - ξ' - η') * z) t :=
      hξ.add ((((hasDerivAt_const t (1:ℝ)).sub hξ).sub hη).mul_const z)
    have hDen_t : HasDerivAt (fun s => 1 - η s * z) (0 - η' * z) t :=
      (hasDerivAt_const t (1:ℝ)).sub (hη.mul_const z)
    have ha := hNum_t.div hDen_t hD
    have hNum_z : HasDerivAt (fun y => ξ t + (1 - ξ t - η t) * y) (1 - ξ t - η t) z := by
      simpa using ((hasDerivAt_id z).const_mul (1 - ξ t - η t)).const_add (ξ t)
    have hDen_z : HasDerivAt (fun y => 1 - η t * y) (-η t) z := by
      simpa using ((hasDerivAt_id z).const_mul (η t)).const_sub 1
    have hb := hNum_z.div hDen_z hD
    have ha' : HasDerivAt (fun s => genFun (ξ s) (η s) z)
        (((ξ' - (ξ' + η') * z) * (1 - η t * z) +
          (ξ t + (1 - ξ t - η t) * z) * (η' * z)) / (1 - η t * z) ^ 2) t :=
      ha.congr_deriv (by field_simp; ring)
    have hb' : HasDerivAt (fun y => genFun (ξ t) (η t) y)
        (((1 - ξ t - η t) * (1 - η t * z) +
          (ξ t + (1 - ξ t - η t) * z) * η t) / (1 - η t * z) ^ 2) z :=
      hb.congr_deriv (by field_simp; ring)
    refine ⟨_, _, ha', hb', ?_⟩
    have e : ((ξ' - (ξ' + η') * z) * (1 - η t * z) +
          (ξ t + (1 - ξ t - η t) * z) * (η' * z)) / (1 - η t * z) ^ 2
        - (z - 1) * (lam t * z - mu t) * (((1 - ξ t - η t) * (1 - η t * z) +
          (ξ t + (1 - ξ t - η t) * z) * η t) / (1 - η t * z) ^ 2)
        = P z / (1 - η t * z) ^ 2 := by
      rw [hPdef]; field_simp; ring
    rw [← sub_eq_zero, e]
    exact div_eq_zero_iff.trans (or_iff_left (pow_ne_zero 2 hD))
  constructor
  · intro H
    have hP : ∀ z, η t * z ≠ 1 → P z = 0 := fun z hz => by
      obtain ⟨a, b, ha, hb, hi⟩ := key z hz
      exact hi.1 (H z hz a b ha hb)
    have h0 := hP 0 (by simp)
    rw [hPdef] at h0
    have h2 : ∃ z : ℝ, z = -1 ∨ z = 2 ∧ η t * z ≠ 1 ∧ (z = -1 ∨ z = 2) := by
      exact ⟨-1, Or.inl rfl⟩
    have hz : ∃ z : ℝ, η t * z ≠ 1 ∧ (z = -1 ∨ z = 2) := by
      by_cases h : η t * (-1) = 1
      · exact ⟨2, by intro h'; linarith, Or.inr rfl⟩
      · exact ⟨-1, h, Or.inl rfl⟩
    obtain ⟨z, hzne, hz12⟩ := hz
    have h1 := hP z hzne
    rw [hPdef] at h1
    have hA : (η t * ξ' - ξ t * η' + η') - lam t * ((1 - ξ t) * (1 - η t)) = 0 := by
      rcases hz12 with rfl | rfl <;> nlinarith [h0, h1]
    constructor
    · linarith
    · nlinarith [h0]
  · rintro ⟨h1, h2⟩ z hz a b ha hb
    obtain ⟨a0, b0, ha0, hb0, hi⟩ := key z hz
    rw [ha.unique ha0, hb.unique hb0, hi, hPdef]
    have : (η t * ξ' - ξ t * η' + η') - lam t * ((1 - ξ t) * (1 - η t)) = 0 := by
      linarith [h1]
    have h2' : ξ' - mu t * ((1 - ξ t) * (1 - η t)) = 0 := by linarith [h2]
    linear_combination (z ^ 2 - z) * this + (1 - z) * h2'
