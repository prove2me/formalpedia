-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartz_exists_good_invariant
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:24:50.188405+00:00
-- url     : https://prove2.me/submissions/0bc071ab-2721-4185-ab1a-fbdd67cb7232

import Theorems.Thm_MasulloGRH_expDecay_exists_cofinal_goodSubgroups
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le

set_option autoImplicit false

universe u

namespace MasulloGRHGoodInvAux

open MasulloGRH

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma extendPullback_mul {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemGroup m n r s d → ℂ) (x y : G) (hy : y ∈ k) :
    extendPullback Γ π g (x * y) = extendPullback Γ π g x := by
  have hyΓ : y ∈ Γ := hs.2.2.2 hy
  unfold extendPullback
  by_cases hx : x ∈ Γ
  · have hxy : x * y ∈ Γ := Γ.mul_mem hx hyΓ
    rw [dif_pos hxy, dif_pos hx]
    have h1 : π ⟨y, hyΓ⟩ = 1 := (hπ.2.2.2.2 ⟨y, hyΓ⟩).2 hy
    have : (⟨x * y, hxy⟩ : Γ) = ⟨x, hx⟩ * ⟨y, hyΓ⟩ := rfl
    rw [this, map_mul, h1, mul_one]
  · have hxy : x * y ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem hyΓ))
    rw [dif_neg hxy, dif_neg hx]

/-- the kernel of a module as a subgroup -/
def modKer {m : G → ℝ} (hm : IsModule m) : Subgroup G where
  carrier := {g | m g = 1}
  one_mem' := by
    show m 1 = 1
    have h := hm.map_mul 1 1
    rw [mul_one] at h
    have hp := hm.pos 1
    nlinarith
  mul_mem' {a b} ha hb := by
    show m (a * b) = 1
    rw [hm.map_mul, show m a = 1 from ha, show m b = 1 from hb, one_mul]
  inv_mem' {a} ha := by
    show m a⁻¹ = 1
    have h := hm.map_mul a a⁻¹
    rw [mul_inv_cancel, show m a = 1 from ha, one_mul] at h
    have h1 := hm.map_mul 1 1
    rw [mul_one] at h1
    have hp := hm.pos 1
    have : m 1 = 1 := by nlinarith
    rw [← h, this]

end MasulloGRHGoodInvAux

open MasulloGRH MasulloGRHGoodInvAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (ϕ : ExpDecaySchwartz G m I) :
    ∃ k : Subgroup G, IsGoodSubgroup k ∧ ϕ ∈ expDecayInvSubmodule G m I k := by
  obtain ⟨k, hkg, hka, hkc⟩ := expDecay_exists_cofinal_goodSubgroups G m hm
  -- the module is trivial on each `k N`
  have hmk : ∀ N, ∀ h ∈ k N, m h = 1 := by
    intro N h hh
    have := (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2
      (k N) (isCompact_of_isGoodSubgroup G (k N) (hkg N)) hh
    exact this
  -- Schwartz–Bruhat functions are invariant under some `k N`
  have hSB : ∀ F ∈ schwartzBruhatSubmodule G, ∃ N, ∀ h ∈ k N, ∀ g, F (g * h) = F g := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF =>
      obtain ⟨Γ, k', m', n', r', s', d', π, g, hs, hπ, rfl⟩ := hF
      obtain ⟨N, hN⟩ := hkc k' hs.2.2.1
      exact ⟨N, fun h hh x => extendPullback_mul Γ k' π hs hπ g.toFun x h (hN hh)⟩
    | zero => exact ⟨0, fun _ _ _ => rfl⟩
    | add F₁ F₂ _ _ h₁ h₂ =>
      obtain ⟨N₁, hN₁⟩ := h₁
      obtain ⟨N₂, hN₂⟩ := h₂
      refine ⟨max N₁ N₂, fun h hh x => ?_⟩
      simp only [Pi.add_apply]
      rw [hN₁ h (hka (le_max_left _ _) hh), hN₂ h (hka (le_max_right _ _) hh)]
    | smul c F _ h₁ =>
      obtain ⟨N, hN⟩ := h₁
      exact ⟨N, fun h hh x => by simp only [Pi.smul_apply, hN h hh x]⟩
  obtain ⟨a, ha⟩ := hne
  have hE : ∀ f ∈ expDecaySubmodule G m I, ∃ N, ∀ h ∈ k N, ∀ g, f (g * h) = f g := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨-, hf⟩ := hf
      obtain ⟨N, hN⟩ := hSB _ (hf a ha)
      refine ⟨N, fun h hh x => ?_⟩
      have h1 := hN h hh x
      simp only [hm.1.map_mul, hmk N h hh, mul_one] at h1
      have hpos : ((m x ^ a : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (Real.rpow_pos_of_pos (hm.1.pos x) a).ne'
      exact mul_left_cancel₀ hpos h1
    | zero => exact ⟨0, fun _ _ _ => rfl⟩
    | add F₁ F₂ _ _ h₁ h₂ =>
      obtain ⟨N₁, hN₁⟩ := h₁
      obtain ⟨N₂, hN₂⟩ := h₂
      refine ⟨max N₁ N₂, fun h hh x => ?_⟩
      simp only [Pi.add_apply]
      rw [hN₁ h (hka (le_max_left _ _) hh), hN₂ h (hka (le_max_right _ _) hh)]
    | smul c F _ h₁ =>
      obtain ⟨N, hN⟩ := h₁
      exact ⟨N, fun h hh x => by simp only [Pi.smul_apply, hN h hh x]⟩
  obtain ⟨N, hN⟩ := hE ϕ.1 ϕ.2
  exact ⟨k N, hkg N, fun h hh g => hN h hh g⟩
