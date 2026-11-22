-- Prove2me | solution 1 for MasulloGRH.expDecayStage_weighted_mem
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T19:10:49.980753+00:00
-- url     : https://prove2.me/submissions/997b7792-95d5-48e8-be13-b63741125172

import Theorems.Thm_MasulloGRH_schwartzBruhat_descent_goodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_isCompact_moduleKernel_and_compact_le
import Definitions.Def_MasulloGRH_ExpDecayStages

set_option autoImplicit false

universe u

namespace MasulloGRHWMemAux

open MasulloGRH

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

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

end MasulloGRHWMemAux

open MasulloGRH MasulloGRHWMemAux in
theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) (k : Subgroup G) (hk : IsGoodSubgroup k)
    (y : ExpDecayStage G m I k) (a : ℝ) (ha : a ∈ I) :
    (fun x : G ⧸ k => ((m x.out ^ a : ℝ) : ℂ) * y.1.toFun x.out) ∈
      schwartzBruhatSubmodule (G ⧸ k) := by
  have hm1 : ∀ h ∈ k, m h = 1 := by
    intro h hh
    exact (isCompact_moduleKernel_and_compact_le G m hm (modKer hm.1) (fun g => Iff.rfl)).2
      k (isCompact_of_isGoodSubgroup G k hk) hh
  -- `|·|^a y ∈ S(G)`
  have hS : (fun g => ((m g ^ a : ℝ) : ℂ) * y.1.toFun g) ∈ schwartzBruhatSubmodule G := by
    have key : ∀ φ ∈ expDecaySubmodule G m I,
        (fun g => ((m g ^ a : ℝ) : ℂ) * φ g) ∈ schwartzBruhatSubmodule G := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem φ hφ => exact hφ.2 a ha
      | zero =>
        have : (fun g => ((m g ^ a : ℝ) : ℂ) * (0 : G → ℂ) g) = 0 := by funext g; simp
        rw [this]; exact Submodule.zero_mem _
      | add φ ψ _ _ h₁ h₂ =>
        have : (fun g => ((m g ^ a : ℝ) : ℂ) * (φ + ψ) g) =
            (fun g => ((m g ^ a : ℝ) : ℂ) * φ g) + (fun g => ((m g ^ a : ℝ) : ℂ) * ψ g) := by
          funext g; simp [mul_add]
        rw [this]; exact Submodule.add_mem _ h₁ h₂
      | smul c φ _ h =>
        have : (fun g => ((m g ^ a : ℝ) : ℂ) * (c • φ) g) =
            c • (fun g => ((m g ^ a : ℝ) : ℂ) * φ g) := by
          funext g; simp; ring
        rw [this]; exact Submodule.smul_mem _ c h
    exact key y.1.1 y.1.2
  have hinv : ∀ h ∈ k, ∀ g, ((m (g * h) ^ a : ℝ) : ℂ) * y.1.toFun (g * h) =
      ((m g ^ a : ℝ) : ℂ) * y.1.toFun g := by
    intro h hh g
    rw [hm.1.map_mul, hm1 h hh, mul_one, y.2 h hh g]
  exact schwartzBruhat_descent_goodSubgroup G k hk _ hS hinv
