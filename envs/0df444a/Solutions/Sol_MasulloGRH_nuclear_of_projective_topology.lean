-- Prove2me | solution 1 for MasulloGRH.nuclear_of_projective_topology
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:38:38.996211+00:00
-- url     : https://prove2.me/submissions/467d4670-f2bd-470f-93bd-d61c894a63e2

import Theorems.Thm_MasulloGRH_nuclear_pi
import Theorems.Thm_MasulloGRH_nuclear_subspace
import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv

set_option autoImplicit false

open MasulloGRH

universe u

theorem solution (ι : Type u) (Y : ι → Type u)
    [∀ i, AddCommGroup (Y i)] [∀ i, Module ℂ (Y i)] [∀ i, TopologicalSpace (Y i)]
    (hY : ∀ i, IsNuclear (Y i))
    (E : Type u) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (π : ∀ i, E →ₗ[ℂ] Y i)
    (htop : ‹TopologicalSpace E› = ⨅ i, TopologicalSpace.induced (π i) inferInstance)
    (hsep : ∀ x : E, (∀ i, π i x = 0) → x = 0) :
    IsNuclear E := by
  -- the canonical map into the product
  let Φ : E →ₗ[ℂ] (∀ i, Y i) := LinearMap.pi π
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact hsep x fun i => congrFun hx i
  -- `E` carries the topology induced by `Φ`
  have hind : ‹TopologicalSpace E› = TopologicalSpace.induced Φ inferInstance := by
    rw [htop]
    change _ = TopologicalSpace.induced Φ Pi.topologicalSpace
    rw [Pi.topologicalSpace, induced_iInf]
    refine iInf_congr fun i => ?_
    rw [induced_compose]
    rfl
  have hΦc : Continuous Φ := by
    rw [hind]
    exact continuous_induced_dom
  -- `E` is linearly homeomorphic to the range of `Φ`
  let e₀ : E ≃ₗ[ℂ] LinearMap.range Φ := LinearEquiv.ofInjective Φ hΦinj
  have he₀ : ∀ x, ((e₀ x : LinearMap.range Φ) : ∀ i, Y i) = Φ x := fun x => rfl
  have hc1 : Continuous e₀ := by
    refine Continuous.subtype_mk hΦc _
  have hc2 : Continuous e₀.symm := by
    rw [hind, continuous_induced_rng]
    have : (Φ ∘ e₀.symm) = fun v : LinearMap.range Φ => (v : ∀ i, Y i) := by
      funext v
      have := he₀ (e₀.symm v)
      rw [LinearEquiv.apply_symm_apply] at this
      exact this.symm
    rw [this]
    exact continuous_subtype_val
  let e : E ≃L[ℂ] LinearMap.range Φ :=
    { e₀ with continuous_toFun := hc1, continuous_invFun := hc2 }
  exact nuclear_of_continuousLinearEquiv E (LinearMap.range Φ) e
    (nuclear_subspace _ (nuclear_pi ι Y hY) (LinearMap.range Φ))
