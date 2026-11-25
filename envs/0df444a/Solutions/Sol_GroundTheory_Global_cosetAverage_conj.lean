-- Prove2me | solution 1 for GroundTheory.Global.cosetAverage_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:08:46.908655+00:00
-- url     : https://prove2.me/submissions/e2efb527-0d3a-4458-b9e7-fc07676c91d5

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Polynomial
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {G : Type*} [Group G]
namespace GroundTheory.Global
theorem _root_.solution (I J : Subgroup G) (f : G → ℂ) (hf : ∀ g h : G, f (h * g * h⁻¹) = f g)
    (h : G) (hIJ : ∀ σ, σ ∈ J ↔ h⁻¹ * σ * h ∈ I) (g : G) :
    cosetAverage J f (h * g * h⁻¹) = cosetAverage I f g := by
  let e : I ≃ J :=
    { toFun := fun i => ⟨h * i * h⁻¹, (hIJ _).2 (by
        rw [show h⁻¹ * (h * (i : G) * h⁻¹) * h = i by group]; exact i.2)⟩
      invFun := fun j => ⟨h⁻¹ * j * h, (hIJ _).1 j.2⟩
      left_inv := fun i => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc] }
  unfold cosetAverage
  rw [Nat.card_congr e, ← finsum_comp_equiv e]
  congr 1
  refine finsum_congr fun i => ?_
  simp only [e, Equiv.coe_fn_mk]
  rw [show h * g * h⁻¹ * (h * (i : G) * h⁻¹) = h * (g * i) * h⁻¹ by group, hf]
end GroundTheory.Global
