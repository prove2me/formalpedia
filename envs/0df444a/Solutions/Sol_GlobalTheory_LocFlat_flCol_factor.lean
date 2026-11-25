-- Prove2me | solution 1 for GlobalTheory.LocFlat.flCol_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:57:24.45941+00:00
-- url     : https://prove2.me/submissions/6dde76cd-d102-47c0-a4cd-f4dca0aee259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatMapsPreserveSchwartzBruhatAndSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFactorThroughFlatMapFourierJacobiColumn
import Theorems.Thm_GlobalTheory_LocFlat_flCol_add_of_SB
import Theorems.Thm_GlobalTheory_LocFlat_flCol_smul
import Theorems.Thm_GlobalTheory_LocFlat_flat_SB_onto


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
noncomputable section
open GlobalTheory GlobalTheory.LocFlat
namespace GlobalTheory.LocFlat
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), (∀ x, GlobalTheory.LocFlat.flCol ψ ν p Φ.1 x = 0) → L Φ = 0) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν p Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψ hν n n' _ _ _ _ c p hp1 hpc M _ _ L hL
  have hSB := (flat_SB_onto k ψ ν hψ hν n n' c p hp1).1 hpc
  let F : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) :=
    { toFun := fun Φ => ⟨flCol ψ ν p Φ.1, hSB.1 Φ.1 Φ.2⟩
      map_add' := fun Φ₁ Φ₂ => Subtype.ext (flCol_add_of_SB ψ hψ ν hν p Φ₁.1 Φ₂.1 Φ₁.2 Φ₂.2)
      map_smul' := fun a Φ => Subtype.ext (flCol_smul ψ ν p a Φ.1) }
  have hFs : Function.Surjective F := fun Ψ => by
    obtain ⟨Φ, hΦ, h⟩ := hSB.2 Ψ.1 Ψ.2
    exact ⟨⟨Φ, hΦ⟩, Subtype.ext h⟩
  have hker : LinearMap.ker F ≤ LinearMap.ker L := fun Φ hΦ => by
    rw [LinearMap.mem_ker] at hΦ ⊢
    apply hL
    intro x
    have := congrArg (fun Ψ : SB (Matrix n (n' ⊕ Unit) k) => Ψ.1 x) hΦ
    simpa [F] using this
  refine ⟨((LinearMap.ker F).liftQ L hker).comp (F.quotKerEquivOfSurjective hFs).symm.toLinearMap, ?_⟩
  intro Φ Ψ hΨ
  have hΨF : Ψ = F Φ := Subtype.ext hΨ
  subst hΨF
  have h2 : (F.quotKerEquivOfSurjective hFs).symm (F Φ) = Submodule.Quotient.mk Φ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h2]
  rfl
end GlobalTheory.LocFlat
