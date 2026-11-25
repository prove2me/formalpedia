-- Prove2me | solution 1 for GlobalTheory.schur_heisenberg_linearModel_fintype
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:03:29.9646+00:00
-- url     : https://prove2.me/submissions/55db23ae-7a68-45ac-a0a7-62ea4bb9c056

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeilRepBijectionSchwartz
import Theorems.Thm_P2M_GlobalTheory_SchurHeisReindex_comp_mem_SB__96b25bb61081
import Theorems.Thm_GlobalTheory_T_eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory.SchurHeisReindex
namespace GlobalTheory
theorem _root_.solution : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {β : Type} [Fintype β] [DecidableEq β] {Xt : Type} [AddCommGroup Xt] [Module ℂ Xt] (V : Submodule ℂ Xt)
    (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι₁ : Xt →ₗ[ℂ] (Matrix (Fin n) β k → ℂ)) (ι₂ : Xt → Matrix (Fin n) β k → ℂ),
    Set.BijOn ι₁ (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) β k) : Set _) →
    (∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂ (c • x + y) = c • ι₂ x + ι₂ y) →
    ∀ (Tr : Matrix (Fin n) β k → Xt → Xt) (Mu : (Matrix (Fin n) β k →ₗ[k] k) → Xt → Xt),
    (∀ C, ∀ x ∈ V, Tr C x ∈ V ∧ ι₁ (Tr C x) = (fun Y => ι₁ x (Y + C)) ∧ ι₂ (Tr C x) = fun Y => ι₂ x (Y + C)) →
    (∀ l, ∀ x ∈ V, Mu l x ∈ V ∧ ι₁ (Mu l x) = (fun Y => ψ0 (l Y) * ι₁ x Y) ∧ ι₂ (Mu l x) = fun Y => ψ0 (l Y) * ι₂ x Y) →
    ∃ c : ℂ, ∀ x ∈ V, ι₂ x = c • ι₁ x := by
  intro k _ _ _ _ n β _ _ Xt _ _ V ψ0 hψc hψ1 ι₁ ι₂ hbij hlin Tr Mu hTr hMu
  set e := eL k n β with he
  let ι₁' : Xt →ₗ[ℂ] (Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ) := LinearMap.funLeft ℂ ℂ e ∘ₗ ι₁
  have hι₁' : ∀ x, ι₁' x = ι₁ x ∘ e := fun x => rfl
  let ι₂' : Xt → Matrix (Fin n) (Fin (Fintype.card β)) k → ℂ := fun x => ι₂ x ∘ e
  have hsurj : Function.Surjective e := e.surjective
  have hbij' : Set.BijOn ι₁' (V : Set Xt) (GlobalTheory.WeilM.SB (Matrix (Fin n) (Fin (Fintype.card β)) k) : Set _) := by
    refine ⟨fun x hx => ?_, fun x hx y hy hxy => ?_, fun f hf => ?_⟩
    · rw [hι₁']
      exact comp_mem_SB' (eH k n β) (hbij.1 hx)
    · apply hbij.2.1 hx hy
      rw [hι₁', hι₁'] at hxy
      funext Z
      obtain ⟨Y, rfl⟩ := hsurj Z
      exact congrFun hxy Y
    · have hf' : f ∘ (eH k n β).symm ∈ GlobalTheory.WeilM.SB (Matrix (Fin n) β k) := comp_mem_SB' (eH k n β).symm hf
      obtain ⟨x, hx, hxf⟩ := hbij.2.2 hf'
      refine ⟨x, hx, ?_⟩
      rw [hι₁', hxf]
      funext Y
      show f ((eH k n β).symm (e Y)) = f Y
      exact congrArg f ((eL k n β).symm_apply_apply Y)
  have hlin' : ∀ x ∈ V, ∀ y ∈ V, ∀ c : ℂ, ι₂' (c • x + y) = c • ι₂' x + ι₂' y := by
    intro x hx y hy c
    funext Y
    simp [ι₂', hlin x hx y hy c]
  have hadd : ∀ Y C, e (Y + C) = e Y + e C := fun Y C => map_add e Y C
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat V ψ0 hψc hψ1 ι₁' ι₂' hbij' hlin'
    (fun C => Tr (e C)) (fun l => Mu (l ∘ₗ e.symm.toLinearMap))
    (fun C x hx => by
      obtain ⟨h1, h2, h3⟩ := hTr (e C) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2, hadd]
      · funext Y; simp [ι₂', h3, hadd])
    (fun l x hx => by
      obtain ⟨h1, h2, h3⟩ := hMu (l ∘ₗ e.symm.toLinearMap) x hx
      refine ⟨h1, ?_, ?_⟩
      · funext Y; simp [hι₁', h2]
      · funext Y; simp [ι₂', h3])
  refine ⟨c, fun x hx => ?_⟩
  funext Z
  obtain ⟨Y, rfl⟩ := hsurj Z
  have := congrFun (hc x hx) Y
  simpa [ι₂', hι₁'] using this
end GlobalTheory
