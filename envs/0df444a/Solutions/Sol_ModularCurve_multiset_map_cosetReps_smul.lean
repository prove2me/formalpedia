-- Prove2me | solution 1 for ModularCurve.multiset_map_cosetReps_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/6d48a970-a392-5156-97e4-0a4109bdb3cb

import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Tactic.Group
import Theorems.Thm_ModularCurve_exists_perm_gamma0_cosetReps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_multiset_map_cosetReps_smul

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup
open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "exists_perm_gamma0_cosetReps"
p2m_open "ModularCurve"

namespace QexpN

private def rep (ℓ : ℕ) (i : Fin (ℓ + 1)) : SL(2, ℤ) :=
  Fin.cases 1 (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i

private theorem multiset_map_cosetReps_smul' (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (α : Type*)
    (F : UpperHalfPlane → α)
    (hF : ∀ γ ∈ Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (γ : SL(2, ℤ)) (τ : UpperHalfPlane) :
    (Finset.univ.val.map fun i : Fin (ℓ + 1) => F (rep ℓ i • γ • τ))
      = Finset.univ.val.map fun i : Fin (ℓ + 1) => F (rep ℓ i • τ) := by
  obtain ⟨e, he⟩ := ModularCurve.exists_perm_gamma0_cosetReps ℓ γ
  have key : ∀ i : Fin (ℓ + 1), F (rep ℓ i • γ • τ) = F (rep ℓ (e i) • τ) := by
    intro i
    have hmem : rep ℓ i * γ * (rep ℓ (e i))⁻¹ ∈ Gamma0 ℓ := he i
    have h1 : rep ℓ i • γ • τ = (rep ℓ i * γ) • τ := (mul_smul _ _ _).symm
    have h2 : rep ℓ i * γ = rep ℓ i * γ * (rep ℓ (e i))⁻¹ * rep ℓ (e i) := by group
    rw [h1, h2, mul_smul]
    exact hF _ hmem _
  have huniv : Finset.univ.val.map ⇑e = Finset.univ.val := by
    rw [← Equiv.coe_toEmbedding, ← Finset.map_val, Finset.map_univ_equiv]
  conv_rhs => rw [← huniv, Multiset.map_map]
  exact Multiset.map_congr rfl fun i _ => key i

end QexpN

end ModularCurve

end

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (α : Type*) (F : UpperHalfPlane → α) (hF : ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) : (Finset.univ.val.map fun i : Fin (ℓ + 1) => F ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) • γ • τ)) = Finset.univ.val.map fun i : Fin (ℓ + 1) => F ((Fin.cases (1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) (fun b : Fin ℓ => ModularGroup.S * ModularGroup.T ^ (b : ℕ)) i : Matrix.SpecialLinearGroup (Fin 2) ℤ) • τ) :=
  ModularCurve.QexpN.multiset_map_cosetReps_smul' ℓ α F hF γ τ

end S_ModularCurve_multiset_map_cosetReps_smul
end P2MW
export P2MW.S_ModularCurve_multiset_map_cosetReps_smul (solution)
