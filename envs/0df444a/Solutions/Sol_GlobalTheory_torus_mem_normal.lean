-- Prove2me | solution 1 for GlobalTheory.torus_mem_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:46.553336+00:00
-- url     : https://prove2.me/submissions/ef95135c-97c3-440b-be85-169af6d660c2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_GlobalTheory_TorusNormal_pm_mul
import Theorems.Thm_GlobalTheory_TorusNormal_diagonal_pm
import Theorems.Thm_GlobalTheory_TorusNormal_idx_cases
import Theorems.Thm_GlobalTheory_TorusNormal_exists_mem_pm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory
open Formalism.UG.P GlobalTheory.TorusNormal
namespace GlobalTheory
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal →
    Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ (c : Fin n → ℤ),
    (∀ i : Fin n, c i.rev = -c i) → ∀ t : Formalism.UG.GU σ n,
    ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ c i) → t ∈ N := by
  intro L _ _ ϖ σ q n hU N _ hK hUn c hc t ht
  obtain ⟨hσσ, hσv, hσϖ, hvϖ, ⟨x, -, hx⟩, -⟩ := hU
  set δ := σ x - x with hδ
  have hδ0 : δ ≠ 0 := by
    intro h; rw [h, map_zero] at hx; exact zero_ne_one hx
  have hδσ : σ δ = -δ := by
    rw [hδ, map_sub, hσσ]; ring
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hvϖ; exact WithZero.zero_ne_coe hvϖ
  obtain ⟨g0, hg0, e0⟩ := exists_mem_pm σ hσv N hK hUn (fun _ => δ) (fun _ => hδ0) (fun _ => hδσ)
  obtain ⟨g1, hg1, e1⟩ := exists_mem_pm σ hσv N hK hUn (fun i => ϖ ^ c i * δ)
    (fun i => mul_ne_zero (zpow_ne_zero _ hϖ0) hδ0)
    (fun i => by rw [map_mul, map_zpow₀, hσϖ, hδσ, mul_neg])
  have key : t * g0 = g1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [ht, e0, e1, diagonal_pm, pm_mul]
    congr 1 <;> funext i <;>
      rcases idx_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
    · have hc0 : c i = 0 := by have := hc i; rw [h3] at this; omega
      simp only [Fin.val_rev] at h1 h2; simp [h1, h2, hc0]
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
    · simp only [Fin.val_rev] at h1 h2
      simp [h1, h2, hc i, _root_.zpow_neg]
      ring
    · simp only [Fin.val_rev] at h1 h2; simp [h1, h2]
  rw [eq_mul_inv_of_mul_eq key]
  exact mul_mem hg1 (inv_mem hg0)
end GlobalTheory
