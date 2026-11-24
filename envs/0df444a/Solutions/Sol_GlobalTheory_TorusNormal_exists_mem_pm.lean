-- Prove2me | solution 1 for GlobalTheory.TorusNormal.exists_mem_pm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:34.0836+00:00
-- url     : https://prove2.me/submissions/9282c8da-4ca7-4fa2-a89e-5c2a16711c39

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_GlobalTheory_TorusNormal_pm_mul
import Theorems.Thm_GlobalTheory_TorusNormal_cT_pm
import Theorems.Thm_GlobalTheory_TorusNormal_antiJ_pm
import Theorems.Thm_GlobalTheory_TorusNormal_un_pm
import Theorems.Thm_GlobalTheory_TorusNormal_unip_pm
import Theorems.Thm_GlobalTheory_TorusNormal_idx_cases
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
import Theorems.Thm_Formalism_UG_P_fIwasawa_mk_mem_K
import Theorems.Thm_Formalism_UG_P_fIwasawa_mk_val
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
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.TorusNormal
theorem _root_.solution (σ : L →+* L) {n : ℕ} (hσv : ∀ x, Valued.v (σ x) = Valued.v x)
    (N : Subgroup (GU σ n)) (hK : KU σ n ≤ N) (hU : ∀ u : GU σ n, IsUnipU u → u ∈ N)
    (y : Fin n → L) (hy0 : ∀ i, y i ≠ 0) (hyσ : ∀ i, σ (y i) = -y i) :
    ∃ g ∈ N, ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      pm (fun i => if 2 * i.val + 1 < n ∨ 2 * (Fin.rev i).val + 1 < n then 0 else 1)
        (fun i => (if 2 * i.val + 1 < n then y i else 0) +
          (if 2 * (Fin.rev i).val + 1 < n then -(y (Fin.rev i))⁻¹ else 0)) := by
  set u : Fin n → L := fun i => if 2 * i.val + 1 < n then y i else 0 with hu
  set l : Fin n → L := fun i => if 2 * i.val + 1 < n then -(y i)⁻¹ else 0 with hl
  have hu1 : ∀ i, σ (u i) = -u i := by
    intro i; simp only [hu]; split_ifs <;> simp [hyσ]
  have hu2 : ∀ i, u i ≠ 0 → 2 * i.val + 1 < n := by
    intro i h; simp only [hu] at h; split_ifs at h with h'
    · exact h'
    · exact absurd rfl h
  have hl1 : ∀ i, σ (l i) = -l i := by
    intro i; simp only [hl]; split_ifs <;> simp [hyσ, map_inv₀, inv_neg]
  have hl2 : ∀ i, l i ≠ 0 → 2 * i.val + 1 < n := by
    intro i h; simp only [hl] at h; split_ifs at h with h'
    · exact h'
    · exact absurd rfl h
  have hW : fIwasawaUn σ (antiJ L n) := by
    unfold fIwasawaUn
    rw [antiJ_pm, cT_pm, pm_mul, pm_mul]
    congr 1 <;> funext i <;> simp
  have hWK : fIwasawaMk σ _ hW ∈ KU σ n := by
    refine fIwasawa_mk_mem_K σ hσv _ hW fun i j => ?_
    rw [fIwasawa_antiJ]
    split_ifs <;> simp
  have hA := hU _ (unip_pm σ u (un_pm σ u hu1 hu2) hu2)
  have hB := hU _ (unip_pm σ l (un_pm σ l hl1 hl2) hl2)
  refine ⟨fIwasawaMk σ _ (un_pm σ u hu1 hu2) * fIwasawaMk σ _ hW * fIwasawaMk σ _ (un_pm σ l hl1 hl2) *
    fIwasawaMk σ _ hW * fIwasawaMk σ _ (un_pm σ u hu1 hu2),
    mul_mem (mul_mem (mul_mem (mul_mem hA (hK hWK)) hB) (hK hWK)) hA, ?_⟩
  simp only [Subgroup.coe_mul, Units.val_mul, fIwasawa_mk_val]
  rw [antiJ_pm, pm_mul, pm_mul, pm_mul, pm_mul]
  congr 1 <;> funext i <;>
    rcases idx_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ <;>
    simp only [Fin.val_rev] at h1 h2 <;>
    simp [hu, hl, h1, h2, Fin.rev_rev, hy0]
end GlobalTheory.TorusNormal
