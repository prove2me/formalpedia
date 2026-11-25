-- Prove2me | solution 1 for GlobalTheory.RootEx.ParabolicEntries.mem_R_iff_and_mem_RFJ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:12:42.80145+00:00
-- url     : https://prove2.me/submissions/fc751dbe-d2aa-41a6-981b-198f4f227bf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierJacobiUnipotentEqProdRootExchange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MemRootExchangeParabolicAndFourierJacobiIffEntri
import Theorems.Thm_GlobalTheory_RootEx_ParabolicEntries_exists_eq_embX_mul
import Theorems.Thm_GlobalTheory_RootEx_ParabolicEntries_embX_mem_R
import Theorems.Thm_GlobalTheory_RootEx_ParabolicEntries_R_le
import Theorems.Thm_GlobalTheory_RootEx_FJUnipotent_fj_unipotent
import Theorems.Thm_GlobalTheory_RootEx_Radical_mem_N_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.ParabolicEntries
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.RootEx.ParabolicEntries
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), (∀ g : GL (n ⊕ Fin c) k, g ∈ R k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) s ≤ Sum.elim (fun _ => ρ) (fun i : Fin c => i.val + 1) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) ∧ (1 ≤ ρ → ρ < c → ∀ g : GL (n ⊕ Fin c) k, g ∈ RFJ k n c ρ ↔ ∀ r s : n ⊕ Fin c, (r.isRight ∨ s.isRight) → Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) s ≤ Sum.elim (fun _ => 2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) r → g.val r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s) := by
  intro k _ n _ _ c ρ
  refine ⟨fun g => ⟨fun hg => ?_, fun hg => ?_⟩, fun h1 hc g => ⟨fun hg => ?_, fun hg => ?_⟩⟩
  · exact R_le (L := ρ) (b := fun i : Fin c => i.val + 1)
      (fun u hu r s _ hrs => (mem_N_iff u).1 hu r s hrs) hg
  · obtain ⟨x, u, hu, rfl⟩ := exists_eq_embX_mul (L := ρ) (b := fun i : Fin c => i.val + 1) hg
    exact mul_mem (embX_mem_R ρ x) (Subgroup.mem_sup_right ((mem_N_iff u).2 hu))
  · have hN : NFJ k n c ρ ≤ parGroup k n (2 * ρ + 1) (fun i : Fin c => 2 * (i.val + 1)) :=
      fun u hu r s _ hrs => ((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).1 hu r s hrs
    exact sup_le (R_le (le_sup_left.trans hN)) (R_le (le_sup_right.trans hN)) hg
  · obtain ⟨x, u, hu, rfl⟩ :=
      exists_eq_embX_mul (L := 2 * ρ + 1) (b := fun i : Fin c => 2 * (i.val + 1)) hg
    have hN : NFJ k n c ρ ≤ RFJ k n c ρ := sup_le_sup le_sup_right le_sup_right
    exact mul_mem (Subgroup.mem_sup_left (embX_mem_R ρ x))
      (hN (((GlobalTheory.RootEx.FJUnipotent.fj_unipotent k n c ρ h1 hc).2.1 u).2 hu))
end GlobalTheory.RootEx.ParabolicEntries
