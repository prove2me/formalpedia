-- Prove2me | solution 1 for GlobalTheory.MinorGerm.dg_monAl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:59.178996+00:00
-- url     : https://prove2.me/submissions/fcb7098f-7d67-4efb-8f50-ca9b1c2ef1e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_dgOne_eq_smul
import Theorems.Thm_GlobalTheory_MinorGerm_monAl_eq
import Theorems.Thm_GlobalTheory_MinorGerm_sum_range_ite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
noncomputable section
open GlobalTheory GlobalTheory.MinorGerm
variable {C : Type} [Field C] {σ : Type} {N N' : ℕ}
namespace GlobalTheory.MinorGerm
theorem _root_.solution (j : Fin N × Fin N' → σ) (e : ℕ → ℕ) :
    dg j (monAl N N' e) =
      ∑ k ∈ Finset.Icc 1 (min N N'), e k • ∑ ρ ∈ Finset.range k, dgOne j ρ 1 := by
  classical
  unfold dg
  have h : ∀ ρ, dgOne j ρ (monAl N N' e ρ) =
      ∑ k ∈ Finset.Icc 1 (min N N'), if ρ < k then e k • dgOne j ρ 1 else 0 := by
    intro ρ
    rw [dgOne_eq_smul, monAl_eq, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro k _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun ρ _ => h ρ), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_Icc] at hk
  rw [sum_range_ite (by omega : k ≤ N) (fun ρ => e k • dgOne j ρ 1), Finset.smul_sum]
end GlobalTheory.MinorGerm
