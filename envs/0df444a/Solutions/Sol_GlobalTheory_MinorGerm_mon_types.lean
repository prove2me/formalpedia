-- Prove2me | solution 1 for GlobalTheory.MinorGerm.mon_types
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:43:57.627118+00:00
-- url     : https://prove2.me/submissions/ce5427f2-7029-4563-9b68-a0b09addfa5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_low_prod
import Theorems.Thm_GlobalTheory_MinorGerm_lead_prod
import Theorems.Thm_GlobalTheory_MinorGerm_jet_eq
import Theorems.Thm_GlobalTheory_MinorGerm_lead_monP
import Theorems.Thm_GlobalTheory_MinorGerm_low_monG
import Theorems.Thm_GlobalTheory_MinorGerm_dg_apply
import Theorems.Thm_GlobalTheory_MinorGerm_dg_apply_of_notMem
import Theorems.Thm_GlobalTheory_MinorGerm_prod_factorial_diag
import Theorems.Thm_GlobalTheory_LegendreFacts_mfact_eq_prod


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
namespace GlobalTheory.MinorGerm
theorem _root_.solution : MONTypes := by
  classical
  intro C _ _ B _ _ N N' e t ht
  classical
  let p : (Σ b : B, Fin N × Fin (N' b)) → Prop := fun x => x.2.1.val = x.2.2.val
  have hL : Lead p (∑ b : B, dg (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b))) (monAl N (N' b) (e b)))
      (∏ b : B, MvPolynomial.rename (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b)))
        (monP C N (N' b) (e b))) :=
    lead_prod _ _ _ (fun b _ => lead_monP _ (fun r c => Iff.rfl) (e b))
  have hG : Low (∑ b : B, dg (fun x => (⟨b, x⟩ : Σ b : B, Fin N × Fin (N' b))) (monAl N (N' b) (e b)))
      (∏ b : B, monG N (N' b) (e b) fun x => t ⟨b, x⟩) :=
    low_prod _ _ _ (fun b _ => low_monG _ ht (e b))
  rw [jet_eq hL hG, GlobalTheory.LegendreFacts.mfact_eq_prod, Fintype.prod_sigma]
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  rw [← prod_factorial_diag (e b)]
  apply Finset.prod_congr rfl
  intro y _
  congr 1
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single b]
  · obtain ⟨r, c⟩ := y
    exact dg_apply _ (fun x y hxy => eq_of_heq (Sigma.mk.inj hxy).2) _ r c
  · intro b' _ hb'
    apply dg_apply_of_notMem
    intro z hz
    exact hb' (congrArg Sigma.fst hz).symm
  · intro h
    exact absurd (Finset.mem_univ b) h
end GlobalTheory.MinorGerm
