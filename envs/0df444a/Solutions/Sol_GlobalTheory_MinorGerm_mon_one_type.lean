-- Prove2me | solution 1 for GlobalTheory.MinorGerm.mon_one_type
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:43:55.958588+00:00
-- url     : https://prove2.me/submissions/50c4e3e6-fc85-4065-a309-42a4574def22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LegendreAndCapelli
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ProdFactorialDiag
import Theorems.Thm_GlobalTheory_MinorGerm_jet_eq
import Theorems.Thm_GlobalTheory_MinorGerm_sum_monAl
import Theorems.Thm_GlobalTheory_MinorGerm_lead_monP
import Theorems.Thm_GlobalTheory_MinorGerm_low_monG
import Theorems.Thm_GlobalTheory_MinorGerm_dg_apply
import Theorems.Thm_GlobalTheory_MinorGerm_prod_factorial_diag
import Theorems.Thm_GlobalTheory_MinorGerm_val_coprime
import Theorems.Thm_GlobalTheory_MinorGerm_val_nat
import Theorems.Thm_GlobalTheory_LegendreFacts_legendre_facts
import Theorems.Thm_GlobalTheory_LegendreFacts_mfact_eq_prod
import Theorems.Thm_P2M_GlobalTheory_LegendreFacts_degree_eq_sum__2b1d5d1ba054


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
theorem _root_.solution : MON := by
  classical
  intro C _ _ N N' e t ht
  classical
  have hL := lead_monP (C := C) (p := fun x : Fin N × Fin N' => x.1.val = x.2.val) id (fun b c => Iff.rfl) e
  have hG := low_monG (C := C) (N := N) (N' := N') id ht e
  simp only [MvPolynomial.rename_id, AlgHom.id_apply] at hL
  have hjet := jet_eq hL hG
  have hm2 : mfact (dg (id : Fin N × Fin N' → Fin N × Fin N') (monAl N N' e)) =
      ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial := by
    rw [GlobalTheory.LegendreFacts.mfact_eq_prod, ← prod_factorial_diag e]
    apply Finset.prod_congr rfl
    intro x _
    obtain ⟨b, c⟩ := x
    exact congrArg Nat.factorial (dg_apply id Function.injective_id _ b c)
  refine ⟨?_, sum_monAl e, ?_⟩
  · rw [← hm2]
    exact hjet
  · intro v l hl hv
    set M := ∏ ρ : Fin N, (monAl N N' e ρ.val).factorial with hM
    have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.2 (fun ρ _ => Nat.factorial_ne_zero _)
    refine ⟨?_, ?_⟩
    · rw [val_nat v hl hv hM0, WithTop.coe_le_coe]
      let A : Fin N →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun ρ => monAl N N' e ρ.val)
      have hA1 : mfact A = M := by
        rw [GlobalTheory.LegendreFacts.mfact_eq_prod]
        rfl
      have hA2 : A.degree = monDeg N N' e := by
        rw [GlobalTheory.LegendreFacts.degree_eq_sum', ← sum_monAl e]
        rfl
      by_cases hd : 1 ≤ A.degree
      · have h := ((GlobalTheory.LegendreFacts.legendre_facts l hl).2.2.1 (Fin N) A hd).2
        rw [hA1, hA2] at h
        exact h
      · have hd0 : monDeg N N' e = 0 := by omega
        have hall : ∀ ρ : Fin N, monAl N N' e ρ.val = 0 := by
          intro ρ
          have h := sum_monAl (N := N) (N' := N') e
          rw [hd0] at h
          exact (Finset.sum_eq_zero_iff.1 h) ρ (Finset.mem_univ _)
        have hM1 : M = 1 := by
          rw [hM]
          simp [hall]
        rw [hM1, hd0]
        simp
    · intro hlt
      apply val_coprime v hl hv
      rw [hM]
      intro hdvd
      obtain ⟨ρ, _, hρ⟩ := (Prime.dvd_finsetProd_iff hl.prime _).1 hdvd
      exact absurd ((Nat.Prime.dvd_factorial hl).1 hρ) (not_le.2 (hlt ρ))
end GlobalTheory.MinorGerm
