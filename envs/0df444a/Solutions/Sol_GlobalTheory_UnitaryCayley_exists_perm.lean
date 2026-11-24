-- Prove2me | solution 1 for GlobalTheory.UnitaryCayley.exists_perm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:10.649572+00:00
-- url     : https://prove2.me/submissions/018b9c5b-165c-4e73-9afd-ff52fd9490c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_ExistsIsCayleyUIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset PI.UpqRep
noncomputable section
open GlobalTheory GlobalTheory.UnitaryCayley
namespace GlobalTheory.UnitaryCayley
theorem _root_.solution {n : ℕ} (ε δ : Fin n → Bool)
    (h : (univ.filter fun i => ε i = true).card = (univ.filter fun i => δ i = true).card) :
    ∃ e : Fin n ≃ Fin n, ∀ a, δ (e a) = ε a := by
  have h1 : Fintype.card {a // ε a = true} = Fintype.card {a // δ a = true} := by
    simp only [Fintype.card_subtype]; exact h
  have h2 : Fintype.card {a // ¬ ε a = true} = Fintype.card {a // ¬ δ a = true} := by
    simp only [Fintype.card_subtype_compl, h1]
  let e1 := Fintype.equivOfCardEq h1
  let e2 := Fintype.equivOfCardEq h2
  refine ⟨(Equiv.sumCompl fun a => ε a = true).symm.trans
    ((Equiv.sumCongr e1 e2).trans (Equiv.sumCompl fun a => δ a = true)), fun a => ?_⟩
  by_cases ha : ε a = true
  · have := (e1 ⟨a, ha⟩).2
    simp [Equiv.sumCompl_symm_apply_of_pos (p := fun a => ε a = true) ha, ha, this]
  · have := (e2 ⟨a, ha⟩).2
    simp only [Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg (p := fun a => ε a = true) ha,
      Equiv.sumCongr_apply, Sum.map_inr, Equiv.sumCompl_apply_inr]
    simp only [Bool.not_eq_true] at ha this
    rw [ha, this]
end GlobalTheory.UnitaryCayley
