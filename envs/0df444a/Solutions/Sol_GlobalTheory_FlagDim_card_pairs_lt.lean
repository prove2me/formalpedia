-- Prove2me | solution 1 for GlobalTheory.FlagDim.card_pairs_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:09:38.086711+00:00
-- url     : https://prove2.me/submissions/fd4e8f8e-3122-4dc5-b01a-6a407671b45b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FnTrdegOf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFinsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_DimAddCardFlagVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.FlagDim
open NumberField
namespace GlobalTheory.FlagDim
namespace _root_.GlobalTheory.FlagDim
theorem _root_.solution (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  have e : {p : Fin n × Fin n // p.1 < p.2} ≃ (j : Fin n) × Fin j :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨(⟨q.2, q.2.2.trans q.1.2⟩, q.1), q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]
end _root_.GlobalTheory.FlagDim
end GlobalTheory.FlagDim
