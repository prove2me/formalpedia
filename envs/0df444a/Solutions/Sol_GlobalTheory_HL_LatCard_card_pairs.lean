-- Prove2me | solution 1 for GlobalTheory.HL.LatCard.card_pairs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:37:11.837734+00:00
-- url     : https://prove2.me/submissions/81bb184f-8257-4d94-899d-eb5c34b0fdfa

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelIndexTupleLatticeHermitianLatticeUniformizer
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.LatCard
namespace GlobalTheory.HL.LatCard
theorem _root_.solution (m : ℕ) :
    m + 2 * Fintype.card {p : Fin m × Fin m // p.1 < p.2} = m ^ 2 := by
  rw [← Nat.card_eq_fintype_card]
  have e1 : {p : Fin m × Fin m // p.1 < p.2} ≃ {p : Fin m × Fin m // p.2 < p.1} :=
    Equiv.subtypeEquiv (Equiv.prodComm _ _) (fun p => Iff.rfl)
  have e2 : {p : Fin m × Fin m // p.1 = p.2} ≃ Fin m :=
    { toFun := fun p => p.1.1
      invFun := fun a => ⟨(a, a), rfl⟩
      left_inv := fun p => by
        obtain ⟨⟨a, b⟩, h⟩ := p
        simp only at h
        subst h
        rfl
      right_inv := fun a => rfl }
  have e3 : {p : Fin m × Fin m // ¬ p.1 = p.2} ≃
      {p : Fin m × Fin m // p.1 < p.2} ⊕ {p : Fin m × Fin m // p.2 < p.1} :=
    (Equiv.subtypeEquivRight (fun p => ne_iff_lt_or_gt)).trans
      (subtypeOrEquiv _ _ (by
        intro r h1 h2 x hx
        exact (lt_asymm (h1 x hx) (h2 x hx)).elim))
  have hcard : Nat.card (Fin m × Fin m) = m + (Nat.card {p : Fin m × Fin m // p.1 < p.2} +
      Nat.card {p : Fin m × Fin m // p.1 < p.2}) := by
    rw [Nat.card_congr (Equiv.sumCompl (fun p : Fin m × Fin m => p.1 = p.2)).symm, Nat.card_sum,
      Nat.card_congr e2, Nat.card_congr e3, Nat.card_sum, ← Nat.card_congr e1]
    simp
  rw [Nat.card_prod] at hcard
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard ⊢
  rw [sq, hcard]
  ring
end GlobalTheory.HL.LatCard
