-- Prove2me | solution 1 for GlobalTheory.MatchParts.rank_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:24.491696+00:00
-- url     : https://prove2.me/submissions/a9e6de7e-6997-4796-9891-960ee33e4616

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TxCosetCriterionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ThetaRecognitionMatchedPartsDimEq
import Theorems.Thm_P2M_GlobalTheory_MatchParts_tot__1edb3291971f
import Theorems.Thm_GlobalTheory_MatchParts_r_inv
import Theorems.Thm_GlobalTheory_MatchParts_card_le_of_rel
import Theorems.Thm_GlobalTheory_IsSiegel_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.MatchParts
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ}
namespace GlobalTheory.MatchParts
theorem _root_.solution (μ : Match N N' n) (hn : 1 < n) {k : ℕ} (hk : k = n ^ 1)
    (hG : ∀ p p', μ.r k p p' → N'.InG p' → N.InG p) (hy : ∀ y : N.X, ∃ p : N.QT k, p.1.1.toAdd = y) :
    Module.finrank ℤ N.X ≤ Module.finrank ℤ N'.X := by
  have hl : ∃ j, k = n ^ j := ⟨1, hk⟩
  have hk1 : 1 < k := by rw [hk, pow_one]; exact hn
  have h1 : Nat.card (N.X ⧸ (nsmulAddMonoidHom k : N.X →+ N.X).range) = k ^ Module.finrank ℤ N.X :=
    AddSubgroup.index_range_nsmul N.X k
  have h2 : Nat.card (N'.X ⧸ (nsmulAddMonoidHom k : N'.X →+ N'.X).range) = k ^ Module.finrank ℤ N'.X :=
    AddSubgroup.index_range_nsmul N'.X k
  haveI : Finite (N'.X ⧸ (nsmulAddMonoidHom k : N'.X →+ N'.X).range) :=
    Nat.finite_of_card_ne_zero (by rw [h2]; positivity)
  rw [← Nat.pow_le_pow_iff_right hk1, ← h1, ← h2]
  refine card_le_of_rel (fun a b => ∃ p p', μ.r k p p' ∧ a = QuotientAddGroup.mk p.1.1.toAdd ∧
    b = QuotientAddGroup.mk p'.1.1.toAdd) (fun a => ?_) ?_
  · obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective a
    obtain ⟨p, rfl⟩ := hy y
    obtain ⟨p', h⟩ := tot' μ hl p
    exact ⟨_, p, p', h, rfl, rfl⟩
  · rintro _ _ _ ⟨p, p', h, rfl, rfl⟩ ⟨q, q', h', rfl, e⟩
    obtain ⟨z, hz⟩ := QuotientAddGroup.eq.1 e
    obtain ⟨w, hw⟩ := hG _ _ (μ.mul k _ _ _ _ (r_inv μ hl h) h') ⟨z, hz.symm⟩
    exact QuotientAddGroup.eq.2 ⟨w, hw.symm⟩
end GlobalTheory.MatchParts
