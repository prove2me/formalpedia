-- Prove2me | solution 1 for GlobalTheory.exists_awayMap_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:38:09.917485+00:00
-- url     : https://prove2.me/submissions/be6df008-8814-40c6-be11-cf15276332ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsAwaySubalgebraEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsFgSubalgebraDescAway
import Theorems.Thm_GlobalTheory_AwaySubalgebraEmbedding_exists_away_subalgebra_embedding


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (S : Type) [CommRing S] [Algebra K S]
    (S₁ : Subalgebra K S) (x : S) (hx : x ∈ S₁) :
    ∃ κ : Localization.Away (⟨x, hx⟩ : S₁) →ₐ[K] Localization.Away x,
      (∀ s : S₁, κ (algebraMap S₁ _ s) = algebraMap S _ (s : S)) ∧ Function.Injective κ ∧
      ∀ (z : Localization.Away x) (m : ℕ) (s : S), s ∈ S₁ →
        z * algebraMap S _ x ^ m = algebraMap S _ s → z ∈ κ.range := by
  first
  | exact @_root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
  | exact _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding
  | (apply _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AwaySubalgebraEmbedding.exists_away_subalgebra_embedding ..)
end GlobalTheory
