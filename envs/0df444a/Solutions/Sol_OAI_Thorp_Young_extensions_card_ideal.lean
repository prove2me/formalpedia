-- Prove2me | solution 1 for OAI.Thorp.Young.extensions_card_ideal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:59:52.113191+00:00
-- url     : https://prove2.me/submissions/d584de61-746a-4b58-b042-e959b4d0150d

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean:L16-L49
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Young.extensions_card_ideal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds

-- ---- from OAI.Probability.ThorpShuffle.ExtensionBounds ----
namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma extensions_card_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions s) ≤ Fintype.card (Extensions A) := by
  obtain ⟨c⟩ := extensions_nonempty (sᶜ : Set A)
  have hc : Fintype.card s + Fintype.card (sᶜ : Set A) = Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.Set.sumCompl s)
  let F (e : Extensions s) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumCongr e.val c.val)).trans
      (finSumFinEquiv.trans (finCongr hc))
  have hFs (e : Extensions s) (x : s) : (F e x).val = (e.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFc (e : Extensions s) (x : (sᶜ : Set A)) :
      (F e x).val = Fintype.card s + (c.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hF (e : Extensions s) : StrictMono (F e) := by
    intro x y hxy
    change (F e x).val < (F e y).val
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [hFs e ⟨x, hx⟩, hFs e ⟨y, hy⟩]
      exact e.property hxy
    · rw [hFs e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact (e.val ⟨x, hx⟩).isLt.trans_le (Nat.le_add_right _ _)
    · exact False.elim (hx (hs hxy.le hy))
    · rw [hFc e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact Nat.add_lt_add_left (c.property hxy) _
  let f (e : Extensions s) : Extensions A := ⟨F e, hF e⟩
  apply Fintype.card_le_of_injective f
  intro e d hed
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hh := congrArg (fun z : Extensions A => (z.val x).val) hed
  change (F e x).val = (F d x).val at hh
  simpa only [hFs] using hh

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

end Thorp.Young

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Young
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical


theorem solution.{uA} : type_of% @_root_.OAI.Thorp.Young.extensions_card_ideal.{uA} := @_root_.OAI.Thorp.Young.extensions_card_ideal.{uA}
