-- Prove2me | solution 1 for OAI.Thorp.Young.choose_le_extensions_split
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:04:15.576984+00:00
-- url     : https://prove2.me/submissions/23a504ec-7473-4185-83ae-f133bb55fe7e

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean:L93-L150
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Young.choose_le_extensions_split. The node keeps its source
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

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma choose_le_extensions_split (s : Set A)
    (hs : ∀ x y : A, x < y → (x ∈ s ↔ y ∈ s)) :
    (Fintype.card A).choose (Fintype.card s) ≤ Fintype.card (Extensions A) := by
  obtain ⟨a⟩ := extensions_nonempty s
  obtain ⟨b⟩ := extensions_nonempty (sᶜ : Set A)
  let I := {S : Finset (Fin (Fintype.card A)) // S.card = Fintype.card s}
  have hi : Fintype.card I = (Fintype.card A).choose (Fintype.card s) := by
    calc
      Fintype.card I = ((Finset.univ : Finset (Fin (Fintype.card A))).powersetCard (Fintype.card s)).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext S
        simp
      _ = _ := by rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  let P (S : I) : Set (Fin (Fintype.card A)) := S.val
  have hP (S : I) : Fintype.card (P S) = Fintype.card s := by
    simpa [P] using S.property
  have hC (S : I) : Fintype.card ((P S)ᶜ : Set (Fin (Fintype.card A))) =
      Fintype.card (sᶜ : Set A) := by
    have h₁ := Fintype.card_congr (Equiv.Set.sumCompl (P S))
    have h₂ := Fintype.card_congr (Equiv.Set.sumCompl s)
    simp only [Fintype.card_sum, Fintype.card_fin, hP] at h₁ h₂
    omega
  let ea (S : I) := (Fintype.orderIsoFinOfCardEq (P S) (hP S))
  let eb (S : I) := (Fintype.orderIsoFinOfCardEq ((P S)ᶜ : Set _) (hC S))
  let F (S : I) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans
      (Equiv.sumCongr (a.val.trans (ea S).toEquiv) (b.val.trans (eb S).toEquiv))).trans
        (Equiv.Set.sumCompl (P S))
  have hFa (S : I) (x : s) : F S x = (ea S (a.val x)).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFb (S : I) (x : (sᶜ : Set A)) : F S x = (eb S (b.val x)).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hFm (S : I) (x : A) : F S x ∈ P S ↔ x ∈ s := by
    by_cases hx : x ∈ s
    · rw [hFa S ⟨x, hx⟩]
      exact iff_of_true (ea S (a.val ⟨x, hx⟩)).property hx
    · rw [hFb S ⟨x, hx⟩]
      exact iff_of_false (eb S (b.val ⟨x, hx⟩)).property hx
  have hF (S : I) : StrictMono (F S) := by
    intro x y hxy
    by_cases hx : x ∈ s
    · have hy := (hs x y hxy).mp hx
      rw [hFa S ⟨x, hx⟩, hFa S ⟨y, hy⟩]
      exact (ea S).strictMono (a.property hxy)
    · have hy : y ∉ s := fun h => hx ((hs x y hxy).mpr h)
      rw [hFb S ⟨x, hx⟩, hFb S ⟨y, hy⟩]
      exact (eb S).strictMono (b.property hxy)
  let f (S : I) : Extensions A := ⟨F S, hF S⟩
  rw [← hi]
  apply Fintype.card_le_of_injective f
  intro S T hST
  apply Subtype.ext
  ext z
  obtain ⟨x, rfl⟩ := (F S).surjective z
  have he : F S x = F T x := congrArg (fun e : Extensions A => e.val x) hST
  change F S x ∈ P S ↔ F S x ∈ P T
  rw [hFm, he, hFm]

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


theorem solution.{uA} : type_of% @_root_.OAI.Thorp.Young.choose_le_extensions_split.{uA} := @_root_.OAI.Thorp.Young.choose_le_extensions_split.{uA}
