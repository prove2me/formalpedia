-- Prove2me | solution 1 for OAI.Thorp.Young.choose_row_le_extensions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T05:05:48.507725+00:00
-- url     : https://prove2.me/submissions/b80ad055-af31-4900-9ca3-85abf2552006

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/ExtensionBounds.lean:L192-L231
-- (upload_full_project.md Phase 4): solution for node OAI.Thorp.Young.choose_row_le_extensions. The node keeps its source
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
import Theorems.Thm_OAI_Thorp_Young_choose_le_extensions_split

-- ---- from OAI.Probability.ThorpShuffle.ExtensionBounds ----
namespace OAI

universe uA

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

lemma extensions_card_compl_ideal (s : Set A) (hs : IsLowerSet s) :
    Fintype.card (Extensions (sᶜ : Set A)) ≤ Fintype.card (Extensions A) := by
  obtain ⟨a⟩ := extensions_nonempty s
  have hc : Fintype.card s + Fintype.card (sᶜ : Set A) = Fintype.card A := by
    simpa only [Fintype.card_sum] using Fintype.card_congr (Equiv.Set.sumCompl s)
  let F (e : Extensions (sᶜ : Set A)) : A ≃ Fin (Fintype.card A) :=
    ((Equiv.Set.sumCompl s).symm.trans (Equiv.sumCongr a.val e.val)).trans
      (finSumFinEquiv.trans (finCongr hc))
  have hFs (e : Extensions (sᶜ : Set A)) (x : s) : (F e x).val = (a.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_mem x.property]
  have hFc (e : Extensions (sᶜ : Set A)) (x : (sᶜ : Set A)) :
      (F e x).val = Fintype.card s + (e.val x).val := by
    simp [F, Equiv.Set.sumCompl_symm_apply_of_notMem x.property]
  have hF (e : Extensions (sᶜ : Set A)) : StrictMono (F e) := by
    intro x y hxy
    change (F e x).val < (F e y).val
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [hFs e ⟨x, hx⟩, hFs e ⟨y, hy⟩]
      exact a.property hxy
    · rw [hFs e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact (a.val ⟨x, hx⟩).isLt.trans_le (Nat.le_add_right _ _)
    · exact False.elim (hx (hs hxy.le hy))
    · rw [hFc e ⟨x, hx⟩, hFc e ⟨y, hy⟩]
      exact Nat.add_lt_add_left (e.property hxy) _
  let f (e : Extensions (sᶜ : Set A)) : Extensions A := ⟨F e, hF e⟩
  apply Fintype.card_le_of_injective f
  intro e d hed
  apply Subtype.ext
  apply Equiv.ext
  intro x
  apply Fin.ext
  have hh := congrArg (fun z : Extensions A => (z.val x).val) hed
  change (F e x).val = (F d x).val at hh
  have h := congrArg (fun z : ℕ => z - Fintype.card s) hh
  simpa only [hFc, Nat.add_sub_cancel_left] using h

end Thorp.Young

namespace Thorp.Young
open scoped Classical
variable {A : Type uA} [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Young
open scoped Classical

lemma topPrefix_lower (D : YoungDiagram) (u : ℕ) : IsLowerSet (topPrefix D u) := by
  intro y x hxy hy
  change y.val.1 = 0 ∧ y.val.2 < u at hy
  change x.val.1 = 0 ∧ x.val.2 < u
  exact ⟨by have := hxy.1; omega, lt_of_le_of_lt hxy.2 hy.2⟩

lemma card_topPrefix (D : YoungDiagram) (u : ℕ) (hu : u ≤ D.rowLen 0) :
    Fintype.card (topPrefix D u) = u := by
  let e : topPrefix D u ≃ Fin u := {
    toFun := fun x => ⟨x.val.val.2, x.property.2⟩
    invFun := fun j => ⟨⟨(0, j), YoungDiagram.mem_iff_lt_rowLen.mpr (j.isLt.trans_le hu)⟩, rfl, j.isLt⟩
    left_inv := by intro x; apply Subtype.ext; apply Subtype.ext; exact Prod.ext x.property.1.symm rfl
    right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (Fintype.card_fin u)

lemma card_lower_add (D : YoungDiagram) :
    D.rowLen 0 + Fintype.card (Lower D) = Fintype.card (Cells D) := by
  have h := Fintype.card_congr (Equiv.sumCompl (fun x : Cells D => x.val.1 = 0))
  simpa only [Fintype.card_sum, card_row_subtype] using h

lemma lower_col_lt (D : YoungDiagram) (x : Lower D) : x.val.val.2 < Fintype.card (Lower D) := by
  let f : Fin (x.val.val.2 + 1) → Lower D := fun j =>
    ⟨⟨(1, j), D.up_left_mem (i2 := x.val.val.1) (j2 := x.val.val.2) (by have := x.property; omega) (by have := j.isLt; omega) x.val.property⟩, by simp⟩
  have hf : Function.Injective f := by
    intro j k hjk
    exact Fin.ext (congrArg (fun z : Lower D => z.val.val.2) hjk)
  have hh := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hh
  omega

theorem choose_row_le_extensions (D : YoungDiagram)
    (hu : Fintype.card (Lower D) ≤ D.rowLen 0) :
    (D.rowLen 0).choose (Fintype.card (Lower D)) ≤ Fintype.card (Extensions (Cells D)) := by
  let u := Fintype.card (Lower D)
  let s := topPrefix D u
  let A := (sᶜ : Set (Cells D))
  let r : Set A := {x | x.val.val.1 ≠ 0}
  have hc : Fintype.card A = D.rowLen 0 := by
    have hh := Fintype.card_congr (Equiv.Set.sumCompl s)
    simp only [Fintype.card_sum] at hh
    have hs : Fintype.card s = u := card_topPrefix D u hu
    have hl := card_lower_add D
    change D.rowLen 0 + u = Fintype.card (Cells D) at hl
    change Fintype.card s + Fintype.card A = Fintype.card (Cells D) at hh
    omega
  let e : r ≃ Lower D := {
    toFun := fun x => ⟨x.val.val, x.property⟩
    invFun := fun x => ⟨⟨x.val, fun h => x.property h.1⟩, x.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hr : Fintype.card r = u := Fintype.card_congr e
  have hsplit : ∀ x y : A, x < y → (x ∈ r ↔ y ∈ r) := by
    intro x y hxy
    have h₁ := hxy.le.1
    have h₂ := hxy.le.2
    change x.val.val.1 ≠ 0 ↔ y.val.val.1 ≠ 0
    constructor
    · intro hx hy; exact hx (by omega)
    · intro hy hx
      have hcol := lower_col_lt D ⟨y.val, hy⟩
      have hp := x.property
      change ¬(x.val.val.1 = 0 ∧ x.val.val.2 < u) at hp
      change y.val.val.2 < u at hcol
      exact hp ⟨hx, lt_of_le_of_lt h₂ hcol⟩
  have hh := choose_le_extensions_split r hsplit
  have hrN : Nat.card r = u := by simpa only [Fintype.card_eq_nat_card] using hr
  have hcN : Nat.card A = D.rowLen 0 := by simpa only [Fintype.card_eq_nat_card] using hc
  have hh' : (D.rowLen 0).choose u ≤ Fintype.card (Extensions A) := by
    simpa only [Fintype.card_eq_nat_card, hrN, hcN] using hh
  exact hh'.trans (extensions_card_compl_ideal s (topPrefix_lower D u))

end Thorp.Young

end

end OAI

-- ---- platform node ----
open OAI OAI.Thorp OAI.Thorp.Young
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter
open scoped Classical


theorem solution : type_of% @_root_.OAI.Thorp.Young.choose_row_le_extensions := @_root_.OAI.Thorp.Young.choose_row_le_extensions
