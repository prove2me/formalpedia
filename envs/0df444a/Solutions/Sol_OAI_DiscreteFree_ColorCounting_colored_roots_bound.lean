-- Prove2me | solution 1 for OAI.DiscreteFree.ColorCounting.colored_roots_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T10:52:37.172684+00:00
-- url     : https://prove2.me/submissions/640b963a-83b7-43e7-87ce-2797cb98e16f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/LipschitzFree/ColorCounting.lean:L137-L155
-- (upload_full_project.md Phase 4): solution for node OAI.DiscreteFree.ColorCounting.colored_roots_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DiscreteLipschitzFree
import Definitions.Def_OAI_Analysis_LipschitzFree_PortGraphs
import Definitions.Def_OAI_Analysis_LipschitzFree_RenormingModel
import Definitions.Def_OAI_Analysis_LipschitzFree_Model
import Definitions.Def_OAI_Analysis_LipschitzFree_Parameters
import Definitions.Def_OAI_Analysis_LipschitzFree_BoxLabels
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricClosure
import Definitions.Def_OAI_Analysis_LipschitzFree_MetricBlock
import Definitions.Def_OAI_Analysis_LipschitzFree_Attachment
import Definitions.Def_OAI_Analysis_LipschitzFree_Words
import Definitions.Def_OAI_Analysis_LipschitzFree_StatePaths
import Definitions.Def_OAI_Analysis_LipschitzFree_SignedTests
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphWalks
import Definitions.Def_OAI_Analysis_LipschitzFree_Evaluation
import Definitions.Def_OAI_Analysis_LipschitzFree_Coordinates
import Definitions.Def_OAI_Analysis_LipschitzFree_AffineWeights
import Definitions.Def_OAI_Analysis_LipschitzFree_LabelBumps
import Definitions.Def_OAI_Analysis_LipschitzFree_ScalarTests
import Definitions.Def_OAI_Analysis_LipschitzFree_FiniteQuotients
import Definitions.Def_OAI_Analysis_LipschitzFree_GraphGirth
import Definitions.Def_OAI_Analysis_LipschitzFree_ColorCounting

-- ---- from OAI.Analysis.LipschitzFree.ColorCounting ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Counting colorings subject to vertex constraints
-/

noncomputable section
open scoped BigOperators ENNReal

namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

variable {X I C : Type*}

theorem cardinal_identity [Fintype X] [Fintype I] [Fintype C]
    (f : I → X) (hf : Function.Injective f) (P : I → Finset C) :
    Fintype.card {c : X → C // ∀ i, c (f i) ∈ P i} *
        Fintype.card C ^ Fintype.card I =
      (∏ i, (P i).card) * Fintype.card (X → C) := by
  classical
  have hg := Fintype.card_congr (goodColoringEquiv f hf (fun i c => c ∈ P i))
  have hp := Fintype.card_congr
    (Equiv.subtypePiEquivPi (p := fun i c => c ∈ P i))
  simp only [Fintype.card_pi, Fintype.card_coe] at hp
  simp only [Fintype.card_prod, hp, Fintype.card_fun] at hg
  have ht := Fintype.card_congr (coloringEquiv (C := C) f hf)
  simp only [Fintype.card_prod, Fintype.card_fun] at ht
  rw [hg, Fintype.card_fun, ht]
  ring

theorem cardinal_bound [Fintype X] [Fintype I] [Fintype C]
    (f : I → X) (hf : Function.Injective f) (P : I → Finset C)
    (H : ℕ) (hH : ∀ i, (P i).card ≤ H) :
    Fintype.card {c : X → C // ∀ i, c (f i) ∈ P i} *
        Fintype.card C ^ Fintype.card I ≤
      H ^ Fintype.card I * Fintype.card (X → C) := by
  classical
  rw [cardinal_identity f hf P]
  apply Nat.mul_le_mul_right
  simpa using Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
    (fun index (_ : index ∈ (Finset.univ : Finset I)) => hH index)

end DiscreteFree.ColorCounting

noncomputable section
namespace DiscreteFree.ColorCounting
open scoped BigOperators Classical

theorem union_bound {X P : Type*} [Fintype X] [Fintype P] (r : P → X → Prop) :
    Fintype.card {x : X // ∃ p, r p x} ≤ ∑ p, Fintype.card {x : X // r p x} := by
  let f : (Σ p : P, {x : X // r p x}) → {x : X // ∃ p, r p x} :=
    fun z => ⟨z.2.val, z.1, z.2.property⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, p, hp⟩
    exact ⟨⟨p, x, hp⟩, rfl⟩
  simpa only [Fintype.card_sigma] using Fintype.card_le_of_surjective f hf

theorem weighted_union_bound {X P : Type*} [Fintype X] [Fintype P]
    (r : P → X → Prop) (a b : ℕ)
    (h : ∀ p, Fintype.card {x : X // r p x} * a ≤ b) :
    Fintype.card {x : X // ∃ p, r p x} * a ≤ Fintype.card P * b := by
  calc
    _ ≤ (∑ p, Fintype.card {x : X // r p x}) * a :=
      Nat.mul_le_mul_right _ (union_bound r)
    _ = ∑ p, Fintype.card {x : X // r p x} * a := Finset.sum_mul _ _ _
    _ ≤ ∑ _p : P, b := Finset.sum_le_sum (fun p _ => h p)
    _ = _ := by simp

theorem many_walks_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : W → I → X) (hf : ∀ w, Function.Injective (f w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {c : X → C // ∃ w s, ∀ i, c (f w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card (X → C) := by
  have h := weighted_union_bound
    (fun ws : W × S => fun c : X → C => ∀ i, c (f ws.1 i) ∈ P ws.2 i)
    (Fintype.card C ^ Fintype.card I) (H ^ Fintype.card I * Fintype.card (X → C))
    (fun ws => by
      convert cardinal_bound (f ws.1) (hf ws.1) (P ws.2) H (hH ws.2) using 1
      simp only [← Nat.card_eq_fintype_card])
  simp only [Prod.exists, Fintype.card_prod] at h
  exact h.trans_eq (by ring)

theorem colored_roots_bound {X W I S C : Type*}
    [Fintype X] [Fintype W] [Fintype I] [Fintype S] [Fintype C]
    (f : X → W → I → X) (hf : ∀ x w, Function.Injective (f x w))
    (P : S → I → Finset C) (H : ℕ) (hH : ∀ s i, (P s i).card ≤ H) :
    Fintype.card {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} *
        Fintype.card C ^ Fintype.card I ≤
      Fintype.card W * Fintype.card S * H ^ Fintype.card I * Fintype.card ((X → C) × X) := by
  let e : {z : (X → C) × X // ∃ w s, ∀ i, z.1 (f z.2 w i) ∈ P s i} ≃
      Σ x : X, {c : X → C // ∃ w s, ∀ i, c (f x w i) ∈ P s i} :=
    { toFun := fun z => ⟨z.val.2, z.val.1, z.property⟩
      invFun := fun z => ⟨(z.2.val, z.1), z.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma, Finset.sum_mul]
  calc
    _ ≤ ∑ _x : X, Fintype.card W * Fintype.card S * H ^ Fintype.card I *
        Fintype.card (X → C) :=
      Finset.sum_le_sum (fun x _ => many_walks_bound (f x) (hf x) P H hH)
    _ = _ := by simp; ring

end DiscreteFree.ColorCounting
end

end

end OAI

-- ---- platform node ----
open OAI OAI.DiscreteFree OAI.DiscreteFree.ColorCounting
open scoped BigOperators ENNReal
open scoped BigOperators Classical


theorem solution : type_of% @_root_.OAI.DiscreteFree.ColorCounting.colored_roots_bound := @_root_.OAI.DiscreteFree.ColorCounting.colored_roots_bound
