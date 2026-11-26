-- Prove2me | solution 1 for KrohnRhodes.sgdiv_of_covering
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:32.791655+00:00
-- url     : https://prove2.me/submissions/21f73745-4e80-4d01-8983-e2af315f7e8f

module
public import Definitions.Def_KrohnRhodes_Defs
public import Mathlib
public import Definitions.Def_KrohnRhodes_Foundations_WreathProduct
public import Definitions.Def_KrohnRhodes_Foundations_LocalDivisor
public import Definitions.Def_KrohnRhodes_Foundations_ConstantMaps
public import Definitions.Def_KrohnRhodes_Foundations_Division
public import Definitions.Def_KrohnRhodes_Foundations_MonoidWreathBridge
public import Definitions.Def_KrohnRhodes_Foundations_KrasnerKaloujnine
public import Definitions.Def_KrohnRhodes_FactorTower
public import Definitions.Def_KrohnRhodes_PrimeDecomposition
public import Theorems.Thm_KrohnRhodes_covers_one
public import Theorems.Thm_KrohnRhodes_covers_mul
public import Theorems.Thm_KrohnRhodes_covers_unique

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedFintypeInType false
open KrohnRhodes
open Green
namespace KrohnRhodes
theorem _root_.solution {A B P X R : Type} [Monoid A] [Monoid B] [MulAction A P]
    [MulAction B X] {φ : P × X → R} (_hφ : Function.Surjective φ)
    (S : Set (Function.End R)) (T : Submonoid (Function.End R))
    (_hgen : Submonoid.closure S = T)
    (_hcov : ∀ t ∈ S, ∃ w : WreathProduct A B X, Covers φ w t) :
    SgDiv ↥T (WreathProduct A B X) := by
  classical
  -- Step 1: every element of `T = ⟨S⟩` is covered by some wreath element.
  have hcovT : ∀ t ∈ T, ∃ w : WreathProduct A B X, Covers φ w t := by
    intro t ht
    rw [← _hgen] at ht
    induction ht using Submonoid.closure_induction with
    | mem x hx => exact _hcov x hx
    | one => exact ⟨1, covers_one φ⟩
    | mul x y _ _ ihx ihy =>
      obtain ⟨wx, hwx⟩ := ihx
      obtain ⟨wy, hwy⟩ := ihy
      exact ⟨wx * wy, covers_mul φ hwx hwy⟩
  -- Step 2: the subsemigroup `V` of wreath elements covering some member of `T`.
  let V : Subsemigroup (WreathProduct A B X) :=
    { carrier := {w : WreathProduct A B X | ∃ t ∈ T, Covers φ w t}
      mul_mem' := by
        rintro w₁ w₂ ⟨t₁, ht₁, hc₁⟩ ⟨t₂, ht₂, hc₂⟩
        exact ⟨t₁ * t₂, mul_mem ht₁ ht₂, covers_mul φ hc₁ hc₂⟩ }
  -- Step 3: the decoded transformation of a member of `V` (choice; unique by
  -- `covers_unique` since `φ` is surjective).
  have hmem : ∀ w : ↥V, ∃ t ∈ T, Covers φ (w : WreathProduct A B X) t := fun w => w.2
  have hdecC : ∀ w : ↥V,
      Covers φ (w : WreathProduct A B X) (Classical.choose (hmem w)) :=
    fun w => (Classical.choose_spec (hmem w)).2
  refine ⟨V,
    ⟨fun w => ⟨Classical.choose (hmem w), (Classical.choose_spec (hmem w)).1⟩, ?_⟩, ?_⟩
  · -- Multiplicativity: both sides cover `↑w₁ * ↑w₂`, so they agree by uniqueness.
    intro w₁ w₂
    exact Subtype.ext (covers_unique _hφ (hdecC (w₁ * w₂))
      (covers_mul φ (hdecC w₁) (hdecC w₂)))
  · -- Surjectivity: a `t ∈ T` is covered by some `w` (Step 1); `w ∈ V`, and the decoded
    -- transformation of `w` is `t` by uniqueness.
    rintro ⟨t, ht⟩
    obtain ⟨w, hw⟩ := hcovT t ht
    have hwV : w ∈ V := ⟨t, ht, hw⟩
    exact ⟨⟨w, hwV⟩, Subtype.ext (covers_unique _hφ (hdecC ⟨w, hwV⟩) hw)⟩
end KrohnRhodes
