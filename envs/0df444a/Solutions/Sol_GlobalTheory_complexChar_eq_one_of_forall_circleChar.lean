-- Prove2me | solution 1 for GlobalTheory.complexChar_eq_one_of_forall_circleChar
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:05:23.641944+00:00
-- url     : https://prove2.me/submissions/b12a7384-09b0-4834-b2f5-ce288fc1e488

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ComplexCharEqOneOfForallCircleChar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
theorem _root_.solution :
    ∀ {G : Type} [Group G] (ν : G →* ℂˣ) (x : G),
      (∀ μ : G →* Circle, (∀ g, ν g = 1 → μ g = 1) → μ x = 1) → ν x = 1 := by
  intro G _ ν x h
  by_contra hne
  set A := ν.range with hA
  set a : A := ⟨ν x, x, rfl⟩ with ha
  have ha1 : Additive.ofMul a ≠ 0 := by
    intro h0
    apply hne
    have : a = 1 := congrArg Additive.toMul h0
    exact congrArg Subtype.val this
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha1
  -- push ℚ/ℤ into the circle, injectively
  have hmap : ∀ z : ℤ, ((Rat.castHom ℝ).toAddMonoidHom) ((zmultiplesHom ℚ 1) z) ∈ AddSubgroup.zmultiples (1 : ℝ) := by
    intro z
    exact ⟨z, by simp⟩
  set ψ : AddCircle (1:ℚ) →+ AddCircle (1:ℝ) :=
    QuotientAddGroup.map (AddSubgroup.zmultiples (1:ℚ)) (AddSubgroup.zmultiples (1:ℝ)) (Rat.castHom ℝ).toAddMonoidHom (by
      rintro q ⟨z, rfl⟩
      exact ⟨z, by simp⟩) with hψ
  have hψinj : ∀ q : AddCircle (1:ℚ), ψ q = 0 → q = 0 := by
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H q =>
      intro hq
      have : ((q : ℝ) : AddCircle (1:ℝ)) = 0 := hq
      obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).1 this
      refine (AddCircle.coe_eq_zero_iff (1:ℚ)).2 ⟨z, ?_⟩
      have : ((z : ℚ) : ℝ) = (q : ℝ) := by simpa using hz
      have : (z : ℚ) = q := by exact_mod_cast this
      simpa using this
  set μ : G →* Circle :=
    { toFun := fun g => AddCircle.toCircle (ψ (c (Additive.ofMul (⟨ν g, g, rfl⟩ : A))))
      map_one' := by
        have e : Additive.ofMul (⟨ν 1, 1, rfl⟩ : A) = 0 := by
          apply Additive.toMul.injective
          exact Subtype.ext (map_one ν)
        rw [e, map_zero, map_zero, AddCircle.toCircle_zero]
      map_mul' := fun g1 g2 => by
        have e : Additive.ofMul (⟨ν (g1*g2), g1*g2, rfl⟩ : A)
            = Additive.ofMul (⟨ν g1, g1, rfl⟩ : A) + Additive.ofMul (⟨ν g2, g2, rfl⟩ : A) := by
          apply Additive.toMul.injective
          exact Subtype.ext (map_mul ν g1 g2)
        rw [e, map_add, map_add, AddCircle.toCircle_add] } with hμ
  have hker : ∀ g, ν g = 1 → μ g = 1 := by
    intro g hg
    have e : Additive.ofMul (⟨ν g, g, rfl⟩ : A) = 0 := by
      apply Additive.toMul.injective
      exact Subtype.ext hg
    show AddCircle.toCircle (ψ (c (Additive.ofMul (⟨ν g, g, rfl⟩ : A)))) = 1
    rw [e, map_zero, map_zero, AddCircle.toCircle_zero]
  have h1 := h μ hker
  have h2 : AddCircle.toCircle (ψ (c (Additive.ofMul a))) = AddCircle.toCircle (0 : AddCircle (1:ℝ)) := by
    rw [AddCircle.toCircle_zero]; exact h1
  have h3 := AddCircle.injective_toCircle (one_ne_zero) h2
  exact hc (hψinj _ h3)

