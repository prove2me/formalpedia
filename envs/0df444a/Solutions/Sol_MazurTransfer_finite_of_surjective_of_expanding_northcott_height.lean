-- Prove2me | solution 1 for MazurTransfer.finite_of_surjective_of_expanding_northcott_height
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-16T19:37:28.901036+00:00
-- url     : https://prove2.me/submissions/84c08b64-b984-4814-b4f3-6b83644e9899

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a surjective self-map with an expanding Northcott height
forces a finite point set. Named downstream consumer: finiteness of the
original rational Picard group from its proved π-surjectivity, once an
actual expanding height on that SAME group is constructed. -/
import Mathlib.Order.Northcott
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

noncomputable section
namespace MazurTransfer.FiniteOfSurjectiveExpandingHeight
open Function
universe u
variable {X : Type u} (h : X → ℝ) (f : X → X)

theorem finite_of_surjective_of_expanding_height [Northcott h]
    (a C : ℝ) (ha : 1 < a) (hg : ∀ x, a * h x - C ≤ h (f x))
    (hf : Function.Surjective f) : Finite X := by
  classical
  let B := C / (a - 1)
  have hB : (a - 1) * B = C := mul_div_cancel₀ C (ne_of_gt (sub_pos.mpr ha))
  have hpre (b : ℝ) (hb : B ≤ b) (x : X) (hx : h (f x) ≤ b) : h x ≤ b := by
    have hCb : C ≤ (a - 1) * b := hB.symm.le.trans (mul_le_mul_of_nonneg_left hb (by linarith))
    nlinarith [hg x]
  have hbound (x : X) : h x ≤ B := by
    let b := max B (h x)
    let S := {y : X | h y ≤ b}
    have hS : S.Finite := Northcott.finite_le b
    letI : Finite S := hS.to_subtype
    let g : S → S := fun y =>
      ⟨surjInv hf y.val, hpre b (le_max_left _ _) _
        ((congrArg h (surjInv_eq hf y.val)).trans_le y.property)⟩
    have hginj : Function.Injective g := by
      intro y z hyz
      apply Subtype.ext
      exact (surjInv_eq hf y.val).symm.trans
        ((congrArg f (congrArg Subtype.val hyz)).trans (surjInv_eq hf z.val))
    have hgsurj := Finite.surjective_of_injective hginj
    have hforward (y : S) : f y.val ∈ S := by
      obtain ⟨z, hz⟩ := hgsurj y
      have he : f y.val = z.val :=
        (congrArg f (congrArg Subtype.val hz)).symm.trans (surjInv_eq hf z.val)
      exact (congrArg h he).trans_le z.property
    have hxS : x ∈ S := show h x ≤ max B (h x) from le_max_right _ _
    obtain ⟨y, hy, hymax⟩ := Set.exists_max_image S h hS ⟨x, hxS⟩
    have hfmax : h (f y) ≤ h y := hymax _ (hforward ⟨y, hy⟩)
    have hyB : h y ≤ B := by nlinarith [hg y]
    exact (hymax x hxS).trans hyB
  letI : Finite {x : X | h x ≤ B} := (Northcott.finite_le B).to_subtype
  exact Finite.of_injective (fun x : X => (⟨x, hbound x⟩ : {x : X | h x ≤ B}))
    (fun _ _ e => congrArg Subtype.val e)

end MazurTransfer.FiniteOfSurjectiveExpandingHeight
universe u
theorem solution {X : Type u} (h : X → ℝ) (f : X → X) [Northcott h]
    (a C : ℝ) (ha : 1 < a) (hg : ∀ x, a * h x - C ≤ h (f x))
    (hf : Function.Surjective f) : Finite X :=
  MazurTransfer.FiniteOfSurjectiveExpandingHeight.finite_of_surjective_of_expanding_height h f a C ha hg hf
#print axioms solution
