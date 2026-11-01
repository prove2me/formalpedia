-- Prove2me | solution 1 for Grunbaum2003.skeletonFace_zero_orderIso_of_exposed_vertices_equiv
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T22:17:25.016753+00:00
-- url     : https://prove2.me/submissions/860ac39d-5154-4a58-9d78-cebda4400d64

import Definitions.Def_Grunbaum2003_SkeletonFace
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Logic.Equiv.Option
import Mathlib.Order.Hom.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Grunbaum2003

def skeletonFaceZeroFromOption {d : ℕ} (P : Set (Fin d → ℝ)) :
    Option {x : Fin d → ℝ | IsExposed ℝ P {x}} → SkeletonFace P 0
  | none => ⟨⟨∅, fun h => (Set.not_nonempty_empty h).elim⟩, Or.inl rfl⟩
  | some v =>
    ⟨⟨{v.val}, v.2⟩,
      Or.inr (by rw [direction_affineSpan, vectorSpan_singleton, finrank_bot])⟩

theorem skeletonFaceZeroFromOption_le_iff {d : ℕ} (P : Set (Fin d → ℝ))
    (a b : Option {x : Fin d → ℝ | IsExposed ℝ P {x}}) :
    skeletonFaceZeroFromOption P a ≤ skeletonFaceZeroFromOption P b ↔ a = none ∨ a = b := by
  cases a with
  | none =>
    simp [skeletonFaceZeroFromOption]
    exact Set.empty_subset _
  | some v₁ =>
    cases b with
    | none =>
      simp [skeletonFaceZeroFromOption]
      change ¬({v₁.val} : Set (Fin d → ℝ)) ⊆ ∅
      simp
    | some v₂ =>
      simp only [skeletonFaceZeroFromOption, reduceCtorEq, Option.some.injEq, false_or]
      change ({v₁.val} : Set (Fin d → ℝ)) ⊆ {v₂.val} ↔ v₁ = v₂
      rw [Set.singleton_subset_iff, Set.mem_singleton_iff, Subtype.ext_iff]

theorem skeletonFaceZeroFromOption_bijective {d : ℕ} (P : Set (Fin d → ℝ)) :
    Function.Bijective (skeletonFaceZeroFromOption P) := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    have h1 : skeletonFaceZeroFromOption P a ≤ skeletonFaceZeroFromOption P b := hab.le
    have h2 : skeletonFaceZeroFromOption P b ≤ skeletonFaceZeroFromOption P a := hab.ge
    rw [skeletonFaceZeroFromOption_le_iff] at h1 h2
    rcases h1 with rfl | h1
    · rcases h2 with rfl | h2
      · rfl
      · exact h2.symm
    · exact h1
  · intro S
    rcases S.val.val.eq_empty_or_nonempty with hEmp | ⟨x, hx⟩
    · refine ⟨none, ?_⟩
      exact Subtype.ext (Subtype.ext hEmp.symm)
    · have hdim : Module.finrank ℝ (affineSpan ℝ S.val.val).direction = 0 := by
        rcases S.2 with hEmp | hle
        · exact (hEmp ▸ hx).elim
        · exact Nat.eq_zero_of_le_zero hle
      have hsub : Subsingleton (affineSpan ℝ S.val.val).direction :=
        Module.finrank_zero_iff.mp hdim
      have hEq : S.val.val = {x} := by
        ext y
        simp only [Set.mem_singleton_iff]
        constructor
        · intro hy
          have hyx : y - x ∈ (affineSpan ℝ S.val.val).direction := by
            rw [direction_affineSpan]
            exact vsub_mem_vectorSpan ℝ hy hx
          exact sub_eq_zero.mp (congr_arg Subtype.val (@Subsingleton.elim _ hsub ⟨y - x, hyx⟩ 0))
        · rintro rfl
          exact hx
      have hx_exp : IsExposed ℝ P {x} := hEq ▸ S.val.2
      refine ⟨some ⟨x, hx_exp⟩, ?_⟩
      exact Subtype.ext (Subtype.ext hEq.symm)

/-- Grünbaum (2003), §3.1 & §4.9 (p. 69b): any bijection between the sets of exposed
vertices of `P` and `Q` induces an order isomorphism between their `0`-skeletons
`SkeletonFace P 0` and `SkeletonFace Q 0`. -/
theorem skeletonFace_zero_orderIso_of_exposed_vertices_equiv (d₁ d₂ : ℕ)
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (e : {x : Fin d₁ → ℝ | IsExposed ℝ P {x}} ≃ {y : Fin d₂ → ℝ | IsExposed ℝ Q {y}}) :
    Nonempty (SkeletonFace P 0 ≃o SkeletonFace Q 0) := by
  let eP := Equiv.ofBijective (skeletonFaceZeroFromOption P)
    (skeletonFaceZeroFromOption_bijective P)
  let eQ := Equiv.ofBijective (skeletonFaceZeroFromOption Q)
    (skeletonFaceZeroFromOption_bijective Q)
  let eqv := eP.symm.trans ((Equiv.optionCongr e).trans eQ)
  refine ⟨{
    toEquiv := eqv
    map_rel_iff' := by
      intro S₁ S₂
      obtain ⟨a, rfl⟩ := eP.surjective S₁
      obtain ⟨b, rfl⟩ := eP.surjective S₂
      change eQ (Equiv.optionCongr e (eP.symm (eP a))) ≤
          eQ (Equiv.optionCongr e (eP.symm (eP b))) ↔
        eP a ≤ eP b
      rw [eP.symm_apply_apply, eP.symm_apply_apply]
      change skeletonFaceZeroFromOption Q (Equiv.optionCongr e a) ≤
          skeletonFaceZeroFromOption Q (Equiv.optionCongr e b) ↔
        skeletonFaceZeroFromOption P a ≤ skeletonFaceZeroFromOption P b
      rw [skeletonFaceZeroFromOption_le_iff, skeletonFaceZeroFromOption_le_iff]
      have hNone : Equiv.optionCongr e a = none ↔ a = none := by
        change Equiv.optionCongr e a = Equiv.optionCongr e none ↔ a = none
        exact (Equiv.optionCongr e).apply_eq_iff_eq
      rw [hNone, (Equiv.optionCongr e).apply_eq_iff_eq]
  }⟩

end Grunbaum2003

theorem solution (d₁ d₂ : ℕ)
    (P : Set (Fin d₁ → ℝ)) (Q : Set (Fin d₂ → ℝ))
    (e : {x : Fin d₁ → ℝ | IsExposed ℝ P {x}} ≃ {y : Fin d₂ → ℝ | IsExposed ℝ Q {y}}) :
    Nonempty (Grunbaum2003.SkeletonFace P 0 ≃o Grunbaum2003.SkeletonFace Q 0) :=
  Grunbaum2003.skeletonFace_zero_orderIso_of_exposed_vertices_equiv d₁ d₂ P Q e
