-- Prove2me | solution 1 for LodhaMoore.isMuAmenable_of_isAmenableRel
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-03T21:28:29.063998+00:00
-- url     : https://prove2.me/submissions/ee446adb-e382-495b-b4b1-a5171936efa1

import Mathlib
import Definitions.Def_LodhaMoore
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_ConnesFeldmanWeiss
import Theorems.Thm_ConnesFeldmanWeiss_exists_nonsingular_generator_of_isAmenableRel

section
/-! # Statement 5: an amenable relation is `μ`-amenable, by Connes–Feldman–Weiss

The Connes–Feldman–Weiss theorem (the published goal of the CFW mission) gives a non-singular
Borel automorphism `T` of `X` and a null Borel set `N` off which `E` is the orbit relation of `T`.
Lodha–Moore's definition asks for an automorphism of `X \ N` itself, and `T` need not preserve
`X \ N`; so `N` is enlarged to its `T`-saturation `⋃ₙ T⁻ⁿ N`, which is null because `T` and `T⁻¹`
are non-singular, and `T` restricted to the complement is the automorphism. -/

namespace LodhaMoore.Dev.Stmt5

open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- The integer powers of a non-singular Borel automorphism are measurable and pull null Borel
sets back to null sets. -/
theorem zpow_measurable_and_null {μ : Measure X} (T : X ≃ᵐ X)
    (hT : ConnesFeldmanWeiss.IsNonsingular μ T) (n : ℤ) :
    Measurable ⇑(T.toEquiv ^ n) ∧
      ∀ A, MeasurableSet A → μ A = 0 → μ (⇑(T.toEquiv ^ n) ⁻¹' A) = 0 := by
  have hfwd : ∀ A, MeasurableSet A → μ A = 0 → μ (⇑T.toEquiv ⁻¹' A) = 0 :=
    fun A hA hA0 => (hT.2 A hA).2 hA0
  have hinv : Measurable ⇑(T.toEquiv)⁻¹ ∧
      ∀ A, MeasurableSet A → μ A = 0 → μ (⇑(T.toEquiv)⁻¹ ⁻¹' A) = 0 := by
    refine ⟨T.symm.measurable, fun A hA hA0 => ?_⟩
    have hpre : ⇑(T.toEquiv)⁻¹ ⁻¹' A = T '' A := by
      ext x
      constructor
      · intro hx
        exact ⟨(T.toEquiv)⁻¹ x, hx, by simp [Equiv.Perm.inv_def]⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [Equiv.Perm.inv_def] using hy
    rw [hpre]
    have hTA : MeasurableSet (T '' A) := T.measurableSet_image.2 hA
    refine (hT.2 _ hTA).1 ?_
    rwa [T.preimage_image]
  induction n using Int.induction_on with
  | zero => exact ⟨by simpa using measurable_id, fun A _ hA0 => by simpa using hA0⟩
  | succ n ih =>
    rw [zpow_add_one, Equiv.Perm.coe_mul]
    refine ⟨ih.1.comp T.measurable, fun A hA hA0 => ?_⟩
    rw [preimage_comp]
    exact hfwd _ (ih.1 hA) (ih.2 A hA hA0)
  | pred n ih =>
    rw [zpow_sub_one, Equiv.Perm.coe_mul]
    refine ⟨ih.1.comp hinv.1, fun A hA hA0 => ?_⟩
    rw [preimage_comp]
    exact hinv.2 _ (ih.1 hA) (ih.2 A hA hA0)

/-- **Statement 5** (Lodha–Moore p. 4, citing Connes–Feldman–Weiss). -/
theorem isMuAmenable_of_isAmenableRel' {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [SigmaFinite μ]
    (E : Set (X × X)) (hE : MeasurableSet E) (hequiv : Equivalence fun x y => (x, y) ∈ E)
    (hcount : ∀ x, {y | (x, y) ∈ E}.Countable)
    (hqi : ∀ A : Set X, μ A = 0 → μ {y | ∃ x ∈ A, (x, y) ∈ E} = 0) :
    Monod.IsAmenableRel μ E → IsMuAmenable μ E := by
  intro hamen
  have hD : ConnesFeldmanWeiss.IsDiscreteMeasured μ E := by
    refine ⟨hE, hequiv, hcount, fun A _ hA0 => ?_⟩
    refine measure_mono_null ?_ (hqi A hA0)
    rintro x ⟨y, hy, hxy⟩
    exact ⟨y, hy, hequiv.symm hxy⟩
  obtain ⟨T, hT, N, hN, hN0, hR⟩ :=
    ConnesFeldmanWeiss.exists_nonsingular_generator_of_isAmenableRel μ E hD hamen
  have hg := zpow_measurable_and_null T hT
  let N' : Set X := ⋃ n : ℤ, ⇑(T.toEquiv ^ n) ⁻¹' N
  have hN' : MeasurableSet N' := MeasurableSet.iUnion fun n => (hg n).1 hN
  have hN'0 : μ N' = 0 := measure_iUnion_null fun n => (hg n).2 N hN hN0
  have hsub : N ⊆ N' := fun x hx => mem_iUnion.2 ⟨0, by simpa using hx⟩
  have hshift : ∀ x (m : ℤ), (T.toEquiv ^ m) x ∈ N' ↔ x ∈ N' := by
    intro x m
    simp only [N', mem_iUnion, mem_preimage]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n + m, ?_⟩
      rwa [zpow_add, Equiv.Perm.mul_apply]
    · rintro ⟨n, hn⟩
      refine ⟨n - m, ?_⟩
      rwa [← Equiv.Perm.mul_apply, ← zpow_add, sub_add_cancel]
  have hTinv : ∀ x, T.toEquiv x ∈ N'ᶜ ↔ x ∈ N'ᶜ := by
    intro x
    have h := hshift x 1
    rw [zpow_one] at h
    exact not_congr h
  let P : Equiv.Perm (N'ᶜ : Set X) := Equiv.Perm.subtypePerm (T.toEquiv : Equiv.Perm X) hTinv
  have hPm : Measurable ⇑P :=
    (T.measurable.comp measurable_subtype_coe).subtype_mk
  have hPim : Measurable ⇑P.symm :=
    (T.symm.measurable.comp measurable_subtype_coe).subtype_mk
  let T' : (N'ᶜ : Set X) ≃ᵐ (N'ᶜ : Set X) :=
    { toEquiv := P
      measurable_toFun := hPm
      measurable_invFun := hPim }
  refine ⟨N', hN', hN'0, T', fun x y => ?_⟩
  have hx : (x : X) ∉ N := fun h => x.2 (hsub h)
  have hy : (y : X) ∉ N := fun h => y.2 (hsub h)
  rw [hR x y hx hy]
  refine exists_congr fun n => ?_
  show _ ↔ (P ^ n) x = y
  rw [Equiv.Perm.subtypePerm_zpow, Subtype.ext_iff, Equiv.Perm.subtypePerm_apply]

end LodhaMoore.Dev.Stmt5
end

section
open LodhaMoore
open LodhaMoore.Dev
open LodhaMoore.Dev.Stmt5
open MeasureTheory Set
variable {X : Type*} [MeasurableSpace X]
theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ]
    (E : Set (X × X)) (hE : MeasurableSet E) (hequiv : Equivalence fun x y => (x, y) ∈ E)
    (hcount : ∀ x, {y | (x, y) ∈ E}.Countable)
    (hqi : ∀ A : Set X, μ A = 0 → μ {y | ∃ x ∈ A, (x, y) ∈ E} = 0) :
    Monod.IsAmenableRel μ E → IsMuAmenable μ E :=
  isMuAmenable_of_isAmenableRel' μ E hE hequiv hcount hqi
end
