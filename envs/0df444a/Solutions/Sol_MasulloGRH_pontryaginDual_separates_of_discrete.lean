-- Prove2me | solution 1 for MasulloGRH.pontryaginDual_separates_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T15:08:50.674328+00:00
-- url     : https://prove2.me/submissions/e9b50aef-beab-4911-a423-212cbb2a13e1

import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Topology.Algebra.PontryaginDual

set_option autoImplicit false

open Topology

namespace MasulloGRHDiscreteCharAux

/-- The embedding `ℚ/ℤ → ℝ/ℤ`. -/
noncomputable def ratCircleToCircle : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map _ _ (Rat.castHom ℝ).toAddMonoidHom (by
    intro q hq
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hq
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨n, by simp⟩)

theorem ratCircleToCircle_injective : Function.Injective ratCircleToCircle := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have : ((q : ℝ) : AddCircle (1 : ℝ)) = 0 := hx
    rw [AddCircle.coe_eq_zero_iff] at this
    obtain ⟨n, hn⟩ := this
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨n, ?_⟩
    have : ((n • (1 : ℚ) : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
    exact_mod_cast this

theorem exists_hom_circle_ne_one {A : Type*} [CommGroup A] (a : A) (ha : a ≠ 1) :
    ∃ χ : A →* Circle, χ a ≠ 1 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero
    (A := Additive A) (a := Additive.ofMul a) (by simpa using ha)
  let χ : A →* Circle :=
    { toFun := fun x => AddCircle.toCircle (ratCircleToCircle (c (Additive.ofMul x))),
      map_one' := by simp [AddCircle.toCircle_zero],
      map_mul' := fun x y => by
        simp only [ofMul_mul, map_add]
        exact AddCircle.toCircle_add _ _ }
  refine ⟨χ, ?_⟩
  intro h
  apply hc
  have h' : AddCircle.toCircle (ratCircleToCircle (c (Additive.ofMul a))) =
      AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
    rw [AddCircle.toCircle_zero]; exact h
  have := AddCircle.injective_toCircle (one_ne_zero) h'
  exact ratCircleToCircle_injective (by simpa using this)

/-- **Characters of a discrete abelian group separate a point from a subgroup.** -/
theorem exists_eq_one_on_subgroup_ne_one_of_discrete
    (G : Type*) [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (H : Subgroup G) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 := by
  have hne : (QuotientGroup.mk g : G ⧸ H) ≠ 1 := by
    rwa [Ne, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hψ⟩ := exists_hom_circle_ne_one _ hne
  refine ⟨⟨ψ.comp (QuotientGroup.mk' H), continuous_of_discreteTopology⟩, ?_, ?_⟩
  · intro h hh
    change ψ (QuotientGroup.mk' H h) = 1
    have : QuotientGroup.mk' H h = 1 := (QuotientGroup.eq_one_iff h).mpr hh
    rw [this, _root_.map_one]
  · exact hψ

end MasulloGRHDiscreteCharAux

theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [DiscreteTopology G]
    (H : Subgroup G) (g : G) (hg : g ∉ H) :
    ∃ χ : PontryaginDual G, (∀ h ∈ H, χ h = 1) ∧ χ g ≠ 1 :=
  MasulloGRHDiscreteCharAux.exists_eq_one_on_subgroup_ne_one_of_discrete G H g hg
