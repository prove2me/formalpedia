-- Prove2me | solution 1 for MeasureTheory.exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/51bc8711-741e-5fb3-982d-94b95f5b1012

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Set Topology Filter
open scoped Pointwise ENNReal

namespace P2mAbstractFujisaki

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [MeasurableSpace R] [BorelSpace R]

theorem isCompact_units_of_val_mem_of_inv_mem {A B : Set R} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact {k : Rˣ | (k : R) ∈ A ∧ ((k⁻¹ : Rˣ) : R) ∈ B} := by
  have hce : IsClosedEmbedding (Units.embedProduct R) := Units.isClosedEmbedding_embedProduct
  have hAB : IsCompact (A ×ˢ (MulOpposite.op '' B) : Set (R × Rᵐᵒᵖ)) :=
    hA.prod (hB.image MulOpposite.continuous_op)
  have heq : {k : Rˣ | (k : R) ∈ A ∧ ((k⁻¹ : Rˣ) : R) ∈ B} =
      Units.embedProduct R ⁻¹' (A ×ˢ (MulOpposite.op '' B)) := by
    ext k
    simp only [mem_setOf_eq, mem_preimage, Units.embedProduct_apply, mem_prod, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, ⟨_, h2, rfl⟩⟩
    · rintro ⟨h1, ⟨b, hb, hbk⟩⟩
      refine ⟨h1, ?_⟩
      have : b = ((k⁻¹ : Rˣ) : R) := MulOpposite.op_injective hbk
      rw [← this]
      exact hb
  rw [heq]
  exact hce.isCompact_preimage hAB

theorem map_mul_right_inv_eq (α : Measure R) (t : Rˣ)
    (h : Measure.map (fun x : R => x * (t : R)) α = α) :
    Measure.map (fun x : R => x * ((t⁻¹ : Rˣ) : R)) α = α := by
  have hm : Measurable fun x : R => x * ((t⁻¹ : Rˣ) : R) := (continuous_id.mul continuous_const).measurable
  have hm' : Measurable fun x : R => x * (t : R) := (continuous_id.mul continuous_const).measurable
  conv_lhs => rw [← h]
  rw [Measure.map_map hm hm']
  have : ((fun x : R => x * ((t⁻¹ : Rˣ) : R)) ∘ fun x : R => x * (t : R)) = id := by
    funext x
    simp
  rw [this, Measure.map_id]

theorem main
    (α : Measure R) [SFinite α] [α.IsAddLeftInvariant]
    (Λ : AddSubgroup R) [Countable Λ]
    (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ)
    (hfin : ∀ C : Set R, IsCompact C → (C ∩ (Λ : Set R)).Finite)
    (hdiv : ∀ x ∈ Λ, x ≠ 0 → ∃ u : Rˣ, (u : R) = x ∧ ((u⁻¹ : Rˣ) : R) ∈ Λ)
    (F : Set R) (hF : IsAddFundamentalDomain Λ F α)
    (C₀ : Set R) (hC₀ : IsCompact C₀) (hlt : α F < α C₀) :
    ∃ C : Set Rˣ, IsCompact C ∧
      ∀ t : Rˣ, Measure.map (fun x : R => (t : R) * x) α = α →
        Measure.map (fun x : R => x * (t : R)) α = α →
        ∃ l : Rˣ, (l : R) ∈ Λ ∧ ((l⁻¹ : Rˣ) : R) ∈ Λ ∧ ∃ k ∈ C, t = l * k := by

  set C₁ : Set R := C₀ + -C₀ with hC₁def
  have hC₁ : IsCompact C₁ := hC₀.add hC₀.neg
  set C₂ : Set R := C₁ * C₁ with hC₂def
  have hC₂ : IsCompact C₂ := hC₁.mul hC₁

  have hΦ : (C₂ ∩ (Λ : Set R)).Finite := hfin C₂ hC₂
  set B : Set R := ⋃ ζ ∈ {ζ : Rˣ | (ζ : R) ∈ C₂ ∩ (Λ : Set R)}, C₁ * {((ζ⁻¹ : Rˣ) : R)} with hBdef
  have hBc : IsCompact B := by
    have hfinU : {ζ : Rˣ | (ζ : R) ∈ C₂ ∩ (Λ : Set R)}.Finite :=
      hΦ.preimage (Units.val_injective.injOn)
    refine hfinU.isCompact_biUnion fun ζ _ => ?_
    exact hC₁.mul isCompact_singleton
  refine ⟨{k : Rˣ | (k : R) ∈ C₁ ∧ ((k⁻¹ : Rˣ) : R) ∈ B},
    isCompact_units_of_val_mem_of_inv_mem hC₁ hBc, fun t hl hr => ?_⟩

  have hmeas_l : Measurable fun x : R => (t : R) * x := (continuous_const.mul continuous_id).measurable
  have hmeas_r : Measurable fun x : R => x * ((t⁻¹ : Rˣ) : R) :=
    (continuous_id.mul continuous_const).measurable
  have hS₁c : IsCompact ((fun x : R => (t : R) * x) '' C₀) := hC₀.image (continuous_const.mul continuous_id)
  have hS₂c : IsCompact ((fun x : R => x * ((t⁻¹ : Rˣ) : R)) '' C₀) :=
    hC₀.image (continuous_id.mul continuous_const)
  have hvol₁ : α F < α ((fun x : R => (t : R) * x) '' C₀) := by
    have hinj : Function.Injective fun x : R => (t : R) * x := fun x y hxy => by
      simpa using congrArg (fun z => ((t⁻¹ : Rˣ) : R) * z) hxy
    have : α ((fun x : R => (t : R) * x) '' C₀) = α C₀ := by
      conv_lhs => rw [← hl]
      rw [Measure.map_apply hmeas_l (hS₁c.measurableSet), hinj.preimage_image]
    rwa [this]
  have hvol₂ : α F < α ((fun x : R => x * ((t⁻¹ : Rˣ) : R)) '' C₀) := by
    have hr' := map_mul_right_inv_eq α t hr
    have hinj : Function.Injective fun x : R => x * ((t⁻¹ : Rˣ) : R) := fun x y hxy => by
      simpa using congrArg (fun z => z * (t : R)) hxy
    have : α ((fun x : R => x * ((t⁻¹ : Rˣ) : R)) '' C₀) = α C₀ := by
      conv_lhs => rw [← hr']
      rw [Measure.map_apply hmeas_r (hS₂c.measurableSet), hinj.preimage_image]
    rwa [this]
  obtain ⟨x₁, y₁, hne₁, hnd₁⟩ := exists_pair_mem_lattice_not_disjoint_vadd (L := Λ) hF
    hS₁c.measurableSet.nullMeasurableSet hvol₁
  obtain ⟨x₂, y₂, hne₂, hnd₂⟩ := exists_pair_mem_lattice_not_disjoint_vadd (L := Λ) hF
    hS₂c.measurableSet.nullMeasurableSet hvol₂

  obtain ⟨z₁, hz₁x, hz₁y⟩ := Set.not_disjoint_iff.1 hnd₁
  obtain ⟨p₁, ⟨c₁, hc₁, rfl⟩, hp₁⟩ := hz₁x
  obtain ⟨q₁, ⟨d₁, hd₁, rfl⟩, hq₁⟩ := hz₁y
  have h₁ : (x₁ : R) + (t : R) * c₁ = (y₁ : R) + (t : R) * d₁ := by
    rw [show (x₁ : R) + (t : R) * c₁ = z₁ from hp₁, show (y₁ : R) + (t : R) * d₁ = z₁ from hq₁]
  have h₁' : (x₁ : R) - (y₁ : R) = (t : R) * (d₁ - c₁) := by
    rw [mul_sub]
    calc (x₁ : R) - (y₁ : R) = ((x₁ : R) + (t : R) * c₁) - (t : R) * c₁ - y₁ := by abel
      _ = ((y₁ : R) + (t : R) * d₁) - (t : R) * c₁ - y₁ := by rw [h₁]
      _ = (t : R) * d₁ - (t : R) * c₁ := by abel
  have hξ : ((t⁻¹ : Rˣ) : R) * ((x₁ : R) - (y₁ : R)) = d₁ - c₁ := by
    rw [h₁', ← mul_assoc, Units.inv_mul, one_mul]
  have hξΛ : (x₁ : R) - (y₁ : R) ∈ Λ := Λ.sub_mem x₁.2 y₁.2
  have hξ0 : (x₁ : R) - (y₁ : R) ≠ 0 := fun h => hne₁ (Subtype.ext (sub_eq_zero.1 h))
  have hξC : ((t⁻¹ : Rˣ) : R) * ((x₁ : R) - (y₁ : R)) ∈ C₁ := by
    rw [hξ, sub_eq_add_neg]
    exact Set.add_mem_add hd₁ (Set.neg_mem_neg.2 hc₁)

  obtain ⟨z₂, hz₂x, hz₂y⟩ := Set.not_disjoint_iff.1 hnd₂
  obtain ⟨p₂, ⟨c₂, hc₂, rfl⟩, hp₂⟩ := hz₂x
  obtain ⟨q₂, ⟨d₂, hd₂, rfl⟩, hq₂⟩ := hz₂y
  have h₂ : (x₂ : R) + c₂ * ((t⁻¹ : Rˣ) : R) = (y₂ : R) + d₂ * ((t⁻¹ : Rˣ) : R) := by
    rw [show (x₂ : R) + c₂ * ((t⁻¹ : Rˣ) : R) = z₂ from hp₂,
      show (y₂ : R) + d₂ * ((t⁻¹ : Rˣ) : R) = z₂ from hq₂]
  have h₂' : (x₂ : R) - (y₂ : R) = (d₂ - c₂) * ((t⁻¹ : Rˣ) : R) := by
    rw [sub_mul]
    calc (x₂ : R) - (y₂ : R) = ((x₂ : R) + c₂ * ((t⁻¹ : Rˣ) : R)) - c₂ * ((t⁻¹ : Rˣ) : R) - y₂ := by abel
      _ = ((y₂ : R) + d₂ * ((t⁻¹ : Rˣ) : R)) - c₂ * ((t⁻¹ : Rˣ) : R) - y₂ := by rw [h₂]
      _ = d₂ * ((t⁻¹ : Rˣ) : R) - c₂ * ((t⁻¹ : Rˣ) : R) := by abel
  have hη : ((x₂ : R) - (y₂ : R)) * (t : R) = d₂ - c₂ := by
    rw [h₂', mul_assoc, Units.inv_mul, mul_one]
  have hηΛ : (x₂ : R) - (y₂ : R) ∈ Λ := Λ.sub_mem x₂.2 y₂.2
  have hη0 : (x₂ : R) - (y₂ : R) ≠ 0 := fun h => hne₂ (Subtype.ext (sub_eq_zero.1 h))
  have hηC : ((x₂ : R) - (y₂ : R)) * (t : R) ∈ C₁ := by
    rw [hη, sub_eq_add_neg]
    exact Set.add_mem_add hd₂ (Set.neg_mem_neg.2 hc₂)

  obtain ⟨uξ, huξ, huξinv⟩ := hdiv _ hξΛ hξ0
  obtain ⟨uη, huη, huηinv⟩ := hdiv _ hηΛ hη0

  have hζΛ : ((uη * uξ : Rˣ) : R) ∈ Λ := by
    rw [Units.val_mul, huη, huξ]
    exact hmul _ hηΛ _ hξΛ
  have hζC : ((uη * uξ : Rˣ) : R) ∈ C₂ := by
    have : ((uη * uξ : Rˣ) : R) =
        (((x₂ : R) - (y₂ : R)) * (t : R)) * (((t⁻¹ : Rˣ) : R) * ((x₁ : R) - (y₁ : R))) := by
      rw [Units.val_mul, huη, huξ, mul_assoc, ← mul_assoc (t : R), Units.mul_inv, one_mul]
    rw [this]
    exact Set.mul_mem_mul hηC hξC

  refine ⟨uη⁻¹, huηinv, ?_, uη * t, ⟨?_, ?_⟩, by group⟩
  · rw [inv_inv, huη]
    exact hηΛ
  · show ((uη * t : Rˣ) : R) ∈ C₁
    rw [Units.val_mul, huη]
    exact hηC
  · show (((uη * t)⁻¹ : Rˣ) : R) ∈ B
    rw [hBdef]
    refine Set.mem_iUnion₂.2 ⟨uη * uξ, ⟨hζC, hζΛ⟩, ?_⟩
    refine ⟨((t⁻¹ : Rˣ) : R) * ((x₁ : R) - (y₁ : R)), hξC, (((uη * uξ)⁻¹ : Rˣ) : R), rfl, ?_⟩
    rw [← huξ]
    have hunit : (t⁻¹ * uξ * (uη * uξ)⁻¹ : Rˣ) = (uη * t)⁻¹ := by group
    have := congrArg Units.val hunit
    simpa only [Units.val_mul] using this

end P2mAbstractFujisaki

open MeasureTheory
open scoped Pointwise

theorem solution
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    [MeasurableSpace R] [BorelSpace R]
    (α : Measure R) [SFinite α] [α.IsAddLeftInvariant]
    (Λ : AddSubgroup R) [Countable Λ]
    (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ)
    (hfin : ∀ C : Set R, IsCompact C → (C ∩ (Λ : Set R)).Finite)
    (hdiv : ∀ x ∈ Λ, x ≠ 0 → ∃ u : Rˣ, (u : R) = x ∧ ((u⁻¹ : Rˣ) : R) ∈ Λ)
    (F : Set R) (hF : IsAddFundamentalDomain Λ F α)
    (C₀ : Set R) (hC₀ : IsCompact C₀) (hlt : α F < α C₀) :
    ∃ C : Set Rˣ, IsCompact C ∧
      ∀ t : Rˣ, Measure.map (fun x : R => (t : R) * x) α = α →
        Measure.map (fun x : R => x * (t : R)) α = α →
        ∃ l : Rˣ, (l : R) ∈ Λ ∧ ((l⁻¹ : Rˣ) : R) ∈ Λ ∧ ∃ k ∈ C, t = l * k :=
  P2mAbstractFujisaki.main α Λ hmul hfin hdiv F hF C₀ hC₀ hlt

end S_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain
end P2MW
export P2MW.S_MeasureTheory_exists_isCompact_forall_exists_eq_mul_of_map_mul_eq_of_isAddFundamentalDomain (solution)
