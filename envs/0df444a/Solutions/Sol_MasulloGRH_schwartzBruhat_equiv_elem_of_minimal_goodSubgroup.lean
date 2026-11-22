-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_equiv_elem_of_minimal_goodSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:18:15.780173+00:00
-- url     : https://prove2.me/submissions/5d5c2d24-874b-4a5c-b8f7-d941e668381e

import Theorems.Thm_MasulloGRH_schwartz_correspondence
import Theorems.Thm_MasulloGRH_isCompact_of_isGoodSubgroup
import Theorems.Thm_MasulloGRH_schwartzBruhat_equiv_elem_of_single_stage

set_option autoImplicit false

universe u

namespace MasulloGRHMinAux

open MasulloGRH MeasureTheory

variable {H : Type u} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]

lemma extendPullback_mul {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup H)
    (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g : ElemGroup m n r s d → ℂ) (x y : H) (hy : y ∈ k) :
    extendPullback Γ π g (x * y) = extendPullback Γ π g x := by
  have hyΓ : y ∈ Γ := hs.2.2.2 hy
  unfold extendPullback
  by_cases hx : x ∈ Γ
  · have hxy : x * y ∈ Γ := Γ.mul_mem hx hyΓ
    rw [dif_pos hxy, dif_pos hx]
    have h1 : π ⟨y, hyΓ⟩ = 1 := (hπ.2.2.2.2 ⟨y, hyΓ⟩).2 hy
    have : (⟨x * y, hxy⟩ : Γ) = ⟨x, hx⟩ * ⟨y, hyΓ⟩ := rfl
    rw [this, map_mul, h1, mul_one]
  · have hxy : x * y ∉ Γ := fun h => hx (by simpa using Γ.mul_mem h (Γ.inv_mem hyΓ))
    rw [dif_neg hxy, dif_neg hx]

lemma average_eq (k₀ : Subgroup H) (hk₀ : IsCompact (k₀ : Set H)) (f : H → ℂ)
    (hf : ∀ x, ∀ y ∈ k₀, f (x * y) = f x) (x : H) :
    schwartzBruhatAverage ⊤ k₀ f x = f x := by
  letI : MeasurableSpace k₀ := borel k₀
  haveI : BorelSpace k₀ := ⟨rfl⟩
  haveI : CompactSpace k₀ := isCompact_iff_compactSpace.mp hk₀
  unfold schwartzBruhatAverage
  rw [Set.indicator_of_mem (by simp : x ∈ ((⊤ : Subgroup H) : Set H))]
  have h1 : (fun y : k₀ => f (x * y)) = fun _ => f x := funext fun y => hf x y y.2
  have h2 : subgroupHaar k₀ = Measure.haarMeasure ⊤ := by
    unfold subgroupHaar
    rw [dif_pos hk₀]
  simp only [h1, h2, integral_const]
  have h3 : (Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts k₀)) Set.univ = 1 := by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts k₀))
    simpa using this
  simp [measureReal_def, h3]

end MasulloGRHMinAux

open MasulloGRH MasulloGRHMinAux in
theorem solution (H : Type u) [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] [LocallyCompactSpace H]
    (k₀ : Subgroup H) (m n r s : ℕ) (d : Fin s → ℕ)
    (π₀ : (⊤ : Subgroup H) →* Multiplicative (ElemGroup m n r s d))
    (hs₀ : IsStructuralPair ⊤ k₀) (hπ₀ : IsElemPresentation ⊤ k₀ π₀)
    (hmin : ∀ k : Subgroup H, IsGoodSubgroup k → k₀ ≤ k) :
    Nonempty (ElemSchwartz m n r s d ≃L[ℂ] SchwartzBruhat H) ∧ IsFrechet (SchwartzBruhat H) := by
  refine schwartzBruhat_equiv_elem_of_single_stage H ⊤ k₀ m n r s d π₀ hs₀ hπ₀ ?_
  intro Γ k m' n' r' s' d' π hs hπ
  have hkc : IsCompact (k : Set H) := isCompact_of_isGoodSubgroup H k hs.2.2.1
  have hk₀c : IsCompact (k₀ : Set H) := isCompact_of_isGoodSubgroup H k₀ hs₀.2.2.1
  let ι : H →* (⊤ : Subgroup H) := Subgroup.topEquiv.symm.toMonoidHom
  have hι : ∀ x, (ι x : H) = x := fun x => rfl
  let β := π₀.comp ι
  have hιc : Continuous ι := continuous_id.subtype_mk _
  have hιo : IsOpenMap ι := by
    intro U hU
    have : ι '' U = Subtype.val ⁻¹' U := by
      ext ⟨x, hx⟩
      constructor
      · rintro ⟨y, hy, hxy⟩
        have := congrArg Subtype.val hxy
        simp only [hι] at this
        subst this; exact hy
      · intro h; exact ⟨x, h, rfl⟩
    rw [this]; exact hU.preimage continuous_subtype_val
  have hβc : Continuous β := hπ₀.2.1.comp hιc
  have hβo : IsOpenMap β := hπ₀.2.2.1.comp hιo
  have hβker : ∀ x, β x = 1 ↔ x ∈ k₀ := fun x => hπ₀.2.2.2.2 (ι x)
  have hβk : IsCompact {x : H | β x = 1} := by
    have : {x : H | β x = 1} = (k₀ : Set H) := Set.ext hβker
    rw [this]; exact hk₀c
  have hαk : IsCompact {x : Γ | π x = 1} := by
    rw [Subtype.isCompact_iff]
    have : (Subtype.val '' {x : Γ | π x = 1}) = (k : Set H) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩; exact (hπ.2.2.2.2 y).1 hy
      · intro hx; exact ⟨⟨x, hs.2.2.2 hx⟩, (hπ.2.2.2.2 _).2 hx, rfl⟩
    rw [this]; exact hkc
  obtain ⟨T, hTc, hT⟩ := schwartz_correspondence H Γ hs.1 m' n' r' s' d' hπ.1 π hπ.2.1
    hπ.2.2.1 hαk m n r s d β hβc hβo hβk
  refine ⟨T, hTc, fun g => ?_⟩
  apply Subtype.ext
  funext x
  show extendPullback Γ π g.toFun x = extendPullback ⊤ π₀ (T g).toFun x
  have hx : x ∈ (⊤ : Subgroup H) := Subgroup.mem_top x
  have e1 : extendPullback ⊤ π₀ (T g).toFun x = (T g).toFun (Multiplicative.toAdd (β x)) := by
    unfold extendPullback; rw [dif_pos hx]; rfl
  rw [e1, (hT g).1 x]
  have hker : β.ker = k₀ := by ext y; exact hβker y
  rw [hker, average_eq k₀ hk₀c _ (fun x y hy =>
    extendPullback_mul Γ k π hs hπ g.toFun x y (hmin k hs.2.2.1 hy))]
