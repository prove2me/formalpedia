-- Prove2me | solution 1 for ModularCurve.exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/09b81199-88ed-5334-990f-2eb658dd4be1

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_ModularCurve_exists_algEquiv_laurentBaseChange_cover
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb

set_option autoImplicit false

theorem solution
    (L : Type) [Field L] [CharZero L]
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ))
    (G : Type) [Group G] (δ : G →* (↥F₀ ≃ₐ[ℚ] ↥F₀)) :
    ∃ δL : G →* (↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀)),
      ∀ (g : G) (x : ↥F₀) (hx : ModularCurve.coeffEmb L (x : LaurentSeries ℚ) ∈ ModularCurve.laurentBaseChange L F₀),
        ((δL g ⟨ModularCurve.coeffEmb L (x : LaurentSeries ℚ), hx⟩ : LaurentSeries L)) =
          ModularCurve.coeffEmb L (((δ g x : ↥F₀)) : LaurentSeries ℚ) := by
  classical

  have hex : ∀ g : G, ∃ τ : ↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀),
      ∀ y : ↥F₀, ((τ ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ :
        ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) = ModularCurve.coeffEmb L ((δ g y : ↥F₀) : LaurentSeries ℚ) :=
    fun g => ModularCurve.exists_algEquiv_laurentBaseChange_cover L F₀ (δ g).toRingEquiv
  choose τ hτ using hex

  have huniq : ∀ σ σ' : ↥(ModularCurve.laurentBaseChange L F₀) ≃ₐ[L] ↥(ModularCurve.laurentBaseChange L F₀),
      (∀ y : ↥F₀, ((σ ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ :
          ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) =
        ((σ' ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ :
          ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L)) → σ = σ' := by
    intro σ σ' h
    apply AlgEquiv.ext
    intro x
    obtain ⟨x, hx⟩ := x
    apply Subtype.ext

    suffices H : ∀ (z : LaurentSeries L) (hz : z ∈ ModularCurve.laurentBaseChange L F₀),
        ((σ ⟨z, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) = ((σ' ⟨z, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) from H x hx
    intro z hz
    have hz' := (ModularCurve.mem_laurentBaseChange_iff).mp hz
    induction hz' using Subfield.closure_induction with
    | mem w hw =>
      rcases hw with ⟨a, rfl⟩ | ⟨y, hy, rfl⟩
      · have e : (⟨algebraMap L (LaurentSeries L) a, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) =
            algebraMap L ↥(ModularCurve.laurentBaseChange L F₀) a := Subtype.ext rfl
        rw [e, AlgEquiv.commutes, AlgEquiv.commutes]
      · exact h ⟨y, hy⟩
    | one =>
      have e : (⟨(1 : LaurentSeries L), hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) = 1 := Subtype.ext rfl
      rw [e, map_one, map_one]
    | add a b ha hb iha ihb =>
      have ha' : a ∈ ModularCurve.laurentBaseChange L F₀ := ha
      have hb' : b ∈ ModularCurve.laurentBaseChange L F₀ := hb
      have e : (⟨a + b, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) = ⟨a, ha'⟩ + ⟨b, hb'⟩ := Subtype.ext rfl
      rw [e, map_add, map_add]
      push_cast
      rw [iha ha', ihb hb']
    | neg a ha iha =>
      have ha' : a ∈ ModularCurve.laurentBaseChange L F₀ := ha
      have e : (⟨-a, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) = -⟨a, ha'⟩ := Subtype.ext rfl
      rw [e, map_neg, map_neg]
      push_cast
      rw [iha ha']
    | inv a ha iha =>
      have ha' : a ∈ ModularCurve.laurentBaseChange L F₀ := ha
      have e : (⟨a⁻¹, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) = (⟨a, ha'⟩)⁻¹ := Subtype.ext rfl
      rw [e, map_inv₀, map_inv₀]
      push_cast
      rw [iha ha']
    | mul a b ha hb iha ihb =>
      have ha' : a ∈ ModularCurve.laurentBaseChange L F₀ := ha
      have hb' : b ∈ ModularCurve.laurentBaseChange L F₀ := hb
      have e : (⟨a * b, hz⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) = ⟨a, ha'⟩ * ⟨b, hb'⟩ := Subtype.ext rfl
      rw [e, map_mul, map_mul]
      push_cast
      rw [iha ha', ihb hb']

  refine ⟨{ toFun := τ, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply huniq
    intro y
    rw [hτ 1 y, map_one]
    rfl
  · intro g h
    apply huniq
    intro y
    rw [hτ (g * h) y, map_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply]

    have e : τ h ⟨ModularCurve.coeffEmb L (y : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange L y.2⟩ =
        ⟨ModularCurve.coeffEmb L ((δ h y : ↥F₀) : LaurentSeries ℚ), ModularCurve.coeffEmb_mem_laurentBaseChange L (δ h y).2⟩ :=
      Subtype.ext (hτ h y)
    rw [e, hτ g (δ h y)]
  · intro g x hx
    show ((τ g ⟨ModularCurve.coeffEmb L (x : LaurentSeries ℚ), hx⟩ : ↥(ModularCurve.laurentBaseChange L F₀)) : LaurentSeries L) = _
    exact hτ g x

end S_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb
end P2MW
export P2MW.S_ModularCurve_exists_monoidHom_algEquiv_laurentBaseChange_apply_coeffEmb (solution)
