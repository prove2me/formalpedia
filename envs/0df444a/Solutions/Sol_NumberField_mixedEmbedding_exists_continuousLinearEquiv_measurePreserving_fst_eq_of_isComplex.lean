-- Prove2me | solution 1 for NumberField.mixedEmbedding.exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/7bdb696d-f160-5c4a-8a8b-7f3ee9783d12

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex

set_option autoImplicit false

open MeasureTheory NumberField

namespace SplitCoordComplex

variable (K : Type) [Field K] [NumberField K]

abbrev RIdx := {v : NumberField.InfinitePlace K // v.IsReal}

abbrev CIdx := {w : NumberField.InfinitePlace K // w.IsComplex}

open scoped Classical in

noncomputable def splitLinearEquiv (i₀ : CIdx K) :
    NumberField.mixedEmbedding.mixedSpace K ≃ₗ[ℝ]
      (ℂ × ((RIdx K → ℝ) × ({w : CIdx K // w ≠ i₀} → ℂ))) where
  toFun X := (X.2 i₀, (X.1, fun w => X.2 w.1))
  invFun Y := (Y.2.1, fun w => if h : w = i₀ then Y.1 else Y.2.2 ⟨w, h⟩)
  map_add' X Y := by rfl
  map_smul' c X := by rfl
  left_inv X := by
    rcases X with ⟨f, g⟩
    simp only [Prod.mk.injEq, true_and]
    funext w
    by_cases h : w = i₀
    · subst h; simp
    · simp [h]
  right_inv Y := by
    rcases Y with ⟨r, f, g⟩
    simp only [Prod.mk.injEq]
    refine ⟨by simp, trivial, ?_⟩
    funext w
    have hw : (w : CIdx K) ≠ i₀ := w.2
    simp [hw]

open scoped Classical in

theorem measurePreserving_splitLinearEquiv (i₀ : CIdx K) :
    MeasurePreserving (splitLinearEquiv K i₀) volume volume := by

  letI instF : Fintype {w : CIdx K // w = i₀} := Subtype.fintype fun w => w = i₀

  have h0 : MeasurePreserving (Prod.swap : NumberField.mixedEmbedding.mixedSpace K → (CIdx K → ℂ) × (RIdx K → ℝ))
      volume volume :=
    Measure.measurePreserving_swap

  have h1 := volume_preserving_piEquivPiSubtypeProd (fun _ : CIdx K => ℂ) (fun w => w = i₀)
  have hA := (h1.prod (MeasurePreserving.id (volume : Measure (RIdx K → ℝ)))).comp h0

  have hB := (volume_preserving_prodAssoc
    (α₁ := ({w : CIdx K // w = i₀} → ℂ)) (β₁ := ({w : CIdx K // ¬ w = i₀} → ℂ)) (γ₁ := (RIdx K → ℝ)))
  have hAB := hB.comp hA

  have h3 : MeasurePreserving
      (Prod.swap : ({w : CIdx K // ¬ w = i₀} → ℂ) × (RIdx K → ℝ) → (RIdx K → ℝ) × ({w : CIdx K // ¬ w = i₀} → ℂ))
      volume volume :=
    Measure.measurePreserving_swap
  have hC := (MeasurePreserving.id (volume : Measure ({w : CIdx K // w = i₀} → ℂ))).prod h3
  have hABC := hC.comp hAB

  have h4 := measurePreserving_piUnique (ι := {w : CIdx K // w = i₀}) (fun _ => (volume : Measure ℂ))
  have hD := h4.prod (MeasurePreserving.id
    (volume : Measure ((RIdx K → ℝ) × ({w : CIdx K // ¬ w = i₀} → ℂ))))
  have hABCD := hD.comp hABC

  have hfun : (⇑(splitLinearEquiv K i₀) : NumberField.mixedEmbedding.mixedSpace K →
      ℂ × ((RIdx K → ℝ) × ({w : CIdx K // w ≠ i₀} → ℂ))) =
      (Prod.map (⇑(MeasurableEquiv.piUnique fun _ : {w : CIdx K // w = i₀} => ℂ)) id) ∘
        ((Prod.map id Prod.swap) ∘
          ((⇑(MeasurableEquiv.prodAssoc :
              (({w : CIdx K // w = i₀} → ℂ) × ({w : CIdx K // ¬ w = i₀} → ℂ)) × (RIdx K → ℝ) ≃ᵐ
                ({w : CIdx K // w = i₀} → ℂ) × (({w : CIdx K // ¬ w = i₀} → ℂ) × (RIdx K → ℝ)))) ∘
            (Prod.map (⇑(MeasurableEquiv.piEquivPiSubtypeProd (fun _ : CIdx K => ℂ) fun w => w = i₀)) id ∘
              Prod.swap))) := by
    funext X
    rfl
  rw [hfun]
  exact hABCD

end SplitCoordComplex

open scoped Classical in
theorem solution
    (K : Type) [Field K] [NumberField K] (i₀ : {v : NumberField.InfinitePlace K // v.IsComplex}) :
    ∃ e : NumberField.mixedEmbedding.mixedSpace K ≃L[ℝ] (ℂ × (({v : NumberField.InfinitePlace K // v.IsReal} → ℝ) × ({w : {w : NumberField.InfinitePlace K // w.IsComplex} // w ≠ i₀} → ℂ))),
      MeasurePreserving e volume volume ∧
      ∀ X : NumberField.mixedEmbedding.mixedSpace K, (e X).1 = X.2 i₀ :=
  ⟨(SplitCoordComplex.splitLinearEquiv K i₀).toContinuousLinearEquiv,
    SplitCoordComplex.measurePreserving_splitLinearEquiv K i₀, fun _ => rfl⟩

end S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex
end P2MW
export P2MW.S_NumberField_mixedEmbedding_exists_continuousLinearEquiv_measurePreserving_fst_eq_of_isComplex (solution)
