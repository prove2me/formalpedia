-- Prove2me | solution 1 for GlobalTheory.PeriodRowsCompare.isTypeFn_letters
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:08:14.904675+00:00
-- url     : https://prove2.me/submissions/dd84f6b5-023d-4b5d-8cf0-e3ffb257f99c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModelBaseTrivModels

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PeriodRowsCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.PeriodRowsCompare
theorem _root_.solution (c : Coeff l) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) : IsTypeFn H Dw.p Dw.q (fun j => relab c σ (e j).1) := by
  classical
  have hinj : Function.Injective (relab c σ) := by
    intro τ₁ τ₂ h
    ext a
    have := congrArg (fun f : E →+* ℂ => f a) h
    exact congrArg Subtype.val (σ.injective this)
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  have hrel : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := fun τ => by
    have hval : relab c σ τ (H.rt : E) = σ ⟨τ (H.rt : E), c.conj τ _⟩ := rfl
    rw [hval]
    refine ⟨fun h => congrArg Subtype.val (σ.injective (h.trans hσ0.symm)), fun h => ?_⟩
    exact (congrArg σ (Subtype.ext h)).trans hσ0
  intro τ
  obtain ⟨τ₀, rfl⟩ := Finite.injective_iff_surjective.1 hinj τ
  have hcard : Nat.card {i // relab c σ (e i).1 = relab c σ τ₀} = Dw.mult τ₀ := by
    have e1 : {i // relab c σ (e i).1 = relab c σ τ₀} ≃ {i // (e i).1 = τ₀} :=
      Equiv.subtypeEquivRight (fun i => hinj.eq_iff)
    have e2 : {i // (e i).1 = τ₀} ≃ {s : Σ τ : E →+* ℂ, Fin (Dw.mult τ) // s.1 = τ₀} :=
      e.subtypeEquiv (fun _ => Iff.rfl)
    rw [Nat.card_congr (e1.trans (e2.trans (Equiv.sigmaSubtype τ₀))), Nat.card_eq_fintype_card, Fintype.card_fin]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hcard]
    exact if_pos ((hrel τ₀).1 h)
  · rw [hcard]
    exact if_neg (fun h' => h ((hrel τ₀).2 h'))
end GlobalTheory.PeriodRowsCompare
