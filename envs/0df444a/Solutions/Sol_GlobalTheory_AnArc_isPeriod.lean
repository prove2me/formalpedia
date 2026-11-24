-- Prove2me | solution 1 for GlobalTheory.AnArc.isPeriod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:59:13.675783+00:00
-- url     : https://prove2.me/submissions/067813d0-a21f-420a-bf6f-eebf7b7ca2b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Theorems.Thm_GlobalTheory_AnArc_period_clauses
import Theorems.Thm_GlobalTheory_AnArc_Pw_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
open Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
namespace GlobalTheory
namespace AnArc
theorem _root_.solution {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)]
    (A : AnArc (𝓞 E)) {w : ℂ} (hw : (A.BwMat w).PosDef) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (h : A.V ≃ₗ[ℂ] (Fin g → ℂ)) (hh : ∀ (a : 𝓞 E) v i, h (A.actV a v) i = ty i (a : E) * h v i)
    (e : D.La ≃+ A.La) (he : ∀ (a : 𝓞 E) x, e (a • x) = a • e x) (hE : ∀ x y, A.EF (e x) (e y) = D.EF x y)
    (P : D.La →+ (Fin g → ℂ)) (hP : ∀ x, P x = h (A.Pw w (e x))) : IsPeriod D ty P := by
  obtain ⟨h1, h2, h3, Hm, h4, h5, h6⟩ := A.period_clauses hw h e P hP
  refine ⟨fun a x i => ?_, h1, h2, h3, Hm, h4, h5, fun x y => by rw [h6, hE]⟩
  rw [hP, hP, he, A.Pw_smul, hh]
end AnArc
end GlobalTheory
