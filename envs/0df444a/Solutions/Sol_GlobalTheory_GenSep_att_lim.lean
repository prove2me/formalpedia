-- Prove2me | solution 1 for GlobalTheory.GenSep.att_lim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:57:10.435678+00:00
-- url     : https://prove2.me/submissions/3a5214ee-58fa-4664-b607-6c29510ee77b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IsUnitOfValEqZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_WeakApprox
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AlgebraicCurves_PlacesRestrictInjective
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_AlgebraMapMemMax
import Theorems.Thm_GlobalTheory_GenSep_val_eq_of_close

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.T0 IsLocalRing MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.GenSep
variable {Ω F F' : Type} [Field Ω] [Field F] [Field F'] (w : AddValuation F (WithTop ℤ))
  (w' : AddValuation F' (WithTop ℤ)) (ι : Ω →+* F) (ι' : Ω →+* F')
namespace GlobalTheory.GenSep
theorem _root_.solution (heq : ∀ a, w (ι a) = w' (ι' a)) {A : Subring (F × F')} (hA : ∀ z ∈ A, Att w w' ι ι' z) :
    ∀ z ∈ lim w w' A, Att w w' ι ι' z := by
  intro z hz
  induction h : w z.1 using WithTop.recTopCoe with
  | top =>
    induction h' : w' z.2 using WithTop.recTopCoe with
    | top => exact ⟨0, by simp [h], by simp [h']⟩
    | coe n =>
      obtain ⟨a, ha, h1, h2⟩ := hz (n + 1)
      obtain ⟨b, hb1, hb2⟩ := hA a ha
      have e2 := (val_eq_of_close w' h2).1 h'
      have e1 := (val_eq_of_close w h1).2 (by rw [hb1, heq, ← hb2, e2])
      rw [h] at e1
      exact absurd e1 WithTop.top_ne_coe
  | coe n =>
    obtain ⟨a, ha, h1, h2⟩ := hz (n + 1)
    obtain ⟨b, hb1, hb2⟩ := hA a ha
    have e1 := (val_eq_of_close w h1).1 h
    have e2 := (val_eq_of_close w' h2).2 (by rw [hb2, ← heq, ← hb1, e1])
    exact ⟨b, by rw [h, ← hb1, e1], by rw [e2, ← heq, ← hb1, e1]⟩
end GlobalTheory.GenSep
