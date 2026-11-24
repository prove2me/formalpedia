-- Prove2me | solution 1 for GlobalTheory.PeriodChart.anti_comm_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:21:21.536102+00:00
-- url     : https://prove2.me/submissions/f3ee6a46-06e3-4d17-b822-ca89b0895fdc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.PeriodChart
theorem _root_.solution (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (Z : Matrix (Fin g) (Fin g) ℂ) :
    (∀ z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ↔
      dg ty a * Z = Z * dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by
  have hs : ∀ z : Fin g → ℂ,
      star (dg ty a *ᵥ z) = dg (fun i => ComplexEmbedding.conjugate (ty i)) a *ᵥ star z := by
    intro z
    funext k
    simp [dg, Matrix.mulVec_diagonal, ComplexEmbedding.conjugate_coe_eq, mul_comm]
  have key : ∀ z : Fin g → ℂ, anti Z (dg ty a *ᵥ z) =
      (Z * dg (fun i => ComplexEmbedding.conjugate (ty i)) a) *ᵥ star z := by
    intro z
    change Z *ᵥ star (dg ty a *ᵥ z) = _
    rw [hs, Matrix.mulVec_mulVec]
  have key2 : ∀ z : Fin g → ℂ, dg ty a *ᵥ anti Z z = (dg ty a * Z) *ᵥ star z := by
    intro z
    change dg ty a *ᵥ (Z *ᵥ star z) = _
    rw [Matrix.mulVec_mulVec]
  simp only [key, key2]
  constructor
  · intro h
    ext i j
    have hst : star (Pi.single j (1 : ℂ) : Fin g → ℂ) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
    have e := congrFun (h (Pi.single j 1)) i
    rw [hst, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at e
    exact e.symm
  · intro h z
    rw [h]
end GlobalTheory.PeriodChart
