-- Prove2me | solution 1 for GlobalTheory.PeriodChart.herm_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:39:38.983529+00:00
-- url     : https://prove2.me/submissions/d0ad4d78-9bed-435b-ab9c-173168ed3e2a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_single
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_mulVec_left
import Theorems.Thm_GlobalTheory_PeriodChart_sesq_mulVec_right
import Theorems.Thm_GlobalTheory_PeriodChart_im_eq_of_span

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
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
namespace GlobalTheory.PeriodChart
theorem _root_.solution (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (a : 𝓞 E) : dg ty a * Gᵀ = Gᵀ * dg ty a := by

  have hconjb : ∀ i, starRingEnd ℂ (ty i ((H.bar a : 𝓞 E) : E)) = ty i (a : E) := by
    intro i
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  let S : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin (dg ty a)).restrictScalars ℝ
  let T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin (dg ty (H.bar a))).restrictScalars ℝ

  have h1 := im_eq_of_span (⇑P) hs (sesq G) (sesq G) S LinearMap.id LinearMap.id T (fun x y => by
    simp only [S, T, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, LinearMap.id_apply]
    rw [← hl, ← hl, hE, hE, D.adj])
  have h2 : ∀ z w, (sesq ((dg ty a)ᵀ * G) z w).im =
      (sesq (G * (dg ty (H.bar a)).map (starRingEnd ℂ)) z w).im := by
    intro z w
    have e := h1 z w
    simp only [S, T, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, LinearMap.id_apply] at e
    rwa [sesq_mulVec_left, sesq_mulVec_right] at e

  have h3 : ∀ z w, sesq ((dg ty a)ᵀ * G) z w = sesq (G * (dg ty (H.bar a)).map (starRingEnd ℂ)) z w := by
    intro z w
    apply Complex.ext
    · have e := h2 (Complex.I • z) w
      simpa using e
    · exact h2 z w
  have hX : (dg ty a)ᵀ * G = G * (dg ty (H.bar a)).map (starRingEnd ℂ) := by
    ext i j
    have e := h3 (Pi.single i 1) (Pi.single j 1)
    rwa [sesq_single, sesq_single] at e
  have hT : (dg ty a)ᵀ = dg ty a := Matrix.diagonal_transpose _
  have hM : (dg ty (H.bar a)).map (starRingEnd ℂ) = dg ty a := by
    unfold dg
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact hconjb i
  rw [hT, hM] at hX
  have e := congrArg Matrix.transpose hX
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hT] at e
  exact e.symm
end GlobalTheory.PeriodChart
