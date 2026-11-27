-- Prove2me | solution 1 for GlobalTheory.TorusCoord.coordMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:58.652519+00:00
-- url     : https://prove2.me/submissions/fe1a54bc-bf99-41e8-8f27-2bb50566d186

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_mem
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_not_mem
import Theorems.Thm_GlobalTheory_TorusCoord_c_pos
import Theorems.Thm_GlobalTheory_TorusCoord_coordMap_pos
import Theorems.Thm_GlobalTheory_TorusCoord_coordMap_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.TorusAtDataPf
open scoped ComplexConjugate
open GlobalTheory
open GlobalTheory.TorusCoord
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.TorusCoord
theorem _root_.solution (X : Data E r) (e : X.Ψ → Fin r → (Fin r → ℂ))
    (he : ∀ τ a b, hermC τ.1 X.Gm (e τ a) (e τ b) =
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) :
    Function.Injective (coordMap X e) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  funext τ
  have hb : ∀ b, pr X e y τ b = 0 := by
    intro b
    by_cases h : b.1 < X.p0
    · have := coordMap_pos X e y τ ⟨b.1, by rw [dimOf_mem X τ.2]; exact h⟩
      rw [hy] at this
      exact this.symm
    · have := coordMap_neg X e y τ ⟨b.1 - X.p0, by
        rw [dimOf_not_mem X ((X.cmType _).mp τ.2)]; have := b.2; omega⟩
      rw [hy] at this
      have h2 : (⟨X.p0 + (b.1 - X.p0), by have := b.2; omega⟩ : Fin r) = b := Fin.ext (by simp only; omega)
      simp only [h2] at this
      have h3 : - conj (pr X e y τ b) = 0 := this.symm
      simpa using h3
  have hs : (Real.sqrt (X.c τ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (c_pos X τ)).ne'
  have hb' : ∀ b, hermC τ.1 X.Gm (y τ) (e τ b) = 0 := fun b =>
    (mul_eq_zero.mp (hb b)).resolve_left hs
  rw [expand X τ (e τ) (he τ) (y τ)]
  simp [hb']
end GlobalTheory.TorusCoord
