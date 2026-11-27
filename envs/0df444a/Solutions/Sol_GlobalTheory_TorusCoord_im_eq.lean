-- Prove2me | solution 1 for GlobalTheory.TorusCoord.im_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:35.083529+00:00
-- url     : https://prove2.me/submissions/6cca7341-2f5d-4855-b5a4-ecfe25e960b6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsTorusCoordinates
import Theorems.Thm_GlobalTheory_TorusCoord_sum_emb_split
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_mem
import Theorems.Thm_GlobalTheory_TorusCoord_dimOf_not_mem
import Theorems.Thm_GlobalTheory_TorusCoord_c_pos
import Theorems.Thm_GlobalTheory_TorusCoord_coordMap_pos
import Theorems.Thm_GlobalTheory_TorusCoord_coordMap_neg
import Theorems.Thm_GlobalTheory_TorusCoord_parseval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sum_castLE_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_TorusAtDataPf_sum_shift_eq


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
      if a = b then ((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 a : ℝ) : ℂ) else 0) (y y' : X.Ψ → Fin r → ℂ) :
    (Hf (coordMap X e y) (coordMap X e y')).im =
      ∑ τ : X.Ψ, X.c τ * (hermC τ.1 X.Gm (y τ) (y' τ)).im := by
  rw [Hf, Fintype.sum_sigma, sum_emb_split X, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  let g : Fin r → ℝ := fun b => X.c τ * (((ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 b : ℝ) : ℂ) *
      (hermC τ.1 X.Gm (y τ) (e τ b) * conj (hermC τ.1 X.Gm (y' τ) (e τ b)))).im
  have hsq : Real.sqrt (X.c τ) * Real.sqrt (X.c τ) = X.c τ := Real.mul_self_sqrt (c_pos X τ).le
  have hle : dimOf X τ.1 ≤ r := by rw [dimOf_mem X τ.2]; exact X.p0_le
  have hn := (X.cmType _).mp τ.2
  rw [parseval X τ (e τ) (he τ), Complex.im_sum, Finset.mul_sum, Complex.add_im, Complex.im_sum,
    Complex.im_sum]
  show _ = ∑ b, g b
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b : Fin r => (b : ℕ) < X.p0)]
  congr 1
  · have h := sum_castLE_eq hle g
    rw [show (Finset.univ.filter (fun b : Fin r => (b : ℕ) < X.p0)) =
      Finset.univ.filter (fun b : Fin r => (b : ℕ) < dimOf X τ.1) by rw [dimOf_mem X τ.2], ← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : a.1 < X.p0 := lt_of_lt_of_eq a.2 (dimOf_mem X τ.2)
    rw [coordMap_pos, coordMap_pos]
    have hc : (⟨a.1, lt_pos X τ.2 a⟩ : Fin r) = Fin.castLE hle a := rfl
    simp only [g, pr, hc, ReciprocityTheory.ChartRestriction.G.FD.sgn, Fin.val_castLE, if_pos ha]
    generalize hermC τ.1 X.Gm (y τ) (e τ (Fin.castLE hle a)) = A
    generalize hermC τ.1 X.Gm (y' τ) (e τ (Fin.castLE hle a)) = B
    simp
    linear_combination (A.im * B.re - A.re * B.im) * hsq
  · rw [← sum_shift_eq X.p0_le (dimOf_not_mem X hn) g (fun a => ⟨X.p0 + a.1, lt_neg X hn a⟩)
      (fun a => rfl)]
    refine Finset.sum_congr rfl fun a _ => ?_
    have ha : ¬ (X.p0 + a.1 < X.p0) := by omega
    rw [coordMap_neg, coordMap_neg]
    simp only [g, pr, ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg ha]
    generalize hermC τ.1 X.Gm (y τ) (e τ ⟨X.p0 + a.1, _⟩) = A
    generalize hermC τ.1 X.Gm (y' τ) (e τ ⟨X.p0 + a.1, _⟩) = B
    simp
    linear_combination (A.re * B.im - A.im * B.re) * hsq
end GlobalTheory.TorusCoord
