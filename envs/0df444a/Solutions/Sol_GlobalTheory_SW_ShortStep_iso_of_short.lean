-- Prove2me | solution 1 for GlobalTheory.SW.ShortStep.iso_of_short
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:10:43.615954+00:00
-- url     : https://prove2.me/submissions/4dd91b98-9660-45ed-be40-52ecf39de3e1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsNearlyPrimitive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ShortIsotropicVectorsExistenceSuccOfVeryShortSte
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_mul
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_one
import Theorems.Thm_GlobalTheory_SW_ShortStep_den_conj
import Theorems.Thm_GlobalTheory_SW_ShortStep_map_conj
import Theorems.Thm_GlobalTheory_SW_ShortStep_det_map_ne
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_card_type
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_gram_le
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_hval_eq
import Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_one_le_prod
import Theorems.Thm_GlobalTheory_spanCovol_bot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.spanCovol_bot



set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.ShortStep
open MinkowskiProductBounds
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)}
namespace GlobalTheory.SW.ShortStep
theorem _root_.solution (h : IsType Ψ) {n D : ℕ} (hD : 0 < D) {G : Matrix (Fin n) (Fin n) E}
    {H : CM Ψ n n} (hG : Gᴴ = G) (h0 : G.det ≠ 0) (hD1 : Den D G) (hH : IsMaj Ψ G H)
    {V : Matrix (Fin 1) (Fin n) E} (hV : IntM V) (hs : ∀ τ, hval Ψ H τ (V 0) < 1 / D) :
    V * G * Vᴴ = 0 := by
  have hi := den_mul (den_mul (den_one hV) hD1) (den_conj (den_one hV)) 0 0
  have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  have hD'' : (0 : ℝ) < D := by exact_mod_cast hD
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  by_contra hne
  simp only [one_mul, mul_one, Matrix.smul_apply, smul_eq_mul] at hi
  have hne' := mul_ne_zero hD' hne
  have h1 := one_le_prod h hi hne'
  have hΨ : Nonempty Ψ := by
    have := card_type h
    have h2 := Module.finrank_pos (R := ℚ) (M := E)
    exact (Finset.card_pos.1 (by omega)).to_subtype
  have h2 : ∏ τ : Ψ, ‖τ.1 (D * (V * G * Vᴴ) 0 0)‖ < ∏ _τ : Ψ, (1 : ℝ) := by
    refine Finset.prod_lt_prod_of_nonempty (fun τ _ => norm_pos_iff.2 ((_root_.map_ne_zero _).2 hne')) (fun τ _ => ?_)
      Finset.univ_nonempty
    have h3 := gram_le (hH τ).1 (by rw [← map_conj, hG]) (det_map_ne τ.1 h0) (hH τ).2 _ _
      (le_of_eq (hval_eq H τ (V 0)).symm) (le_of_eq (hval_eq H τ (V 0)).symm)
    have h4 : τ.1 ((V * G * Vᴴ) 0 0) = ((fun a => τ.1 (V 0 a)) ⬝ᵥ G.map τ.1 *ᵥ
        star fun a => τ.1 (V 0 a)) := by
      rw [← Matrix.map_apply (f := τ.1), Matrix.map_mul, Matrix.map_mul, map_conj, Matrix.mul_assoc]
      rfl
    rw [map_mul, norm_mul, h4, map_natCast, Complex.norm_natCast]
    have := h3.trans_lt (hs τ)
    rwa [lt_div_iff₀' hD''] at this
  rw [Finset.prod_const_one] at h2
  exact absurd h1 h2.not_ge
end GlobalTheory.SW.ShortStep
