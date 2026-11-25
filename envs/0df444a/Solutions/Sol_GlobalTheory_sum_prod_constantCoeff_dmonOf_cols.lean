-- Prove2me | solution 1 for GlobalTheory.sum_prod_constantCoeff_dmonOf_cols
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:10:02.986021+00:00
-- url     : https://prove2.me/submissions/d69ffd46-d905-4b45-be2c-2d728f2bfca8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Theorems.Thm_GlobalTheory_SymbolCols_colM_apply
import Theorems.Thm_GlobalTheory_SymbolCols_sum_degree_colM
import Theorems.Thm_GlobalTheory_SymbolCols_coeff_mul_congr
import Theorems.Thm_GlobalTheory_SymbolCols_exists_col
import Theorems.Thm_GlobalTheory_constantCoeff_DmonOf_congr_jet
import Theorems.Thm_GlobalTheory_constantCoeff_dmonOf_prod_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open SymbolCols
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (u : ι → Fin d → k) (lam : Fin n → ι → Fin d → k) (α : ι → k) (al : ι × Fin n →₀ ℕ) (P : MvPolynomial (ι × Fin n) k) (g E : Fin n → PS k 1 d), P.IsHomogeneous al.degree → (∀ b l l', al (l, b) ≠ 0 → (∃ mo ∈ P.support, mo (l', b) ≠ 0) → ∑ i, lam b l i * u l' i = if l = l' then α l else 0) → (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (g b) = coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) = P.coeff al * ∏ b, ((∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b)) := by
  intro R k _ _ φ d G ι _ _ n u lam α al P g E hP hpair hg
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hP (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  have hval : ∀ mo ∈ P.support, ∀ b, (colM mo b).degree ≤ (colM al b).degree →
      constantCoeff (DmonOf (G.mapF φ) u (colM mo b) (g b * E b)) =
        if colM mo b = colM al b then
          (∏ l, ((al (l, b)).factorial : k) * α l ^ al (l, b)) * constantCoeff (E b) else 0 := by
    intro mo hmo b hb
    have hle : (colM mo b).degree ≤ al.degree := by
      rw [← hdeg mo hmo, ← sum_degree_colM]
      exact Finset.single_le_sum (f := fun b => (colM mo b).degree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    rw [constantCoeff_DmonOf_congr_jet k d (G.mapF φ) ι u (colM mo b) _ _
      (fun m hm => coeff_mul_congr al.degree _ _ (E b) (hg b) m (hm.trans hle))]
    have := constantCoeff_dmonOf_prod_linear R k φ d G ι u (lam b) α (colM al b) (colM mo b) (E b)
      (fun l l' hl hl' => hpair b l l' (by rwa [colM_apply] at hl)
        ⟨mo, hmo, by rwa [colM_apply] at hl'⟩) hb
    simpa only [colM_apply] using this
  rw [Finset.sum_eq_single al]
  · by_cases hal : al ∈ P.support
    · congr 1
      exact Finset.prod_congr rfl fun b _ => by rw [hval al hal b le_rfl, if_pos rfl]
    · rw [MvPolynomial.notMem_support_iff.1 hal, zero_mul, zero_mul]
  · intro mo hmo hne
    obtain ⟨b, hb, hb'⟩ := exists_col mo al (hdeg mo hmo) hne
    rw [Finset.prod_eq_zero (Finset.mem_univ b) (by rw [hval mo hmo b hb, if_neg hb']), mul_zero]
  · intro hal
    rw [MvPolynomial.notMem_support_iff.1 hal, zero_mul]
end GlobalTheory
