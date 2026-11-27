-- Prove2me | solution 1 for GlobalTheory.ThetaClaimsCompare.exists_harmA_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:34:16.314875+00:00
-- url     : https://prove2.me/submissions/74fb43eb-32b4-461c-a8df-ac9f7889a68c

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThProps
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_JetRangeLevelFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLastEntryPosNotLastPos
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_coeff_mem
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_ne_zero
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_mem_harmonic
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_rowInvariant
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_minorMonomial_rowDegree
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_not_inPsi_conjugate
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_mult_of_inPsi
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_mult_of_not_inPsi
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_antitone_trunc
import Theorems.Thm_GlobalTheory_ThetaClaimsCompare_harmA_trunc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaClaimsCompare
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.JetRangeLevelFactor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
namespace GlobalTheory.ThetaClaimsCompare
theorem _root_.solution {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : RowsDominant Dw a) (hn : Dw.p + Dw.q ≤ n) :
    ∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0 := by
  classical
  let col : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin n := fun τ i =>
    if h : InPsi H τ then ⟨i, by have := i.isLt; have := mult_of_inPsi (Dw := Dw) h; omega⟩
    else ⟨Dw.p + i, by have := i.isLt; have := mult_of_not_inPsi (Dw := Dw) h; omega⟩
  have hinj : ∀ τ, Function.Injective (col τ) := by
    intro τ i j hij
    have := congrArg Fin.val hij
    by_cases h : InPsi H τ
    · simp only [col, dif_pos h] at this
      exact Fin.ext this
    · simp only [col, dif_neg h] at this
      exact Fin.ext (by omega)
  have hdis : ∀ τ, InPsi H τ → ∀ i j, col τ i ≠ col (ComplexEmbedding.conjugate τ) j := by
    intro τ h i j hij
    have := congrArg Fin.val hij
    simp only [col, dif_pos h, dif_neg (not_inPsi_conjugate h)] at this
    have := i.isLt
    have := mult_of_inPsi (Dw := Dw) h
    omega
  rw [← harmA_trunc]
  exact ⟨minorsP Dw.mult n col c.F fun τ i => trunc Dw a (τ, i),
    ⟨⟨minorMonomial_mem_harmonic _ _ _ _ _ _ hdis _, minorMonomial_rowInvariant _ _ _ _ _,
      minorMonomial_rowDegree _ _ _ _ _ (antitone_trunc ha) fun τ => if_neg (lt_irrefl _)⟩,
      minorMonomial_coeff_mem _ _ _ _ _ _⟩, minorMonomial_ne_zero _ _ _ _ hinj _⟩
end GlobalTheory.ThetaClaimsCompare
