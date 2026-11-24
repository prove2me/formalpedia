-- Prove2me | solution 1 for GlobalTheory.QuadSymbol.NormIndex.isSquare_mul_of_near
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:04:55.964458+00:00
-- url     : https://prove2.me/submissions/7e6e50ea-c4c4-4584-9ae0-3b647d0015bc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_QuadraticExtNormFormOverAlgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_UnitNormFormAtOddPlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsUnitMulSqQuadraticDefectStep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsGlobalUniformizerResidueRepresentatives
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSubSqLtOneOfTwoLtOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareMulOfNonsquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfValuedSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsSquareMulInfinite
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_map_two_le
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_isSquare_of_near
import Theorems.Thm_GlobalTheory_QuadSymbol_NormIndex_exists_sq_add_of_not
import Theorems.Thm_GlobalTheory_LocalQuad_isSquare_of_valued_sub_one_lt
import Theorems.Thm_GlobalTheory_QNorm_isSquare_mul_of_nonsquare_units
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain IsLocalRing
open scoped WithZero
open GlobalTheory GlobalTheory.QuadSymbol
open GlobalTheory.QuadSymbol.NormIndex
variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace GlobalTheory.QuadSymbol.NormIndex
theorem _root_.solution {x y : v.adicCompletion F} (hx : Valued.v x = 1) (hy : Valued.v y = 1)
    (hx4 : Valued.v (x - 1) ≤ Valued.v (4 : v.adicCompletion F))
    (hy4 : Valued.v (y - 1) ≤ Valued.v (4 : v.adicCompletion F))
    (hx' : ¬ IsSquare x) (hy' : ¬ IsSquare y) : IsSquare (x * y) := by
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  rcases (map_two_le (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰)).eq_or_lt with h2 | h2
  · exact GlobalTheory.QNorm.isSquare_mul_of_nonsquare_units F v h2 x y hx hy hx' hy'
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hres : ∀ z : v.adicCompletionIntegers F,
      residue (v.adicCompletionIntegers F) z = 0 ↔ Valued.v (z : v.adicCompletion F) < 1 := by
    intro z
    rw [residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
      HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    exact ⟨fun h => lt_of_le_of_ne z.2 h, fun h => h.ne⟩
  have h20 : (2 : ResidueField (v.adicCompletionIntegers F)) = 0 := by
    have := (hres 2).2 h2
    rwa [map_ofNat] at this
  have hpos : 0 < Valued.v (4 : v.adicCompletion F) :=
    zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (by norm_num))
  have key : ∀ r s : v.adicCompletionIntegers F,
      residue _ s ^ 2 + residue _ s = residue _ r → IsSquare (1 + 4 * (r : v.adicCompletion F)) := by
    intro r s h
    have h1 := (hres (r - (s ^ 2 + s))).1 (by rw [map_sub, map_add, map_pow, h, sub_self])
    refine isSquare_of_near Valued.v (GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v)
      (s := 1 + 2 * (s : v.adicCompletion F)) (Valuation.map_one_add_of_lt _ ?_) ?_
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' s.2) h2
    · rw [show 1 + 4 * (r : v.adicCompletion F) - (1 + 2 * (s : v.adicCompletion F)) ^ 2 =
        4 * ((r : v.adicCompletion F) - ((s : v.adicCompletion F) ^ 2 + s)) by ring, map_mul]
      exact mul_lt_of_lt_one_right hpos h1
  let r : v.adicCompletionIntegers F := ⟨(x - 1) / 4, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hx4 zero_le⟩
  let t : v.adicCompletionIntegers F := ⟨(y - 1) / 4, by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact div_le_one_of_le₀ hy4 zero_le⟩
  have ex : x = 1 + 4 * (r : v.adicCompletion F) := by
    change x = 1 + 4 * ((x - 1) / 4)
    ring
  have ey : y = 1 + 4 * (t : v.adicCompletion F) := by
    change y = 1 + 4 * ((y - 1) / 4)
    ring
  obtain ⟨s, hs⟩ := exists_sq_add_of_not h20 (a := residue _ r) (b := residue _ t)
    (fun s h => by
      obtain ⟨s, rfl⟩ := residue_surjective s
      exact hx' (ex ▸ key r s h))
    (fun s h => by
      obtain ⟨s, rfl⟩ := residue_surjective s
      exact hy' (ey ▸ key t s h))
  obtain ⟨s, rfl⟩ := residue_surjective s
  have := key (r + t + 2 * (2 * r * t)) s (by
    rw [hs, map_add, map_add, map_mul, map_ofNat, h20, zero_mul, add_zero])
  have e : x * y = 1 + 4 * ((r : v.adicCompletion F) + t + 2 * (2 * r * t)) := by
    rw [ex, ey]; ring
  rw [e]
  exact this
end GlobalTheory.QuadSymbol.NormIndex
