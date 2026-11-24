-- Prove2me | solution 1 for GlobalTheory.WeylInt.lowerTriIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:28:08.12359+00:00
-- url     : https://prove2.me/submissions/90c7e15a-3518-440b-9370-6dd04ab02dac

import Mathlib
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LowerTriIntegral
import Theorems.Thm_GlobalTheory_WeylInt_lowerTri_of_interlaced
import Theorems.Thm_GlobalTheory_WeylInt_intQ_apply
import Theorems.Thm_GlobalTheory_WeylInt_intQ_bidet
import Theorems.Thm_Formalism_GradedWeylDivisibility_bidetMem
import Theorems.Thm_Formalism_GradedWeylDivisibility_colSums
import Theorems.Thm_Formalism_GradedWeylDivisibility_column_lex_bideterminant
import Theorems.Thm_Formalism_GradedWeylDivisibility_lcassem_sub_lt
import Theorems.Thm_Formalism_GradedWeylDivisibility_leadInterlaced
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_sSYTExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.WeylInt
open Formalism.GradedWeylDivisibility
namespace GlobalTheory.WeylInt
theorem _root_.solution : Formalism.GradedWeylDivisibility.LowerTriIntegral := by
  intro r n ν
  suffices key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl ℚ r n ν,
      (colLex r n).toSyn ((colLex r n).degree f) = d →
      (∀ e : Fin r × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e f = z) →
      ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f = intQ r n Q' by
    intro f hf hint
    exact key _ f hf rfl hint
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro f hf hd hz
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0, map_zero]⟩
    set m := (colLex r n).degree f with hm
    have hint : Interlaced m := leadInterlaced ℚ r n ν f hf hf0
    have hcol : ∀ t : Fin n, ∑ a : Fin r, m (a, t) = ν t :=
      colSums ℚ r n ν f hf m (((colLex r n).degree_mem_support_iff f).mpr hf0)
    obtain ⟨K, sz, hsz, I, hshape, hmono, hexp⟩ := sSYTExists r n ν m hcol hint
    obtain ⟨hdeg, hlc⟩ := column_lex_bideterminant ℚ r n K sz hsz I hmono
    have hmem : bideterminant ℚ sz hsz I ∈ dualWeyl ℚ r n ν := by
      have := bidetMem ℚ r n K sz hsz I
      rwa [hshape] at this
    obtain ⟨z, hzm⟩ := hz m (lowerTri_of_interlaced hint)
    have hlcf : (colLex r n).leadingCoeff f = (z : ℚ) := hzm
    set f' := f - (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I with hf'
    have hf'mem : f' ∈ dualWeyl ℚ r n ν := Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hmem)
    have hb : (colLex r n).leadingCoeff f • bideterminant ℚ sz hsz I = intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [map_smul, intQ_bidet, hlcf, Int.cast_smul_eq_zsmul]
    have hdecomp : f = f' + intQ r n (z • bideterminant ℤ sz hsz I) := by
      rw [hf', ← hb]; abel
    have hQ : ∃ Q' : MvPolynomial (Fin r × Fin n) ℤ, f' = intQ r n Q' := by
      by_cases h0 : f' = 0
      · exact ⟨0, by rw [h0, map_zero]⟩
      have hlt := lcassem_sub_lt (colLex r n) (f := f) (g := bideterminant ℚ sz hsz I) (hdeg.trans hexp) hlc h0
      refine ih _ (hd ▸ hlt) f' hf'mem rfl fun e he => ?_
      obtain ⟨w, hw⟩ := hz e he
      refine ⟨w - coeff e (z • bideterminant ℤ sz hsz I), ?_⟩
      rw [hf', hb, coeff_sub, hw, intQ_apply, coeff_map]
      simp only [Int.cast_sub, eq_intCast]
    obtain ⟨Q', hQ'⟩ := hQ
    exact ⟨Q' + z • bideterminant ℤ sz hsz I, by rw [map_add, ← hQ']; exact hdecomp⟩
end GlobalTheory.WeylInt
