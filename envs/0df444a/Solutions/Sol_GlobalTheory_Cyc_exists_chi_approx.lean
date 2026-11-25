-- Prove2me | solution 1 for GlobalTheory.Cyc.exists_chi_approx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:37:13.934428+00:00
-- url     : https://prove2.me/submissions/c503945b-8eb6-454d-9c11-1513c80f50d9

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormPrimitiveRootPrimePowSubOnePadicComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormEqZpowOfMemMaxUnramifiedSubfieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankCyclotomicExtAndCyclotomicCharSurjective
import Theorems.Thm_GlobalTheory_Cyc_minpoly_unramifiedSubfield_eq_cyclotomic
import Theorems.Thm_GlobalTheory_Cyc_exists_primitiveRoot_Om

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cyc
open Formalism.BasicNotions Formalism.BasicNotions.Loc Polynomial
open scoped IntermediateField
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc
theorem _root_.solution (K : FinExt l) (χ : GQ l →* ℚ_[l]ˣ) (hχ : IsCyc χ) (u : ℚ_[l])
    (hu : ‖u‖ = 1) (j : ℕ) (hj : 1 ≤ j) :
    ∃ g ∈ (K0 K).fixingSubgroup, ‖(χ g : ℚ_[l]) - u‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
  have hlp : l.Prime := Fact.out
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hlp.one_lt
  have hpos : 0 < l ^ j := pow_pos hlp.pos j
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_Om (l := l) j
  let z : ℤ_[l] := ⟨u, hu.le⟩
  set a := z.appr j with ha
  have hza : ‖u - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (PadicInt.norm_le_pow_iff_mem_span_pow _ j).2 (PadicInt.appr_spec j z)
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at this
    exact this
  have hlt : (l : ℝ) ^ (-(j : ℤ)) < 1 := zpow_lt_one_of_neg₀ hl1 (by omega)
  have hna : ‖(a : ℚ_[l])‖ = 1 := by
    have h1 : (a : ℚ_[l]) = u + -(u - a) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, hu, norm_neg,
      max_eq_left (hza.trans hlt.le)]
    rw [hu, norm_neg]
    exact (hza.trans_lt hlt).ne'
  have hcop : a.Coprime (l ^ j) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, hlp.coprime_iff_not_dvd]
    intro hd
    have : ‖((a : ℤ) : ℚ_[l])‖ < 1 := Padic.norm_intCast_lt_one_iff.2 (by exact_mod_cast hd)
    rw [Int.cast_natCast, hna] at this
    exact lt_irrefl _ this
  have hζa := hζ.pow_of_coprime a hcop
  have hconj : IsConjRoot ↥(K0 K) (ζ ^ a) ζ := by
    unfold IsConjRoot
    rw [minpoly_unramifiedSubfield_eq_cyclotomic K j hj ζ hζ, minpoly_unramifiedSubfield_eq_cyclotomic K j hj _ hζa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  refine ⟨σ.restrictScalars ℚ_[l], fun x => σ.commutes x, ?_⟩
  obtain ⟨b, hb, hb'⟩ := hχ (σ.restrictScalars ℚ_[l]) j ζ hζ.pow_eq_one
  have hab : ζ ^ a = ζ ^ b := hσ.symm.trans hb'
  have hmod : a ≡ b [MOD l ^ j] := by
    rw [hζ.eq_orderOf]
    exact (hζ.isOfFinOrder hpos.ne').pow_eq_pow_iff_modEq.1 hab
  have hba : ‖(b : ℚ_[l]) - a‖ ≤ (l : ℝ) ^ (-(j : ℤ)) := by
    have := (Padic.norm_int_le_pow_iff_dvd ((b : ℤ) - a) j (p := l)).2
      (by exact_mod_cast hmod.dvd)
    simpa using this
  have h1 : (χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - u =
      ((χ (σ.restrictScalars ℚ_[l]) : ℚ_[l]) - b) + (((b : ℚ_[l]) - a) + -(u - a)) := by ring
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb ?_)
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hba ?_)
  rwa [norm_neg]
end GlobalTheory.Cyc
