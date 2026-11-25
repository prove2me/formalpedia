-- Prove2me | solution 1 for GlobalTheory.TorsionCard.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:28.659379+00:00
-- url     : https://prove2.me/submissions/262d65cd-47ff-4bb9-8a03-2cfb10248137

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCosetRepresentativesOfFiniteSubgroupPadicI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ChiOntoOfUnramified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardTorsionMulFinrank
import Theorems.Thm_GlobalTheory_TorsionCard_red_val
import Theorems.Thm_GlobalTheory_Cyc_IsCyc_norm_le_one
import Theorems.Thm_GlobalTheory_UnramValue_norm_le_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open GlobalTheory GlobalTheory.TorsionCard
variable {l : ℕ} [hl : Fact l.Prime]
namespace GlobalTheory.TorsionCard
theorem _root_.solution (h2 : l ≠ 2) (u : (ZMod l)ˣ) :
    ∃ x : ℤ_[l]ˣ, IsOfFinOrder x ∧ red l x = u := by
  classical
  have hl3 : 2 < l := lt_of_le_of_ne hl.out.two_le (Ne.symm h2)
  set a : ℤ_[l] := ((u : ZMod l).val : ℤ_[l]) with ha
  have hred_a : PadicInt.toZMod a = (u : ZMod l) := by
    rw [ha, map_natCast, ZMod.natCast_zmod_val]
  have norm_of : ∀ y : ℤ_[l], PadicInt.toZMod y ≠ 0 → ‖y‖ = 1 := by
    intro y hy
    by_contra hne
    have hlt : ‖y‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one y) hne
    apply hy
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton, ← PadicInt.norm_lt_one_iff_dvd]
    exact hlt
  have lt_of : ∀ y : ℤ_[l], PadicInt.toZMod y = 0 → ‖y‖ < 1 := by
    intro y hy
    rw [PadicInt.norm_lt_one_iff_dvd, ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hy
  let F : Polynomial ℤ_[l] := Polynomial.X ^ (l - 1) - 1
  have hF : PadicInt.toZMod (F.aeval a) = 0 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one, hred_a]
    rw [sub_eq_zero, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one]
  have hF' : PadicInt.toZMod (F.derivative.aeval a) ≠ 0 := by
    simp [F, hred_a, Polynomial.derivative_X_pow]
    rw [ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [norm_of _ hF', one_pow]; exact lt_of _ hF
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma hnorm
  have hz1 : z ^ (l - 1) = 1 := by
    simp only [F, map_sub, map_pow, Polynomial.aeval_X, map_one] at hz
    exact sub_eq_zero.mp hz
  have e : l - 1 = (l - 2) + 1 := by omega
  let x : ℤ_[l]ˣ := ⟨z, z ^ (l - 2), by rw [← pow_succ', ← e, hz1], by rw [← pow_succ, ← e, hz1]⟩
  refine ⟨x, ?_, ?_⟩
  · refine isOfFinOrder_iff_pow_eq_one.mpr ⟨l - 1, by omega, Units.ext ?_⟩
    rw [Units.val_pow_eq_pow_val]
    exact hz1
  · apply Units.ext
    rw [red_val, ← hred_a, ← sub_eq_zero, ← map_sub]
    by_contra hne
    have h1 := norm_of _ hne
    rw [norm_of _ hF'] at hza
    change ‖z - a‖ < 1 at hza
    linarith
end GlobalTheory.TorsionCard
