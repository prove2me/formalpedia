-- Prove2me | solution 1 for GlobalTheory.WpFam.wp_wpd_separate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:40.846542+00:00
-- url     : https://prove2.me/submissions/c963fdeb-15bb-4262-8842-3c3beef621ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembershipStatement
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EllipticOnePole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqOfWeierstrassPDerivWeierstrassPTorsionEq
import Theorems.Thm_Formalism_L2_Th1_F_pDerivZero
import Theorems.Thm_Formalism_L2_Th1_F_pInjective
import Theorems.Thm_GlobalTheory_T_torsionPointOfLatticeTau_lattice_membership


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam
namespace GlobalTheory.WpFam
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (x y : Fin 2 → ZMod N), x ≠ 0 → y ≠ 0 →
    wp N x τ = wp N y τ → wpd N x τ = wpd N y τ → x = y := by
  intro N _ τ x y hx hy h1 h2
  obtain ⟨hsub, -, hmem, -, -⟩ := GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hz : tors N τ x ∉ (tauPair τ).lattice := fun h => hx ((hmem x).1 h)
  have hw : tors N τ y ∉ (tauPair τ).lattice := fun h => hy ((hmem y).1 h)
  rw [wp, wp, div_left_inj' (pow_ne_zero _ hc)] at h1
  rw [wpd, wpd, div_left_inj' (pow_ne_zero _ hc)] at h2
  rcases (Formalism.L2.Th1.F.pInjective (tauPair τ) _ _ hz hw).1 h1 with h | h
  · exact (hsub x y).1 h
  · apply (hsub x y).1
    have e : tors N τ x = -tors N τ y + ((⟨_, h⟩ : (tauPair τ).lattice) : ℂ) := by
      simp
    have h3 : (tauPair τ).derivWeierstrassP (tors N τ x) =
        -(tauPair τ).derivWeierstrassP (tors N τ y) := by
      conv_lhs => rw [e]
      rw [PeriodPair.derivWeierstrassP_add_coe, PeriodPair.derivWeierstrassP_neg]
    have h0 : (tauPair τ).derivWeierstrassP (tors N τ y) = 0 := by
      rw [h2] at h3
      linear_combination h3 / 2
    have h4 := (Formalism.L2.Th1.F.pDerivZero (tauPair τ) _ hw).1 h0
    have h5 := (tauPair τ).lattice.sub_mem h h4
    convert h5 using 1
    ring
end GlobalTheory.WpFam
