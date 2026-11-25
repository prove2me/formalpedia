-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.ext_PD
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:22:08.302033+00:00
-- url     : https://prove2.me/submissions/e3c345e6-4b1a-4df5-a7d1-08c7a2127278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittExtensionTotallyDefiniteHermitianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaximalIntegralHermitianLatticeOrthonormalStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemHcompl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_DefiniteHermitianIsometricOfSameBadPrimes
import Theorems.Thm_GlobalTheory_Mass_SameBad_ext_apply
import Theorems.Thm_Formalism_H_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution (hK : IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) {β : K}
    (hβ : ∀ τ : K →+* ℂ, 0 < (τ β).re) : PD (ext h β) := by
  intro τ x hx
  have e : (τ (β * (star x.2 * x.2))).re = (τ β).re * Complex.normSq (τ x.2) := by
    rw [map_mul, map_mul, hK.2.1, ← Complex.normSq_eq_conj_mul_self, Complex.re_mul_ofReal]
  rw [ext_apply, map_add, Complex.add_re, e]
  have n1 := Complex.normSq_nonneg (τ x.2)
  have b := hβ τ
  by_cases h1 : x.1 = 0
  · have h2 : x.2 ≠ 0 := fun h2 => hx (Prod.ext h1 h2)
    have : 0 < Complex.normSq (τ x.2) := Complex.normSq_pos.2 (by simpa using h2)
    simp only [h1, map_zero, Complex.zero_re, zero_add]
    positivity
  · have := hp τ _ h1
    positivity
end GlobalTheory.Mass.SameBad
