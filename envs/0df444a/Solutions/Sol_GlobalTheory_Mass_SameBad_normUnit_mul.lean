-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.normUnit_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:40.210533+00:00
-- url     : https://prove2.me/submissions/030fa1b7-4f59-43eb-ad67-8f797055ed43

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
import Theorems.Thm_GlobalTheory_Mass_SameBad_normUnit_iff
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_Mass_LocWitt_Rel_trans
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
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (h : NormUnit P x ↔ NormUnit P y) : NormUnit P (x * y) := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) :=
    ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField K)⟩
  have hx' : v.valuation K x ≠ 0 := by simpa using hx
  have hy' : v.valuation K y ≠ 0 := by simpa using hy
  have e1 := normUnit_iff v hc (WithZero.exp_log hx').symm
  have e2 := normUnit_iff v hc (WithZero.exp_log hy').symm
  have e3 := normUnit_iff v hc (x := x * y)
    (m := WithZero.log (v.valuation K x) + WithZero.log (v.valuation K y))
    (by rw [map_mul, WithZero.exp_add, WithZero.exp_log hx', WithZero.exp_log hy'])
  exact e3.2 (Int.even_add.2 (e1.symm.trans (h.trans e2)))
end GlobalTheory.Mass.SameBad
