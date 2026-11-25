-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.mem_locR_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:33:51.734357+00:00
-- url     : https://prove2.me/submissions/ec0e8474-a7d1-4ccb-bd92-718049b0a615

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
import Theorems.Thm_GlobalTheory_Mass_LocWitt_mem_hcompl


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.SameBad
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.Mass.SameBad
theorem _root_.solution (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (hc : conjIdeal (K := K) v.asIdeal = v.asIdeal) (a : K) :
    a ∈ locR (K := K) v.asIdeal ↔ v.valuation K a ≤ 1 := by
  have mR : a ∈ locR (K := K) v.asIdeal ↔ ∃ s, s ∉ v.asIdeal ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a :=
    exists_congr fun s => and_congr (LocWitt.mem_hcompl v.isMaximal hc s)
      (by rw [Submodule.mem_one, Algebra.smul_def])
  rw [mR]
  constructor
  · rintro ⟨s, hs, r, e⟩
    have h1 : v.valuation K (algebraMap (𝓞 K) K s) = 1 :=
      (v.valuation_eq_one_iff_notMem (K := K)).2 hs
    have h2 : v.valuation K (algebraMap (𝓞 K) K r) ≤ 1 := v.valuation_le_one (K := K) r
    rwa [e, map_mul, h1, one_mul] at h2
  · intro ha
    obtain ⟨n, d, e⟩ := v.exists_primeCompl_mul_eq_of_integer a ha
    exact ⟨d, d.2, n, by rw [← e, mul_comm]⟩
end GlobalTheory.Mass.SameBad
