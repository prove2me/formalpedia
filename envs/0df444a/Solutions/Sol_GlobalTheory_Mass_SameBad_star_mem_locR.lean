-- Prove2me | solution 1 for GlobalTheory.Mass.SameBad.star_mem_locR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:59:35.111804+00:00
-- url     : https://prove2.me/submissions/3425a839-aec5-4922-9625-f681de41fe6f

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
import Theorems.Thm_GlobalTheory_Mass_LocWitt_star_int
import Theorems.Thm_GlobalTheory_MaxLatStruct_star_int
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L3_StandardSymmetricSums_star_int


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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) (hc : conjIdeal (K := K) P = P) {a : K}
    (ha : a ∈ locR (K := K) P) : star a ∈ locR (K := K) P := by
  have mR : ∀ a : K, a ∈ locR (K := K) P ↔ ∃ s, s ∉ P ∧ ∃ r : 𝓞 K,
      algebraMap (𝓞 K) K r = algebraMap (𝓞 K) K s * a := fun a =>
    exists_congr fun s => and_congr (LocWitt.mem_hcompl hP hc s)
      (by rw [Submodule.mem_one, Algebra.smul_def])
  obtain ⟨s, hs, r, e⟩ := (mR a).1 ha
  obtain ⟨s', es⟩ := LocWitt.star_int s
  obtain ⟨r', er⟩ := LocWitt.star_int r
  refine (mR _).2 ⟨s', fun a => hs ?_, r', by rw [er, es, e, star_mul']⟩
  rw [← hc]
  exact Ideal.subset_span ⟨s', a, by rw [es, star_star]⟩
end GlobalTheory.Mass.SameBad
