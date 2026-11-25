-- Prove2me | solution 1 for GlobalTheory.MaxLatDet.mem_locR_iff_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:32:59.455807+00:00
-- url     : https://prove2.me/submissions/b0cd5977-5409-4183-b856-2cef989e3093

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsMaxVector
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeLocalStructureDiscriminan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MaximalHermitianLatticeBadPrimesIffGramDet
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_hcompl
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_alg_mem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locDual_mem_locR
import Theorems.Thm_GlobalTheory_MassOrth_mem_locR_iff


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
open GlobalTheory GlobalTheory.MaxLatDet
open IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace GlobalTheory.MaxLatDet
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) (hw : conjIdeal (K := K) w.asIdeal = w.asIdeal)
    (k : K) : k ∈ locR (K := K) w.asIdeal ↔ w.valuation K k ≤ 1 := by
  refine ⟨fun hk => ((GlobalTheory.MassOrth.mem_locR_iff w k).1 hk).1, fun hk => ?_⟩
  obtain ⟨n, d, hnd⟩ := w.exists_primeCompl_mul_eq_of_integer k hk
  refine (locDual_mem_locR _ _).2 ⟨d, locBasic_mem_hcompl _ _ d.2 (by rw [hw]; exact d.2), ?_⟩
  rw [mul_comm, hnd]
  exact locDual_alg_mem _
end GlobalTheory.MaxLatDet
