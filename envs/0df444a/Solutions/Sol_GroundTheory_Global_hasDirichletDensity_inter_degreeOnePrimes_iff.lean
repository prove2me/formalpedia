-- Prove2me | solution 1 for GroundTheory.Global.hasDirichletDensity_inter_degreeOnePrimes_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:09:24.379738+00:00
-- url     : https://prove2.me/submissions/8c8bb1bd-4af7-4f82-8184-f7ba99d38a6a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
import Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_mono
import Theorems.Thm_GroundTheory_Global_hasDirichletDensity_iff_of_subset_of_isBoundedUnder
import Theorems.Thm_GroundTheory_Global_compl_degreeOnePrimes
import Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_higherDegreePrimes_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
variable (K)
namespace GroundTheory.Global
theorem _root_.solution (S : Set (HeightOneSpectrum (𝓞 L)))
    (δ : ℝ) : (S ∩ degreeOnePrimes K L).HasDirichletDensity δ ↔ S.HasDirichletDensity δ := by
  refine hasDirichletDensity_iff_of_subset_of_isBoundedUnder inter_subset_left ?_ δ
  obtain ⟨C, hC⟩ := primeIdealZetaSum_higherDegreePrimes_le K L
  refine isBoundedUnder_of_eventually_le (a := C)
    (eventually_nhdsWithin_of_forall fun s (hs : 1 < s) => ?_)
  refine (primeIdealZetaSum_mono ?_ hs).trans (hC s hs.le)
  intro w hw
  rw [← compl_degreeOnePrimes]
  exact fun h => hw.2 ⟨hw.1, h⟩
end GroundTheory.Global
