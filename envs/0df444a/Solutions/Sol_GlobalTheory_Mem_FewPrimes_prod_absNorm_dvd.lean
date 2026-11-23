-- Prove2me | solution 1 for GlobalTheory.Mem.FewPrimes.prod_absNorm_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:41:00.969807+00:00
-- url     : https://prove2.me/submissions/709ca614-32ea-4ba0-b3b0-c335ef6f3d15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimeMemHeightOneSpectrum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.FewPrimes
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.FewPrimes
theorem _root_.solution (s : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K))
    (h : ∀ v ∈ s, v.asIdeal ∣ I) :
    ∏ v ∈ s, Ideal.absNorm v.asIdeal ∣ Ideal.absNorm I := by
  have h1 : ∏ v ∈ s, v.asIdeal ∣ I :=
    Finset.prod_dvd_of_coprime
      (fun a _ b _ hab => HeightOneSpectrum.isCoprime_of_ne _ _ hab) h
  rw [← map_prod]
  exact map_dvd _ h1
end GlobalTheory.Mem.FewPrimes
