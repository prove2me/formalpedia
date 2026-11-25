-- Prove2me | solution 1 for GlobalTheory.PlaceSum.finite_resChar_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:58:18.091317+00:00
-- url     : https://prove2.me/submissions/2a31943e-6a76-4251-979e-c0b8bd47e9ce

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumFinitePlacesLeSumOverPrimes
import Theorems.Thm_GlobalTheory_PlaceSum_mem_primesOverFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Pj
open GlobalTheory GlobalTheory.PlaceSum
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.PlaceSum
theorem _root_.solution {p : ℕ} (hp : p.Prime) :
    {la : HeightOneSpectrum (𝓞 K) | resCharOf la = p}.Finite := by
  refine Set.Finite.of_finite_image (f := fun la => la.asIdeal) ?_
    (fun a _ b _ h => HeightOneSpectrum.ext h)
  refine (IsDedekindDomain.primesOverFinset (Ideal.span {(p : ℤ)}) (𝓞 K)).finite_toSet.subset ?_
  rintro _ ⟨la, hla, rfl⟩
  exact mem_primesOverFinset hp la hla
end GlobalTheory.PlaceSum
