-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.defectAt_vw_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:38:45.146263+00:00
-- url     : https://prove2.me/submissions/bd7fb8c9-5a96-4559-9a37-76cdc6fe9db6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_HeightDefect_SchurLatticeConjugates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
namespace GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
theorem _root_.solution {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (σ : E →+* K) (n' : ℕ+) (a : ℕ) (la : HeightOneSpectrum (𝓞 K)) :
    defectAt_vw σ n' a la ≤ defect_vw E n' a la :=
  Finset.le_sup (f := fun σ : E →+* K => defectAt_vw σ n' a la) (Finset.mem_univ σ)
end GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
