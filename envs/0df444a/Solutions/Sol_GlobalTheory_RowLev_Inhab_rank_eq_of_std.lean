-- Prove2me | solution 1 for GlobalTheory.RowLev.Inhab.rank_eq_of_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:13.163151+00:00
-- url     : https://prove2.me/submissions/32154790-dff6-4dc3-b152-cae1182a6193

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_absNorm_eq
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_prime
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_rank_unique
import Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_frame

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.RowLev
open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Matrix
open Formalism.UG Formalism.UG.P
open scoped TensorProduct
open Inhab
open GlobalTheory.RowLev.Inhab
namespace GlobalTheory.RowLev.Inhab
theorem _root_.solution {I : AutInst} (hI : ∀ y, y ∈ I.Lf ↔ ∀ i, y i ∈ IntAf I.F I.E) {N p : ℕ}
    {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w) : N = I.n :=
  fr.rank_unique (exists_frame I hI p fr.prime w fr.absNorm_eq).choose
end GlobalTheory.RowLev.Inhab
