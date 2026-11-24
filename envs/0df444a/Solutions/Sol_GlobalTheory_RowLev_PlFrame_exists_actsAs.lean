-- Prove2me | solution 1 for GlobalTheory.RowLev.PlFrame.exists_actsAs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:31:19.209805+00:00
-- url     : https://prove2.me/submissions/5e3e8c0e-df7e-4fd9-97c2-996b55425511

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Theorems.Thm_GlobalTheory_RowLev_Inhab_exists_matrix
import Theorems.Thm_GlobalTheory_RowLev_PlFrame_c_eq_zero_iff

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
open GlobalTheory.RowLev.PlFrame
variable {I : AutInst} {N p : ℕ} {w : HeightOneSpectrum (𝓞 I.E)} (fr : PlFrame I N p w)
namespace GlobalTheory.RowLev.PlFrame
theorem _root_.solution {x : I.Gf} (hx : x ∈ I.Kset) : ∃ M, fr.ActsAs x M := by
  obtain ⟨M, hM⟩ := exists_matrix fr.r (ZMod.ringHom_surjective _) fr.c fr.c_surj (extId I w.asIdeal)
    fr.c_eq_zero_iff (latEnd hx)
  exact ⟨M, fun y _ => hM y⟩
end GlobalTheory.RowLev.PlFrame
