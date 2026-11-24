-- Prove2me | solution 1 for GlobalTheory.RowLev.Red.map_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:15:42.875845+00:00
-- url     : https://prove2.me/submissions/2290d5f3-ea14-44b3-b412-71c92a2090df

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsApprox
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction

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
open GlobalTheory.RowLev.Red
variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)
namespace GlobalTheory.RowLev.Red
theorem _root_.solution {x : I.Gf} (hx : x ∈ I.Kset) : ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹ := ρ.toHom.map_inv ⟨x, hx⟩
end GlobalTheory.RowLev.Red
