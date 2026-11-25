-- Prove2me | solution 1 for GlobalTheory.Mem.An.Model.span_mem_principalRayGroup_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:04:26.845955+00:00
-- url     : https://prove2.me/submissions/431da1a2-8983-4e9b-b1b9-44d3e1d9a4c5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_RayPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NormOneSevenOneTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset ArithmeticFunction NumberField IsDedekindDomain
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.An GlobalTheory.Mem.An.Model
namespace GlobalTheory.Mem.An.Model
theorem _root_.solution {K : Type} [Field K] [NumberField K] (a : 𝓞 K) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    (h : (I : FractionalIdeal (𝓞 K)⁰ K) = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) :
    I ∈ rayP (⊤ : Ideal (𝓞 K)) :=
  Subgroup.subset_closure ⟨a, Submodule.mem_top, h⟩
end GlobalTheory.Mem.An.Model
