-- Prove2me | solution 1 for GlobalTheory.QSA.TraceOpenProd.continuous_coord
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:44:59.993748+00:00
-- url     : https://prove2.me/submissions/3c08810d-790e-4b91-9d49-a39a294f1423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.TraceOpenProd
variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}
namespace GlobalTheory.QSA.TraceOpenProd
theorem _root_.solution {R : Type} [CommRing R] [TopologicalSpace R] {a b : R} (i : Fin 4) :
    Continuous (fun x : ℍ[R, a, b] => coords x i) :=
  (continuous_apply i).comp continuous_induced_dom
end GlobalTheory.QSA.TraceOpenProd
