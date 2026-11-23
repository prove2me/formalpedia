-- Prove2me | solution 1 for GlobalTheory.InducedPBW.c_strip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:29.098611+00:00
-- url     : https://prove2.me/submissions/95a020be-f35d-49ac-b0e5-b3d2313bd3f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_strip_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
variable {g : Type*} [LieRing g] [LieAlgebra R g]
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
include hce
omit [Fintype ι]
namespace GlobalTheory.InducedPBW
theorem _root_.solution {s : Finset ι} {i : ι} (hi : i ∈ s) (x : g) : c i (strip e c s x) = 0 := by
  simp [strip_apply, hce, hi]
end GlobalTheory.InducedPBW
