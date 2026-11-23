-- Prove2me | solution 1 for GlobalTheory.InducedPBW.le_support_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:48:14.944745+00:00
-- url     : https://prove2.me/submissions/abc3fdcf-6890-45c9-807d-7192e9d7fef6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd

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
variable (hf : step e c act δ = δ)
include hf
omit hce hf [Fintype ι]
namespace GlobalTheory.InducedPBW
theorem _root_.solution {i j : ι} {J : ι →₀ ℕ} (hJ : ∀ k ∈ J.support, i ≤ k) (hij : i ≤ j) :
    ∀ k ∈ (Finsupp.single j 1 + J).support, i ≤ k := by
  intro k hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h1 | h1
  · exact hij.trans (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge
  · exact hJ k h1
end GlobalTheory.InducedPBW
