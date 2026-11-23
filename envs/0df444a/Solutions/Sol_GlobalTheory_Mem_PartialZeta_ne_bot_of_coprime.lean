-- Prove2me | solution 1 for GlobalTheory.Mem.PartialZeta.ne_bot_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:54.515804+00:00
-- url     : https://prove2.me/submissions/3a109928-2340-407d-b621-56228c3a67e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Mem.PartialZeta
theorem _root_.solution {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) {I : Ideal (𝓞 K)}
    (hI : IsCoprime I (Ideal.span {(M : 𝓞 K)})) : I ≠ ⊥ := by
  rintro rfl
  rw [Ideal.isCoprime_iff_sup_eq, bot_sup_eq] at hI
  exact hM hI
end GlobalTheory.Mem.PartialZeta
