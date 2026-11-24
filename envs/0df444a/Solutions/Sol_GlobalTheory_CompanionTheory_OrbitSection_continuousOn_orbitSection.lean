-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OrbitSection.continuousOn_orbitSection
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:10:27.50811+00:00
-- url     : https://prove2.me/submissions/b501a6a3-f035-4c00-9de9-583b575b75c4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_coe_orbitSection
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_coe_orbitSection_inv
import Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_continuousOn_shear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OrbitSection
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.OrbitSection
theorem _root_.solution (j : Fin n) (ζ : Fin n → k) (h0 : ζ j ≠ 0) :
    ContinuousOn (orbitSection j ζ) {ξ | ξ j ≠ 0} := by
  have hinv : ContinuousOn (fun ξ : Fin n → k => -(ξ j)⁻¹) {ξ | ξ j ≠ 0} :=
    (((continuous_apply j).continuousOn).inv₀ fun ξ h => h).neg
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨(continuousOn_iff_continuous_restrict.1
      (continuousOn_shear j ζ (c := fun _ => (ζ j)⁻¹) continuousOn_const)).congr fun ξ => ?_,
    (continuousOn_iff_continuous_restrict.1 (continuousOn_shear j ζ hinv)).congr fun ξ => ?_⟩
  · exact (coe_orbitSection j ζ ξ.1 h0 ξ.2).symm
  · exact (coe_orbitSection_inv j ζ ξ.1 h0 ξ.2).symm
end GlobalTheory.CompanionTheory.OrbitSection
