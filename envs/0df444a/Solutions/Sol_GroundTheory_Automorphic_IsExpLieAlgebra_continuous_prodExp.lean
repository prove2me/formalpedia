-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.continuous_prodExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:36.62908+00:00
-- url     : https://prove2.me/submissions/cc738cf0-a706-443e-b35c-468c4ff4056c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
import Theorems.Thm_GroundTheory_Automorphic_contDiff_prodExpVal
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_isEmbedding_coe_coe
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_val_prodExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable {G : Subgroup 𝔸ˣ} (h : IsExpLieAlgebra G 𝔤)
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution {d : ℕ} (X : Fin d → 𝔤) : Continuous (h.prodExp X) := by
  rw [isEmbedding_coe_coe.continuous_iff]
  have : (fun x : G => ((x : 𝔸ˣ) : 𝔸)) ∘ h.prodExp X = prodExpVal (fun i => (X i : 𝔸)) :=
    funext fun t => h.val_prodExp X t
  rw [this]; exact (contDiff_prodExpVal _).continuous
end GroundTheory.Automorphic.IsExpLieAlgebra
