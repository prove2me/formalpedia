-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.val_prodExp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:53.765331+00:00
-- url     : https://prove2.me/submissions/91a5dc63-714a-4d0a-9922-6ca4d0d9bc53

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord

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
theorem _root_.solution {d : ℕ} (X : Fin d → 𝔤) (t : Fin d → ℝ) :
    (((h.prodExp X t : G) : 𝔸ˣ) : 𝔸) = prodExpVal (fun i => (X i : 𝔸)) t := by
  let f : G →* 𝔸 := (Units.coeHom 𝔸).comp G.subtype
  show f (List.ofFn fun i => h.expG (t i • X i)).prod = _
  rw [map_list_prod, List.map_ofFn]
  simp [prodExpVal, f, Function.comp_def]
end GroundTheory.Automorphic.IsExpLieAlgebra
