-- Prove2me | solution 1 for GroundTheory.Automorphic.mem_unitaryPoints
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:45:37.3392+00:00
-- url     : https://prove2.me/submissions/aff43eed-ff70-4d5d-a551-fdbf8343f247

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HermitianSpaces
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryGroupScheme

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable (F E : Type*) [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable (R S T : Type*) [CommRing R] [Algebra F R] [CommRing S] [Algebra F S]
  [CommRing T] [Algebra F T]
variable {F E H R S T}
namespace GroundTheory.Automorphic
theorem _root_.solution {g : GL ι (R ⊗[F] E)} :
    g ∈ unitaryPoints F E H R ↔
      ((g : Matrix ι ι (R ⊗[F] E)).map (conjBase F E R))ᵀ *
        H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) * g =
      H.map (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E) := Iff.rfl
end GroundTheory.Automorphic
