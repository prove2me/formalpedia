-- Prove2me | solution 1 for GlobalTheory.residue_eval_map_eq_aeval
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:31:32.737624+00:00
-- url     : https://prove2.me/submissions/58ccc0b4-9fd1-4ce0-870a-f4a19e6187b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPrimitiveElementComplete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R]
    [IsLocalRing R] (φ : A →+* R) [IsLocalHom φ] (P : A[X]) (x : R) :
    letI := (ResidueField.map φ).toAlgebra
    residue R ((P.map φ).eval x) = aeval (residue R x) (P.map (residue A)) := by
  letI := (ResidueField.map φ).toAlgebra
  rw [aeval_def, eval₂_map, eval_map, hom_eval₂]
  congr 1
end GlobalTheory
