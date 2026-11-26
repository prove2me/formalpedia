-- Prove2me | solution 1 for GlobalTheory.map_mem_upperTriangularGL
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:49:53.945697+00:00
-- url     : https://prove2.me/submissions/4833dfab-e8cd-4262-a3e6-db99462316ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable (ι R : Type*) [CommRing R] [Fintype ι] [LinearOrder ι]
variable {ι R}
theorem _root_.solution {S : Type*} [CommRing S] (f : R →+* S) {g : GL ι R}
    (hg : g ∈ upperTriangularGL ι R) :
    Matrix.GeneralLinearGroup.map f g ∈ upperTriangularGL ι S := by
  show Matrix.IsUpperTriangular ((Matrix.GeneralLinearGroup.map f g : GL ι S) : Matrix ι ι S)
  intro i j hij
  have h0 : (g : Matrix ι ι R) i j = 0 := hg hij
  show f ((g : Matrix ι ι R) i j) = 0
  rw [h0, map_zero]

