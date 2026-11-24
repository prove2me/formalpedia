-- Prove2me | solution 1 for GlobalTheory.flat_of_flat_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:26.771618+00:00
-- url     : https://prove2.me/submissions/3e4bc3e8-3b05-428b-bf51-098841265187

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_ringHom_flat_of_square
import Theorems.Thm_GlobalTheory_includeRight_faithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A B A' B' : Type*} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
namespace GlobalTheory
theorem _root_.solution {k : Type*} (K : Type*) [CommRing k] [CommRing K] [Algebra k K]
    [Module.FaithfullyFlat k K] [Algebra k A] [Algebra k B] (φ : A →ₐ[k] B)
    (h : (Algebra.TensorProduct.map (AlgHom.id k K) φ : K ⊗[k] A →+* K ⊗[k] B).Flat) :
    (φ : A →+* B).Flat :=
  ringHom_flat_of_square (by ext a; simp) (includeRight_faithfullyFlat k K A).flat
    (includeRight_faithfullyFlat k K B) h
end GlobalTheory
