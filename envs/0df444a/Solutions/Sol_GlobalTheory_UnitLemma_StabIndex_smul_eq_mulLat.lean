-- Prove2me | solution 1 for GlobalTheory.UnitLemma.StabIndex.smul_eq_mulLat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:10:58.933939+00:00
-- url     : https://prove2.me/submissions/a7bd304e-69c6-44ec-a6f4-f7f3857ece15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RelIndexNeZeroOfBetween

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open scoped Pointwise
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.StabIndex
variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A]
namespace GlobalTheory.UnitLemma.StabIndex
theorem _root_.solution (t : Aˣ) (L : Submodule O A) : t • L = mulLat O (t : A) L := by
  ext y
  simp [mulLat, Submodule.mem_smul_pointwise_iff_exists, Units.smul_def]
end GlobalTheory.UnitLemma.StabIndex
