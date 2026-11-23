-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.LocalDens.red_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:29:07.210875+00:00
-- url     : https://prove2.me/submissions/13cfe384-1116-419f-b280-51560042bf72

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
namespace GlobalTheory.CompanionTheory.LocalDens
theorem _root_.solution (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k x = red ϖ k y ↔ ∀ i j, ϖ ^ k ∣ x i j - y i j := by
  constructor
  · intro h i j
    have := congrFun (congrFun h i) j
    simp only [red, Matrix.map_apply] at this
    exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 this)
  · intro h
    ext i j
    simp only [red, Matrix.map_apply]
    exact Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (h i j))
end GlobalTheory.CompanionTheory.LocalDens
