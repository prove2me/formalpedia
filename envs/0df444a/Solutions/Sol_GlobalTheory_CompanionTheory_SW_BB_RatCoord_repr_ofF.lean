-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.BB.RatCoord.repr_ofF
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:42.762874+00:00
-- url     : https://prove2.me/submissions/c5a5ada2-fe86-4315-86b0-0a49fb16974f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GaussQ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateBijectionTraceForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB GlobalTheory.CompanionTheory.SW.BB.RatCoord
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
namespace GlobalTheory.CompanionTheory.SW.BB.RatCoord
theorem _root_.solution {F E : Type} [Field F] [Field E] [Algebra F E] {d M : ℕ}
    (b : Module.Basis (Fin d) F E) (x : Fin M × Fin d → F) (u : Fin 1) (i : Fin M) (k : Fin d) :
    b.repr (ofF b x u i) k = x (i, k) := by
  have h : ofF b x u i = b.equivFun.symm (fun k => x (i, k)) := by
    simp [ofF, Module.Basis.equivFun_symm_apply]
  rw [h, ← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
end GlobalTheory.CompanionTheory.SW.BB.RatCoord
