-- Prove2me | solution 1 for GlobalTheory.Tw.sup_perp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:33:14.24381+00:00
-- url     : https://prove2.me/submissions/49b2459d-98b8-4891-821f-39062b52b025

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsHermitianOfMemRealScalars

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw
variable {n : ℕ}
namespace GlobalTheory.Tw
theorem _root_.solution (V : Submodule ℂ (Fin n → ℂ)) : V ⊔ perp V = ⊤ := by
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨y, hy, w, hw, h⟩ := Submodule.exists_add_mem_mem_orthogonal
    (K := V.comap (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap) (WithLp.toLp 2 z : EuclideanSpace ℂ (Fin n))
  refine Submodule.mem_sup.2 ⟨y.ofLp, hy, w.ofLp, fun v hv => ?_, (congrArg WithLp.ofLp h).symm⟩
  have := hw (WithLp.toLp 2 v) hv
  rwa [EuclideanSpace.inner_eq_star_dotProduct] at this
end GlobalTheory.Tw
