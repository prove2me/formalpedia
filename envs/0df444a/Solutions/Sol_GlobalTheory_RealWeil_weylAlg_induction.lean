-- Prove2me | solution 1 for GlobalTheory.RealWeil.weylAlg_induction
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:41.565792+00:00
-- url     : https://prove2.me/submissions/8dd1a544-8deb-4ce9-9d03-fb8f61c750fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
namespace GlobalTheory.RealWeil
theorem _root_.solution {P : (Sch l →L[ℂ] Sch l) → Prop} (h1 : P 1)
    (hmul : ∀ A w, P A → P (A * dRho w)) (h0 : P 0) (hadd : ∀ A B, P A → P B → P (A + B))
    (hsmul : ∀ (c : ℂ) A, P A → P (c • A)) {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l) : P A := by
  have h : A ∈ Submodule.span ℂ (Submonoid.closure (Set.range (dRho (l := l))) : Set (Sch l →L[ℂ] Sch l)) := by
    rw [← Algebra.adjoin_eq_span]; exact hA
  refine Submodule.span_induction (p := fun A _ => P A) (fun B hB => ?_) h0 (fun A B _ _ => hadd A B)
    (fun c A _ => hsmul c A) h
  refine Submonoid.closure_induction_right (motive := fun A _ => P A) h1 ?_ hB
  rintro A _ _ ⟨w, rfl⟩ hA
  exact hmul A w hA
end GlobalTheory.RealWeil
