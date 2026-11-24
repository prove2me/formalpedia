-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.LatDual.dual_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:34:40.077804+00:00
-- url     : https://prove2.me/submissions/06e20ac1-390d-4b1e-9786-69c4599eeee7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EtaleLocalizationAtPrimeTensorOfLowHeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_IsVBOnDualAndBidual
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_mem_span_basis_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LatDual_mem_dual_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LatDual
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]
namespace GlobalTheory.CompanionTheory.Ar.LatDual
theorem _root_.solution (L : Lat ξ E) (p : Cpt ξ) {r : ℕ} (B : Module.Basis (Fin r) Ω E)
    (h : L p = Submodule.span (regAt ξ p) (Set.range B)) :
    L.dual p = Submodule.span (regAt ξ p) (Set.range B.dualBasis) := by
  ext w
  rw [mem_dual_iff L p B h w, mem_span_basis_iff p B.dualBasis w]
  simp only [Module.Basis.dualBasis_repr]
end GlobalTheory.CompanionTheory.Ar.LatDual
