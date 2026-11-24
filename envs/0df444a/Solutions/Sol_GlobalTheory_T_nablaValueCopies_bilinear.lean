-- Prove2me | solution 1 for GlobalTheory.T.nablaValueCopies_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:00.479742+00:00
-- url     : https://prove2.me/submissions/d565d1ef-5261-4913-82f0-8351d20f9969

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinear
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_NablaValueCopiesBilinearStatement
import Theorems.Thm_GlobalTheory_nabValN_bilinear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), (∀ (f g : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (f + g) cp u P = nabValN B K h w0 m f cp u P + nabValN B K h w0 m g cp u P) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m (t • f) cp u P = t * nabValN B K h w0 m f cp u P) ∧ (∀ (f : PS K n d) (P Q : MvPolynomial ι K), nabValN B K h w0 m f cp u (P + Q) = nabValN B K h w0 m f cp u P + nabValN B K h w0 m f cp u Q) ∧ (∀ (t : K) (f : PS K n d) (P : MvPolynomial ι K), nabValN B K h w0 m f cp u (MvPolynomial.C t * P) = t * nabValN B K h w0 m f cp u P) := by
  first | exact @GlobalTheory.nabValN_bilinear | exact GlobalTheory.nabValN_bilinear | (intros; apply GlobalTheory.nabValN_bilinear <;> assumption)
end _root_.GlobalTheory.T
