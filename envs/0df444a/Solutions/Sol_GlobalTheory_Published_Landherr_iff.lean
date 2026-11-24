-- Prove2me | solution 1 for GlobalTheory.Published.Landherr.iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:52.048744+00:00
-- url     : https://prove2.me/submissions/06555cf4-ae8a-4b16-95dc-b4ea72202f41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__AlgebraMapNormOfBasisOneSqrt_07cf76d090f2548e
import Theorems.Thm_GlobalTheory_Published_Landherr_congr_complex
import Theorems.Thm_GlobalTheory_Published_Landherr_det_norm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.Landherr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.Published.Landherr
theorem _root_.solution (H : Landherr) (hG : ∀ a b, cc (G a b) = G b a) (hG' : ∀ a b, cc (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) ↔
      (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
        G'.map τ = Qᵀ * G.map τ * Q.map conj) ∧ ∃ x : E, G.det / G'.det = x * cc x :=
  ⟨fun h => ⟨congr_complex h, det_norm hd h⟩, fun h => H E r G G' hG hG' hd hd' h.1 h.2⟩
end GlobalTheory.Published.Landherr
