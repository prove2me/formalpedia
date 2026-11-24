-- Prove2me | solution 1 for GlobalTheory.T.eigen_line_bilinear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:06:45.391962+00:00
-- url     : https://prove2.me/submissions/e54c58b2-cbfb-414a-b087-3341f52fa64c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegralStatement
import Theorems.Thm_GlobalTheory_Div_eigen_line_bilinear_lower_skew_orth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ → ∀ (l : ℕ), l.Prime → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K], (l : O) ∈ IsLocalRing.maximalIdeal O → Nat.card (E →+* K) = Module.finrank ℚ E → ∀ (D : O), D ≠ 0 → ClearsIdem K c D → ∀ (I : Type) [Fintype I] (φ : I → E →+* K), IsCMTypeIn φ → ∀ (H : Type) [AddCommGroup H] [Module O H] (ρ : orderC c →+* Module.End O H) (Fil : Submodule O H) (B : LinearMap.BilinForm O H), IsCMLattice φ ρ Fil B → EigenClaims φ ρ Fil B D → ∀ e f : I → H, IsGens φ ρ e f → ∀ N : I → Module.End K (K ⊗[O] H), (∀ i, IsLower ρ (φ i) (e i) (f i) (N i)) → (∀ i x y, B.baseChange K (N i x) y + B.baseChange K x (N i y) = 0) ∧ ∀ i j x y, B.baseChange K (N i x) (N j y) = 0 := by
  first | exact @GlobalTheory.Div.eigen_line_bilinear.lower_skew_orth | exact GlobalTheory.Div.eigen_line_bilinear.lower_skew_orth | (intros; apply GlobalTheory.Div.eigen_line_bilinear.lower_skew_orth <;> assumption)
end _root_.GlobalTheory.T
