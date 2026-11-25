-- Prove2me | solution 1 for GlobalTheory.RelConstThickening.existsUnique_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:06:17.404659+00:00
-- url     : https://prove2.me/submissions/b8547865-4e97-4b09-aeef-336dee7ffc7a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualNumberSectionsUniqueDecomposition
import Theorems.Thm_GlobalTheory_RelConstThickening_existsUnique_affine
import Theorems.Thm_GlobalTheory_RelConstThickening_existsUnique_comb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.RelConstThickening
namespace GlobalTheory.RelConstThickening
theorem _root_.solution : ∀ {X Z P : Scheme.{0}} (U : X.affineOpens) (h : Z ⟶ X) (p₁ : P ⟶ Sp (DualNumber Γ(X, U.1))) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap Γ(X, U.1) (DualNumber Γ(X, U.1))) ≫ GlobalTheory.LogKS.chart U) → ∀ (O : Z.Opens), O ≤ h ⁻¹ᵁ U.1 → ∀ F : Γ(P, p₂ ⁻¹ᵁ O), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun U h p₁ p₂ H O hO F =>
    existsUnique_comb (fun _ hV hVU F => existsUnique_affine U h p₁ p₂ H hV hVU F) O hO F
end GlobalTheory.RelConstThickening
