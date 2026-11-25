-- Prove2me | solution 1 for GlobalTheory.ConvexCutOff.polyDeriv_rename_of_convex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:40:08.192533+00:00
-- url     : https://prove2.me/submissions/dad7219d-f41a-4316-aee2-58447947f2b3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsPermOfOfFnPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PolyDerivRenameOfConvex
import Theorems.Thm_GlobalTheory_ConvexCutOff_iteratedFDeriv_symm
import Theorems.Thm_GlobalTheory_ConvexCutOff_term_eq
import Theorems.Thm_GlobalTheory_ConvexCutOff_ofFn_get_cast

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open GlobalTheory GlobalTheory.ConvexCutOff
namespace GlobalTheory.ConvexCutOff
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (K : Set V) (F : V → ℂ), Convex ℝ K → (∀ z, z ∉ K → F z = 0) → DifferentiableOn ℂ F (interior K) → ∀ (x : V) (ι κ : Type) (ρ : ι → κ), Function.Injective ρ → ∀ (Q : MvPolynomial ι ℂ) (u : κ → V), polyDeriv (MvPolynomial.rename ρ Q) u F x = polyDeriv Q (u ∘ ρ) F x := by
  intro V _ _ _ K F hK hF hd x ι κ ρ hρ Q u
  classical
  unfold polyDeriv
  rw [MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ]
  congr 1
  apply term_eq (iteratedFDeriv_symm hK hF hd x)
  rw [ofFn_get_cast, ofFn_get_cast, ← List.map_map]
  apply List.Perm.map
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map]
end GlobalTheory.ConvexCutOff
