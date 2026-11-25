-- Prove2me | solution 1 for GlobalTheory.T.exteriorSquare_equiv_of_baseChange_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:56.693392+00:00
-- url     : https://prove2.me/submissions/f263e265-2fb6-4168-a591-0ddf2c05a298

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareEquivOfBaseChangeField
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_PreUMono
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorSquareEquivOfBaseChangeFieldStatement
import Theorems.Thm_GlobalTheory_AbCoh_exteriorSquare_equiv_of_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (M N M' N' : Type) [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module L M'] [AddCommGroup N'] [Module L N'] (c : M →ₗ[K] M →ₗ[K] N) (c' : M' →ₗ[L] M' →ₗ[L] N') (e₁ : L ⊗[K] M ≃ₗ[L] M') (e₂ : L ⊗[K] N ≃ₗ[L] N'), (∀ a b, e₂ (1 ⊗ₜ c a b) = c' (e₁ (1 ⊗ₜ a)) (e₁ (1 ⊗ₜ b))) → (∃ e : ⋀[L]^2 M' ≃ₗ[L] N', ∀ a b, e (exteriorPower.ιMulti L 2 ![a, b]) = c' a b) → ∃ e : ⋀[K]^2 M ≃ₗ[K] N, ∀ a b, e (exteriorPower.ιMulti K 2 ![a, b]) = c a b := by
  first | exact @GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange | exact GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange | (intros; apply GlobalTheory.AbCoh.exteriorSquare_equiv_of_baseChange <;> assumption)
end _root_.GlobalTheory.T
