-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.HT.LatBasic.eigProj_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:35:21.485108+00:00
-- url     : https://prove2.me/submissions/a7974995-ebfb-44bb-9270-674086a1d877

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_LogAbsVpOfNormalised
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_CommutativeAlgebra_LatNormGrLatNeZeroOfSpan
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_eigSp_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HT_LatBasic_eigProj_of_eigenSub_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT
open Module NumberField
open GlobalTheory.CompanionTheory.Ar.HT.LatBasic
open TensorProduct
variable {A : Type} [CommRing A] {K : Type} [Field K] [Algebra A K]
  {V : Type} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CompanionTheory.Ar.HT.LatBasic
theorem _root_.solution {ρ : 𝓞 E →+* Module.End K V} {σ σ' : E →+* K} (h : σ ≠ σ') {x : V}
    (hx : x ∈ eigSp ρ σ') : eigProj ρ σ x = 0 :=
  eigProj_of_eigenSub_ne (fun e => h (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e))
    (by rwa [← eigSp_eq])
end GlobalTheory.CompanionTheory.Ar.HT.LatBasic
