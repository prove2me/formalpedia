-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DSCoreSub.algCoreSub_of_algCore
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:01:31.662572+00:00
-- url     : https://prove2.me/submissions/66fe183b-7c38-4df6-ae2c-09ff6e6193ba

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AlgCoreSubOfAlgCore
import Theorems.Thm_GlobalTheory_CompanionTheory_DSCoreSub_qdet_intertwine
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Formalism.REAL CompanionTheory.D.DSIC
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DSCoreSub
variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
namespace GlobalTheory.CompanionTheory.DSCoreSub
theorem _root_.solution : AlgCore → AlgCoreSub := by
  intro hA n ε lam V _ _ E V₀ v S hlam hgl hun hst hS hv hfd hK hvS hmin Y
  let E' : Fin n → Fin n → Module.End ℂ V₀ := fun a b => (E a b).restrict (hst a b)
  have hE : ∀ a b (x : V₀), ((E' a b x : V₀) : V) = E a b x := fun a b x => rfl
  have hhi : ∀ (μ : Fin n → ℝ) (x : V₀), KHighest ε E' μ x ↔ KHighest ε E μ (x : V) := by
    intro μ x
    unfold KHighest IsWeight
    simp only [Subtype.ext_iff, hE, Submodule.coe_smul, Submodule.coe_zero]
  have hgl' : GlRel E' := by
    intro a b c d
    ext x
    have := LinearMap.congr_fun (hgl a b c d) (x : V)
    simp only [LinearMap.sub_apply, Module.End.mul_apply, Submodule.coe_sub, hE] at this ⊢
    rw [this]
    split_ifs <;> simp [hE]
  have hun' : IsUnitary ε E' := fun a b x y => hun a b x y
  haveI : FiniteDimensional ℂ (S.comap V₀.subtype) :=
    (Submodule.comapSubtypeEquivOfLe hS).symm.finiteDimensional
  have key := hA n ε lam V₀ E' ⟨v, hS hvS⟩ (S.comap V₀.subtype) hlam hgl' hun' ((hhi _ _).2 hv) inferInstance
    (fun a b hab x hx => hK a b hab x hx) hvS
    (fun μ x hx hμ => hmin μ x x.2 (fun h0 => hx (Subtype.ext h0)) ((hhi μ x).1 hμ)) Y
  have h2 := qdet_intertwine V₀.subtype E' E hE (Y + ((n : ℂ) - 1) / 2) ⟨v, hS hvS⟩
  rw [key] at h2
  simpa using h2.symm
end GlobalTheory.CompanionTheory.DSCoreSub
