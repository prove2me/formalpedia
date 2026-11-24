-- Prove2me | solution 1 for GlobalTheory.SymSignature.card_type_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:15:03.858231+00:00
-- url     : https://prove2.me/submissions/ed0d8cd8-832e-4086-8c73-4d8bc209e53d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardTypeLe
import Theorems.Thm_GlobalTheory_SymSignature_finite_hom
import Theorems.Thm_GlobalTheory_SymSignature_card_hom_le
import Theorems.Thm_GlobalTheory_SymSignature_root_ne_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SymSignature
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SymSignature
theorem _root_.solution (H : Host E) {K : Type} [Field K] [CharZero K] {ρ : K}
    (hρ : ρ ^ 2 = -(H.d : K)) :
    Nat.card {τ : 𝓞 E →+* K // τ H.rt = ρ} ≤ Module.finrank ℚ E / 2 := by
  haveI := finite_hom E K
  have hne := root_ne_neg H hρ
  let f : {τ : 𝓞 E →+* K // τ H.rt = ρ} ⊕ {τ : 𝓞 E →+* K // τ H.rt = ρ} → (𝓞 E →+* K) :=
    Sum.elim (fun τ => τ.1) (fun τ => τ.1.comp (H.bar : 𝓞 E →+* 𝓞 E))
  have hf : Function.Injective f := by
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this.symm
    · exfalso
      have := RingHom.congr_fun h H.rt
      simp [f, HostModel.bar_rt, a.2, b.2] at this
      exact hne this
    · refine congrArg Sum.inr (Subtype.ext (RingHom.ext fun x => ?_))
      have := RingHom.congr_fun h (H.bar x)
      simpa [f, HostModel.bar_bar] using this
  have h1 := (Nat.card_le_card_of_injective f hf).trans (card_hom_le E K)
  rw [Nat.card_sum] at h1
  omega
end GlobalTheory.SymSignature
