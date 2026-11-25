-- Prove2me | solution 1 for GlobalTheory.KS.EndClass.comb_exists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:14:42.142146+00:00
-- url     : https://prove2.me/submissions/d206d702-9bff-4e30-9a5b-150304f0e0ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsAlongGroupHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_InvariantVectorFieldsBasisVerticalDerivationsStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerClassCohomologousAlongEndomorphism
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pbT___bijective_504caa37308d
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pre___eq_20bc979cb662
import Theorems.Thm_P2M_GlobalTheory_KS_EndClass_pbT___comb_5bc8e4e36b6a
import Theorems.Thm_GlobalTheory_SqZero_ptsMap_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.SqZero.ptsMap_apply



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EndClass
variable {X Y Z T : Scheme.{0}}
variable {K : Type} [Field K] {R : Type} [CommRing R] {g : ℕ}
namespace GlobalTheory.KS.EndClass
theorem _root_.solution {q : Y ⟶ Sp K} {p : X ⟶ Sp R} {m : Y ⟶ X} {dd : Fin g → ∀ O : Y.Opens, Γ(Y, O) → Γ(Y, O)}
    (hb : IsBasis q p m dd) (y : Z ⟶ Y) (O : Z.Opens) (W₀ : X.Opens) (hO : O ≤ y ⁻¹ᵁ m ⁻¹ᵁ W₀)
    (ν : ∀ W : X.Opens, Γ(X, W) → Γ(Z, O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W))
    (hν : LocDerK ((O.ι ≫ y) ≫ q) p ((O.ι ≫ y) ≫ m) (fun _ => 0) W₀ (fun W f => pbT O.ι (ν W f) _)) :
    ∃ c : Fin g → Γ(Z, O), ∀ W, W ≤ W₀ → ∀ f : Γ(X, W), ν W f =
      ∑ a, rsT (c a) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) (O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W) := by
  have hV₀ : ((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀ = O.ι ⁻¹ᵁ O := by rw [pre_ι_eq, inf_eq_left.mpr hO]
  obtain ⟨c₀, hc₀, -⟩ := hb O.toScheme (O.ι ≫ y) W₀ _ hν
  choose c hc using fun a => (pbT_ι_bijective O (le_refl O) hV₀).2 (c₀ a)
  have hc' : ∀ a, pbT O.ι (c a) (((O.ι ≫ y) ≫ m) ⁻¹ᵁ W₀) = c₀ a := hc
  refine ⟨c, fun W hW f => ?_⟩
  apply (pbT_ι_bijective O (inf_le_left : O ⊓ y ⁻¹ᵁ m ⁻¹ᵁ W ≤ O) (pre_ι_eq O y m W)).1
  have e := hc₀ W hW f
  beta_reduce at e ⊢
  rw [e, pbT_ι_comb dd y O hO hW c f]
  simp only [hc']
end GlobalTheory.KS.EndClass
