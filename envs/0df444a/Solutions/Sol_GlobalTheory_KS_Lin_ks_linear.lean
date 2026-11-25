-- Prove2me | solution 1 for GlobalTheory.KS.Lin.ks_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:20:14.694972+00:00
-- url     : https://prove2.me/submissions/a5f3f0fd-0f70-433c-b332-d6df68785923

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAnalyticKodairaSpencerClassStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FderivFnAddLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_KodairaSpencerMatrixLinearInDerivation
import Theorems.Thm_GlobalTheory_KS_Lin_ksRel_add
import Theorems.Thm_GlobalTheory_KS_Lin_ksRel_smul
import Theorems.Thm_GlobalTheory_KS_Uniq_ks_unique
import Theorems.Thm_GlobalTheory_T_exists_analytic_kodairaSpencer_class


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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.Lin
namespace GlobalTheory.KS.Lin
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (o R : Type) [CommRing o] [CommRing R] [Algebra o R] [Algebra o ℂ] [Algebra R ℂ] [IsScalarTower o R ℂ] (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap (algebraMap R ℂ)) → ∃ κ : Derivation o R ℂ →ₗ[ℂ] Matrix (Fin P₀.g) (Fin P₀.g) ℂ, ∀ D : Derivation o R ℂ, ∃ s, KSRel u p m (fun r => D r) (κ D) s := by
  intro P₀ u Hm χ hG o R _ _ _ _ _ _ X p m hs hpb
  have hder : ∀ D : Derivation o R ℂ, IsDer (algebraMap R ℂ) (fun r => D r) := fun D =>
    ⟨fun a b => D.map_add a b, fun a b => by
      show D (a * b) = _
      rw [D.leibniz, Algebra.smul_def, Algebra.smul_def]⟩
  have hex : ∀ D : Derivation o R ℂ, ∃ Θ s, KSRel u p m (fun r => D r) Θ s := fun D =>
    GlobalTheory.T.exists_analytic_kodairaSpencer_class P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ (hder D)
  choose Θ s hΘ using hex
  have huniq : ∀ (D : Derivation o R ℂ) Θ' s', KSRel u p m (fun r => D r) Θ' s' → Θ D = Θ' :=
    fun D Θ' s' h => GlobalTheory.KS.Uniq.ks_unique P₀ u Hm χ hG R (algebraMap R ℂ) X p m hs hpb _ _ _ _ _ (hΘ D) h
  refine ⟨{ toFun := Θ, map_add' := ?_, map_smul' := ?_ }, fun D => ⟨s D, hΘ D⟩⟩
  · intro D D'
    apply huniq (D + D')
    have e : (fun r => (D + D') r) = fun r => D r + D' r := funext fun _ => Derivation.add_apply _
    rw [e]
    exact ksRel_add (hΘ D) (hΘ D')
  · intro c D
    rw [RingHom.id_apply]
    apply huniq (c • D)
    have e : (fun r => (c • D) r) = fun r => c * D r := funext fun r => by
      rw [Derivation.smul_apply, smul_eq_mul]
    rw [e]
    exact ksRel_smul c (hΘ D)
end GlobalTheory.KS.Lin
