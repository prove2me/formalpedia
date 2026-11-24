-- Prove2me | solution 1 for GlobalTheory.HalfPairing.exists_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:12:54.412162+00:00
-- url     : https://prove2.me/submissions/35540f24-fcb1-45e4-a5e5-9c815e6a8172

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegPFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegQFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsGenFrGenFr
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartDirectionsIntegral
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HalvesFreeAndAdjoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.HalfPairing
namespace GlobalTheory.HalfPairing
theorem _root_.solution {R P Q Z : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup Z] (s : R → R) (B : P → Q → Z) (hadd : ∀ u v w, B u (v + w) = B u v + B u w)
    (hbal : ∀ a u v, B u (a • v) = B (s a • u) v)
    (hnd : ∀ v w, (∀ u, B u v = B u w) → v = w)
    (hrep : ∀ (g : P →ₗ[R] P) (v : Q), ∃ w, ∀ u, B (g u) v = B u w) :
    ∃ adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q), (∀ g g', adj (g * g') = adj g' * adj g) ∧
      ∀ (k : Q ≃ₗ[R] Q) (g : P ≃ₗ[R] P), (∀ u v, B (g u) v = B u (k v)) ↔ k = adj g := by
  choose w hw using hrep
  let a : (P →ₗ[R] P) → (Q →ₗ[R] Q) := fun g =>
    { toFun := w g
      map_add' := fun v v' => hnd _ _ fun u => by rw [← hw, hadd, hadd, hw, hw]
      map_smul' := fun r v => hnd _ _ fun u => by
        rw [← hw, RingHom.id_apply, hbal, hbal, ← map_smul, hw] }
  have ha : ∀ g u v, B (g u) v = B u (a g v) := fun g u v => hw g v u
  have hinv : ∀ g g' : P →ₗ[R] P, (∀ u, g (g' u) = u) → a g' ∘ₗ a g = LinearMap.id := fun g g' h => by
    ext v
    refine hnd _ _ fun u => ?_
    rw [LinearMap.comp_apply, ← ha, ← ha, h, LinearMap.id_apply]
  let adj : (P ≃ₗ[R] P) → (Q ≃ₗ[R] Q) := fun g =>
    LinearEquiv.ofLinear (a g) (a g.symm) (hinv _ _ fun u => g.symm_apply_apply u)
      (hinv _ _ fun u => g.apply_symm_apply u)
  have hadj : ∀ (g : P ≃ₗ[R] P) u v, B (g u) v = B u (adj g v) := fun g u v => ha g u v
  refine ⟨adj, fun g g' => ?_, fun k g => ⟨fun h => ?_, fun h => h ▸ hadj g⟩⟩
  · ext v
    refine hnd _ _ fun u => ?_
    rw [← hadj, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ← hadj, ← hadj]
  · ext v
    exact hnd _ _ fun u => by rw [← h, hadj]
end GlobalTheory.HalfPairing
