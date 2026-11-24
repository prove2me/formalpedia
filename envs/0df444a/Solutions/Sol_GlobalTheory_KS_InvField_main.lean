-- Prove2me | solution 1 for GlobalTheory.KS.InvField.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:31:03.827007+00:00
-- url     : https://prove2.me/submissions/92a9ac05-5344-47a8-bb18-b499a9b773b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningFieldStructureStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueInvariantVectorFieldOfTangent
import Theorems.Thm_GlobalTheory_KS_InvField_aux

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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.InvField
namespace GlobalTheory.KS.InvField
theorem _root_.solution : ∀ (K : Type) [Field K] (A₀ : Over (Sp K)) [GrpObj A₀] (v : epsR K ⟶ A₀), IsTangent v → (∃ dd, IsInvDer v dd) ∧ ∀ dd, IsInvDer v dd → (∀ W f f', dd W (f + f') = dd W f + dd W f') ∧ (∀ W f f', dd W (f * f') = f * dd W f' + f' * dd W f) ∧ (∀ W W' (f : Γ(A₀.left, W)), W' ≤ W → dd W' (rsT f W') = rsT (dd W f) W') ∧ (∀ W a, dd W (constFn A₀.hom W a) = 0) ∧ ∀ dd', IsInvDer v dd' → dd' = dd := by
  intro K _ A₀ _ v hv
  let s : 𝟙_ (Over (Sp K)) ⟶ epsR K := Over.homMk (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) (by
    change spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1)
  have hs : s ≫ v = η[A₀] := Over.OverMorphism.ext hv
  let j : A₀ ⟶ epsR K ⊗ A₀ := lift (toUnit A₀ ≫ s) (𝟙 A₀)
  have hT : j ≫ ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀) = 𝟙 A₀ := by
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd, Category.assoc, hs, ← Hom.one_def, _root_.one_mul]
  refine aux A₀.hom (fst (epsR K) A₀).left (snd (epsR K) A₀).left
    ((fst (epsR K) A₀ ≫ v) * snd (epsR K) A₀).left j.left ?_ ?_ ?_ ?_ ?_ (IsInvDer v) (fun _ => Iff.rfl)
  · exact (IsPullback.of_hasPullback (epsR K).hom A₀.hom).flip
  · rw [← Over.comp_left, lift_snd]; rfl
  · rw [← Over.comp_left, lift_fst, Over.comp_left, Over.toUnit_left]; rfl
  · rw [← Over.comp_left, hT]; rfl
  · rw [Over.w, Over.w]
end GlobalTheory.KS.InvField
