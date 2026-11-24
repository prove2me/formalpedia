-- Prove2me | solution 1 for GlobalTheory.KS.exists_fibre_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:50.195323+00:00
-- url     : https://prove2.me/submissions/0b4fda69-d11d-4fad-a937-51331b7fe363

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueUniformisingVectorVerticalTangentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFibreCoords
import Theorems.Thm_GlobalTheory_KS_exists_det_ne_zero_of_common_ker
import Theorems.Thm_GlobalTheory_KS_top_le_preimage_finset_inf
import Theorems.Thm_GlobalTheory_KS_fderiv_fn_resG
import Theorems.Thm_GlobalTheory_T_existsUnique_uniformising_vector_vertical_tangent


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
open GlobalTheory GlobalTheory.KS
namespace GlobalTheory.KS
theorem _root_.solution : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb z
  let J : Type := {Wf : (W : X.Opens) × Γ(X, W) // z ∈ dom u m Wf.1}
  let φ : J → (Fin P₀.g → ℂ) →ₗ[ℂ] ℂ := fun j => (fderiv ℂ (fn u m j.1.1 j.1.2) z).toLinearMap
  have hker : ∀ w, (∀ j, φ j w = 0) → w = 0 := by
    intro w hw
    have hδ : PtDer ((u.ex z).left ≫ m) (fun _ _ => (0 : ℂ)) :=
      ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
    obtain ⟨w₀, _, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hsm hpb z (fun _ _ => 0) hδ (fun _ => rfl)
    have e1 : w = w₀ := huniq w (fun W f hzW => (hw ⟨⟨W, f⟩, hzW⟩).symm)
    have e2 : (0 : Fin P₀.g → ℂ) = w₀ := huniq 0 (fun W f _ => (ContinuousLinearMap.map_zero _).symm)
    exact e1.trans e2.symm
  obtain ⟨c, hc⟩ := exists_det_ne_zero_of_common_ker φ hker
  have hzW : z ∈ dom u m (Finset.univ.inf fun b => (c b).1.1) :=
    top_le_preimage_finset_inf ((u.ex z).left ≫ m) Finset.univ (fun b => (c b).1.1) (fun b _ => (c b).2)
  refine ⟨Finset.univ.inf fun b => (c b).1.1,
    fun b => resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2, hzW, ?_⟩
  have hE : (Matrix.of fun a b => fderiv ℂ (fn u m (Finset.univ.inf fun b => (c b).1.1)
      (resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2)) z (Pi.single a 1)) =
      Matrix.of fun a b => φ (c b) (Pi.single a 1) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [fderiv_fn_resG u m (Finset.inf_le (Finset.mem_univ b)) (c b).1.2 hzW]
    rfl
  rw [hE]
  exact hc
end GlobalTheory.KS
