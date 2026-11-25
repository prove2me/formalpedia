-- Prove2me | solution 1 for GlobalTheory.exists_finite_projective_complex_of_noetherian_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:03.158725+00:00
-- url     : https://prove2.me/submissions/1cc32211-7aaa-4523-ac60-6a50dec677b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexOfNoetherianModel
import Theorems.Thm_GlobalTheory_Cube_nonempty_extendScalars_iso_baseChange
import Theorems.Thm_GlobalTheory_finite_projective_extendScalars_obj
import Theorems.Thm_GlobalTheory_quasiIso_extendScalars_extendScalars
import Theorems.Thm_GlobalTheory_Cube_flat_term
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_exists_finite_projective_complex_quasiIso
import Theorems.Thm_GlobalTheory_isIso_cechComplexMap
import Theorems.Thm_GlobalTheory_isZero_cechComplex_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R₀ R : Type) [CommRing R₀] [IsNoetherianRing R₀] [CommRing R] [Algebra R₀ R] (C₀ : Cube.{0} ι R₀) (A : Cube.{0} ι R) (θ : Cube.baseChange R C₀ ⟶ A), (∀ s : Finset ι, s.Nonempty → Module.Flat R₀ (C₀.obj s)) → (∀ p, Module.Finite R₀ ((cechComplex C₀).homology p)) → (∀ s : Finset ι, s.Nonempty → Function.Bijective (θ.app s).hom) → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cechComplex A), (∀ p, Fintype.card ι ≤ p + 1 → IsZero (K.X (p + 1))) ∧ (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  intro ι _ _ R₀ R _ _ _ _ C₀ A θ hflat hfin hθ
  obtain ⟨K₀, φ₀, h0, h1, -, h2, -, -, h3⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} (cechComplex C₀) (Fintype.card ι - 1)
      (fun p hp => isZero_cechComplex_X C₀ (by omega))
      (fun p => Cube.flat_term C₀ (p + 1) fun s hs => hflat s (Finset.card_pos.1 (by omega))) hfin
  obtain ⟨e⟩ := Cube.nonempty_extendScalars_iso_baseChange (R := R) C₀
  let F := (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).mapHomologicalComplex
    (ComplexShape.up ℕ)
  let ψ : F.obj (cechComplex C₀) ≅ cechComplex A :=
    cechExtendScalarsIso (algebraMap R₀ R) C₀ ≪≫ (cechFunctor ι R).mapIso e ≪≫
      @asIso _ _ _ _ (cechComplexMap θ) (isIso_cechComplexMap θ hθ)
  refine ⟨F.obj K₀, F.map φ₀ ≫ ψ.hom, fun p hp => ?_, fun p => ?_, fun R' _ _ => ?_⟩
  · exact (ModuleCat.extendScalars.{0, 0, 0} (algebraMap R₀ R)).map_isZero (h0 _ (by omega))
  · have := h1 p
    have := h2 p
    exact finite_projective_extendScalars_obj (algebraMap R₀ R) (K₀.X p)
  · letI := ((algebraMap R R').comp (algebraMap R₀ R)).toAlgebra
    have := quasiIso_extendScalars_extendScalars (algebraMap R₀ R) (algebraMap R R') φ₀ (h3 R')
    rw [Functor.map_comp]
    infer_instance
end GlobalTheory
