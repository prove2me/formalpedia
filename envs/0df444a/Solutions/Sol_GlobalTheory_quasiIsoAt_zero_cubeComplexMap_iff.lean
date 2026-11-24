-- Prove2me | solution 1 for GlobalTheory.quasiIsoAt_zero_cubeComplexMap_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:29.531819+00:00
-- url     : https://prove2.me/submissions/aa9cc0b2-59b8-4907-af2d-7b4ecb806f14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Theorems.Thm_GlobalTheory_cubeCyclesIso_hom_subtype


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits HomologicalComplex
universe v u
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
theorem _root_.solution {A B : Cube.{v} ι R} (φ : A ⟶ B) :
    QuasiIsoAt (cubeComplexMap φ) 0 ↔ Set.BijOn (φ.app ∅).hom
      (LinearMap.ker (Cube.aug A)) (LinearMap.ker (Cube.aug B)) := by
  have h1 : QuasiIsoAt (cubeComplexMap φ) 0 ↔ IsIso (cyclesMap (cubeComplexMap φ) 0) := by
    rw [quasiIsoAt_iff_isIso_homologyMap]
    exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
      (Arrow.isoMk (CochainComplex.isoHomologyπ₀ (cubeComplex A))
        (CochainComplex.isoHomologyπ₀ (cubeComplex B))
        (homologyπ_naturality (cubeComplexMap φ) 0))).symm
  let j (X : Cube.{v} ι R) (x : (cubeComplex X).cycles 0) : X.obj ∅ :=
    Cube.termZeroEquiv X (((cubeComplex X).iCycles 0).hom x)
  have hj (X : Cube.{v} ι R) : Function.Injective (j X) :=
    (Cube.termZeroEquiv X).injective.comp
      ((ModuleCat.mono_iff_injective ((cubeComplex X).iCycles 0)).1 inferInstance)
  have hr (X : Cube.{v} ι R) : Set.range (j X) = LinearMap.ker (Cube.aug X) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      have h := congr(($((cubeComplex X).iCycles_d 0 (0 + 1))).hom x)
      rw [cubeComplex_d] at h
      exact (Cube.d_zero_apply X _).symm.trans h
    · intro ha
      have ha' : (Cube.termZeroEquiv X).symm a ∈ LinearMap.ker (Cube.d X 0) := by
        rw [LinearMap.mem_ker, Cube.d_zero_apply, LinearEquiv.apply_symm_apply]
        exact ha
      refine ⟨(cubeCyclesIso X 0).inv.hom ⟨_, ha'⟩, ?_⟩
      have h := congr(($((Iso.inv_comp_eq _).2 (cubeCyclesIso_hom_subtype X 0).symm)).hom ⟨_, ha'⟩)
      exact (congrArg (Cube.termZeroEquiv X) h).trans (LinearEquiv.apply_symm_apply _ a)
  have hc (x : (cubeComplex A).cycles 0) :
      j B ((cyclesMap (cubeComplexMap φ) 0).hom x) = (φ.app ∅).hom (j A x) :=
    congrArg (Cube.termZeroEquiv B) congr(($(cyclesMap_i (cubeComplexMap φ) 0)).hom x)
  rw [h1, ConcreteCategory.isIso_iff_bijective, ← hr, ← hr]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨_, hc x⟩
    · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact congrArg _ (h.1 (hj B ((hc x).trans (hxy.trans (hc y).symm))))
    · rintro _ ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := h.2 y
      exact ⟨_, ⟨x, rfl⟩, (hc x).symm⟩
  · intro h
    refine ⟨fun x y hxy => hj A (h.injOn ⟨x, rfl⟩ ⟨y, rfl⟩
      ((hc x).symm.trans ((congrArg (j B) hxy).trans (hc y)))), fun y => ?_⟩
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := h.surjOn ⟨y, rfl⟩
    exact ⟨x, hj B ((hc x).trans hx)⟩
end GlobalTheory
