-- Prove2me | solution 1 for GlobalTheory.homologyMap_cechClass
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:39.062632+00:00
-- url     : https://prove2.me/submissions/115fc057-e1af-44ec-bcb8-45c207eb0c57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CubeComplexAcyclicIffQuasiIsoCechAug
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HomologyRestrictScalarsBijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
universe v v' u u'
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {A B : _root_.GlobalTheory.Cube.{v} ι R} (φ : A ⟶ B) (p : ℕ)
    (x : LinearMap.ker (_root_.GlobalTheory.Cube.d A (p + 1)))
    (y : LinearMap.ker (_root_.GlobalTheory.Cube.d B (p + 1)))
    (h : _root_.GlobalTheory.Cube.termMap φ (p + 1) x.1 = y.1) :
    (HomologicalComplex.homologyMap (_root_.GlobalTheory.cechComplexMap φ) p).hom (_root_.GlobalTheory.cechClass A p x) =
      _root_.GlobalTheory.cechClass B p y := by
  have hi : Function.Injective ((_root_.GlobalTheory.cechComplex B).iCycles p).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hc : (HomologicalComplex.cyclesMap (_root_.GlobalTheory.cechComplexMap φ) p).hom
      ((_root_.GlobalTheory.cechCyclesIso A p).inv.hom x) = (_root_.GlobalTheory.cechCyclesIso B p).inv.hom y := by
    apply hi
    rw [_root_.GlobalTheory.iCycles_cechCyclesIso_inv, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
      HomologicalComplex.cyclesMap_i, ModuleCat.hom_comp, LinearMap.comp_apply,
      _root_.GlobalTheory.iCycles_cechCyclesIso_inv, ← h]
    rfl
  simp only [_root_.GlobalTheory.cechClass, ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [← hc, ← LinearMap.comp_apply, ← ModuleCat.hom_comp,
    HomologicalComplex.homologyπ_naturality]
  rfl
end _root_.GlobalTheory
end GlobalTheory
