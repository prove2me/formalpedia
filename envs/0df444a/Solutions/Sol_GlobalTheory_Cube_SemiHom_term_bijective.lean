-- Prove2me | solution 1 for GlobalTheory.Cube.SemiHom.term_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:41.401103+00:00
-- url     : https://prove2.me/submissions/0c4f1761-7e41-4e9f-863c-09e87402ec68

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
open GlobalTheory.Cube GlobalTheory.Cube.SemiHom
variable {f : R →+* S} {A A' : Cube.{v} ι R} {B B' : Cube.{v'} ι S} (ψ : Cube.SemiHom f A B)
open CategoryTheory Limits
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R] {S : Type u'} [Ring S]
variable {f : R →+* S} {A A' : _root_.GlobalTheory.Cube.{v} ι R} {B B' : _root_.GlobalTheory.Cube.{v'} ι S}
  (ψ : _root_.GlobalTheory.Cube.SemiHom f A B)
omit [LinearOrder ι]
namespace GlobalTheory.Cube.SemiHom
namespace _root_.GlobalTheory.Cube.SemiHom
theorem _root_.solution
    (h : ∀ s : Finset ι, s.Nonempty → Function.Bijective (ψ.app s)) (p : ℕ) :
    Function.Bijective (ψ.term (p + 1)) := by
  have hne : ∀ s : {s : Finset ι // s.card = p + 1}, s.1.Nonempty := fun s =>
    Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos p)
  refine ⟨fun x y hxy => funext fun s => (h s.1 (hne s)).1 (congrFun hxy s), fun y => ?_⟩
  refine ⟨fun s => ((h s.1 (hne s)).2 (y s)).choose, funext fun s => ?_⟩
  exact ((h s.1 (hne s)).2 (y s)).choose_spec
end _root_.GlobalTheory.Cube.SemiHom
end GlobalTheory.Cube.SemiHom
