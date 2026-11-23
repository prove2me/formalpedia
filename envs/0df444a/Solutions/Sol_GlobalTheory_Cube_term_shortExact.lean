-- Prove2me | solution 1 for GlobalTheory.Cube.term_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:34:11.784098+00:00
-- url     : https://prove2.me/submissions/304e693b-368c-49e0-bd87-5c000425d785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsIsoTermComparisonRestrictScalars

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
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type u} [Ring R]
namespace GlobalTheory
namespace Cube
theorem _root_.solution (S : ShortComplex (Cube.{v} ι R)) (p : ℕ)
    (hS : ∀ s : Finset ι, s.card = p → (S.map ((evaluation _ _).obj s)).ShortExact) :
    ((S.map (cubeFunctor ι R)).map (HomologicalComplex.eval _ _ p)).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · change Function.Exact (Cube.termMap S.f p) (Cube.termMap S.g p)
    have h := fun s : {s : Finset ι // s.card = p} =>
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (hS s.1 s.2).exact
    intro y
    constructor
    · intro hy
      choose x hx using fun s => (h s (y s)).1 (congrFun hy s)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      exact funext fun s => (h s _).2 ⟨x s, rfl⟩
  · change Function.Injective (Cube.termMap S.f p)
    exact fun x y hxy => funext fun s => (hS s.1 s.2).moduleCat_injective_f (congrFun hxy s)
  · change Function.Surjective (Cube.termMap S.g p)
    intro y
    choose x hx using fun s : {s : Finset ι // s.card = p} =>
      (hS s.1 s.2).moduleCat_surjective_g (y s)
    exact ⟨x, funext hx⟩
end Cube
end GlobalTheory
