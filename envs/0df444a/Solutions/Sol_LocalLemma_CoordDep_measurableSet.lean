-- Prove2me | solution 1 for LocalLemma.CoordDep.measurableSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:20:41.090154+00:00
-- url     : https://prove2.me/submissions/27906d78-31be-4658-9a12-5eb4c2b42d52

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
namespace CoordDep
theorem _root_.solution {ι : Type*} {A : Set (ι → Bool)} {D : Finset ι}
    (h : CoordDep A D) :
    MeasurableSet[MeasurableSpace.comap (fun ω (i : D) => ω i) MeasurableSpace.pi] A := by
  refine ⟨(fun ω (i : D) => ω i) '' A, (Set.toFinite _).measurableSet, ?_⟩
  ext ω
  simp only [Set.mem_preimage, Set.mem_image]
  constructor
  · rintro ⟨ω', hω', he⟩
    refine h ω' ω (fun i hi => ?_) hω'
    exact congrFun he ⟨i, hi⟩
  · intro hω; exact ⟨ω, hω, rfl⟩
end CoordDep
end LocalLemma
