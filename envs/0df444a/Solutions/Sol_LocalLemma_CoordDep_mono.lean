-- Prove2me | solution 1 for LocalLemma.CoordDep.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:14.172096+00:00
-- url     : https://prove2.me/submissions/c23966f1-a57b-4350-9ecf-c117d275f6fb

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
theorem _root_.solution {ι : Type*} {A : Set (ι → Bool)} {D D' : Finset ι} (h : CoordDep A D)
    (hD : D ⊆ D') : CoordDep A D' :=
  fun ω ω' hω => h ω ω' fun i hi => hω i (hD hi)
end CoordDep
end LocalLemma
