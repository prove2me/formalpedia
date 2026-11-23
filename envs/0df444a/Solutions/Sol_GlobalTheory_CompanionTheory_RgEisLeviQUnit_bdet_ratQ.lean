-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_ratQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:16.824511+00:00
-- url     : https://prove2.me/submissions/c1a7954c-7455-4775-bdf0-cf971ee06524

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLeviQUnit
open PositivityTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] (A : Ad E R) (ε : ℤˣ)
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hL : A.GoodL)
    (p : A.U ε κ) (hp : p ∈ A.uQ ε S) (hr : p ∈ A.uΓ ε κ) :
    ∃ x, bdet (Sum.inl '' S) p.1 = Units.map A.i.toMonoidHom x :=
  (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.2.2.1 _ (Subgroup.mem_subgroupOf.1 hp) (Subgroup.mem_subgroupOf.1 hr)
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
