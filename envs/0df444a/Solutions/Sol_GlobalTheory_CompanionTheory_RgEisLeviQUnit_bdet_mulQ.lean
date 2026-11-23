-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_mulQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:34:16.568871+00:00
-- url     : https://prove2.me/submissions/16d149b1-def0-49c2-9784-4cbb297216d6

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
    (p q : A.U ε κ) (hp : p ∈ A.uQ ε S) (hq : q ∈ A.uQ ε S) :
    bdet (Sum.inl '' S) (p * q).1 = bdet (Sum.inl '' S) p.1 * bdet (Sum.inl '' S) q.1 :=
  (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.1 _ (Subgroup.mem_subgroupOf.1 hp) _ (Subgroup.mem_subgroupOf.1 hq)
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
