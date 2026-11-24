-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.uH_pk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:39.28737+00:00
-- url     : https://prove2.me/submissions/0ce7f650-4d23-411f-9e8f-4845d29e964e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_uQ_closed
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_mulQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_contQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_ratQ

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
theorem _root_.solution {κ : Type} [Fintype κ] [DecidableEq κ] (S : Set κ) (hB : BdetLaw) (hE : ExtLaw) (hL : A.GoodL)
    [T2Space (A.U ε κ)] (hK : IsCompact (A.uK ε κ : Set (A.U ε κ))) (hI : Iwa (A.uQ ε S) (A.uK ε κ))
    (p : A.U ε κ) (hp : p ∈ A.uQ ε S) (k : A.U ε κ) (hk : k ∈ A.uK ε κ) :
    A.uH ε S (p * k) = A.lg (bdet (Sum.inl '' S) p.1) := by
  refine (hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε S) (fun p => A.lg (bdet (Sum.inl '' S) p.1)) hK
    (uQ_closed A ε S hB hL) hI ?_ ?_ ?_ ?_).2 p hp k hk
  · intro a ha b hb
    change A.lg (bdet (Sum.inl '' S) (a * b).1) = _
    rw [bdet_mulQ A ε S hB hL a b ha hb, hL.lgmul]
  · exact hL.lgcont.comp_continuousOn (bdet_contQ A ε S hB hL)
  · intro a ha hk
    exact (hB E R A hL (κ ⊕ κ) (Sum.inl '' S)).2.2.2.2.1 _ (Subgroup.mem_subgroupOf.1 ha)
      (Subgroup.mem_subgroupOf.1 hk)
  · intro a ha hr
    obtain ⟨x, hx⟩ := bdet_ratQ A ε S hB hL a ha hr
    change A.lg (bdet (Sum.inl '' S) a.1) = 0
    rw [hx]
    exact hL.lgi x
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
