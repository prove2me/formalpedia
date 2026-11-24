-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLeviQUnit.bdet_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:43:57.509853+00:00
-- url     : https://prove2.me/submissions/edb64e4f-3662-4910-8f26-e2542c55841d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviQuotientOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_jQ_val
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_bdet_val
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLeviQUnit_det_sub_one

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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {s : Set ι} {_fF : Fintype ↥sᶜ} {_fD : DecidableEq ↥sᶜ}
namespace GlobalTheory.CompanionTheory.RgEisLeviQUnit
theorem _root_.solution (m : A.U ε ↥sᶜ) : bdet (Sum.inl '' s) (jQ (s := s) A ε m : A.U ε ι).1 = 1 := by
  classical
  refine Units.ext ?_
  rw [bdet_val _ _ (show ((jQ (s := s) A ε m : A.U ε ι).1 : GL (ι ⊕ ι) R) ∈ stab R (Sum.inl '' s : Set (ι ⊕ ι)) from
    jG_stab m.1), Units.val_one]
  refine det_sub_one _ fun a b => ?_
  have hb : b.1 ∉ Set.range (emb s) := fun hh => by
    obtain ⟨i, hi, h⟩ := b.2
    rw [← h] at hh
    exact (inl_mem_range i).1 hh hi
  rw [jQ_val, jG_val, jM_off_right _ _ _ _ hb, Matrix.one_apply]
  simp [Subtype.ext_iff]
end GlobalTheory.CompanionTheory.RgEisLeviQUnit
