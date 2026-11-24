-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisPar.ext_u
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:41.525115+00:00
-- url     : https://prove2.me/submissions/d54bdced-d061-41a5-9563-4895a5ff50a8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ParabolicLawOfBlockDet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEisPar_closed_uQ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisPar
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
namespace GlobalTheory.CompanionTheory.RgEisPar
theorem _root_.solution (hB : BdetLaw) (hE : ExtLaw) (hT : GrpTop) (A : Ad E R) (hA : A.Good) (ε : ℤˣ) {κ : Type} [Fintype κ]
    [DecidableEq κ] (t : Set κ) (hI : Iwa (A.uQ ε t) (A.uK ε κ)) :
    IsHt (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (A.uH ε t) ∧
      ∀ p ∈ A.uQ ε t, ∀ k ∈ A.uK ε κ, A.uH ε t (p * k) = A.lg (bdet (Sum.inl '' t) p.1) := by
  obtain ⟨-, hm, hcont, hr, hk, -⟩ := hB E R A hA.toGoodL (κ ⊕ κ) (Sum.inl '' t)
  obtain ⟨-, -, -, h2, -, -, hK⟩ := hT E R A hA κ ε
  haveI := h2
  refine hE (A.U ε κ) (A.uΓ ε κ) (A.uK ε κ) (A.uQ ε t) (fun p => A.lg (bdet (Sum.inl '' t) p.1)) hK
    (closed_uQ hB A hA.toGoodL ε t) hI ?_ ?_ ?_ ?_
  · intro p hp q hq
    simp only [Subgroup.coe_mul, hm p.1 hp q.1 hq, hA.lgmul]
  · exact hA.lgcont.comp_continuousOn (hcont.comp continuous_subtype_val.continuousOn fun x hx => hx)
  · exact fun p hp hpk => hk p.1 hp hpk
  · intro p hp hg
    obtain ⟨x, hx⟩ := hr p.1 hp hg
    simp only [hx, hA.lgi x]
end GlobalTheory.CompanionTheory.RgEisPar
