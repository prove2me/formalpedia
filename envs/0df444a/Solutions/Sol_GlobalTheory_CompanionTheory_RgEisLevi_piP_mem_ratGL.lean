-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEisLevi.piP_mem_ratGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:08:23.724824+00:00
-- url     : https://prove2.me/submissions/80471984-3a22-4c7b-b184-1f74148713c8

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RgEisLevi
theorem _root_.solution (A : Ad E R) (hi : Function.Injective A.i) (q : stab R (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)))
    (hq : q.1 ∈ A.ratGL (ι ⊕ ι)) : piP q ∈ A.ratGL ι := by
  obtain ⟨x, hx⟩ := hq
  have hxm : ∀ a b, ((Matrix.GeneralLinearGroup.map A.i x : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) a b = A.i ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) E) a b) := fun a b => rfl
  have hxi : ∀ a b, (((Matrix.GeneralLinearGroup.map A.i x)⁻¹ : GL (ι ⊕ ι) R) : Matrix (ι ⊕ ι) (ι ⊕ ι) R) a b = A.i (((x⁻¹ : GL (ι ⊕ ι) E) : Matrix (ι ⊕ ι) (ι ⊕ ι) E) a b) := fun a b => by
    rw [← map_inv]; rfl
  have hst : x ∈ stab E (Sum.inl '' (Set.univ : Set ι) : Set (ι ⊕ ι)) := mem_stab_univ.2 fun r c => by
    have h := mem_stab_univ.1 q.2 r c
    rw [← hx, hxm, hxi] at h
    exact ⟨hi (by rw [h.1, map_zero]), hi (by rw [h.2, map_zero])⟩
  refine ⟨piP ⟨x, hst⟩, Units.ext ?_⟩
  ext r c
  show A.i ((x : Matrix (ι ⊕ ι) (ι ⊕ ι) E) (Sum.inl r) (Sum.inl c)) = (q.1 : Matrix (ι ⊕ ι) (ι ⊕ ι) R) (Sum.inl r) (Sum.inl c)
  rw [← hx, hxm]
end GlobalTheory.CompanionTheory.RgEisLevi
