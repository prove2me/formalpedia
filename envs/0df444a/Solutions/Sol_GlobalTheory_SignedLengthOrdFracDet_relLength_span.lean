-- Prove2me | solution 1 for GlobalTheory.SignedLengthOrdFracDet.relLength_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:15:06.546813+00:00
-- url     : https://prove2.me/submissions/bfa6c322-f1cc-4359-9b9a-1e810ef23583

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SignedLengthSpanEqOrdFracDet
import Theorems.Thm_GlobalTheory_SignedLengthOrdFracDet_length_coker

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SignedLengthOrdFracDet
open Module Submodule
namespace GlobalTheory.SignedLengthOrdFracDet
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a c : ι → V} (ha : LinearIndependent R a) (P : Matrix ι ι R) (hP : P.det ≠ 0)
    (hc : ∀ j, c j = ∑ i, P i j • a i) :
    span R (Set.range c) ≤ span R (Set.range a) ∧
      relLength (span R (Set.range a)) (span R (Set.range c)) = Ring.ord R P.det := by
  let φ : (ι → R) →ₗ[R] V := Fintype.linearCombination R a
  have hφ : Function.Injective φ := ha.fintypeLinearCombination_injective
  have h1 : span R (Set.range a) = (⊤ : Submodule R (ι → R)).map φ := by
    rw [Submodule.map_top, Fintype.range_linearCombination]
  have h2 : span R (Set.range c) = (LinearMap.range (Matrix.toLin' P)).map φ := by
    rw [Matrix.range_toLin', Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    simp [φ, hc j, Fintype.linearCombination_apply]
  have hinj : Function.Injective (Matrix.toLin' P) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hP (by simpa using hv)
  refine ⟨?_, ?_⟩
  · rw [h1, h2]; exact Submodule.map_mono le_top
  · rw [h1, h2, relLength_map_of_injective φ hφ, relLength_top_left,
      length_coker (Pi.basisFun R ι) _ hinj, LinearMap.det_toLin']
end GlobalTheory.SignedLengthOrdFracDet
