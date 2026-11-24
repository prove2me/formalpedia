-- Prove2me | solution 1 for GlobalTheory.LineThrough.isMaximal_of_ker_lineMap_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:10:23.793142+00:00
-- url     : https://prove2.me/submissions/2cd1b905-7005-49ca-ad16-d07e254478f2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsPrimeDimensionLEOneAvoiding
import Theorems.Thm_GlobalTheory_LineThrough_lineMap_self
import Theorems.Thm_GlobalTheory_LineThrough_lineMap_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.LineThrough
namespace GlobalTheory.LineThrough
theorem _root_.solution {d : ℕ} (a c : Fin d → ℂ)
    (P : Ideal (MvPolynomial (Fin d) ℂ)) [hP : P.IsPrime] (h : RingHom.ker (lineMap a c) < P) :
    P.IsMaximal := by
  by_cases hc : c = a
  · subst hc
    have hk : RingHom.ker (lineMap c c) = RingHom.ker (MvPolynomial.eval c) := by
      ext f
      simp [RingHom.mem_ker, lineMap_self]
    have hm : (RingHom.ker (MvPolynomial.eval c)).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun z => ⟨MvPolynomial.C z, by simp⟩)
    rw [hk] at h
    exact absurd (hm.1.2 P h) hP.ne_top
  · have hs := lineMap_surjective hc
    have hp : (P.map (lineMap a c)).IsPrime := Ideal.map_isPrime_of_surjective hs h.le
    have hcm : (P.map (lineMap a c)).comap (lineMap a c) = P := by
      rw [Ideal.comap_map_of_surjective _ hs, sup_eq_left]
      exact h.le
    have hne : P.map (lineMap a c) ≠ ⊥ := by
      intro hb
      rw [hb] at hcm
      exact h.ne hcm
    have hm : (P.map (lineMap a c)).IsMaximal := Ring.DimensionLEOne.maximalOfPrime hne hp
    rw [← hcm]
    exact Ideal.comap_isMaximal_of_surjective _ hs
end GlobalTheory.LineThrough
