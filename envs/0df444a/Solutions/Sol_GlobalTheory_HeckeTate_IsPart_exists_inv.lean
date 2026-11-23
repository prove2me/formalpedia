-- Prove2me | solution 1 for GlobalTheory.HeckeTate.IsPart.exists_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:23.353636+00:00
-- url     : https://prove2.me/submissions/e551b4ab-a201-46c3-90bb-38b0a32c9343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R]
namespace GlobalTheory.HeckeTate
namespace IsPart
theorem _root_.solution {P : Ideal R} {N e s : R} (h : IsPart P N e) (hs : s ∉ P) :
    ∃ w, N ∣ w * s * e - e := by
  have htop : Ideal.span {N, s, 1 - e} = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : N ∈ q := hle (Ideal.subset_span (by simp))
    have h2 : 1 - e ∈ q := hle (Ideal.subset_span (by simp))
    have h3 : s ∈ q := hle (Ideal.subset_span (by simp))
    by_cases hqP : q = P
    · exact hs (hqP ▸ h3)
    · exact hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.add_mem h2 (h.2.2 q hq h1 hqP)))
  obtain ⟨a, b, c, habc⟩ := Submodule.mem_span_triple.1 ((Ideal.eq_top_iff_one _).1 htop)
  simp only [smul_eq_mul] at habc
  obtain ⟨d, hd⟩ := h.1
  exact ⟨b, -(a * e) - c * d, by linear_combination e * habc - c * hd⟩
end IsPart
end GlobalTheory.HeckeTate
