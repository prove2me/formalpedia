-- Prove2me | solution 1 for GlobalTheory.HeckeTate.dvd_of_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:18.507885+00:00
-- url     : https://prove2.me/submissions/c2526afc-bc6a-4b6b-937b-b7dede3afff8

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
theorem _root_.solution {N x : R} (h : N ∣ x * (1 - x))
    (hx : ∀ q : Ideal R, q.IsMaximal → N ∈ q → x ∈ q) : N ∣ x := by
  have htop : Ideal.span {N, 1 - x} = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    have h1 : N ∈ q := hle (Ideal.subset_span (by simp))
    have h2 : 1 - x ∈ q := hle (Ideal.subset_span (by simp))
    exact hq.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using q.add_mem h2 (hx q hq h1)))
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 ((Ideal.eq_top_iff_one _).1 htop)
  obtain ⟨c, hc⟩ := h
  exact ⟨a * x + b * c, by linear_combination (-x) * hab + b * hc⟩
end GlobalTheory.HeckeTate
