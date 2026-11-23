-- Prove2me | solution 1 for GlobalTheory.CoefEmbed.norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:50:34.765853+00:00
-- url     : https://prove2.me/submissions/2ee155bf-6018-44f4-bbaa-82ce73e13b9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EmbeddingClosedIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CoefEmbed
open IsLocalRing Topology
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
namespace GlobalTheory.CoefEmbed
theorem _root_.solution (f : O →+* PadicAlgCl l)
    (hf : ∀ z : ℤ_[l], f (algebraMap ℤ_[l] O z) = algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))
    (a : O) : ‖f a‖ ≤ 1 := by
  obtain ⟨p, hp, hp0⟩ : IsIntegral ℤ_[l] a := Algebra.IsIntegral.isIntegral a
  by_contra hlt
  push Not at hlt
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have hp1 := congrArg f hp0
  simp only [map_add, map_sum, map_mul, map_pow, map_zero, hf] at hp1
  set y := f a
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree,
        algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l]) * y ^ i := by
    linear_combination hp1
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree,
      algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l]) * y ^ i‖ < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℚ_[l] (PadicAlgCl l) (p.coeff i : ℚ_[l])‖ ≤ 1 := by
        rw [norm_algebraMap']
        exact (p.coeff i).2
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2
end GlobalTheory.CoefEmbed
