-- Prove2me | solution 1 for GlobalTheory.LadicPlace.norm_embedding_integer_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:35:12.018048+00:00
-- url     : https://prove2.me/submissions/7a8422c3-8399-4a36-bf75-e4f8a09227a6

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__ExistsUniqueHcharOfFiniteOrder_ea3c3b0616a9bf04
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormEmbeddingIntegerLeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory GlobalTheory.LadicPlace
namespace GlobalTheory.LadicPlace
theorem _root_.solution {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (a : E)) := by
    have := (RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
    simpa using this
  obtain ⟨p, hp, hp0⟩ := h
  by_contra hlt
  push_neg at hlt
  set y := τ (a : E)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i := by
    linear_combination hp0
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℤ (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) (p.coeff i)
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2
end GlobalTheory.LadicPlace
