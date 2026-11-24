-- Prove2me | solution 1 for GlobalTheory.NormEq.Cmpl.exists_lim_of_cauchy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:29:27.598196+00:00
-- url     : https://prove2.me/submissions/6054f5d7-0e4a-41c8-954c-9045887fbc43

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_exists_pow_lt
import Theorems.Thm_GlobalTheory_NormEq_Cmpl_ball_mem_nhds_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.NormEq GlobalTheory.NormEq.Cmpl
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]
namespace GlobalTheory.NormEq.Cmpl
theorem _root_.solution [CompleteSpace L] {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (s : ℕ → L) (hsO : ∀ n, Valued.v (s n) ≤ 1)
    (hs : ∀ N : ℕ, ∃ M, ∀ m ≥ M, ∀ n ≥ M, Valued.v (s n - s m) ≤ Valued.v ϖ ^ N) :
    ∃ ℓ, Valued.v ℓ ≤ 1 ∧ ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) ≤ Valued.v ϖ ^ N := by
  have hϖ0 : ϖ ≠ 0 := fun h0 => by rw [h0, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hcs : CauchySeq s := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    obtain ⟨c, hc⟩ := MonoidWithZeroHom.ValueGroup₀.restrict₀_surjective
      (.ofClass (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) γ.1
    have hc' : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict c = γ.1 := hc
    have hc0 : Valued.v c ≠ 0 := by
      intro h0
      rw [(Valued.v).zero_iff.mp h0, map_zero] at hc'
      exact γ.ne_zero hc'.symm
    obtain ⟨N, hN⟩ := exists_pow_lt hϖ hc0
    obtain ⟨M, hM⟩ := hs N
    refine ⟨M, fun m hm n hn => ?_⟩
    change (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).restrict (s n - s m) < γ.1
    rw [← hc', Valuation.restrict_lt_iff]
    exact lt_of_le_of_lt (hM m hm n hn) hN
  obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcs
  have hev : ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (s n - ℓ) < Valued.v ϖ ^ N := fun N => by
    have := hℓ (ball_mem_nhds_of_ne (x := ℓ) (pow_ne_zero N hϖ0))
    simpa [map_pow] using this
  refine ⟨ℓ, ?_, fun N => (hev N).mono fun n hn => hn.le⟩
  obtain ⟨n, hn⟩ := (hev 0).exists
  rw [pow_zero] at hn
  have e : ℓ = s n - (s n - ℓ) := by ring
  rw [e]
  exact (Valued.v.map_sub _ _).trans (max_le (hsO n) hn.le)
end GlobalTheory.NormEq.Cmpl
