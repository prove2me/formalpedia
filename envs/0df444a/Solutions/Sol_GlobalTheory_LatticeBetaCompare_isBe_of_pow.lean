-- Prove2me | solution 1 for GlobalTheory.LatticeBetaCompare.isBe_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:55:37.146488+00:00
-- url     : https://prove2.me/submissions/777bfda3-f715-4dc5-80ab-0896bd212abe

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ReflexNormIndexIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsMulMemOfMemSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsCoeEqSpanDetOfIntVecLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_MultAddMultConjugate
import Theorems.Thm_GlobalTheory_LatticeBetaCompare_reflexIdeal_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LatticeBetaCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.GenusLatCompare
open scoped nonZeroDivisors Pointwise
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)
variable {Dw c}
namespace GlobalTheory.LatticeBetaCompare
theorem _root_.solution {𝔞 : Ideal (𝓞 E)} {ψ : c.F} {k : ℕ} (hk : 0 < k) (h : IsBe Dw c (𝔞 ^ k) (ψ ^ k)) :
    IsBe Dw c 𝔞 ψ := by
  obtain ⟨⟨b, hb, hI⟩, h⟩ := h
  have hψ : IsIntegral ℤ ψ := IsIntegral.of_pow hk (hb ▸ b.isIntegral_coe)
  obtain ⟨b₀, rfl⟩ : ∃ b₀ : 𝓞 c.F, (b₀ : c.F) = ψ := ⟨⟨ψ, hψ⟩, rfl⟩
  refine ⟨⟨b₀, rfl, ?_⟩, fun s => ?_⟩
  · have e : b = b₀ ^ k := RingOfIntegers.ext hb
    rw [e, ← Ideal.span_singleton_pow, reflexIdeal_pow] at hI
    exact pow_left_injective hk.ne' hI
  · have := h s
    rw [map_pow, norm_pow, map_pow, Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k, mul_comm k, pow_mul,
      pow_mul] at this
    exact (pow_left_inj₀ (by positivity) (by positivity) hk.ne').1 this
end GlobalTheory.LatticeBetaCompare
