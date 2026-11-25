-- Prove2me | solution 1 for GlobalTheory.FramePsi.exists_nsmul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:31:31.029953+00:00
-- url     : https://prove2.me/submissions/48c179e5-49c5-4e19-be5b-b7a034713c82

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.FramePsi
theorem _root_.solution [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : E) * y ∈ L.O := by
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  have hyF : IsAlgebraic F y := Algebra.IsAlgebraic.isAlgebraic y
  have hy : IsAlgebraic 𝒪[F] y := (IsFractionRing.isAlgebraic_iff 𝒪[F] F E).2 hyF
  obtain ⟨c, hc, hcy⟩ := hy.exists_integral_multiple
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc hϖ
  have hp : ((Nat.card 𝓀[F] : ℕ) : 𝒪[F]) ∈ IsLocalRing.maximalIdeal 𝒪[F] := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    have := Fintype.ofFinite 𝓀[F]
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hp
  have hdv : c ∣ ((Nat.card 𝓀[F] ^ m : ℕ) : 𝒪[F]) := by
    rw [hu, Nat.cast_pow, Units.mul_left_dvd]
    exact pow_dvd_pow_of_dvd hp m
  obtain ⟨d, hd⟩ := hdv
  refine ⟨Nat.card 𝓀[F] ^ m, pow_ne_zero _ Nat.card_pos.ne', (L.O_def _).2 ?_⟩
  have : ((Nat.card 𝓀[F] ^ m : ℕ) : E) * y = d • (c • y) := by
    rw [smul_smul, mul_comm d c, ← hd, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]
  rw [this]
  exact hcy.smul d
end GlobalTheory.FramePsi
