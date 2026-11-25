-- Prove2me | solution 1 for GlobalTheory.heckeChar_val_isAlgebraic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:29:42.00066+00:00
-- url     : https://prove2.me/submissions/d3fac679-f5d3-44ad-8698-1d4ae5b7fbff

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HeckeCharUniformiserValueIsAlgebraic
import Theorems.Thm_GlobalTheory_isAlgebraic_embedding_apply
import Theorems.Thm_Formalism_L2_Host_unif_spec
import Theorems.Thm_Neutral_B1_localIdele_isSupportedAt
import Theorems.Thm_Neutral_B1_localIdele_snd_self
import Theorems.Thm_PI_AlgValsFin_W_classPow
import Theorems.Thm_PI_AlgValsFin_W_decomp
import Theorems.Thm_PI_AlgValsFin_W_torsUnits
import Theorems.Thm_PI_AlgValsFin_W_valued_atFin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.L2.Host
noncomputable section
open GlobalTheory
open PI.AlgValsFin.W ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
namespace GlobalTheory
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] (χ : HChar L) (m : (L →+* ℂ) → ℤ),
    (∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ φ : L →+* ℂ, φ (k : L) ^ m φ) →
    ∀ w : HeightOneSpectrum (𝓞 L), IsAlgebraic ℚ ((χ.val w : ℂˣ) : ℂ) := by
  intro L _ _ χ m hm w
  classical

  obtain ⟨h, hpos, hk⟩ := (classPow : ClassPow L)
  obtain ⟨k, hk⟩ := hk w
  have hkw : ordF w k = (h : ℤ) := by rw [hk w, if_pos rfl]
  have hout : ∀ v, v ∉ ({w} : Finset (HeightOneSpectrum (𝓞 L))) → ordF v k = 0 := by
    intro v hv
    rw [hk v, if_neg (by simpa using hv)]
  obtain ⟨r, hr, hdec⟩ := (decomp : Decomp L) k {w} hout
  rw [Finset.prod_singleton] at hdec
  have hrel : χ.inf k * χ.loc w (atFin w k) * χ.1 r = 1 := by
    have e := χ.2.2 k
    rw [hdec, map_mul, map_mul] at e
    exact e
  obtain ⟨N, hN, hNt⟩ := torsUnits L χ

  have hinf : IsAlgebraic ℚ ((χ.inf k : ℂˣ) : ℂ) := by
    rw [hm k, ← mem_algebraicClosure_iff]
    refine prod_mem fun φ _ => zpow_mem ?_ _
    exact mem_algebraicClosure_iff.2 (isAlgebraic_embedding_apply φ _)

  have hloc : IsAlgebraic ℚ ((χ.loc w (atFin w k) : ℂˣ) : ℂ) := by
    have e : χ.loc w (atFin w k) ^ N = (χ.inf k ^ N)⁻¹ := by
      have e1 := congrArg (· ^ N) hrel
      simp only [mul_pow, hNt r hr, mul_one, one_pow] at e1
      exact eq_inv_of_mul_eq_one_right e1
    refine IsAlgebraic.of_pow hN ?_
    rw [← Units.val_pow_eq_pow_val, e, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val,
      ← mem_algebraicClosure_iff]
    exact inv_mem (pow_mem (mem_algebraicClosure_iff.2 hinf) _)

  set y : (w.adicCompletion L)ˣ := atFin w (unif w) ^ h * (atFin w k)⁻¹ with hy
  have hyv : Valued.v ((y : (w.adicCompletion L)ˣ) : w.adicCompletion L) = 1 := by
    have h1 : Valued.v ((atFin w (unif w) : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
        WithZero.exp (-1) := unif_spec w
    rw [hy, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_mul, map_inv₀, map_pow, h1,
      valued_atFin, hkw, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hyU : localIdele L w y ∈ UFin L := by
    refine ⟨rfl, fun v => ?_⟩
    by_cases hv : v = w
    · subst hv
      rw [localIdele_snd_self]
      exact hyv
    · rw [(localIdele_isSupportedAt L w y).2 v hv, map_one]
  have hyN : χ.loc w y ^ N = 1 := hNt _ hyU
  have hyval : χ.loc w y = χ.val w ^ h * (χ.loc w (atFin w k))⁻¹ := by
    rw [hy, map_mul, map_pow, map_inv]
    rfl
  have hpow : χ.val w ^ (h * N) = χ.loc w (atFin w k) ^ N := by
    rw [hyval, mul_pow, ← pow_mul, inv_pow, mul_inv_eq_one] at hyN
    exact hyN
  refine IsAlgebraic.of_pow (Nat.mul_pos hpos hN) ?_
  rw [← Units.val_pow_eq_pow_val, hpow, Units.val_pow_eq_pow_val, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hloc) _
end GlobalTheory
