-- Prove2me | solution 1 for GlobalTheory.NormMod.exists_norm_mod_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:08:38.473664+00:00
-- url     : https://prove2.me/submissions/cc61178d-90db-45f1-a4c5-e6cfd202b23e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHostNormModCoprimeLevelHalf
import Theorems.Thm_GlobalTheory_NormMod_exists_norm_eq
import Theorems.Thm_GlobalTheory_NormMod_span_sub_bar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NormMod
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.HostModel
open scoped TensorProduct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
namespace GlobalTheory.NormMod
theorem _root_.solution {p : ℕ} (hp : p.Prime) {ν : ℤ} (hν : IsCoprime ν (p : ℤ)) :
    ∃ t : 𝓞 E, (p : 𝓞 E) ∣ t * H.bar t - (ν : 𝓞 E) := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨k, rfl⟩ : Odd ν := by
      rw [← Int.isCoprime_two_right]; simpa using hν
    exact ⟨1, -k, by simp⟩
  let I : Ideal (𝓞 E) := Ideal.span {(p : 𝓞 E)}
  have hI : I ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  haveI : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  let σ : 𝓞 E ⧸ I →+* 𝓞 E ⧸ I := Ideal.quotientMap I (H.bar : 𝓞 E →+* 𝓞 E) (by
    rw [Ideal.span_le]
    rintro _ rfl
    rw [SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_span_singleton_self _)
  have hσ : ∀ a, σ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk I (H.bar a) := fun a => rfl
  have htop : Ideal.span {a | σ a = -a} = ⊤ := by
    rw [eq_top_iff, ← Ideal.map_top (Ideal.Quotient.mk I), ← span_sub_bar H, Ideal.map_span]
    refine Ideal.span_mono ?_
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    change σ _ = _
    rw [hσ, map_sub H.bar, bar_bar, ← map_neg, neg_sub]
  have h0 : (p : 𝓞 E ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hu : IsUnit (ν : 𝓞 E ⧸ I) := by
    obtain ⟨a, b, hab⟩ := hν
    have := congrArg (Int.cast : ℤ → 𝓞 E ⧸ I) hab
    push_cast at this
    rw [h0] at this
    exact IsUnit.of_mul_eq_one (a : 𝓞 E ⧸ I) (by linear_combination this)
  obtain ⟨t, ht⟩ := exists_norm_eq σ htop hp hp2 h0 hu (map_intCast σ ν)
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
  refine ⟨t, ?_⟩
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, ← hσ, ht,
    map_intCast, sub_self]
end GlobalTheory.NormMod
