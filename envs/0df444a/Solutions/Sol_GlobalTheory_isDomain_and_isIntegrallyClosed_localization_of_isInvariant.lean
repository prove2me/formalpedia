-- Prove2me | solution 1 for GlobalTheory.isDomain_and_isIntegrallyClosed_localization_of_isInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:11:28.753313+00:00
-- url     : https://prove2.me/submissions/139c96b1-c533-4ad4-8f7d-79b306682bb9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoNormalizationPullbackOfToIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsDomainAndIsIntegrallyClosedLocalizationOfIsInv
import Theorems.Thm_GlobalTheory_exists_invariant_mem_notMem
import Theorems.Thm_GlobalTheory_isIntegrallyClosed_of_injective_of_dvd
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_exists_orbit_eq_primesOver_of_isInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor



set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
variable (G A)
namespace GlobalTheory
theorem _root_.solution (B : Type*) [CommRing B]
    [Algebra B A] [FaithfulSMul B A] [SMulCommClass G B A] [Algebra.IsInvariant B A G]
    (hA : ∀ (q : Ideal A) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (p : Ideal B) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  classical
  cases nonempty_fintype G
  have hinj := FaithfulSMul.algebraMap_injective B A
  obtain ⟨q₀, hq₀, hq₀p, -⟩ := exists_orbit_eq_primesOver_of_isInvariant A G B p
  have hover (q : Ideal A) [q.LiesOver p] (g : G) : (g • q).LiesOver p :=
    ⟨by rw [Ideal.under_smul]; exact q.over_def p⟩
  have key (q : Ideal A) [q.IsPrime] [q.LiesOver p] (I : Ideal A) (h : ∀ g : G, ¬ I ≤ g • q) :
      ∃ t : B, t ∉ p ∧ algebraMap B A t ∈ I := by
    obtain ⟨t, htI, ht, htq⟩ := exists_invariant_mem_notMem q I h
    obtain ⟨t, rfl⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) t ht
    exact ⟨t, fun hp ↦ htq ((Ideal.mem_of_liesOver q p t).mp hp), htI⟩
  have zero (q : Ideal A) [q.IsPrime] [q.LiesOver p] (b : B)
      (hb : algebraMap A (Localization.AtPrime q) (algebraMap B A b) = 0) :
      algebraMap B (Localization.AtPrime p) b = 0 := by
    obtain ⟨⟨s, hs⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff q.primeCompl _ _).mp hb
    obtain ⟨t, htp, ht⟩ := key q ((⊥ : Ideal A).colon {algebraMap B A b}) fun g hg ↦ by
      refine hs (Ideal.smul_mem_pointwise_smul_iff.mp (hg (?_ : g • s ∈ _)))
      rw [Submodule.mem_colon_singleton, Ideal.mem_bot, smul_eq_mul, ← smul_algebraMap g b,
        ← smul_mul', show s * algebraMap B A b = 0 from hsb, smul_zero]
    rw [Submodule.mem_colon_singleton, Ideal.mem_bot, smul_eq_mul, ← map_mul,
      map_eq_zero_iff _ hinj] at ht
    exact (IsLocalization.map_eq_zero_iff p.primeCompl _ _).mpr ⟨⟨t, htp⟩, ht⟩
  obtain ⟨_, _⟩ := hA q₀
  let φ := Localization.localRingHom p q₀ (algebraMap B A) (q₀.over_def p)
  have hφa (b : B) : φ (algebraMap B _ b) = algebraMap A _ (algebraMap B A b) :=
    Localization.localRingHom_to_map ..
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj p.primeCompl x
    have := congrArg φ hbs
    rw [map_mul, hx, zero_mul, hφa] at this
    rw [zero q₀ b this.symm] at hbs
    exact (IsLocalization.map_units _ s).mul_left_eq_zero.mp hbs
  have : IsDomain (Localization.AtPrime p) := hφ.isDomain φ
  refine ⟨this, isIntegrallyClosed_of_injective_of_dvd φ hφ fun x y hy hxy ↦ ?_⟩
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj p.primeCompl x
  obtain ⟨⟨b, s'⟩, hbs⟩ := IsLocalization.surj p.primeCompl y
  have hs := IsLocalization.map_units (Localization.AtPrime p) s
  have hs' := IsLocalization.map_units (Localization.AtPrime p) s'
  dsimp only at has hbs
  have hb0 : algebraMap B (Localization.AtPrime p) b ≠ 0 := by
    rw [← hbs]; exact mul_ne_zero hy hs'.ne_zero
  rw [← hs.dvd_mul_right, ← hs'.mul_right_dvd, has, hbs]
  rw [← (hs.map φ).dvd_mul_right, ← (hs'.map φ).mul_right_dvd, ← map_mul, ← map_mul, has, hbs,
    hφa, hφa] at hxy
  obtain ⟨z, hz⟩ := hxy
  obtain ⟨⟨c, r⟩, hcr⟩ := IsLocalization.surj q₀.primeCompl z
  dsimp only at hcr
  have e : algebraMap A (Localization.AtPrime q₀) (r * algebraMap B A a) =
      algebraMap A _ (algebraMap B A b * c) := by
    rw [map_mul, map_mul, hz, ← hcr]; ring
  obtain ⟨r', hr'⟩ := (IsLocalization.eq_iff_exists q₀.primeCompl _).mp e
  obtain ⟨t, htp, ht⟩ := key q₀ ((Ideal.span {algebraMap B A b}).colon {algebraMap B A a})
    fun g hg ↦ by
      refine (r' * r).2 (Ideal.smul_mem_pointwise_smul_iff.mp (hg (?_ : g • (r' * r : A) ∈ _)))
      rw [Submodule.mem_colon_singleton, Ideal.mem_span_singleton, smul_eq_mul,
        ← smul_algebraMap g a, ← smul_mul', mul_assoc, hr', mul_left_comm, smul_mul',
        smul_algebraMap]
      exact dvd_mul_right _ _
  rw [Submodule.mem_colon_singleton, Ideal.mem_span_singleton, smul_eq_mul] at ht
  obtain ⟨c, hc⟩ := ht
  have hc' (g : G) : algebraMap B A b * (g • c - c) = 0 := by
    rw [mul_sub, ← hc, ← smul_algebraMap g b, ← smul_mul', ← hc, ← map_mul, smul_algebraMap,
      sub_self]
  obtain ⟨t', ht'p, ht'⟩ := key q₀ (Finset.univ.inf fun g : G ↦ (⊥ : Ideal A).colon {g • c - c})
    fun k hk ↦ by
      have := hover q₀ k
      obtain ⟨_, -⟩ := hA (k • q₀)
      obtain ⟨g, -, hg⟩ := (Ideal.IsPrime.inf_le' inferInstance).mp hk
      have h1 := congrArg (algebraMap A (Localization.AtPrime (k • q₀))) (hc' g)
      rw [map_mul, map_zero, mul_eq_zero] at h1
      obtain ⟨⟨w, hw⟩, hw'⟩ := (IsLocalization.map_eq_zero_iff (k • q₀).primeCompl _ _).mp
        (h1.resolve_left fun h0 ↦ hb0 (zero _ b h0))
      exact hw (hg (Submodule.mem_colon_singleton.mpr hw'))
  obtain ⟨d, hd⟩ := Algebra.IsInvariant.isInvariant (A := B) (G := G) (algebraMap B A t' * c)
    fun g ↦ by
      have := Submodule.mem_colon_singleton.mp
        ((Finset.inf_le (f := fun g : G ↦ (⊥ : Ideal A).colon {g • c - c}) (Finset.mem_univ g)) ht')
      rw [Ideal.mem_bot, smul_eq_mul, mul_sub, sub_eq_zero] at this
      rw [smul_mul', smul_algebraMap, this]
  have e' : t' * t * a = b * d := hinj (by
    rw [map_mul, map_mul, map_mul, hd, mul_assoc, hc, mul_left_comm])
  rw [← (IsLocalization.map_units (Localization.AtPrime p)
    (⟨t', ht'p⟩ * ⟨t, htp⟩ : p.primeCompl)).dvd_mul_left, ← map_mul]
  exact map_dvd _ ⟨d, e'⟩
end GlobalTheory
