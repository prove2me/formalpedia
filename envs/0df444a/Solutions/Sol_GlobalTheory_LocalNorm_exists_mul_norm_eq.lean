-- Prove2me | solution 1 for GlobalTheory.LocalNorm.exists_mul_norm_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:10:22.775156+00:00
-- url     : https://prove2.me/submissions/5b611a65-87be-4475-9147-c1accc760c80

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Theorems.Thm_GlobalTheory_LocalNorm_exists_local_generator
import Theorems.Thm_GlobalTheory_LocalNorm_exists_mul_eq_of_mem_mul_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LocalNorm
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.LocalNorm
theorem _root_.solution (x : maximalRealSubfield E) (hx : x ≠ 0) {I J : Ideal (𝓞 E)}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) (σ : 𝓞 E →+* 𝓞 E)
    (hσ : ∀ a, ((σ a : 𝓞 E) : E) = IsCMField.complexConj E (a : E))
    (h : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x : E)
      * ((I * I.map σ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E)
      = ((J * J.map σ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ (z₁ z₂ : E) (u : 𝓞 (maximalRealSubfield E)), z₁ ≠ 0 ∧ u ∉ v.asIdeal ∧
      (x : E) * (z₁ * IsCMField.complexConj E z₁)
        = ((u : maximalRealSubfield E) : E) * (z₂ * IsCMField.complexConj E z₂) := by
  haveI := v.isMaximal
  obtain ⟨P, hP, hPv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 E) v.asIdeal
    (by simp [RingHom.ker_eq_bot_iff_eq_zero, (RingHom.injective_iff_ker_eq_bot _).1
      (FaithfulSMul.algebraMap_injective (𝓞 (maximalRealSubfield E)) (𝓞 E))])
  set Q := v.asIdeal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) with hQdef
  have hQP : Q ≤ P := Ideal.map_le_iff_le_comap.2 hPv.ge
  have hQ : Q ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hσ' : ∀ a, σ a = IsCMField.ringOfIntegersComplexConj E a := fun a =>
    RingOfIntegers.ext (hσ a)
  have hQσ : Q ≤ Q.comap σ := by
    refine Ideal.map_le_iff_le_comap.2 fun y hy => ?_
    rw [Ideal.mem_comap, Ideal.mem_comap, hσ', AlgEquiv.commutes]
    exact Ideal.mem_map_of_mem _ hy
  have hone : ∀ r, r - 1 ∈ Q → r ∉ P := fun r hr hrP =>
    hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using P.sub_mem hrP (hQP hr)))
  have hnorm : ∀ r, r - 1 ∈ Q → r * σ r ∉ P := fun r hr hrP =>
    (hP.isPrime.mem_or_mem hrP).elim (hone r hr) (hone _ (by simpa using hQσ hr))
  have hgen : ∀ {K : Ideal (𝓞 E)}, K ≠ ⊥ → ∀ i r : 𝓞 E, r - 1 ∈ Q →
      Ideal.span {r} * K ≤ Ideal.span {i} → (i : E) ≠ 0 := by
    intro K hK i r hr hle hi
    have hi' : i = 0 := by exact_mod_cast hi
    rw [hi', Ideal.span_singleton_zero, le_bot_iff, Ideal.mul_eq_bot,
      Ideal.span_singleton_eq_bot] at hle
    exact hone r hr (by rw [hle.resolve_right hK]; exact P.zero_mem)
  obtain ⟨i, hi, r, hr, hri⟩ := exists_local_generator hI hQ
  obtain ⟨j, hj, s, hs, hsj⟩ := exists_local_generator hJ hQ
  have hi0 := hgen hI i r hr hri
  have hj0 := hgen hJ j s hs hsj
  have hs0 : (s : E) ≠ 0 := fun h0 => hone s hs (by
    rw [show s = 0 by exact_mod_cast h0]; exact P.zero_mem)
  obtain ⟨m, hm, hmx⟩ : ∃ m ∈ J * J.map σ,
      algebraMap (𝓞 E) E m = (x : E) * algebraMap (𝓞 E) E (i * σ i) := by
    rw [← FractionalIdeal.mem_coeIdeal (𝓞 E)⁰, ← h, FractionalIdeal.mem_singleton_mul]
    exact ⟨_, (FractionalIdeal.mem_coeIdeal _).2
      ⟨_, Ideal.mul_mem_mul hi (Ideal.mem_map_of_mem _ hi), rfl⟩, rfl⟩
  obtain ⟨m', hm', hmx'⟩ : ∃ m' ∈ I * I.map σ,
      algebraMap (𝓞 E) E (j * σ j) = (x : E) * algebraMap (𝓞 E) E m' := by
    have : algebraMap (𝓞 E) E (j * σ j)
        ∈ ((J * J.map σ : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
      (FractionalIdeal.mem_coeIdeal _).2
        ⟨_, Ideal.mul_mem_mul hj (Ideal.mem_map_of_mem _ hj), rfl⟩
    rw [← h, FractionalIdeal.mem_singleton_mul] at this
    obtain ⟨y, hy, hy'⟩ := this
    obtain ⟨m', hm', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hy
    exact ⟨m', hm', hy'⟩
  obtain ⟨c, hc⟩ := exists_mul_eq_of_mem_mul_map σ hsj hm
  obtain ⟨c', hc'⟩ := exists_mul_eq_of_mem_mul_map σ hri hm'
  have hcE := congrArg (algebraMap (𝓞 E) E) hc
  have hcE' := congrArg (algebraMap (𝓞 E) E) hc'
  have hσE : ∀ a, algebraMap (𝓞 E) E (σ a) = IsCMField.complexConj E (algebraMap (𝓞 E) E a) := hσ
  simp only [map_mul, hσE] at hcE hcE' hmx hmx'
  rw [hmx] at hcE
  have hj1 : algebraMap (𝓞 E) E j * IsCMField.complexConj E (algebraMap (𝓞 E) E j) ≠ 0 :=
    mul_ne_zero hj0 ((map_ne_zero _).2 hj0)
  have hi1 : algebraMap (𝓞 E) E i * IsCMField.complexConj E (algebraMap (𝓞 E) E i) ≠ 0 :=
    mul_ne_zero hi0 ((map_ne_zero _).2 hi0)
  have hcc : c * c' = (r * σ r) * (s * σ s) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    simp only [map_mul, hσE]
    apply mul_right_cancel₀ hj1
    linear_combination algebraMap (𝓞 E) E c' * hcE
      + algebraMap (𝓞 E) E s * IsCMField.complexConj E (algebraMap (𝓞 E) E s) * (x : E) * hcE'
      - algebraMap (𝓞 E) E s * IsCMField.complexConj E (algebraMap (𝓞 E) E s)
        * algebraMap (𝓞 E) E r * IsCMField.complexConj E (algebraMap (𝓞 E) E r) * hmx'
  have hcP : c ∉ P := fun hcP =>
    (hP.isPrime.mem_or_mem (hcc ▸ P.mul_mem_right c' hcP)).elim (hnorm r hr) (hnorm s hs)
  have hfix : IsCMField.ringOfIntegersComplexConj E c = c := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [← hσ', hσE]
    have := congrArg (IsCMField.complexConj E) hcE
    simp only [map_mul, IsCMField.complexConj_apply_apply,
      IsCMField.complexConj_apply_eq_self] at this
    apply mul_right_cancel₀ hj1
    linear_combination this - hcE
  obtain ⟨u, rfl⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff E c).1 hfix
  refine ⟨algebraMap (𝓞 E) E i * algebraMap (𝓞 E) E s, algebraMap (𝓞 E) E j, u,
    mul_ne_zero hi0 hs0, fun hu => hcP (hQP (Ideal.mem_map_of_mem _ hu)), ?_⟩
  have hu : ((u : maximalRealSubfield E) : E)
      = algebraMap (𝓞 E) E (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) u) := rfl
  rw [hu, map_mul]
  linear_combination -hcE
end GlobalTheory.LocalNorm
