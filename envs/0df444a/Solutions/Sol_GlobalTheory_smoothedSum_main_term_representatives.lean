-- Prove2me | solution 1 for GlobalTheory.smoothedSum_main_term_representatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:51:38.289805+00:00
-- url     : https://prove2.me/submissions/1af05684-91e6-4979-81bf-e5ebc3980051

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TsumIdealEqSumClassGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealSumPeriodicDilate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsSmoothHomogeneousHasSumUnitSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SmoothedIdealCharacterSumMainTermIdealClassRepre
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_GlobalTheory_IdealSum_ideal_sum_periodic_dilate
import Theorems.Thm_GlobalTheory_existsUnique_isPrincipal_mul_classRep
import Theorems.Thm_GlobalTheory_exists_smooth_homogeneous_hasSum_unit_smul
import Theorems.Thm_GlobalTheory_tsum_isPrincipal_mul_eq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem exists_periodic_mod_ideal_eq_character_div_infinity_type {K : Type} [Field K] [NumberField K]
    (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (φ : mixedSpace K → ℂ)
    (hXmul : ∀ I J, X (I * J) = X I * X J) (hXcop : ∀ I, I ⊔ m ≠ ⊤ → X I = 0)
    (hφmul : ∀ x y, φ (x * y) = φ x * φ y)
    (hφnorm : ∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1)
    (hXφ : ∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) :
    ∃ ψ : 𝓞 K → ℂ, (∀ a b, a - b ∈ m → ψ a = ψ b) ∧
      ∀ β : 𝓞 K, β ≠ 0 → X (Ideal.span {β}) = ψ β * φ (mixedEmbedding K β) := by
  have hφne : ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) ≠ 0 := by
    intro β hβ h0
    have h1 := hφnorm (mixedEmbedding K β) (by
      rw [mixedEmbedding.norm_eq_norm]
      simpa [Algebra.norm_eq_zero_iff] using hβ)
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1

  have hinv : ∀ a : 𝓞 K, Ideal.span {a} ⊔ m = ⊤ → ∃ r : 𝓞 K, r * a - 1 ∈ m := by
    intro a ha
    have h1 : (1 : 𝓞 K) ∈ Ideal.span {a} ⊔ m := by rw [ha]; exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h1
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    refine ⟨r, ?_⟩
    have : r * a - 1 = -z := by rw [← hyz]; ring
    rw [this]
    exact m.neg_mem hz
  have hunit : ∀ c : 𝓞 K, c - 1 ∈ m → m ≠ ⊤ → c ≠ 0 := by
    intro c hc hm h0
    apply hm
    rw [h0, zero_sub] at hc
    exact (Ideal.eq_top_iff_one _).2 (by simpa using m.neg_mem hc)
  let ψ : 𝓞 K → ℂ := fun β =>
    if Ideal.span {β} ⊔ m = ⊤ ∧ β ≠ 0 then X (Ideal.span {β}) * (φ (mixedEmbedding K β))⁻¹
    else if m = ⊤ then 1 else 0
  have hψtop : m = ⊤ → ∀ a, ψ a = 1 := by
    intro hm a
    by_cases ha : a = 0
    · simp [ψ, ha, hm]
    · have h1 : Ideal.span {a} ⊔ m = ⊤ := by rw [hm, sup_top_eq]
      simp only [ψ, h1, ne_eq, ha, not_false_eq_true, and_self, if_true]
      rw [hXφ a ha (by rw [hm]; exact Submodule.mem_top)]
      exact mul_inv_cancel₀ (hφne a ha)
  refine ⟨ψ, ?_, ?_⟩
  · intro a b hab
    by_cases hm : m = ⊤
    · rw [hψtop hm a, hψtop hm b]
    have hsup : Ideal.span {a} ⊔ m = Ideal.span {b} ⊔ m := by
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        rw [Ideal.span_singleton_le_iff_mem]
        have : a = b + (a - b) := by ring
        rw [this]
        exact Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self b))
          (Ideal.mem_sup_right hab)
      · refine sup_le ?_ le_sup_right
        rw [Ideal.span_singleton_le_iff_mem]
        have : b = a - (a - b) := by ring
        rw [this]
        exact Ideal.sub_mem _ (Ideal.mem_sup_left (Ideal.mem_span_singleton_self a))
          (Ideal.mem_sup_right hab)
    have hnz : ∀ c : 𝓞 K, Ideal.span {c} ⊔ m = ⊤ → c ≠ 0 := by
      intro c hc h0
      apply hm
      rw [h0, Ideal.span_singleton_eq_bot.2 rfl, bot_sup_eq] at hc
      exact hc
    by_cases ha : Ideal.span {a} ⊔ m = ⊤
    · have hb : Ideal.span {b} ⊔ m = ⊤ := hsup ▸ ha
      have ha0 := hnz a ha
      have hb0 := hnz b hb
      obtain ⟨r, hr⟩ := hinv a ha
      have hrb : r * b - 1 ∈ m := by
        have : r * b - 1 = (r * a - 1) - r * (a - b) := by ring
        rw [this]
        exact m.sub_mem hr (m.mul_mem_left r hab)
      have eA := hXφ (r * a) (hunit _ hr hm) hr
      have eB := hXφ (r * b) (hunit _ hrb hm) hrb
      rw [← Ideal.span_singleton_mul_span_singleton, hXmul] at eA eB
      push_cast at eA eB
      rw [map_mul, hφmul] at eA eB
      have hXr : X (Ideal.span {r}) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at eA
        exact mul_ne_zero (hφne r (fun h => by simp [h] at hr; exact hm ((Ideal.eq_top_iff_one _).2
          (by simpa using m.neg_mem hr)))) (hφne a ha0) eA.symm
      simp only [ψ, ha, hb, ne_eq, ha0, hb0, not_false_eq_true, and_self, if_true]
      have hφa := hφne a ha0
      have hφb := hφne b hb0
      rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff hφa hφb]
      apply mul_left_cancel₀ hXr
      linear_combination φ (mixedEmbedding K b) * eA - φ (mixedEmbedding K a) * eB
    · have hb : ¬ Ideal.span {b} ⊔ m = ⊤ := hsup ▸ ha
      simp [ψ, ha, hb, hm]
  · intro β hβ
    by_cases hc : Ideal.span {β} ⊔ m = ⊤
    · simp only [ψ, hc, ne_eq, hβ, not_false_eq_true, and_self, if_true]
      rw [mul_assoc, inv_mul_cancel₀ (hφne β hβ), mul_one]
    · have hm : m ≠ ⊤ := fun hm => hc (by rw [hm, sup_top_eq])
      simp [ψ, hc, hm, hXcop _ hc]
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem contDiffAt_mixedEmbedding_norm_of_ne_zero {K : Type} [Field K] [NumberField K] {x : mixedSpace K}
    (hx : mixedEmbedding.norm x ≠ 0) : ContDiffAt ℝ ∞ (⇑(mixedEmbedding.norm (K := K))) x := by
  have hfun : (⇑(mixedEmbedding.norm (K := K)) : mixedSpace K → ℝ) =
      fun y => ∏ w, (normAtPlace w) y ^ w.mult := by
    funext y; exact mixedEmbedding.norm_apply y
  rw [hfun]
  rw [mixedEmbedding.norm_apply] at hx
  apply contDiffAt_prod
  intro w _
  have hw : (normAtPlace w) x ≠ 0 := by
    intro h0
    exact hx (Finset.prod_eq_zero (Finset.mem_univ w) (by rw [h0, zero_pow (by
      unfold NumberField.InfinitePlace.mult; split_ifs <;> norm_num)]))
  apply ContDiffAt.pow
  by_cases hr : w.IsReal
  · have e : (⇑(normAtPlace w) : mixedSpace K → ℝ) = fun y => ‖y.1 ⟨w, hr⟩‖ := by
      funext y; exact normAtPlace_apply_of_isReal hr y
    rw [e]
    have hx' : x.1 ⟨w, hr⟩ ≠ 0 := by
      intro h0; apply hw; rw [normAtPlace_apply_of_isReal hr, h0, norm_zero]
    exact (contDiffAt_norm ℝ hx').comp x
      ((contDiff_apply ℝ ℝ (⟨w, hr⟩ : {w : InfinitePlace K // w.IsReal})).comp contDiff_fst).contDiffAt
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.1 hr
    have e : (⇑(normAtPlace w) : mixedSpace K → ℝ) = fun y => ‖y.2 ⟨w, hc⟩‖ := by
      funext y; exact normAtPlace_apply_of_isComplex hc y
    rw [e]
    have hx' : x.2 ⟨w, hc⟩ ≠ 0 := by
      intro h0; apply hw; rw [normAtPlace_apply_of_isComplex hc, h0, norm_zero]
    exact (contDiffAt_norm ℝ hx').comp x
      ((contDiff_apply ℝ ℂ (⟨w, hc⟩ : {w : InfinitePlace K // w.IsComplex})).comp contDiff_snd).contDiffAt
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem contDiff_and_hasCompactSupport_mul_weight_mixedNorm {K : Type} [Field K] [NumberField K]
    (h : mixedSpace K → ℝ) (hh : ContDiffOn ℝ ∞ h {x | mixedEmbedding.norm x ≠ 0})
    (hC : ∀ a b : ℝ, 0 < a → ∃ C, IsCompact C ∧ (∀ x ∈ C, mixedEmbedding.norm x ≠ 0) ∧
      ∀ x : mixedSpace K, h x ≠ 0 → a ≤ mixedEmbedding.norm x → mixedEmbedding.norm x ≤ b →
        x ∈ C)
    (φ : mixedSpace K → ℂ) (hφ : ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0})
    (wt : ℝ → ℂ) (hwt : ContDiff ℝ ∞ wt) (a b : ℝ) (ha : 0 < a)
    (hab : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) :
    ContDiff ℝ ∞ (fun x => (h x : ℂ) * φ x * wt (mixedEmbedding.norm x)) ∧
      HasCompactSupport (fun x => (h x : ℂ) * φ x * wt (mixedEmbedding.norm x)) := by
  obtain ⟨C, hCc, hCn, hCmem⟩ := hC a b ha
  have hsupp : ∀ x, x ∉ C → (h x : ℂ) * φ x * wt (mixedEmbedding.norm x) = 0 := by
    intro x hx
    by_contra hne
    have hw : wt (mixedEmbedding.norm x) ≠ 0 := right_ne_zero_of_mul hne
    have hh0 : (h x : ℂ) ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul hne)
    exact hx (hCmem x (by exact_mod_cast hh0) (hab _ hw).1 (hab _ hw).2)
  refine ⟨?_, HasCompactSupport.intro hCc hsupp⟩
  have hU : IsOpen {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} :=
    isOpen_ne_fun (mixedEmbedding.continuous_norm K) continuous_const
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : mixedEmbedding.norm x ≠ 0
  · have hn : {x : mixedSpace K | mixedEmbedding.norm x ≠ 0} ∈ nhds x := hU.mem_nhds hx
    refine ContDiffAt.mul (ContDiffAt.mul ?_ (hφ.contDiffAt hn)) ?_
    · exact Complex.ofRealCLM.contDiff.contDiffAt.comp x (hh.contDiffAt hn)
    · exact hwt.contDiffAt.comp x (contDiffAt_mixedEmbedding_norm_of_ne_zero hx)
  · have hxC : x ∉ C := fun hxC => hCn x hxC (not_not.1 hx ▸ by simpa using hx)
    have hev : (fun x => (h x : ℂ) * φ x * wt (mixedEmbedding.norm x)) =ᶠ[nhds x]
        fun _ => (0 : ℂ) := by
      filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hxC] with y hy
      exact hsupp y hy
    exact contDiffAt_const.congr_of_eventuallyEq hev
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem finite_setOf_ringOfIntegers_mixedEmbedding_mem_compact {K : Type} [Field K] [NumberField K]
    (C : Set (mixedSpace K)) (hC : IsCompact C) :
    {β : 𝓞 K | mixedEmbedding K (β : K) ∈ C}.Finite := by
  haveI : DiscreteTopology (mixedEmbedding.integerLattice K).toAddSubgroup :=
    (inferInstance : DiscreteTopology (mixedEmbedding.integerLattice K))
  have hcl : IsClosed ((mixedEmbedding.integerLattice K : Submodule ℤ (mixedSpace K)) :
      Set (mixedSpace K)) :=
    AddSubgroup.isClosed_of_discrete (H := (mixedEmbedding.integerLattice K).toAddSubgroup)
  have hc : IsCompact (((↑) : mixedEmbedding.integerLattice K → mixedSpace K) ⁻¹' C) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hfin2 := hc.finite_of_discrete.image Subtype.val
  refine (hfin2.preimage (f := fun β : 𝓞 K => mixedEmbedding K (β : K)) ?_).subset ?_
  · intro x _ y _ hxy
    exact RingOfIntegers.ext ((mixedEmbedding_injective K) hxy)
  · intro β hβ
    exact ⟨⟨mixedEmbedding K (β : K), ⟨β, rfl⟩⟩, hβ, rfl⟩
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem mixedEmbedding_norm_eq_absNorm_span_singleton {K : Type} [Field K] [NumberField K] (β : 𝓞 K) :
    mixedEmbedding.norm (mixedEmbedding K (β : K)) = (Ideal.absNorm (Ideal.span {β}) : ℝ) := by
  rw [mixedEmbedding.norm_eq_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int]
  push_cast
  simp [Nat.cast_natAbs]
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
set_option maxHeartbeats 1000000 in
private theorem tsum_principal_le_eq_tsum_mul_cutoff_span {K : Type} [Field K] [NumberField K]
    (B : Ideal (𝓞 K)) (G : Ideal (𝓞 K) → ℂ) (hG0 : G ⊥ = 0) (h : mixedSpace K → ℝ)
    (hsum : ∀ x : mixedSpace K, mixedEmbedding.norm x ≠ 0 →
      HasSum (fun u : (𝓞 K)ˣ => h (u • x)) 1)
    (hfin : (Function.support fun β : B =>
      (h (mixedEmbedding K ((β : 𝓞 K) : K)) : ℂ) * G (Ideal.span {(β : 𝓞 K)})).Finite) :
    ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, G J =
      ∑' β : B, (h (mixedEmbedding K ((β : 𝓞 K) : K)) : ℂ) * G (Ideal.span {(β : 𝓞 K)}) := by
  set g : B → ℂ := fun β =>
    (h (mixedEmbedding K ((β : 𝓞 K) : K)) : ℂ) * G (Ideal.span {(β : 𝓞 K)}) with hg
  have hgsum : Summable g := summable_of_finite_support hfin

  let gen : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B} → 𝓞 K := fun J =>
    @Submodule.IsPrincipal.generator _ _ _ _ _ J.1 J.2.2.1
  have hgen : ∀ J, Ideal.span {gen J} = J.1 := fun J =>
    @Ideal.span_singleton_generator _ _ J.1 J.2.2.1
  have hgen0 : ∀ J, gen J ≠ 0 := fun J h0 => J.2.1 (by rw [← hgen J, h0, Ideal.span_singleton_eq_bot])
  have hgenB : ∀ J, gen J ∈ B := fun J =>
    J.2.2.2 (by rw [← hgen J]; exact Ideal.mem_span_singleton_self _)
  let e : (Σ _J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B}, (𝓞 K)ˣ) →
      {β : B // (β : 𝓞 K) ≠ 0} := fun p =>
    ⟨⟨(p.2 : 𝓞 K) * gen p.1, B.mul_mem_left _ (hgenB p.1)⟩,
      mul_ne_zero p.2.ne_zero (hgen0 p.1)⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨J, u⟩ ⟨J', u'⟩ hJ
      have h1 : (u : 𝓞 K) * gen J = (u' : 𝓞 K) * gen J' := congrArg (fun x => ((x.1 : B) : 𝓞 K)) hJ
      have hJJ : J = J' := by
        apply Subtype.ext
        calc J.1 = Ideal.span {gen J} := (hgen J).symm
          _ = Ideal.span {(u : 𝓞 K) * gen J} :=
            (Ideal.span_singleton_mul_left_unit u.isUnit (gen J)).symm
          _ = Ideal.span {(u' : 𝓞 K) * gen J'} := by rw [h1]
          _ = Ideal.span {gen J'} := Ideal.span_singleton_mul_left_unit u'.isUnit (gen J')
          _ = J'.1 := hgen J'
      subst hJJ
      have hu : u = u' := Units.ext (mul_right_cancel₀ (hgen0 J) h1)
      subst hu; rfl
    · rintro ⟨β, hβ⟩
      have hβB : (β : 𝓞 K) ∈ B := β.2
      let J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B} :=
        ⟨Ideal.span {(β : 𝓞 K)}, by simpa [Ideal.span_singleton_eq_bot] using hβ,
          ⟨⟨β, rfl⟩⟩, (Ideal.span_singleton_le_iff_mem _).2 hβB⟩
      have hass : Associated (gen J) (β : 𝓞 K) :=
        Ideal.span_singleton_eq_span_singleton.1 (hgen J)
      obtain ⟨u, hu⟩ := hass
      refine ⟨⟨J, u⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show (u : 𝓞 K) * gen J = β
      rw [mul_comm]; exact hu
  have hsub : ∑' β : B, g β = ∑' β : {β : B // (β : 𝓞 K) ≠ 0}, g β := by
    refine (tsum_subtype_eq_of_support_subset ?_).symm
    intro β hβ h0
    apply hβ
    simp only [hg]
    have : (β : 𝓞 K) = 0 := h0
    rw [this, Ideal.span_singleton_eq_bot.2 rfl, hG0, mul_zero]
  rw [hsub, ← (Equiv.ofBijective e he).tsum_eq]
  have hfiber : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal ∧ J ≤ B},
      HasSum (fun u : (𝓞 K)ˣ => g (e ⟨J, u⟩)) (G J) := by
    intro J
    have hn : mixedEmbedding.norm (mixedEmbedding K ((gen J : 𝓞 K) : K)) ≠ 0 := by
      rw [mixedEmbedding.norm_eq_norm]
      simpa [Algebra.norm_eq_zero_iff] using hgen0 J
    have h0 := Complex.hasSum_ofReal.2 (hsum _ hn)
    rw [Complex.ofReal_one] at h0
    have h1 := h0.mul_right (G J)
    rw [one_mul] at h1
    have hfun : (fun u : (𝓞 K)ˣ => g (e ⟨J, u⟩)) =
        fun u => (h (u • mixedEmbedding K ((gen J : 𝓞 K) : K)) : ℂ) * G J := by
      funext u
      show (h (mixedEmbedding K ((((u : 𝓞 K) * gen J : 𝓞 K)) : K)) : ℂ) *
          G (Ideal.span {(u : 𝓞 K) * gen J}) = _
      rw [unitSMul_smul, Ideal.span_singleton_mul_left_unit u.isUnit, hgen J]
      push_cast
      rw [map_mul]
    rw [hfun]
    exact h1
  have hsumm : Summable fun p => g (e p) :=
    (Equiv.ofBijective e he).summable_iff.2 (hgsum.subtype _)
  exact ((hsumm.tsum_sigma' (fun J => (hfiber J).summable)).trans
    (tsum_congr fun J => (hfiber J).tsum_eq)).symm
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem finite_support_mul_weight_absNorm_of_bounded_support {K : Type} [Field K] [NumberField K]
    (X : Ideal (𝓞 K) → ℂ) (wt : ℝ → ℂ) (a b : ℝ)
    (hw : ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) (t : ℝ) (ht : 0 < t) :
    (Function.support fun I : Ideal (𝓞 K) => X I * wt (t * (Ideal.absNorm I : ℝ))).Finite := by
  refine (Ideal.finite_setOfPred_absNorm_le (⌊b / t⌋₊)).subset ?_
  intro I hI
  have h1 : wt (t * (Ideal.absNorm I : ℝ)) ≠ 0 := right_ne_zero_of_mul hI
  have h2 := (hw _ h1).2
  show Ideal.absNorm I ≤ ⌊b / t⌋₊
  apply Nat.le_floor
  rw [le_div_iff₀ ht]
  linarith
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private theorem tsum_ideal_eq_sum_classGroup_tsum_mul_isPrincipal {K : Type} [Field K] [NumberField K]
    (b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰)
    (hb : Function.Bijective (fun c => ClassGroup.mk0 (b c)))
    (F : Ideal (𝓞 K) → ℂ) (hF0 : F ⊥ = 0) (hfin : (Function.support F).Finite) :
    ∑' I, F I = ∑ c, ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal},
      F I := by
  have hsub : ∀ c, ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal},
      F I = ∑' I, ({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal}).indicator
        F I :=
    fun c => tsum_subtype {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal} F
  simp_rw [hsub]
  have hsum := hasSum_sum (s := Finset.univ) (L := SummationFilter.unconditional _)
    (f := fun (c : ClassGroup (𝓞 K)) (I : Ideal (𝓞 K)) =>
      ({I : Ideal (𝓞 K) | I ≠ ⊥ ∧ (I * (b c : Ideal (𝓞 K))).IsPrincipal}).indicator F I)
    (fun c _ => (summable_of_finite_support
      (hfin.subset fun I hI h0 => hI (Set.indicator_apply_eq_zero.2 fun _ => h0))).hasSum)
  rw [← hsum.tsum_eq]
  refine tsum_congr fun I => ?_
  by_cases hI : I = ⊥
  · subst hI; simp [hF0]
  · obtain ⟨c, hc, huniq⟩ := _root_.GlobalTheory.existsUnique_isPrincipal_mul_classRep b hb I hI
    rw [Finset.sum_eq_single c]
    · simp [Set.indicator, hI, hc]
    · intro c' _ hc'
      rw [Set.indicator_of_notMem]
      rintro ⟨_, h⟩
      exact hc' (huniq c' h)
    · simp
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (m : Ideal (𝓞 K)) (X : Ideal (𝓞 K) → ℂ) (φ : mixedSpace K → ℂ), m ≠ ⊥ → X ⊥ = 0 → (∀ I J, X (I * J) = X I * X J) → (∀ I, I ≠ ⊥ → I ⊔ m = ⊤ → ‖X I‖ = 1) → (∀ I, I ⊔ m ≠ ⊤ → X I = 0) → (∀ x y, φ (x * y) = φ x * φ y) → (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) → ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} → (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) → (∀ β : 𝓞 K, β ≠ 0 → β - 1 ∈ m → X (Ideal.span {β}) = φ (mixedEmbedding K β)) → ∀ (wt : ℝ → ℂ), ContDiff ℝ ∞ wt → (∃ a b : ℝ, 0 < a ∧ ∀ y, wt y ≠ 0 → a ≤ y ∧ y ≤ b) → ∃ κ : ℂ, ∀ b : ClassGroup (𝓞 K) → (Ideal (𝓞 K))⁰, Function.Bijective (fun c => ClassGroup.mk0 (b c)) → (∀ c, (b c : Ideal (𝓞 K)) ⊔ m = ⊤) → ∀ A : ℕ, ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → ‖∑' I, X I * wt (t * (Ideal.absNorm I : ℝ)) - (κ * ∑ c, (X (b c))⁻¹) / (t : ℂ)‖ ≤ C * t ^ A := by
  intro K _ _ m X φ hm hX0 hXmul hXnorm hXcop hφmul hφhom hφsm hφnorm hXφ wt hwt hwtsupp
  obtain ⟨a, b', ha, hab⟩ := hwtsupp
  obtain ⟨ψ, hψper, hψ⟩ :=
    exists_periodic_mod_ideal_eq_character_div_infinity_type m X φ hXmul hXcop hφmul hφnorm hXφ
  obtain ⟨h, h1, h2, h3, h4⟩ := _root_.GlobalTheory.exists_smooth_homogeneous_hasSum_unit_smul K
  obtain ⟨hf1, hf2⟩ := contDiff_and_hasCompactSupport_mul_weight_mixedNorm h h1 h4 φ hφsm wt hwt a b' ha hab
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.IdealSum.ideal_sum_periodic_dilate K m ψ _ hm hψper hf1 hf2
  refine ⟨κ, fun B hB hBm A => ?_⟩
  set d := Module.finrank ℚ K with hd
  have hd0 : d ≠ 0 := Module.finrank_pos.ne'
  have hwt0 : wt 0 = 0 := by
    by_contra h0
    linarith [(hab 0 h0).1]
  have hBne : ∀ c, (B c : Ideal (𝓞 K)) ≠ ⊥ := fun c => nonZeroDivisors.coe_ne_zero (B c)
  choose Cc hCc using fun c => hκ (B c) (hBne c) (hBm c) (A * d)
  refine ⟨∑ c, max (Cc c) 0, fun t ht ht1 => ?_⟩
  have hN : ∀ c, (1 : ℝ) ≤ (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) := fun c => by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (by simpa [Ideal.absNorm_eq_zero_iff] using hBne c)
  set s : ClassGroup (𝓞 K) → ℝ := fun c =>
    (t / (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ)) ^ ((d : ℝ)⁻¹) with hs
  have hq : ∀ c, 0 < t / (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) :=
    fun c => div_pos ht (by linarith [hN c])
  have hs0 : ∀ c, 0 < s c := fun c => Real.rpow_pos_of_pos (hq c) _
  have hsd : ∀ c, s c ^ d = t / (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) := fun c =>
    Real.rpow_inv_natCast_pow (hq c).le hd0
  have hs1 : ∀ c, s c ≤ 1 := fun c => Real.rpow_le_one (hq c).le
    ((div_le_one (by linarith [hN c])).2 (ht1.trans (hN c))) (by positivity)
  have hXB : ∀ c, X (B c) ≠ 0 := fun c h0 => by
    have h' := hXnorm _ (hBne c) (hBm c)
    rw [h0, norm_zero] at h'
    exact zero_ne_one h'
  have key : ∀ c, ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * (B c : Ideal (𝓞 K))).IsPrincipal},
      X I * wt (t * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)) =
      (X (B c))⁻¹ * ∑' α : (B c : Ideal (𝓞 K)), ψ α *
        ((h (s c • mixedEmbedding K ((α : 𝓞 K) : K)) : ℂ) *
          φ (s c • mixedEmbedding K ((α : 𝓞 K) : K)) *
          wt (mixedEmbedding.norm (s c • mixedEmbedding K ((α : 𝓞 K) : K)))) := by
    intro c
    have hNB : (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) ≠ 0 := by linarith [hN c]
    set G : Ideal (𝓞 K) → ℂ := fun J => (X (B c))⁻¹ * (X J *
      wt (t * (Ideal.absNorm J : ℝ) / (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ))) with hG
    have stepA : ∀ I : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ (I * (B c : Ideal (𝓞 K))).IsPrincipal},
        X I * wt (t * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ)) = G (I * (B c : Ideal (𝓞 K))) := by
      intro I
      simp only [hG, hXmul, map_mul, Nat.cast_mul]
      have e : t * ((Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) *
          (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ)) / (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) =
          t * (Ideal.absNorm (I : Ideal (𝓞 K)) : ℝ) := by field_simp
      rw [e]
      field_simp [hXB c]
    rw [tsum_congr stepA, _root_.GlobalTheory.tsum_isPrincipal_mul_eq _ (hBne c) G]
    have hG0 : G ⊥ = 0 := by simp [hG, hX0]
    have hfin : (Function.support fun β : (B c : Ideal (𝓞 K)) =>
        (h (mixedEmbedding K ((β : 𝓞 K) : K)) : ℂ) * G (Ideal.span {(β : 𝓞 K)})).Finite := by
      obtain ⟨C, hC, -, hCmem⟩ := h4 (a * (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) / t)
        (b' * (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) / t)
        (div_pos (mul_pos ha (by linarith [hN c])) ht)
      refine ((finite_setOf_ringOfIntegers_mixedEmbedding_mem_compact C hC).preimage
        (f := fun β : (B c : Ideal (𝓞 K)) => (β : 𝓞 K)) Subtype.val_injective.injOn).subset ?_
      intro β hβ
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      have hh : h (mixedEmbedding K ((β : 𝓞 K) : K)) ≠ 0 := fun h0 => hβ (by simp [h0])
      have hw : wt (t * (Ideal.absNorm (Ideal.span {(β : 𝓞 K)}) : ℝ) /
          (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ)) ≠ 0 := fun h0 => hβ (by
          show (h (mixedEmbedding K ((β : 𝓞 K) : K)) : ℂ) * G (Ideal.span {(β : 𝓞 K)}) = 0
          simp only [hG]
          rw [h0]
          simp)
      obtain ⟨hl, hu⟩ := hab _ hw
      rw [le_div_iff₀ (by linarith [hN c])] at hl
      rw [div_le_iff₀ (by linarith [hN c])] at hu
      apply hCmem _ hh
      · rw [mixedEmbedding_norm_eq_absNorm_span_singleton, div_le_iff₀ ht]; linarith
      · rw [mixedEmbedding_norm_eq_absNorm_span_singleton, le_div_iff₀ ht]; linarith
    rw [tsum_principal_le_eq_tsum_mul_cutoff_span _ G hG0 h h3 hfin, ← tsum_mul_left]
    refine tsum_congr fun β => ?_
    rw [h2 _ _ (hs0 c), hφhom _ _ (hs0 c), mixedEmbedding.norm_smul, abs_of_pos (hs0 c), hsd c,
      mixedEmbedding_norm_eq_absNorm_span_singleton]
    by_cases hβ : (β : 𝓞 K) = 0
    · simp [hG, hβ, hX0, hwt0]
    · simp only [hG]
      rw [hψ _ hβ]
      ring_nf
  have hfinF := finite_support_mul_weight_absNorm_of_bounded_support X wt a b' hab t ht
  rw [tsum_ideal_eq_sum_classGroup_tsum_mul_isPrincipal B hB _ (by simp [hX0]) hfinF, Finset.sum_congr rfl fun c _ => key c]
  have hmain : (κ * ∑ c, (X (B c))⁻¹) / (t : ℂ) = ∑ c, (X (B c))⁻¹ *
      (κ / (((Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) * s c ^ d : ℝ) : ℂ)) := by
    rw [Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e : (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) *
        (t / (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ)) = t := by
      field_simp [(by linarith [hN c] : (Ideal.absNorm (B c : Ideal (𝓞 K)) : ℝ) ≠ 0)]
    rw [hsd c, e]
    ring
  rw [hmain, ← Finset.sum_sub_distrib]
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [← mul_sub, norm_mul, norm_inv, hXnorm _ (hBne c) (hBm c), inv_one, one_mul]
  have hC' := hCc c (s c) (hs0 c) (hs1 c)
  beta_reduce at hC'
  refine hC'.trans ?_
  have hpow : s c ^ (A * d) ≤ t ^ A := by
    rw [pow_mul', hsd c]
    exact pow_le_pow_left₀ (hq c).le (div_le_self ht.le (hN c)) A
  calc Cc c * s c ^ (A * d) ≤ max (Cc c) 0 * s c ^ (A * d) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (hs0 c).le _)
    _ ≤ max (Cc c) 0 * t ^ A := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
end _root_.GlobalTheory
end GlobalTheory
