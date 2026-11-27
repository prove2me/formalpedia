-- Prove2me | solution 1 for GlobalTheory.exists_summation_kernel_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:37:49.828729+00:00
-- url     : https://prove2.me/submissions/21eee7b5-d5f3-4809-a14b-b53d73fc8de5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDescendPeriodicTrig
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierCoeffMulCharConvAndHasDerivAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SetIntegralPosOfPeriodicNonneg
import Theorems.Thm_GlobalTheory_fourierCoeff_mul_char_conv_and_hasDerivAt
import Theorems.Thm_GlobalTheory_measure_addFundamentalDomain_lt_top_of_cocompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
namespace GlobalTheory
open MeasureTheory in
open scoped Pointwise in
private lemma compactSpace_quotient_of_cocompact {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K)
    (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K) : CompactSpace (G ⧸ Γ) := by
  refine ⟨?_⟩
  have : (QuotientAddGroup.mk '' K : Set (G ⧸ Γ)) = Set.univ := by
    refine Set.eq_univ_of_forall fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨γ, hγ, hx⟩ := hcov x
      refine ⟨γ + x, hx, ?_⟩
      rw [QuotientAddGroup.eq]; simpa using hγ
  rw [← this]
  exact hK.image continuous_quotient_mk'
open MeasureTheory in
open scoped Pointwise in
private lemma exists_continuous_descend_of_periodic {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (Γ : AddSubgroup G) {Φ : G → ℂ} (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    ∃ Ψ : C(G ⧸ Γ, ℂ), ∀ x : G, Ψ (x : G ⧸ Γ) = Φ x := by
  have h : ∀ x y : G, (QuotientAddGroup.leftRel Γ) x y → Φ x = Φ y := by
    intro x y hxy
    rw [QuotientAddGroup.leftRel_apply] at hxy
    rw [← hper _ hxy x]; congr 1; abel
  exact ⟨⟨Quotient.lift Φ h, hΦ.quotient_lift h⟩, fun x => rfl⟩
open MeasureTheory in
open scoped Pointwise in
private lemma eventually_norm_translate_sub_le {Q : Type} [AddCommGroup Q] [TopologicalSpace Q]
    [IsTopologicalAddGroup Q] [CompactSpace Q] (f : C(Q, ℂ)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ w in nhds (0 : Q), ∀ q, ‖f (q + w) - f q‖ ≤ η := by
  let F : C(Q × Q, ℂ) := ⟨fun p => f (p.2 + p.1), by fun_prop⟩
  have hc : Continuous F.curry := F.curry.continuous
  have ht := (hc.tendsto 0)
  rw [Metric.tendsto_nhds] at ht
  filter_upwards [ht η hη] with w hw q
  have h := ContinuousMap.dist_apply_le_dist (f := F.curry w) (g := F.curry 0) q
  have e1 : F.curry w q = f (q + w) := rfl
  have e2 : F.curry 0 q = f q := by simp [F]
  rw [e1, e2, dist_eq_norm] at h
  exact h.trans hw.le
open MeasureTheory in
open scoped Pointwise in
private lemma exists_norm_le_of_periodic {G : Type} [AddCommGroup G] [TopologicalSpace G]
    (Γ : AddSubgroup G) {K : Set G} (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {Φ : G → ℂ} (hΦ : Continuous Φ) (hper : ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) :
    ∃ M, ∀ x, ‖Φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hK.image hΦ.norm).bddAbove
  refine ⟨M, fun x => ?_⟩
  obtain ⟨γ, hγ, hx⟩ := hcov x
  rw [← hper γ hγ x]
  exact hM ⟨_, hx, rfl⟩
open MeasureTheory in
open scoped Pointwise in
private lemma exists_charSum_approx {Q : Type} [TopologicalSpace Q] [CompactSpace Q] {A : Type}
    [AddCommGroup A] (ψ : A → C(Q, ℂ)) (hmul : ∀ a b, ψ (a + b) = ψ a * ψ b) (h0 : ψ 0 = 1)
    (hstar : ∀ a, star (ψ a) = ψ (-a)) (hsep : ∀ p q : Q, p ≠ q → ∃ a, ψ a p ≠ ψ a q)
    (f : C(Q, ℂ)) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (s : Finset A) (d : A → ℂ), ∀ q, ‖f q - ∑ a ∈ s, d a * ψ a q‖ ≤ δ := by
  classical
  set V := Submodule.span ℂ (Set.range ψ) with hV
  have hVV : V * V ≤ V := by
    rw [hV, Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
    exact Submodule.subset_span ⟨a + b, hmul a b⟩
  have hone : (1 : C(Q, ℂ)) ∈ V := h0 ▸ Submodule.subset_span ⟨0, rfl⟩
  have hst : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      rw [hstar]; exact Submodule.subset_span ⟨-a, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(Q, ℂ) :=
    { carrier := V
      mul_mem' := fun hp hq => hVV (Submodule.mul_mem_mul hp hq)
      one_mem' := hone
      add_mem' := fun hp hq => V.add_mem hp hq
      zero_mem' := V.zero_mem
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]; exact V.smul_mem r hone
      star_mem' := fun hp => hst _ hp }
  have hS : S.SeparatesPoints := by
    intro p q hpq
    obtain ⟨a, ha⟩ := hsep p q hpq
    exact ⟨ψ a, ⟨ψ a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints S hS
  have hf : f ∈ closure (S : Set C(Q, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, htop]; trivial
  obtain ⟨g, hgS, hfg⟩ := Metric.mem_closure_iff.mp hf δ hδ
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp (show g ∈ V from hgS)
  refine ⟨c.support, c, fun q => ?_⟩
  have hgq : g q = ∑ a ∈ c.support, c a * ψ a q := by
    rw [← hc, Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply]
    rfl
  rw [← hgq]
  calc ‖f q - g q‖ = ‖(f - g) q‖ := rfl
    _ ≤ ‖f - g‖ := (f - g).norm_coe_le_norm q
    _ ≤ δ := by rw [← dist_eq_norm]; exact hfg.le
end GlobalTheory
end

set_option autoImplicit false
open MeasureTheory
open GlobalTheory
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → ∀ l : List (G → ℂ), (∀ Φ ∈ l, Continuous Φ ∧ ∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → ∀ ε : ℝ, 0 < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ Φ ∈ l, ∀ x, ‖Φ x - ∑ a ∈ s, c a * ((∫ y in 𝓕, Φ y * starRingEnd ℂ (χ a y) ∂μ) * χ a x)‖ ≤ ε := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ χ hχc hχmul hχadd hχ0 hχnorm hχΓ μ 𝓕 hμ h𝓕 l hl ε hε
  classical
  haveI : Countable Γ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  haveI : IsClosed (Γ : Set G) := AddSubgroup.isClosed_of_discrete
  haveI : CompactSpace (G ⧸ Γ) := compactSpace_quotient_of_cocompact Γ hK hcov
  have hχz : ∀ a, χ a 0 = 1 := by
    intro a
    have h := hχmul a 0 0
    rw [add_zero] at h
    have hne : χ a 0 ≠ 0 := by
      intro h0; have := hχnorm a 0; rw [h0, norm_zero] at this; exact zero_ne_one this
    exact (mul_right_eq_self₀.mp h.symm).resolve_right hne
  have hχper : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := by
    intro a γ hγ x; rw [hχmul, (hχΓ γ).mpr hγ a, one_mul]
  choose ψ hψ using fun a => exists_continuous_descend_of_periodic Γ (hχc a) (hχper a)
  have hcc : ∀ a x, starRingEnd ℂ (χ a x) = χ (-a) x := by
    intro a x
    have h1 : χ a x * χ (-a) x = 1 := by rw [← hχadd, add_neg_cancel, hχ0]
    have h2 : starRingEnd ℂ (χ a x) * χ a x = 1 := by
      rw [Complex.conj_mul', hχnorm]; simp
    calc starRingEnd ℂ (χ a x) = starRingEnd ℂ (χ a x) * (χ a x * χ (-a) x) := by
          rw [h1, _root_.mul_one]
      _ = χ (-a) x := by rw [← _root_.mul_assoc, h2, _root_.one_mul]
  have hψmul : ∀ a b, ψ (a + b) = ψ a * ψ b := by
    intro a b; ext q
    induction q using QuotientAddGroup.induction_on with
    | H x => simp [hψ, hχadd]
  have hψ0 : ψ 0 = 1 := by
    ext q
    induction q using QuotientAddGroup.induction_on with
    | H x => simp [hψ, hχ0]
  have hψstar : ∀ a, star (ψ a) = ψ (-a) := by
    intro a; ext q
    induction q using QuotientAddGroup.induction_on with
    | H x => simp [hψ, ← hcc]
  have hψsep : ∀ p q : G ⧸ Γ, p ≠ q → ∃ a, ψ a p ≠ ψ a q := by
    intro p q hpq
    induction p using QuotientAddGroup.induction_on with
    | H x =>
    induction q using QuotientAddGroup.induction_on with
    | H y =>
    by_contra hcon
    push_neg at hcon
    apply hpq
    rw [QuotientAddGroup.eq]
    apply (hχΓ (-x + y)).mp
    intro a
    have e := hcon a
    rw [hψ, hψ] at e
    rw [hχmul, ← e, ← hχmul, neg_add_cancel, hχz]
  have hη : (0 : ℝ) < ε / 2 := by positivity
  have hev : ∀ Φ ∈ l.toFinset, ∀ᶠ w in nhds (0 : G ⧸ Γ), ∀ x y : G, (y : G ⧸ Γ) = w →
      ‖Φ (x + y) - Φ x‖ ≤ ε / 2 := by
    intro Φ hΦ
    rw [List.mem_toFinset] at hΦ
    obtain ⟨Ψ, hΨ⟩ := exists_continuous_descend_of_periodic Γ (hl Φ hΦ).1 (hl Φ hΦ).2
    filter_upwards [eventually_norm_translate_sub_le Ψ hη] with w hw x y hy
    have := hw (x : G ⧸ Γ)
    rwa [← hy, ← QuotientAddGroup.mk_add, hΨ, hΨ] at this
  obtain ⟨U, hU, hUprop⟩ := ((Filter.eventually_all_finset l.toFinset).2 hev).exists_mem
  obtain ⟨O, hOU, hOopen, h0O⟩ := mem_nhds_iff.mp hU
  obtain ⟨b, hb0, hb1, hb01⟩ := exists_continuous_zero_one_of_isClosed hOopen.isClosed_compl
    (isClosed_singleton (x := (0 : G ⧸ Γ)))
    (Set.disjoint_singleton_right.mpr (by simpa using h0O))
  have hMev : ∀ Φ ∈ l.toFinset, ∀ᶠ M in Filter.atTop, ∀ x, ‖Φ x‖ ≤ M := by
    intro Φ hΦ
    rw [List.mem_toFinset] at hΦ
    obtain ⟨M, hM⟩ := exists_norm_le_of_periodic Γ hK hcov (hl Φ hΦ).1 (hl Φ hΦ).2
    exact Filter.eventually_atTop.2 ⟨M, fun M' hM' x => (hM x).trans hM'⟩
  obtain ⟨M, hM⟩ := ((Filter.eventually_all_finset l.toFinset).2 hMev).exists
  have hfin : μ 𝓕 < ⊤ := _root_.GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact Γ hK hcov μ h𝓕
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.mpr hfin.ne
  set β : G → ℝ := fun y => b (y : G ⧸ Γ) with hβ
  have hβc : Continuous β := b.continuous.comp continuous_quotient_mk'
  have hβ0 : ∀ y, 0 ≤ β y := fun y => (hb01 _).1
  have hβ1 : ∀ y, β y ≤ 1 := fun y => (hb01 _).2
  have hβU : ∀ y, β y ≠ 0 → (y : G ⧸ Γ) ∈ U := by
    intro y hy
    by_contra hyU
    exact hy (hb0 (fun h => hyU (hOU h)))
  set I := ∫ y in 𝓕, β y ∂μ with hIdef
  have hβper : ∀ γ ∈ Γ, ∀ y, β (γ + y) = β y := by
    intro γ hγ y
    simp only [hβ]
    congr 1
    rw [QuotientAddGroup.eq]
    convert Γ.neg_mem hγ using 1
    abel
  have hβint : IntegrableOn β 𝓕 μ := Integrable.of_bound hβc.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hβ0 y)]; exact hβ1 y)
  have hI : 0 < I := by
    rw [hIdef, setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hβ0) hβint]
    rw [pos_iff_ne_zero]
    intro h0
    have hinv : ∀ g : Γ, g +ᵥ Function.support β = Function.support β := by
      intro g
      ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      simp only [Function.mem_support]
      rw [show (-g) +ᵥ y = ((-g : Γ) : G) + y from rfl, hβper _ (-g).2 y]
    have hzero := h𝓕.measure_zero_of_invariant _ hinv h0
    have hβ00 : β 0 ≠ 0 := by
      simp only [hβ, QuotientAddGroup.mk_zero]
      rw [hb1 (Set.mem_singleton 0)]
      simp
    have hpos := (isOpen_ne_fun hβc continuous_const).measure_pos μ ⟨0, hβ00⟩
    exact hpos.ne' hzero
  set m := (μ 𝓕).toReal with hm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set δ := ε / (2 * (|M| + 1) * (m + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  let f : C(G ⧸ Γ, ℂ) := ⟨fun q => ((b q / I : ℝ) : ℂ), by fun_prop⟩
  obtain ⟨s, d, hsd⟩ := exists_charSum_approx ψ hψmul hψ0 hψstar hψsep f δ hδ
  refine ⟨s, fun a => starRingEnd ℂ (d a), fun Φ hΦ x => ?_⟩
  obtain ⟨hΦc, hΦp⟩ := hl Φ hΦ
  have hMΦ : ∀ y, ‖Φ y‖ ≤ M := hM Φ (List.mem_toFinset.mpr hΦ)
  have hconv : ∀ a, (∫ y in 𝓕, Φ y * starRingEnd ℂ (χ a y) ∂μ) * χ a x =
      ∫ y in 𝓕, Φ (x + y) * starRingEnd ℂ (χ a y) ∂μ := fun a =>
    (_root_.GlobalTheory.fourierCoeff_mul_char_conv_and_hasDerivAt G Γ K hK hcov μ 𝓕 hμ h𝓕 (χ a) (hχc a) (hχmul a)
      (hχnorm a) (fun γ hγ => (hχΓ γ).mpr hγ a) Φ hΦc hΦp).1 x
  set k : G → ℂ := fun y => ∑ a ∈ s, d a * χ a y with hkdef
  have hkc : Continuous k := by fun_prop
  have hk : ∀ y, ‖((β y / I : ℝ) : ℂ) - k y‖ ≤ δ := by
    intro y
    have := hsd (y : G ⧸ Γ)
    simpa [f, k, hψ, hβ] using this
  have hkb : ∀ y, ‖k y‖ ≤ ∑ a ∈ s, ‖d a‖ := by
    intro y
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_mul, hχnorm, _root_.mul_one]
  have hsum : ∑ a ∈ s, starRingEnd ℂ (d a) * ((∫ y in 𝓕, Φ y * starRingEnd ℂ (χ a y) ∂μ) * χ a x)
      = ∫ y in 𝓕, Φ (x + y) * starRingEnd ℂ (k y) ∂μ := by
    simp_rw [hconv, ← integral_const_mul]
    rw [← integral_finset_sum]
    · congr 1
      funext y
      simp only [hkdef, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    · intro a _
      exact Integrable.of_bound (by fun_prop) (‖starRingEnd ℂ (d a)‖ * M)
        (Filter.Eventually.of_forall fun y => by
          simp only [norm_mul, Complex.norm_conj, hχnorm, _root_.mul_one]
          exact mul_le_mul_of_nonneg_left (hMΦ _) (norm_nonneg _))
  rw [hsum]
  have hIone : ∫ y in 𝓕, Φ x * ((β y / I : ℝ) : ℂ) ∂μ = Φ x := by
    rw [integral_const_mul, integral_complex_ofReal, integral_div, ← hIdef, div_self hI.ne']
    simp
  have hint1 : Integrable (fun y => Φ x * ((β y / I : ℝ) : ℂ)) (μ.restrict 𝓕) :=
    Integrable.of_bound (by fun_prop) (M * (1 / I)) (Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hβ0 y) hI.le)]
      exact mul_le_mul (hMΦ x) (div_le_div_of_nonneg_right (hβ1 y) hI.le)
        (div_nonneg (hβ0 y) hI.le) ((norm_nonneg _).trans (hMΦ x)))
  have hint2 : Integrable (fun y => Φ (x + y) * starRingEnd ℂ (k y)) (μ.restrict 𝓕) :=
    Integrable.of_bound (by fun_prop) (M * ∑ a ∈ s, ‖d a‖) (Filter.Eventually.of_forall fun y => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (hMΦ _) (hkb y) (norm_nonneg _) ((norm_nonneg _).trans (hMΦ x)))
  have hgint : Integrable (fun y => ε / 2 * (β y / I) + M * δ) (μ.restrict 𝓕) :=
    ((hβint.div_const I).const_mul _).add (integrable_const _)
  calc ‖Φ x - ∫ y in 𝓕, Φ (x + y) * starRingEnd ℂ (k y) ∂μ‖
      = ‖∫ y in 𝓕, (Φ x * ((β y / I : ℝ) : ℂ) - Φ (x + y) * starRingEnd ℂ (k y)) ∂μ‖ := by
        rw [integral_sub hint1 hint2, hIone]
    _ ≤ ∫ y in 𝓕, (ε / 2 * (β y / I) + M * δ) ∂μ := by
        refine norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall fun y => ?_)
        have e : Φ x * ((β y / I : ℝ) : ℂ) - Φ (x + y) * starRingEnd ℂ (k y) =
            (Φ x - Φ (x + y)) * ((β y / I : ℝ) : ℂ) +
              Φ (x + y) * starRingEnd ℂ (((β y / I : ℝ) : ℂ) - k y) := by
          simp only [map_sub, Complex.conj_ofReal]; ring
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hβ0 y) hI.le)]
          by_cases hy : β y = 0
          · simp [hy]
          · refine mul_le_mul_of_nonneg_right ?_ (div_nonneg (hβ0 y) hI.le)
            rw [norm_sub_rev]
            exact hUprop _ (hβU y hy) Φ (List.mem_toFinset.mpr hΦ) x y rfl
        · rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul (hMΦ _) (hk y) (norm_nonneg _) ((norm_nonneg _).trans (hMΦ x))
    _ = ε / 2 + M * δ * m := by
        rw [integral_add ((hβint.div_const I).const_mul _) (integrable_const _), integral_const_mul,
          integral_div, ← hIdef, div_self hI.ne', setIntegral_const]
        simp [hm, smul_eq_mul, Measure.real]
        ring
    _ ≤ ε := by
        have h1 : M * δ * m ≤ ε / 2 := by
          have hMle : M ≤ |M| + 1 := (le_abs_self M).trans (by linarith)
          have hmle : m ≤ m + 1 := by linarith
          calc M * δ * m ≤ (|M| + 1) * δ * (m + 1) := by
                rcases le_or_gt 0 M with hM0 | hM0
                · exact mul_le_mul (mul_le_mul_of_nonneg_right hMle hδ.le) hmle hm0 (by positivity)
                · have : M * δ * m ≤ 0 := by
                    have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hM0.le hδ.le) hm0
                    exact this
                  exact this.trans (by positivity)
            _ = ε / 2 := by
                rw [hδdef]; field_simp
        linarith
end _root_.GlobalTheory
end GlobalTheory
