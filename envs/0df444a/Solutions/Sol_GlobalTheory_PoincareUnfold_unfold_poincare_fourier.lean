-- Prove2me | solution 1 for GlobalTheory.PoincareUnfold.unfold_poincare_fourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:27:10.166235+00:00
-- url     : https://prove2.me/submissions/8756301e-39dc-4be0-b0ab-4f9256539f04

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnfoldPoincareSeriesLatticeFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.PoincareUnfold
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]
open MeasureTheory in
open scoped Pointwise in
private lemma setIntegral_exp_linear_fundamentalDomain_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [VAddInvariantMeasure L V μ] [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D μ)
    (hDm : MeasurableSet D) (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (hint : ∀ y ∈ L, ∃ z : ℤ, φ y = z) :
    ∫ v in D, Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) ∂μ = 0 := by
  set f : V → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) with hf
  have hper : ∀ (g : L) (v : V), f (g +ᵥ v) = f v := by
    intro g v
    obtain ⟨z, hz⟩ := hint g g.2
    have hgv : (g +ᵥ v : V) = (g : V) + v := rfl
    simp only [hf, hgv, map_add, hz]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I z]; ring_nf
    rw [this, one_mul]
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  set w : V := (1 / (2 * φ u)) • u with hw
  have hφw : φ w = 1 / 2 := by
    rw [hw, map_smul, smul_eq_mul]; field_simp
  have hshift : ∀ v, f (w + v) = -f v := by
    intro v
    simp only [hf, map_add, hφw]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    rw [this, neg_one_mul]
  have hD' : IsAddFundamentalDomain L (w +ᵥ D) μ := hD.vadd_of_comm w
  have h1 : ∫ v in D, f v ∂μ = ∫ v in w +ᵥ D, f v ∂μ := hD.setIntegral_eq hD' hper
  have h2 : ∫ v in w +ᵥ D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := by
    rw [← integral_indicator (hDm.const_vadd w), ← integral_indicator hDm]
    · rw [← integral_add_left_eq_self (μ := μ) _ w]
      congr 1
      ext v
      by_cases hv : v ∈ D
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show w + v ∈ w +ᵥ D from Set.vadd_mem_vadd_set hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
        rwa [← vadd_eq_add, Set.vadd_mem_vadd_set_iff]

  have h3 : ∫ v in D, f v ∂μ = -∫ v in D, f v ∂μ := by
    calc ∫ v in D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := h1.trans h2
      _ = ∫ v in D, -f v ∂μ := setIntegral_congr_fun hDm fun v _ => hshift v
      _ = -∫ v in D, f v ∂μ := integral_neg _
  have h4 : (2 : ℂ) * ∫ v in D, f v ∂μ = 0 := by
    rw [two_mul]; nth_rewrite 2 [h3]; ring
  simpa using h4
end GlobalTheory.PoincareUnfold
end

set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.PoincareUnfold
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]
open MeasureTheory
open scoped Pointwise
namespace GlobalTheory.PoincareUnfold
namespace _root_.GlobalTheory.PoincareUnfold
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ,
    (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ →
    ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) →
    (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) →
    ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) →
    l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) →
    (∀ v, ∑' x, Q x * F (j x + v) =
      ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) →
    ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  intro V _ _ _ _ _ μ _ Γ _ j hj C hfin hspan n t Q hQsupp ht hQper F hF a l ha hl0 hl hint H
  classical
  set L : Submodule ℤ V := (C.map j).toIntSubmodule with hLdef
  have hmemL : ∀ y, y ∈ L ↔ ∃ c ∈ C, j c = y := fun y => by
    exact AddSubgroup.mem_map
  have hLset : (L : Set V) = j '' (C : Set Γ) := by
    ext y; simp only [SetLike.mem_coe, hmemL, Set.mem_image]
  have hj0 : ∀ c, j c = 0 ↔ c = 0 := fun c => ⟨fun h => hj (by rw [h, map_zero]), fun h => by
    rw [h, map_zero]⟩
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    set T : Finset ℝ := insert 1 (((hfin 1).toFinset.filter (· ≠ 0)).image fun c => ‖j c‖)
    have hTne : T.Nonempty := Finset.insert_nonempty _ _
    refine ⟨T.min' hTne, ?_, ?_⟩
    · show 0 < T.min' hTne
      rw [Finset.lt_min'_iff]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨c, hc, rfl⟩
      · exact one_pos
      · rw [Finset.mem_filter] at hc
        exact norm_pos_iff.2 fun h => hc.2 ((hj0 c).1 h)
    · rintro ⟨y, hy⟩ hdist
      obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
      have hlt : ‖j c‖ < T.min' hTne := by simpa [dist_eq_norm] using hdist
      have hle1 : T.min' hTne ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      by_cases hc0 : c = 0
      · ext; simp [hc0]
      · exfalso
        have hmem : ‖j c‖ ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.2
          ⟨c, Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨hc, by linarith⟩, hc0⟩, rfl⟩)
        exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hspan⟩
  haveI : VAddInvariantMeasure L V μ := ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  set ψ : C → L := fun c => ⟨j c, (hmemL _).2 ⟨c, c.2, rfl⟩⟩ with hψ
  have hψinj : Function.Injective ψ := fun c c' h => Subtype.ext (hj (congrArg Subtype.val h))
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨c, hc, hcy⟩ := (hmemL y).1 y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  haveI : Countable L := (Module.Free.chooseBasis ℤ L).repr.injective.countable
  haveI : Countable C := hψinj.countable
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) with hDdef
  have hD : IsAddFundamentalDomain L D μ := ZLattice.isAddFundamentalDomain _ μ
  have hDfin : μ D < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  refine ⟨ZLattice.covolume L μ, ZLattice.covolume_pos L μ, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hD]
  have hR : ∫ v in D, (∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) ∂μ =
      ((μ.real D : ℝ) : ℂ) * a 0 := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set E : Γ → V → ℂ := fun x v => Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ)) with hE
    have hEnorm : ∀ x v, ‖E x v‖ₑ = 1 := by
      intro x v
      rw [← ofReal_norm_eq_enorm]
      simp only [hE]
      rw [show (2 * Real.pi * Complex.I * ((l x v : ℝ) : ℂ)) = ((2 * Real.pi * l x v : ℝ) : ℂ) *
        Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    have hEcont : ∀ x, Continuous (E x) := fun x => by
      simp only [hE]
      fun_prop
    set s := Function.support a with hs
    have hscount : s.Countable := ha.of_norm.countable_support
    haveI : Countable s := hscount.to_subtype
    have hsub : ∀ v, ∑' x, a x * E x v = ∑' x : s, a x * E x v := fun v =>
      (tsum_subtype_eq_of_support_subset fun x hx => by
        simp only [Function.mem_support] at hx ⊢
        intro h; exact hx (by rw [h, zero_mul])).symm
    have hchar : ∀ x, ∫ v in D, a x * E x v ∂μ =
        if x = 0 then ((μ.real D : ℝ) : ℂ) * a 0 else 0 := by
      intro x
      rw [integral_const_mul]
      split_ifs with hx
      · subst hx
        simp only [hE, hl0, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          setIntegral_const, Complex.real_smul, mul_one]
        ring
      · by_cases hax : a x = 0
        · rw [hax, zero_mul]
        · rw [setIntegral_exp_linear_fundamentalDomain_eq_zero μ L hD hDm (l x) (hl x hx)
            (fun y hy => by
              obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
              exact hint x hax c hc), mul_zero]
    show ∫ v in D, (∑' x, a x * E x v) ∂μ = _
    simp_rw [hsub]
    rw [integral_tsum]
    · rw [tsum_subtype_eq_of_support_subset (f := fun x => ∫ v in D, a x * E x v ∂μ)]
      · simp_rw [hchar]
        exact tsum_ite_eq 0 _
      · intro x hx
        rw [Function.mem_support, hchar] at hx
        split_ifs at hx with h0
        · subst h0
          intro h; exact hx (by rw [h, mul_zero])
        · exact absurd rfl hx
    · intro x
      exact ((hEcont x).const_mul (a x) |>.aestronglyMeasurable)
    · simp_rw [enorm_mul, hEnorm, mul_one, lintegral_const, Measure.restrict_apply_univ]
      rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ hDfin.ne
      simp_rw [enorm_eq_nnnorm]
      refine ENNReal.tsum_coe_ne_top_iff_summable.2 ?_
      rw [← NNReal.summable_coe]
      exact ha.subtype s
  have hLHS : ∫ v in D, (∑' x, Q x * F (j x + v)) ∂μ = (∑ k, Q (t k)) * ∫ v, F v ∂μ := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set e : Fin n × C → Γ := fun p => t p.1 + p.2 with he
    have heinj : Function.Injective e := by
      rintro ⟨k, c⟩ ⟨k', c'⟩ h
      simp only [he] at h
      have hk : k = k' := ht k k' (by
        rw [show t k - t k' = c' - c by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]]
        exact C.sub_mem c'.2 c.2)
      subst hk
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    have hsupp : ∀ v, Function.support (fun x => Q x * F (j x + v)) ⊆ Set.range e := by
      intro v x hx
      have hQx : Q x ≠ 0 := fun h => hx (by simp [h])
      obtain ⟨k, hk⟩ := hQsupp x hQx
      exact ⟨(k, ⟨x - t k, hk⟩), by simp [he]⟩
    set g : Fin n × C → V → ℂ := fun p v => Q (t p.1) * F (j (t p.1) + (j p.2 + v)) with hg
    have hrw : ∀ v, ∑' x, Q x * F (j x + v) = ∑' p, g p v := by
      intro v
      rw [← heinj.tsum_eq (hsupp v)]
      refine tsum_congr fun p => ?_
      simp only [he, hg, map_add, hQper _ _ p.2.2, add_assoc]
    have hunf : ∀ G : V → ℂ, Integrable G μ → ∫ v, G v ∂μ = ∑' c : C, ∫ v in D, G (j c + v) ∂μ := by
      intro G hG
      rw [hD.integral_eq_tsum' G hG,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hunfl : ∀ G : V → ENNReal, ∫⁻ v, G v ∂μ = ∑' c : C, ∫⁻ v in D, G (j c + v) ∂μ := by
      intro G
      rw [hD.lintegral_eq_tsum' G,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hfinite : ∑' p, ∫⁻ v in D, ‖g p v‖ₑ ∂μ ≠ ⊤ := by
      simp_rw [hg, enorm_mul]
      simp_rw [lintegral_const_mul' _ _ enorm_ne_top]
      rw [ENNReal.tsum_prod (f := fun k (c : C) =>
        ‖Q (t k)‖ₑ * ∫⁻ v in D, ‖F (j (t k) + (j c + v))‖ₑ ∂μ), tsum_fintype]
      refine (ENNReal.sum_lt_top.2 fun k _ => ?_).ne
      rw [ENNReal.tsum_mul_left, ← hunfl (fun v => ‖F (j (t k) + v)‖ₑ)]
      exact ENNReal.mul_lt_top enorm_lt_top (hF.comp_add_left (j (t k))).hasFiniteIntegral
    have hmeas : ∀ p, AEStronglyMeasurable (g p) (μ.restrict D) := fun p =>
      (((hF.comp_add_left (j (t p.1))).comp_add_left (j p.2)).aestronglyMeasurable.const_mul
        _).restrict
    have hsumm : Summable (fun p => ∫ v in D, g p v ∂μ) := by
      refine Summable.of_norm_bounded (ENNReal.summable_toReal hfinite) fun p => ?_
      refine (norm_integral_le_lintegral_norm _).trans_eq ?_
      simp_rw [ofReal_norm_eq_enorm]
    simp_rw [hrw]
    rw [integral_tsum hmeas hfinite, hsumm.tsum_prod, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, integral_const_mul]
    rw [tsum_mul_left, ← hunf _ (hF.comp_add_left (j (t k))), integral_add_left_eq_self]
  rw [← hLHS, ← hR]
  exact setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun v _ => H v
end _root_.GlobalTheory.PoincareUnfold
end GlobalTheory.PoincareUnfold
