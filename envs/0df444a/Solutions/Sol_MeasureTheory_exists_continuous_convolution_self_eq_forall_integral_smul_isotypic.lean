-- Prove2me | solution 1 for MeasureTheory.exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3f58f686-6b6b-5a53-9582-f746c2048014

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic

set_option autoImplicit false

open MeasureTheory
open scoped ComplexConjugate

namespace Ws50CharIdem

theorem eq_of_isMulLeftInvariant_of_isProbabilityMeasure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ' μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] [μ'.IsMulLeftInvariant] [IsProbabilityMeasure μ'] : μ' = μ := by
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace μ' μ
  have hc : Measure.haarScalarFactor μ' μ = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν Set.univ) h
    simp only [Measure.smul_apply, measure_univ] at h1
    rw [ENNReal.smul_def, smul_eq_mul, mul_one] at h1
    exact_mod_cast h1.symm
  rw [h, hc, one_smul]

theorem isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  haveI : IsProbabilityMeasure (μ.map (· * g)) :=
    Measure.isProbabilityMeasure_map (measurable_mul_const g).aemeasurable
  exact eq_of_isMulLeftInvariant_of_isProbabilityMeasure (μ.map (· * g)) μ

theorem isInvInvariant_of_isHaarMeasure_of_isProbabilityMeasure {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] [IsProbabilityMeasure μ] : μ.IsInvInvariant := by
  haveI := isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure μ
  refine ⟨?_⟩
  haveI : IsProbabilityMeasure μ.inv :=
    Measure.isProbabilityMeasure_map measurable_inv.aemeasurable
  exact eq_of_isMulLeftInvariant_of_isProbabilityMeasure μ.inv μ

theorem coeffSpan_stable {K : Type*} [Monoid K] {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) :
    (∀ a ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun κ : K => ρ κ p.1 p.2), ∀ t : K,
        (fun κ => a (κ * t)) ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun κ : K => ρ κ p.1 p.2)) ∧
    (∀ a ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun κ : K => ρ κ p.1 p.2), ∀ t : K,
        (fun κ => a (t * κ)) ∈ Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun κ : K => ρ κ p.1 p.2)) := by
  classical
  set V : Submodule ℂ (K → ℂ) := Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun κ : K => ρ κ p.1 p.2)
    with hVdef
  have hVmem : ∀ i j, (fun κ : K => ρ κ i j) ∈ V := fun i j => Submodule.subset_span ⟨(i, j), rfl⟩
  refine ⟨?_, ?_⟩
  · intro a ha t
    refine Submodule.span_induction (p := fun a _ => (fun κ => a (κ * t)) ∈ V) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨p, rfl⟩
      have : (fun κ => ρ (κ * t) p.1 p.2) = ∑ k, ρ t k p.2 • fun κ : K => ρ κ p.1 k := by
        funext κ
        rw [map_mul, Matrix.mul_apply]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      show (fun κ => ρ (κ * t) p.1 p.2) ∈ V
      rw [this]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hVmem p.1 k)
    · exact V.zero_mem
    · intro a b _ _ ha hb; exact V.add_mem ha hb
    · intro c a _ ha; exact V.smul_mem c ha
  · intro a ha t
    refine Submodule.span_induction (p := fun a _ => (fun κ => a (t * κ)) ∈ V) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨p, rfl⟩
      have : (fun κ => ρ (t * κ) p.1 p.2) = ∑ k, ρ t p.1 k • fun κ : K => ρ κ k p.2 := by
        funext κ
        rw [map_mul, Matrix.mul_apply]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      show (fun κ => ρ (t * κ) p.1 p.2) ∈ V
      rw [this]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hVmem k p.2)
    · exact V.zero_mem
    · intro a b _ _ ha hb; exact V.add_mem ha hb
    · intro c a _ ha; exact V.smul_mem c ha

theorem exists_gram_reproducer {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (V : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ ↥V] (hVcont : ∀ a ∈ V, Continuous a) (κ₀ : K) :
    ∃ e : K → ℂ, Continuous e ∧ (fun κ => conj (e κ)) ∈ V ∧ ∀ a ∈ V, ∫ κ, e κ * a κ ∂μ = a κ₀ := by
  classical
  have hnormsq : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = conj z * z := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

  have hint : ∀ {g : K → ℂ}, Continuous g → Integrable g μ := by
    intro g hg
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun κ => hC κ (Set.mem_univ κ))

  have hL2zero : ∀ {g : K → ℂ}, Continuous g → ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ = 0 → g = 0 := by
    intro g hg h0
    by_contra hne
    obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁, g κ₁ ≠ 0 := Function.ne_iff.1 hne
    have hcont : Continuous fun κ => (‖g κ‖ ^ 2 : ℝ) := (continuous_norm.comp hg).pow 2
    have hnn : 0 ≤ fun κ => (‖g κ‖ ^ 2 : ℝ) := fun κ => sq_nonneg _
    have hintg : Integrable (fun κ => (‖g κ‖ ^ 2 : ℝ)) μ := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact Integrable.mono' (integrable_const C) hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun κ => hC κ (Set.mem_univ κ))
    have hpos : 0 < ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hnn hintg]
      refine (hcont.isOpen_support).measure_pos μ ⟨κ₁, ?_⟩
      rw [Function.mem_support]
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 hκ₁)
    exact absurd h0 hpos.ne'

  obtain ⟨m, bV⟩ : Σ m : ℕ, Module.Basis (Fin m) ℂ ↥V := ⟨_, Module.finBasis ℂ ↥V⟩
  let w : Fin m → K → ℂ := fun k => ((bV k : ↥V) : K → ℂ)
  have hwV : ∀ k, w k ∈ V := fun k => (bV k).2
  have hwC : ∀ k, Continuous (w k) := fun k => hVcont _ (hwV k)
  let G : Matrix (Fin m) (Fin m) ℂ := fun k l => ∫ κ, w k κ * conj (w l κ) ∂μ
  have hGint : ∀ k l, Integrable (fun κ => w k κ * conj (w l κ)) μ := fun k l =>
    hint ((hwC k).mul (Complex.continuous_conj.comp (hwC l)))

  have hquad : ∀ c : Fin m → ℂ, star c ⬝ᵥ G.mulVec c
      = ∫ κ, (((‖∑ l, c l * conj (w l κ)‖ ^ 2 : ℝ)) : ℂ) ∂μ := by
    intro c
    have h1 : ∀ κ, (((‖∑ l, c l * conj (w l κ)‖ ^ 2 : ℝ)) : ℂ)
        = ∑ k, ∑ l, (conj (c k) * c l) * (w k κ * conj (w l κ)) := by
      intro κ
      rw [hnormsq, map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, Complex.conj_conj]
      ring
    simp_rw [h1]
    rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hGint k l).const_mul _]
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finsetSum _ fun l _ => (hGint k l).const_mul _]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_const_mul]
    ring
  have hinj : Function.Injective G.mulVec := by
    intro c₁ c₂ h12
    rw [← sub_eq_zero]
    have hc0 : G.mulVec (c₁ - c₂) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
    have hq : star (c₁ - c₂) ⬝ᵥ G.mulVec (c₁ - c₂) = 0 := by rw [hc0, dotProduct_zero]
    rw [hquad, integral_complex_ofReal, Complex.ofReal_eq_zero] at hq
    obtain ⟨g, hgdef⟩ : ∃ g : K → ℂ, ∀ κ, g κ = ∑ l, (c₁ - c₂) l * conj (w l κ) := ⟨_, fun _ => rfl⟩
    have hgC : Continuous g := by
      have : g = fun κ => ∑ l, (c₁ - c₂) l * conj (w l κ) := funext hgdef
      rw [this]
      exact continuous_finsetSum _ fun l _ => continuous_const.mul (Complex.continuous_conj.comp (hwC l))
    have hq' : ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ = 0 := by
      have : (fun κ => (‖g κ‖ ^ 2 : ℝ)) = fun κ => (‖∑ l, (c₁ - c₂) l * conj (w l κ)‖ ^ 2 : ℝ) :=
        funext fun κ => by rw [hgdef]
      rw [this]; exact hq
    have hg0 := hL2zero hgC hq'

    have hsum : (∑ l, (conj ((c₁ - c₂) l)) • (bV l : ↥V)) = 0 := by
      refine Subtype.ext (funext fun κ => ?_)
      have h0 := congrArg conj ((hgdef κ).symm.trans (congrFun hg0 κ))
      simp only [Pi.zero_apply, map_zero, map_sum, map_mul, Complex.conj_conj] at h0
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0 ⊢
      exact h0
    have hli := Fintype.linearIndependent_iff.1 bV.linearIndependent (fun l => conj ((c₁ - c₂) l)) hsum
    funext l
    have := congrArg conj (hli l)
    simpa using this
  have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)

  let y : Fin m → ℂ := fun k => w k κ₀
  let d : Fin m → ℂ := G⁻¹.mulVec y
  have hGd : G.mulVec d = y := by
    show G.mulVec (G⁻¹.mulVec y) = y
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGdet, Matrix.one_mulVec]
  refine ⟨fun κ => ∑ l, d l * conj (w l κ), ?_, ?_, ?_⟩
  · exact continuous_finsetSum _ fun l _ => continuous_const.mul (Complex.continuous_conj.comp (hwC l))
  · have : (fun κ => conj (∑ l, d l * conj (w l κ))) = ∑ l, conj (d l) • w l := by
      funext κ
      simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hwV l)
  ·
    have hbasis : ∀ k, ∫ κ, (∑ l, d l * conj (w l κ)) * w k κ ∂μ = w k κ₀ := by
      intro k
      have : (fun κ => (∑ l, d l * conj (w l κ)) * w k κ) = fun κ => ∑ l, d l * (w k κ * conj (w l κ)) := by
        funext κ; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; ring
      rw [this, integral_finsetSum _ fun l _ => (hGint k l).const_mul _]
      simp_rw [integral_const_mul]
      have := congrFun hGd k
      simp only [Matrix.mulVec, dotProduct] at this
      refine Eq.trans ?_ this
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    intro a ha

    have hexp : a = ∑ k, bV.repr ⟨a, ha⟩ k • w k := by
      have h := congrArg (fun v : ↥V => (v : K → ℂ)) (bV.sum_repr ⟨a, ha⟩).symm
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
    have hintk : ∀ k, Integrable (fun κ => (∑ l, d l * conj (w l κ)) * w k κ) μ := fun k =>
      hint ((continuous_finsetSum _ fun l _ =>
        continuous_const.mul (Complex.continuous_conj.comp (hwC l))).mul (hwC k))
    rw [hexp]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [integral_finsetSum _ fun k _ => ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have : (fun κ => (∑ l, d l * conj (w l κ)) * (bV.repr ⟨a, ha⟩ k * w k κ))
          = fun κ => bV.repr ⟨a, ha⟩ k * ((∑ l, d l * conj (w l κ)) * w k κ) := by
        funext κ; ring
      rw [this, integral_const_mul, hbasis]
    · have : (fun κ => (∑ l, d l * conj (w l κ)) * (bV.repr ⟨a, ha⟩ k * w k κ))
          = fun κ => bV.repr ⟨a, ha⟩ k * ((∑ l, d l * conj (w l κ)) * w k κ) := by
        funext κ; ring
      rw [this]
      exact (hintk k).const_mul _

theorem conj_invariant_and_inv_eq_conj_of_reproducer {K : Type*} [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (V : Submodule ℂ (K → ℂ))
    (hVright : ∀ a ∈ V, ∀ t : K, (fun κ => a (κ * t)) ∈ V)
    (hVleft : ∀ a ∈ V, ∀ t : K, (fun κ => a (t * κ)) ∈ V)
    (e : K → ℂ) (heC : Continuous e) (heV : (fun κ => conj (e κ)) ∈ V)
    (he : ∀ a ∈ V, ∫ κ, e κ * a κ ∂μ = a 1) :
    (∀ κ κ' : K, e (κ' * κ * κ'⁻¹) = e κ) ∧ (∀ κ : K, e κ⁻¹ = conj (e κ)) := by
  have hnormsq : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = conj z * z := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

  have hint : ∀ {g : K → ℂ}, Continuous g → Integrable g μ := by
    intro g hg
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun κ => hC κ (Set.mem_univ κ))

  have hL2zero : ∀ {g : K → ℂ}, Continuous g → ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ = 0 → g = 0 := by
    intro g hg h0
    by_contra hne
    obtain ⟨κ₁, hκ₁⟩ : ∃ κ₁, g κ₁ ≠ 0 := Function.ne_iff.1 hne
    have hcont : Continuous fun κ => (‖g κ‖ ^ 2 : ℝ) := (continuous_norm.comp hg).pow 2
    have hnn : 0 ≤ fun κ => (‖g κ‖ ^ 2 : ℝ) := fun κ => sq_nonneg _
    have hintg : Integrable (fun κ => (‖g κ‖ ^ 2 : ℝ)) μ := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact Integrable.mono' (integrable_const C) hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun κ => hC κ (Set.mem_univ κ))
    have hpos : 0 < ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hnn hintg]
      refine (hcont.isOpen_support).measure_pos μ ⟨κ₁, ?_⟩
      rw [Function.mem_support]
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 hκ₁)
    exact absurd h0 hpos.ne'
  have hVconj : ∀ a ∈ V, ∀ t : K, (fun κ => a (t * κ * t⁻¹)) ∈ V := fun a ha t =>
    hVleft _ (hVright a ha t⁻¹) t

  have huniq : ∀ e₁ e₂ : K → ℂ, Continuous e₁ → Continuous e₂ →
      (fun κ => conj (e₁ κ)) ∈ V → (fun κ => conj (e₂ κ)) ∈ V →
      (∀ a ∈ V, ∫ κ, e₁ κ * a κ ∂μ = a 1) → (∀ a ∈ V, ∫ κ, e₂ κ * a κ ∂μ = a 1) → e₁ = e₂ := by
    intro e₁ e₂ h1 h2 hV1 hV2 hr1 hr2
    obtain ⟨d, hddef⟩ : ∃ d : K → ℂ, ∀ κ, d κ = e₁ κ - e₂ κ := ⟨_, fun _ => rfl⟩
    have hdC : Continuous d := by
      have : d = fun κ => e₁ κ - e₂ κ := funext hddef
      rw [this]; exact h1.sub h2
    have hdV : (fun κ => conj (d κ)) ∈ V := by
      have : (fun κ => conj (d κ)) = (fun κ => conj (e₁ κ)) - fun κ => conj (e₂ κ) := by
        funext κ; simp only [hddef, map_sub, Pi.sub_apply]
      rw [this]; exact V.sub_mem hV1 hV2
    have hzero : ∫ κ, d κ * conj (d κ) ∂μ = 0 := by
      have ha1 := hr1 _ hdV
      have ha2 := hr2 _ hdV
      have hi1 : Integrable (fun κ => e₁ κ * conj (d κ)) μ :=
        hint (h1.mul (Complex.continuous_conj.comp hdC))
      have hi2 : Integrable (fun κ => e₂ κ * conj (d κ)) μ :=
        hint (h2.mul (Complex.continuous_conj.comp hdC))
      have : (fun κ => d κ * conj (d κ)) = fun κ => e₁ κ * conj (d κ) - e₂ κ * conj (d κ) := by
        funext κ; rw [hddef κ]; ring
      rw [this, integral_sub hi1 hi2, ha1, ha2, sub_self]
    have hsq : ∫ κ, (‖d κ‖ ^ 2 : ℝ) ∂μ = 0 := by
      have : (fun κ => d κ * conj (d κ)) = fun κ => (((‖d κ‖ ^ 2 : ℝ)) : ℂ) := by
        funext κ; rw [hnormsq, mul_comm]
      rw [this, integral_complex_ofReal] at hzero
      exact_mod_cast hzero
    have hd0 := hL2zero hdC hsq
    funext κ
    have hκ := congrFun hd0 κ
    rw [hddef κ, Pi.zero_apply] at hκ
    exact sub_eq_zero.1 hκ
  refine ⟨?_, ?_⟩
  ·
    intro κ κ'
    have key : (fun κ => e (κ' * κ * κ'⁻¹)) = e := by
      refine huniq _ _ (heC.comp ((continuous_const.mul continuous_id).mul continuous_const)) heC ?_ heV ?_ he
      · exact hVconj _ heV κ'
      · intro a ha
        have haV := hVconj a ha κ'⁻¹
        simp only [inv_inv] at haV
        have h1 := he _ haV
        simp only [mul_one, inv_mul_cancel] at h1
        rw [← h1]
        have hsubR := integral_mul_right_eq_self (μ := μ) (fun x => e (κ' * x) * a (x * κ')) κ'⁻¹
        have hsubL := integral_mul_left_eq_self (μ := μ) (fun x => e x * a (κ'⁻¹ * x * κ')) κ'
        have step1 : (fun κ => e (κ' * κ * κ'⁻¹) * a κ) = fun κ => (fun x => e (κ' * x) * a (x * κ')) (κ * κ'⁻¹) := by
          funext κ; simp only [mul_assoc, inv_mul_cancel, mul_one]
        have step2 : (fun x => e (κ' * x) * a (x * κ')) = fun x => (fun y => e y * a (κ'⁻¹ * y * κ')) (κ' * x) := by
          funext x; simp only [← mul_assoc, inv_mul_cancel, one_mul]
        rw [step1, hsubR, step2, hsubL]
    exact congrFun key κ
  ·
    intro s
    have star : ∀ t : K, ∫ κ, e κ * conj (e (κ * t)) ∂μ = conj (e t) := by
      intro t
      have h := he _ (hVright _ heV t)
      simpa only [one_mul] using h
    have h1 : e s⁻¹ = conj (∫ κ, e κ * conj (e (κ * s⁻¹)) ∂μ) := by rw [star, Complex.conj_conj]
    rw [h1, ← integral_conj]
    have h2 : (fun κ => (starRingEnd ℂ) (e κ * conj (e (κ * s⁻¹)))) = fun κ => (fun x => e x * conj (e (x * s))) (κ * s⁻¹) := by
      funext κ
      simp only [map_mul, Complex.conj_conj, inv_mul_cancel_right, mul_comm]
    rw [h2, integral_mul_right_eq_self (μ := μ) (fun x => e x * conj (e (x * s))) s⁻¹, star]

theorem eside {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ (e : K → ℂ) (c : Fin n → Fin n → ℂ), Continuous e ∧ (∀ k : K, e k = ∑ i, ∑ j, c i j * (ρ k⁻¹) i j) ∧
      (∀ k l : K, e (l * k * l⁻¹) = e k) ∧ (∀ k : K, e k⁻¹ = conj (e k)) ∧
      (∀ k : K, ∫ l, e l * e (l⁻¹ * k) ∂μ = e k) ∧
      (∀ i j : Fin n, ∫ k, e k * (ρ k) i j ∂μ = if i = j then 1 else 0) := by
  classical
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_of_isHaarMeasure_of_isProbabilityMeasure μ
  set V : Submodule ℂ (K → ℂ) := Submodule.span ℂ (Set.range fun p : Fin n × Fin n => fun κ : K => ρ κ p.1 p.2)
    with hVdef
  haveI : FiniteDimensional ℂ ↥V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hVcont : ∀ a ∈ V, Continuous a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => Continuous a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨p, rfl⟩
      exact hρ.matrix_elem p.1 p.2
    · exact continuous_const
    · intro a b _ _ ha hb; exact ha.add hb
    · intro c a _ ha; exact ha.const_smul c
  obtain ⟨hVright, hVleft⟩ := coeffSpan_stable ρ
  obtain ⟨e, heC, heV, he⟩ := exists_gram_reproducer μ V hVcont 1
  obtain ⟨hclass, hflat⟩ :=
    conj_invariant_and_inv_eq_conj_of_reproducer μ V hVright hVleft e heC heV he
  have heV' := heV
  rw [hVdef] at heV'
  obtain ⟨c', hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 heV'
  refine ⟨e, fun i j => c' (i, j), heC, ?_, hclass, hflat, ?_, ?_⟩
  · intro k
    have h1 : e k = conj (e k⁻¹) := by rw [hflat, Complex.conj_conj]
    have h2 := congrFun hc' k⁻¹
    rw [h1, ← h2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Fintype.sum_prod_type]
  · intro k
    have haV : (fun l => e (l⁻¹ * k)) ∈ V := by
      have : (fun l => e (l⁻¹ * k)) = fun l => conj (e (k⁻¹ * l)) := by
        funext l
        rw [← hflat, mul_inv_rev, inv_inv]
      rw [this]
      exact hVleft _ heV k⁻¹
    have h := he _ haV
    simpa only [inv_one, one_mul] using h
  · intro i j
    have haV : (fun κ : K => ρ κ i j) ∈ V := Submodule.subset_span ⟨(i, j), rfl⟩
    have h := he _ haV
    rw [h, map_one, Matrix.one_apply]

end Ws50CharIdem

namespace Ws50CharIdem

section generic

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  {n : ℕ}

theorem integrable_of_continuous' (μ : Measure K) [IsFiniteMeasureOnCompacts μ]
    {F : Type*} [NormedAddCommGroup F] (f : K → F) (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_inv_apply (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) (j i : Fin n) :
    Continuous fun k : K => (ρ k⁻¹) j i :=
  (hρ.comp continuous_inv).matrix_elem j i

noncomputable def avgVec (μ : Measure K) (ρ : K →* Matrix (Fin n) (Fin n) ℂ)
    (π : K →* (E →L[ℂ] E)) (w : E) (j i : Fin n) : E :=
  ∫ k, (ρ k⁻¹) j i • π k w ∂μ

noncomputable def avgMap (μ : Measure K) (ρ : K →* Matrix (Fin n) (Fin n) ℂ)
    (π : K →* (E →L[ℂ] E)) (w : E) : (Fin n → Fin n → ℂ) →ₗ[ℂ] E :=
  ∑ j : Fin n, ∑ i : Fin n,
    ((LinearMap.proj i).comp (LinearMap.proj j : (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ))).smulRight
      (avgVec μ ρ π w j i)

theorem avgMap_apply (μ : Measure K) (ρ : K →* Matrix (Fin n) (Fin n) ℂ)
    (π : K →* (E →L[ℂ] E)) (w : E) (x : Fin n → Fin n → ℂ) :
    avgMap μ ρ π w x = ∑ j, ∑ i, x j i • avgVec μ ρ π w j i := by
  simp [avgMap, LinearMap.sum_apply, LinearMap.smulRight_apply]

theorem apply_avgVec (μ : Measure K) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (π : K →* (E →L[ℂ] E)) (w : E) (hπc : Continuous fun k => π k w) (g : K) (j l : Fin n) :
    π g (avgVec μ ρ π w j l) = ∑ i, (ρ g) i l • avgVec μ ρ π w j i := by
  have hcont := continuous_inv_apply ρ hρ
  unfold avgVec

  rw [← ContinuousLinearMap.integral_comp_comm _
    (integrable_of_continuous' μ _ ((hcont j l).fun_smul hπc))]
  have h1 : (fun k => π g ((ρ k⁻¹) j l • π k w)) = fun k => (ρ k⁻¹) j l • π (g * k) w := by
    funext k
    rw [map_smul, map_mul]
    rfl
  rw [h1]

  have h2 : (∫ k, (ρ k⁻¹) j l • π (g * k) w ∂μ) = ∫ k, (ρ (k⁻¹ * g)) j l • π k w ∂μ := by
    have h := integral_mul_left_eq_self (μ := μ) (fun k => (ρ (k⁻¹ * g)) j l • π k w) g
    simp only [mul_inv_rev, inv_mul_cancel_right] at h
    exact h
  rw [h2]

  have h3 : (fun k => (ρ (k⁻¹ * g)) j l • π k w) =
      fun k => ∑ i, (ρ g) i l • ((ρ k⁻¹) j i • π k w) := by
    funext k
    rw [map_mul, Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  rw [h3, integral_finsetSum (f := fun i k => (ρ g) i l • ((ρ k⁻¹) j i • π k w)) _
    (fun i _ => (integrable_of_continuous' μ _ ((hcont j i).smul hπc)).smul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact integral_smul _ _

theorem avgMap_mulVec (μ : Measure K) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]
    (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (π : K →* (E →L[ℂ] E)) (w : E) (hπc : Continuous fun k => π k w) (g : K)
    (x : Fin n → Fin n → ℂ) :
    avgMap μ ρ π w (fun j => (ρ g).mulVec (x j)) = π g (avgMap μ ρ π w x) := by
  rw [avgMap_apply, avgMap_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  simp_rw [map_smul, apply_avgVec μ ρ hρ π w hπc g, Matrix.mulVec, dotProduct, Finset.sum_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

theorem integral_coeff_smul_eq_avgMap (μ : Measure K) [IsFiniteMeasureOnCompacts μ]
    (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (π : K →* (E →L[ℂ] E)) (v : E) (hπc : Continuous fun k => π k v)
    (c : Fin n → Fin n → ℂ) :
    (∫ k, (∑ i, ∑ j, c i j * (ρ k⁻¹) i j) • π k v ∂μ) = avgMap μ ρ π v c := by
  have hcont := continuous_inv_apply ρ hρ
  rw [avgMap_apply]
  simp_rw [Finset.sum_smul]
  rw [integral_finsetSum (f := fun i k => ∑ j, (c i j * (ρ k⁻¹) i j) • π k v) _
    (fun i _ => integrable_finsetSum _
      (fun j _ => integrable_of_continuous' μ _ ((continuous_const.mul (hcont i j)).smul hπc)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum (f := fun j k => (c i j * (ρ k⁻¹) i j) • π k v) _
    (fun j _ => integrable_of_continuous' μ _ ((continuous_const.mul (hcont i j)).smul hπc))]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold avgVec
  rw [← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  simp only [smul_smul]

theorem integral_smul_mulVec_eq_self (μ : Measure K) [IsFiniteMeasureOnCompacts μ]
    (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (e : K → ℂ) (he : Continuous e)
    (horth : ∀ i j, ∫ k, e k * (ρ k) i j ∂μ = if i = j then 1 else 0)
    {m : ℕ} (x : Fin m → (Fin n → ℂ)) :
    (∫ k, e k • (fun i => (ρ k).mulVec (x i)) ∂μ) = x := by
  have hF : Continuous fun k : K => e k • (fun i => (ρ k).mulVec (x i)) :=
    he.smul (continuous_pi fun i => hρ.matrix_mulVec continuous_const)
  have hint := integrable_of_continuous' μ _ hF
  funext i l
  let P : (Fin m → Fin n → ℂ) →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj l : (Fin n → ℂ) →L[ℂ] ℂ).comp
      (ContinuousLinearMap.proj i : (Fin m → Fin n → ℂ) →L[ℂ] (Fin n → ℂ))
  have hP : ∀ y : Fin m → Fin n → ℂ, P y = y i l := fun y => rfl
  calc (∫ k, e k • (fun i => (ρ k).mulVec (x i)) ∂μ) i l
      = P (∫ k, e k • (fun i => (ρ k).mulVec (x i)) ∂μ) := (hP _).symm
    _ = ∫ k, P (e k • (fun i => (ρ k).mulVec (x i))) ∂μ := (P.integral_comp_comm hint).symm
    _ = ∫ k, ∑ j, x i j * (e k * (ρ k) l j) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [hP, Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, x i j * ∫ k, e k * (ρ k) l j ∂μ := by
        rw [integral_finsetSum (f := fun j k => x i j * (e k * (ρ k) l j)) _
          (fun j _ => integrable_of_continuous' μ _
            (continuous_const.mul (he.mul (hρ.matrix_elem l j))))]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact integral_const_mul _ _
    _ = x i l := by
        simp_rw [horth, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp

end generic

section exports

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
  [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
  {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
  (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (π : K →* (H →L[ℂ] H)) (hπi : ∀ (k : K) (v : H), ‖π k v‖ = ‖v‖)
  (hπc : ∀ v : H, Continuous fun k : K => π k v)

include hρ hπc in

theorem exists_equivariant_range (c : Fin n → Fin n → ℂ) (v : H) :
    ∃ T : (Fin n → (Fin n → ℂ)) →L[ℂ] H,
      (∀ (g : K) (x : Fin n → (Fin n → ℂ)), T (fun i => (ρ g).mulVec (x i)) = π g (T x)) ∧
      (∫ k, (∑ i, ∑ j, c i j * (ρ k⁻¹) i j) • π k v ∂μ) ∈
        LinearMap.range (T : (Fin n → (Fin n → ℂ)) →ₗ[ℂ] H) := by
  refine ⟨LinearMap.toContinuousLinearMap (avgMap μ ρ π v), fun g x => ?_, ⟨c, ?_⟩⟩
  · simp only [LinearMap.coe_toContinuousLinearMap']
    exact avgMap_mulVec μ ρ hρ π v (hπc v) g x
  · simp only [ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap']
    exact (integral_coeff_smul_eq_avgMap μ ρ hρ π v (hπc v) c).symm

include hρ in

theorem integral_smul_apply_eq_of_equivariant (e : K → ℂ) (he : Continuous e)
    (horth : ∀ i j, ∫ k, e k * (ρ k) i j ∂μ = if i = j then 1 else 0)
    {m : ℕ} (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H)
    (hT : ∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x))
    (x : Fin m → (Fin n → ℂ)) :
    (∫ k, e k • π k (T x) ∂μ) = T x := by
  have hF : Continuous fun k : K => e k • (fun i => (ρ k).mulVec (x i)) :=
    he.smul (continuous_pi fun i => hρ.matrix_mulVec continuous_const)
  calc (∫ k, e k • π k (T x) ∂μ)
      = ∫ k, T (e k • (fun i => (ρ k).mulVec (x i))) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
        simp only [map_smul, hT]
    _ = T (∫ k, e k • (fun i => (ρ k).mulVec (x i)) ∂μ) :=
        T.integral_comp_comm (integrable_of_continuous' μ _ hF)
    _ = T x := by rw [integral_smul_mulVec_eq_self μ ρ hρ e he horth x]

end exports

theorem hSide_range
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H)) (hiso : ∀ (k : K) (v : H), ‖π k v‖ = ‖v‖)
    (hπc : ∀ v : H, Continuous fun k : K => π k v)
    (c : Fin n → Fin n → ℂ) (v : H) :
    ∃ T : (Fin n → (Fin n → ℂ)) →L[ℂ] H,
      (∀ (k : K) (x : Fin n → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
      (∫ k, (∑ i, ∑ j, c i j * (ρ k⁻¹) i j) • π k v ∂μ) ∈
        LinearMap.range (T : (Fin n → (Fin n → ℂ)) →ₗ[ℂ] H) :=
  exists_equivariant_range μ ρ hρ H π hπc c v

theorem hSide_reproduce
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (π : K →* (H →L[ℂ] H)) (hiso : ∀ (k : K) (v : H), ‖π k v‖ = ‖v‖)
    (hπc : ∀ v : H, Continuous fun k : K => π k v)
    (e : K → ℂ) (he : Continuous e)
    (horth : ∀ i j : Fin n, ∫ k, e k * (ρ k) i j ∂μ = if i = j then 1 else 0)
    {m : ℕ} (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H)
    (hT : ∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x))
    (x : Fin m → (Fin n → ℂ)) :
    ∫ k, e k • π k (T x) ∂μ = T x :=
  integral_smul_apply_eq_of_equivariant μ ρ hρ H π e he horth T hT x

end Ws50CharIdem

theorem solution
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [T2Space K]
    [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsHaarMeasure] [IsProbabilityMeasure μ]
    {n : ℕ} (ρ : K →* Matrix (Fin n) (Fin n) ℂ) (hρ : Continuous ρ) :
    ∃ e : K → ℂ, Continuous e ∧ (∀ k l : K, e (l * k * l⁻¹) = e k) ∧ (∀ k : K, e k⁻¹ = conj (e k)) ∧
      (∀ k : K, ∫ l, e l * e (l⁻¹ * k) ∂μ = e k) ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (π : K →* (H →L[ℂ] H)), (∀ (k : K) (v : H), ‖π k v‖ = ‖v‖) → (∀ v : H, Continuous fun k : K => π k v) →
        ∀ A : H →L[ℂ] H, (∀ v : H, A v = ∫ k, (e k) • (π k v) ∂μ) →
          A.comp A = A ∧
          (∀ v : H, A v = v ↔
            ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) ∧
          (∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
              (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
              A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H)) := by
  obtain ⟨e, c, hcont, hec, hclass, hflat, hconv, horth⟩ := Ws50CharIdem.eside μ ρ hρ
  refine ⟨e, hcont, hclass, hflat, hconv, ?_⟩
  intro H _ _ _ π hiso hπc A hA

  have h5c : ∀ v : H, ∃ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
      (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) ∧
      A v ∈ LinearMap.range (T : (Fin m → (Fin n → ℂ)) →ₗ[ℂ] H) := by
    intro v
    obtain ⟨T, hT, hmem⟩ := Ws50CharIdem.hSide_range μ ρ hρ H π hiso hπc c v
    refine ⟨n, T, hT, ?_⟩
    have hfun : (fun k : K => e k • π k v) = fun k : K => (∑ i, ∑ j, c i j * (ρ k⁻¹) i j) • π k v := by
      funext k
      rw [hec k]
    rw [hA v, hfun]
    exact hmem

  have hfix : ∀ (m : ℕ) (T : (Fin m → (Fin n → ℂ)) →L[ℂ] H),
      (∀ (k : K) (x : Fin m → (Fin n → ℂ)), T (fun i => (ρ k).mulVec (x i)) = π k (T x)) →
      ∀ x : Fin m → (Fin n → ℂ), A (T x) = T x := by
    intro m T hT x
    rw [hA]
    exact Ws50CharIdem.hSide_reproduce μ ρ hρ H π hiso hπc e hcont horth T hT x
  refine ⟨?_, ?_, h5c⟩
  ·
    ext v
    obtain ⟨m, T, hT, hmem⟩ := h5c v
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem
    have hx' : T x = A v := by simpa using hx
    rw [ContinuousLinearMap.coe_comp', Function.comp_apply, ← hx', hfix m T hT x]
  ·
    intro v
    constructor
    · intro hAv
      obtain ⟨m, T, hT, hmem⟩ := h5c v
      rw [hAv] at hmem
      exact ⟨m, T, hT, hmem⟩
    · rintro ⟨m, T, hT, hmem⟩
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hmem
      have hx' : T x = v := by simpa using hx
      rw [← hx', hfix m T hT x]

end S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic
end P2MW
export P2MW.S_MeasureTheory_exists_continuous_convolution_self_eq_forall_integral_smul_isotypic (solution)
