-- Prove2me | solution 1 for KernelDRO.Duality.theorem_3_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T03:49:04.368172+00:00
-- url     : https://prove2.me/submissions/801404d8-4ab3-484a-8553-1d013e20c547

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_erealExpectation
import Definitions.Def_KernelDRO_Duality_Setting

open MeasureTheory
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality WassersteinDRO.Duality
end KernelDualityProof

open MeasureTheory Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality

variable {X : Type*} [MeasurableSpace X]

def probMix (P Q : ProbabilityMeasure X) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : ProbabilityMeasure X :=
  ⟨ENNReal.ofReal a • (P : Measure X) + ENNReal.ofReal b • (Q : Measure X), by
    constructor
    simp only [Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add ha hb, hab, ENNReal.ofReal_one]⟩

theorem integral_probMix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P Q : ProbabilityMeasure X) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) (f : X → E) (hP : Integrable f (P : Measure X))
    (hQ : Integrable f (Q : Measure X)) :
    (∫ x, f x ∂(probMix P Q a b ha hb hab : Measure X)) =
      a • (∫ x, f x ∂(P : Measure X)) + b • (∫ x, f x ∂(Q : Measure X)) := by
  change (∫ x, f x ∂(ENNReal.ofReal a • (P : Measure X) +
    ENNReal.ofReal b • (Q : Measure X))) = _
  rw [integral_add_measure (hP.smul_measure ENNReal.ofReal_ne_top)
    (hQ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, ENNReal.toReal_ofReal ha, ENNReal.toReal_ofReal hb]

theorem bounded_integrable (P : ProbabilityMeasure X) (h : X → ℝ) (hm : Measurable h)
    (B : ℝ) (hb : ∀ x, |h x| ≤ B) : Integrable h (P : Measure X) := by
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x

variable [MetricSpace X] [CompactSpace X] [BorelSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
theorem feature_integrable {φ : X → H} (hφ : Continuous φ) (P : ProbabilityMeasure X) :
    Integrable φ (P : Measure X) := by
  simpa only [integrableOn_univ] using hφ.continuousOn.integrableOn_compact isCompact_univ

theorem mean_probMix {φ : X → H} (hφ : Continuous φ) (P Q : ProbabilityMeasure X)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    meanEmbedding φ (probMix P Q a b ha hb hab) =
      a • meanEmbedding φ P + b • meanEmbedding φ Q :=
  integral_probMix P Q a b ha hb hab φ (feature_integrable hφ P) (feature_integrable hφ Q)

end KernelDualityProof

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality

variable {X H : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : X → H}

theorem integral_rkhsEval (hφ : Continuous φ) (P : ProbabilityMeasure X) (f : H) :
    (∫ x, rkhsEval φ f x ∂(P : Measure X)) = inner ℝ f (meanEmbedding φ P) := by
  exact (innerSL ℝ f).integral_comp_comm (feature_integrable hφ P)

def weakMean (φ : X → H) (P : ProbabilityMeasure X) : WeakSpace ℝ H :=
  toWeakSpace ℝ H (meanEmbedding φ P)

theorem weakMean_continuous (hφ : Continuous φ) : Continuous (weakMean φ) := by
  apply WeakBilin.continuous_of_continuous_eval
  intro f
  let g : C(X, ℝ) := ⟨fun x => f (φ x), f.continuous.comp hφ⟩
  have hi : (fun P : ProbabilityMeasure X => f (meanEmbedding φ P)) =
      fun P : ProbabilityMeasure X => ∫ x, g x ∂(P : Measure X) := by
    funext P
    exact (f.integral_comp_comm (feature_integrable hφ P)).symm
  change Continuous (fun P : ProbabilityMeasure X => f (meanEmbedding φ P))
  rw [hi]
  exact ProbabilityMeasure.continuous_integral_continuousMap g

omit [CompleteSpace H] in
theorem weak_closed {C : Set H} (hC : IsClosed C) (hv : Convex ℝ C) :
    IsClosed (toWeakSpace ℝ H '' C) := by
  rw [← closure_eq_iff_isClosed, ← hv.toWeakSpace_closure ℝ, hC.closure_eq]

theorem ambiguity_isClosed (hφ : Continuous φ) {C : Set H} (hC : IsClosed C)
    (hv : Convex ℝ C) : IsClosed (ambiguitySet φ C) := by
  have he : ambiguitySet φ C = (weakMean φ) ⁻¹' (toWeakSpace ℝ H '' C) := by
    ext P
    change meanEmbedding φ P ∈ C ↔ toWeakSpace ℝ H (meanEmbedding φ P) ∈ toWeakSpace ℝ H '' C
    constructor
    · exact fun hp => ⟨_, hp, rfl⟩
    · rintro ⟨y, hy, he⟩
      exact (toWeakSpace ℝ H).injective he ▸ hy
  rw [he]
  exact (weak_closed hC hv).preimage (weakMean_continuous hφ)

def momentPair (φ : X → H) (g : X → ℝ) (P : ProbabilityMeasure X) :
    WeakSpace ℝ H × ℝ := (weakMean φ P, ∫ x, g x ∂(P : Measure X))

theorem momentPair_continuous (hφ : Continuous φ) {g : X → ℝ} (hg : Continuous g) :
    Continuous (momentPair φ g) :=
  (weakMean_continuous hφ).prodMk
    (ProbabilityMeasure.continuous_integral_continuousMap (⟨g, hg⟩ : C(X, ℝ)))

theorem momentPair_mix (hφ : Continuous φ) {g : X → ℝ} (hg : Continuous g)
    (P Q : ProbabilityMeasure X) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    momentPair φ g (probMix P Q a b ha hb hab) =
      a • momentPair φ g P + b • momentPair φ g Q := by
  apply Prod.ext
  · change toWeakSpace ℝ H (meanEmbedding φ (probMix P Q a b ha hb hab)) = _
    rw [mean_probMix hφ]
    rfl
  · exact integral_probMix P Q a b ha hb hab g
      (feature_integrable hg P) (feature_integrable hg Q)

theorem momentRange_convex (hφ : Continuous φ) {g : X → ℝ} (hg : Continuous g) :
    Convex ℝ (range (momentPair φ g)) := by
  rintro _ ⟨P, rfl⟩ _ ⟨Q, rfl⟩ a b ha hb hab
  exact ⟨probMix P Q a b ha hb hab, momentPair_mix hφ hg P Q a b ha hb hab⟩

end KernelDualityProof

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

abbrev Hypo (h : X → ℝ) (B : ℝ) := {z : X × ℝ // -B ≤ z.2 ∧ z.2 ≤ h z.1}

def hypoFirst {h : X → ℝ} {B : ℝ} (z : Hypo h B) : X := z.val.1

def hypoHeight {h : X → ℝ} {B : ℝ} (z : Hypo h B) : ℝ := z.val.2

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem hypoFirst_continuous (h : X → ℝ) (B : ℝ) :
    Continuous (hypoFirst : Hypo h B → X) := continuous_fst.comp continuous_subtype_val

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem hypoHeight_continuous (h : X → ℝ) (B : ℝ) :
    Continuous (hypoHeight : Hypo h B → ℝ) := continuous_snd.comp continuous_subtype_val

omit [MeasurableSpace X] [BorelSpace X] in
theorem hypo_compact (h : X → ℝ) (hh : UpperSemicontinuous h) (B : ℝ)
    (hb : ∀ x, |h x| ≤ B) : CompactSpace (Hypo h B) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed {z : X × ℝ | -B ≤ z.2 ∧ z.2 ≤ h z.1} :=
    (isClosed_le continuous_const continuous_snd).inter hh.IsClosed_hypograph
  apply (isCompact_univ.prod (isCompact_Icc (a := -B) (b := B))).of_isClosed_subset hc
  intro z hz
  exact ⟨mem_univ _, hz.1, hz.2.trans (abs_le.mp (hb z.1)).2⟩

def hypoGraph (h : X → ℝ) (B : ℝ) (hb : ∀ x, |h x| ≤ B) (x : X) : Hypo h B :=
  ⟨(x, h x), (abs_le.mp (hb x)).1, le_rfl⟩

omit [CompactSpace X] in
theorem hypoGraph_measurable (h : X → ℝ) (hh : UpperSemicontinuous h) (B : ℝ)
    (hb : ∀ x, |h x| ≤ B) : Measurable (hypoGraph h B hb) :=
  (measurable_id.prodMk hh.measurable).subtype_mk

def hypoLift (h : X → ℝ) (hh : UpperSemicontinuous h) (B : ℝ)
    (hb : ∀ x, |h x| ≤ B) (P : ProbabilityMeasure X) : ProbabilityMeasure (Hypo h B) :=
  P.map (hypoGraph_measurable h hh B hb).aemeasurable

def hypoMarginal {h : X → ℝ} {B : ℝ} (R : ProbabilityMeasure (Hypo h B)) :
    ProbabilityMeasure X := R.map (hypoFirst_continuous h B).measurable.aemeasurable

omit [CompactSpace X] in
theorem hypoMarginal_continuous (h : X → ℝ) (B : ℝ) :
    Continuous (hypoMarginal : ProbabilityMeasure (Hypo h B) → ProbabilityMeasure X) :=
  ProbabilityMeasure.continuous_map (hypoFirst_continuous h B)

omit [CompactSpace X] in
theorem hypoMarginal_lift (h : X → ℝ) (hh : UpperSemicontinuous h) (B : ℝ)
    (hb : ∀ x, |h x| ≤ B) (P : ProbabilityMeasure X) :
    hypoMarginal (hypoLift h hh B hb P) = P := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map hypoFirst (Measure.map (hypoGraph h B hb) (P : Measure X)) = _
  rw [Measure.map_map (hypoFirst_continuous h B).measurable
    (hypoGraph_measurable h hh B hb)]
  have he : hypoFirst ∘ hypoGraph h B hb = id := rfl
  rw [he, Measure.map_id]

omit [CompactSpace X] in
theorem hypoHeight_integrable {h : X → ℝ} {B : ℝ} (hb : ∀ x, |h x| ≤ B)
    (R : ProbabilityMeasure (Hypo h B)) : Integrable hypoHeight (R : Measure (Hypo h B)) := by
  apply bounded_integrable R _ (hypoHeight_continuous h B).measurable B
  intro z
  exact abs_le.mpr ⟨z.property.1, z.property.2.trans (abs_le.mp (hb z.val.1)).2⟩

omit [CompactSpace X] in
theorem hypoHeight_lift (h : X → ℝ) (hh : UpperSemicontinuous h) (B : ℝ)
    (hb : ∀ x, |h x| ≤ B) (P : ProbabilityMeasure X) :
    (∫ z, hypoHeight z ∂(hypoLift h hh B hb P : Measure (Hypo h B))) =
      ∫ x, h x ∂(P : Measure X) := by
  exact integral_map (hypoGraph_measurable h hh B hb).aemeasurable
    (hypoHeight_integrable hb (hypoLift h hh B hb P)).aestronglyMeasurable

omit [CompactSpace X] in
theorem hypoHeight_le_marginal (h : X → ℝ) (hh : UpperSemicontinuous h) (B : ℝ)
    (hb : ∀ x, |h x| ≤ B) (R : ProbabilityMeasure (Hypo h B)) :
    (∫ z, hypoHeight z ∂(R : Measure (Hypo h B))) ≤
      ∫ x, h x ∂(hypoMarginal R : Measure X) := by
  rw [show (∫ x, h x ∂(hypoMarginal R : Measure X)) =
      ∫ z, h (hypoFirst z) ∂(R : Measure (Hypo h B)) from
    integral_map (hypoFirst_continuous h B).measurable.aemeasurable
      (bounded_integrable (hypoMarginal R) h hh.measurable B hb).aestronglyMeasurable]
  apply integral_mono (hypoHeight_integrable hb R)
    (bounded_integrable R _ (hh.measurable.comp (hypoFirst_continuous h B).measurable)
      B (fun z => hb (hypoFirst z)))
  exact fun z => z.property.2

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : X → H}

theorem hypo_mean_marginal (hφ : Continuous φ) {h : X → ℝ} {B : ℝ}
    (R : ProbabilityMeasure (Hypo h B)) :
    meanEmbedding (fun z : Hypo h B => φ (hypoFirst z)) R = meanEmbedding φ (hypoMarginal R) := by
  exact (integral_map (hypoFirst_continuous h B).measurable.aemeasurable
    (feature_integrable hφ (hypoMarginal R)).aestronglyMeasurable).symm

theorem feasible_superlevel_isCompact (hφ : Continuous φ) {C : Set H}
    (hC : IsClosed C) (hconv : Convex ℝ C) (h : X → ℝ) (hh : UpperSemicontinuous h)
    (B : ℝ) (_hB : 0 ≤ B) (hb : ∀ x, |h x| ≤ B) (r : ℝ) :
    IsCompact {P : ProbabilityMeasure X |
      P ∈ ambiguitySet φ C ∧ r ≤ ∫ x, h x ∂(P : Measure X)} := by
  let : CompactSpace (Hypo h B) := hypo_compact h hh B hb
  let T : Set (ProbabilityMeasure (Hypo h B)) :=
    {R | R ∈ ambiguitySet (fun z => φ (hypoFirst z)) C ∧
      r ≤ ∫ z, hypoHeight z ∂(R : Measure (Hypo h B))}
  have hT : IsCompact T := by
    apply IsClosed.isCompact
    exact (ambiguity_isClosed (hφ.comp (hypoFirst_continuous h B)) hC hconv).inter
      (isClosed_le continuous_const (ProbabilityMeasure.continuous_integral_continuousMap
        (⟨hypoHeight, hypoHeight_continuous h B⟩ : C(Hypo h B, ℝ))))
  have he : hypoMarginal '' T = {P : ProbabilityMeasure X |
      P ∈ ambiguitySet φ C ∧ r ≤ ∫ x, h x ∂(P : Measure X)} := by
    ext P
    constructor
    · rintro ⟨R, hR, rfl⟩
      refine ⟨?_, hR.2.trans (hypoHeight_le_marginal h hh B hb R)⟩
      change meanEmbedding φ (hypoMarginal R) ∈ C
      rw [← hypo_mean_marginal hφ]
      exact hR.1
    · intro hP
      refine ⟨hypoLift h hh B hb P, ⟨?_, ?_⟩, hypoMarginal_lift h hh B hb P⟩
      · change meanEmbedding (fun z : Hypo h B => φ (hypoFirst z)) _ ∈ C
        rw [hypo_mean_marginal hφ, hypoMarginal_lift]
        exact hP.1
      · rw [hypoHeight_lift]
        exact hP.2
  rw [← he]
  exact hT.image (hypoMarginal_continuous h B)

end KernelDualityProof

open MeasureTheory Set
open scoped Topology
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality

variable {X H : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {φ : X → H} {C : Set H}

theorem bounded_majorant (hφ : Continuous φ) (hC : IsClosed C) (hconv : Convex ℝ C)
    (hK : (ambiguitySet φ C).Nonempty) (h : X → ℝ) (hh : UpperSemicontinuous h)
    (B : ℝ) (_hB : 0 ≤ B) (hb : ∀ x, |h x| ≤ B) (r : ℝ)
    (hr : ∀ P ∈ ambiguitySet φ C, (∫ x, h x ∂(P : Measure X)) < r) :
    ∃ f0 : ℝ, ∃ f : H, IsDualFeasible φ (fun x => (h x : EReal)) f0 f ∧
      (f0 : EReal) + supportFun C f < (r : EReal) := by
  let : CompactSpace (Hypo h B) := hypo_compact h hh B hb
  let : LocallyConvexSpace ℝ (WeakSpace ℝ H) :=
    inferInstanceAs (LocallyConvexSpace ℝ (WeakBilin (topDualPairing ℝ H).flip))
  let Φ : Hypo h B → H := fun z => φ (hypoFirst z)
  have hΦ : Continuous Φ := hφ.comp (hypoFirst_continuous h B)
  let K : Set (WeakSpace ℝ H × ℝ) := range (momentPair Φ hypoHeight)
  let T : Set (WeakSpace ℝ H × ℝ) := (toWeakSpace ℝ H '' C) ×ˢ Ici r
  have hKc : IsCompact K := by
    simpa only [image_univ] using
      isCompact_univ.image (momentPair_continuous hΦ (hypoHeight_continuous h B))
  have hKv : Convex ℝ K := momentRange_convex hΦ (hypoHeight_continuous h B)
  have hTc : IsClosed T := (weak_closed hC hconv).prod isClosed_Ici
  have hTv : Convex ℝ T :=
    (hconv.linear_image (toWeakSpace ℝ H).toLinearMap).prod (convex_Ici r)
  have hd : Disjoint K T := by
    apply disjoint_left.mpr
    rintro z ⟨R, rfl⟩ hz
    rcases hz.1 with ⟨c, hc, he⟩
    have he' : c = meanEmbedding φ (hypoMarginal R) := by
      apply (toWeakSpace ℝ H).injective
      exact he.trans (congrArg (toWeakSpace ℝ H) (hypo_mean_marginal hφ R))
    have hp : hypoMarginal R ∈ ambiguitySet φ C := by
      change meanEmbedding φ (hypoMarginal R) ∈ C
      exact he' ▸ hc
    exact (hr _ hp).not_ge (hz.2.trans (hypoHeight_le_marginal h hh B hb R))
  obtain ⟨L, u, v, hKu, huv, hTv'⟩ :=
    geometric_hahn_banach_compact_closed hKv hKc hTv hTc hd
  let G : H →L[ℝ] ℝ := L.comp ((toWeakSpaceCLM ℝ H).prod (0 : H →L[ℝ] ℝ))
  let τ : ℝ := L (0, 1)
  have hL (c : H) (t : ℝ) : L (toWeakSpace ℝ H c, t) = G c + τ * t := by
    calc
      L (toWeakSpace ℝ H c, t) = L ((toWeakSpace ℝ H c, 0) + t • (0, 1)) := by
        congr 1
        simp
      _ = G c + τ * t := by
        rw [L.map_add, L.map_smul]
        change G c + t * τ = G c + τ * t
        ring
  obtain ⟨P0, hP0⟩ := hK
  let c0 := meanEmbedding φ P0
  let t0 := ∫ x, h x ∂(P0 : Measure X)
  have hz0 : (toWeakSpace ℝ H c0, t0) ∈ K := by
    refine ⟨hypoLift h hh B hb P0, ?_⟩
    apply Prod.ext
    · change toWeakSpace ℝ H (meanEmbedding Φ (hypoLift h hh B hb P0)) = _
      change toWeakSpace ℝ H (meanEmbedding (fun z : Hypo h B => φ (hypoFirst z))
        (hypoLift h hh B hb P0)) = _
      rw [hypo_mean_marginal hφ, hypoMarginal_lift]
    · exact hypoHeight_lift h hh B hb P0
  have hzT : (toWeakSpace ℝ H c0, r) ∈ T := ⟨⟨c0, hP0, rfl⟩, by change r ≤ r; exact le_rfl⟩
  have hu0 := hKu _ hz0
  have hv0 := hTv' _ hzT
  rw [hL] at hu0 hv0
  have ht0 : t0 < r := hr P0 hP0
  have hτ : 0 < τ := by
    by_contra hn
    have hn' : τ ≤ 0 := le_of_not_gt hn
    have hn'' := mul_nonpos_of_nonpos_of_nonneg hn' (sub_nonneg.mpr ht0.le)
    nlinarith
  let w : H := (InnerProductSpace.toDual ℝ H).symm G
  have hw (c : H) : inner ℝ w c = G c := InnerProductSpace.toDual_symm_apply
  let f : H := (-(τ⁻¹)) • w
  let f0 : ℝ := u / τ
  have hf (c : H) : inner ℝ f c = -(G c) / τ := by
    change inner ℝ ((-(τ⁻¹)) • w) c = _
    rw [real_inner_smul_left, hw]
    ring
  refine ⟨f0, f, ?_, ?_⟩
  · intro x
    have hxK : (toWeakSpace ℝ H (φ x), h x) ∈ K := by
      refine ⟨⟨Measure.dirac (hypoGraph h B hb x), inferInstance⟩, ?_⟩
      simp [momentPair, weakMean, meanEmbedding, Φ, hypoFirst, hypoHeight, hypoGraph]
    have hx := hKu _ hxK
    rw [hL] at hx
    have hx' : h x ≤ (u - G (φ x)) / τ :=
      (le_div_iff₀ hτ).mpr (by nlinarith)
    apply EReal.coe_le_coe_iff.mpr
    change h x ≤ u / τ + inner ℝ f (φ x)
    rw [hf, neg_div]
    rw [sub_div] at hx'
    simpa only [sub_eq_add_neg] using hx'
  · have hs : supportFun C f ≤ ((r - v / τ : ℝ) : EReal) := by
      apply iSup_le
      intro c
      apply iSup_le
      intro hc
      have hc' := hTv' (toWeakSpace ℝ H c, r) ⟨⟨c, hc, rfl⟩, by change r ≤ r; exact le_rfl⟩
      rw [hL] at hc'
      have hc'' : (v - G c) / τ < r := (div_lt_iff₀ hτ).mpr (by nlinarith)
      apply EReal.coe_le_coe_iff.mpr
      rw [hf, neg_div]
      rw [sub_div] at hc''
      linarith
    calc
      (f0 : EReal) + supportFun C f ≤ (f0 : EReal) + ((r - v / τ : ℝ) : EReal) :=
        add_le_add le_rfl hs
      _ = ((f0 + (r - v / τ) : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ < (r : EReal) := by
        apply EReal.coe_lt_coe_iff.mpr
        have huv' := div_lt_div_of_pos_right huv hτ
        dsimp [f0]
        linarith

end KernelDualityProof

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality WassersteinDRO.Duality

theorem deficit_parts (z : EReal) (M : ℝ) (hM : 0 ≤ M) (hz : z ≤ (M : EReal)) :
    ((M : EReal) - z).toENNReal + z.toENNReal =
      ENNReal.ofReal M + (-z).toENNReal := by
  by_cases hbot : z = ⊥
  · subst z
    simp
  have htop : z ≠ ⊤ := by
    intro h
    simp [h] at hz
  lift z to ℝ using ⟨htop, hbot⟩
  have hzM : z ≤ M := EReal.coe_le_coe_iff.mp hz
  simp only [← EReal.coe_sub, ← EReal.coe_neg, EReal.real_coe_toENNReal]
  by_cases h : 0 ≤ z
  · rw [ENNReal.ofReal_of_nonpos (neg_nonpos.mpr h), add_zero,
      ← ENNReal.ofReal_add (sub_nonneg.mpr hzM) h]
    congr 1
    ring
  · have hz0 : z ≤ 0 := le_of_not_ge h
    rw [ENNReal.ofReal_of_nonpos hz0, add_zero,
      ← ENNReal.ofReal_add hM (neg_nonneg.mpr hz0)]
    congr 1

variable {X : Type*} [MeasurableSpace X]

theorem lintegral_ofReal_ne_top (μ : Measure X) (g : X → ℝ) (hg : Integrable g μ) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ≠ ⊤ := by
  apply ne_of_lt
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_)
    ((hasFiniteIntegral_iff_norm g).mp hg.hasFiniteIntegral)
  exact ENNReal.ofReal_le_ofReal (le_abs_self (g x))

theorem expectation_coe (μ : Measure X) (g : X → ℝ) (hg : Integrable g μ) :
    erealExpectation μ (fun x => (g x : EReal)) = ((∫ x, g x ∂μ : ℝ) : EReal) := by
  have hp := lintegral_ofReal_ne_top μ g hg
  have hn := lintegral_ofReal_ne_top μ (fun x => -g x) hg.neg
  have hp' : (∫⁻ x, (g x : EReal).toENNReal ∂μ) ≠ ⊤ := hp
  rw [erealExpectation, if_neg hp']
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  rw [← EReal.coe_ennreal_toReal hp, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_sub, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hg]

theorem expectation_le_integral (μ : Measure X) (l : X → EReal) (g : X → ℝ)
    (hg : Integrable g μ) (hle : ∀ x, l x ≤ (g x : EReal)) :
    erealExpectation μ l ≤ ((∫ x, g x ∂μ : ℝ) : EReal) := by
  have hp := lintegral_ofReal_ne_top μ g hg
  have hpos : (∫⁻ x, (l x).toENNReal ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂μ :=
    lintegral_mono fun x => EReal.toENNReal_le_toENNReal (hle x)
  have hneg : (∫⁻ x, ENNReal.ofReal (-g x) ∂μ) ≤ ∫⁻ x, (-l x).toENNReal ∂μ := by
    apply lintegral_mono
    intro x
    simpa only [← EReal.coe_neg, EReal.real_coe_toENNReal] using
      EReal.toENNReal_le_toENNReal (EReal.neg_le_neg_iff.mpr (hle x))
  have hlp := ne_top_of_le_ne_top hp hpos
  rw [← expectation_coe μ g hg]
  have hp' : (∫⁻ x, (g x : EReal).toENNReal ∂μ) ≠ ⊤ := hp
  rw [erealExpectation, if_neg hlp, erealExpectation, if_neg hp']
  simp only [EReal.real_coe_toENNReal, ← EReal.coe_neg]
  exact EReal.sub_le_sub
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hpos)
    (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hneg)

theorem expectation_deficit (P : ProbabilityMeasure X) (l : X → EReal)
    (hl : Measurable l) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, l x ≤ (M : EReal)) :
    erealExpectation (P : Measure X) l = (M : EReal) -
      ((∫⁻ x, ((M : EReal) - l x).toENNReal ∂(P : Measure X) : ENNReal) : EReal) := by
  let A : ENNReal := ∫⁻ x, (l x).toENNReal ∂(P : Measure X)
  let B : ENNReal := ∫⁻ x, (-l x).toENNReal ∂(P : Measure X)
  let D : ENNReal := ∫⁻ x, ((M : EReal) - l x).toENNReal ∂(P : Measure X)
  have hAb : A ≤ ENNReal.ofReal M := by
    calc
      A ≤ ∫⁻ _ : X, ENNReal.ofReal M ∂(P : Measure X) :=
        lintegral_mono fun x => EReal.toENNReal_le_toENNReal (hb x)
      _ = _ := by simp
  have hA : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hAb
  have hd : Measurable (fun x => ((M : EReal) - l x).toENNReal) :=
    (measurable_const.sub hl).ereal_toENNReal
  have hn : Measurable (fun x => (-l x).toENNReal) := hl.neg.ereal_toENNReal
  have hEq : D + A = ENNReal.ofReal M + B := by
    calc
      D + A = ∫⁻ x, ((M : EReal) - l x).toENNReal + (l x).toENNReal
          ∂(P : Measure X) := (lintegral_add_left hd _).symm
      _ = ∫⁻ x, ENNReal.ofReal M + (-l x).toENNReal ∂(P : Measure X) :=
        lintegral_congr fun x => deficit_parts (l x) M hM (hb x)
      _ = _ := by rw [lintegral_add_right _ hn]; simp [B]
  change (if A = ⊤ then ⊤ else (A : EReal) - (B : EReal)) =
    (M : EReal) - (D : EReal)
  rw [if_neg hA]
  by_cases hB : B = ⊤
  · have hD : D = ⊤ := by
      rw [hB, add_top] at hEq
      exact (ENNReal.add_eq_top.mp hEq).resolve_right hA
    simp [hB, hD]
  · have hDA : D + A ≠ ⊤ := by
      rw [hEq]
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, hB⟩
    have hD : D ≠ ⊤ := ne_top_of_le_ne_top hDA (le_add_of_nonneg_right (show 0 ≤ A from bot_le))
    have he := congrArg ENNReal.toReal hEq
    rw [ENNReal.toReal_add hD hA, ENNReal.toReal_add ENNReal.ofReal_ne_top hB,
      ENNReal.toReal_ofReal hM] at he
    rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB,
      ← EReal.coe_ennreal_toReal hD, ← EReal.coe_sub, ← EReal.coe_sub]
    exact congrArg (fun t : ℝ => (t : EReal)) (by linarith)

end KernelDualityProof

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality WassersteinDRO.Duality

def realTruncation {X : Type*} (l : X → EReal) (n : ℕ) (x : X) : ℝ :=
  (max (l x) ((-(n : ℝ)) : EReal)).toReal

theorem realTruncation_coe {X : Type*} (l : X → EReal) (ht : ∀ x, l x ≠ ⊤)
    (n : ℕ) (x : X) : (realTruncation l n x : EReal) = max (l x) ((-(n : ℝ)) : EReal) := by
  apply EReal.coe_toReal
  · exact ne_of_lt (max_lt (lt_top_iff_ne_top.mpr (ht x)) (EReal.coe_lt_top _))
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (le_max_right _ _)

theorem realTruncation_upper {X : Type*} (l : X → EReal) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, l x ≤ (M : EReal)) (n : ℕ) (x : X) : realTruncation l n x ≤ M := by
  have ht : ∀ x, l x ≠ ⊤ := fun x => ne_top_of_le_ne_top (EReal.coe_ne_top _) (hb x)
  apply EReal.coe_le_coe_iff.mp
  rw [realTruncation_coe l ht]
  refine max_le (hb x) ?_
  exact_mod_cast (show -(n : ℝ) ≤ M by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem realTruncation_bound {X : Type*} (l : X → EReal) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, l x ≤ (M : EReal)) (n : ℕ) : ∀ x, |realTruncation l n x| ≤ M + n := by
  intro x
  have ht : ∀ x, l x ≠ ⊤ := fun x => ne_top_of_le_ne_top (EReal.coe_ne_top _) (hb x)
  have hlo : -(n : ℝ) ≤ realTruncation l n x := by
    apply EReal.coe_le_coe_iff.mp
    rw [realTruncation_coe l ht]
    exact le_max_right _ _
  have hhi := realTruncation_upper l M hM hb n x
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem realTruncation_antitone {X : Type*} (l : X → EReal) (ht : ∀ x, l x ≠ ⊤) :
    Antitone (realTruncation l) := by
  intro n m hnm x
  apply EReal.coe_le_coe_iff.mp
  rw [realTruncation_coe l ht, realTruncation_coe l ht]
  apply max_le_max_left
  exact_mod_cast (neg_le_neg (Nat.cast_le.mpr hnm) : -(m : ℝ) ≤ -(n : ℝ))

theorem truncated_deficit_iSup (z : EReal) (M : ℝ) (hM : 0 ≤ M) :
    (⨆ n : ℕ, ((M : EReal) - max z ((-(n : ℝ)) : EReal)).toENNReal) =
      ((M : EReal) - z).toENNReal := by
  apply le_antisymm
  · apply iSup_le
    intro n
    exact EReal.toENNReal_le_toENNReal (EReal.sub_le_sub le_rfl (le_max_left _ _))
  · induction z
    · simp only [EReal.coe_sub_bot, EReal.toENNReal_top]
      rw [← ENNReal.iSup_natCast]
      apply iSup_le
      intro n
      refine le_trans ?_ (le_iSup _ n)
      simp only [max_eq_right bot_le, ← EReal.coe_neg, ← EReal.coe_sub, EReal.real_coe_toENNReal]
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rename_i z
      obtain ⟨n, hn⟩ := exists_nat_ge (-z)
      have h : ((-(n : ℝ)) : EReal) ≤ (z : EReal) := by exact_mod_cast (show -(n : ℝ) ≤ z by linarith)
      exact le_trans (by rw [max_eq_left h]) (le_iSup _ n)
    · simp

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem realTruncation_usc (l : X → EReal) (hu : UpperSemicontinuous l)
    (ht : ∀ x, l x ≠ ⊤) (n : ℕ) : UpperSemicontinuous (realTruncation l n) := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro c
  have he : (realTruncation l n) ⁻¹' Iio c =
      (l ⁻¹' Iio (c : EReal)) ∩ {x : X | -(n : ℝ) < c} := by
    ext x
    simp only [mem_preimage, mem_Iio, mem_inter_iff, mem_ofPred_eq]
    rw [← EReal.coe_lt_coe_iff, realTruncation_coe l ht, max_lt_iff]
    simp only [← EReal.coe_neg, EReal.coe_lt_coe_iff]
  rw [he]
  exact (hu.isOpen_preimage _).inter isOpen_const

omit [MeasurableSpace X] [BorelSpace X] in
theorem usc_upper_bound (l : X → EReal) (hu : UpperSemicontinuous l)
    (ht : ∀ x, l x ≠ ⊤) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, l x ≤ (M : EReal) := by
  classical
  by_cases hX : Nonempty X
  · let _ := hX
    obtain ⟨a, _, ha⟩ := UpperSemicontinuousOn.exists_isMaxOn
      (s := (univ : Set X)) univ_nonempty isCompact_univ (hu.upperSemicontinuousOn univ)
    refine ⟨max 0 (l a).toReal, le_max_left _ _, fun x => ?_⟩
    have hx : l x ≤ l a := ha (mem_univ x)
    by_cases hbot : l a = ⊥
    · exact hx.trans (by simp [hbot])
    · calc
        l x ≤ l a := hx
        _ = ((l a).toReal : EReal) := (EReal.coe_toReal (ht a) hbot).symm
        _ ≤ _ := EReal.coe_le_coe_iff.mpr (le_max_right _ _)
  · exact ⟨0, le_rfl, fun x => (hX ⟨x⟩).elim⟩

omit [CompactSpace X] in
theorem truncation_deficit_integral (P : ProbabilityMeasure X) (l : X → EReal)
    (hu : UpperSemicontinuous l) (ht : ∀ x, l x ≠ ⊤) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, l x ≤ (M : EReal)) (n : ℕ) :
    (∫⁻ x, ((M : EReal) - max (l x) ((-(n : ℝ)) : EReal)).toENNReal ∂(P : Measure X)) =
      ENNReal.ofReal (M - ∫ x, realTruncation l n x ∂(P : Measure X)) := by
  have hi := bounded_integrable P (realTruncation l n)
    (realTruncation_usc l hu ht n).measurable (M + n) (realTruncation_bound l M hM hb n)
  simp_rw [← realTruncation_coe l ht, ← EReal.coe_sub, EReal.real_coe_toENNReal]
  have hi' : Integrable (fun x => M - realTruncation l n x) (P : Measure X) := by
    convert! (integrable_const M).sub hi using 1
  rw [← ofReal_integral_eq_lintegral_ofReal hi']
  · rw [integral_sub (integrable_const M) hi]
    simp
  · exact Eventually.of_forall fun x => sub_nonneg.mpr (realTruncation_upper l M hM hb n x)

omit [CompactSpace X] in
theorem expectation_truncation_inf (P : ProbabilityMeasure X) (l : X → EReal)
    (hu : UpperSemicontinuous l) (ht : ∀ x, l x ≠ ⊤) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ x, l x ≤ (M : EReal)) : erealExpectation (P : Measure X) l =
      ⨅ n : ℕ, ((∫ x, realTruncation l n x ∂(P : Measure X) : ℝ) : EReal) := by
  have hi (n : ℕ) := bounded_integrable P (realTruncation l n)
    (realTruncation_usc l hu ht n).measurable (M + n) (realTruncation_bound l M hM hb n)
  have hleft : erealExpectation (P : Measure X) l ≤
      ⨅ n : ℕ, ((∫ x, realTruncation l n x ∂(P : Measure X) : ℝ) : EReal) := by
    apply le_iInf
    intro n
    apply expectation_le_integral _ _ _ (hi n)
    intro x
    rw [realTruncation_coe l ht]
    exact le_max_left _ _
  refine le_antisymm hleft ?_
  by_contra! hbad
  obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real hbad
  have hrn (n : ℕ) : r ≤ ∫ x, realTruncation l n x ∂(P : Measure X) :=
    EReal.coe_le_coe_iff.mp (hr'.le.trans (iInf_le _ n))
  have hrM : r ≤ M := by
    refine (hrn 0).trans ?_
    calc
      _ ≤ ∫ _ : X, M ∂(P : Measure X) := integral_mono (hi 0) (integrable_const M)
        (realTruncation_upper l M hM hb 0)
      _ = M := by simp
  let d (n : ℕ) (x : X) : ENNReal :=
    ((M : EReal) - max (l x) ((-(n : ℝ)) : EReal)).toENNReal
  have hd (n : ℕ) : Measurable (d n) :=
    (measurable_const.sub (hu.measurable.max measurable_const)).ereal_toENNReal
  have hmono : Monotone d := by
    intro n m hnm x
    apply EReal.toENNReal_le_toENNReal
    apply EReal.sub_le_sub le_rfl
    apply max_le_max_left
    exact_mod_cast (neg_le_neg (Nat.cast_le.mpr hnm) : -(m : ℝ) ≤ -(n : ℝ))
  have hD : (∫⁻ x, ((M : EReal) - l x).toENNReal ∂(P : Measure X)) ≤
      ENNReal.ofReal (M - r) := by
    have he : (fun x => ((M : EReal) - l x).toENNReal) = fun x => ⨆ n, d n x := by
      funext x
      exact (truncated_deficit_iSup (l x) M hM).symm
    rw [he, lintegral_iSup hd hmono]
    apply iSup_le
    intro n
    rw [truncation_deficit_integral P l hu ht M hM hb n]
    exact ENNReal.ofReal_le_ofReal (sub_le_sub_left (hrn n) M)
  have hDf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hD
  have hDr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hD
  rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hrM)] at hDr
  have hrE : (r : EReal) ≤ erealExpectation (P : Measure X) l := by
    rw [expectation_deficit P l hu.measurable M hM hb,
      ← EReal.coe_ennreal_toReal hDf, ← EReal.coe_sub]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  exact not_lt_of_ge hrE hr

end KernelDualityProof

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality WassersteinDRO.Duality

variable {X H : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem weak_duality (φ : X → H) (hφ : Continuous φ) (C : Set H) (l : X → EReal) :
    primalValue φ C l ≤ dualValue φ C l := by
  apply le_iInf
  intro f0
  apply le_iInf
  intro f
  apply le_iInf
  intro hf
  apply iSup_le
  intro P
  apply iSup_le
  intro hP
  have hg : Continuous (fun x => f0 + rkhsEval φ f x) :=
    continuous_const.add (continuous_const.inner hφ)
  have hi := feature_integrable hg P
  have hgi : Integrable (rkhsEval φ f) (P : Measure X) :=
    feature_integrable (show Continuous (rkhsEval φ f) from continuous_const.inner hφ) P
  have he : (∫ x, f0 + rkhsEval φ f x ∂(P : Measure X)) =
      f0 + inner ℝ f (meanEmbedding φ P) := by
    rw [integral_add (integrable_const f0) hgi, integral_rkhsEval hφ P f]
    simp
  have hs : ((inner ℝ f (meanEmbedding φ P) : ℝ) : EReal) ≤ supportFun C f :=
    le_iSup_of_le (meanEmbedding φ P) (le_iSup_of_le hP le_rfl)
  calc
    erealExpectation (P : Measure X) l ≤
        ((∫ x, f0 + rkhsEval φ f x ∂(P : Measure X) : ℝ) : EReal) :=
      expectation_le_integral _ _ _ hi hf
    _ = (f0 : EReal) + ((inner ℝ f (meanEmbedding φ P) : ℝ) : EReal) := by
      rw [he, EReal.coe_add]
    _ ≤ _ := add_le_add le_rfl hs

end KernelDualityProof

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
noncomputable section
namespace KernelDualityProof
open KernelDRO.Duality WassersteinDRO.Duality

variable {X H : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem strong_duality (φ : X → H) (hφ : Continuous φ) (C : Set H)
    (hc : IsClosed C) (hv : Convex ℝ C) (hk : (ambiguitySet φ C).Nonempty)
    (l : X → EReal) (hu : UpperSemicontinuous l) (ht : ∀ x, l x ≠ ⊤) :
    primalValue φ C l = dualValue φ C l := by
  classical
  refine le_antisymm (weak_duality φ hφ C l) ?_
  by_contra! hbad
  obtain ⟨r, hr, hr'⟩ := EReal.exists_between_coe_real hbad
  obtain ⟨M, hM, hb⟩ := usc_upper_bound l hu ht
  let S (n : ℕ) : Set (ProbabilityMeasure X) :=
    {P | P ∈ ambiguitySet φ C ∧ r ≤ ∫ x, realTruncation l n x ∂(P : Measure X)}
  have hi (P : ProbabilityMeasure X) (n : ℕ) := bounded_integrable P (realTruncation l n)
    (realTruncation_usc l hu ht n).measurable (M + n) (realTruncation_bound l M hM hb n)
  have hcompact (n : ℕ) : IsCompact (S n) :=
    feasible_superlevel_isCompact (φ := φ) (C := C) hφ hc hv (realTruncation l n)
      (realTruncation_usc l hu ht n) (M + n) (by positivity)
      (realTruncation_bound l M hM hb n) r
  have hdec (n : ℕ) : S (n + 1) ⊆ S n := by
    intro P hP
    refine ⟨hP.1, hP.2.trans ?_⟩
    exact integral_mono (hi P (n + 1)) (hi P n)
      (realTruncation_antitone l ht (Nat.le_succ n))
  have hempty : ∃ n, S n = ∅ := by
    by_contra hno
    have hnon (n : ℕ) : (S n).Nonempty :=
      nonempty_iff_ne_empty.mpr (fun hn => hno ⟨n, hn⟩)
    obtain ⟨P, hP⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      S hdec hnon (hcompact 0) (fun n => (hcompact n).isClosed)
    have hPn : ∀ n, P ∈ S n := mem_iInter.mp hP
    have hrE : (r : EReal) ≤ erealExpectation (P : Measure X) l := by
      rw [expectation_truncation_inf P l hu ht M hM hb]
      exact le_iInf fun n => EReal.coe_le_coe_iff.mpr (hPn n).2
    have hEp : erealExpectation (P : Measure X) l ≤ primalValue φ C l :=
      le_iSup_of_le P (le_iSup_of_le (hPn 0).1 le_rfl)
    exact not_lt_of_ge (hrE.trans hEp) hr
  obtain ⟨n, hn⟩ := hempty
  have hlow : ∀ P ∈ ambiguitySet φ C, (∫ x, realTruncation l n x ∂(P : Measure X)) < r := by
    intro P hP
    by_contra! h
    have hm : P ∈ S n := ⟨hP, h⟩
    rw [hn] at hm
    exact hm
  obtain ⟨f0, f, hf, hout⟩ := bounded_majorant (φ := φ) (C := C) hφ hc hv hk
    (realTruncation l n) (realTruncation_usc l hu ht n) (M + n) (by positivity)
    (realTruncation_bound l M hM hb n) r hlow
  have hfl : IsDualFeasible φ l f0 f := by
    intro x
    refine le_trans ?_ (hf x)
    change l x ≤ ((realTruncation l n x : ℝ) : EReal)
    rw [realTruncation_coe l ht]
    exact le_max_left _ _
  have hd : dualValue φ C l ≤ (f0 : EReal) + supportFun C f :=
    iInf_le_of_le f0 (iInf_le_of_le f (iInf_le _ hfl))
  exact not_lt_of_ge (hd.trans hout.le) hr'

end KernelDualityProof

open MeasureTheory

namespace KernelDRO.Duality

open WassersteinDRO.Duality

/-- **Theorem 3.1** (Generalized Duality) (Zhu, Jitkrittum, Diehl & Schölkopf, Kernel Distributionally
Robust Optimization, arXiv:2006.06981v3, Theorem 3.1, p. 5; proved on p. 16 from Proposition A.1 by
(15)). Under Assumption 3.1, the Kernel DRO problem
`(P) := min_θ sup_{P,µ} {∫ l(θ, ξ) dP(ξ) : ∫ φ dP = µ, P ∈ 𝒫, µ ∈ 𝒞}` (2) is equivalent to
`(D) := min_{θ, f₀∈ℝ, f∈ℋ} f₀ + δ*_𝒞(f)` subject to `l(θ, ξ) ≤ f₀ + f(ξ), ∀ ξ ∈ 𝒳` (4), where
`δ*_𝒞(f) := sup_{µ∈𝒞} ⟨f, µ⟩_ℋ`; i.e. `(P) = (D)`, and strong duality holds for the inner moment
problem for every `θ` pointwise.

**Formalization Note.** The decision variable `θ` ranges over an arbitrary type `Θ` ("The theorem
holds regardless of the dependency of l on θ", p. 5) and the loss is `l : Θ → 𝒳 → [−∞, ∞)`. Standing
hypotheses (Assumption 3.1, p. 3, and §2, p. 2): `𝒳` is a compact metric space with its Borel
σ-algebra (a compact `𝒳 ⊂ ℝᵈ` is an instance); the RKHS is in feature-map form, a real Hilbert space
`ℋ` with a continuous feature map `φ` (continuity of the kernel is not written in Assumption 3.1 but
is used by §D.2 through a universal, hence continuous, kernel); `𝒞 ⊆ ℋ` is closed and convex; every
`l(θ, ·)` is upper semicontinuous, never `+∞`, and proper (not identically `−∞`, p. 2). The Slater
clause "ri(𝒦_𝒞) ≠ ∅" names no topology on measures and is used in the proof only as "the primal
problem has a non-empty solution set" (p. 15); it is read as `𝒦_𝒞 ≠ ∅`, which it implies under any
reading, so this statement is at least as strong as the paper's. Every "min" (the outer `min_θ` of
(2) and (4) and the inner `min_{f₀, f}`) is read as an infimum: dual attainment is not proved in the
paper and can fail. `∫ l dP` is the published `erealExpectation` and all values are extended
reals. The first conjunct is the pointwise strong duality, the second the literal `(P) = (D)`. -/
theorem theorem_3_1 {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Θ : Type*} (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : Θ → X → EReal) (hl_usc : ∀ θ, UpperSemicontinuous (l θ))
    (hl_top : ∀ θ ξ, l θ ξ ≠ ⊤) (hl_proper : ∀ θ, ∃ ξ, l θ ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) :
    (∀ θ, primalValue φ C (l θ) = dualValue φ C (l θ)) ∧
      (⨅ θ, primalValue φ C (l θ)) = ⨅ θ, dualValue φ C (l θ) := by
  have _ := hl_proper
  have hpoint : ∀ θ, primalValue φ C (l θ) = dualValue φ C (l θ) :=
    fun θ => KernelDualityProof.strong_duality φ hφ C hC_closed hC_convex hK
      (l θ) (hl_usc θ) (hl_top θ)
  exact ⟨hpoint, iInf_congr hpoint⟩

end KernelDRO.Duality

open KernelDRO.Duality

theorem solution {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Θ : Type*} (φ : X → H) (hφ : Continuous φ) (C : Set H) (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (l : Θ → X → EReal) (hl_usc : ∀ θ, UpperSemicontinuous (l θ))
    (hl_top : ∀ θ ξ, l θ ξ ≠ ⊤) (hl_proper : ∀ θ, ∃ ξ, l θ ξ ≠ ⊥)
    (hK : (ambiguitySet φ C).Nonempty) :
    (∀ θ, primalValue φ C (l θ) = dualValue φ C (l θ)) ∧
      (⨅ θ, primalValue φ C (l θ)) = ⨅ θ, dualValue φ C (l θ) := by
  exact KernelDRO.Duality.theorem_3_1 φ hφ C hC_closed hC_convex l hl_usc hl_top hl_proper hK
