-- Prove2me | solution 1 for OAI.ComparatorModel.CurrentMain.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T22:14:46.15533+00:00
-- url     : https://prove2.me/submissions/592d398a-e659-420d-b528-336f84d1af13

import Mathlib
import Definitions.Def_UniformGamma
import Definitions.Def_OAIQWCMM000
import Theorems.Thm_OAI_CurrentMain_finite_set_central_splitting

section
-- module Solutions.OAIQW_TracialSplitting.TraceEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section TraceIdentities

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D]

lemma trace_projection_corner (τ : TracialState D) {p : D}
    (hp : IsStarProjection p) (a : D) :
    τ.functional (p * a * p) = τ.functional (p * a) := by
  rw [τ.tracial (p * a) p, ← mul_assoc, hp.isIdempotentElem]

end TraceIdentities

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SpectralCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section FiniteSpectralResolution

variable {D : Type uD} [CStarAlgebra D]

lemma realSpectrum_finite {a : D} (ha : IsSelfAdjoint a)
    (hfinite : (spectrum ℂ a).Finite) : (spectrum ℝ a).Finite := by
  rw [← ha.spectrumRestricts.image]
  exact hfinite.image _

end FiniteSpectralResolution

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ScalarCompression
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ScalarCompression

attribute [instance] ProjectionPartition.indexFintype

end ScalarCompression

section SpectralThresholds

variable {D : Type uD} [CStarAlgebra D]

lemma spectralThreshold_projection {a : D} (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    IsStarProjection (spectralThreshold a t) := by
  refine ⟨?_, cfc_predicate _ _⟩
  change cfc _ a * cfc _ a = cfc _ a
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

lemma spectralThreshold_complement {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    1 - spectralThreshold a t = cfc (fun s : ℝ => if t ≤ s then (0 : ℝ) else 1) a := by
  rw [spectralThreshold, ← cfc_one ℝ a ha,
    ← cfc_sub _ _ a (hf.continuousOn _) (hf.continuousOn _)]
  apply cfc_congr
  intro x _
  dsimp only
  split_ifs <;> norm_num

variable [PartialOrder D] [StarOrderedRing D]

lemma spectralThreshold_lower {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    t • spectralThreshold a t ≤ spectralThreshold a t * a * spectralThreshold a t := by
  unfold spectralThreshold
  nth_rw 3 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_smul _ _ a (hf.continuousOn _)]
  apply (cfc_le_iff _ _ a (hf.continuousOn _) (hf.continuousOn _) ha).mpr
  intro x _
  simp only [smul_eq_mul]
  split_ifs with hx
  · simpa using hx
  · simp

lemma spectralThreshold_complement_upper {a : D} (ha : IsSelfAdjoint a)
    (hf : (spectrum ℝ a).Finite) (t : ℝ) :
    (1 - spectralThreshold a t) * a * (1 - spectralThreshold a t) ≤
      t • (1 - spectralThreshold a t) := by
  rw [spectralThreshold_complement ha hf]
  nth_rw 2 [← cfc_id ℝ a ha]
  rw [← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_mul _ _ a (hf.continuousOn _) (hf.continuousOn _),
    ← cfc_smul _ _ a (hf.continuousOn _)]
  apply (cfc_le_iff _ _ a (hf.continuousOn _) (hf.continuousOn _) ha).mpr
  intro x _
  simp only [smul_eq_mul]
  split_ifs with hx
  · simp
  · simpa using (le_of_lt (lt_of_not_ge hx))

lemma compress_perturbation_lower {a b p : D} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hp : IsStarProjection p) :
    p * a * p - ‖a - b‖ • p ≤ p * b * p := by
  have h := star_left_conjugate_le_conjugate (ha.sub hb).le_algebraMap_norm_self p
  simp only [hp.isSelfAdjoint.star_eq, mul_sub, sub_mul, Algebra.algebraMap_eq_smul_one,
    mul_smul_comm, smul_mul_assoc, mul_one, hp.isIdempotentElem.eq] at h
  exact sub_le_comm.mp h

lemma compress_perturbation_upper {a b p : D} (ha : IsSelfAdjoint a)
    (hb : IsSelfAdjoint b) (hp : IsStarProjection p) :
    p * b * p ≤ p * a * p + ‖a - b‖ • p := by
  have h := compress_perturbation_lower hb ha hp
  rw [norm_sub_rev] at h
  exact sub_le_iff_le_add.mp h

end SpectralThresholds

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section ColumnSplitting

variable {D : Type uD} [CStarAlgebra D]

variable [PartialOrder D] [StarOrderedRing D]

lemma exists_spectral_cut (hRR : RealRankZero D) {a : D} (ha : IsSelfAdjoint a)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ e : D, IsStarProjection e ∧
      (t - ε) • e ≤ e * a * e ∧
      (1 - e) * a * (1 - e) ≤ (t + ε) • (1 - e) := by
  obtain ⟨b, hb, hbf, hba⟩ := hRR a ha ε hε
  have hbf' := realSpectrum_finite hb hbf
  let e := spectralThreshold b t
  have he : IsStarProjection e := spectralThreshold_projection hbf' t
  have hr : IsStarProjection (1 - e) := he.one_sub
  have hn : ‖b - a‖ ≤ ε := (norm_sub_rev b a ▸ hba.le)
  refine ⟨e, he, ?_, ?_⟩
  · calc
      (t - ε) • e = t • e - ε • e := sub_smul _ _ _
      _ ≤ e * b * e - ‖b - a‖ • e := sub_le_sub
        (spectralThreshold_lower hb hbf' t)
        (smul_le_smul_of_nonneg_right hn he.nonneg)
      _ ≤ e * a * e := compress_perturbation_lower hb ha he
  · calc
      (1 - e) * a * (1 - e) ≤ (1 - e) * b * (1 - e) + ‖b - a‖ • (1 - e) :=
        compress_perturbation_upper hb ha hr
      _ ≤ t • (1 - e) + ε • (1 - e) := add_le_add
        (spectralThreshold_complement_upper hb hbf' t)
        (smul_le_smul_of_nonneg_right hn hr.nonneg)
      _ = (t + ε) • (1 - e) := (add_smul _ _ _).symm

end ColumnSplitting

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ProjectionSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uI


section

noncomputable section

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section OrthogonalInsertion

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma trace_mul_mono_right (τ : TracialState D) {a b c : D} (ha : 0 ≤ a) (hbc : b ≤ c) :
    (τ.functional (a * b)).re ≤ (τ.functional (a * c)).re := by
  have h := (trace_mul_nonneg τ ha (sub_nonneg.mpr hbc)).1
  simp only [mul_sub, map_sub, Complex.sub_re, Complex.zero_re] at h
  linarith

lemma trace_mul_mono_left (τ : TracialState D) {a b c : D} (hc : 0 ≤ c) (hab : a ≤ b) :
    (τ.functional (a * c)).re ≤ (τ.functional (b * c)).re := by
  rw [τ.tracial a c, τ.tracial b c]
  exact trace_mul_mono_right τ hc hab

end OrthogonalInsertion

end CurrentMain

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.Completion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uD uE uI uJ uX

namespace CurrentMain

section

open Pureness

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

lemma familyTwoNorm_sub_le (a b : D) :
    familyTwoNorm τ (a - b) ≤ familyTwoNorm τ a + familyTwoNorm τ b := by
  simpa only [sub_eq_add_neg, familyTwoNorm_neg] using familyTwoNorm_add_le τ a (-b)

omit [Nonempty I] in
lemma familyTraceNorm_bdd (a : D) : BddAbove (Set.range (fun i => ‖(τ i).functional a‖)) :=
  ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact trace_norm_le_norm (τ i) a⟩

omit [Nonempty I] in
lemma traceNorm_le_family (i : I) (a : D) :
    ‖(τ i).functional a‖ ≤ familyTraceNorm τ a := le_ciSup (familyTraceNorm_bdd τ a) i

lemma familyTraceNorm_nonneg (a : D) : 0 ≤ familyTraceNorm τ a := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (norm_nonneg _).trans (traceNorm_le_family τ i a)

lemma familyTraceNorm_le_twoNorm (a : D) : familyTraceNorm τ a ≤ familyTwoNorm τ a := by
  apply ciSup_le
  intro i
  exact (trace_norm_le_twoNorm (τ i) a).trans (traceTwoNorm_le_family τ i a)

lemma familyTraceNorm_le_norm (a : D) : familyTraceNorm τ a ≤ ‖a‖ :=
  (familyTraceNorm_le_twoNorm τ a).trans (familyTwoNorm_le_norm τ a)

end

open Pureness Filter

open scoped Topology NNReal ENNReal

end CurrentMain

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma familyLimitTrace_tendsto (s : X → I) (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => (τ (s n)).functional (u n)) (U : Filter X)
      (𝓝 ((familyLimitTrace τ U s).functional
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) :=
  ultraTraceValue_tendsto (fun n => τ (s n)) U u

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

lemma uniform_sup_ultralimit {X : Type uX} {I : Type uI} [Nonempty I]
    (U : Ultrafilter X) (f : X → I → ℝ) (M : ℝ)
    (h₀ : ∀ n i, 0 ≤ f n i) (hM : ∀ n i, f n i ≤ M) :
    (⨆ s : X → I, limUnder (U : Filter X) (fun n => f n (s n))) =
      limUnder (U : Filter X) (fun n => ⨆ i, f n i) := by
  have hb (n : X) : BddAbove (Set.range (f n)) := ⟨M, by rintro _ ⟨i,rfl⟩; exact hM n i⟩
  have hs₀ (n : X) : 0 ≤ ⨆ i, f n i := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (h₀ n i).trans (le_ciSup (hb n) i)
  have hsM (n : X) : (⨆ i, f n i) ≤ M := ciSup_le (hM n)
  have ht (s : X → I) := bounded_ultrafilter_tendsto U (fun n => f n (s n)) M
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h₀ n (s n))] using hM n (s n))
  have hst := bounded_ultrafilter_tendsto U (fun n => ⨆ i, f n i) M
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hs₀ n)] using hsM n)
  have hbound : BddAbove (Set.range (fun s : X → I =>
      limUnder (U : Filter X) (fun n => f n (s n)))) := by
    refine ⟨M,?_⟩
    rintro _ ⟨s,rfl⟩
    exact le_of_tendsto (ht s) (Eventually.of_forall (fun n => hM n (s n)))
  apply le_antisymm
  · apply ciSup_le
    intro s
    exact le_of_tendsto_of_tendsto (ht s) hst
      (Eventually.of_forall (fun n => le_ciSup (hb n) (s n)))
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hex (n : X) : ∃ i, (⨆ j, f n j) - ε < f n i :=
      exists_lt_of_lt_ciSup (sub_lt_self _ hε)
    choose s hs using hex
    have hle := le_of_tendsto_of_tendsto hst ((ht s).add_const ε)
      (Eventually.of_forall (fun n => by linarith [hs n]))
    exact hle.trans (add_le_add (le_ciSup hbound s) le_rfl)

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]

variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma familyQuotientMap_eq_zero (u : lp (fun _ : X => D) ∞) :
    (familyNullIdeal τ (U : Filter X)).quotientMap u = 0 ↔
      IsFamilyNull τ (U : Filter X) (fun n => u n) := by
  let J := familyNullIdeal τ (U : Filter X)
  change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ _
  exact (show J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal from
    Quotient.eq).trans (familyNull_mem τ _ u)

lemma traceTwoNorm_limitTrace_tendsto (s : X → I) (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => traceTwoNorm (τ (s n)) (u n)) (U : Filter X)
      (𝓝 (traceTwoNorm (familyLimitTrace τ U s)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  have ht := familyLimitTrace_tendsto τ U s (star u*u)
  rw [map_mul, ClosedStarIdeal.quotientMap_star] at ht
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)

lemma familyTwoNorm_limitTrace (u : lp (fun _ : X => D) ∞) :
    familyTwoNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => familyTwoNorm τ (u n)) := by
  have he (s : X → I) : traceTwoNorm (familyLimitTrace τ U s)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => traceTwoNorm (τ (s n)) (u n)) := by
    exact tendsto_nhds_unique (traceTwoNorm_limitTrace_tendsto τ U s u)
      (bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (traceTwoNorm_nonneg _ _)] using
          (traceTwoNorm_le_norm (τ (s n)) (u n)).trans
            (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)))
  simp only [familyTwoNorm, he]
  exact uniform_sup_ultralimit U (fun n i => traceTwoNorm (τ i) (u n)) ‖u‖
    (fun _ _ => traceTwoNorm_nonneg _ _) (fun n i =>
      (traceTwoNorm_le_norm (τ i) (u n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma familyTwoNorm_limitTrace_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => familyTwoNorm τ (u n)) (U : Filter X)
      (𝓝 (familyTwoNorm (familyLimitTrace τ U)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  rw [familyTwoNorm_limitTrace]
  exact bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTwoNorm_nonneg τ _)] using
      (familyTwoNorm_le_norm τ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma familyTraceNorm_limitTrace (u : lp (fun _ : X => D) ∞) :
    familyTraceNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => familyTraceNorm τ (u n)) := by
  have he (s : X → I) : ‖(familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter X)).quotientMap u)‖ =
      limUnder (U : Filter X) (fun n => ‖(τ (s n)).functional (u n)‖) := by
    exact tendsto_nhds_unique (familyLimitTrace_tendsto τ U s u).norm
      (bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
        simpa only [norm_norm] using (trace_norm_le_norm (τ (s n)) (u n)).trans
          (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)))
  simp only [familyTraceNorm, he]
  exact uniform_sup_ultralimit U (fun n i => ‖(τ i).functional (u n)‖) ‖u‖
    (fun _ _ => norm_nonneg _) (fun n i =>
      (trace_norm_le_norm (τ i) (u n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma familyTraceNorm_limitTrace_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => familyTraceNorm τ (u n)) (U : Filter X)
      (𝓝 (familyTraceNorm (familyLimitTrace τ U)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  rw [familyTraceNorm_limitTrace]
  exact bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTraceNorm_nonneg τ _)] using
      (familyTraceNorm_le_norm τ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))

lemma limitTrace_detects_zero (z : FamilyUltrapower τ U)
    (hz : ∀ s : X → I, traceTwoNorm (familyLimitTrace τ U s) z = 0) : z = 0 := by
  obtain ⟨u,rfl⟩ := (familyNullIdeal τ (U : Filter X)).quotientMap_surjective z
  apply (familyQuotientMap_eq_zero τ U u).mpr
  have ht := familyTwoNorm_limitTrace_tendsto τ U u
  have he : familyTwoNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) = 0 := by
    simp only [familyTwoNorm, hz, ciSup_const]
  change Tendsto _ _ (𝓝 0)
  simpa only [he] using ht

end

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]

lemma completionTrace_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop
      (𝓝 ((completionTrace τ i).functional ((familyCauchyNullIdeal τ).quotientMap u))) :=
  cauchyTrace_tendsto τ i u

lemma completionTwoNorm_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => traceTwoNorm (τ i) (u.1 n)) atTop
      (𝓝 (traceTwoNorm (completionTrace τ i) ((familyCauchyNullIdeal τ).quotientMap u))) := by
  have ht := completionTrace_tendsto τ i (star u*u)
  rw [map_mul, ClosedStarIdeal.quotientMap_star] at ht
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)

lemma completion_distance_tendsto_zero (u : familyCauchyAlgebra τ) :
    Tendsto (fun m : ℕ => familyTwoNorm (completionTrace τ)
      ((familyCauchyNullIdeal τ).quotientMap u - completionMap τ (u.1 m)))
      atTop (𝓝 0) := by
  apply (isFamilyNull_iff (completionTrace τ) atTop _).mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (isFamilyCauchy_iff τ _).mp u.2 (ε/2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with m hm
  refine lt_of_le_of_lt (ciSup_le fun i => ?_) (half_lt_self hε)
  have ht := completionTwoNorm_tendsto τ i (u-cauchyConstant τ (u.1 m))
  rw [map_sub] at ht
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (traceTwoNorm_le_family τ i _).trans (hN n hn m hm).le

theorem completion_uniform_dense (x : UniformTracialCompletion τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D, familyTwoNorm (completionTrace τ) (x-completionMap τ a) < ε := by
  obtain ⟨u,rfl⟩ := (familyCauchyNullIdeal τ).quotientMap_surjective x
  obtain ⟨m,hm⟩ := ((isFamilyNull_iff (completionTrace τ) atTop _).mp
    (completion_distance_tendsto_zero τ u) ε hε).exists
  exact ⟨u.1 m,hm⟩

end CurrentMain

namespace Pureness.ClosedStarIdeal

open scoped ComplexStarModule

variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (J : ClosedStarIdeal D)

lemma quotientMap_realPart (u : D) :
    J.quotientMap (realPart u : D) = (realPart (J.quotientMap u) : J.Quotient) := by
  have hs : J.quotientMap ((2 : ℝ)⁻¹ • (u+star u)) =
      (2 : ℝ)⁻¹ • J.quotientMap (u+star u) :=
    (J.quotientMap.toLinearMap.restrictScalars ℝ).map_smul _ _
  rw [realPart_apply_coe, realPart_apply_coe, hs, map_add, J.quotientMap_star]
  rfl

lemma exists_bounded_selfAdjoint_lift {p : J.Quotient} (hp : IsStarProjection p) :
    ∃ u : D, IsSelfAdjoint u ∧ ‖u‖ ≤ 2 ∧ J.quotientMap u = p := by
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep p (show (0 : ℝ) < 1 by norm_num)
  refine ⟨realPart v,(realPart v).property,?_,?_⟩
  · exact (realPart.norm_le v).trans
      (hvn.le.trans (by linarith [hp.norm_le p]))
  · rw [J.quotientMap_realPart, hv]
    exact hp.isSelfAdjoint.coe_realPart

end Pureness.ClosedStarIdeal

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section UltrapowerConstants

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma familyTwoNorm_ultrapowerMap (a : D) :
    familyTwoNorm (familyLimitTrace τ U) (familyUltrapowerMap τ U a) = familyTwoNorm τ a := by
  change familyTwoNorm (familyLimitTrace τ U)
    ((familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)) = _
  rw [familyTwoNorm_limitTrace]
  exact tendsto_nhds_unique
    (bounded_ultrafilter_tendsto U (fun _ => familyTwoNorm τ a) ‖a‖ (fun _ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTwoNorm_nonneg τ a)] using
        familyTwoNorm_le_norm τ a)) tendsto_const_nhds

end UltrapowerConstants

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.Diagonalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD uE uI uS uX

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)

lemma exists_coordinate_split (K : Finset D) {ε : ℝ} (hε : 0 < ε)
    {P : FamilyUltrapower τ U} (hP : IsStarProjection P)
    (hc : ∀ x ∈ K, familyTwoNorm (familyLimitTrace τ U)
      (P * familyUltrapowerMap τ U x - familyUltrapowerMap τ U x * P) < ε)
    (hh : ∀ x ∈ K, familyTraceNorm (familyLimitTrace τ U)
      (P * familyUltrapowerMap τ U x - (1/2 : ℂ) • familyUltrapowerMap τ U x) < ε) :
    ∃ b : D, IsSelfAdjoint b ∧ ‖b‖ ≤ 2 ∧ familyTwoNorm τ (b*b-b) < ε ∧
      ∀ x ∈ K, familyTwoNorm τ (b*x-x*b) < ε ∧
        familyTraceNorm τ (b*x-(1/2 : ℂ) • x) < ε := by
  let q := (familyNullIdeal τ (U : Filter X)).quotientMap
  obtain ⟨c,hcsa,hcn,hcq⟩ :=
    (familyNullIdeal τ (U : Filter X)).exists_bounded_selfAdjoint_lift hP
  have hd : IsFamilyNull τ (U : Filter X) (fun j => c j*c j-c j) := by
    apply (familyQuotientMap_eq_zero τ U (c*c-c)).mp
    rw [map_sub, map_mul, hcq, hP.isIdempotentElem.eq, sub_self]
  have hc' (x : D) (hx : x ∈ K) : ∀ᶠ j in (U : Filter X),
      familyTwoNorm τ (c j*x-x*c j) < ε := by
    have ht := familyTwoNorm_limitTrace_tendsto τ U
      (c * boundedFamilyConstant x - boundedFamilyConstant x * c)
    have he : q (c * boundedFamilyConstant x - boundedFamilyConstant x * c) =
        P * familyUltrapowerMap τ U x - familyUltrapowerMap τ U x * P := by
      rw [map_sub, map_mul, map_mul]
      exact congrArg₂ (fun a b => a * familyUltrapowerMap τ U x -
        familyUltrapowerMap τ U x * b) hcq hcq
    change Tendsto (fun j => familyTwoNorm τ (c j*x-x*c j)) _ (𝓝 (familyTwoNorm _
      (q (c * boundedFamilyConstant x - boundedFamilyConstant x * c)))) at ht
    rw [he] at ht
    exact ht.eventually (gt_mem_nhds (hc x hx))
  have hh' (x : D) (hx : x ∈ K) : ∀ᶠ j in (U : Filter X),
      familyTraceNorm τ (c j*x-(1/2 : ℂ) • x) < ε := by
    have ht := familyTraceNorm_limitTrace_tendsto τ U
      (c * boundedFamilyConstant x - (1/2 : ℂ) • boundedFamilyConstant x)
    have he : q (c * boundedFamilyConstant x - (1/2 : ℂ) • boundedFamilyConstant x) =
        P * familyUltrapowerMap τ U x - (1/2 : ℂ) • familyUltrapowerMap τ U x := by
      rw [map_sub, map_mul, map_smul]
      exact congrArg (fun a => a * familyUltrapowerMap τ U x -
        (1/2 : ℂ) • familyUltrapowerMap τ U x) hcq
    change Tendsto (fun j => familyTraceNorm τ (c j*x-(1/2 : ℂ) • x)) _
      (𝓝 (familyTraceNorm _ (q (c * boundedFamilyConstant x -
        (1/2 : ℂ) • boundedFamilyConstant x)))) at ht
    rw [he] at ht
    exact ht.eventually (gt_mem_nhds (hh x hx))
  have hevent : ∀ᶠ j in (U : Filter X), familyTwoNorm τ (c j*c j-c j) < ε ∧
      ∀ x ∈ K, familyTwoNorm τ (c j*x-x*c j) < ε ∧
        familyTraceNorm τ (c j*x-(1/2 : ℂ) • x) < ε :=
    ((isFamilyNull_iff τ _ _).mp hd ε hε).and
      ((eventually_all_finset K).mpr (fun x hx => (hc' x hx).and (hh' x hx)))
  obtain ⟨j,hj⟩ := hevent.exists
  refine ⟨c j,?_,(lp.norm_apply_le_norm ENNReal.top_ne_zero c j).trans hcn,hj⟩
  exact congrArg (fun a : lp (fun _ : X => D) ∞ => a j) hcsa.star_eq

end

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter ℕ)

lemma projection_of_bounded_sequence (c : lp (fun _ : ℕ => D) ∞)
    (hsa : ∀ n, IsSelfAdjoint (c n))
    (hd : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*c n-c n)) :
    IsStarProjection ((familyNullIdeal τ (U : Filter ℕ)).quotientMap c) := by
  have hcsa : star c = c := by
    apply lp.ext
    funext n
    exact (hsa n).star_eq
  refine ⟨?_,?_⟩
  · have he := (familyQuotientMap_eq_zero τ U (c*c-c)).mpr hd
    rw [map_sub, map_mul, sub_eq_zero] at he
    exact he
  · change star ((familyNullIdeal τ (U : Filter ℕ)).quotientMap c) = _
    rw [← ClosedStarIdeal.quotientMap_star,hcsa]

lemma commute_of_null_sequence (c : lp (fun _ : ℕ => D) ∞) (a : D)
    (hc : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*a-a*c n)) :
    (familyNullIdeal τ (U : Filter ℕ)).quotientMap c * familyUltrapowerMap τ U a =
      familyUltrapowerMap τ U a * (familyNullIdeal τ (U : Filter ℕ)).quotientMap c := by
  let v : lp (fun _ : ℕ => D) ∞ := boundedFamilyConstant a
  have hv : IsFamilyNull τ (U : Filter ℕ) (fun n => (c*v-v*c) n) := by
    exact hc
  have he := (familyQuotientMap_eq_zero τ U (c*v-v*c)).mpr hv
  rw [map_sub, map_mul, map_mul, sub_eq_zero] at he
  exact he

lemma halftrace_of_null_sequence (c : lp (fun _ : ℕ => D) ∞) (a : D)
    (hh : Tendsto (fun n => familyTraceNorm τ (c n*a-(1/2 : ℂ) • a))
      (U : Filter ℕ) (𝓝 0)) (s : ℕ → I) :
    (familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter ℕ)).quotientMap c * familyUltrapowerMap τ U a) =
      (1/2 : ℂ) * (familyLimitTrace τ U s).functional (familyUltrapowerMap τ U a) := by
  let q := (familyNullIdeal τ (U : Filter ℕ)).quotientMap
  have hz : familyTraceNorm (familyLimitTrace τ U)
      (q (c*boundedFamilyConstant a-(1/2 : ℂ) • boundedFamilyConstant a)) = 0 :=
    tendsto_nhds_unique (familyTraceNorm_limitTrace_tendsto τ U _) hh
  have hs : (familyLimitTrace τ U s).functional
      (q (c*boundedFamilyConstant a-(1/2 : ℂ) • boundedFamilyConstant a)) = 0 :=
    norm_eq_zero.mp (le_antisymm ((traceNorm_le_family _ s _).trans hz.le) (norm_nonneg _))
  rw [map_sub, map_mul, map_smul, map_sub, map_smul, smul_eq_mul, sub_eq_zero] at hs
  exact hs

theorem diagonalize_finite_splittings (hfree : (U : Filter ℕ) ≤ atTop)
    (x : ℕ → D)
    (hfinite : ∀ n : ℕ, ∀ ε : ℝ, 0 < ε → ∃ P : FamilyUltrapower τ U,
      IsStarProjection P ∧ ∀ k ≤ n,
        familyTwoNorm (familyLimitTrace τ U)
          (P * familyUltrapowerMap τ U (x k) - familyUltrapowerMap τ U (x k) * P) < ε ∧
        familyTraceNorm (familyLimitTrace τ U)
          (P * familyUltrapowerMap τ U (x k) -
            (1/2 : ℂ) • familyUltrapowerMap τ U (x k)) < ε) :
    ∃ p : FamilyUltrapower τ U, IsStarProjection p ∧ ∀ k : ℕ,
      p * familyUltrapowerMap τ U (x k) = familyUltrapowerMap τ U (x k) * p ∧
      ∀ s : ℕ → I, (familyLimitTrace τ U s).functional (p * familyUltrapowerMap τ U (x k)) =
        (1/2 : ℂ) * (familyLimitTrace τ U s).functional (familyUltrapowerMap τ U (x k)) := by
  classical
  let e : ℕ → ℝ := fun n => 1 / ((n : ℝ)+1)
  have hepos (n : ℕ) : 0 < e n := by dsimp [e]; positivity
  have hetend : Tendsto e atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hb (n : ℕ) : ∃ b : D, IsSelfAdjoint b ∧ ‖b‖ ≤ 2 ∧
      familyTwoNorm τ (b*b-b) < e n ∧ ∀ k ≤ n,
        familyTwoNorm τ (b*x k-x k*b) < e n ∧
        familyTraceNorm τ (b*x k-(1/2 : ℂ) • x k) < e n := by
    obtain ⟨P,hP,hPtest⟩ := hfinite n (e n) (hepos n)
    have hm {a : D} (ha : a ∈ (Finset.range (n+1)).image x) :
        ∃ k ≤ n, x k = a := by
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
      exact ⟨k,Nat.lt_succ_iff.mp (Finset.mem_range.mp hk),rfl⟩
    obtain ⟨b,hbsa,hbn,hbd,hbt⟩ := exists_coordinate_split τ U
      ((Finset.range (n+1)).image x) (hepos n) hP
      (by intro a ha; obtain ⟨k,hk,rfl⟩ := hm ha; exact (hPtest k hk).1)
      (by intro a ha; obtain ⟨k,hk,rfl⟩ := hm ha; exact (hPtest k hk).2)
    refine ⟨b,hbsa,hbn,hbd,fun k hk => hbt (x k) ?_⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk),rfl⟩
  choose b hbsa hbn hbd hbt using hb
  let c : lp (fun _ : ℕ => D) ∞ :=
    ⟨b,memℓp_infty_iff.mpr ⟨2,by rintro _ ⟨n,rfl⟩; exact hbn n⟩⟩
  have hd : IsFamilyNull τ (U : Filter ℕ) (fun n => c n*c n-c n) := by
    exact (squeeze_zero (fun _ => familyTwoNorm_nonneg τ _)
      (fun n => (hbd n).le) hetend).mono_left hfree
  refine ⟨(familyNullIdeal τ (U : Filter ℕ)).quotientMap c,
    projection_of_bounded_sequence τ U c hbsa hd,fun k => ⟨?_,?_⟩⟩
  · apply commute_of_null_sequence τ U c (x k)
    apply Tendsto.mono_left _ hfree
    apply squeeze_zero' (Eventually.of_forall (fun _ => familyTwoNorm_nonneg τ _)) _ hetend
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hbt n k hn).1.le
  · apply halftrace_of_null_sequence τ U c (x k)
    apply Tendsto.mono_left _ hfree
    apply squeeze_zero' (Eventually.of_forall (fun _ => familyTraceNorm_nonneg τ _)) _ hetend
    filter_upwards [eventually_ge_atTop k] with n hn
    exact (hbt n k hn).2.le

end

section

open Pureness

open scoped ComplexOrder

section DenseUnitaryExtension

variable {A : Type uA} {E : Type uE} [CStarAlgebra A] [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma linearMap_zero_of_dense_unitaries (u : ℕ → unitary A) (hu : DenseRange u)
    (L : A →ₗ[ℂ] E) (hL : Continuous L) (hzero : ∀ n, L (u n : A) = 0) :
    ∀ a : A, L a = 0 := by
  have hunit : ∀ v : unitary A, L (v : A) = 0 := by
    exact congrFun (hu.equalizer (hL.comp continuous_subtype_val) continuous_const
      (funext hzero))
  have hspan : Submodule.span ℂ (unitary A : Set A) ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    intro a ha
    exact hunit ⟨a,ha⟩
  rw [CStarAlgebra.span_unitary A] at hspan
  intro a
  exact hspan (Submodule.mem_top : a ∈ (⊤ : Submodule ℂ A))

end DenseUnitaryExtension

variable {A : Type uA} {E : Type uE} {S : Type uS} [CStarAlgebra A] [CStarAlgebra E]

variable [PartialOrder E] [StarOrderedRing E]

lemma splitting_of_dense_unitaries (ι : A →⋆ₐ[ℂ] E) (σ : S → TracialState E)
    (p : E) (u : ℕ → unitary A) (hu : DenseRange u)
    (htest : ∀ n, p * ι (u n : A) = ι (u n : A) * p ∧
      ∀ s, (σ s).functional (p * ι (u n : A)) = (1/2 : ℂ) * (σ s).functional (ι (u n : A))) :
    ∀ a : A, p * ι a = ι a * p ∧
      ∀ s, (σ s).functional (p * ι a) = (1/2 : ℂ) * (σ s).functional (ι a) := by
  have hι : Continuous ι := AddMonoidHomClass.continuous_of_bound ι 1 (fun a => by
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))
  let L : A →ₗ[ℂ] E :=
    (LinearMap.mulLeft ℂ p - LinearMap.mulRight ℂ p).comp ι.toLinearMap
  have hc : ∀ a, L a = 0 := linearMap_zero_of_dense_unitaries u hu L
    ((continuous_const.mul hι).sub (hι.mul continuous_const))
    (fun n => sub_eq_zero.mpr (htest n).1)
  have hh (s : S) : ∀ a : A,
      (σ s).functional (p * ι a) - (1/2 : ℂ) * (σ s).functional (ι a) = 0 := by
    let M : A →ₗ[ℂ] ℂ :=
      (σ s).functional.toLinearMap.comp ((LinearMap.mulLeft ℂ p).comp ι.toLinearMap) -
        (1/2 : ℂ) • ((σ s).functional.toLinearMap.comp ι.toLinearMap)
    have hσ : Continuous (σ s).functional := map_continuous (σ s).functional
    exact linearMap_zero_of_dense_unitaries u hu M
      ((hσ.comp (continuous_const.mul hι)).sub (continuous_const.mul (hσ.comp hι)))
      (fun n => sub_eq_zero.mpr ((htest n).2 s))
  exact fun a => ⟨sub_eq_zero.mp (hc a),fun s => sub_eq_zero.mp (hh s a)⟩

end

section

open Pureness

open scoped ComplexOrder

variable {E : Type uE} {S : Type uS} [CStarAlgebra E] [PartialOrder E] [StarOrderedRing E]

variable (σ : S → TracialState E) [Nonempty S]

lemma commutator_twoNorm_bound {p a b : E} (hp : ‖p‖ ≤ 1) (hb : p*b=b*p) :
    familyTwoNorm σ (p*a-a*p) ≤ 2 * familyTwoNorm σ (a-b) := by
  have he : p*a-a*p = p*(a-b)-(a-b)*p := by
    rw [mul_sub,sub_mul,hb]
    noncomm_ring
  rw [he]
  have h₁ := familyTwoNorm_mul_left σ p (a-b)
  have h₂ := familyTwoNorm_mul_right σ (a-b) p
  have hn := familyTwoNorm_nonneg σ (a-b)
  have ht := familyTwoNorm_sub_le σ (p*(a-b)) ((a-b)*p)
  nlinarith

lemma coefficient_half_error_bound (τ : TracialState E) {p a b : E} (hp : ‖p‖ ≤ 1)
    (hb : τ.functional (p*b) = (1/2 : ℂ) * τ.functional b) :
    ‖τ.functional (p*a) - (1/2 : ℂ) * τ.functional a‖ ≤
      (3/2 : ℝ) * traceTwoNorm τ (a-b) := by
  have he : τ.functional (p*a) - (1/2 : ℂ) * τ.functional a =
      τ.functional (p*(a-b)) - (1/2 : ℂ) * τ.functional (a-b) := by
    rw [mul_sub,map_sub,map_sub,hb]
    ring
  rw [he]
  have hn := traceTwoNorm_nonneg τ (a-b)
  have h₁ := (trace_norm_le_twoNorm τ (p*(a-b))).trans
    (traceTwoNorm_mul_left τ p (a-b))
  have h₂ : ‖(1/2 : ℂ) * τ.functional (a-b)‖ ≤ (1/2 : ℝ) * traceTwoNorm τ (a-b) := by
    rw [norm_mul]
    norm_num only [norm_div,norm_one,Complex.norm_ofNat]
    exact mul_le_mul_of_nonneg_left (trace_norm_le_twoNorm τ (a-b)) (by norm_num)
  have ht := norm_sub_le (τ.functional (p*(a-b))) ((1/2 : ℂ) * τ.functional (a-b))
  nlinarith

lemma splitting_of_uniform_approximants
    (hdetect : ∀ z : E, (∀ s, traceTwoNorm (σ s) z = 0) → z = 0)
    {p x : E} (hp : IsStarProjection p)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ b : E, familyTwoNorm σ (x-b) < ε ∧
      p*b=b*p ∧ ∀ s, (σ s).functional (p*b) = (1/2 : ℂ) * (σ s).functional b) :
    p*x=x*p ∧ ∀ s, (σ s).functional (p*x) = (1/2 : ℂ) * (σ s).functional x := by
  have hn : familyTwoNorm σ (p*x-x*p) = 0 := by
    apply le_antisymm _ (familyTwoNorm_nonneg σ _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hb,hbc,_⟩ := happrox (ε/4) (by linarith)
    have ht := commutator_twoNorm_bound σ (a := x) (hp.norm_le p) hbc
    change familyTwoNorm σ (p*x-x*p) ≤ 0+ε
    linarith
  refine ⟨sub_eq_zero.mp (hdetect _ (fun s => ?_)),fun s => ?_⟩
  · exact le_antisymm ((traceTwoNorm_le_family σ s _).trans hn.le) (traceTwoNorm_nonneg _ _)
  · apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b,hb,_,hbh⟩ := happrox (ε/4) (by linarith)
    have ht := coefficient_half_error_bound (σ s) (a := x) (hp.norm_le p) (hbh s)
    have hl := traceTwoNorm_le_family σ s (x-b)
    change ‖(σ s).functional (p*x) - (1/2 : ℂ) * (σ s).functional x‖ ≤ 0+ε
    linarith

end

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

variable {A : Type uA} {I : Type uI} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [Nontrivial A] [TopologicalSpace.SeparableSpace A]

variable (τ : I → TracialState A) [Nonempty I] (U : Ultrafilter ℕ)

theorem completion_central_splitting_of_finite_stages
    (hfree : (U : Filter ℕ) ≤ atTop)
    (hfinite : ∀ (K : Finset (unitary A)) (ε : ℝ), 0 < ε →
      ∃ P : FamilyUltrapower (completionTrace τ) U, IsStarProjection P ∧ ∀ u ∈ K,
        familyTwoNorm (familyLimitTrace (completionTrace τ) U)
          (P * familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A)) -
           familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A)) * P) < ε ∧
        familyTraceNorm (familyLimitTrace (completionTrace τ) U)
          (P * familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A)) -
           (1/2 : ℂ) • familyUltrapowerMap (completionTrace τ) U (completionMap τ (u : A))) < ε) :
    ∃ p : FamilyUltrapower (completionTrace τ) U, IsStarProjection p ∧
      ∀ x : UniformTracialCompletion τ,
        p * familyUltrapowerMap (completionTrace τ) U x =
          familyUltrapowerMap (completionTrace τ) U x * p ∧
        ∀ s : ℕ → I, (familyLimitTrace (completionTrace τ) U s).functional
          (p * familyUltrapowerMap (completionTrace τ) U x) =
          (1/2 : ℂ) * (familyLimitTrace (completionTrace τ) U s).functional
            (familyUltrapowerMap (completionTrace τ) U x) := by
  classical
  obtain ⟨u,hu⟩ := TopologicalSpace.exists_dense_seq (unitary A)
  let j : A →⋆ₐ[ℂ] FamilyUltrapower (completionTrace τ) U :=
    (familyUltrapowerMap (completionTrace τ) U).comp (completionMap τ)
  have hstage (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
      ∃ P : FamilyUltrapower (completionTrace τ) U, IsStarProjection P ∧ ∀ k ≤ n,
        familyTwoNorm (familyLimitTrace (completionTrace τ) U)
          (P * j (u k : A) - j (u k : A) * P) < ε ∧
        familyTraceNorm (familyLimitTrace (completionTrace τ) U)
          (P * j (u k : A) - (1/2 : ℂ) • j (u k : A)) < ε := by
    obtain ⟨P,hP,htest⟩ := hfinite ((Finset.range (n+1)).image u) ε hε
    refine ⟨P,hP,fun k hk => htest (u k) ?_⟩
    exact Finset.mem_image.mpr ⟨k,Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk),rfl⟩
  obtain ⟨p,hp,hptest⟩ := diagonalize_finite_splittings (completionTrace τ) U hfree
    (fun n => completionMap τ (u n : A)) hstage
  have hA := splitting_of_dense_unitaries j (familyLimitTrace (completionTrace τ) U) p u hu hptest
  refine ⟨p,hp,fun x => ?_⟩
  apply splitting_of_uniform_approximants (familyLimitTrace (completionTrace τ) U)
    (limitTrace_detects_zero (completionTrace τ) U) hp
  intro ε hε
  obtain ⟨a,ha⟩ := completion_uniform_dense τ x hε
  refine ⟨j a,?_,(hA a).1,(hA a).2⟩
  change familyTwoNorm (familyLimitTrace (completionTrace τ) U)
    (familyUltrapowerMap (completionTrace τ) U x -
      familyUltrapowerMap (completionTrace τ) U (completionMap τ a)) < ε
  rw [← map_sub,familyTwoNorm_ultrapowerMap]
  exact ha

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SimpleIdeals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uC uι

namespace Pureness

section

open Filter Topology

variable {A : Type uA} [NormedRing A]

theorem closure_span_singleton_eq_univ (hsimple : TopologicallySimple A)
    (h : A) (hh : h ≠ 0) :
    closure (TwoSidedIdeal.span {h} : Set A) = Set.univ := by
  let I : TwoSidedIdeal A := TwoSidedIdeal.span {h}
  have hclosed : IsClosed (closedTwoSidedIdeal I : Set A) := by
    rw [coe_closedTwoSidedIdeal]
    exact isClosed_closure
  have hmem : h ∈ closedTwoSidedIdeal I := by
    rw [← SetLike.mem_coe, coe_closedTwoSidedIdeal]
    exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton h))
  rcases hsimple (closedTwoSidedIdeal I) hclosed with hbot | htop
  · rw [hbot] at hmem
    exact (hh ((TwoSidedIdeal.mem_bot A).mp hmem)).elim
  · have heq := congrArg (fun J : TwoSidedIdeal A => (J : Set A)) htop
    simpa only [coe_closedTwoSidedIdeal, TwoSidedIdeal.coe_top] using heq

end

section

variable {A : Type uA} [Ring A]

theorem exists_finiteIdealSum {h x : A} (hx : x ∈ TwoSidedIdeal.span {h}) :
    ∃ l : List (A × A), finiteIdealSum h l = x := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    have : x = h := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨[(1, 1)], by simp [finiteIdealSum]⟩
  | zero => exact ⟨[], rfl⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨l, rfl⟩ := ihx
    obtain ⟨m, rfl⟩ := ihy
    exact ⟨l ++ m, by simp [finiteIdealSum]⟩
  | neg x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (-p.1, p.2)), ?_⟩
    clear hx
    induction l with
    | nil => simp [finiteIdealSum]
    | cons p l ih =>
      simp_all [finiteIdealSum, List.map_map, Function.comp_def, neg_add_rev, add_comm]
  | left_absorb a x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (a * p.1, p.2)), ?_⟩
    simp [finiteIdealSum, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]
  | right_absorb b x hx ih =>
    obtain ⟨l, rfl⟩ := ih
    refine ⟨l.map (fun p => (p.1, p.2 * b)), ?_⟩
    simp only [finiteIdealSum, List.map_map, Function.comp_def]
    simpa only [mul_assoc] using
      (List.sum_map_mul_right (l := l) (f := fun p => p.1 * h * p.2) (r := b))

end

section

open Topology

variable {A : Type uA} [NormedRing A] [CompleteSpace A]

theorem exists_invertible_finiteIdealSum (hsimple : TopologicallySimple A)
    (h : A) (hh : h ≠ 0) :
    ∃ l : List (A × A), IsUnit (finiteIdealSum h l) := by
  have h1 : (1 : A) ∈ closure (TwoSidedIdeal.span {h} : Set A) := by
    rw [closure_span_singleton_eq_univ hsimple h hh]
    exact Set.mem_univ _
  have hn : {x : A | IsUnit x} ∈ 𝓝 (1 : A) := Units.isOpen.mem_nhds isUnit_one
  obtain ⟨x, hxunit, hxspan⟩ := mem_closure_iff_nhds.mp h1 _ hn
  obtain ⟨l, hl⟩ := exists_finiteIdealSum hxspan
  exact ⟨l, hl.symm ▸ hxunit⟩

end

section

variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem normalize_fullness_sum (I : Finset ι) (h : A) (hh : 0 ≤ h) (t : ι → A)
    (hunit : IsUnit (∑ i ∈ I, star (t i) * h * t i)) :
    ∃ s : ι → A, ∑ i ∈ I, star (s i) * h * s i = 1 := by
  let q := ∑ i ∈ I, star (t i) * h * t i
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => star_left_conjugate_nonneg hh (t i))
  obtain ⟨u, hu⟩ := (CFC.isUnit_sqrt_iff q hq).mpr hunit
  have hfactor : q = star (u : A) * (u : A) := by
    rw [hu, (CFC.sqrt_nonneg q).star_eq, CFC.sqrt_mul_sqrt_self q hq]
  have hnormalize : star (↑(u⁻¹) : A) * q * (↑(u⁻¹) : A) = 1 := by
    rw [hfactor]
    calc
      star (↑(u⁻¹) : A) * (star (u : A) * (u : A)) * (↑(u⁻¹) : A) =
          star ((u : A) * (↑(u⁻¹) : A)) * ((u : A) * (↑(u⁻¹) : A)) := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by simp
  refine ⟨fun i => t i * (↑(u⁻¹) : A), ?_⟩
  calc
    (∑ i ∈ I, star (t i * (↑(u⁻¹) : A)) * h * (t i * (↑(u⁻¹) : A))) =
        star (↑(u⁻¹) : A) * q * (↑(u⁻¹) : A) := by
      simp only [q, Finset.mul_sum, Finset.sum_mul, star_mul, mul_assoc]
    _ = 1 := hnormalize

end

section

open scoped WithCStarModule InnerProductSpace

variable {A : Type uA} {ι : Type uι} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] [Fintype ι]

theorem invertible_positive_sum_of_invertible_sum (h : A) (hh : 0 ≤ h) (r t : ι → A)
    (hS : IsUnit (∑ i, r i * h * t i)) :
    IsUnit (∑ i, star (t i) * h * t i) := by
  nontriviality A
  let S := ∑ i, r i * h * t i
  let q := ∑ i, star (t i) * h * t i
  let x : C⋆ᵐᵒᵈ(A, ι → A) := (WithCStarModule.equiv A _).symm (fun i => r i * CFC.sqrt h)
  let y : C⋆ᵐᵒᵈ(A, ι → A) := (WithCStarModule.equiv A _).symm (fun i => star (t i) * CFC.sqrt h)
  have hsqrt : star (CFC.sqrt h) = CFC.sqrt h := (CFC.sqrt_nonneg h).star_eq
  have hsquare (z : A) : CFC.sqrt h * (CFC.sqrt h * z) = h * z := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self h hh]
  have hxy : ⟪x, y⟫_A = star S := by
    simp [x, y, S, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, hh.star_eq, mul_assoc, hsquare]
  have hyx : ⟪y, x⟫_A = S := by
    simp [x, y, S, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, mul_assoc, hsquare]
  have hyy : ⟪y, y⟫_A = q := by
    simp [y, q, WithCStarModule.pi_inner, WithCStarModule.inner_def,
      hsqrt, mul_assoc, hsquare]
  have hbound : star S * S ≤ ‖x‖ ^ 2 • q := by
    simpa only [hxy, hyx, hyy] using (CStarModule.inner_mul_inner_swap_le (A := A) (x := x) (y := y))
  have hpos : IsStrictlyPositive (star S * S) :=
    IsStrictlyPositive.iff_of_unital.mpr ⟨star_mul_self_nonneg S, hS.star.mul hS⟩
  have hunit : IsUnit (‖x‖ ^ 2 • q) := CStarAlgebra.isUnit_of_le _ hbound hpos
  have hx : x ≠ 0 := by
    intro hx
    have hzero : S = 0 := by simpa [hx] using hyx.symm
    have hS' : IsUnit S := hS
    exact not_isUnit_zero (hzero ▸ hS')
  have hc : ‖x‖ ^ 2 ≠ (0 : ℝ) := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
  have hcunit : IsUnit (algebraMap ℝ A (‖x‖ ^ 2)) :=
    (isUnit_iff_ne_zero.mpr hc).map (algebraMap ℝ A)
  rw [Algebra.smul_def] at hunit
  obtain ⟨u, hu⟩ := hcunit
  have huq := u⁻¹.isUnit.mul hunit
  simpa only [← hu, ← mul_assoc, Units.inv_mul, one_mul] using huq

end

section

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem fullness (hsimple : TopologicallySimple A) (h : A) (hh : 0 ≤ h) (hne : h ≠ 0) :
    ∃ n : ℕ, ∃ s : Fin n → A, ∑ i, star (s i) * h * s i = 1 := by
  obtain ⟨l, hl⟩ := exists_invertible_finiteIdealSum hsimple h hne
  have hrep : finiteIdealSum h l = ∑ i : Fin l.length, (l.get i).1 * h * (l.get i).2 := by
    have heq := congrArg (fun v : List (A × A) => finiteIdealSum h v) (List.ofFn_get l)
    simpa only [finiteIdealSum, List.map_ofFn, List.sum_ofFn, Function.comp_apply] using heq.symm
  have hunit : IsUnit (∑ i : Fin l.length, star (l.get i).2 * h * (l.get i).2) :=
    invertible_positive_sum_of_invertible_sum h hh
      (fun i : Fin l.length => (l.get i).1) (fun i => (l.get i).2) (hrep ▸ hl)
  obtain ⟨s, hs⟩ := normalize_fullness_sum Finset.univ h hh (fun i : Fin l.length => (l.get i).2) hunit
  exact ⟨l.length, s, hs⟩

end

section

open scoped ComplexOrder

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

namespace TracialState

theorem conjugate_le (τ : TracialState A) (h : A) (hh : 0 ≤ h) (s : A) :
    τ.functional (star s * h * s) ≤ ‖s * star s‖ • τ.functional h := by
  have hsqrt : star (CFC.sqrt h) = CFC.sqrt h := (CFC.sqrt_nonneg h).star_eq
  have hsquare (z : A) : CFC.sqrt h * (CFC.sqrt h * z) = h * z := by
    rw [← mul_assoc, CFC.sqrt_mul_sqrt_self h hh]
  have heq : τ.functional (star s * h * s) =
      τ.functional (CFC.sqrt h * (s * star s) * CFC.sqrt h) := by
    calc
      τ.functional (star s * h * s) =
          τ.functional ((star s * CFC.sqrt h) * (CFC.sqrt h * s)) := by
        simp only [mul_assoc, hsquare]
      _ = τ.functional ((CFC.sqrt h * s) * (star s * CFC.sqrt h)) := τ.tracial _ _
      _ = τ.functional (CFC.sqrt h * (s * star s) * CFC.sqrt h) := by simp only [mul_assoc]
  have hb : CFC.sqrt h * (s * star s) * CFC.sqrt h ≤ ‖s * star s‖ • h := by
    simpa only [hsqrt, CFC.sqrt_mul_sqrt_self h hh] using
      (CStarAlgebra.star_left_conjugate_le_norm_smul
        (a := CFC.sqrt h) (b := s * star s) (mul_star_self_nonneg s).isSelfAdjoint)
  rw [heq, ← τ.functional.map_smul_of_tower]
  exact τ.functional.monotone hb

theorem faithful (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hzero : τ.functional h = 0) : h = 0 := by
  by_contra hne
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hne
  have hz (i : Fin n) : τ.functional (star (s i) * h * s i) = 0 := by
    apply le_antisymm
    · simpa only [hzero, smul_zero] using τ.conjugate_le h hh (s i)
    · exact τ.functional.map_nonneg (star_left_conjugate_nonneg hh (s i))
  have h1 : τ.functional 1 = 0 := by
    rw [← hs, map_sum]
    exact Finset.sum_eq_zero (fun i _ => hz i)
  exact one_ne_zero (τ.normalized.symm.trans h1)

end TracialState

end

section

open scoped ComplexOrder ENNReal NNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma normalizePositive_nonneg (a : A) (ha : 0 ≤ a) : 0 ≤ normalizePositive a :=
  smul_nonneg (inv_nonneg.mpr (norm_nonneg a)) ha

omit [PartialOrder A] [StarOrderedRing A] in
lemma normalizePositive_norm_le (a : A) : ‖normalizePositive a‖ ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · simp [normalizePositive, norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.mpr ha)]

lemma normalizedRoot_nonneg (a : A) (j : ℕ) : 0 ≤ normalizedRoot a j := CFC.nnrpow_nonneg

lemma normalizedRoot_le_one (a : A) (ha : 0 ≤ a) (j : ℕ) : normalizedRoot a j ≤ 1 := by
  apply (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg a j)).mp
  unfold normalizedRoot
  rw [CFC.nnrpow_eq_pow, CFC.norm_nnrpow _ (by positivity) (normalizePositive_nonneg a ha)]
  exact Real.rpow_le_one (norm_nonneg _) (normalizePositive_norm_le a) (by positivity)

lemma normalized_trace_le_rank (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    ENNReal.ofReal (τ.functional (normalizePositive a)).re ≤ normalizedRootRank τ a := by
  have h := le_iSup (fun j : ℕ => ENNReal.ofReal (τ.functional (normalizedRoot a j)).re) 0
  simpa [normalizedRootRank, normalizedRoot, CFC.nnrpow_one _ (normalizePositive_nonneg a ha)] using h

lemma normalizedRoot_monotone (a : A) (ha : 0 ≤ a) : Monotone (normalizedRoot a) := by
  intro j k hjk
  have hjpos : 0 < ((j : ℝ≥0) + 1)⁻¹ := by positivity
  have hkpos : 0 < ((k : ℝ≥0) + 1)⁻¹ := by positivity
  have hexp : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ := by
    apply inv_anti₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hjk 1
  simp only [normalizedRoot, CFC.nnrpow_eq_pow, CFC.nnrpow_def]
  apply cfcₙ_mono
  · intro z hz
    have hz1 : z ≤ 1 :=
      (NonUnitalIsometricContinuousFunctionalCalculus.quasispectrum_le _ hz
        (normalizePositive_nonneg a ha)).trans (by exact_mod_cast normalizePositive_norm_le a)
    by_cases hz0 : z = 0
    · subst z
      change (0 : ℝ≥0) ^ (((j : ℝ≥0) + 1)⁻¹ : ℝ) ≤
        (0 : ℝ≥0) ^ (((k : ℝ≥0) + 1)⁻¹ : ℝ)
      rw [NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos)),
        NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))]
    · apply NNReal.rpow_le_rpow_of_exponent_ge (pos_iff_ne_zero.mpr hz0) hz1
      exact_mod_cast hexp
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact (NNReal.continuous_nnrpow_const _).continuousOn
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hjpos))
  · exact NNReal.zero_rpow (by exact_mod_cast (ne_of_gt hkpos))

lemma normalizedRootRank_tendsto (τ : TracialState A) (a : A) (ha : 0 ≤ a) :
    Filter.Tendsto (fun j : ℕ => ENNReal.ofReal (τ.functional (normalizedRoot a j)).re)
      Filter.atTop (nhds (normalizedRootRank τ a)) := by
  apply tendsto_atTop_iSup
  intro j k hjk
  apply ENNReal.ofReal_le_ofReal
  exact (Complex.le_def.mp (τ.functional.monotone (normalizedRoot_monotone a ha hjk))).1

end

open Filter Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma hereditary_sqrt_mem {h a : A} (hh : 0 ≤ h) (ha : 0 ≤ a)
    (ham : a ∈ hereditaryCarrier h) : CFC.sqrt a ∈ hereditaryCarrier h := by
  change CFC.sqrt a ∈ hereditarySubalgebra h hh
  rw [CFC.sqrt_eq_real_sqrt a ha]
  exact cfcₙ_mem Real.sqrt (show a ∈ hereditarySubalgebra h hh from ham)

lemma self_mem_hereditary (h : A) (hh : 0 ≤ h) : h ∈ hereditaryCarrier h := by
  have hm : h * h ∈ hereditaryCarrier h := subset_closure ⟨1, by simp⟩
  have hs := hereditary_sqrt_mem hh (by simpa only [hh.star_eq] using star_mul_self_nonneg h) hm
  simpa only [CFC.sqrt_mul_self h hh] using hs

lemma normalizedRoot_mem_hereditary {h a : A} (hh : 0 ≤ h)
    (ha : a ∈ hereditaryCarrier h) (ha0 : 0 ≤ a) (j : ℕ) :
    normalizedRoot a j ∈ hereditaryCarrier h := by
  change normalizedRoot a j ∈ hereditarySubalgebra h hh
  unfold normalizedRoot
  rw [CFC.nnrpow_eq_pow, CFC.nnrpow_def, cfcₙ_nnreal_eq_real _ _ (normalizePositive_nonneg a ha0)]
  apply cfcₙ_mem
  exact (hereditarySubalgebra h hh).smul_mem (‖a‖⁻¹) ha

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.OrthogonalElements
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uB

namespace Pureness

section

open Filter Topology

open scoped NNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma rootExponent_tendsto :
    Tendsto (fun j : ℕ => ((j : ℝ≥0) + 1)⁻¹) atTop (𝓝 0) := by
  apply tendsto_inv_atTop_zero.comp
  have hn : Tendsto (fun j : ℕ => (j : ℝ≥0)) atTop atTop := tendsto_natCast_atTop_atTop
  exact tendsto_atTop_mono (fun j => le_add_of_nonneg_right (by positivity)) hn

lemma root_mul_uniform :
    TendstoUniformlyOn
      (fun j : ℕ => fun t : ℝ => t ^ ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
      (fun t => t) atTop (Set.Icc 0 1) := by
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto isCompact_Icc
  · intro j
    exact (Real.continuous_rpow_const (by positivity)).continuousOn
  · intro t ht j k hjk
    by_cases ht0 : t = 0
    · subst t
      simp only [Real.zero_rpow (by positivity :
        (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ)),
        Real.zero_rpow (by positivity :
        (((k : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ))]
      exact le_rfl
    · apply Real.rpow_le_rpow_of_exponent_ge (lt_of_le_of_ne ht.1 (Ne.symm ht0)) ht.2
      have hi : ((k : ℝ≥0) + 1)⁻¹ ≤ ((j : ℝ≥0) + 1)⁻¹ :=
        inv_anti₀ (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1)
      exact NNReal.coe_le_coe.mpr (add_le_add hi le_rfl)
  · exact continuousOn_id
  · intro t _
    have he : Tendsto (fun j : ℕ => ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
        atTop (𝓝 1) := by
      have hn : Tendsto (fun j : ℕ => ((j : ℝ≥0) + 1)⁻¹ + 1) atTop (𝓝 1) :=
        by simpa using rootExponent_tendsto.add_const 1
      exact (NNReal.continuous_coe.tendsto 1).comp hn
    simpa using (tendsto_const_nhds.rpow he (Or.inr zero_lt_one) :
      Tendsto (fun j : ℕ => t ^ ((((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) : ℝ))
        atTop (𝓝 (t ^ (1 : ℝ))))

lemma normalizedRoot_mul_normalize_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun j => normalizedRoot h j * normalizePositive h) atTop
      (𝓝 (normalizePositive h)) := by
  nontriviality A
  have hsub : quasispectrum ℝ (normalizePositive h) ⊆ Set.Icc 0 1 := by
    intro t ht
    refine ⟨quasispectrum_nonneg_of_nonneg _ (normalizePositive_nonneg h hh) _ ht, ?_⟩
    rw [quasispectrum_eq_spectrum_union_zero] at ht
    rcases ht with ht | ht
    · exact (le_abs_self t).trans ((spectrum.norm_le_norm_of_mem ht).trans
        (normalizePositive_norm_le h))
    · simpa only [Set.mem_singleton_iff.mp ht] using (zero_le_one : (0 : ℝ) ≤ 1)
  have ht := tendsto_cfcₙ_fun (a := normalizePositive h) (root_mul_uniform.mono hsub)
    (Eventually.of_forall fun j =>
      (Real.continuous_rpow_const (by positivity :
        (0 : ℝ) ≤ (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0))).continuousOn)
    (Eventually.of_forall fun j => Real.zero_rpow (by positivity :
        (((j : ℝ≥0) + 1)⁻¹ + 1 : ℝ≥0) ≠ (0 : ℝ)))
  simp only [cfcₙ_id' ℝ (normalizePositive h) (normalizePositive_nonneg h hh).isSelfAdjoint] at ht
  convert ht using 1
  ext j
  rw [← CFC.nnrpow_eq_cfcₙ_real _ _ (normalizePositive_nonneg h hh), CFC.nnrpow_add (by positivity) (by positivity),
    CFC.nnrpow_one _ (normalizePositive_nonneg h hh)]
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_smul_normalizePositive (h : A) : ‖h‖ • normalizePositive h = h := by
  by_cases he : h = 0
  · simp [he]
  · simp [normalizePositive, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr he)]

lemma normalizedRoot_mul_self_tendsto (h : A) (hh : 0 ≤ h) :
    Tendsto (fun j => normalizedRoot h j * h) atTop (𝓝 h) := by
  have ht := (normalizedRoot_mul_normalize_tendsto h hh).const_smul ‖h‖
  simpa only [← mul_smul_comm, norm_smul_normalizePositive] using ht

lemma normalizedRoot_mul_hereditary_tendsto (h : A) (hh : 0 ≤ h)
    (c : A) (hc : c ∈ hereditaryCarrier h) :
    Tendsto (fun j => normalizedRoot h j * c) atTop (𝓝 c) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨d, ⟨w, rfl⟩, hd⟩ := Metric.mem_closure_iff.mp hc (ε / 4) (by positivity)
  have ht : Tendsto (fun j => normalizedRoot h j * (h * w * h)) atTop
      (𝓝 (h * w * h)) := by
    simpa only [mul_assoc] using
      ((normalizedRoot_mul_self_tendsto h hh).mul_const w).mul_const h
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp ht (ε / 2) (by positivity)
  refine ⟨J, fun j hj => ?_⟩
  have hsmall := hJ j hj
  simp only [dist_eq_norm] at hd hsmall ⊢
  have he : ‖normalizedRoot h j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have heq : normalizedRoot h j * c - c =
      normalizedRoot h j * (c - h * w * h) +
        (normalizedRoot h j * (h * w * h) - h * w * h) + (h * w * h - c) := by
    noncomm_ring
  rw [heq]
  calc
    _ ≤ ‖normalizedRoot h j * (c - h * w * h)‖ +
        ‖normalizedRoot h j * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖normalizedRoot h j‖ * ‖c - h * w * h‖ +
        ‖normalizedRoot h j * (h * w * h) - h * w * h‖ + ‖h * w * h - c‖ := by
      gcongr
      exact norm_mul_le _ _
    _ < ε := by
      rw [norm_sub_rev (h * w * h) c]
      nlinarith [norm_nonneg (c - h * w * h)]

end

section

open Filter Topology

open scoped ComplexOrder ENNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_mul_contraction_le (τ : TracialState A) (e c : A)
    (he : 0 ≤ e) (hc : c ≤ 1) : τ.functional (e * c) ≤ τ.functional e := by
  have heq : τ.functional (e * c) =
      τ.functional (CFC.sqrt e * c * CFC.sqrt e) := by
    calc
      _ = τ.functional ((CFC.sqrt e * CFC.sqrt e) * c) := by
        rw [CFC.sqrt_mul_sqrt_self e he]
      _ = τ.functional ((CFC.sqrt e * c) * CFC.sqrt e) := by
        rw [mul_assoc, τ.tracial (CFC.sqrt e) (CFC.sqrt e * c)]
  rw [heq]
  apply τ.functional.monotone
  simpa only [(CFC.sqrt_nonneg e).star_eq, mul_one, CFC.sqrt_mul_sqrt_self e he] using
    star_left_conjugate_le_conjugate hc (CFC.sqrt e)

lemma trace_le_rank_of_mem_hereditary (τ : TracialState A) (h c : A)
    (hh : 0 ≤ h) (hc : c ∈ hereditaryCarrier h) (hc1 : c ≤ 1) :
    ENNReal.ofReal (τ.functional c).re ≤ normalizedRootRank τ h := by
  have ht : Tendsto (fun j => ENNReal.ofReal (τ.functional (normalizedRoot h j * c)).re)
      atTop (𝓝 (ENNReal.ofReal (τ.functional c).re)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Complex.continuous_re.continuousAt.tendsto.comp
        ((map_continuous τ.functional).continuousAt.tendsto.comp
          (normalizedRoot_mul_hereditary_tendsto h hh c hc)))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro j
  calc
    _ ≤ ENNReal.ofReal (τ.functional (normalizedRoot h j)).re :=
      ENNReal.ofReal_le_ofReal (Complex.le_def.mp
        (trace_mul_contraction_le τ _ c (normalizedRoot_nonneg h j) hc1)).1
    _ ≤ normalizedRootRank τ h :=
      le_iSup (fun j => ENNReal.ofReal (τ.functional (normalizedRoot h j)).re) j

theorem hereditary_rank_domination (τ : TracialState A) (h c : A)
    (hh : 0 ≤ h) (hc : 0 ≤ c) (hcmem : c ∈ hereditaryCarrier h) :
    normalizedRootRank τ c ≤ normalizedRootRank τ h := by
  apply iSup_le
  intro j
  exact trace_le_rank_of_mem_hereditary τ h (normalizedRoot c j) hh
    (normalizedRoot_mem_hereditary hh hcmem hc j) (normalizedRoot_le_one c hc j)

end

open Filter Topology

open scoped ComplexOrder NNReal Polynomial

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma trace_cfc_eq_of_moments (τ : TracialState A) (a b : A)
    (ha : IsSelfAdjoint a) (hb : IsSelfAdjoint b)
    (hm : ∀ n : ℕ, τ.functional (a ^ n) = τ.functional (b ^ n))
    (f : ℝ → ℝ) (hf : Continuous f) :
    τ.functional (cfc f a) = τ.functional (cfc f b) := by
  let : Algebra ℝ (A × A) := Algebra.complexToReal
  let : NormedSpace ℝ (A × A) := NormedSpace.complexToReal
  have hp : IsSelfAdjoint (a, b) := by
    show star (a, b) = (a, b)
    simp only [Prod.star_def, ha.star_eq, hb.star_eq]
  have hpoly (p : ℝ[X]) :
      τ.functional ((Polynomial.aeval (a, b) p).1) =
      τ.functional ((Polynomial.aeval (a, b) p).2) := by
    rw [Polynomial.aeval_eq_sum_range]
    simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      Prod.pow_mk, map_sum, τ.functional.map_smul_of_tower, hm]
  have hclosed : IsClosed {z : A × A | τ.functional z.1 = τ.functional z.2} :=
    isClosed_eq ((map_continuous τ.functional).comp continuous_fst)
      ((map_continuous τ.functional).comp continuous_snd)
  have hsub : (StarAlgebra.elemental ℝ (a, b) : Set (A × A)) ⊆
      {z : A × A | τ.functional z.1 = τ.functional z.2} := by
    apply closure_minimal _ hclosed
    intro z hz
    change z ∈ (StarAlgebra.adjoin ℝ {(a, b)}).toSubalgebra at hz
    rw [StarAlgebra.adjoin_toSubalgebra, Set.star_singleton, hp.star_eq, Set.union_self,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    exact hpoly p
  have hc := hsub (cfc_mem_elemental (p := IsSelfAdjoint) f (a, b))
  have hfst : (cfc f (a, b)).1 = cfc f a :=
    (StarAlgHom.fst ℂ A A).map_cfc f (a, b) hf.continuousOn continuous_fst hp ha
  have hsnd : (cfc f (a, b)).2 = cfc f b :=
    (StarAlgHom.snd ℂ A A).map_cfc f (a, b) hf.continuousOn continuous_snd hp hb
  change τ.functional (cfc f (a, b)).1 = τ.functional (cfc f (a, b)).2 at hc
  rwa [hfst, hsnd] at hc

omit [StarOrderedRing A] in
lemma trace_star_mul_self_pow (τ : TracialState A) (x : A) (n : ℕ) :
    τ.functional ((star x * x) ^ n) = τ.functional ((x * star x) ^ n) := by
  cases n with
  | zero => simp
  | succ n =>
    have hid : (star x * x) ^ (n + 1) = star x * (x * star x) ^ n * x := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ (star x * x) (n + 1), ih, pow_succ (x * star x) n]
        simp only [mul_assoc]
    rw [hid, mul_assoc, τ.tracial (star x) ((x * star x) ^ n * x),
      mul_assoc, ← pow_succ]

lemma trace_nnrpow_eq_of_moments (τ : TracialState A) (a b : A)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hm : ∀ n : ℕ, τ.functional (a ^ n) = τ.functional (b ^ n))
    (r : ℝ≥0) (hr : 0 < r) :
    τ.functional (CFC.nnrpow a r) = τ.functional (CFC.nnrpow b r) := by
  simp only [CFC.nnrpow_eq_pow, CFC.nnrpow_eq_cfcₙ_real a r ha,
    CFC.nnrpow_eq_cfcₙ_real b r hb]
  have hf0 : (0 : ℝ) ^ (r : ℝ) = 0 := Real.zero_rpow (by exact_mod_cast hr.ne')
  rw [cfcₙ_eq_cfc (hf0 := hf0), cfcₙ_eq_cfc (hf0 := hf0)]
  exact trace_cfc_eq_of_moments τ a b ha.isSelfAdjoint hb.isSelfAdjoint hm _
    (Real.continuous_rpow_const (by positivity))

theorem rank_star_mul_self (τ : TracialState A) (x : A) :
    normalizedRootRank τ (star x * x) = normalizedRootRank τ (x * star x) := by
  have hnorm : ‖star x * x‖ = ‖x * star x‖ := by
    calc
      _ = ‖x‖ * ‖x‖ := CStarRing.norm_star_mul_self (x := x)
      _ = ‖star x‖ * ‖star x‖ := by rw [norm_star]
      _ = _ := by simpa only [star_star] using (CStarRing.norm_star_mul_self (x := star x)).symm
  have hm (n : ℕ) :
      τ.functional ((normalizePositive (star x * x)) ^ n) =
      τ.functional ((normalizePositive (x * star x)) ^ n) := by
    simp only [normalizePositive, smul_pow, τ.functional.map_smul_of_tower,
      hnorm, trace_star_mul_self_pow τ x n]
  unfold normalizedRootRank
  congr 1
  funext j
  unfold normalizedRoot
  rw [trace_nnrpow_eq_of_moments τ _ _
    (normalizePositive_nonneg _ (star_mul_self_nonneg x))
    (normalizePositive_nonneg _ (mul_star_self_nonneg x)) hm _ (by positivity)]

end Pureness

open Filter Topology

namespace Pureness

variable {B : Type uB} [NonUnitalNormedRing B] [StarRing B]

theorem cuntzSubequiv_iff_sequence (a b : B) :
    CuntzSubequiv a b ↔
      ∃ v : ℕ → B, Tendsto (fun j => star (v j) * b * v j) atTop (𝓝 a) := by
  rw [CuntzSubequiv, mem_closure_iff_seq_limit]
  constructor
  · rintro ⟨u, hu, hlim⟩
    choose v hv using hu
    exact ⟨v, by simpa only [hv] using hlim⟩
  · rintro ⟨v, hv⟩
    exact ⟨_, fun j => ⟨v j, rfl⟩, hv⟩

theorem cuntzSubequiv_conjugate (b v : B) : CuntzSubequiv (star v * b * v) b :=
  subset_closure ⟨v, rfl⟩

theorem cuntzSubequiv_of_tendsto {a : ℕ → B} {b c : B}
    (h : ∀ j, CuntzSubequiv (a j) b) (ha : Tendsto a atTop (𝓝 c)) :
    CuntzSubequiv c b :=
  isClosed_closure.mem_of_tendsto ha (Filter.Eventually.of_forall h)

theorem CuntzSubequiv.conjugate_left {a b : B} (h : CuntzSubequiv a b) (v : B) :
    CuntzSubequiv (star v * a * v) b := by
  obtain ⟨w, hw⟩ := (cuntzSubequiv_iff_sequence a b).mp h
  apply (cuntzSubequiv_iff_sequence _ _).mpr
  refine ⟨fun j => w j * v, ?_⟩
  have hlim : Tendsto (fun j => star v * (star (w j) * b * w j) * v)
      atTop (𝓝 (star v * a * v)) :=
    (tendsto_const_nhds.mul hw).mul tendsto_const_nhds
  simpa only [star_mul, mul_assoc] using hlim

theorem CuntzSubequiv.trans {a b c : B}
    (hab : CuntzSubequiv a b) (hbc : CuntzSubequiv b c) : CuntzSubequiv a c := by
  obtain ⟨v, hv⟩ := (cuntzSubequiv_iff_sequence a b).mp hab
  exact cuntzSubequiv_of_tendsto (fun j => hbc.conjugate_left (v j)) hv

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.HereditaryAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uι

open Filter Topology

namespace Pureness

section

open Filter Topology

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem hereditary_cuntzSubequiv (h c : A) (hh : 0 ≤ h) (hc : 0 ≤ c)
    (hcm : c ∈ hereditaryCarrier h) : CuntzSubequiv c h := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (hereditary_sqrt_mem hh hc hcm)
  have hs := (hlim.star.mul hlim)
  rw [(CFC.sqrt_nonneg c).star_eq, CFC.sqrt_mul_sqrt_self c hc] at hs
  apply cuntzSubequiv_of_tendsto (a := fun j => star (u j) * u j) _ hs
  intro j
  obtain ⟨w, hw⟩ := hu j
  rw [← hw]
  have hsquare : CFC.sqrt h * h * CFC.sqrt h = h * h := by
    calc
      _ = CFC.sqrt h * (CFC.sqrt h * CFC.sqrt h) * CFC.sqrt h := by
        rw [CFC.sqrt_mul_sqrt_self h hh]
      _ = (CFC.sqrt h * CFC.sqrt h) * (CFC.sqrt h * CFC.sqrt h) := by
        noncomm_ring
      _ = h * h := by rw [CFC.sqrt_mul_sqrt_self h hh]
  have heq : star (h * w * h) * (h * w * h) =
      star (CFC.sqrt h * w * h) * h * (CFC.sqrt h * w * h) := by
    simp only [star_mul, hh.star_eq, (CFC.sqrt_nonneg h).star_eq]
    calc
      _ = h * star w * (h * h) * w * h := by simp only [mul_assoc]
      _ = h * star w * (CFC.sqrt h * h * CFC.sqrt h) * w * h := by rw [hsquare]
      _ = _ := by simp only [mul_assoc]
  rw [heq]
  exact cuntzSubequiv_conjugate _ _

omit [PartialOrder A] [StarOrderedRing A] in
lemma norm_mul_star_self (x : A) : ‖x * star x‖ = ‖x‖ * ‖x‖ := by
  simpa only [star_star, norm_star] using (CStarRing.norm_star_mul_self (x := star x))

omit [PartialOrder A] [StarOrderedRing A] in
lemma tendsto_mul_zero_of_norm_le_one (z e : ℕ → A)
    (hz : Tendsto z atTop (𝓝 0)) (he : ∀ n, ‖e n‖ ≤ 1) :
    Tendsto (fun n => z n * e n) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
    (by simpa only [norm_zero] using hz.norm)
  calc
    _ ≤ ‖z n‖ * ‖e n‖ := norm_mul_le _ _
    _ ≤ ‖z n‖ * 1 := mul_le_mul_of_nonneg_left (he n) (norm_nonneg _)
    _ = ‖z n‖ := mul_one _

lemma normalizedRoot_mul_of_mul_star_self_tendsto (h x : A) (hh : 0 ≤ h)
    (hx : x * star x ∈ hereditaryCarrier h) :
    Tendsto (fun j => normalizedRoot h j * x) atTop (𝓝 x) := by
  let e := normalizedRoot h
  let z := fun j => x * star x - e j * (x * star x)
  have he (j : ℕ) : ‖e j‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ (normalizedRoot_nonneg h j)).mpr
      (normalizedRoot_le_one h hh j)
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds (x := x * star x)).sub
      (normalizedRoot_mul_hereditary_tendsto h hh _ hx)
  have hw : Tendsto (fun j => z j - z j * e j) atTop (𝓝 0) := by
    simpa only [sub_zero] using hz.sub (tendsto_mul_zero_of_norm_le_one z e hz he)
  have hn (j : ℕ) : ‖x - e j * x‖ ^ 2 = ‖z j - z j * e j‖ := by
    calc
      _ = ‖(x - e j * x) * star (x - e j * x)‖ := by
        rw [norm_mul_star_self, pow_two]
      _ = _ := by
        congr 1
        dsimp [z, e]
        simp only [star_sub, star_mul, (normalizedRoot_nonneg h j).star_eq]
        noncomm_ring
  have hsq : Tendsto (fun j => ‖x - e j * x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hn, norm_zero] using hw.norm
  have hzero : Tendsto (fun j => x - e j * x) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsq.sqrt
  simpa only [sub_sub_cancel, sub_zero] using (tendsto_const_nhds (x := x)).sub hzero

theorem star_mul_self_cuntzSubequiv_of_hereditary (h x : A) (hh : 0 ≤ h)
    (hx : x * star x ∈ hereditaryCarrier h) : CuntzSubequiv (star x * x) h := by
  have ht : Tendsto (fun j => star x * normalizedRoot h j * x) atTop (𝓝 (star x * x)) := by
    simpa only [mul_assoc] using tendsto_const_nhds.mul
      (normalizedRoot_mul_of_mul_star_self_tendsto h x hh hx)
  apply cuntzSubequiv_of_tendsto _ ht
  intro j
  exact (hereditary_cuntzSubequiv h (normalizedRoot h j) hh (normalizedRoot_nonneg h j)
    (normalizedRoot_mem_hereditary hh (self_mem_hereditary h hh) hh j)).conjugate_left x

theorem star_mul_self_cuntzSubequiv (x : A) : CuntzSubequiv (star x * x) (x * star x) :=
  star_mul_self_cuntzSubequiv_of_hereditary _ x (mul_star_self_nonneg x)
    (self_mem_hereditary _ (mul_star_self_nonneg x))

end

section

open scoped ComplexOrder

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_nonzero_cross (hsimple : TopologicallySimple A) (e f : A)
    (he : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) : ∃ z : A, e * z * f ≠ 0 := by
  obtain ⟨n, s, hs⟩ := fullness hsimple f hf hf0
  by_contra hnone
  have hz (z : A) : e * z * f = 0 := by
    by_contra hne
    exact hnone ⟨z, hne⟩
  apply he
  calc
    e = e * (∑ i : Fin n, star (s i) * f * s i) := by rw [hs, mul_one]
    _ = ∑ i : Fin n, (e * star (s i) * f) * s i := by
      rw [Finset.mul_sum]
      simp only [mul_assoc]
    _ = 0 := by simp only [hz, zero_mul, Finset.sum_const_zero]

theorem exists_common_minorant (hsimple : TopologicallySimple A) (e f : A)
    (he : 0 ≤ e) (he0 : e ≠ 0) (hf : 0 ≤ f) (hf0 : f ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧ CuntzSubequiv h e ∧ CuntzSubequiv h f ∧
      ∀ τ : TracialState A,
        normalizedRootRank τ h ≤ normalizedRootRank τ e ∧
        normalizedRootRank τ h ≤ normalizedRootRank τ f := by
  obtain ⟨z, hz⟩ := exists_nonzero_cross hsimple e f he0 hf hf0
  let v := e * z * f
  have hv : v ≠ 0 := hz
  have hvm : v * star v ∈ hereditaryCarrier e := by
    apply subset_closure
    refine ⟨z * f * f * star z, ?_⟩
    simp only [v, star_mul, he.star_eq, hf.star_eq, mul_assoc]
  have hsm : star v * v ∈ hereditaryCarrier f := by
    apply subset_closure
    refine ⟨star z * e * e * z, ?_⟩
    simp only [v, star_mul, he.star_eq, hf.star_eq, mul_assoc]
  have hne : star v * v ≠ 0 := by
    intro heq
    have hn : ‖v‖ * ‖v‖ = 0 := by
      rw [← CStarRing.norm_star_mul_self, heq, norm_zero]
    rcases mul_eq_zero.mp hn with hn | hn
    all_goals exact hv (norm_eq_zero.mp hn)
  refine ⟨star v * v, star_mul_self_nonneg v, hne, ?_,
    hereditary_cuntzSubequiv f _ hf (star_mul_self_nonneg v) hsm, ?_⟩
  · exact (star_mul_self_cuntzSubequiv v).trans
      (hereditary_cuntzSubequiv e _ he (mul_star_self_nonneg v) hvm)
  · intro τ
    constructor
    · rw [rank_star_mul_self τ v]
      exact hereditary_rank_domination τ e _ he (mul_star_self_nonneg v) hvm
    · exact hereditary_rank_domination τ f _ hf (star_mul_self_nonneg v) hsm

theorem exists_finite_common_minorant [Nontrivial A] (hsimple : TopologicallySimple A)
    {ι : Type uι} (I : Finset ι) (e : ι → A)
    (he : ∀ i ∈ I, 0 ≤ e i) (he0 : ∀ i ∈ I, e i ≠ 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      (∀ i ∈ I, CuntzSubequiv h (e i)) ∧
      (∀ τ : TracialState A, ∀ i ∈ I, normalizedRootRank τ h ≤ normalizedRootRank τ (e i)) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, zero_le_one, one_ne_zero, by simp, by simp⟩
  | @insert i I hi ih =>
    obtain ⟨h, hh, hh0, hhC, hhR⟩ := ih
      (fun j hj => he j (Finset.mem_insert_of_mem hj))
      (fun j hj => he0 j (Finset.mem_insert_of_mem hj))
    obtain ⟨k, hk, hk0, hkh, hki, hkr⟩ := exists_common_minorant hsimple h (e i)
      hh hh0 (he i (Finset.mem_insert_self i I)) (he0 i (Finset.mem_insert_self i I))
    refine ⟨k, hk, hk0, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hki
      · exact hkh.trans (hhC j hj)
    · intro τ j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact (hkr τ).2
      · exact (hkr τ).1.trans (hhR τ j hj)

end

section

open Filter Topology

open scoped ComplexOrder ENNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_mul_eq_zero {h k x y : A}
    (hx : x ∈ hereditaryCarrier h) (hy : y ∈ hereditaryCarrier k) (hhk : h * k = 0) :
    x * y = 0 := by
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨v, hv, hvy⟩ := mem_closure_iff_seq_limit.mp hy
  have hz (j : ℕ) : u j * v j = 0 := by
    obtain ⟨a, ha⟩ := hu j
    obtain ⟨b, hb⟩ := hv j
    rw [← ha, ← hb]
    calc
      _ = h * a * (h * k) * b * k := by simp only [mul_assoc]
      _ = 0 := by rw [hhk]; simp
  have ht := hux.mul hvy
  simp only [hz] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

lemma orthogonal_add_le_one (a b : A) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hab : a * b = 0) : a + b ≤ 1 := by
  have hba : b * a = 0 := by
    simpa only [star_mul, ha.star_eq, hb.star_eq, star_zero] using congrArg star hab
  have hcomm : Commute (1 - a) (1 - b) := by
    show (1 - a) * (1 - b) = (1 - b) * (1 - a)
    noncomm_ring [hab, hba]
  have hpos := Commute.mul_nonneg (sub_nonneg.mpr ha1) (sub_nonneg.mpr hb1) hcomm
  have heq : (1 - a) * (1 - b) = 1 - (a + b) := by noncomm_ring [hab]
  rw [heq] at hpos
  exact sub_nonneg.mp hpos

lemma orthogonal_sum_le_one {ι : Type uι} (I : Finset ι) (a : ι → A)
    (ha : ∀ i ∈ I, 0 ≤ a i) (ha1 : ∀ i ∈ I, a i ≤ 1)
    (horth : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i * a j = 0) :
    ∑ i ∈ I, a i ≤ 1 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    apply orthogonal_add_le_one (a i) (∑ j ∈ I, a j)
      (ha i (Finset.mem_insert_self i I))
      (Finset.sum_nonneg fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (ha1 i (Finset.mem_insert_self i I))
    · exact ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
        (fun j hj => ha1 j (Finset.mem_insert_of_mem hj))
        (fun j hj k hk hjk => horth j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk)
    · rw [Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro j hj
      exact horth i (Finset.mem_insert_self i I) j (Finset.mem_insert_of_mem hj)
        (fun heq => hi (heq ▸ hj))

theorem orthogonal_rank_sum_le_one (τ : TracialState A) {ι : Type uι} (I : Finset ι)
    (a : ι → A) (ha : ∀ i ∈ I, 0 ≤ a i)
    (horth : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → a i * a j = 0) :
    ∑ i ∈ I, normalizedRootRank τ (a i) ≤ 1 := by
  have ht : Tendsto (fun n => ∑ i ∈ I, ENNReal.ofReal (τ.functional (normalizedRoot (a i) n)).re)
      atTop (𝓝 (∑ i ∈ I, normalizedRootRank τ (a i))) :=
    tendsto_finsetSum I (fun i hi => normalizedRootRank_tendsto τ (a i) (ha i hi))
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro n
  have hs : ∑ i ∈ I, normalizedRoot (a i) n ≤ 1 := by
    apply orthogonal_sum_le_one I (fun i => normalizedRoot (a i) n)
      (fun i _ => normalizedRoot_nonneg (a i) n)
      (fun i hi => normalizedRoot_le_one (a i) (ha i hi) n)
    intro i hi j hj hij
    exact hereditary_mul_eq_zero
      (normalizedRoot_mem_hereditary (ha i hi) (self_mem_hereditary _ (ha i hi)) (ha i hi) n)
      (normalizedRoot_mem_hereditary (ha j hj) (self_mem_hereditary _ (ha j hj)) (ha j hj) n)
      (horth i hi j hj hij)
  have hreal : (τ.functional (∑ i ∈ I, normalizedRoot (a i) n)).re ≤ 1 := by
    have hτ : τ.functional (∑ i ∈ I, normalizedRoot (a i) n) ≤ τ.functional 1 :=
      τ.functional.monotone hs
    rw [τ.normalized] at hτ
    exact (Complex.le_def.mp hτ).1
  have hn (i : ι) (hi : i ∈ I) : 0 ≤ (τ.functional (normalizedRoot (a i) n)).re :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (normalizedRoot_nonneg (a i) n))).1
  rw [← ENNReal.ofReal_sum_of_nonneg hn]
  apply ENNReal.ofReal_le_one.mpr
  simpa only [map_sum, Complex.re_sum] using hreal

theorem small_rank_of_orthogonal_family [Nontrivial A] (hsimple : TopologicallySimple A)
    (N : ℕ) (hN : 1 ≤ N) (a : Fin N → A) (ha : ∀ i, 0 ≤ a i)
    (ha0 : ∀ i, a i ≠ 0) (horth : ∀ i j, i ≠ j → a i * a j = 0) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      (∀ i, CuntzSubequiv h (a i)) ∧
      (∀ τ : TracialState A, normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞)) := by
  obtain ⟨h, hh, hh0, hhC, hhR⟩ := exists_finite_common_minorant hsimple Finset.univ a
    (fun i _ => ha i) (fun i _ => ha0 i)
  refine ⟨h, hh, hh0, fun i => hhC i (Finset.mem_univ i), ?_⟩
  intro τ
  have hsum : (N : ℝ≥0∞) * normalizedRootRank τ h ≤ 1 := by
    calc
      _ = ∑ i : Fin N, normalizedRootRank τ h := by simp [nsmul_eq_mul]
      _ ≤ ∑ i : Fin N, normalizedRootRank τ (a i) :=
        Finset.sum_le_sum (fun i hi => hhR τ i hi)
      _ ≤ 1 := orthogonal_rank_sum_le_one τ Finset.univ a
        (fun i _ => ha i) (fun i _ j _ hij => horth i j hij)
  apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast (Nat.ne_of_gt hN))) (by simp)).mpr
  simpa only [mul_comm] using hsum

end

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem finiteDimensional_of_scalar_sandwich (hsimple : TopologicallySimple A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0)
    (hcorner : ∀ a : A, ∃ z : ℂ, h * a * h = z • h) : FiniteDimensional ℂ A := by
  classical
  obtain ⟨n, s, hs⟩ := fullness hsimple h hh hh0
  let g : Fin n × Fin n → A := fun ij => star (s ij.1) * h * s ij.2
  let T : (Fin n × Fin n → ℂ) →ₗ[ℂ] A := {
    toFun := fun c => ∑ ij, c ij • g ij
    map_add' := by
      intro c d
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro z c
      simp only [Pi.smul_apply, smul_smul, smul_eq_mul, Finset.smul_sum, RingHom.id_apply] }
  apply Module.Finite.of_surjective T
  intro a
  choose c hc using fun i j : Fin n => hcorner (s i * a * star (s j))
  refine ⟨fun ij => c ij.1 ij.2, ?_⟩
  change (∑ ij : Fin n × Fin n, c ij.1 ij.2 • g ij) = a
  symm
  calc
    a = (∑ i : Fin n, star (s i) * h * s i) * a *
        (∑ j : Fin n, star (s j) * h * s j) := by rw [hs, one_mul, mul_one]
    _ = ∑ i : Fin n, ∑ j : Fin n,
        star (s i) * (h * (s i * a * star (s j)) * h) * s j := by
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]
    _ = ∑ i : Fin n, ∑ j : Fin n, c i j • (star (s i) * h * s j) := by
      simp only [hc, mul_smul_comm, smul_mul_assoc]
    _ = _ := by simp only [Fintype.sum_prod_type, g]

end Pureness

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.FullProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD

open Filter Topology

namespace Pureness

section

open Filter Topology ComplexStarModule

open scoped ComplexOrder CStarAlgebra

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
lemma hereditary_complex_smul_mem {h x : A} (z : ℂ) (hx : x ∈ hereditaryCarrier h) :
    z • x ∈ hereditaryCarrier h := by
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp hx
  apply isClosed_closure.mem_of_tendsto (ht.const_smul z)
  apply Eventually.of_forall
  intro j
  obtain ⟨w, hw⟩ := hu j
  apply subset_closure
  exact ⟨z • w, by simp only [← hw, mul_smul_comm, smul_mul_assoc]⟩

lemma hereditary_realPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℜ x : A) ∈ hereditaryCarrier h := by
  rw [realPart_apply_coe]
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).add_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma hereditary_imaginaryPart_mem {h x : A} (hh : 0 ≤ h) (hx : x ∈ hereditaryCarrier h) :
    (ℑ x : A) ∈ hereditaryCarrier h := by
  rw [imaginaryPart_apply_coe]
  apply hereditary_complex_smul_mem
  exact (hereditarySubalgebra h hh).smul_mem _
    ((hereditarySubalgebra h hh).sub_mem hx (star_mem (s := hereditarySubalgebra h hh) hx))

lemma trace_selfAdjoint_im_zero (τ : TracialState A) (x : A) (hx : IsSelfAdjoint x) :
    (τ.functional x).im = 0 := by
  have hp : (τ.functional x⁺).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.posPart_nonneg x))).2.symm
  have hq : (τ.functional x⁻).im = 0 :=
    (Complex.nonneg_iff.mp (τ.functional.map_nonneg (CFC.negPart_nonneg x))).2.symm
  have he := congrArg (fun a => (τ.functional a).im) (CFC.posPart_sub_negPart x hx)
  simpa only [map_sub, Complex.sub_im, hp, hq, sub_self] using he.symm

lemma trace_zero_selfadjoint_split (τ : TracialState A) (hsimple : TopologicallySimple A)
    (h x : A) (hh : 0 ≤ h) (hx : IsSelfAdjoint x) (hx0 : x ≠ 0)
    (hxm : x ∈ hereditaryCarrier h) (hτ : τ.functional x = 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  have heq : τ.functional (x⁺) = τ.functional (x⁻) := by
    apply sub_eq_zero.mp
    rw [← map_sub, CFC.posPart_sub_negPart x hx, hτ]
  have hp0 : x⁺ ≠ 0 := by
    intro hp
    have hq := τ.faithful hsimple _ (CFC.negPart_nonneg x) (by rw [← heq, hp, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  have hq0 : x⁻ ≠ 0 := by
    intro hq
    have hp := τ.faithful hsimple _ (CFC.posPart_nonneg x) (by rw [heq, hq, map_zero])
    apply hx0
    rw [← CFC.posPart_sub_negPart x hx, hp, hq, sub_zero]
  refine ⟨x⁺, x⁻, CFC.posPart_nonneg x, hp0, ?_,
    CFC.negPart_nonneg x, hq0, ?_, CFC.posPart_mul_negPart x⟩
  · change x⁺ ∈ hereditarySubalgebra h hh
    rw [CFC.posPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)
  · change x⁻ ∈ hereditarySubalgebra h hh
    rw [CFC.negPart_def]
    exact cfcₙ_mem _ (show x ∈ hereditarySubalgebra h hh from hxm)

theorem exists_orthogonal_pair_hereditary (τ : TracialState A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) :
    ∃ e f : A, 0 ≤ e ∧ e ≠ 0 ∧ e ∈ hereditaryCarrier h ∧
      0 ≤ f ∧ f ≠ 0 ∧ f ∈ hereditaryCarrier h ∧ e * f = 0 := by
  by_contra hno
  have hτh0 : τ.functional h ≠ 0 := fun hz => hh0 (τ.faithful hsimple h hh hz)
  have hτh : 0 < (τ.functional h).re :=
    (Complex.pos_iff.mp (lt_of_le_of_ne (τ.functional.map_nonneg hh) hτh0.symm)).1
  have hscalar (x : A) (hx : IsSelfAdjoint x) (hxm : x ∈ hereditaryCarrier h) :
      ∃ r : ℝ, x = r • h := by
    let r := (τ.functional x).re / (τ.functional h).re
    have hy : IsSelfAdjoint (x - r • h) := hx.sub ((IsSelfAdjoint.all r).smul hh.isSelfAdjoint)
    have hym : x - r • h ∈ hereditaryCarrier h :=
      (hereditarySubalgebra h hh).sub_mem hxm
        ((hereditarySubalgebra h hh).smul_mem r (self_mem_hereditary h hh))
    have hτy : τ.functional (x - r • h) = 0 := by
      rw [map_sub, τ.functional.map_smul_of_tower]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.smul_re, Complex.zero_re]
        dsimp [r]
        exact sub_eq_zero.mpr (div_mul_cancel₀ _ (ne_of_gt hτh)).symm
      · simp only [Complex.sub_im, Complex.smul_im, Complex.zero_im,
          trace_selfAdjoint_im_zero τ x hx, trace_selfAdjoint_im_zero τ h hh.isSelfAdjoint,
          smul_zero, sub_zero]
    have hy0 : x - r • h = 0 := by
      by_contra hy0
      exact hno (trace_zero_selfadjoint_split τ hsimple h _ hh hy hy0 hym hτy)
    exact ⟨r, sub_eq_zero.mp hy0⟩
  apply hinf
  apply finiteDimensional_of_scalar_sandwich hsimple h hh hh0
  intro a
  have ham : h * a * h ∈ hereditaryCarrier h := subset_closure ⟨a, rfl⟩
  obtain ⟨r, hr⟩ := hscalar (ℜ (h * a * h)) (ℜ (h * a * h)).2 (hereditary_realPart_mem hh ham)
  obtain ⟨s, hs⟩ := hscalar (ℑ (h * a * h)) (ℑ (h * a * h)).2 (hereditary_imaginaryPart_mem hh ham)
  refine ⟨(r : ℂ) + Complex.I * (s : ℂ), ?_⟩
  rw [← realPart_add_I_smul_imaginaryPart (h * a * h), hr, hs]
  simp only [add_smul, mul_smul, Complex.coe_smul]

end

open scoped ENNReal

variable {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma exists_orthogonal_family_with_reserve (τ : TracialState A)
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (h : A) (hh : 0 ≤ h) (hh0 : h ≠ 0) (N : ℕ) :
    ∃ r : A, ∃ a : Fin N → A,
      0 ≤ r ∧ r ≠ 0 ∧ (∀ i, 0 ≤ a i) ∧ (∀ i, a i ≠ 0) ∧
      (∀ i j, i ≠ j → a i * a j = 0) ∧ (∀ i, a i * r = 0) := by
  induction N with
  | zero => exact ⟨h, Fin.elim0, hh, hh0, by simp, by simp, by simp, by simp⟩
  | succ N ih =>
    obtain ⟨r, a, hr, hr0, ha, ha0, horth, har⟩ := ih
    obtain ⟨e, f, he, he0, hem, hf, hf0, hfm, hef⟩ :=
      exists_orthogonal_pair_hereditary τ hsimple hinf r hr hr0
    have hae (i : Fin N) : a i * e = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hem (har i)
    have hea (i : Fin N) : e * a i = 0 := by
      simpa only [star_mul, he.star_eq, (ha i).star_eq, star_zero] using congrArg star (hae i)
    have haf (i : Fin N) : a i * f = 0 :=
      hereditary_mul_eq_zero (self_mem_hereditary _ (ha i)) hfm (har i)
    refine ⟨f, Fin.cons e a, hf, hf0, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i using Fin.cases with
      | zero => exact he
      | succ i => exact ha i
    · intro i
      cases i using Fin.cases with
      | zero => exact he0
      | succ i => exact ha0 i
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
        cases j using Fin.cases with
        | zero => exact (hij rfl).elim
        | succ j => exact hea j
      | succ i =>
        cases j using Fin.cases with
        | zero => exact hae i
        | succ j => exact horth i j (fun heq => hij (congrArg Fin.succ heq))
    · intro i
      cases i using Fin.cases with
      | zero => exact hef
      | succ i => exact haf i

theorem small_hereditary_rank (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (hT : Nonempty (TracialState A))
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ h : A, 0 ≤ h ∧ h ≠ 0 ∧
      ∀ τ : TracialState A, normalizedRootRank τ h ≤ 1 / (N : ℝ≥0∞) := by
  classical
  rcases subsingleton_or_nontrivial A with hsub | hnontriv
  · let := hsub
    exact False.elim (hinf inferInstance)
  · let := hnontriv
    obtain ⟨τ⟩ := hT
    obtain ⟨_, a, _, _, ha, ha0, horth, _⟩ :=
      exists_orthogonal_family_with_reserve τ hsimple hinf 1 zero_le_one one_ne_zero N
    obtain ⟨h, hh, hh0, _, hR⟩ := small_rank_of_orthogonal_family hsimple N hN a ha ha0 horth
    exact ⟨h, hh, hh0, hR⟩

end Pureness

namespace CurrentMain

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section SmallFullSupport

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma small_positive (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hT : Nonempty (TracialState A)) (N : ℕ) (hN : 1 ≤ N) :
    ∃ b : A, 0 ≤ b ∧ ‖b‖ = 1 ∧ ∀ τ : TracialState A,
      (τ.functional b).re ≤ 1 / (N : ℝ) := by
  obtain ⟨h,hh,hh0,hr⟩ := small_hereditary_rank hsimple hinf hT N hN
  refine ⟨normalizePositive h,normalizePositive_nonneg h hh,?_,?_⟩
  · simp [normalizePositive,norm_smul,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hh0)]
  · intro τ
    have hb0 : 0 ≤ (τ.functional (normalizePositive h)).re :=
      (τ.functional.map_nonneg (normalizePositive_nonneg h hh)).1
    have hb := (normalized_trace_le_rank τ h hh).trans (hr τ)
    have hN0 : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    have ht := ENNReal.toReal_mono (by simp [hN0]) hb
    simpa only [ENNReal.toReal_ofReal hb0,ENNReal.toReal_div,ENNReal.toReal_one,
      ENNReal.toReal_natCast] using ht

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma simple_starAlgHom_injective [Nontrivial D] (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) : Function.Injective ι := by
  have hι : Continuous ι := (ι.toLinearMap.mkContinuous 1 (fun a => by
    change ‖ι a‖ ≤ 1 * ‖a‖
    simpa only [one_mul] using (NonUnitalStarAlgHom.norm_apply_le ι a))).continuous
  have hc : IsClosed (TwoSidedIdeal.ker ι : Set A) := by
    have he : (TwoSidedIdeal.ker ι : Set A) = {a : A | ι a = 0} := by
      ext a; exact TwoSidedIdeal.mem_ker ι
    rw [he]
    exact isClosed_eq hι continuous_const
  rcases hsimple (TwoSidedIdeal.ker ι) hc with hb | ht
  · exact (TwoSidedIdeal.ker_eq_bot ι).mp hb
  · have : (1 : A) ∈ TwoSidedIdeal.ker ι := by rw [ht]; exact Set.mem_univ _
    have hz := (TwoSidedIdeal.mem_ker ι).mp this
    simp at hz

end SmallFullSupport

namespace ClosedSelfAdjointSpan

variable {D : Type uD} [CStarAlgebra D]

lemma ideal_coe {g : D} (hg : IsSelfAdjoint g) :
    ((ideal hg).ideal : Set D) = closure (TwoSidedIdeal.span {g} : Set D) :=
  coe_closedTwoSidedIdeal _

lemma quotientMap_g {g : D} (hg : IsSelfAdjoint g) : (ideal hg).quotientMap g = 0 := by
  change (ideal hg).ideal.ringCon.mk' g = (ideal hg).ideal.ringCon.mk' 0
  apply Quotient.sound
  change g ∈ (ideal hg).ideal
  rw [← SetLike.mem_coe,ideal_coe]
  exact subset_closure (TwoSidedIdeal.subset_span (Set.mem_singleton g))

lemma nontrivial_quotient {g : D} (hg : IsSelfAdjoint g) (hfull : ¬IsFull g) :
    Nontrivial (ideal hg).Quotient := by
  apply nontrivial_of_ne (1 : (ideal hg).Quotient) 0
  intro h
  have h1 : (1 : D) ∈ (ideal hg).ideal := by
    have he : (ideal hg).ideal.ringCon.mk' (1 : D) = (ideal hg).ideal.ringCon.mk' 0 := by
      change (ideal hg).quotientMap 1 = (ideal hg).quotientMap 0
      simpa using h
    exact Quotient.exact he
  have htop : (ideal hg).ideal = ⊤ := (TwoSidedIdeal.one_mem_iff _).mp h1
  apply hfull
  unfold IsFull
  rw [← ideal_coe hg,htop,TwoSidedIdeal.coe_top]

end ClosedSelfAdjointSpan

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.SmallProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uA uD


section

noncomputable section

noncomputable section

noncomputable section

open Filter Topology

namespace CurrentMain

open Pureness

open scoped ComplexOrder

section SmallFullProjection

variable {A : Type uA} {D : Type uD} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

lemma full_of_complement_bound (hsimple : TopologicallySimple A)
    (ι : A →⋆ₐ[ℂ] D) {b : A} (hb : 0 ≤ b) (hbn : ‖b‖ = 1)
    {g : D} (hg : IsStarProjection g) {α : ℝ} (hα : 0 ≤ α) (hα1 : α < 1)
    (hc : (1-g) * ι b * (1-g) ≤ α • (1-g)) : IsFull g := by
  by_contra hn
  let J := ClosedSelfAdjointSpan.ideal hg.isSelfAdjoint
  let : Nontrivial J.Quotient := ClosedSelfAdjointSpan.nontrivial_quotient hg.isSelfAdjoint hn
  let π := J.quotientStarHom
  have hπg : π g = 0 := ClosedSelfAdjointSpan.quotientMap_g hg.isSelfAdjoint
  have hπr : π (1-g) = 1 := by rw [map_sub,map_one,hπg,sub_zero]
  have hπc := map_rel π hc
  have hπsmul : π (α • (1-g)) = algebraMap ℂ J.Quotient (α : ℂ) * π (1-g) := by
    rw [Algebra.smul_def,map_mul]
    congr 1
  simp only [map_mul,hπsmul,hπr,one_mul,mul_one] at hπc
  have hπb : 0 ≤ π (ι b) := map_nonneg π (map_nonneg ι hb)
  have hnrm : ‖π (ι b)‖ ≤ α := (CStarAlgebra.norm_le_iff_le_algebraMap _ hα hπb).mpr (by
    exact hπc)
  have hfaith := simple_starAlgHom_injective hsimple (π.comp ι)
  have he := NonUnitalStarAlgHom.norm_map (π.comp ι) hfaith b
  change ‖π (ι b)‖ = ‖b‖ at he
  rw [he,hbn] at hnrm
  exact (not_le_of_gt hα1) hnrm

theorem small_full_projections (hsimple : TopologicallySimple A)
    (hinf : ¬FiniteDimensional ℂ A) (ι : A →⋆ₐ[ℂ] D)
    (hRR : RealRankZero D) (hT : Nonempty (TracialState D))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ g : D, IsStarProjection g ∧ IsFull g ∧
      (⨆ τ : TracialState D, (τ.functional g).re) < δ := by
  classical
  let := hT
  have hTA : Nonempty (TracialState A) := ⟨pullbackTrace (Classical.choice hT) ι⟩
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (show 0 < (3/8 : ℝ)*δ by positivity)
  obtain ⟨b,hb,hbn,hbτ⟩ := small_positive hsimple hinf hTA (n+1) (by omega)
  have hbD : 0 ≤ ι b := map_nonneg ι hb
  obtain ⟨g,hg,hl,hu⟩ := exists_spectral_cut hRR (IsSelfAdjoint.of_nonneg hbD)
    (1/2 : ℝ) (show (0 : ℝ) < 1/8 by norm_num)
  norm_num at hl hu
  refine ⟨g,hg,full_of_complement_bound hsimple ι hb hbn hg
    (by norm_num : (0 : ℝ) ≤ 5/8) (by norm_num) hu,?_⟩
  have ht (τ : TracialState D) : (τ.functional g).re ≤ (8/3 : ℝ) * (1/(n+1 : ℝ)) := by
    have h1 := (τ.functional.monotone hl).1
    change (τ.functional ((3/8 : ℝ) • g)).re ≤ (τ.functional (g * ι b * g)).re at h1
    rw [τ.functional.map_smul_of_tower,Complex.smul_re,smul_eq_mul,
      trace_projection_corner τ hg] at h1
    have h2 := trace_mul_mono_left τ hbD hg.le_one
    rw [one_mul] at h2
    have h3 := hbτ (pullbackTrace τ ι)
    change (τ.functional (ι b)).re ≤ 1 / ((n+1 : ℕ) : ℝ) at h3
    simp only [Nat.cast_add,Nat.cast_one] at h3
    linarith
  exact (ciSup_le ht).trans_lt (by linarith)

end SmallFullProjection

end CurrentMain

end

end

end

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.ConditionalSplitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

universe uA uD uI

open Filter Topology

namespace CurrentMain

section

open Pureness Filter

open scoped Topology NNReal ENNReal ComplexOrder

section TraceFamilyRestriction

variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (τ : I → TracialState D) [Nonempty I]

lemma familyTwoNorm_le_uniform (a : D) : familyTwoNorm τ a ≤ uniformTwoNorm a := by
  apply ciSup_le
  intro i
  exact le_ciSup (familyTwoNorm_bdd (fun t : TracialState D => t) a) (τ i)

lemma familyHalvingError_le_uniform (p x : D) :
    familyTraceNorm τ (p*x-(1/2 : ℂ) • x) ≤ uniformHalvingError p x := by
  have hb : BddAbove (Set.range fun t : TracialState D =>
      ‖t.functional (p*x)-(1/2 : ℂ)*t.functional x‖) := by
    refine ⟨‖p*x-(1/2 : ℂ) • x‖,?_⟩
    rintro _ ⟨t,rfl⟩
    simpa only [map_sub,map_smul,smul_eq_mul] using
      trace_norm_le_norm t (p*x-(1/2 : ℂ) • x)
  apply ciSup_le
  intro i
  simpa only [map_sub,map_smul,smul_eq_mul,uniformHalvingError] using le_ciSup hb (τ i)

end TraceFamilyRestriction

end

open MeasureTheory MeasureTheory.Measure

open scoped TensorProduct

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uNuclear


section

namespace CurrentMain

open Pureness Filter

theorem real_rank_zero_uniform_gamma
    {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [Nontrivial A] [TopologicalSpace.SeparableSpace A]
    (hsimple : TopologicallySimple A) (hinf : ¬FiniteDimensional ℂ A)
    (hA : IsNuclear.{0, uNuclear} A) (_hfinite : StablyFinite A)
    [Nonempty (TracialState A)] (U : Ultrafilter ℕ)
    (hfree : (U : Filter ℕ) ≤ atTop)
    (hRR : RealRankZero (FamilyUltrapower (completionTrace (fun τ : TracialState A => τ)) U)) :
    UniformPropertyGammaAt A U := by
  classical
  let τ := fun t : TracialState A => t
  let D := FamilyUltrapower (completionTrace τ) U
  let j : A →⋆ₐ[ℂ] D := (familyUltrapowerMap (completionTrace τ) U).comp (completionMap τ)
  let σ := familyLimitTrace (completionTrace τ) U
  have hTD : Nonempty (TracialState D) := ⟨σ (fun _ => Classical.arbitrary _)⟩
  apply completion_central_splitting_of_finite_stages τ U hfree
  intro K ε hε
  obtain ⟨P,hP,htest⟩ := finite_set_central_splitting j (simple_starAlgHom_injective hsimple j)
    hA hRR hTD (fun _ hδ => small_full_projections hsimple hinf j hRR hTD hδ) K ε hε
  refine ⟨P,hP,?_⟩
  intro u hu
  exact ⟨(familyTwoNorm_le_uniform σ _).trans_lt (htest u hu).1,
    (familyHalvingError_le_uniform σ P (j (u : A))).trans_lt (htest u hu).2⟩

end CurrentMain

end

end OAI
end

section
-- module Solutions.OAIQW_TracialSplitting.Challenge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The construction certificates are proved here, outside the self-contained challenge.
`main_iff_original` checks that packaging them preserves the original assertion. -/

universe uNuclear

namespace ComparatorModel.CurrentMain

noncomputable section

open Filter

attribute [local instance] OAI.ComparatorModel.CurrentMain.canonicalNorm
attribute [local instance] OAI.ComparatorModel.CurrentMain.canonicalNull
attribute [local instance] OAI.ComparatorModel.CurrentMain.canonicalCauchy
attribute [local instance] OAI.ComparatorModel.CurrentMain.canonicalLimit
attribute [local instance] OAI.ComparatorModel.CurrentMain.canonicalTrace
/-- The asserted conclusion, including all hypotheses, is definitionally unchanged. -/
theorem statement_iff_original : Statement.{uNuclear} ↔
    _root_.OAI.CurrentMain.OriginalGammaStatement.{uNuclear} := Iff.rfl

/-- The existential construction requirements do not change the original assertion. -/
theorem main_iff_original : MainClaim.{uNuclear} ↔
    _root_.OAI.CurrentMain.OriginalGammaStatement.{uNuclear} := by
  constructor
  · rintro ⟨_, _, _, _, _, h⟩
    exact statement_iff_original.mp h
  · intro h
    exact ⟨canonicalNorm, canonicalNull, canonicalCauchy, canonicalLimit, canonicalTrace,
      statement_iff_original.mpr h⟩

theorem main_oai : MainClaim.{uNuclear} :=
  main_iff_original.mpr @_root_.OAI.CurrentMain.real_rank_zero_uniform_gamma

end

end ComparatorModel.CurrentMain

end OAI
end

theorem solution.{uNuclear} : type_of% @OAI.ComparatorModel.CurrentMain.main_oai.{uNuclear} := @OAI.ComparatorModel.CurrentMain.main_oai.{uNuclear}
