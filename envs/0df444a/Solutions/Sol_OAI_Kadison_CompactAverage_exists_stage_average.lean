-- Prove2me | solution 1 for OAI.Kadison.CompactAverage.exists_stage_average
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:05:39.053798+00:00
-- url     : https://prove2.me/submissions/3c88277f-cd58-4618-8fc3-06fb789bc130

import Mathlib
import Definitions.Def_OAIQ039C003
import Definitions.Def_OAIQ039C004
import Definitions.Def_OAIQ039C019
import Theorems.Thm_OAI_Kadison_CompactAverage_exists_average

section
-- module Solutions.OAIQ039_CM.Commutator_Average
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory Filter

namespace Kadison.WeakOperatorIntegral

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

omit [CompleteSpace H] in
include hV in
lemma norm_le_of_integral {C : ℝ} (hC : 0 ≤ C) (hT : ∀ i, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    rw [hV]
    have h := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun i => inner ℂ (T i x) (V x)) (C := C*‖x‖*‖V x‖)
      (Eventually.of_forall (fun i => (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hT i) (norm_nonneg x))) (norm_nonneg _))))
    simpa only [probReal_univ,mul_one] using h
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [mul_comm,mul_left_comm,mul_assoc] using hi)

omit [IsProbabilityMeasure μ] in
include hI hV in
lemma commutator_coeff (a : H →L[ℂ] H) (x y : H) :
    inner ℂ ((V*a-a*V) x) y = ∫ i, inner ℂ ((T i*a-a*T i) x) y ∂μ := by
  simp only [sub_apply,mul_apply_eq_comp,inner_sub_left]
  simp only [← ContinuousLinearMap.adjoint_inner_right a]
  rw [hV,hV,integral_sub (hI (a x) y) (hI x (a.adjoint y))]

include hI hV in
lemma commutator_norm (a : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ i, ‖T i*a-a*T i‖ ≤ C) : ‖V*a-a*V‖ ≤ C := by
  exact norm_le_of_integral μ (fun i => T i*a-a*T i) (V*a-a*V)
    (commutator_coeff μ T hI V hV a) hC hb

omit [IsProbabilityMeasure μ] in
include hV in
lemma sandwich_coeff (a b : H →L[ℂ] H) (x y : H) :
    inner ℂ ((a*V*b) x) y = ∫ i, inner ℂ ((a*T i*b) x) y ∂μ := by
  simp only [mul_apply_eq_comp]
  simp only [← ContinuousLinearMap.adjoint_inner_right a]
  exact hV _ _

include hV in
lemma preserves_sandwich (a b Z : H →L[ℂ] H) (hZ : ∀ i, a*T i*b=Z) : a*V*b=Z := by
  ext x
  apply ext_inner_right ℂ
  intro y
  rw [sandwich_coeff μ T V hV]
  simp_rw [hZ]
  simp only [integral_const,probReal_univ,one_smul]

end Kadison.WeakOperatorIntegral

namespace Kadison.WeakOperatorIntegral

open MeasureTheory Filter

variable {ι H : Type*} [MeasurableSpace ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (μ : Measure ι) [IsProbabilityMeasure μ] (T : ι → H →L[ℂ] H)
  (hI : ∀ x y, Integrable (fun i => inner ℂ (T i x) y) μ)
  (V : H →L[ℂ] H)
  (hV : ∀ x y, inner ℂ (V x) y = ∫ i, inner ℂ (T i x) y ∂μ)

include hI hV in
lemma preserves_compressed_commutator (a b s W : H →L[ℂ] H)
    (hb : ∀ i, a*(T i*s-s*T i)*b=W) : a*(V*s-s*V)*b=W :=
  preserves_sandwich μ _ _ (commutator_coeff μ T hI V hV s) a b W hb

end Kadison.WeakOperatorIntegral

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StrongContinuity
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology

open Filter

namespace Kadison.StrongContinuity

variable {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (T : X → E →ₗᵢ[ℂ] E)

lemma joint (h : ∀ x, Continuous fun g => T g x) : Continuous (fun p : X × E => T p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro g
    exact (T g).isometry.lipschitz
  · exact h

end Kadison.StrongContinuity

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CompactAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure

namespace Kadison.CompactAverage

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (U : G →* (H ≃ₗᵢ[ℂ] H)) (hU : ∀ x : H, Continuous fun g => U g x)

variable (Y : H →L[ℂ] H)

omit [CompactSpace G] [MeasurableSpace G] [BorelSpace G] in
include hU in
lemma conjugate_continuous (x : H) : Continuous fun g => conjugate U Y g x := by
  have hi : Continuous fun g => (U g).symm x := by
    simpa only [Function.comp_def, map_inv,LinearIsometryEquiv.coe_inv] using (hU x).comp continuous_inv
  have hj := StrongContinuity.joint (fun g => (U g).toLinearIsometry) hU
  exact hj.comp (continuous_id.prodMk (Y.continuous.comp hi))

end Kadison.CompactAverage

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakOperatorLimit
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem norm_le_of_tendsto {l : Filter ι} [l.NeBot] {T : ι → E →L[ℂ] F}
    {V : E →L[ℂ] F} (hlim : ∀ x y, Tendsto (fun i => inner ℂ (T i x) y) l
      (𝓝 (inner ℂ (V x) y))) {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) : ‖V‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound V hC
  intro x
  have hi : ‖inner ℂ (V x) (V x)‖ ≤ C*‖x‖*‖V x‖ := by
    apply le_of_tendsto (hlim x (V x)).norm
    filter_upwards [hT] with i hi
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (((T i).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg x))) (norm_nonneg _))
  rw [← inner_self_re_eq_norm,inner_self_eq_norm_mul_norm] at hi
  by_cases hv : ‖V x‖=0
  · rw [hv]; positivity
  · have hp : 0 < ‖V x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    exact (mul_le_mul_iff_left₀ hp).mp (by simpa [pow_two,mul_comm,mul_left_comm,mul_assoc] using hi)

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_WeakConvergence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open Filter

namespace Kadison.WeakOperatorLimit

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

variable {l : Filter ι} {T : ι → H →L[ℂ] H} {V : H →L[ℂ] H}

lemma Converges.sub {S : ι → H →L[ℂ] H} {W : H →L[ℂ] H}
    (hT : Converges T V l) (hS : Converges S W l) : Converges (T-S) (V-W) l := by
  intro x y
  simpa only [Pi.sub_apply,sub_apply,inner_sub_left] using (hT x y).sub (hS x y)

lemma Converges.mul_right (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => T i*a) (V*a) l := by
  intro x y
  exact hT (a x) y

lemma Converges.mul_left [CompleteSpace H] (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => a*T i) (a*V) l := by
  intro x y
  simpa only [mul_apply_eq_comp,← ContinuousLinearMap.adjoint_inner_right a] using hT x (a.adjoint y)

lemma Converges.commutator [CompleteSpace H] (hT : Converges T V l) (a : H →L[ℂ] H) :
    Converges (fun i => T i*a-a*T i) (V*a-a*V) l :=
  (hT.mul_right a).sub (hT.mul_left a)

lemma Converges.unique [l.NeBot] {W : H →L[ℂ] H}
    (hT : Converges T V l) (hW : Converges T W l) : V=W := by
  ext x
  exact ext_inner_right ℂ (fun y => tendsto_nhds_unique (hT x y) (hW x y))

lemma Converges.eq_const [l.NeBot] (hT : Converges T V l) (W : H →L[ℂ] H)
    (hW : ∀ᶠ i in l, T i=W) : V=W := by
  apply hT.unique
  intro x y
  exact tendsto_const_nhds.congr' (hW.mono fun i h => by change inner ℂ (W x) y = inner ℂ (T i x) y; rw [h])

lemma Converges.norm [l.NeBot] (hT : Converges T V l) {C : ℝ} (hC : 0≤C)
    (hb : ∀ᶠ i in l, ‖T i‖≤C) : ‖V‖≤C := norm_le_of_tendsto hT hC hb

lemma Converges.commutes [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a : H →L[ℂ] H)
    (hb : ∀ᶠ i in l, T i*a=a*T i) : V*a=a*V := by
  apply sub_eq_zero.mp
  exact (hT.commutator a).eq_const 0 (hb.mono fun _ h => sub_eq_zero.mpr h)

lemma Converges.commutator_norm [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a : H →L[ℂ] H)
    {C : ℝ} (hC : 0≤C) (hb : ∀ᶠ i in l, ‖T i*a-a*T i‖≤C) : ‖V*a-a*V‖≤C :=
  (hT.commutator a).norm hC hb

lemma Converges.preserves_sandwich [CompleteSpace H] [l.NeBot] (hT : Converges T V l) (a b W : H →L[ℂ] H)
    (hb : ∀ᶠ i in l, a*T i*b=W) : a*V*b=W :=
  ((hT.mul_left a).mul_right b).eq_const W hb

end Kadison.WeakOperatorLimit

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_StageAverage
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped Topology InnerProductSpace

open MeasureTheory MeasureTheory.Measure Filter

namespace Kadison.CompactAverage

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (G : ℕ → Type*) [∀ n, Group (G n)] [∀ n, TopologicalSpace (G n)]
  [∀ n, IsTopologicalGroup (G n)] [∀ n, CompactSpace (G n)]
  [∀ n, MeasurableSpace (G n)] [∀ n, BorelSpace (G n)]

variable (U : ∀ n, G n →* (H ≃ₗᵢ[ℂ] H))
  (hU : ∀ n x, Continuous fun g => U n g x)
  (hnest : ∀ i j, i≤j → ∀ g : G i, ∃ k : G j, U j k=U i g)

variable (μ : ∀ n, Measure (G n)) [∀ n, IsProbabilityMeasure (μ n)] [∀ n, IsMulLeftInvariant (μ n)]

variable (Y : H →L[ℂ] H)

omit [∀ n, IsMulLeftInvariant (μ n)] in
include hU in
lemma scalar_integrable (n : ℕ) (x y : H) :
    Integrable (fun g => inner ℂ (conjugate (U n) Y g x) y) (μ n) :=
  ((conjugate_continuous (U n) (hU n) Y x).inner continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

include hU hnest μ in
theorem exists_stage_average_oai {ι : Type*} (a : ι → H →L[ℂ] H) (C : ι → ℝ)
    (hC : ∀ i, 0≤C i)
    (hb : ∀ n g i, ‖conjugate (U n) Y g * a i-a i*conjugate (U n) Y g‖≤C i)
    (p q s : H →L[ℂ] H)
    (hc : ∀ n g, p*(conjugate (U n) Y g*s-s*conjugate (U n) Y g)*q = p*(Y*s-s*Y)*q) :
    ∃ V : H →L[ℂ] H, ‖V‖≤‖Y‖ ∧
      (∀ n g, V*(U n g : H →L[ℂ] H)=(U n g : H →L[ℂ] H)*V) ∧
      (∀ i, ‖V*a i-a i*V‖≤C i) ∧ p*(V*s-s*V)*q=p*(Y*s-s*Y)*q := by
  choose T hT hcomm hcoeff using fun n => exists_average (U n) (hU n) Y (μ n)
  let ω : Ultrafilter ℕ := Ultrafilter.of atTop
  obtain ⟨V,hV,hlim⟩ := WeakOperatorLimit.exists_ultralimit ω T ‖Y‖ (norm_nonneg _) hT
  have hconv : WeakOperatorLimit.Converges T V (ω:Filter ℕ) := hlim
  refine ⟨V,hV,?_,?_,?_⟩
  · intro n g
    apply hconv.commutes
    have he : ∀ᶠ j : ℕ in atTop, T j*(U n g : H →L[ℂ] H)=(U n g : H →L[ℂ] H)*T j := by
      filter_upwards [eventually_ge_atTop n] with j hj
      obtain ⟨k,hk⟩ := hnest n j hj g
      simpa only [hk] using hcomm j k
    exact (Ultrafilter.of_le atTop) he
  · intro i
    apply hconv.commutator_norm (a i) (hC i)
    exact Eventually.of_forall fun n => WeakOperatorIntegral.commutator_norm (μ n)
      (conjugate (U n) Y) (scalar_integrable G U hU μ Y n) (T n) (hcoeff n)
      (a i) (hC i) (fun g => hb n g i)
  · apply (hconv.commutator s).preserves_sandwich
    exact Eventually.of_forall fun n => WeakOperatorIntegral.preserves_compressed_commutator
      (μ n) (conjugate (U n) Y) (scalar_integrable G U hU μ Y n) (T n) (hcoeff n)
      p q s (p*(Y*s-s*Y)*q) (hc n)

end Kadison.CompactAverage

end

end
end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.Kadison.CompactAverage.exists_stage_average_oai.{u_1, u_2, u_3} := @OAI.Kadison.CompactAverage.exists_stage_average_oai.{u_1, u_2, u_3}
