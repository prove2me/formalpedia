-- Prove2me | solution 1 for OAI.Kadison.PositiveWOT.positive_strong_null
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:23:51.789806+00:00
-- url     : https://prove2.me/submissions/df925331-6b0e-4a07-b0d4-4362788b3906

import Mathlib
import Definitions.Def_OAIQ039C035
import Definitions.Def_OAIQ039C038
import Definitions.Def_OAIQ039C040
import Theorems.Thm_OAI_Kadison_PositiveWOT_exists_smoothing_subsequence
import Theorems.Thm_OAI_Kadison_PositiveWOT_threshold_exhaustion

section
-- module Solutions.OAIQ039_CM.Compat
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SmoothingSubsequence
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter Finset

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sandwich_nonneg {A B : H →L[ℂ] H} (hA : 0≤A) (hB : IsSelfAdjoint B) : 0≤B*A*B := by
  simpa using hB.conjugate_le_conjugate hA

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralThreshold
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma threshold_projection (B : H →L[ℂ] H) (r : ℝ) : IsStarProjection (threshold B r) :=
  Polar.isProjection_rightSupport _

lemma threshold_mem (M : VonNeumannAlgebra H) {B : H →L[ℂ] H} (hB : B∈M) (r : ℝ) :
    threshold B r∈M := by
  apply Polar.rightSupport_mem M
  apply Polar.posPart_mem M
  apply M.toStarSubalgebra.sub_mem hB
  rw [RCLike.real_smul_eq_coe_smul (K:=ℂ)]
  change (Complex.ofReal r) • (1:H →L[ℂ] H)∈M
  exact M.toStarSubalgebra.smul_mem M.one_mem _

lemma threshold_commute {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    Commute (threshold B r) B := by
  let a : H →L[ℂ] H := B-r • (1:H →L[ℂ] H)
  have hr : Commute (r • (1:H →L[ℂ] H)) B := (Commute.one_left B).smul_left r
  have hc : Commute a B := (Commute.refl B).sub_left hr
  have hp : Commute a⁺ B := hc.cfcₙ_real (·⁺)
  have hs : Commute a⁺ (star B) := by rwa [hB.star_eq]
  have hh : Commute (Polar.partialIsometry a⁺) B := Polar.partialIsometry_commutes a⁺ B hp hs
  rw [Polar.partialIsometry_of_nonneg (CFC.posPart_nonneg a)] at hh
  exact hh

lemma threshold_mul_shift {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    threshold B r*(B-r • (1:H →L[ℂ] H))=(B-r • (1:H →L[ℂ] H))⁺ := by
  let a := B-r • (1:H →L[ℂ] H)
  have ha : IsSelfAdjoint a := hB.sub ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one _))
  have hp : Polar.rightSupport a⁺*a⁺=a⁺ := by
    simpa only [CFC.abs_of_nonneg _ (CFC.posPart_nonneg a)] using Polar.initial_mul_abs a⁺
  have hn : Polar.rightSupport a⁺*a⁻=0 :=
    Polar.rightSupport_mul_eq_zero_of_nonneg (CFC.posPart_nonneg a) (CFC.posPart_mul_negPart a)
  change Polar.rightSupport a⁺*a=a⁺
  nth_rw 2 [←CFC.posPart_sub_negPart a ha]
  rw [mul_sub,hp,hn,sub_zero]

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralThresholdBounds
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma threshold_lower {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) (r : ℝ) :
    r • threshold B r≤B*threshold B r := by
  have hh := CFC.posPart_nonneg (B-r • (1:H →L[ℂ] H))
  rw [←threshold_mul_shift hB r,mul_sub,mul_smul_comm,mul_one,
    (threshold_commute hB r).eq] at hh
  exact sub_nonneg.mp hh

lemma threshold_remainder_nonneg {B : H →L[ℂ] H} (hB : 0≤B) (r : ℝ) :
    0≤B*(1-threshold B r) := by
  exact Commute.mul_nonneg hB (threshold_projection B r).one_sub.nonneg
    (((Commute.one_left B).sub_left (threshold_commute (IsSelfAdjoint.of_nonneg hB) r)).symm)

lemma threshold_lower_whole {B : H →L[ℂ] H} (hB : 0≤B) (r : ℝ) :
    r • threshold B r≤B := by
  have hh := threshold_lower (IsSelfAdjoint.of_nonneg hB) r
  have hl : B*threshold B r≤B := by
    have hh := threshold_remainder_nonneg hB r
    rw [mul_sub,mul_one] at hh
    exact sub_nonneg.mp hh
  exact hh.trans hl

lemma threshold_completion_unit {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0 < r) :
    IsUnit (B+r • (1-threshold B r)) := by
  let E := threshold B r
  have hdecomp : r • (1:H →L[ℂ] H)=r • E+r • (1-E) := by
    rw [smul_sub]
    abel
  have hlow : r • E≤B := threshold_lower_whole hB r
  have hl : r • (1:H →L[ℂ] H)≤B+r • (1-E) := by
    rw [hdecomp]
    exact add_le_add hlow le_rfl
  have hs : IsStrictlyPositive (1:H →L[ℂ] H) := by cfc_tac
  exact CStarAlgebra.isUnit_of_le _ hl (IsStrictlyPositive.smul hr hs)

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_SpectralCompression
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma threshold_factor {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0 < r) :
    ∃ C : H →L[ℂ] H,C*B=threshold B r ∧ B*star C=threshold B r := by
  let E := threshold B r
  let D := B+r • (1-E)
  let U : (H →L[ℂ] H)ˣ := (threshold_completion_unit hB hr).unit
  have hu : (U:H →L[ℂ] H)=D := IsUnit.unit_spec _
  let C := (↑U⁻¹:H →L[ℂ] H)*E
  have hp : E*E=E := (threshold_projection B r).isIdempotentElem.eq
  have he : D*E=B*E := by
    dsimp only [D]
    rw [add_mul,smul_mul_assoc,sub_mul,one_mul,hp,sub_self,smul_zero,add_zero]
  have hc : C*B=E := by
    dsimp only [C]
    rw [mul_assoc,(threshold_commute (IsSelfAdjoint.of_nonneg hB) r).eq,←he,←hu,←mul_assoc,Units.inv_mul,one_mul]
  refine ⟨C,hc,?_⟩
  have hh := congrArg star hc
  simpa only [star_mul,(IsSelfAdjoint.of_nonneg hB).star_eq,
    (show star E=E from (threshold_projection B r).isSelfAdjoint.star_eq)] using hh

lemma threshold_compression_tendsto {B : H →L[ℂ] H} (hB : 0≤B) {r : ℝ} (hr : 0 < r)
    (A : ℕ → H →L[ℂ] H)
    (ht : Tendsto (fun n => B*A n*B) atTop (𝓝 0)) :
    Tendsto (fun n => threshold B r*A n*threshold B r) atTop (𝓝 0) := by
  obtain ⟨C,hCB,hBC⟩ := threshold_factor hB hr
  have he (n : ℕ) : threshold B r*A n*threshold B r=C*(B*A n*B)*star C := by
    nth_rw 1 [←hCB]
    nth_rw 1 [←hBC]
    simp only [mul_assoc]
  simp_rw [he]
  simpa only [mul_zero,zero_mul] using (tendsto_const_nhds (x:=C)).mul ht |>.mul (tendsto_const_nhds (x:=star C))

lemma positive_compression_bound {A E : H →L[ℂ] H} (hA : 0≤A) (hA1 : A≤1)
    (hE : IsStarProjection E) : A≤(2:ℝ) • (E*A*E)+(2:ℝ) • (1-E) := by
  let Q := 1-E
  have hQ : IsStarProjection Q := hE.one_sub
  have hsa : IsSelfAdjoint (E-Q) := hE.isSelfAdjoint.sub hQ.isSelfAdjoint
  have hp : 0≤(E-Q)*A*(E-Q) := sandwich_nonneg hA hsa
  have hs : A≤(2:ℝ) • (E*A*E)+(2:ℝ) • (Q*A*Q) := by
    apply sub_nonneg.mp
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [Q]
    simp only [two_smul ℝ]
    noncomm_ring
  have hle : Q*A*Q≤Q := by
    have hh := hQ.isSelfAdjoint.conjugate_le_conjugate hA1
    simpa only [mul_one,hQ.isIdempotentElem.eq] using hh
  have htwo : (2:ℝ) • (Q*A*Q)≤(2:ℝ) • Q := by
    simpa only [two_smul ℝ] using add_le_add hle hle
  exact hs.trans (add_le_add le_rfl htwo)

end Kadison.PositiveWOT

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_ProjectionNormalPositive
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open Filter

open scoped ComplexOrder InnerProductSpace Topology

namespace Kadison.PositiveWOT

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma functional_compression_bound (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ)
    (A E : M) (hA : 0≤A) (h1 : A≤1) (hE : IsStarProjection (E : H →L[ℂ] H)) :
    ‖f A‖≤2*‖f (E*A*E)‖+2*‖f (1-E)‖ := by
  have hl : A≤(E*A*E+E*A*E)+((1-E)+(1-E)) := by
    have hh := positive_compression_bound (show 0≤(A:H →L[ℂ] H) from hA)
      (show (A:H →L[ℂ] H)≤1 from h1) hE
    change (A:H →L[ℂ] H)≤(E:H →L[ℂ] H)*(A:H →L[ℂ] H)*(E:H →L[ℂ] H)+
      (E:H →L[ℂ] H)*(A:H →L[ℂ] H)*(E:H →L[ℂ] H)+
      ((1:H →L[ℂ] H)-(E:H →L[ℂ] H)+((1:H →L[ℂ] H)-(E:H →L[ℂ] H)))
    simpa only [two_smul ℝ] using hh
  have hn := CStarAlgebra.norm_le_norm_of_le_of_nonneg (f.monotone hl) (f.map_nonneg hA)
  change ‖f A‖≤‖f ((E*A*E+E*A*E)+((1-E)+(1-E)))‖ at hn
  simp only [map_add] at hn
  have ht := norm_add_le (f (E*A*E)+f (E*A*E)) (f (1-E)+f (1-E))
  have ht1 := norm_add_le (f (E*A*E)) (f (E*A*E))
  have ht2 := norm_add_le (f (1-E)) (f (1-E))
  linarith

theorem positive_subsequence_null [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (A : ℕ → M) (hA : ∀ n,0≤A n) (h1 : ∀ n,A n≤1)
    (ht : ∀ x,Tendsto (fun n => (A n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    ∃ u : ℕ → ℕ,StrictMono u ∧ Tendsto (fun n => f (A (u n))) atTop (𝓝 0) := by
  obtain ⟨u,hu,B,hBM,hB,hB1,hi,hdecay⟩ := exists_smoothing_subsequence M
    (fun n => (A n : H →L[ℂ] H)) (fun n => (A n).property) hA ht
  let P (n : ℕ) : M := ⟨threshold B (1/((n:ℝ)+1)),threshold_mem M hBM _⟩
  have hp (n : ℕ) : IsStarProjection (P n : H →L[ℂ] H) := threshold_projection B _
  obtain ⟨hmono,hstrong⟩ := threshold_exhaustion M hBM hB hi
  have hfp : Tendsto (fun n => f (P n)) atTop (𝓝 (f 1)) := hf P hp hmono hstrong
  have hfq : Tendsto (fun n => ‖f (1-P n)‖) atTop (𝓝 0) := by
    simp only [map_sub]
    simpa only [sub_self,norm_zero] using ((tendsto_const_nhds (x:=f 1)).sub hfp).norm
  have hbab : Tendsto (fun k => B*(A (u k) : H →L[ℂ] H)*B) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) hdecay tendsto_one_div_add_atTop_nhds_zero_nat)
  have hcompress (n : ℕ) : Tendsto (fun k => ‖f (P n*A (u k)*P n)‖) atTop (𝓝 0) := by
    have hh := threshold_compression_tendsto hB (by positivity : (0:ℝ)<1/((n:ℝ)+1))
      (fun k => (A (u k) : H →L[ℂ] H)) hbab
    have hs : Tendsto (fun k => P n*A (u k)*P n) atTop (𝓝 (0:M)) := tendsto_subtype_rng.mpr hh
    have hfc : Continuous f := map_continuous f
    simpa only [Function.comp_def,map_zero,norm_zero] using (hfc.tendsto 0 |>.comp hs).norm
  refine ⟨u,hu,tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨n,hn⟩ := (hfq.eventually_lt_const (show (0:ℝ)<ε/8 by positivity)).exists
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((hcompress n).eventually_lt_const (show (0:ℝ)<ε/8 by positivity))
  refine ⟨K,?_⟩
  intro k hk
  have hb := functional_compression_bound M f (A (u k)) (P n) (hA _) (h1 _) (hp n)
  have hsmall := hK k hk
  simpa only [dist_zero_right,Real.norm_eq_abs,abs_norm] using (show ‖f (A (u k))‖<ε by linarith)

theorem positive_strong_null_oai [TopologicalSpace.SeparableSpace H]
    (M : VonNeumannAlgebra H) (f : M →ₚ[ℂ] ℂ) (hf : ProjectionContinuousAtOne M f)
    (A : ℕ → M) (hA : ∀ n,0≤A n) (h1 : ∀ n,A n≤1)
    (ht : ∀ x,Tendsto (fun n => (A n : H →L[ℂ] H) x) atTop (𝓝 0)) :
    Tendsto (fun n => f (A n)) atTop (𝓝 0) := by
  apply tendsto_of_subseq_tendsto
  intro v hv
  obtain ⟨u,hu,hlim⟩ := positive_subsequence_null M f hf (fun n => A (v n))
    (fun n => hA (v n)) (fun n => h1 (v n)) (fun x => (ht x).comp hv)
  exact ⟨u,hlim⟩

end Kadison.PositiveWOT

end

end
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Kadison.PositiveWOT.positive_strong_null_oai.{u_1} := @OAI.Kadison.PositiveWOT.positive_strong_null_oai.{u_1}
