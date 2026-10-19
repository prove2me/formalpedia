-- Prove2me | solution 1 for HunterPDE.Parabolic.form_time_regularity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-17T05:09:36.443642+00:00
-- url     : https://prove2.me/submissions/1a529815-16a9-4cf1-a261-6651fb8d98ba

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

/-! Child of the reduction of `HunterPDE.Parabolic.galerkin_limit` (Hunter, *Notes on PDEs*, §6.1):
under Assumption 6.1 the time-dependent bilinear form `a(u, v; t)` is, for a.e. `t`, a bounded
(hence continuous) bilinear form on `H¹₀(Ω)`; `t ↦ ψ(t) a(f(t), v; t)` is integrable on `(0, T)` for
bounded measurable `ψ` and `f ∈ L²(0, T; H¹₀)`; and it passes to weak limits in `L²(0, T; H¹₀)`. -/

set_option autoImplicit false
set_option linter.all false

section Q0ffd_I
/-! Shortcut instances for `H¹₀(Ω)` and `H⁻¹(Ω)`: each one is exactly the instance that type-class
search finds anyway (`inferInstance`), declared once with high priority so that later searches stop at
it instead of re-deriving it through the submodule / continuous-linear-map hierarchy every time.
They are `scoped` (opened in each block below, not at the final `theorem solution`), so the
statement of `solution` is elaborated with the standard instances, exactly like the target's. -/
open MeasureTheory
namespace HunterPDE.Parabolic.Q0ffdFast
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
noncomputable scoped instance (priority := high) q0ffdEMS : MeasureSpace (EuclideanSpace ℝ (Fin n)) :=
  inferInstance
noncomputable scoped instance (priority := high) q0ffdH10NACG : NormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10SACG : SeminormedAddCommGroup (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10IPS : InnerProductSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10NS : NormedSpace ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdH10Mod : Module ℝ (H10 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1NACG : NormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1SACG : SeminormedAddCommGroup (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1NS : NormedSpace ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1Mod : Module ℝ (Hm1 n Ω) := inferInstance
noncomputable scoped instance (priority := high) q0ffdHm1CS : CompleteSpace (Hm1 n Ω) := inferInstance
end HunterPDE.Parabolic.Q0ffdFast
end Q0ffd_I

section Q0ffd_L0
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section ht
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}



instance fact_two_ne_top : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

instance : TopologicalSpace.SeparableSpace (Jet n) := by
  haveI : ProperSpace (Jet n) := FiniteDimensional.proper ℝ _
  infer_instance

lemma separable_H10 : TopologicalSpace.SeparableSpace (H10 n Ω) := by
  have : SecondCountableTopology (JetL2 n Ω) := inferInstance
  infer_instance

end ht

section b1
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}



/-! ## Components of `H¹₀` elements as `L²` functions -/

noncomputable def pdCLM (n : ℕ) (j : Fin n) : Jet n →L[ℝ] ℝ :=
  (EuclideanSpace.proj j).comp (WithLp.sndL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n)))

noncomputable def pdL (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (j : Fin n) :
    H10 n Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  ((pdCLM n j).compLpL 2 (volume.restrict Ω)).comp (H10 n Ω).subtypeL

lemma pdL_ae (j : Fin n) (u : H10 n Ω) :
    (pdL n Ω j u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] pd u j := by
  have := (pdCLM n j).coeFn_compLp (μ := volume.restrict Ω) (p := 2) (u : JetL2 n Ω)
  filter_upwards [this] with x hx
  exact hx

lemma val_ae (u : H10 n Ω) :
    (toL2L n Ω u : EuclideanSpace ℝ (Fin n) → ℝ) =ᵐ[volume.restrict Ω] val u := by
  have := (WithLp.fstL 2 ℝ ℝ (EuclideanSpace ℝ (Fin n))).coeFn_compLp
    (μ := volume.restrict Ω) (p := 2) (u : JetL2 n Ω)
  filter_upwards [this] with x hx
  exact hx

lemma val_memLp (u : H10 n Ω) : MemLp (val u) 2 (volume.restrict Ω) :=
  (Lp.memLp (toL2L n Ω u)).ae_eq (val_ae u)

lemma pd_memLp (u : H10 n Ω) (j : Fin n) : MemLp (pd u j) 2 (volume.restrict Ω) :=
  (Lp.memLp (pdL n Ω j u)).ae_eq (pdL_ae j u)

lemma val_add (u₁ u₂ : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), val (u₁ + u₂) x = val u₁ x + val u₂ x := by
  have h := Lp.coeFn_add (toL2L n Ω u₁) (toL2L n Ω u₂)
  rw [← ContinuousLinearMap.map_add] at h
  filter_upwards [val_ae (u₁ + u₂), val_ae u₁, val_ae u₂, h] with x h0 h1 h2 h3
  exact h0.symm.trans (h3.trans (congrArg₂ (· + ·) h1 h2))

lemma pd_add (u₁ u₂ : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ j, pd (u₁ + u₂) j x = pd u₁ j x + pd u₂ j x := by
  rw [ae_all_iff]
  intro j
  have h := Lp.coeFn_add (pdL n Ω j u₁) (pdL n Ω j u₂)
  rw [← ContinuousLinearMap.map_add] at h
  filter_upwards [pdL_ae j (u₁ + u₂), pdL_ae j u₁, pdL_ae j u₂, h] with x h0 h1 h2 h3
  exact h0.symm.trans (h3.trans (congrArg₂ (· + ·) h1 h2))

lemma val_smul (c : ℝ) (u : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), val (c • u) x = c * val u x := by
  have h := Lp.coeFn_smul c (toL2L n Ω u)
  rw [← ContinuousLinearMap.map_smul] at h
  filter_upwards [val_ae (c • u), val_ae u, h] with x h0 h1 h3
  exact h0.symm.trans (h3.trans (congrArg (c * ·) h1))

lemma pd_smul (c : ℝ) (u : H10 n Ω) :
    ∀ᵐ x ∂(volume.restrict Ω), ∀ j, pd (c • u) j x = c * pd u j x := by
  rw [ae_all_iff]
  intro j
  have h := Lp.coeFn_smul c (pdL n Ω j u)
  rw [← ContinuousLinearMap.map_smul] at h
  filter_upwards [pdL_ae j (c • u), pdL_ae j u, h] with x h0 h1 h3
  exact h0.symm.trans (h3.trans (congrArg (c * ·) h1))

/-! ## Time sections of coefficients on the cylinder -/

lemma ae_time_of_cyl {T : ℝ} {p : EuclideanSpace ℝ (Fin n) × ℝ → Prop}
    (h : ∀ᵐ q ∂(cylMeasure Ω T), p q) :
    ∀ᵐ t ∂(timeMeasure T), ∀ᵐ x ∂(volume.restrict Ω), p (x, t) := by
  have h2 : ∀ᵐ z ∂((timeMeasure T).prod (volume.restrict Ω)), p z.swap :=
    (Measure.measurePreserving_swap (μ := timeMeasure T)
      (ν := volume.restrict Ω)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h2

lemma aesm_time_of_cyl {T : ℝ} {f : EuclideanSpace ℝ (Fin n) × ℝ → ℝ}
    (h : AEStronglyMeasurable f (cylMeasure Ω T)) :
    ∀ᵐ t ∂(timeMeasure T), AEStronglyMeasurable (fun x => f (x, t)) (volume.restrict Ω) :=
  (h.comp_measurePreserving (Measure.measurePreserving_swap (μ := timeMeasure T)
      (ν := volume.restrict Ω))).prodMk_left

lemma ae_bound_of_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (h : MemLp f ⊤ μ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ q ∂μ, |f q| ≤ M := by
  refine ⟨(eLpNorm f ⊤ μ).toReal, ENNReal.toReal_nonneg, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with q hq
  have hlt := h.eLpNorm_lt_top
  rw [eLpNorm_exponent_top] at hlt ⊢
  have := ENNReal.toReal_mono hlt.ne hq
  rwa [toReal_enorm, Real.norm_eq_abs] at this

/-- A time `t` at which the coefficients are measurable and bounded by `M` on `Ω` and elliptic
with constant `θ`. -/
def GoodT (P : Coeffs n) (Ω : Set (EuclideanSpace ℝ (Fin n))) (θ M t : ℝ) : Prop :=
  (∀ i j, AEStronglyMeasurable (fun x => P.a i j x t) (volume.restrict Ω)) ∧
  (∀ j, AEStronglyMeasurable (fun x => P.b j x t) (volume.restrict Ω)) ∧
  AEStronglyMeasurable (fun x => P.c x t) (volume.restrict Ω) ∧
  (∀ᵐ x ∂(volume.restrict Ω), (∀ i j, |P.a i j x t| ≤ M) ∧ (∀ j, |P.b j x t| ≤ M) ∧
    |P.c x t| ≤ M ∧ ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j x t * ξ i * ξ j)

lemma good_ae {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T) :
    ∃ θ M : ℝ, 0 < θ ∧ 0 ≤ M ∧ ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t := by
  obtain ⟨ha, hb, hc, -, θ, hθ, hell⟩ := hP
  choose Ma hMa0 hMa using fun i j => ae_bound_of_top (ha i j)
  choose Mb hMb0 hMb using fun j => ae_bound_of_top (hb j)
  have hob8 := ae_bound_of_top hc
  obtain ⟨Mc, hMc0, hMc⟩ := hob8
  have hob9 : ∃ M, M = (∑ i, ∑ j, Ma i j) + (∑ j, Mb j) + Mc := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ := hob9
  have hSa : 0 ≤ ∑ i, ∑ j, Ma i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hMa0 i j
  have hSb : 0 ≤ ∑ j, Mb j := Finset.sum_nonneg fun j _ => hMb0 j
  have hMa_le : ∀ i j, Ma i j ≤ M := by
    intro i j
    have h1 : Ma i j ≤ ∑ j', Ma i j' :=
      Finset.single_le_sum (f := fun j' => Ma i j') (fun j' _ => hMa0 i j') (Finset.mem_univ j)
    have h2 : ∑ j', Ma i j' ≤ ∑ i', ∑ j', Ma i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', Ma i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hMa0 i' j') (Finset.mem_univ i)
    linarith
  have hMb_le : ∀ j, Mb j ≤ M := by
    intro j
    have h1 : Mb j ≤ ∑ j', Mb j' :=
      Finset.single_le_sum (f := fun j' => Mb j') (fun j' _ => hMb0 j') (Finset.mem_univ j)
    linarith
  have hMc_le : Mc ≤ M := by linarith
  refine ⟨θ, M, hθ, by linarith, ?_⟩
  have h1 : ∀ᵐ q ∂(cylMeasure Ω T), ∀ i j, |P.a i j q.1 q.2| ≤ Ma i j := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; exact hMa i
  have h2 : ∀ᵐ q ∂(cylMeasure Ω T), ∀ j, |P.b j q.1 q.2| ≤ Mb j := by
    rw [ae_all_iff]; exact hMb
  have hall : ∀ᵐ q ∂(cylMeasure Ω T), (∀ i j, |P.a i j q.1 q.2| ≤ M) ∧
      (∀ j, |P.b j q.1 q.2| ≤ M) ∧ |P.c q.1 q.2| ≤ M ∧
      ∀ ξ : Fin n → ℝ, θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, P.a i j q.1 q.2 * ξ i * ξ j := by
    filter_upwards [h1, h2, hMc, hell] with q q1 q2 q3 q4
    exact ⟨fun i j => (q1 i j).trans (hMa_le i j), fun j => (q2 j).trans (hMb_le j),
      q3.trans hMc_le, q4⟩
  have hA : ∀ᵐ t ∂(timeMeasure T), ∀ i j,
      AEStronglyMeasurable (fun x => P.a i j x t) (volume.restrict Ω) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    exact aesm_time_of_cyl (f := fun p => P.a i j p.1 p.2) (ha i j).aestronglyMeasurable
  have hB : ∀ᵐ t ∂(timeMeasure T), ∀ j,
      AEStronglyMeasurable (fun x => P.b j x t) (volume.restrict Ω) := by
    rw [ae_all_iff]; intro j
    exact aesm_time_of_cyl (f := fun p => P.b j p.1 p.2) (hb j).aestronglyMeasurable
  have hC : ∀ᵐ t ∂(timeMeasure T),
      AEStronglyMeasurable (fun x => P.c x t) (volume.restrict Ω) :=
    aesm_time_of_cyl (f := fun p => P.c p.1 p.2) hc.aestronglyMeasurable
  filter_upwards [hA, hB, hC, ae_time_of_cyl hall] with t t1 t2 t3 t4
  exact ⟨t1, t2, t3, t4⟩

/-! ## The form at a good time -/

lemma int3 {X : Type*} [MeasurableSpace X] {μ : Measure X} {g p q : X → ℝ} {M : ℝ}
    (hg : AEStronglyMeasurable g μ) (hgb : ∀ᵐ x ∂μ, |g x| ≤ M) (hp : MemLp p 2 μ)
    (hq : MemLp q 2 μ) : Integrable (fun x => g x * p x * q x) μ := by
  have hgp : MemLp (fun x => g x * p x) 2 μ := by
    refine hp.of_le_mul (c := M) (hg.mul hp.1) ?_
    filter_upwards [hgb] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  exact hgp.integrable_mul hq

section good
variable {P : Coeffs n} {θ M t : ℝ}

lemma form_terms_int (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    (∀ i j, Integrable (fun x => P.a i j x t * pd u i x * pd v j x) (volume.restrict Ω)) ∧
    (∀ j, Integrable (fun x => P.b j x t * pd u j x * val v x) (volume.restrict Ω)) ∧
    Integrable (fun x => P.c x t * val u x * val v x) (volume.restrict Ω) := by
  obtain ⟨ha, hb, hc, hbd⟩ := hg
  refine ⟨fun i j => int3 (M := M) (ha i j) ?_ (pd_memLp u i) (pd_memLp v j),
    fun j => int3 (M := M) (hb j) ?_ (pd_memLp u j) (val_memLp v), int3 (M := M) hc ?_ (val_memLp u) (val_memLp v)⟩
  · filter_upwards [hbd] with x hx using hx.1 i j
  · filter_upwards [hbd] with x hx using hx.2.1 j
  · filter_upwards [hbd] with x hx using hx.2.2.1

lemma form_integrand_int (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    Integrable (fun x => (∑ i, ∑ j, P.a i j x t * pd u i x * pd v j x) +
      (∑ j, P.b j x t * pd u j x * val v x) + P.c x t * val u x * val v x)
      (volume.restrict Ω) := by
  have hob10 := form_terms_int hg u v
  obtain ⟨hA, hB, hC⟩ := hob10
  exact ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hA i j).add
    (integrable_finsetSum _ fun j _ => hB j)).add hC

/-- The integrand of the bilinear form, as a function of the jets of `u` and `v` at the point. -/
def qf (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (U : Fin n → ℝ) (u0 : ℝ)
    (V : Fin n → ℝ) (v0 : ℝ) : ℝ :=
  (∑ i, ∑ j, P.a i j x t * U i * V j) + (∑ j, P.b j x t * U j * v0) + P.c x t * u0 * v0

lemma qf_add_left (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (U U' : Fin n → ℝ)
    (u0 u0' : ℝ) (V : Fin n → ℝ) (v0 : ℝ) :
    qf P t x (fun i => U i + U' i) (u0 + u0') V v0 = qf P t x U u0 V v0 + qf P t x U' u0' V v0 := by
  simp only [qf, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma qf_add_right (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (U : Fin n → ℝ) (u0 : ℝ)
    (V V' : Fin n → ℝ) (v0 v0' : ℝ) :
    qf P t x U u0 (fun i => V i + V' i) (v0 + v0') = qf P t x U u0 V v0 + qf P t x U u0 V' v0' := by
  simp only [qf, mul_add, add_mul, Finset.sum_add_distrib]
  ring

lemma qf_smul_left (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (U : Fin n → ℝ)
    (u0 : ℝ) (V : Fin n → ℝ) (v0 : ℝ) :
    qf P t x (fun i => c * U i) (c * u0) V v0 = c * qf P t x U u0 V v0 := by
  have hA : (∑ i, ∑ j, P.a i j x t * (c * U i) * V j) = c * ∑ i, ∑ j, P.a i j x t * U i * V j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : (∑ j, P.b j x t * (c * U j) * v0) = c * ∑ j, P.b j x t * U j * v0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold qf
  rw [hA, hB]
  ring

lemma qf_smul_right (P : Coeffs n) (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ) (U : Fin n → ℝ)
    (u0 : ℝ) (V : Fin n → ℝ) (v0 : ℝ) :
    qf P t x U u0 (fun i => c * V i) (c * v0) = c * qf P t x U u0 V v0 := by
  have hA : (∑ i, ∑ j, P.a i j x t * U i * (c * V j)) = c * ∑ i, ∑ j, P.a i j x t * U i * V j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hB : (∑ j, P.b j x t * U j * (c * v0)) = c * ∑ j, P.b j x t * U j * v0 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  unfold qf
  rw [hA, hB]
  ring

lemma form_eq_qf (P : Coeffs n) (t : ℝ) (u v : H10 n Ω) :
    form P t u v = ∫ x in Ω, qf P t x (fun i => pd u i x) (val u x) (fun j => pd v j x) (val v x) :=
  rfl

lemma qf_int (hg : GoodT P Ω θ M t) (u v : H10 n Ω) :
    Integrable (fun x => qf P t x (fun i => pd u i x) (val u x) (fun j => pd v j x) (val v x))
      (volume.restrict Ω) :=
  form_integrand_int hg u v

lemma form_add_left (hg : GoodT P Ω θ M t) (u₁ u₂ v : H10 n Ω) :
    form P t (u₁ + u₂) v = form P t u₁ v + form P t u₂ v := by
  rw [form_eq_qf, form_eq_qf, form_eq_qf, ← integral_add (qf_int hg u₁ v) (qf_int hg u₂ v)]
  refine integral_congr_ae ?_
  filter_upwards [pd_add u₁ u₂, val_add u₁ u₂] with x hpd hval
  have : (fun i => pd (u₁ + u₂) i x) = fun i => pd u₁ i x + pd u₂ i x := funext hpd
  rw [this, hval, qf_add_left]

lemma form_smul_left (hg : GoodT P Ω θ M t) (c : ℝ) (u v : H10 n Ω) :
    form P t (c • u) v = c * form P t u v := by
  rw [form_eq_qf, form_eq_qf, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [pd_smul c u, val_smul c u] with x hpd hval
  have : (fun i => pd (c • u) i x) = fun i => c * pd u i x := funext hpd
  rw [this, hval, qf_smul_left]

lemma form_add_right (hg : GoodT P Ω θ M t) (u v₁ v₂ : H10 n Ω) :
    form P t u (v₁ + v₂) = form P t u v₁ + form P t u v₂ := by
  rw [form_eq_qf, form_eq_qf, form_eq_qf, ← integral_add (qf_int hg u v₁) (qf_int hg u v₂)]
  refine integral_congr_ae ?_
  filter_upwards [pd_add v₁ v₂, val_add v₁ v₂] with x hpd hval
  have : (fun i => pd (v₁ + v₂) i x) = fun i => pd v₁ i x + pd v₂ i x := funext hpd
  rw [this, hval, qf_add_right]

lemma form_smul_right (hg : GoodT P Ω θ M t) (c : ℝ) (u v : H10 n Ω) :
    form P t u (c • v) = c * form P t u v := by
  rw [form_eq_qf, form_eq_qf, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [pd_smul c v, val_smul c v] with x hpd hval
  have : (fun i => pd (c • v) i x) = fun i => c * pd v i x := funext hpd
  rw [this, hval, qf_smul_right]

/-- Pointwise bound on the integrand of the form at a good time. -/
noncomputable def qBnd (M : ℝ) (u v : H10 n Ω) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  M * ((∑ i, ∑ j, |pd u i x * pd v j x|) + (∑ j, |pd u j x * val v x|) + |val u x * val v x|)

lemma qBnd_int (M : ℝ) (u v : H10 n Ω) : Integrable (qBnd M u v) (volume.restrict Ω) := by
  have h1 : ∀ i j, Integrable (fun x => |pd u i x * pd v j x|) (volume.restrict Ω) :=
    fun i j => ((pd_memLp u i).integrable_mul (pd_memLp v j)).abs
  have h2 : ∀ j, Integrable (fun x => |pd u j x * val v x|) (volume.restrict Ω) :=
    fun j => ((pd_memLp u j).integrable_mul (val_memLp v)).abs
  have h3 : Integrable (fun x => |val u x * val v x|) (volume.restrict Ω) :=
    ((val_memLp u).integrable_mul (val_memLp v)).abs
  exact (((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j).add
    (integrable_finsetSum _ fun j _ => h2 j)).add h3).const_mul M

noncomputable def formBnd (M : ℝ) (u v : H10 n Ω) : ℝ := ∫ x in Ω, qBnd M u v x

lemma qf_abs_le {t M : ℝ} {x : EuclideanSpace ℝ (Fin n)} (P : Coeffs n) (U V : Fin n → ℝ) (u0 v0 : ℝ)
    (ha : ∀ i j, |P.a i j x t| ≤ M) (hb : ∀ j, |P.b j x t| ≤ M) (hc : |P.c x t| ≤ M) :
    |qf P t x U u0 V v0| ≤
      M * ((∑ i, ∑ j, |U i * V j|) + (∑ j, |U j * v0|) + |u0 * v0|) := by
  have h1 : |∑ i, ∑ j, P.a i j x t * U i * V j| ≤ M * ∑ i, ∑ j, |U i * V j| := by
    calc |∑ i, ∑ j, P.a i j x t * U i * V j| ≤ ∑ i, |∑ j, P.a i j x t * U i * V j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |P.a i j x t * U i * V j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, M * |U i * V j| :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [mul_assoc, abs_mul]
            exact mul_le_mul_of_nonneg_right (ha i j) (abs_nonneg _)
      _ = M * ∑ i, ∑ j, |U i * V j| := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
  have h2 : |∑ j, P.b j x t * U j * v0| ≤ M * ∑ j, |U j * v0| := by
    calc |∑ j, P.b j x t * U j * v0| ≤ ∑ j, |P.b j x t * U j * v0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, M * |U j * v0| :=
          Finset.sum_le_sum fun j _ => by
            rw [mul_assoc, abs_mul]
            exact mul_le_mul_of_nonneg_right (hb j) (abs_nonneg _)
      _ = M * ∑ j, |U j * v0| := by rw [Finset.mul_sum]
  have h3 : |P.c x t * u0 * v0| ≤ M * |u0 * v0| := by
    rw [mul_assoc, abs_mul]
    exact mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  unfold qf
  calc _ ≤ |(∑ i, ∑ j, P.a i j x t * U i * V j) + (∑ j, P.b j x t * U j * v0)| +
        |P.c x t * u0 * v0| := abs_add_le _ _
    _ ≤ |∑ i, ∑ j, P.a i j x t * U i * V j| + |∑ j, P.b j x t * U j * v0| +
        |P.c x t * u0 * v0| := by gcongr; exact abs_add_le _ _
    _ ≤ _ := by linarith

lemma form_abs_le (hg : GoodT P Ω θ M t) (u v : H10 n Ω) : |form P t u v| ≤ formBnd M u v := by
  rw [form_eq_qf, formBnd]
  have := norm_integral_le_of_norm_le (qBnd_int M u v) (μ := volume.restrict Ω)
    (f := fun x => qf P t x (fun i => pd u i x) (val u x) (fun j => pd v j x) (val v x)) (by
      obtain ⟨-, -, -, hbd⟩ := hg
      filter_upwards [hbd] with x hx
      rw [Real.norm_eq_abs]
      exact qf_abs_le P _ _ _ _ hx.1 hx.2.1 hx.2.2.1)
  rwa [Real.norm_eq_abs] at this

end good

/-! ## Measurability of the form in time -/

lemma form_aesm {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T) (u v : H10 n Ω) :
    AEStronglyMeasurable (fun t => form P t u v) (timeMeasure T) := by
  obtain ⟨ha, hb, hc, -, -⟩ := hP
  have hfst : ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, AEStronglyMeasurable f (volume.restrict Ω) →
      AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ => f q.1) (cylMeasure Ω T) :=
    fun hf => hf.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_fst (μ := volume.restrict Ω) (ν := timeMeasure T))
  have hG : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
      qf P q.2 q.1 (fun i => pd u i q.1) (val u q.1) (fun j => pd v j q.1) (val v q.1))
      (cylMeasure Ω T) := by
    have e1 : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        ∑ i, ∑ j, P.a i j q.1 q.2 * pd u i q.1 * pd v j q.1) (cylMeasure Ω T) :=
      Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (((ha i j).aestronglyMeasurable).mul (hfst (pd_memLp u i).aestronglyMeasurable)).mul
          (hfst (pd_memLp v j).aestronglyMeasurable)
    have e2 : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        ∑ j, P.b j q.1 q.2 * pd u j q.1 * val v q.1) (cylMeasure Ω T) :=
      Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        (((hb j).aestronglyMeasurable).mul (hfst (pd_memLp u j).aestronglyMeasurable)).mul
          (hfst (val_memLp v).aestronglyMeasurable)
    have e3 : AEStronglyMeasurable (fun q : EuclideanSpace ℝ (Fin n) × ℝ =>
        P.c q.1 q.2 * val u q.1 * val v q.1) (cylMeasure Ω T) :=
      ((hc.aestronglyMeasurable).mul (hfst (val_memLp u).aestronglyMeasurable)).mul
        (hfst (val_memLp v).aestronglyMeasurable)
    exact (e1.add e2).add e3
  have hsw := hG.comp_measurePreserving
    (Measure.measurePreserving_swap (μ := timeMeasure T) (ν := volume.restrict Ω))
  exact hsw.integral_prod_right'


end b1

section b2
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}


/-! ## `L²` inner product, coordinates and the Galerkin space -/

section orth
variable {w : ℕ → H10 n Ω}

end orth


end b2

end HunterPDE.Parabolic
end Q0ffd_L0

section Q0ffd_W
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section weak
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

end weak

section linf
variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

end linf

section lpfun
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {μ : Measure ℝ}

lemma inner_toLp {f g : ℝ → V} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ t, inner ℝ (f t) (g t) ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with t h1 h2
  rw [h1, h2]

theorem weak_clm [IsFiniteMeasure μ] {x : ℕ → ℝ → V} {y : ℝ → V}
    (hx : ∀ k, MemLp (x k) 2 μ) (hy : MemLp y 2 μ)
    (hconv : ∀ Z : ℝ → V, MemLp Z 2 μ →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂μ) atTop (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂μ)))
    (Λ : Lp V 2 μ →L[ℝ] ℝ) :
    Tendsto (fun k => Λ ((hx k).toLp (x k))) atTop (𝓝 (Λ (hy.toLp y))) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Zl : Lp V 2 μ := (InnerProductSpace.toDual ℝ (Lp V 2 μ)).symm Λ with hZl
  have hΛ : ∀ w : Lp V 2 μ, Λ w = inner ℝ Zl w := by
    intro w; rw [hZl, InnerProductSpace.toDual_symm_apply]
  have h := hconv ⇑Zl (Lp.memLp Zl)
  have e1 : ∀ k, Λ ((hx k).toLp (x k)) = ∫ t, inner ℝ (Zl t) (x k t) ∂μ := by
    intro k; rw [hΛ]
    have := inner_toLp (Lp.memLp Zl) (hx k)
    rwa [Lp.toLp_coeFn] at this
  have e2 : Λ (hy.toLp y) = ∫ t, inner ℝ (Zl t) (y t) ∂μ := by
    rw [hΛ]
    have := inner_toLp (Lp.memLp Zl) hy
    rwa [Lp.toLp_coeFn] at this
  simpa only [e1, e2] using h

end lpfun
end HunterPDE.Parabolic
end Q0ffd_W

section Q0ffd_R
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section riesz
variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

variable {V}

end riesz

section eval
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

end eval

section wtd
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

end wtd

end HunterPDE.Parabolic
end Q0ffd_R

section Q0ffd_R2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section r2

end r2
end HunterPDE.Parabolic
end Q0ffd_R2

section Q0ffd_F
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section F
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma integral_abs_mul_le {α : Type*} {m : MeasurableSpace α} {ν : Measure α} {f g : α → ℝ}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ∫ x, |f x * g x| ∂ν ≤ (eLpNorm f 2 ν).toReal * (eLpNorm g 2 ν).toReal := by
  have : Fact ((1:ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hF := hf.norm
  have hG := hg.norm
  have h := real_inner_le_norm (hF.toLp _) (hG.toLp _)
  have e : inner ℝ (hF.toLp _) (hG.toLp _) = ∫ x, |f x * g x| ∂ν := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp only [Real.norm_eq_abs, RCLike.inner_apply, Real.ringHom_apply, mul_comm, abs_mul]
  rw [e, Lp.norm_toLp, Lp.norm_toLp, eLpNorm_norm, eLpNorm_norm] at h
  exact h

lemma eLpNorm_pd (u : H10 n Ω) (j : Fin n) :
    (eLpNorm (pd u j) 2 (volume.restrict Ω)).toReal = ‖pdL n Ω j u‖ := by
  rw [Lp.norm_def]; congr 1; exact eLpNorm_congr_ae (pdL_ae j u).symm

lemma eLpNorm_val (u : H10 n Ω) :
    (eLpNorm (val u) 2 (volume.restrict Ω)).toReal = ‖toL2L n Ω u‖ := by
  rw [Lp.norm_def]; congr 1; exact eLpNorm_congr_ae (val_ae u).symm

noncomputable def formK (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) (M : ℝ) : ℝ :=
  M * ((∑ i, ∑ j, ‖pdL n Ω i‖ * ‖pdL n Ω j‖) + (∑ j, ‖pdL n Ω j‖ * ‖toL2L n Ω‖) +
    ‖toL2L n Ω‖ * ‖toL2L n Ω‖)

lemma form_le {P : Coeffs n} {θ M t : ℝ} (hg : GoodT P Ω θ M t) (hM : 0 ≤ M) (u v : H10 n Ω) :
    |form P t u v| ≤ formK n Ω M * ‖u‖ * ‖v‖ := by
  refine (form_abs_le hg u v).trans ?_
  unfold formBnd qBnd
  have h1 : ∀ i j, Integrable (fun x => |pd u i x * pd v j x|) (volume.restrict Ω) :=
    fun i j => ((pd_memLp u i).integrable_mul (pd_memLp v j)).abs
  have h2 : ∀ j, Integrable (fun x => |pd u j x * val v x|) (volume.restrict Ω) :=
    fun j => ((pd_memLp u j).integrable_mul (val_memLp v)).abs
  have h3 : Integrable (fun x => |val u x * val v x|) (volume.restrict Ω) :=
    ((val_memLp u).integrable_mul (val_memLp v)).abs
  have hS1 : Integrable (fun x => ∑ i, ∑ j, |pd u i x * pd v j x|) (volume.restrict Ω) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j
  have hS2 : Integrable (fun x => ∑ j, |pd u j x * val v x|) (volume.restrict Ω) :=
    integrable_finsetSum _ fun j _ => h2 j
  have hS12 : Integrable (fun x => (∑ i, ∑ j, |pd u i x * pd v j x|) +
      ∑ j, |pd u j x * val v x|) (volume.restrict Ω) := hS1.add hS2
  have e1 : (∑ i, ∫ x in Ω, ∑ j, |pd u i x * pd v j x|) =
      ∑ i, ∑ j, ∫ x in Ω, |pd u i x * pd v j x| :=
    Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => h1 i j
  rw [integral_const_mul, integral_add hS12 h3, integral_add hS1 hS2,
    integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => h1 i j),
    integral_finsetSum _ (fun j _ => h2 j), e1]
  have hA : ∀ i j, ∫ x in Ω, |pd u i x * pd v j x| ≤ (‖pdL n Ω i‖ * ‖pdL n Ω j‖) * (‖u‖ * ‖v‖) := by
    intro i j
    refine (integral_abs_mul_le (pd_memLp u i) (pd_memLp v j)).trans ?_
    rw [eLpNorm_pd, eLpNorm_pd]
    calc ‖pdL n Ω i u‖ * ‖pdL n Ω j v‖ ≤ (‖pdL n Ω i‖ * ‖u‖) * (‖pdL n Ω j‖ * ‖v‖) :=
          mul_le_mul ((pdL n Ω i).le_opNorm u) ((pdL n Ω j).le_opNorm v) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hB : ∀ j, ∫ x in Ω, |pd u j x * val v x| ≤ (‖pdL n Ω j‖ * ‖toL2L n Ω‖) * (‖u‖ * ‖v‖) := by
    intro j
    refine (integral_abs_mul_le (pd_memLp u j) (val_memLp v)).trans ?_
    rw [eLpNorm_pd, eLpNorm_val]
    calc ‖pdL n Ω j u‖ * ‖toL2L n Ω v‖ ≤ (‖pdL n Ω j‖ * ‖u‖) * (‖toL2L n Ω‖ * ‖v‖) :=
          mul_le_mul ((pdL n Ω j).le_opNorm u) ((toL2L n Ω).le_opNorm v) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hC : ∫ x in Ω, |val u x * val v x| ≤ (‖toL2L n Ω‖ * ‖toL2L n Ω‖) * (‖u‖ * ‖v‖) := by
    refine (integral_abs_mul_le (val_memLp u) (val_memLp v)).trans ?_
    rw [eLpNorm_val, eLpNorm_val]
    calc ‖toL2L n Ω u‖ * ‖toL2L n Ω v‖ ≤ (‖toL2L n Ω‖ * ‖u‖) * (‖toL2L n Ω‖ * ‖v‖) :=
          mul_le_mul ((toL2L n Ω).le_opNorm u) ((toL2L n Ω).le_opNorm v) (norm_nonneg _)
            (by positivity)
      _ = _ := by ring
  have hsum : (∑ i, ∑ j, ∫ x in Ω, |pd u i x * pd v j x|) + (∑ j, ∫ x in Ω, |pd u j x * val v x|) +
      ∫ x in Ω, |val u x * val v x| ≤
      ((∑ i, ∑ j, ‖pdL n Ω i‖ * ‖pdL n Ω j‖) + (∑ j, ‖pdL n Ω j‖ * ‖toL2L n Ω‖) +
        ‖toL2L n Ω‖ * ‖toL2L n Ω‖) * (‖u‖ * ‖v‖) := by
    rw [add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
    refine add_le_add (add_le_add ?_ ?_) hC
    · refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hA i j
    · exact Finset.sum_le_sum fun j _ => hB j
  calc M * _ ≤ M * (((∑ i, ∑ j, ‖pdL n Ω i‖ * ‖pdL n Ω j‖) + (∑ j, ‖pdL n Ω j‖ * ‖toL2L n Ω‖) +
        ‖toL2L n Ω‖ * ‖toL2L n Ω‖) * (‖u‖ * ‖v‖)) := mul_le_mul_of_nonneg_left hsum hM
    _ = formK n Ω M * ‖u‖ * ‖v‖ := by unfold formK; ring

lemma form_sub_left' {P : Coeffs n} {θ M t : ℝ} (hg : GoodT P Ω θ M t) (u₁ u₂ v : H10 n Ω) :
    form P t (u₁ - u₂) v = form P t u₁ v - form P t u₂ v := by
  have : u₁ - u₂ = u₁ + (-1 : ℝ) • u₂ := by rw [neg_one_smul, sub_eq_add_neg]
  rw [this, form_add_left hg, form_smul_left hg]; ring

noncomputable def formCLM {P : Coeffs n} {θ M t : ℝ} (hg : GoodT P Ω θ M t) (hM : 0 ≤ M)
    (u : H10 n Ω) : H10 n Ω →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun v => form P t u v
      map_add' := fun a b => form_add_right hg u a b
      map_smul' := fun c a => by simpa only [Real.ringHom_apply, smul_eq_mul] using form_smul_right hg c u a }
    (formK n Ω M * ‖u‖) (fun v => by
      have := form_le hg hM u v
      rw [Real.norm_eq_abs]
      calc _ ≤ formK n Ω M * ‖u‖ * ‖v‖ := by
            simpa only [LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_norm, mul_assoc] using this
        _ = _ := by ring)

lemma form_tendsto_left {P : Coeffs n} {θ M t : ℝ} (hg : GoodT P Ω θ M t) (hM : 0 ≤ M)
    (v : H10 n Ω) {s : ℕ → H10 n Ω} {x : H10 n Ω} (hs : Tendsto s atTop (𝓝 x)) :
    Tendsto (fun k => form P t (s k) v) atTop (𝓝 (form P t x v)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun k => ‖s k - x‖ * (formK n Ω M * ‖v‖)) atTop
      (𝓝 (0 * (formK n Ω M * ‖v‖))) := (tendsto_iff_norm_sub_tendsto_zero.1 hs).mul_const _
  rw [zero_mul] at h0
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h0
  rw [Real.norm_eq_abs, ← form_sub_left' hg]
  calc |form P t (s k - x) v| ≤ formK n Ω M * ‖s k - x‖ * ‖v‖ := form_le hg hM _ _
    _ = ‖s k - x‖ * (formK n Ω M * ‖v‖) := by ring

lemma form_simple_meas {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T)
    (s : SimpleFunc ℝ (H10 n Ω)) (v : H10 n Ω) :
    AEStronglyMeasurable (fun t => form P t (s t) v) (timeMeasure T) := by
  have : (fun t => form P t (s t) v) =
      fun t => ∑ c ∈ s.range, (s ⁻¹' {c}).indicator (fun t => form P t c v) t := by
    funext t
    rw [Finset.sum_eq_single (s t)]
    · exact (Set.indicator_of_mem (Set.mem_preimage.2 (Set.mem_singleton (s t)))
        (fun t => form P t (s t) v)).symm
    · intro c _ hc
      exact Set.indicator_of_notMem
        (fun h => hc (Set.mem_singleton_iff.1 (Set.mem_preimage.1 h)).symm) (fun t => form P t c v)
    · intro h; exact absurd (s.mem_range_self t) h
  rw [this]
  refine Finset.aestronglyMeasurable_fun_sum _ fun c _ => ?_
  exact (form_aesm hP c v).indicator (s.measurableSet_fiber c)

lemma form_meas {T : ℝ} {P : Coeffs n} (hP : P.Assumption61 Ω T) {x : ℝ → H10 n Ω}
    (hx : AEStronglyMeasurable x (timeMeasure T)) (v : H10 n Ω) :
    AEStronglyMeasurable (fun t => form P t (x t) v) (timeMeasure T) := by
  have hob18 := good_ae hP
  obtain ⟨θ, M, hθ, hM, hgood⟩ := hob18
  obtain ⟨s, hs⟩ := hx.stronglyMeasurable_mk
  refine AEStronglyMeasurable.congr ?_
    (?_ : (fun t => form P t (hx.mk x t) v) =ᵐ[timeMeasure T] fun t => form P t (x t) v)
  · refine aestronglyMeasurable_of_tendsto_ae atTop (fun k => form_simple_meas hP (s k) v) ?_
    filter_upwards [hgood] with t hg
    exact form_tendsto_left hg hM v (hs t)
  · filter_upwards [hx.ae_eq_mk] with t ht
    rw [← ht]

section lam
variable {T : ℝ} {P : Coeffs n} {θ M : ℝ}

lemma lam_integrable (hP : P.Assumption61 Ω T) (hM : 0 ≤ M)
    (hgood : ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) (v : H10 n Ω)
    {f : ℝ → H10 n Ω} (hf : MemLp f 2 (timeMeasure T)) :
    Integrable (fun t => ψ t * form P t (f t) v) (timeMeasure T) := by
  have hint : Integrable (fun t => ‖f t‖) (timeMeasure T) := hf.norm.integrable (by norm_num)
  refine Integrable.mono' (hint.const_mul (B * (formK n Ω M * ‖v‖))) ?_ ?_
  · exact hψm.aestronglyMeasurable.mul (form_meas hP hf.1 v)
  · filter_upwards [hgood, ae_restrict_mem measurableSet_Ioo] with t hg ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |ψ t| * |form P t (f t) v| ≤ B * (formK n Ω M * ‖f t‖ * ‖v‖) :=
          mul_le_mul (hψb t ht) (form_le hg hM _ _) (abs_nonneg _) hB
      _ = B * (formK n Ω M * ‖v‖) * ‖f t‖ := by ring

noncomputable def lamLin (hP : P.Assumption61 Ω T) (hM : 0 ≤ M)
    (hgood : ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) (v : H10 n Ω) :
    Lp (H10 n Ω) 2 (timeMeasure T) →ₗ[ℝ] ℝ where
  toFun x := ∫ t, ψ t * form P t (x t) v ∂(timeMeasure T)
  map_add' x y := by
    have hx := lam_integrable hP hM hgood hψm hB hψb v (Lp.memLp x)
    have hy := lam_integrable hP hM hgood hψm hB hψb v (Lp.memLp y)
    rw [← integral_add hx hy]
    refine integral_congr_ae ?_
    filter_upwards [hgood, Lp.coeFn_add x y] with t hg h
    rw [h, Pi.add_apply, form_add_left hg]; ring
  map_smul' c x := by
    show (∫ t, ψ t * form P t ((c • x : Lp (H10 n Ω) 2 (timeMeasure T)) t) v ∂(timeMeasure T)) =
      c * ∫ t, ψ t * form P t (x t) v ∂(timeMeasure T)
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hgood, Lp.coeFn_smul c x] with t hg h
    rw [h, Pi.smul_apply, form_smul_left hg]; ring

lemma lamLin_bound [IsFiniteMeasure (timeMeasure T)] (hP : P.Assumption61 Ω T) (hM : 0 ≤ M)
    (hgood : ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) (v : H10 n Ω)
    (x : Lp (H10 n Ω) 2 (timeMeasure T)) :
    ‖lamLin hP hM hgood hψm hB hψb v x‖ ≤
      (B * formK n Ω M * ‖v‖ * (eLpNorm (fun _ : ℝ => (1:ℝ)) 2 (timeMeasure T)).toReal) * ‖x‖ := by
  have hx2 := Lp.memLp x
  have hnorm : MemLp (fun t => ‖x t‖) 2 (timeMeasure T) := hx2.norm
  have hone : MemLp (fun _ : ℝ => (1:ℝ)) 2 (timeMeasure T) := memLp_const 1
  have hint : Integrable (fun t => |1 * ‖x t‖|) (timeMeasure T) := by
    simp only [one_mul, abs_norm]; exact hnorm.integrable (by norm_num)
  have h1 := norm_integral_le_of_norm_le
    (hint.const_mul (B * formK n Ω M * ‖v‖))
    (μ := timeMeasure T) (f := fun t => ψ t * form P t (x t) v) (by
      filter_upwards [hgood, ae_restrict_mem measurableSet_Ioo] with t hg ht
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |ψ t| * |form P t (x t) v| ≤ B * (formK n Ω M * ‖x t‖ * ‖v‖) :=
            mul_le_mul (hψb t ht) (form_le hg hM _ _) (abs_nonneg _) hB
        _ = B * formK n Ω M * ‖v‖ * |1 * ‖x t‖| := by
            simp only [one_mul, abs_norm]; ring)
  rw [integral_const_mul] at h1
  have h2 := integral_abs_mul_le hone hnorm
  rw [eLpNorm_norm] at h2
  have h3 : (eLpNorm (⇑x) 2 (timeMeasure T)).toReal = ‖x‖ := by rw [Lp.norm_def]
  rw [h3] at h2
  have hBK : 0 ≤ B * formK n Ω M * ‖v‖ := by
    have hB0 : 0 ≤ B := hB
    have : 0 ≤ formK n Ω M := by
      unfold formK
      refine mul_nonneg hM ?_
      positivity
    positivity
  calc ‖lamLin hP hM hgood hψm hB hψb v x‖ ≤ _ := h1
    _ ≤ (B * formK n Ω M * ‖v‖) * ((eLpNorm (fun _ : ℝ => (1:ℝ)) 2 (timeMeasure T)).toReal * ‖x‖) :=
        mul_le_mul_of_nonneg_left h2 hBK
    _ = _ := by ring

noncomputable def lamCLM [IsFiniteMeasure (timeMeasure T)] (hP : P.Assumption61 Ω T) (hM : 0 ≤ M)
    (hgood : ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) (v : H10 n Ω) :
    Lp (H10 n Ω) 2 (timeMeasure T) →L[ℝ] ℝ :=
  LinearMap.mkContinuous (E := Lp (H10 n Ω) 2 (timeMeasure T)) (F := ℝ)
    (lamLin hP hM hgood hψm hB hψb v) _ (lamLin_bound hP hM hgood hψm hB hψb v)

lemma lamCLM_apply [IsFiniteMeasure (timeMeasure T)] (hP : P.Assumption61 Ω T) (hM : 0 ≤ M)
    (hgood : ∀ᵐ t ∂(timeMeasure T), GoodT P Ω θ M t)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) (v : H10 n Ω)
    (x : Lp (H10 n Ω) 2 (timeMeasure T)) :
    lamCLM hP hM hgood hψm hB hψb v x = ∫ t, ψ t * form P t (x t) v ∂(timeMeasure T) := rfl

theorem form_weak_conv [IsFiniteMeasure (timeMeasure T)] [TopologicalSpace.SeparableSpace (H10 n Ω)]
    (hP : P.Assumption61 Ω T)
    {ψ : ℝ → ℝ} (hψm : Measurable ψ) {B : ℝ} (hB : 0 ≤ B) (hψb : ∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) (v : H10 n Ω)
    {x : ℕ → ℝ → H10 n Ω} {y : ℝ → H10 n Ω}
    (hx : ∀ k, MemLp (x k) 2 (timeMeasure T)) (hy : MemLp y 2 (timeMeasure T))
    (hconv : ∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
      Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
        (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂(timeMeasure T)))) :
    Tendsto (fun k => ∫ t in Set.Ioo 0 T, ψ t * form P t (x k t) v) atTop
      (𝓝 (∫ t in Set.Ioo 0 T, ψ t * form P t (y t) v)) := by
  have hob19 := good_ae hP
  obtain ⟨θ, M, hθ, hM, hgood⟩ := hob19
  have h := weak_clm hx hy hconv (lamCLM hP hM hgood hψm hB hψb v)
  have e : ∀ {g : ℝ → H10 n Ω} (hg : MemLp g 2 (timeMeasure T)),
      lamCLM hP hM hgood hψm hB hψb v (hg.toLp g) = ∫ t in Set.Ioo 0 T, ψ t * form P t (g t) v := by
    intro g hg
    rw [lamCLM_apply]
    refine integral_congr_ae ?_
    filter_upwards [hg.coeFn_toLp] with t ht
    rw [ht]
  simpa only [e] using h

end lam

end F
end HunterPDE.Parabolic
end Q0ffd_F

section Q0ffd_D
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section D
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

end D
end HunterPDE.Parabolic
end Q0ffd_D

section Q0ffd_D2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section D2
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

end D2
end HunterPDE.Parabolic
end Q0ffd_D2

section Q0ffd_P1
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section limit
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end limit
end HunterPDE.Parabolic
end Q0ffd_P1

section Q0ffd_P2
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section eqn
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end eqn
end HunterPDE.Parabolic
end Q0ffd_P2

section Q0ffd_P3
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section ibp
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end ibp
end HunterPDE.Parabolic
end Q0ffd_P3

section Q0ffd_P4
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section init
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ}

end init
end HunterPDE.Parabolic
end Q0ffd_P4

section Q0ffd_P5
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast

section est

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] {T : ℝ}

end est
end HunterPDE.Parabolic
end Q0ffd_P5

section Q0ffd_A
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal ContDiff
namespace HunterPDE.Parabolic
open scoped HunterPDE.Parabolic.Q0ffdFast
section asm

end asm
end HunterPDE.Parabolic
end Q0ffd_A


open MeasureTheory Filter Topology HunterPDE.Parabolic in
theorem solution {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ} {P : Coeffs n}
    (hP : P.Assumption61 Ω T) :
    (∀ᵐ t ∂(timeMeasure T), ∀ w : H10 n Ω, Continuous (fun v : H10 n Ω => form P t w v)) ∧
    (∀ {ψ : ℝ → ℝ}, Measurable ψ → ∀ {B : ℝ}, 0 ≤ B → (∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) →
      ∀ (v : H10 n Ω) {f : ℝ → H10 n Ω}, MemLp f 2 (timeMeasure T) →
        Integrable (fun t => ψ t * form P t (f t) v) (timeMeasure T)) ∧
    (∀ {ψ : ℝ → ℝ}, Measurable ψ → ∀ {B : ℝ}, 0 ≤ B → (∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) →
      ∀ (v : H10 n Ω) {x : ℕ → ℝ → H10 n Ω} {y : ℝ → H10 n Ω},
        (∀ k, MemLp (x k) 2 (timeMeasure T)) → MemLp y 2 (timeMeasure T) →
        (∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
          Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
            (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂(timeMeasure T)))) →
        Tendsto (fun k => ∫ t in Set.Ioo 0 T, ψ t * form P t (x k t) v) atTop
          (𝓝 (∫ t in Set.Ioo 0 T, ψ t * form P t (y t) v))) := by
  haveI : IsFiniteMeasure (timeMeasure T) := isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  haveI : TopologicalSpace.SeparableSpace (H10 n Ω) := separable_H10
  have hob := good_ae hP
  obtain ⟨θ, M, hθ, hM, hgood⟩ := hob
  refine ⟨?_, @fun ψ hψm B hB hψb v f hf => lam_integrable hP hM hgood hψm hB hψb v hf,
    @fun ψ hψm B hB hψb v x y hx hy hc => form_weak_conv hP hψm hB hψb v hx hy hc⟩
  filter_upwards [hgood] with t hg w
  exact (formCLM hg hM w).continuous
