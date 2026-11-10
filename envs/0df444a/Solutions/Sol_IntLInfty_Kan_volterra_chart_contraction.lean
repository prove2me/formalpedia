-- Prove2me | solution 1 for IntLInfty.Kan.volterra_chart_contraction
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:08:40.104083+00:00
-- url     : https://prove2.me/submissions/45adc242-7eff-4cba-96cf-a7c1a416927c

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_crForms_eq_jet_image
import Theorems.Thm_IntLInfty_Kan_crForms_exterior_calculus
import Theorems.Thm_IntLInfty_Kan_generator_lift_dga
import Theorems.Thm_IntLInfty_Kan_wedge_continuous_bilinear
import Theorems.Thm_IntLInfty_Kan_integ_iff_generator_condition
import Theorems.Thm_IntLInfty_Kan_cone_homotopy_operator

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace IntLInfty.Kan.A83
open IntLInfty.Kan

def FormEqOn {m : ℕ} (ω ω' : Ω m) : Prop := ∀ x ∈ simplex m, ω x = ω' x

theorem crForms_eq_image {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (CrForms r m n : Set (Jet r m × Jet r m)) = jet r '' {ω : Ω m | IsDeg n ω ∧ IsCr r ω} :=
  (IntLInfty.Kan.crForms_eq_jet_image hr n).1

theorem convex_simplex :
    ∀ (m : ℕ), Convex ℝ (simplex m) :=
  IntLInfty.Kan.crForms_exterior_calculus.1

theorem uniqueDiffOn_simplex :
    ∀ (m : ℕ), UniqueDiffOn ℝ (simplex m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.1

theorem isCr_smul :
    ∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω), IsCr r (c • ω) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.1

theorem jet_add :
    ∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'),
      jet r (ω + ω') = jet r ω + jet r ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.1

theorem jet_smul :
    ∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω),
      jet r (c • ω) = c • jet r ω :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.1

theorem isCr_zero :
    ∀ {m r : ℕ}, IsCr r (0 : Ω m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem isDeg_zero :
    ∀ {m : ℕ} {n : ℕ}, IsDeg n (0 : Ω m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem isClosed_simplex :
    ∀ (m : ℕ), IsClosed (simplex m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem jetComp_apply :
    ∀ {m r : ℕ} {f : (Fin m → ℝ) → ℝ} (hf : ContDiffOn ℝ r f (simplex m)) {k : ℕ}
      (hk : k ≤ r) (β : Fin k → Fin m) {x : Fin m → ℝ} (hx : x ∈ simplex m),
      jetComp f k β ⟨x, hx⟩ = iteratedFDerivWithin ℝ k f (simplex m) x (fun l => Pi.single (β l) 1) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem coeff_eqOn :
    ∀ {m : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω') (I : Finset (Fin m)),
      Set.EqOn (coeff ω I) (coeff ω' I) (simplex m) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem extD_congr :
    ∀ {m : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω'), FormEqOn (extD ω) (extD ω') :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem jet_congr :
    ∀ {m r : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω'), jet r ω = jet r ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_rep {m r : ℕ} (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ϖ : Ω m, (IsDeg n ϖ ∧ IsCr r ϖ) ∧ jet r ϖ = w := by
  have h : (w : Jet r m × Jet r m) ∈ (CrForms r m n : Set (Jet r m × Jet r m)) := w.2
  rw [crForms_eq_image hr n] at h
  obtain ⟨ϖ, hϖ, e⟩ := h
  exact ⟨ϖ, hϖ, e⟩

end IntLInfty.Kan.A83

namespace IntLInfty.Kan.A83Cone

open Set Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : ℕ) (f : E → F)
    (x : E) : F :=
  ∫ t in (0 : ℝ)..1, (t ^ p) • f (t • x)

theorem norm_pow_le_one {p : ℕ} {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) 1) : ‖t ^ p‖ ≤ 1 := by
  rw [Set.uIoc_of_le zero_le_one] at ht
  rw [norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
  exact pow_le_one₀ ht.1.le ht.2

theorem mem_Icc_of_uIoc {t : ℝ} (ht : t ∈ Set.uIoc (0 : ℝ) 1) : t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.uIoc_of_le zero_le_one] at ht
  exact ⟨ht.1.le, ht.2⟩

variable {S : Set E}

theorem intervalIntegrable_cone {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} (hf : ContinuousOn f S) (p : ℕ)
    {x : E} (hx : x ∈ S) :
    IntervalIntegrable (fun t : ℝ => (t ^ p) • f (t • x)) MeasureTheory.volume 0 1 := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le zero_le_one]
  refine ContinuousOn.smul (continuousOn_pow p) (hf.comp ?_ ?_)
  · exact (continuous_id.smul continuous_const).continuousOn
  · intro t ht
    exact hconv.smul_mem_of_zero_mem h0 hx ht

theorem uc_ray {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (hS : IsCompact S)
    (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} (hf : ContinuousOn f S) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, ‖y - x‖ < δ → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ‖f (t • y) - f (t • x)‖ < ε := by
  have hu := hS.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy t ht => ?_⟩
  have htx := hconv.smul_mem_of_zero_mem h0 hx ht
  have hty := hconv.smul_mem_of_zero_mem h0 hy ht
  have hd : dist (t • y) (t • x) < δ := by
    rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact ht.2
      _ = ‖y - x‖ := one_mul _
      _ < δ := hxy
  have := h _ hty _ htx hd
  rwa [dist_eq_norm] at this

theorem continuousOn_coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F}
    (hf : ContinuousOn f S) (p : ℕ) : ContinuousOn (coneInt p f) S := by
  rw [Metric.continuousOn_iff]
  intro x hx ε hε
  obtain ⟨δ, hδ, h⟩ := uc_ray hS hconv h0 hf (half_pos hε)
  refine ⟨δ, hδ, fun y hy hyx => ?_⟩
  rw [dist_eq_norm] at hyx ⊢
  simp only [coneInt]
  rw [← intervalIntegral.integral_sub (intervalIntegrable_cone hconv h0 hf p hy)
    (intervalIntegrable_cone hconv h0 hf p hx)]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(t ^ p) • f (t • y) - (t ^ p) • f (t • x)‖ ≤ ε / 2 := by
    intro t ht
    rw [← smul_sub, norm_smul]
    calc ‖t ^ p‖ * ‖f (t • y) - f (t • x)‖ ≤ 1 * (ε / 2) := by
          gcongr
          · exact norm_pow_le_one ht
          · exact (h x hx y hy hyx t (mem_Icc_of_uIoc ht)).le
      _ = ε / 2 := one_mul _
  calc _ ≤ ε / 2 * |(1 : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ < ε := by simp; linarith

theorem hasFDerivWithinAt_coneInt {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F}
    {f' : E → E →L[ℝ] F} (hf : ∀ x ∈ S, HasFDerivWithinAt f (f' x) S x)
    (hf' : ContinuousOn f' S) (p : ℕ) {x : E} (hx : x ∈ S) :
    HasFDerivWithinAt (coneInt p f) (coneInt (p + 1) f' x) S x := by
  have hfc : ContinuousOn f S := fun y hy => (hf y hy).continuousWithinAt
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have hu := hS.uniformContinuousOn_of_continuous hf'
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, h⟩ := hu c hc
  have hball : ∀ᶠ y in 𝓝[S] x, y ∈ S ∧ ‖y - x‖ < δ := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds x hδ)]
      with y hy hb
    exact ⟨hy, by rwa [Metric.mem_ball, dist_eq_norm] at hb⟩
  filter_upwards [hball] with y hyy
  obtain ⟨hy, hyx⟩ := hyy
  have hI1 := intervalIntegrable_cone hconv h0 hfc p hy
  have hI2 := intervalIntegrable_cone hconv h0 hfc p hx
  have hI3 := intervalIntegrable_cone hconv h0 hf' (p + 1) hx
  have hray : ContinuousOn (fun t : ℝ => f' (t • x)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le zero_le_one]
    refine hf'.comp (continuous_id.smul continuous_const).continuousOn ?_
    intro t ht
    exact hconv.smul_mem_of_zero_mem h0 hx ht
  have hI4 : IntervalIntegrable (fun t : ℝ => (t ^ p) • (f' (t • x)) (t • y - t • x))
      MeasureTheory.volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.smul (continuousOn_pow p) (hray.clm_apply ?_)
    exact ((continuous_id.smul continuous_const).sub
      (continuous_id.smul continuous_const)).continuousOn
  have happ : (coneInt (p + 1) f' x) (y - x) =
      ∫ t in (0 : ℝ)..1, (t ^ p) • (f' (t • x)) (t • y - t • x) := by
    simp only [coneInt]
    rw [ContinuousLinearMap.intervalIntegral_apply hI3]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [FunLike.coe_smul, Pi.smul_apply, ← smul_sub, map_smul, smul_smul, pow_succ]
  have hsplit : coneInt p f y - coneInt p f x - (coneInt (p + 1) f' x) (y - x) =
      ∫ t in (0 : ℝ)..1, (t ^ p) • (f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x)) := by
    rw [happ]
    simp only [coneInt]
    rw [← intervalIntegral.integral_sub hI1 hI2, ← intervalIntegral.integral_sub (hI1.sub hI2) hI4]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [smul_sub]
  rw [hsplit]
  have hb : ∀ t ∈ Set.uIoc (0 : ℝ) 1,
      ‖(t ^ p) • (f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x))‖ ≤ c * ‖y - x‖ := by
    intro t ht
    have ht' := mem_Icc_of_uIoc ht
    have htx := hconv.smul_mem_of_zero_mem h0 hx ht'
    have hty := hconv.smul_mem_of_zero_mem h0 hy ht'
    have hseg : segment ℝ (t • x) (t • y) ⊆ S := hconv.segment_subset htx hty
    have hle : ‖t • y - t • x‖ ≤ ‖y - x‖ := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1]
      calc t * ‖y - x‖ ≤ 1 * ‖y - x‖ := by gcongr; exact ht'.2
        _ = ‖y - x‖ := one_mul _
    have hmv : ‖f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x)‖ ≤ c * ‖t • y - t • x‖ := by
      refine Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
        (fun z hz => (hf z (hseg hz)).mono hseg) (fun z hz => ?_) (convex_segment _ _)
        (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
      have hzb : z ∈ Metric.closedBall (t • x) ‖t • y - t • x‖ :=
        (convex_closedBall _ _).segment_subset (Metric.mem_closedBall_self (norm_nonneg _))
          (by rw [Metric.mem_closedBall, dist_eq_norm]) hz
      rw [Metric.mem_closedBall] at hzb
      have := h z (hseg hz) (t • x) htx (lt_of_le_of_lt (hzb.trans hle) hyx)
      rw [dist_eq_norm] at this
      exact this.le
    rw [norm_smul]
    calc ‖t ^ p‖ * ‖f (t • y) - f (t • x) - (f' (t • x)) (t • y - t • x)‖
        ≤ 1 * (c * ‖y - x‖) := by
          gcongr
          · exact norm_pow_le_one ht
          · exact hmv.trans (by gcongr)
      _ = c * ‖y - x‖ := one_mul _
  calc _ ≤ c * ‖y - x‖ * |(1 : ℝ) - 0| := intervalIntegral.norm_integral_le_of_norm_le_const hb
    _ = c * ‖y - x‖ := by simp

theorem contDiffOn_coneInt (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hU : UniqueDiffOn ℝ S) (r : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F)
      (p : ℕ), ContDiffOn ℝ r f S → ContDiffOn ℝ r (coneInt p f) S := by
  induction r with
  | zero =>
    intro F _ _ _ f p hf
    rw [Nat.cast_zero, contDiffOn_zero] at hf ⊢
    exact continuousOn_coneInt hS hconv h0 hf p
  | succ r ih =>
    intro F _ _ _ f p hf
    have hd : ∀ x ∈ S, HasFDerivWithinAt f (fderivWithin ℝ f S x) S x := fun x hx =>
      ((hf.differentiableOn (by simp)) x hx).hasFDerivWithinAt
    have hc : ContinuousOn (fderivWithin ℝ f S) S := hf.continuousOn_fderivWithin hU (by simp)
    have hD := fun (x : E) (hx : x ∈ S) => hasFDerivWithinAt_coneInt hS hconv h0 hd hc p hx
    have hfd : ContDiffOn ℝ r (fderivWithin ℝ f S) S := hf.fderivWithin hU (by push_cast; rfl)
    rw [show ((r + 1 : ℕ) : WithTop ℕ∞) = (r : WithTop ℕ∞) + 1 by push_cast; rfl,
      contDiffOn_succ_iff_fderivWithin hU]
    refine ⟨fun x hx => (hD x hx).differentiableWithinAt, by simp, ?_⟩
    exact (ih (fderivWithin ℝ f S) (p + 1) hfd).congr fun x hx => (hD x hx).fderivWithin (hU x hx)

end IntLInfty.Kan.A83Cone

namespace IntLInfty.Kan.A83Poinc

open IntLInfty.Kan IntLInfty.Kan.A83Cone

abbrev Alg (m : ℕ) : Type := ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ))

@[reducible] noncomputable def algNAG (m : ℕ) : NormedAddCommGroup (Alg m) :=
  NormedAddCommGroup.induced (Alg m) (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap
    (formBasis m).equivFun.injective

attribute [local instance] algNAG

@[reducible] noncomputable def algNS (m : ℕ) : NormedSpace ℝ (Alg m) :=
  NormedSpace.induced ℝ (Alg m) (Finset (Fin m) → ℝ) (formBasis m).equivFun.toLinearMap

attribute [local instance] algNS

theorem algFD (m : ℕ) : FiniteDimensional ℝ (Alg m) := Module.Finite.of_basis (formBasis m)

attribute [local instance] algFD

theorem algComplete (m : ℕ) : CompleteSpace (Alg m) := FiniteDimensional.complete ℝ (Alg m)

attribute [local instance] algComplete

noncomputable def cL (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] Alg m →ₗ[ℝ] Alg m :=
  (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))).comp
    (Module.Dual.eval ℝ (Fin m → ℝ))

noncomputable def cB (m : ℕ) : (Fin m → ℝ) →L[ℝ] Alg m →L[ℝ] Alg m :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Alg m →ₗ[ℝ] Alg m) ≃ₗ[ℝ] (Alg m →L[ℝ] Alg m)).toLinearMap
      ∘ₗ cL m)

section generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

end generic

theorem isCompact_simplex (m : ℕ) : IsCompact (simplex m) :=
  Metric.isCompact_of_isClosed_isBounded (A83.isClosed_simplex m)
    ((Metric.isBounded_Icc (0 : Fin m → ℝ) 1).subset fun x hx =>
      ⟨fun i => hx.1 i, fun i =>
        (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2⟩)

theorem zero_mem_simplex (m : ℕ) : (0 : Fin m → ℝ) ∈ simplex m :=
  ⟨fun _ => le_refl 0, by simp⟩

noncomputable def coeffL (m : ℕ) (I : Finset (Fin m)) : Alg m →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.proj I).comp (formBasis m).equivFun.toLinearMap)

theorem coeffL_apply (m : ℕ) (I : Finset (Fin m)) (a : Alg m) :
    coeffL m I a = (formBasis m).repr a I := by
  simp [coeffL]

theorem coeff_eq_coeffL {m : ℕ} (ω : Ω m) (I : Finset (Fin m)) :
    coeff ω I = fun y => coeffL m I (ω y) := by
  funext y
  rw [coeffL_apply]
  rfl

theorem contDiffOn_of_coeff {m r : ℕ} {ω : Ω m} {S : Set (Fin m → ℝ)}
    (h : ∀ I, ContDiffOn ℝ r (coeff ω I) S) : ContDiffOn ℝ r ω S := by
  have e : ω = fun y => (formBasis m).equivFun.symm (fun I => coeff ω I y) := by
    funext y
    apply (formBasis m).equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    funext I
    simp [coeff]
  rw [e]
  exact (LinearMap.toContinuousLinearMap (formBasis m).equivFun.symm.toLinearMap).contDiff.comp_contDiffOn
    (contDiffOn_pi.mpr h)

noncomputable def Kop {m : ℕ} (n : ℕ) (β : Ω m) : Ω m := fun y => cB m y (coneInt n β y)

theorem C1 (r : ℕ) (hr : 1 ≤ r) :
    type_of% (IntLInfty.Kan.cone_homotopy_operator r hr (fun _ n β => Kop n β) (fun _ _ _ _ => rfl)) :=
  IntLInfty.Kan.cone_homotopy_operator r hr (fun _ n β => Kop n β) (fun _ _ _ _ => rfl)

theorem Kop_hom {m n r : ℕ} (hr : 1 ≤ r) {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    ∀ x ∈ simplex m, extD (Kop n β) x + Kop (n + 1) (extD β) x = β x := ((IntLInfty.Kan.A83Poinc.C1 r hr).1 m n β hC hD).2.2

theorem isDeg_extD {m n r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω) (hD : IsDeg n ω) :
    IsDeg (n + 1) (extD ω) := (IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.1 m n ω hC hD

theorem isCr_extD {m r : ℕ} (hr : 1 ≤ r) {ω : Ω m} (hC : IsCr r ω) : IsCr r (extD ω) := (IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.1 m ω hC

end IntLInfty.Kan.A83Poinc

namespace IntLInfty.Kan.A83Fill

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

variable {m r : ℕ}

end IntLInfty.Kan.A83Fill

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83Graph

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83Proj

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem norm_alg_le {a : Alg m} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ I, |(formBasis m).repr a I| ≤ C) : ‖a‖ ≤ C := by
  show ‖(formBasis m).equivFun a‖ ≤ C
  refine (pi_norm_le_iff_of_nonneg hC).2 fun I => ?_
  simpa [Real.norm_eq_abs] using h I

theorem jet_zero' (hr : 1 ≤ r) : jet r (0 : Ω m) = 0 := by
  have := jet_smul hr (0 : ℝ) (isCr_zero (r := r) (m := m))
  simpa using this

end IntLInfty.Kan.A83Proj

namespace IntLInfty.Kan.A83Leib

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

attribute [local instance] algNAG algNS algFD algComplete

variable {m : ℕ}

noncomputable def mulB (m : ℕ) : Alg m →L[ℝ] Alg m →L[ℝ] Alg m :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (Alg m →ₗ[ℝ] Alg m) ≃ₗ[ℝ] (Alg m →L[ℝ] Alg m)).toLinearMap ∘ₗ
      LinearMap.mul ℝ (Alg m))

theorem mulB_apply (m : ℕ) (a b : Alg m) : mulB m a b = a * b := by
  simp [mulB]

theorem mul_eq_mulB (γ η : Ω m) : γ * η = fun y => mulB m (γ y) (η y) := by
  funext y
  simp [mulB_apply]

theorem extD_mul {r p : ℕ} (hr : 1 ≤ r) {α β : Ω m} (hα : IsCr r α) (hβ : IsCr r β)
    (hD : IsDeg p α) {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    extD (α * β) x = extD α x * β x + (-1 : ℝ) ^ p • (α x * extD β x) :=
  IntLInfty.Kan.generator_lift_dga.2.2.2.1 hr hα hβ hD x hx

theorem isCr_mul {r p : ℕ} (hr : 1 ≤ r) {α β : Ω m} (hα : IsCr r α) (hβ : IsCr r β)
    (hD : IsDeg p α) : IsCr r (α * β) :=
  IntLInfty.Kan.generator_lift_dga.2.2.2.2.1 hr hα hβ hD

end IntLInfty.Kan.A83Leib

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan

section Ext

variable {V : Type} [AddCommGroup V] [Module ℝ V]

end Ext

section Lift

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

def GenHom (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) : Prop :=
  ∀ i ξ x, f i ξ x ∈ ⋀[ℝ]^(i + 1) (Module.Dual ℝ (Fin m → ℝ))

noncomputable def ceLift (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) :
    CE L →ₐ[ℝ] Ω m :=
  (IntLInfty.Kan.generator_lift_dga.1 f hf).choose

theorem ceLift_gen (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : ceLift f hf (gen L i ξ) = f i ξ :=
  (IntLInfty.Kan.generator_lift_dga.1 f hf).choose_spec i ξ

end Lift

end IntLInfty.Kan.A83DGA

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83Proj

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem gen_mem_ceDeg (i : ℕ) (ξ : Module.Dual ℝ (L i)) : gen L i ξ ∈ ceDeg L (i + 1) :=
  Submodule.subset_span ⟨1, fun _ => i, fun _ => ξ, by simp, by simp⟩

end IntLInfty.Kan.A83DGA

namespace IntLInfty.Kan.A83DGA

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

open Classical in
noncomputable def cutL : Ω m →ₗ[ℝ] Ω m where
  toFun ω x := if x ∈ simplex m then ω x else 0
  map_add' ω ω' := by funext x; by_cases hx : x ∈ simplex m <;> simp [hx]
  map_smul' c ω := by funext x; by_cases hx : x ∈ simplex m <;> simp [hx]

theorem cutL_eqOn (ω : Ω m) : FormEqOn (cutL ω) ω := fun x hx => by simp [cutL, hx]

theorem isCr_of_formEqOn {r : ℕ} {ω ω' : Ω m} (h : FormEqOn ω ω') (hC : IsCr r ω) :
    IsCr r ω' := fun I =>
  ⟨(hC I).1.congr (fun x hx => (coeff_eqOn h I hx).symm),
    (hC I).2.congr (fun x hx => (coeff_eqOn (extD_congr h) I hx).symm)⟩

theorem genHom_cut (g : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m)
    (hg : ∀ i (ξ : Module.Dual ℝ (L i)), IsDeg (i + 1) (g i ξ)) :
    GenHom (fun i => cutL ∘ₗ g i) := fun i ξ x => by
  by_cases hx : x ∈ simplex m
  · simp only [cutL, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]
    exact hg i ξ x hx
  · simp only [cutL, LinearMap.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, hx, ↓reduceIte]
    exact Submodule.zero_mem _

end IntLInfty.Kan.A83DGA

namespace IntLInfty.Kan.A83Wedge

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib Filter Topology
open scoped ContDiff

variable {m r : ℕ}

noncomputable def wRep (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) : Ω m :=
  (exists_rep hr w).choose

theorem wRep_spec (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    (IsDeg n (wRep hr w) ∧ IsCr r (wRep hr w)) ∧ jet r (wRep hr w) = w :=
  (exists_rep hr w).choose_spec

noncomputable def wedgeCLM (hr : 1 ≤ r) (p q : ℕ) :
    CrForms r m p →L[ℝ] CrForms r m q →L[ℝ] CrForms r m (p + q) :=
  (IntLInfty.Kan.wedge_continuous_bilinear.1 hr).choose p q

theorem wedgeCLM_val (hr : 1 ≤ r) {p q : ℕ} {w1 : CrForms r m p} {w2 : CrForms r m q}
    {α β : Ω m} (hα : IsDeg p α ∧ IsCr r α) (hβ : IsDeg q β ∧ IsCr r β)
    (h1 : jet r α = w1) (h2 : jet r β = w2) :
    (wedgeCLM hr p q w1 w2 : Jet r m × Jet r m) = jet r (α * β) :=
  (IntLInfty.Kan.wedge_continuous_bilinear.1 hr).choose_spec.1 p q w1 w2 α β hα hβ h1 h2

end IntLInfty.Kan.A83Wedge

namespace IntLInfty.Kan.A83Gron

open intervalIntegral

end IntLInfty.Kan.A83Gron

namespace IntLInfty.Kan.A83Ev

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj
open scoped ContDiff

section Fam

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jet_mem (hr : 1 ≤ r) {n : ℕ} {w0 : Ω m} (h : IsDeg n w0 ∧ IsCr r w0) :
    jet r w0 ∈ CrForms r m n := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.1 <;> assumption)

def SmoothFam (r n : ℕ) (F : E → Ω m) : Prop :=
  ∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧
    ∀ z, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = a z

theorem smoothFam_zero (hr : 1 ≤ r) (n : ℕ) : SmoothFam (m := m) r n (fun _ : E => 0) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.1 <;> assumption)

theorem smoothFam_add (hr : 1 ≤ r) {n : ℕ} {F G : E → Ω m} (hF : SmoothFam r n F)
    (hG : SmoothFam r n G) : SmoothFam r n (fun z => F z + G z) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.1 <;> assumption)

theorem smoothFam_smul (hr : 1 ≤ r) {n : ℕ} (c : ℝ) {F : E → Ω m} (hF : SmoothFam r n F) :
    SmoothFam r n (fun z => c • F z) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.1 <;> assumption)

theorem smoothFam_sum (hr : 1 ≤ r) {n : ℕ} {ι : Type} (s : Finset ι) {F : ι → E → Ω m}
    (hF : ∀ i ∈ s, SmoothFam r n (F i)) : SmoothFam r n (fun z => ∑ i ∈ s, F i z) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.1 <;> assumption)

theorem smoothFam_mul (hr : 1 ≤ r) {p q : ℕ} {F G : E → Ω m} (hF : SmoothFam r p F)
    (hG : SmoothFam r q G) : SmoothFam r (p + q) (fun z => F z * G z) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.1 <;> assumption)

theorem smoothFam_const (hr : 1 ≤ r) {n : ℕ} {w0 : Ω m} (h : IsDeg n w0 ∧ IsCr r w0) :
    SmoothFam r n (fun _ : E => w0) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.1 <;> assumption)

theorem smoothFam_congr {n : ℕ} {F G : E → Ω m} (hF : SmoothFam r n F)
    (h : ∀ z, FormEqOn (G z) (F z)) : SmoothFam r n G := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.1 <;> assumption)

theorem smoothFam_rep (hr : 1 ≤ r) {n : ℕ} {a : E → CrForms r m n} (ha : ContDiff ℝ ∞ a) :
    SmoothFam r n (fun z => wRep hr (a z)) :=
  ⟨a, ha, fun z => wRep_spec hr (a z)⟩

theorem isDeg_algebraMap (c : ℝ) : IsDeg 0 (algebraMap ℝ (Ω m) c) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.1 <;> assumption)

theorem isCr_algebraMap (c : ℝ) : IsCr r (algebraMap ℝ (Ω m) c) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.1 <;> assumption)

theorem graded_extract {ι : Type} [Fintype ι] (d : ι → ℕ) {n : ℕ}
    (y : ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
    (hy : y ∈ ⋀[ℝ]^n (Module.Dual ℝ (Fin m → ℝ)))
    (g : ι → ExteriorAlgebra ℝ (Module.Dual ℝ (Fin m → ℝ)))
    (hg : ∀ i, g i ∈ ⋀[ℝ]^(d i) (Module.Dual ℝ (Fin m → ℝ))) (hsum : y = ∑ i, g i) :
    y = ∑ i ∈ Finset.univ.filter (fun i => d i = n), g i := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.1 <;> assumption)

end Fam

section Lift

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem smoothFam_ceLift (hr : 1 ≤ r) (S : GenSys L)
    (f : E → ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : ∀ z, GenHom (f z))
    (hgen : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → SmoothFam r (i + 1) (fun z => f z i ξ))
    {n : ℕ} (x : CE L) (hx : x ∈ genAlg L S) (hd : ∀ z, IsDeg n (ceLift (f z) (hf z) x)) :
    SmoothFam r n (fun z => ceLift (f z) (hf z) x) :=
  IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 hr S f hf (fun z => ceLift (f z) (hf z))
    (fun z => ceLift_gen (f z) (hf z)) hgen x hx hd

end Lift

end IntLInfty.Kan.A83Ev

namespace IntLInfty.Kan.A83Ev

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj
open scoped ContDiff

section AmbVal

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

noncomputable def retr (S : GenSys L) (i : ℕ) : Module.Dual ℝ (L i) →ₗ[ℝ] S i :=
  (LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := S i) (V' := Module.Dual ℝ (L i))
    (S i).subtype (Submodule.ker_subtype _)).choose

theorem retr_spec (S : GenSys L) (i : ℕ) (ξ : S i) : retr S i (ξ : Module.Dual ℝ (L i)) = ξ :=
  LinearMap.congr_fun
    (LinearMap.exists_leftInverse_of_injective (K := ℝ) (V := S i) (V' := Module.Dual ℝ (L i))
      (S i).subtype (Submodule.ker_subtype _)).choose_spec ξ

noncomputable def rawVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ) :
    Module.Dual ℝ (L i) →ₗ[ℝ] Ω m :=
  if h : i < m then
    ∑ k : Fin (Module.finrank ℝ (S i)), LinearMap.smulRight
      ((Finsupp.lapply k).comp ((genBasis S i).repr.toLinearMap.comp (retr S i)))
      (wRep hr (z ⟨i, h⟩ k))
  else 0

theorem rawVal_lt (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) {i : ℕ} (h : i < m)
    (ξ : Module.Dual ℝ (L i)) :
    rawVal hr S z i ξ = ∑ k : Fin (Module.finrank ℝ (S i)),
      (genBasis S i).repr (retr S i ξ) k • wRep hr (z ⟨i, h⟩ k) := by
  simp only [rawVal, h, ↓reduceDIte, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
    LinearEquiv.coe_coe]

theorem rawVal_ge (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) {i : ℕ} (h : ¬ i < m)
    (ξ : Module.Dual ℝ (L i)) : rawVal hr S z i ξ = 0 := by
  simp only [rawVal, h, ↓reduceDIte, LinearMap.zero_apply]

theorem isDeg_rawVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : IsDeg (i + 1) (rawVal hr S z i ξ) := by
  by_cases h : i < m
  · rw [rawVal_lt hr S z h]
    intro x hx
    rw [Finset.sum_apply]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ ((wRep_spec hr _).1.1 x hx)
  · rw [rawVal_ge hr S z h]
    exact isDeg_zero

noncomputable def genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ) :
    Module.Dual ℝ (L i) →ₗ[ℝ] Ω m :=
  cutL ∘ₗ rawVal hr S z i

theorem genHom_genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) : GenHom (genVal hr S z) :=
  genHom_cut _ (isDeg_rawVal hr S z)

theorem contDiff_coord (S : GenSys L) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    ContDiff ℝ ∞ (fun z : Amb r S m => z t k) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.1 <;> assumption)

theorem smoothFam_genVal (hr : 1 ≤ r) (S : GenSys L) (i : ℕ) (ξ : Module.Dual ℝ (L i)) :
    SmoothFam r (i + 1) (fun z : Amb r S m => genVal hr S z i ξ) := by
  by_cases h : i < m
  · have hs : SmoothFam r (i + 1) (fun z : Amb r S m => ∑ k : Fin (Module.finrank ℝ (S i)),
        (genBasis S i).repr (retr S i ξ) k • wRep hr (z ⟨i, h⟩ k)) :=
      smoothFam_sum hr _ fun k _ => smoothFam_smul hr _
        (smoothFam_rep hr (contDiff_coord S ⟨i, h⟩ k))
    refine smoothFam_congr hs fun z x hx => ?_
    show cutL (rawVal hr S z i ξ) x = _
    rw [cutL_eqOn _ x hx, rawVal_lt hr S z h]
  · refine smoothFam_congr (smoothFam_zero hr (i + 1)) fun z x hx => ?_
    show cutL (rawVal hr S z i ξ) x = _
    rw [cutL_eqOn _ x hx, rawVal_ge hr S z h]

theorem jet_genVal_basis (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    jet r (genVal hr S z t (genBasis S t k)) = z t k := by
  have e : FormEqOn (genVal hr S z t (genBasis S t k)) (wRep hr (z t k)) := fun x hx => by
    show cutL (rawVal hr S z t (genBasis S t k)) x = _
    rw [cutL_eqOn _ x hx, rawVal_lt hr S z t.2, retr_spec, Module.Basis.repr_self]
    simp only [Finsupp.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, Fin.eta]
  rw [jet_congr e]
  exact (wRep_spec hr (z t k)).2

theorem smoothFam_eval (hr : 1 ≤ r) (S : GenSys L) {n : ℕ} (x : CE L) (hx : x ∈ genAlg L S)
    (hd : ∀ z : Amb r S m, IsDeg n (ceLift (genVal hr S z) (genHom_genVal hr S z) x)) :
    SmoothFam r n (fun z : Amb r S m => ceLift (genVal hr S z) (genHom_genVal hr S z) x) :=
  smoothFam_ceLift hr S (fun z => genVal hr S z) (fun z => genHom_genVal hr S z)
    (fun i ξ _ => smoothFam_genVal hr S i ξ) x hx hd

end AmbVal

end IntLInfty.Kan.A83Ev

namespace IntLInfty.Kan.A83Defect

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83Defect

namespace IntLInfty.Kan.A83Defect

end IntLInfty.Kan.A83Defect

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem ceLift_mem_deg (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : GenHom f) {p : ℕ}
    {a : CE L} (ha : a ∈ ceDeg L p) (x : Fin m → ℝ) :
    ceLift f hf a x ∈ ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ)) :=
  IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 f hf (ceLift f hf) (ceLift_gen f hf) ha x

theorem isCr_sum (hr : 1 ≤ r) {ι : Type} (s : Finset ι) (ω : ι → Ω m)
    (h : ∀ k ∈ s, IsCr r (ω k)) : IsCr r (∑ k ∈ s, ω k) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 <;> assumption)

variable [∀ i, FiniteDimensional ℝ (L i)]

theorem isCr_genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : IsCr r (genVal hr S z i ξ) := by
  have e : FormEqOn (rawVal hr S z i ξ) (genVal hr S z i ξ) :=
    fun x hx => (cutL_eqOn (rawVal hr S z i ξ) x hx).symm
  refine A83DGA.isCr_of_formEqOn e ?_
  by_cases h : i < m
  · rw [rawVal_lt hr S z h]
    exact isCr_sum hr _ _ fun k _ => isCr_smul hr _ (A83Wedge.wRep_spec hr _).1.2
  · rw [rawVal_ge hr S z h]; exact isCr_zero

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83KK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem isCr_Kop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    IsCr r (Kop n β) := ((IntLInfty.Kan.A83Poinc.C1 r hr).1 m n β hC hD).2.1

end IntLInfty.Kan.A83KK

namespace IntLInfty.Kan.A83KL

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

noncomputable def KCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m (n + 1) →L[ℝ] CrForms r m n :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose m n

theorem KLin_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m (n + 1)) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (KCLM hr n w : Jet r m × Jet r m) = jet r (Kop n ω) :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose_spec.choose_spec.1 m n w ω hC h

end IntLInfty.Kan.A83KL

namespace IntLInfty.Kan.A83G

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem smoothFam_defect (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    SmoothFam r ((t : ℕ) + 1 + 1) (fun z : Amb r S m => A83DGA.ceLift (genVal hr S z)
      (genHom_genVal hr S z) (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t))))) :=
  smoothFam_eval hr S _ (hcl _ _ (genBasis S t k).2)
    (fun z y _ => ceLift_mem_deg _ _ (δ.deg _ _ (A83DGA.gen_mem_ceDeg _ _)) y)

noncomputable def Gfam (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) : Amb r S m → CrForms r m ((t : ℕ) + 1 + 1) :=
  (smoothFam_defect hr δ S hcl t k).choose

noncomputable def Gmap (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) : Amb r S m :=
  fun t k => KCLM hr ((t : ℕ) + 1) (Gfam hr δ S hcl t k z)

theorem Gmap_contDiff (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) :
    ContDiff ℝ ∞ (Gmap (m := m) hr δ S hcl) := by
  refine contDiff_pi.2 fun t => contDiff_pi.2 fun k => ?_
  exact (KCLM hr ((t : ℕ) + 1)).contDiff.comp (smoothFam_defect hr δ S hcl t k).choose_spec.1

theorem Gmap_val (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    (Gmap hr δ S hcl z t k : Jet r m × Jet r m) = jet r (Kop ((t : ℕ) + 1)
      (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t)))))) := by
  have h := (smoothFam_defect hr δ S hcl t k).choose_spec.2 z
  exact KLin_val hr _ h.1.2 h.2

end IntLInfty.Kan.A83G

namespace IntLInfty.Kan.A83H

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Fill IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL
  IntLInfty.Kan.A83Ev IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G
  IntLInfty.Kan.A83Graph
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83H

namespace IntLInfty.Kan.A83W

open IntLInfty.Kan
open scoped BoundedContinuousFunction

theorem exists_pow_norm_lt_one {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] (V : X →L[ℝ] X) (T : X → Y) {a b θ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hθ0 : 0 ≤ θ) (hθ : θ < 1) (h1 : ∀ x, ‖x‖ ≤ a * ‖T x‖) (h2 : ∀ x, ‖T x‖ ≤ b * ‖x‖)
    (hV : ∀ x, ‖T (V x)‖ ≤ θ * ‖T x‖) : ∃ n : ℕ, ‖V ^ n‖ < 1 := by
  have hpow : ∀ n : ℕ, ∀ x, ‖T ((V ^ n) x)‖ ≤ θ ^ n * ‖T x‖ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      calc ‖T (V ((V ^ n) x))‖ ≤ θ * ‖T ((V ^ n) x)‖ := hV _
        _ ≤ θ * (θ ^ n * ‖T x‖) := mul_le_mul_of_nonneg_left (ih x) hθ0
        _ = θ ^ (n + 1) * ‖T x‖ := by ring
  have hab : 0 < a * b + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (a * b + 1) by positivity) hθ
  have hθn : 0 ≤ θ ^ n := pow_nonneg hθ0 n
  refine ⟨n, lt_of_le_of_lt (ContinuousLinearMap.opNorm_le_bound _
    (by positivity : 0 ≤ a * b * θ ^ n) fun x => ?_) ?_⟩
  · calc ‖(V ^ n) x‖ ≤ a * ‖T ((V ^ n) x)‖ := h1 _
      _ ≤ a * (θ ^ n * ‖T x‖) := mul_le_mul_of_nonneg_left (hpow n x) ha
      _ ≤ a * (θ ^ n * (b * ‖x‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h2 x) hθn) ha
      _ = a * b * θ ^ n * ‖x‖ := by ring
  · calc a * b * θ ^ n ≤ (a * b + 1) * θ ^ n :=
          mul_le_mul_of_nonneg_right (by linarith) hθn
      _ < (a * b + 1) * (1 / (a * b + 1)) := mul_lt_mul_of_pos_left hn hab
      _ = 1 := by field_simp

theorem cone_exp_le {lam s : ℝ} (hl : 0 < lam) (hs : 0 ≤ s) :
    s * ∫ t in (0 : ℝ)..1, Real.exp (-(lam * (s * (1 - t)))) ≤ 1 / lam := by
  rcases hs.eq_or_lt with h | h
  · subst h; simp; positivity
  have hc : (lam * s) ≠ 0 := by positivity
  have e1 : (fun t : ℝ => Real.exp (-(lam * (s * (1 - t))))) =
      fun t => Real.exp ((lam * s) * t + -(lam * s)) := by
    funext t; congr 1; ring
  rw [e1, intervalIntegral.integral_comp_mul_add (fun x => Real.exp x) hc, integral_exp]
  simp only [mul_zero, mul_one, zero_add, add_neg_cancel, Real.exp_zero, smul_eq_mul]
  rw [div_eq_mul_inv, one_mul]
  have he : 0 < Real.exp (-(lam * s)) := Real.exp_pos _
  have : s * ((lam * s)⁻¹ * (1 - Real.exp (-(lam * s)))) = lam⁻¹ * (1 - Real.exp (-(lam * s))) := by
    field_simp
  rw [this]
  have hl' : 0 < lam⁻¹ := inv_pos.2 hl
  nlinarith

variable {r m : ℕ}

noncomputable def wt (lam : ℝ) (m : ℕ) : simplex m →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun y => Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)), by fun_prop⟩

theorem wt_apply (lam : ℝ) (y : simplex m) :
    wt lam m y = Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) := rfl

noncomputable def Wj (lam ε : ℝ) (w : Jet r m) : Jet r m :=
  fun I k β => (ε ^ (k : ℕ)) • (wt lam m * w I k β)

theorem Wj_apply (lam ε : ℝ) (w : Jet r m) (I : Finset (Fin m)) (k : Fin (r + 1))
    (β : Fin (k : ℕ) → Fin m) (y : simplex m) :
    Wj lam ε w I k β y = ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * w I k β y) := by
  show ((ε ^ (k : ℕ)) • (wt lam m * w I k β)) y = _
  rw [BoundedContinuousFunction.smul_apply, BoundedContinuousFunction.mul_apply, wt_apply,
    smul_eq_mul]

theorem norm_simplex_le_one {y : Fin m → ℝ} (hy : y ∈ simplex m) : ‖y‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (hy.1 i)]
  calc y i ≤ ∑ j, y j := Finset.single_le_sum (fun j _ => hy.1 j) (Finset.mem_univ i)
    _ ≤ 1 := hy.2

theorem jet_norm_le {w : Jet r m} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ I k β (y : simplex m), |w I k β y| ≤ C) : ‖w‖ ≤ C := by
  show ‖(w : (I : Finset (Fin m)) → (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) →
    (simplex m →ᵇ ℝ))‖ ≤ C
  refine (pi_norm_le_iff_of_nonneg hC).2 fun I => (pi_norm_le_iff_of_nonneg hC).2 fun k =>
    (pi_norm_le_iff_of_nonneg hC).2 fun β => ?_
  exact (BoundedContinuousFunction.norm_le hC).2 fun y => by
    rw [Real.norm_eq_abs]; exact h I k β y

theorem abs_le_jet_norm (w : Jet r m) (I : Finset (Fin m)) (k : Fin (r + 1))
    (β : Fin (k : ℕ) → Fin m) (y : simplex m) : |w I k β y| ≤ ‖w‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖w I k β y‖ ≤ ‖w I k β‖ := BoundedContinuousFunction.norm_coe_le_norm _ _
    _ ≤ ‖w I k‖ := norm_le_pi_norm _ β
    _ ≤ ‖w I‖ := norm_le_pi_norm _ k
    _ ≤ ‖w‖ := norm_le_pi_norm (f := (w : (I : Finset (Fin m)) → (k : Fin (r + 1)) →
        (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ))) I

theorem norm_Wj_le {lam ε : ℝ} (hl : 0 ≤ lam) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (w : Jet r m) :
    ‖Wj lam ε w‖ ≤ ‖w‖ := by
  refine jet_norm_le (norm_nonneg _) fun I k β y => ?_
  rw [Wj_apply, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hε0 _),
    abs_of_pos (Real.exp_pos _)]
  have h1 : ε ^ (k : ℕ) ≤ 1 := pow_le_one₀ hε0 hε1
  have h2 : Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by have := norm_nonneg (y : Fin m → ℝ); nlinarith)
  have h3 := abs_le_jet_norm w I k β y
  have h4 : 0 ≤ |w I k β y| := abs_nonneg _
  calc ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * |w I k β y|)
      ≤ 1 * (1 * |w I k β y|) := by gcongr
    _ ≤ ‖w‖ := by linarith

theorem norm_le_Wj {lam ε : ℝ} (hl : 0 ≤ lam) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (w : Jet r m) :
    ‖w‖ ≤ (ε ^ r)⁻¹ * Real.exp lam * ‖Wj lam ε w‖ := by
  refine jet_norm_le (by positivity) fun I k β y => ?_
  have hy1 := norm_simplex_le_one y.2
  have hk : (k : ℕ) ≤ r := Nat.lt_succ_iff.1 k.2
  have hεk : ε ^ r ≤ ε ^ (k : ℕ) := pow_le_pow_of_le_one hε0.le hε1 hk
  have hεr : 0 < ε ^ r := pow_pos hε0 r
  have he : Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * Real.exp lam ≥ 1 := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by nlinarith)
  have hW := abs_le_jet_norm (Wj lam ε w) I k β y
  rw [Wj_apply, abs_mul, abs_mul, abs_of_pos (pow_pos hε0 _), abs_of_pos (Real.exp_pos _)] at hW
  have hx : 0 ≤ |w I k β y| := abs_nonneg _
  have hE : 0 < Real.exp lam := Real.exp_pos _
  have hE2 : 0 < Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) := Real.exp_pos _
  rw [show (ε ^ r)⁻¹ * Real.exp lam * ‖Wj lam ε w‖ = Real.exp lam * ‖Wj lam ε w‖ / ε ^ r by
    field_simp]
  rw [le_div_iff₀ hεr]
  calc |w I k β y| * ε ^ r ≤ |w I k β y| * ε ^ (k : ℕ) := by gcongr
    _ ≤ |w I k β y| * ε ^ (k : ℕ) *
        (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * Real.exp lam) := by
          have := mul_nonneg hx (pow_nonneg hε0.le (k : ℕ)); nlinarith
    _ = Real.exp lam * (ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * |w I k β y|)) := by
          ring
    _ ≤ Real.exp lam * ‖Wj lam ε w‖ := by gcongr

end IntLInfty.Kan.A83W

namespace IntLInfty.Kan.A83W

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc Set

section ConeW

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

theorem coneInt_wbound_zero {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {lam : ℝ} (hl : 0 < lam) (f : E → F) (p : ℕ)
    {M : ℝ} (hM : ∀ z ∈ S, Real.exp (-(lam * ‖z‖)) * ‖f z‖ ≤ M) {y : E} (hy : y ∈ S) :
    Real.exp (-(lam * ‖y‖)) * ‖coneInt p f y‖ ≤ M ∧
      ‖y‖ * (Real.exp (-(lam * ‖y‖)) * ‖coneInt p f y‖) ≤ M / lam := by
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0 h0)
  have hb : ‖coneInt p f y‖ ≤ ∫ t in (0 : ℝ)..1, M * Real.exp (lam * (‖y‖ * t)) := by
    refine intervalIntegral.norm_integral_le_of_norm_le (g := fun t => M * Real.exp (lam * (‖y‖ * t)))
      zero_le_one (MeasureTheory.ae_of_all _ fun t ht => ?_)
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
    have ht' : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have htu : t ∈ Set.uIoc (0 : ℝ) 1 := by rw [Set.uIoc_of_le zero_le_one]; exact ht
    have hty : t • y ∈ S := hconv.smul_mem_of_zero_mem h0 hy ht'
    have hn : ‖t • y‖ = ‖y‖ * t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht'.1, mul_comm]
    have h1 := hM _ hty
    rw [hn] at h1
    have h2 : ‖f (t • y)‖ ≤ M * Real.exp (lam * (‖y‖ * t)) := by
      have he : Real.exp (lam * (‖y‖ * t)) * Real.exp (-(lam * (‖y‖ * t))) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      calc ‖f (t • y)‖ = Real.exp (lam * (‖y‖ * t)) *
            (Real.exp (-(lam * (‖y‖ * t))) * ‖f (t • y)‖) := by rw [← mul_assoc, he, one_mul]
        _ ≤ Real.exp (lam * (‖y‖ * t)) * M := by gcongr
        _ = M * Real.exp (lam * (‖y‖ * t)) := mul_comm _ _
    rw [norm_smul]
    calc ‖t ^ p‖ * ‖f (t • y)‖ ≤ 1 * ‖f (t • y)‖ :=
          mul_le_mul_of_nonneg_right (norm_pow_le_one htu) (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact h2
  have he : Real.exp (-(lam * ‖y‖)) * ∫ t in (0 : ℝ)..1, M * Real.exp (lam * (‖y‖ * t)) =
      M * ∫ t in (0 : ℝ)..1, Real.exp (-(lam * (‖y‖ * (1 - t)))) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hI : ∫ t in (0 : ℝ)..1, Real.exp (-(lam * (‖y‖ * (1 - t)))) ≤ 1 := by
    have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) (a := (0 : ℝ)) (b := 1)
      (f := fun t : ℝ => Real.exp (-(lam * (‖y‖ * (1 - t))))) (g := fun _ => (1 : ℝ)) zero_le_one
      (Continuous.intervalIntegrable (by fun_prop) 0 1)
      (Continuous.intervalIntegrable continuous_const 0 1)
      (fun t ht => Real.exp_le_one_iff.2 (by
        have := norm_nonneg y
        have h1t : 0 ≤ 1 - t := by linarith [ht.2]
        have := mul_nonneg this h1t
        nlinarith))
    simpa using this
  have hE : 0 ≤ Real.exp (-(lam * ‖y‖)) := (Real.exp_pos _).le
  have key : Real.exp (-(lam * ‖y‖)) * ‖coneInt p f y‖ ≤
      M * ∫ t in (0 : ℝ)..1, Real.exp (-(lam * (‖y‖ * (1 - t)))) := by
    rw [← he]; exact mul_le_mul_of_nonneg_left hb hE
  refine ⟨key.trans (by nlinarith), ?_⟩
  have hc := cone_exp_le hl (norm_nonneg y)
  calc ‖y‖ * (Real.exp (-(lam * ‖y‖)) * ‖coneInt p f y‖)
      ≤ ‖y‖ * (M * ∫ t in (0 : ℝ)..1, Real.exp (-(lam * (‖y‖ * (1 - t))))) :=
        mul_le_mul_of_nonneg_left key (norm_nonneg _)
    _ = M * (‖y‖ * ∫ t in (0 : ℝ)..1, Real.exp (-(lam * (‖y‖ * (1 - t))))) := by ring
    _ ≤ M * (1 / lam) := mul_le_mul_of_nonneg_left hc hM0
    _ = M / lam := by ring

theorem coneInt_wbound (hS : IsCompact S) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S)
    (hU : UniqueDiffOn ℝ S) {lam : ℝ} (hl : 0 < lam) (j : ℕ) :
    ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (f : E → F)
      (p : ℕ), ContDiffOn ℝ j f S → ∀ {M : ℝ},
      (∀ z ∈ S, Real.exp (-(lam * ‖z‖)) * ‖iteratedFDerivWithin ℝ j f S z‖ ≤ M) →
      ∀ y ∈ S, Real.exp (-(lam * ‖y‖)) * ‖iteratedFDerivWithin ℝ j (coneInt p f) S y‖ ≤ M ∧
        ‖y‖ * (Real.exp (-(lam * ‖y‖)) * ‖iteratedFDerivWithin ℝ j (coneInt p f) S y‖) ≤
          M / lam := by
  induction j with
  | zero =>
    intro F _ _ _ f p _ M hM y hy
    simp only [norm_iteratedFDerivWithin_zero] at hM ⊢
    exact coneInt_wbound_zero hconv h0 hl f p hM hy
  | succ j ih =>
    intro F _ _ _ f p hf M hM y hy
    have hd : ∀ x ∈ S, HasFDerivWithinAt f (fderivWithin ℝ f S x) S x := fun x hx =>
      ((hf.differentiableOn (by simp)) x hx).hasFDerivWithinAt
    have hc : ContinuousOn (fderivWithin ℝ f S) S := hf.continuousOn_fderivWithin hU (by simp)
    have hfd : ContDiffOn ℝ j (fderivWithin ℝ f S) S := hf.fderivWithin hU (by push_cast; rfl)
    have heq : EqOn (fderivWithin ℝ (coneInt p f) S) (coneInt (p + 1) (fderivWithin ℝ f S)) S :=
      fun x hx => (hasFDerivWithinAt_coneInt hS hconv h0 hd hc p hx).fderivWithin (hU x hx)
    rw [← norm_iteratedFDerivWithin_fderivWithin hU hy, iteratedFDerivWithin_congr heq hy]
    refine ih (fderivWithin ℝ f S) (p + 1) hfd (fun z hz => ?_) y hy
    rw [norm_iteratedFDerivWithin_fderivWithin hU hz]
    exact hM z hz

theorem norm_iter_id_two (i : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (i + 2) (id : E → E) x‖ = 0 := by
  have hf : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun z => (hasFDerivAt_id z).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem norm_iter_id_one (x : E) : ‖iteratedFDeriv ℝ 1 (id : E → E) x‖ ≤ 1 := by
  have hf : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun z => (hasFDerivAt_id z).fderiv
  rw [← norm_iteratedFDeriv_fderiv, hf, norm_iteratedFDeriv_zero]
  exact ContinuousLinearMap.norm_id_le

end ConeW

attribute [local instance] algNAG algNS algFD algComplete

variable {m : ℕ}

theorem Kop_wbound {lam : ℝ} (hl : 0 < lam) {r n k : ℕ} (hk : k ≤ r) {β : Ω m}
    (hβ : ContDiffOn ℝ r β (simplex m)) {M M' : ℝ}
    (hM : ∀ z ∈ simplex m,
      Real.exp (-(lam * ‖z‖)) * ‖iteratedFDerivWithin ℝ k β (simplex m) z‖ ≤ M)
    (hM' : ∀ z ∈ simplex m,
      Real.exp (-(lam * ‖z‖)) * ‖iteratedFDerivWithin ℝ (k - 1) β (simplex m) z‖ ≤ M')
    {y : Fin m → ℝ} (hy : y ∈ simplex m) :
    Real.exp (-(lam * ‖y‖)) * ‖iteratedFDerivWithin ℝ k (Kop n β) (simplex m) y‖ ≤
      ‖cB m‖ * (M / lam + k * M') := by
  have hU := A83.uniqueDiffOn_simplex m
  have hS := isCompact_simplex m
  have hconv := A83.convex_simplex m
  have h0 := zero_mem_simplex m
  set g := coneInt n β with hg
  have hgc : ContDiffOn ℝ r g (simplex m) := contDiffOn_coneInt hS hconv h0 hU r β n hβ
  have hK : Kop n β = fun y => cB m (id y) (g y) := rfl
  have hb := (cB m).norm_iteratedFDerivWithin_le_of_bilinear (contDiffOn_id (s := simplex m))
    hgc hU hy (n := k) (by exact_mod_cast hk)
  rw [← hK] at hb
  have hid : ∀ i, iteratedFDerivWithin ℝ i (id : (Fin m → ℝ) → (Fin m → ℝ)) (simplex m) y =
      iteratedFDeriv ℝ i (id : (Fin m → ℝ) → (Fin m → ℝ)) y := fun i =>
    iteratedFDerivWithin_eq_iteratedFDeriv hU contDiffAt_id hy
  simp only [hid] at hb
  have hE : 0 ≤ Real.exp (-(lam * ‖y‖)) := (Real.exp_pos _).le
  have hw1 := (coneInt_wbound hS hconv h0 hU hl k β n (hβ.of_le (by exact_mod_cast hk)) hM y hy).2
  have hw2 := (coneInt_wbound hS hconv h0 hU hl (k - 1) β n
    (hβ.of_le (by exact_mod_cast (Nat.sub_le k 1).trans hk)) hM' y hy).1
  have hM'0 : 0 ≤ M' := le_trans (by positivity) (hM' 0 h0)
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
      ‖iteratedFDeriv ℝ i (id : (Fin m → ℝ) → (Fin m → ℝ)) y‖ *
      ‖iteratedFDerivWithin ℝ (k - i) g (simplex m) y‖ ≤
      ‖y‖ * ‖iteratedFDerivWithin ℝ k g (simplex m) y‖ +
        k * ‖iteratedFDerivWithin ℝ (k - 1) g (simplex m) y‖ := by
    rcases k with _ | k
    · simp [norm_iteratedFDeriv_zero]
    · rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : ∑ i ∈ Finset.range k, ((k + 1).choose (i + 1 + 1) : ℝ) *
          ‖iteratedFDeriv ℝ (i + 1 + 1) (id : (Fin m → ℝ) → (Fin m → ℝ)) y‖ *
          ‖iteratedFDerivWithin ℝ (k + 1 - (i + 1 + 1)) g (simplex m) y‖ = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [norm_iter_id_two]; ring
      rw [hz, zero_add]
      simp only [Nat.choose_zero_right, Nat.choose_one_right, Nat.cast_one, one_mul,
        norm_iteratedFDeriv_zero, Nat.sub_zero, zero_add, Nat.add_sub_cancel, Nat.cast_add]
      have h1 := norm_iter_id_one (E := Fin m → ℝ) y
      have h2 : 0 ≤ ‖iteratedFDerivWithin ℝ k g (simplex m) y‖ := norm_nonneg _
      have h3 : ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ 1 (id : (Fin m → ℝ) → (Fin m → ℝ)) y‖ *
          ‖iteratedFDerivWithin ℝ k g (simplex m) y‖ ≤
          ((k : ℝ) + 1) * ‖iteratedFDerivWithin ℝ k g (simplex m) y‖ := by
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)
        nlinarith
      have h3' : ((k : ℝ) + 1) * ‖iteratedFDeriv ℝ (0 + 1) (id : (Fin m → ℝ) → (Fin m → ℝ)) y‖ *
          ‖iteratedFDerivWithin ℝ (k + 1 - (0 + 1)) g (simplex m) y‖ ≤
          ((k : ℝ) + 1) * ‖iteratedFDerivWithin ℝ (k + 1 - 1) g (simplex m) y‖ := h3
      have h4 : ‖(id : (Fin m → ℝ) → (Fin m → ℝ)) y‖ = ‖y‖ := rfl
      rw [h4]
      linarith
  have hcB : 0 ≤ ‖cB m‖ := ContinuousLinearMap.opNorm_nonneg _
  calc Real.exp (-(lam * ‖y‖)) * ‖iteratedFDerivWithin ℝ k (Kop n β) (simplex m) y‖
      ≤ Real.exp (-(lam * ‖y‖)) * (‖cB m‖ * (‖y‖ * ‖iteratedFDerivWithin ℝ k g (simplex m) y‖ +
        k * ‖iteratedFDerivWithin ℝ (k - 1) g (simplex m) y‖)) := by
        gcongr
        exact hb.trans (mul_le_mul_of_nonneg_left hsum hcB)
    _ = ‖cB m‖ * (‖y‖ * (Real.exp (-(lam * ‖y‖)) *
          ‖iteratedFDerivWithin ℝ k g (simplex m) y‖) +
        k * (Real.exp (-(lam * ‖y‖)) * ‖iteratedFDerivWithin ℝ (k - 1) g (simplex m) y‖)) := by
        ring
    _ ≤ ‖cB m‖ * (M / lam + k * M') := by
        gcongr

end IntLInfty.Kan.A83W

namespace IntLInfty.Kan.A83E

open IntLInfty.Kan IntLInfty.Kan.A83

variable {m k : ℕ}

theorem abs_unit_le_norm (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin m → ℝ) ℝ)
    (β : Fin k → Fin m) : |g (fun l => Pi.single (β l) 1)| ≤ ‖g‖ := by
  rw [← Real.norm_eq_abs]
  calc ‖g (fun l => Pi.single (β l) 1)‖ ≤ ‖g‖ * ∏ l, ‖(Pi.single (β l) (1 : ℝ) : Fin m → ℝ)‖ :=
        g.le_opNorm _
    _ ≤ ‖g‖ * 1 := by
        gcongr
        refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => ?_
        rw [Pi.norm_single, norm_one]
    _ = ‖g‖ := mul_one _

theorem norm_le_of_unit (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin m → ℝ) ℝ)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ β : Fin k → Fin m, |g (fun l => Pi.single (β l) 1)| ≤ C) :
    ‖g‖ ≤ (m : ℝ) ^ k * C := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  have hv : v = fun l => ∑ j, v l j • (Pi.single j (1 : ℝ) : Fin m → ℝ) := by
    funext l
    conv_lhs => rw [← Finset.univ_sum_single (v l)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  rw [congrArg g hv, g.map_sum]
  calc ‖∑ β : Fin k → Fin m, g (fun l => v l (β l) • (Pi.single (β l) (1 : ℝ) : Fin m → ℝ))‖
      ≤ ∑ β : Fin k → Fin m, ‖g (fun l => v l (β l) • (Pi.single (β l) (1 : ℝ) : Fin m → ℝ))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _β : Fin k → Fin m, C * ∏ l, ‖v l‖ := by
        refine Finset.sum_le_sum fun β _ => ?_
        rw [g.map_smul_univ, norm_smul, norm_prod, mul_comm, Real.norm_eq_abs]
        gcongr
        · exact h β
        · exact norm_le_pi_norm (v _) _
    _ = (m : ℝ) ^ k * C * ∏ l, ‖v l‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

variable {r : ℕ} {f : (Fin m → ℝ) → ℝ}

theorem abs_jetComp_le (hf : ContDiffOn ℝ r f (simplex m)) (hk : k ≤ r) (β : Fin k → Fin m)
    (y : simplex m) :
    |jetComp f k β y| ≤ ‖iteratedFDerivWithin ℝ k f (simplex m) y‖ := by
  obtain ⟨x, hx⟩ := y
  rw [jetComp_apply hf hk β hx]
  exact abs_unit_le_norm _ β

theorem norm_iter_le_jet (hf : ContDiffOn ℝ r f (simplex m)) (hk : k ≤ r) (y : simplex m)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ β : Fin k → Fin m, |jetComp f k β y| ≤ C) :
    ‖iteratedFDerivWithin ℝ k f (simplex m) y‖ ≤ (m : ℝ) ^ k * C := by
  obtain ⟨x, hx⟩ := y
  refine norm_le_of_unit _ hC fun β => ?_
  rw [← jetComp_apply hf hk β hx]
  exact h β

open IntLInfty.Kan.A83Poinc

attribute [local instance] algNAG algNS algFD algComplete

theorem norm_alg_eq (a : Alg m) : ‖a‖ = ‖(formBasis m).equivFun a‖ := rfl

theorem abs_coeffL_le (I : Finset (Fin m)) (a : Alg m) : |coeffL m I a| ≤ ‖a‖ := by
  rw [coeffL_apply, norm_alg_eq, ← Real.norm_eq_abs]
  exact norm_le_pi_norm ((formBasis m).equivFun a) I

theorem norm_coeffL_le (I : Finset (Fin m)) : ‖coeffL m I‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
    rw [one_mul, Real.norm_eq_abs]; exact abs_coeffL_le I a

theorem norm_alg_le {a : Alg m} {C : ℝ} (hC : 0 ≤ C) (h : ∀ I, |coeffL m I a| ≤ C) :
    ‖a‖ ≤ C := by
  rw [norm_alg_eq]
  refine (pi_norm_le_iff_of_nonneg hC).2 fun I => ?_
  rw [Real.norm_eq_abs]
  simpa [coeffL_apply, Module.Basis.equivFun_apply] using h I

theorem norm_mlin_alg_le (g : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin m → ℝ) (Alg m))
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ I, ‖(coeffL m I).compContinuousMultilinearMap g‖ ≤ C) :
    ‖g‖ ≤ C := by
  refine ContinuousMultilinearMap.opNorm_le_bound hC fun v => ?_
  refine norm_alg_le (by positivity) fun I => ?_
  rw [← Real.norm_eq_abs]
  calc ‖coeffL m I (g v)‖ = ‖(coeffL m I).compContinuousMultilinearMap g v‖ := rfl
    _ ≤ ‖(coeffL m I).compContinuousMultilinearMap g‖ * ∏ l, ‖v l‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ ≤ C * ∏ l, ‖v l‖ := by gcongr; exact h I

variable {ω : Ω m}

theorem iter_coeff_eq (hω : ContDiffOn ℝ r ω (simplex m)) (hk : k ≤ r) (I : Finset (Fin m))
    {x : Fin m → ℝ} (hx : x ∈ simplex m) :
    iteratedFDerivWithin ℝ k (coeff ω I) (simplex m) x =
      (coeffL m I).compContinuousMultilinearMap (iteratedFDerivWithin ℝ k ω (simplex m) x) := by
  rw [coeff_eq_coeffL]
  show iteratedFDerivWithin ℝ k (coeffL m I ∘ ω) (simplex m) x = _
  exact (coeffL m I).iteratedFDerivWithin_comp_left (hω x hx) (uniqueDiffOn_simplex m) hx
    (show ((k : ℕ) : WithTop ℕ∞) ≤ (r : WithTop ℕ∞) by exact_mod_cast hk)

theorem contDiffOn_coeff (hω : ContDiffOn ℝ r ω (simplex m)) (I : Finset (Fin m)) :
    ContDiffOn ℝ r (coeff ω I) (simplex m) := by
  rw [coeff_eq_coeffL]
  exact (coeffL m I).contDiff.comp_contDiffOn hω

theorem abs_jetComp_coeff_le (hω : ContDiffOn ℝ r ω (simplex m)) (hk : k ≤ r)
    (I : Finset (Fin m)) (β : Fin k → Fin m) (y : simplex m) :
    |jetComp (coeff ω I) k β y| ≤ ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖ := by
  refine (abs_jetComp_le (contDiffOn_coeff hω I) hk β y).trans ?_
  rw [iter_coeff_eq hω hk I y.2]
  refine ((coeffL m I).norm_compContinuousMultilinearMap_le _).trans ?_
  calc ‖coeffL m I‖ * ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖
      ≤ 1 * ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖ := by gcongr; exact norm_coeffL_le I
    _ = _ := one_mul _

theorem norm_iter_le_jetComp (hω : ContDiffOn ℝ r ω (simplex m)) (hk : k ≤ r) (y : simplex m)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ I (β : Fin k → Fin m), |jetComp (coeff ω I) k β y| ≤ C) :
    ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖ ≤ (m : ℝ) ^ k * C := by
  refine norm_mlin_alg_le _ (by positivity) fun I => ?_
  rw [← iter_coeff_eq hω hk I y.2]
  exact norm_iter_le_jet (contDiffOn_coeff hω I) hk y hC (h I)

end IntLInfty.Kan.A83E

namespace IntLInfty.Kan.A83E

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Leib

attribute [local instance] algNAG algNS algFD algComplete

variable {m r k : ℕ}

theorem wedge_core {γ η : Ω m} (hγ : ContDiffOn ℝ r γ (simplex m))
    (hη : ContDiffOn ℝ r η (simplex m)) (hk : k ≤ r) {ε : ℝ} (hε : 0 ≤ ε)
    {y : Fin m → ℝ} (hy : y ∈ simplex m) :
    ε ^ k * ‖iteratedFDerivWithin ℝ k (γ * η) (simplex m) y‖ ≤
      ‖mulB m‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
        (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖) := by
  rw [mul_eq_mulB]
  have hb := (mulB m).norm_iteratedFDerivWithin_le_of_bilinear hγ hη (uniqueDiffOn_simplex m) hy
    (n := k) (by exact_mod_cast hk)
  have hεk : 0 ≤ ε ^ k := pow_nonneg hε k
  calc ε ^ k * ‖iteratedFDerivWithin ℝ k (fun y => mulB m (γ y) (η y)) (simplex m) y‖
      ≤ ε ^ k * (‖mulB m‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
          ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖ *
          ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖) := by gcongr
    _ = _ := by
        rw [mul_left_comm, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have e : ε ^ k = ε ^ i * ε ^ (k - i) := by rw [← pow_add, Nat.add_sub_cancel' hik]
        rw [e]; ring

theorem wedge_wbound {γ η : Ω m} (hγ : ContDiffOn ℝ r γ (simplex m))
    (hη : ContDiffOn ℝ r η (simplex m)) (hk : k ≤ r) {ε w P : ℝ} (hε : 0 ≤ ε) (hw : 0 ≤ w)
    {y : Fin m → ℝ} (hy : y ∈ simplex m)
    (hP : ∀ i ≤ k, w * ((ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
        (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖)) ≤ P) :
    w * (ε ^ k * ‖iteratedFDerivWithin ℝ k (γ * η) (simplex m) y‖) ≤ ‖mulB m‖ * (2 ^ k * P) := by
  have hc := wedge_core hγ hη hk hε hy
  have hB : 0 ≤ ‖mulB m‖ := ContinuousLinearMap.opNorm_nonneg _
  calc w * (ε ^ k * ‖iteratedFDerivWithin ℝ k (γ * η) (simplex m) y‖)
      ≤ w * (‖mulB m‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
        (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖)) := by gcongr
    _ = ‖mulB m‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        (w * ((ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
        (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖))) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => by ring
    _ ≤ ‖mulB m‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * P := by
        gcongr with i hi
        exact hP i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    _ = ‖mulB m‖ * (2 ^ k * P) := by
        rw [← Finset.sum_mul]
        congr 2
        exact_mod_cast Nat.sum_range_choose k

end IntLInfty.Kan.A83E

namespace IntLInfty.Kan.A83G1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Leib
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83W IntLInfty.Kan.A83E

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem scaled_iter_le {ω : Ω m} (hω : ContDiffOn ℝ r ω (simplex m)) {i : ℕ} (hi : i ≤ r)
    (y : simplex m) {c B : ℝ} (hc : 0 < c) (hB : 0 ≤ B)
    (h : ∀ I (β : Fin i → Fin m), c * |jetComp (coeff ω I) i β y| ≤ B) :
    c * ‖iteratedFDerivWithin ℝ i ω (simplex m) y‖ ≤ (m : ℝ) ^ i * B := by
  have h1 := norm_iter_le_jetComp hω hi y (C := B / c) (div_nonneg hB hc.le)
    (fun I β => by rw [le_div_iff₀ hc, mul_comm]; exact h I β)
  have hc' : c ≠ 0 := hc.ne'
  calc c * ‖iteratedFDerivWithin ℝ i ω (simplex m) y‖ ≤ c * ((m : ℝ) ^ i * (B / c)) :=
        mul_le_mul_of_nonneg_left h1 hc.le
    _ = (m : ℝ) ^ i * B := by field_simp

theorem wcomp_le (γ : Ω m) {lam ε : ℝ} (hε : 0 ≤ ε) {i : ℕ} (hi : i ≤ r) (y : simplex m)
    (I : Finset (Fin m)) (β : Fin i → Fin m) :
    (ε ^ i * Real.exp (-(lam * ‖(y : Fin m → ℝ)‖))) * |jetComp (coeff γ I) i β y| ≤
      ‖Wj lam ε (jet r γ).1‖ := by
  have h := abs_le_jet_norm (Wj lam ε (jet r γ).1) I ⟨i, Nat.lt_succ_of_le hi⟩ β y
  rw [Wj_apply, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hε _),
    abs_of_nonneg (Real.exp_pos _).le] at h
  rw [mul_assoc]
  exact h

theorem ucomp_le (η : Ω m) {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) {i : ℕ} (hi : i ≤ r)
    (y : simplex m) (I : Finset (Fin m)) (β : Fin i → Fin m) :
    ε ^ i * |jetComp (coeff η I) i β y| ≤ ‖(jet r η).1‖ := by
  have h := abs_le_jet_norm (jet r η).1 I ⟨i, Nat.lt_succ_of_le hi⟩ β y
  have h1 : ε ^ i ≤ 1 := pow_le_one₀ hε hε1
  have h0 : 0 ≤ |jetComp (coeff η I) i β y| := abs_nonneg _
  calc ε ^ i * |jetComp (coeff η I) i β y| ≤ 1 * |jetComp (coeff η I) i β y| :=
        mul_le_mul_of_nonneg_right h1 h0
    _ ≤ ‖(jet r η).1‖ := by rw [one_mul]; exact h

theorem Wj_jet_le_of {ω : Ω m} (hω : ContDiffOn ℝ r ω (simplex m)) {lam ε X : ℝ} (hε : 0 ≤ ε)
    (hX : 0 ≤ X)
    (h : ∀ k ≤ r, ∀ y : simplex m, Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) *
      (ε ^ k * ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖) ≤
        ‖mulB m‖ * (2 ^ k * ((m : ℝ) ^ k * X))) :
    ‖Wj lam ε (jet r ω).1‖ ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r * X := by
  have hM : 0 ≤ ‖mulB m‖ := ContinuousLinearMap.opNorm_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  refine jet_norm_le (mul_nonneg (mul_nonneg hM (pow_nonneg (by linarith) _)) hX)
    fun I k β y => ?_
  have hk : (k : ℕ) ≤ r := Nat.lt_succ_iff.mp k.2
  rw [Wj_apply]
  have e0 : 0 ≤ Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) := (Real.exp_pos _).le
  have hJ' : |(jet r ω).1 I k β y| ≤ ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖ :=
    abs_jetComp_coeff_le hω hk I β y
  have hpow : (2 : ℝ) ^ (k : ℕ) * (m : ℝ) ^ (k : ℕ) ≤ (2 * (m : ℝ) + 1) ^ r := by
    rw [← mul_pow]
    calc (2 * (m : ℝ)) ^ (k : ℕ) ≤ (2 * (m : ℝ) + 1) ^ (k : ℕ) :=
          pow_le_pow_left₀ (by positivity) (by linarith) _
      _ ≤ (2 * (m : ℝ) + 1) ^ r := pow_le_pow_right₀ (by linarith) hk
  calc |ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * (jet r ω).1 I k β y)|
      = Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * (ε ^ (k : ℕ) * |(jet r ω).1 I k β y|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hε _), abs_of_nonneg e0]; ring
    _ ≤ Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) *
          (ε ^ (k : ℕ) * ‖iteratedFDerivWithin ℝ k ω (simplex m) y‖) := by gcongr
    _ ≤ ‖mulB m‖ * (2 ^ (k : ℕ) * ((m : ℝ) ^ (k : ℕ) * X)) := h k hk y
    _ = ‖mulB m‖ * ((2 ^ (k : ℕ) * (m : ℝ) ^ (k : ℕ)) * X) := by ring
    _ ≤ ‖mulB m‖ * ((2 * (m : ℝ) + 1) ^ r * X) := by gcongr
    _ = ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r * X := by ring

theorem wedge_WL {γ η : Ω m} (cγ : ContDiffOn ℝ r γ (simplex m)) (cη : ContDiffOn ℝ r η (simplex m))
    (cγη : ContDiffOn ℝ r (γ * η) (simplex m)) {lam ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖Wj lam ε (jet r (γ * η)).1‖ ≤
      ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r * (‖Wj lam ε (jet r γ).1‖ * ‖(jet r η).1‖) := by
  refine Wj_jet_le_of cγη hε0.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun k hk y => ?_
  refine wedge_wbound cγ cη hk hε0.le (Real.exp_pos _).le y.2 fun i hi => ?_
  have h1 := scaled_iter_le cγ (hi.trans hk) y (mul_pos (pow_pos hε0 i) (Real.exp_pos _))
    (norm_nonneg _) (wcomp_le γ hε0.le (hi.trans hk) y (lam := lam))
  have h2 := scaled_iter_le cη ((Nat.sub_le k i).trans hk) y (pow_pos hε0 (k - i)) (norm_nonneg _)
    (ucomp_le η hε0.le hε1 ((Nat.sub_le k i).trans hk) y)
  have hpk : (m : ℝ) ^ k = (m : ℝ) ^ i * (m : ℝ) ^ (k - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  calc Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) *
        ((ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
          (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖))
      = ((ε ^ i * Real.exp (-(lam * ‖(y : Fin m → ℝ)‖))) *
            ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
          (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖) := by ring
    _ ≤ ((m : ℝ) ^ i * ‖Wj lam ε (jet r γ).1‖) * ((m : ℝ) ^ (k - i) * ‖(jet r η).1‖) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (m : ℝ) ^ k * (‖Wj lam ε (jet r γ).1‖ * ‖(jet r η).1‖) := by rw [hpk]; ring

theorem wedge_WR {γ η : Ω m} (cγ : ContDiffOn ℝ r γ (simplex m)) (cη : ContDiffOn ℝ r η (simplex m))
    (cγη : ContDiffOn ℝ r (γ * η) (simplex m)) {lam ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖Wj lam ε (jet r (γ * η)).1‖ ≤
      ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r * (‖(jet r γ).1‖ * ‖Wj lam ε (jet r η).1‖) := by
  refine Wj_jet_le_of cγη hε0.le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) fun k hk y => ?_
  refine wedge_wbound cγ cη hk hε0.le (Real.exp_pos _).le y.2 fun i hi => ?_
  have h1 := scaled_iter_le cγ (hi.trans hk) y (pow_pos hε0 i) (norm_nonneg _)
    (ucomp_le γ hε0.le hε1 (hi.trans hk) y)
  have h2 := scaled_iter_le cη ((Nat.sub_le k i).trans hk) y
    (mul_pos (pow_pos hε0 (k - i)) (Real.exp_pos _)) (norm_nonneg _)
    (wcomp_le η hε0.le ((Nat.sub_le k i).trans hk) y (lam := lam))
  have hpk : (m : ℝ) ^ k = (m : ℝ) ^ i * (m : ℝ) ^ (k - i) := by
    rw [← pow_add, Nat.add_sub_cancel' hi]
  calc Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) *
        ((ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
          (ε ^ (k - i) * ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖))
      = (ε ^ i * ‖iteratedFDerivWithin ℝ i γ (simplex m) y‖) *
          ((ε ^ (k - i) * Real.exp (-(lam * ‖(y : Fin m → ℝ)‖))) *
            ‖iteratedFDerivWithin ℝ (k - i) η (simplex m) y‖) := by ring
    _ ≤ ((m : ℝ) ^ i * ‖(jet r γ).1‖) * ((m : ℝ) ^ (k - i) * ‖Wj lam ε (jet r η).1‖) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = (m : ℝ) ^ k * (‖(jet r γ).1‖ * ‖Wj lam ε (jet r η).1‖) := by rw [hpk]; ring

theorem Wj_add_smul_le {lam ε : ℝ} (a b : Jet r m) (c : ℝ) :
    ‖Wj lam ε (a + c • b)‖ ≤ ‖Wj lam ε a‖ + |c| * ‖Wj lam ε b‖ := by
  refine jet_norm_le (by positivity) fun I k β y => ?_
  have ha := abs_le_jet_norm (Wj lam ε a) I k β y
  have hb := abs_le_jet_norm (Wj lam ε b) I k β y
  rw [Wj_apply] at ha hb ⊢
  have e : (a + c • b) I k β y = a I k β y + c * b I k β y := rfl
  rw [e]
  calc |ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * (a I k β y + c * b I k β y))|
      = |ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * a I k β y) +
          c * (ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * b I k β y))| := by
        congr 1; ring
    _ ≤ |ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * a I k β y)| +
          |c| * |ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * b I k β y)| := by
        rw [← abs_mul]; exact abs_add_le _ _
    _ ≤ ‖Wj lam ε a‖ + |c| * ‖Wj lam ε b‖ := by gcongr

theorem jet_snd_mul (hr : 1 ≤ r) {p : ℕ} {γ η : Ω m} (hγ : IsCr r γ) (hη : IsCr r η)
    (hD : IsDeg p γ) :
    (jet r (γ * η)).2 = (jet r (extD γ * η)).1 + ((-1 : ℝ) ^ p) • (jet r (γ * extD η)).1 := by
  have hS : FormEqOn (extD (γ * η)) (extD γ * η + ((-1 : ℝ) ^ p) • (γ * extD η)) :=
    fun x hx => by rw [extD_mul hr hγ hη hD hx]; rfl
  have c1 : IsCr r (extD γ * η) := isCr_mul hr (isCr_extD hr hγ) hη (isDeg_extD hr hγ hD)
  have c2 : IsCr r (γ * extD η) := isCr_mul hr hγ (isCr_extD hr hη) hD
  have e1 : (jet r (γ * η)).2 = (jet r (extD (γ * η))).1 := rfl
  rw [e1, jet_congr hS, jet_add hr c1 (isCr_smul hr _ c2), jet_smul hr _ c2] <;> rfl

theorem abs_neg_one_pow (p : ℕ) : |(-1 : ℝ) ^ p| = 1 := by
  rw [abs_pow, abs_neg, abs_one, one_pow]

theorem wedge_WdL (hr : 1 ≤ r) {p : ℕ} {γ η : Ω m} (hγ : IsCr r γ) (hη : IsCr r η)
    (hD : IsDeg p γ) {lam ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖Wj lam ε (jet r (γ * η)).2‖ ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r *
      (‖Wj lam ε (jet r γ).2‖ * ‖(jet r η).1‖ + ‖Wj lam ε (jet r γ).1‖ * ‖(jet r η).2‖) := by
  have c1 : IsCr r (extD γ * η) := isCr_mul hr (isCr_extD hr hγ) hη (isDeg_extD hr hγ hD)
  have c2 : IsCr r (γ * extD η) := isCr_mul hr hγ (isCr_extD hr hη) hD
  have cγ := contDiffOn_of_coeff fun I => (hγ I).1
  have cη := contDiffOn_of_coeff fun I => (hη I).1
  have cdγ := contDiffOn_of_coeff fun I => (isCr_extD hr hγ I).1
  have cdη := contDiffOn_of_coeff fun I => (isCr_extD hr hη I).1
  have b1 := wedge_WL cdγ cη (contDiffOn_of_coeff fun I => (c1 I).1) hε0 hε1 (lam := lam)
  have b2 := wedge_WL cγ cdη (contDiffOn_of_coeff fun I => (c2 I).1) hε0 hε1 (lam := lam)
  have hM : 0 ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r := by
    have := ContinuousLinearMap.opNorm_nonneg (mulB m)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  rw [jet_snd_mul hr hγ hη hD]
  calc ‖Wj lam ε ((jet r (extD γ * η)).1 + ((-1 : ℝ) ^ p) • (jet r (γ * extD η)).1)‖
      ≤ ‖Wj lam ε (jet r (extD γ * η)).1‖ + |(-1 : ℝ) ^ p| * ‖Wj lam ε (jet r (γ * extD η)).1‖ :=
        Wj_add_smul_le _ _ _
    _ ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r * (‖Wj lam ε (jet r (extD γ)).1‖ * ‖(jet r η).1‖) +
          1 * (‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r *
            (‖Wj lam ε (jet r γ).1‖ * ‖(jet r (extD η)).1‖)) := by
        rw [abs_neg_one_pow]; gcongr
    _ = _ := by rw [one_mul, ← mul_add] <;> rfl

theorem wedge_WdR (hr : 1 ≤ r) {p : ℕ} {γ η : Ω m} (hγ : IsCr r γ) (hη : IsCr r η)
    (hD : IsDeg p γ) {lam ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ‖Wj lam ε (jet r (γ * η)).2‖ ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r *
      (‖(jet r γ).2‖ * ‖Wj lam ε (jet r η).1‖ + ‖(jet r γ).1‖ * ‖Wj lam ε (jet r η).2‖) := by
  have c1 : IsCr r (extD γ * η) := isCr_mul hr (isCr_extD hr hγ) hη (isDeg_extD hr hγ hD)
  have c2 : IsCr r (γ * extD η) := isCr_mul hr hγ (isCr_extD hr hη) hD
  have cγ := contDiffOn_of_coeff fun I => (hγ I).1
  have cη := contDiffOn_of_coeff fun I => (hη I).1
  have cdγ := contDiffOn_of_coeff fun I => (isCr_extD hr hγ I).1
  have cdη := contDiffOn_of_coeff fun I => (isCr_extD hr hη I).1
  have b1 := wedge_WR cdγ cη (contDiffOn_of_coeff fun I => (c1 I).1) hε0 hε1 (lam := lam)
  have b2 := wedge_WR cγ cdη (contDiffOn_of_coeff fun I => (c2 I).1) hε0 hε1 (lam := lam)
  have hM : 0 ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r := by
    have := ContinuousLinearMap.opNorm_nonneg (mulB m)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  rw [jet_snd_mul hr hγ hη hD]
  calc ‖Wj lam ε ((jet r (extD γ * η)).1 + ((-1 : ℝ) ^ p) • (jet r (γ * extD η)).1)‖
      ≤ ‖Wj lam ε (jet r (extD γ * η)).1‖ + |(-1 : ℝ) ^ p| * ‖Wj lam ε (jet r (γ * extD η)).1‖ :=
        Wj_add_smul_le _ _ _
    _ ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r * (‖(jet r (extD γ)).1‖ * ‖Wj lam ε (jet r η).1‖) +
          1 * (‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r *
            (‖(jet r γ).1‖ * ‖Wj lam ε (jet r (extD η)).1‖)) := by
        rw [abs_neg_one_pow]; gcongr
    _ = _ := by rw [one_mul, ← mul_add] <;> rfl

theorem wedgeCLM_Wj (hr : 1 ≤ r) {p q : ℕ} (u : CrForms r m p) (w : CrForms r m q)
    {lam ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    let K := ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r
    let U := (u : Jet r m × Jet r m)
    let V := (w : Jet r m × Jet r m)
    let Z := (wedgeCLM hr p q u w : Jet r m × Jet r m)
    ‖Wj lam ε Z.1‖ ≤ K * (‖Wj lam ε U.1‖ * ‖V.1‖) ∧
    ‖Wj lam ε Z.1‖ ≤ K * (‖U.1‖ * ‖Wj lam ε V.1‖) ∧
    ‖Wj lam ε Z.2‖ ≤ K * (‖Wj lam ε U.2‖ * ‖V.1‖ + ‖Wj lam ε U.1‖ * ‖V.2‖) ∧
    ‖Wj lam ε Z.2‖ ≤ K * (‖U.2‖ * ‖Wj lam ε V.1‖ + ‖U.1‖ * ‖Wj lam ε V.2‖) := by
  intro K U V Z
  obtain ⟨⟨hγd, hγc⟩, hγj⟩ := wRep_spec hr u
  obtain ⟨⟨hηd, hηc⟩, hηj⟩ := wRep_spec hr w
  have hZ : Z = jet r (wRep hr u * wRep hr w) := wedgeCLM_val hr ⟨hγd, hγc⟩ ⟨hηd, hηc⟩ hγj hηj
  have hU : U = jet r (wRep hr u) := hγj.symm
  have hV : V = jet r (wRep hr w) := hηj.symm
  have cγ := contDiffOn_of_coeff fun I => (hγc I).1
  have cη := contDiffOn_of_coeff fun I => (hηc I).1
  have cγη := contDiffOn_of_coeff fun I => (isCr_mul hr hγc hηc hγd I).1
  rw [hZ, hU, hV]
  exact ⟨wedge_WL cγ cη cγη hε0 hε1, wedge_WR cγ cη cγη hε0 hε1,
    wedge_WdL hr hγc hηc hγd hε0 hε1, wedge_WdR hr hγc hηc hγd hε0 hε1⟩

end IntLInfty.Kan.A83G1

namespace IntLInfty.Kan.A83Loc

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Leib
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83W IntLInfty.Kan.A83Ev IntLInfty.Kan.A83G1
  IntLInfty.Kan.A83Proj
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem Wj_add_le {lam ε : ℝ} (a b : Jet r m) :
    ‖Wj lam ε (a + b)‖ ≤ ‖Wj lam ε a‖ + ‖Wj lam ε b‖ := by
  have h := Wj_add_smul_le (lam := lam) (ε := ε) a b 1
  rwa [one_smul, abs_one, one_mul] at h

theorem Wj_zero_norm {lam ε : ℝ} : ‖Wj lam ε (0 : Jet r m)‖ = 0 := by
  refine le_antisymm (jet_norm_le le_rfl fun I k β y => ?_) (norm_nonneg _)
  rw [Wj_apply]
  have e : (0 : Jet r m) I k β y = 0 := rfl
  rw [e, mul_zero, mul_zero, abs_zero]

theorem Wj_smul_le {lam ε : ℝ} (c : ℝ) (b : Jet r m) :
    ‖Wj lam ε (c • b)‖ ≤ |c| * ‖Wj lam ε b‖ := by
  have h := Wj_add_smul_le (lam := lam) (ε := ε) 0 b c
  rwa [zero_add, Wj_zero_norm, zero_add] at h

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def Loc (Q1 Q2 : ℝ → ℝ → E → ℝ) {n : ℕ} (a : E → CrForms r m n) : Prop :=
  ∀ x, ∃ C : ℝ, 0 ≤ C ∧ ∀ (lam ε : ℝ) (v : E), 0 < ε → ε ≤ 1 →
    ‖Wj lam ε (fderiv ℝ a x v : Jet r m × Jet r m).1‖ ≤ C * Q1 lam ε v ∧
    ‖Wj lam ε (fderiv ℝ a x v : Jet r m × Jet r m).2‖ ≤ C * (Q1 lam ε v + Q2 lam ε v)

def LocFam (Q1 Q2 : ℝ → ℝ → E → ℝ) (r n : ℕ) (F : E → Ω m) : Prop :=
  ∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧
    (∀ z, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = a z) ∧ Loc Q1 Q2 a

variable {Q1 Q2 : ℝ → ℝ → E → ℝ}

theorem diff_of {n : ℕ} {a : E → CrForms r m n} (ha : ContDiff ℝ ∞ a) (x : E) :
    DifferentiableAt ℝ a x :=
  (ha.differentiable (by simp)) x

theorem loc_const {n : ℕ} (c : CrForms r m n) : Loc Q1 Q2 (fun _ : E => c) := fun x =>
  ⟨0, le_rfl, fun lam ε v _ _ => by
    rw [fderiv_const_apply, ContinuousLinearMap.zero_apply]
    exact ⟨by rw [zero_mul]; exact (Wj_zero_norm).le, by rw [zero_mul]; exact (Wj_zero_norm).le⟩⟩

theorem loc_add {n : ℕ} {a b : E → CrForms r m n} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hla : Loc Q1 Q2 a) (hlb : Loc Q1 Q2 b) : Loc Q1 Q2 (fun z => a z + b z) := fun x => by
  obtain ⟨Ca, hCa, hA⟩ := hla x
  obtain ⟨Cb, hCb, hB⟩ := hlb x
  refine ⟨Ca + Cb, add_nonneg hCa hCb, fun lam ε v h0 h1 => ?_⟩
  have hd : fderiv ℝ (fun z => a z + b z) x v = fderiv ℝ a x v + fderiv ℝ b x v := by
    show fderiv ℝ (a + b) x v = _
    rw [((diff_of ha x).hasFDerivAt.add (diff_of hb x).hasFDerivAt).fderiv]
    rfl
  obtain ⟨a1, a2⟩ := hA lam ε v h0 h1
  obtain ⟨b1, b2⟩ := hB lam ε v h0 h1
  rw [hd]
  have e1 : ((fderiv ℝ a x v + fderiv ℝ b x v : CrForms r m n) : Jet r m × Jet r m).1 =
      (fderiv ℝ a x v : Jet r m × Jet r m).1 + (fderiv ℝ b x v : Jet r m × Jet r m).1 := rfl
  have e2 : ((fderiv ℝ a x v + fderiv ℝ b x v : CrForms r m n) : Jet r m × Jet r m).2 =
      (fderiv ℝ a x v : Jet r m × Jet r m).2 + (fderiv ℝ b x v : Jet r m × Jet r m).2 := rfl
  rw [e1, e2]
  constructor
  · calc _ ≤ _ := Wj_add_le _ _
      _ ≤ Ca * Q1 lam ε v + Cb * Q1 lam ε v := add_le_add a1 b1
      _ = (Ca + Cb) * Q1 lam ε v := by ring
  · calc _ ≤ _ := Wj_add_le _ _
      _ ≤ Ca * (Q1 lam ε v + Q2 lam ε v) + Cb * (Q1 lam ε v + Q2 lam ε v) := add_le_add a2 b2
      _ = (Ca + Cb) * (Q1 lam ε v + Q2 lam ε v) := by ring

theorem loc_smul {n : ℕ} (c : ℝ) {a : E → CrForms r m n} (ha : ContDiff ℝ ∞ a)
    (hla : Loc Q1 Q2 a) : Loc Q1 Q2 (fun z => c • a z) := fun x => by
  obtain ⟨Ca, hCa, hA⟩ := hla x
  refine ⟨|c| * Ca, mul_nonneg (abs_nonneg c) hCa, fun lam ε v h0 h1 => ?_⟩
  have hd : fderiv ℝ (fun z => c • a z) x v = c • fderiv ℝ a x v := by
    show fderiv ℝ (c • a) x v = _
    rw [((diff_of ha x).hasFDerivAt.const_smul c).fderiv]
    rfl
  obtain ⟨a1, a2⟩ := hA lam ε v h0 h1
  rw [hd]
  have e1 : ((c • fderiv ℝ a x v : CrForms r m n) : Jet r m × Jet r m).1 =
      c • (fderiv ℝ a x v : Jet r m × Jet r m).1 := rfl
  have e2 : ((c • fderiv ℝ a x v : CrForms r m n) : Jet r m × Jet r m).2 =
      c • (fderiv ℝ a x v : Jet r m × Jet r m).2 := rfl
  rw [e1, e2]
  constructor
  · calc _ ≤ _ := Wj_smul_le _ _
      _ ≤ |c| * (Ca * Q1 lam ε v) := mul_le_mul_of_nonneg_left a1 (abs_nonneg c)
      _ = |c| * Ca * Q1 lam ε v := by ring
  · calc _ ≤ _ := Wj_smul_le _ _
      _ ≤ |c| * (Ca * (Q1 lam ε v + Q2 lam ε v)) := mul_le_mul_of_nonneg_left a2 (abs_nonneg c)
      _ = |c| * Ca * (Q1 lam ε v + Q2 lam ε v) := by ring

theorem loc_wedge (hr : 1 ≤ r) (hQ : ∀ lam ε v, 0 ≤ Q1 lam ε v ∧ 0 ≤ Q2 lam ε v) {p q : ℕ}
    {a : E → CrForms r m p} {b : E → CrForms r m q} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (hla : Loc Q1 Q2 a) (hlb : Loc Q1 Q2 b) :
    Loc Q1 Q2 (fun z => wedgeCLM hr p q (a z) (b z)) := fun x => by
  obtain ⟨Ca, hCa, hA⟩ := hla x
  obtain ⟨Cb, hCb, hB⟩ := hlb x
  have hK0 : 0 ≤ ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r := by
    have := ContinuousLinearMap.opNorm_nonneg (mulB m)
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    positivity
  set K := ‖mulB m‖ * (2 * (m : ℝ) + 1) ^ r with hK
  set Na := ‖(a x : Jet r m × Jet r m)‖ with hNa
  set Nb := ‖(b x : Jet r m × Jet r m)‖ with hNb
  have hNa0 : 0 ≤ Na := norm_nonneg _
  have hNb0 : 0 ≤ Nb := norm_nonneg _
  refine ⟨2 * K * (Ca * Nb + Na * Cb), mul_nonneg (mul_nonneg zero_le_two hK0)
    (add_nonneg (mul_nonneg hCa hNb0) (mul_nonneg hNa0 hCb)), fun lam ε v h0 h1 => ?_⟩
  have hd : fderiv ℝ (fun z => wedgeCLM hr p q (a z) (b z)) x v =
      wedgeCLM hr p q (a x) (fderiv ℝ b x v) + wedgeCLM hr p q (fderiv ℝ a x v) (b x) := by
    rw [(wedgeCLM hr p q).fderiv_of_bilinear (diff_of ha x) (diff_of hb x)]
    rfl
  obtain ⟨a1, a2⟩ := hA lam ε v h0 h1
  obtain ⟨b1, b2⟩ := hB lam ε v h0 h1
  obtain ⟨q1, q2⟩ := hQ lam ε v
  obtain ⟨-, P1, -, P2⟩ := wedgeCLM_Wj hr (a x) (fderiv ℝ b x v) h0 h1 (lam := lam)
  obtain ⟨R1, -, R2, -⟩ := wedgeCLM_Wj hr (fderiv ℝ a x v) (b x) h0 h1 (lam := lam)
  have na1 : ‖(a x : Jet r m × Jet r m).1‖ ≤ Na := norm_fst_le _
  have na2 : ‖(a x : Jet r m × Jet r m).2‖ ≤ Na := norm_snd_le _
  have nb1 : ‖(b x : Jet r m × Jet r m).1‖ ≤ Nb := norm_fst_le _
  have nb2 : ‖(b x : Jet r m × Jet r m).2‖ ≤ Nb := norm_snd_le _
  rw [hd]
  set P := wedgeCLM hr p q (a x) (fderiv ℝ b x v)
  set R := wedgeCLM hr p q (fderiv ℝ a x v) (b x)
  have e1 : ((P + R : CrForms r m (p + q)) : Jet r m × Jet r m).1 =
      (P : Jet r m × Jet r m).1 + (R : Jet r m × Jet r m).1 := rfl
  have e2 : ((P + R : CrForms r m (p + q)) : Jet r m × Jet r m).2 =
      (P : Jet r m × Jet r m).2 + (R : Jet r m × Jet r m).2 := rfl
  rw [e1, e2]
  set A1 := ‖Wj lam ε (fderiv ℝ a x v : Jet r m × Jet r m).1‖
  set A2 := ‖Wj lam ε (fderiv ℝ a x v : Jet r m × Jet r m).2‖
  set B1 := ‖Wj lam ε (fderiv ℝ b x v : Jet r m × Jet r m).1‖
  set B2 := ‖Wj lam ε (fderiv ℝ b x v : Jet r m × Jet r m).2‖
  have hA1 : 0 ≤ A1 := norm_nonneg _
  have hB1 : 0 ≤ B1 := norm_nonneg _
  have hA2 : 0 ≤ A2 := norm_nonneg _
  have hB2 : 0 ≤ B2 := norm_nonneg _
  have m1 : ‖(a x : Jet r m × Jet r m).1‖ * B1 ≤ Na * (Cb * Q1 lam ε v) :=
    mul_le_mul na1 b1 hB1 hNa0
  have m2 : A1 * ‖(b x : Jet r m × Jet r m).1‖ ≤ (Ca * Q1 lam ε v) * Nb :=
    mul_le_mul a1 nb1 (norm_nonneg _) (mul_nonneg hCa q1)
  have m3 : ‖(a x : Jet r m × Jet r m).2‖ * B1 ≤ Na * (Cb * Q1 lam ε v) :=
    mul_le_mul na2 b1 hB1 hNa0
  have m4 : ‖(a x : Jet r m × Jet r m).1‖ * B2 ≤ Na * (Cb * (Q1 lam ε v + Q2 lam ε v)) :=
    mul_le_mul na1 b2 hB2 hNa0
  have m5 : A2 * ‖(b x : Jet r m × Jet r m).1‖ ≤ (Ca * (Q1 lam ε v + Q2 lam ε v)) * Nb :=
    mul_le_mul a2 nb1 (norm_nonneg _) (mul_nonneg hCa (add_nonneg q1 q2))
  have m6 : A1 * ‖(b x : Jet r m × Jet r m).2‖ ≤ (Ca * Q1 lam ε v) * Nb :=
    mul_le_mul a1 nb2 (norm_nonneg _) (mul_nonneg hCa q1)
  have t1 : 0 ≤ K * (Na * Cb) * Q1 lam ε v := mul_nonneg (mul_nonneg hK0 (mul_nonneg hNa0 hCb)) q1
  have t2 : 0 ≤ K * (Ca * Nb) * Q1 lam ε v := mul_nonneg (mul_nonneg hK0 (mul_nonneg hCa hNb0)) q1
  have t3 : 0 ≤ K * (Na * Cb) * Q2 lam ε v := mul_nonneg (mul_nonneg hK0 (mul_nonneg hNa0 hCb)) q2
  have t4 : 0 ≤ K * (Ca * Nb) * Q2 lam ε v := mul_nonneg (mul_nonneg hK0 (mul_nonneg hCa hNb0)) q2
  constructor
  · calc _ ≤ ‖Wj lam ε (P : Jet r m × Jet r m).1‖ + ‖Wj lam ε (R : Jet r m × Jet r m).1‖ :=
          Wj_add_le _ _
      _ ≤ K * (Na * (Cb * Q1 lam ε v)) + K * ((Ca * Q1 lam ε v) * Nb) :=
          add_le_add (P1.trans (mul_le_mul_of_nonneg_left m1 hK0))
            (R1.trans (mul_le_mul_of_nonneg_left m2 hK0))
      _ ≤ 2 * K * (Ca * Nb + Na * Cb) * Q1 lam ε v := by
          have e : 2 * K * (Ca * Nb + Na * Cb) * Q1 lam ε v -
              (K * (Na * (Cb * Q1 lam ε v)) + K * ((Ca * Q1 lam ε v) * Nb)) =
              K * (Na * Cb) * Q1 lam ε v + K * (Ca * Nb) * Q1 lam ε v := by ring
          linarith
  · calc _ ≤ ‖Wj lam ε (P : Jet r m × Jet r m).2‖ + ‖Wj lam ε (R : Jet r m × Jet r m).2‖ :=
          Wj_add_le _ _
      _ ≤ K * (Na * (Cb * Q1 lam ε v) + Na * (Cb * (Q1 lam ε v + Q2 lam ε v))) +
            K * ((Ca * (Q1 lam ε v + Q2 lam ε v)) * Nb + (Ca * Q1 lam ε v) * Nb) :=
          add_le_add (P2.trans (mul_le_mul_of_nonneg_left (add_le_add m3 m4) hK0))
            (R2.trans (mul_le_mul_of_nonneg_left (add_le_add m5 m6) hK0))
      _ ≤ 2 * K * (Ca * Nb + Na * Cb) * (Q1 lam ε v + Q2 lam ε v) := by
          have e : 2 * K * (Ca * Nb + Na * Cb) * (Q1 lam ε v + Q2 lam ε v) -
              (K * (Na * (Cb * Q1 lam ε v) + Na * (Cb * (Q1 lam ε v + Q2 lam ε v))) +
                K * ((Ca * (Q1 lam ε v + Q2 lam ε v)) * Nb + (Ca * Q1 lam ε v) * Nb)) =
              K * (Na * Cb) * Q2 lam ε v + K * (Ca * Nb) * Q2 lam ε v := by ring
          linarith

theorem locFam_of {n : ℕ} {F : E → Ω m} (hS : SmoothFam r n F) (a : E → CrForms r m n)
    (hFa : ∀ z, jet r (F z) = a z) (hl : Loc Q1 Q2 a) : LocFam Q1 Q2 r n F := by
  obtain ⟨a', ha', hFa'⟩ := hS
  have e : a' = a := funext fun z => Subtype.ext ((hFa' z).2.symm.trans (hFa z))
  subst e
  exact ⟨a', ha', hFa', hl⟩

theorem locFam_zero (hr : 1 ≤ r) (n : ℕ) : LocFam (m := m) Q1 Q2 r n (fun _ : E => 0) :=
  locFam_of (smoothFam_zero hr n) (fun _ => 0) (fun _ => by rw [jet_zero' hr]; rfl) (loc_const 0)

theorem locFam_const (hr : 1 ≤ r) {n : ℕ} {w0 : Ω m} (h : IsDeg n w0 ∧ IsCr r w0) :
    LocFam Q1 Q2 r n (fun _ : E => w0) :=
  locFam_of (smoothFam_const hr h) (fun _ => ⟨jet r w0, jet_mem hr h⟩) (fun _ => rfl) (loc_const _)

theorem locFam_add (hr : 1 ≤ r) {n : ℕ} {F G : E → Ω m} (hF : LocFam Q1 Q2 r n F)
    (hG : LocFam Q1 Q2 r n G) : LocFam Q1 Q2 r n (fun z => F z + G z) := by
  obtain ⟨a, ha, hFa, hla⟩ := hF
  obtain ⟨b, hb, hGb, hlb⟩ := hG
  refine locFam_of (smoothFam_add hr ⟨a, ha, hFa⟩ ⟨b, hb, hGb⟩) (fun z => a z + b z)
    (fun z => ?_) (loc_add ha hb hla hlb)
  rw [jet_add hr (hFa z).1.2 (hGb z).1.2, (hFa z).2, (hGb z).2]
  rfl

theorem locFam_smul (hr : 1 ≤ r) {n : ℕ} (c : ℝ) {F : E → Ω m} (hF : LocFam Q1 Q2 r n F) :
    LocFam Q1 Q2 r n (fun z => c • F z) := by
  obtain ⟨a, ha, hFa, hla⟩ := hF
  refine locFam_of (smoothFam_smul hr c ⟨a, ha, hFa⟩) (fun z => c • a z)
    (fun z => ?_) (loc_smul c ha hla)
  rw [jet_smul hr c (hFa z).1.2, (hFa z).2]
  rfl

theorem locFam_sum (hr : 1 ≤ r) {n : ℕ} {ι : Type} (s : Finset ι) {F : ι → E → Ω m}
    (hF : ∀ i ∈ s, LocFam Q1 Q2 r n (F i)) : LocFam Q1 Q2 r n (fun z => ∑ i ∈ s, F i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locFam_zero (E := E) (m := m) (Q1 := Q1) (Q2 := Q2) hr n
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact locFam_add hr (hF i (Finset.mem_insert_self i s))
      (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

theorem locFam_mul (hr : 1 ≤ r) (hQ : ∀ lam ε v, 0 ≤ Q1 lam ε v ∧ 0 ≤ Q2 lam ε v) {p q : ℕ}
    {F G : E → Ω m} (hF : LocFam Q1 Q2 r p F) (hG : LocFam Q1 Q2 r q G) :
    LocFam Q1 Q2 r (p + q) (fun z => F z * G z) := by
  obtain ⟨a, ha, hFa, hla⟩ := hF
  obtain ⟨b, hb, hGb, hlb⟩ := hG
  refine locFam_of (smoothFam_mul hr ⟨a, ha, hFa⟩ ⟨b, hb, hGb⟩)
    (fun z => wedgeCLM hr p q (a z) (b z)) (fun z => ?_) (loc_wedge hr hQ ha hb hla hlb)
  exact (wedgeCLM_val hr (hFa z).1 (hGb z).1 (hFa z).2 (hGb z).2).symm

theorem locFam_congr {n : ℕ} {F G : E → Ω m} (hF : LocFam Q1 Q2 r n F)
    (h : ∀ z, FormEqOn (G z) (F z)) : LocFam Q1 Q2 r n G := by
  obtain ⟨a, ha, hFa, hla⟩ := hF
  exact locFam_of (smoothFam_congr ⟨a, ha, hFa⟩ h) a
    (fun z => (jet_congr (h z)).trans (hFa z).2) hla

theorem locFam_clm (hr : 1 ≤ r) {n : ℕ} (A : E →L[ℝ] CrForms r m n)
    (hA : ∀ lam ε v, 0 < ε → ε ≤ 1 →
      ‖Wj lam ε (A v : Jet r m × Jet r m).1‖ ≤ Q1 lam ε v ∧
      ‖Wj lam ε (A v : Jet r m × Jet r m).2‖ ≤ Q1 lam ε v + Q2 lam ε v) :
    LocFam Q1 Q2 r n (fun z => wRep hr (A z)) :=
  ⟨A, A.contDiff, fun z => wRep_spec hr (A z), fun x => ⟨1, zero_le_one, fun lam ε v h0 h1 => by
    rw [A.fderiv]
    simpa only [one_mul] using hA lam ε v h0 h1⟩⟩

end IntLInfty.Kan.A83Loc

namespace IntLInfty.Kan.A83Loc

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83Wedge IntLInfty.Kan.A83Proj IntLInfty.Kan.A83W IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83G IntLInfty.Kan.A83IntegK
open scoped ContDiff

section Sum

variable {m r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q1 Q2 : ℝ → ℝ → E → ℝ}

def LocSumFam (Q1 Q2 : ℝ → ℝ → E → ℝ) (r : ℕ) (F : E → Ω m) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (deg : ι → ℕ) (G : ι → E → Ω m),
    (∀ i, LocFam Q1 Q2 r (deg i) (G i)) ∧ ∀ z, F z = ∑ i, G i z

theorem locSumFam_of_locFam {n : ℕ} {F : E → Ω m} (h : LocFam Q1 Q2 r n F) :
    LocSumFam Q1 Q2 r F :=
  ⟨Unit, inferInstance, fun _ => n, fun _ => F, fun _ => h, fun z => by simp⟩

theorem locSumFam_add {F G : E → Ω m} (hF : LocSumFam Q1 Q2 r F) (hG : LocSumFam Q1 Q2 r G) :
    LocSumFam Q1 Q2 r (fun z => F z + G z) := by
  obtain ⟨ι, _, d, F', hF', eF⟩ := hF
  obtain ⟨κ, _, d', G', hG', eG⟩ := hG
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim d d', Sum.elim F' G', ?_, fun z => ?_⟩
  · rintro (i | k)
    · exact hF' i
    · exact hG' k
  · show F z + G z = _
    rw [Fintype.sum_sum_type, eF z, eG z]
    rfl

theorem locSumFam_mul (hr : 1 ≤ r) (hQ : ∀ lam ε v, 0 ≤ Q1 lam ε v ∧ 0 ≤ Q2 lam ε v)
    {F G : E → Ω m} (hF : LocSumFam Q1 Q2 r F) (hG : LocSumFam Q1 Q2 r G) :
    LocSumFam Q1 Q2 r (fun z => F z * G z) := by
  obtain ⟨ι, _, d, F', hF', eF⟩ := hF
  obtain ⟨κ, _, d', G', hG', eG⟩ := hG
  refine ⟨ι × κ, inferInstance, fun s => d s.1 + d' s.2, fun s z => F' s.1 z * G' s.2 z,
    fun s => locFam_mul hr hQ (hF' s.1) (hG' s.2), fun z => ?_⟩
  simp only [eF z, eG z, Fintype.sum_mul_sum, Fintype.sum_prod_type]

theorem locFam_of_locSumFam (hr : 1 ≤ r) {n : ℕ} {F : E → Ω m} (hF : LocSumFam Q1 Q2 r F)
    (hd : ∀ z, IsDeg n (F z)) : LocFam Q1 Q2 r n F := by
  classical
  obtain ⟨ι, _, d, G, hG, eF⟩ := hF
  have hsm : LocFam Q1 Q2 r n
      (fun z => ∑ i ∈ Finset.univ.filter (fun i => d i = n), G i z) := by
    apply locFam_sum hr
    intro i hi
    have hi' : d i = n := (Finset.mem_filter.1 hi).2
    rw [← hi']
    exact hG i
  refine locFam_congr hsm fun z x hx => ?_
  show F z x = (∑ i ∈ Finset.univ.filter (fun i => d i = n), G i z) x
  rw [Finset.sum_apply]
  refine graded_extract d (F z x) (hd z x hx) (fun i => G i z x)
    (fun i => ?_) ?_
  · obtain ⟨_, _, hGa, _⟩ := hG i
    exact (hGa z).1.1 x hx
  · rw [eF z, Finset.sum_apply]

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem locSumFam_ceLift (hr : 1 ≤ r) (hQ : ∀ lam ε v, 0 ≤ Q1 lam ε v ∧ 0 ≤ Q2 lam ε v)
    (S : GenSys L) (f : E → ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : ∀ z, GenHom (f z))
    (hgen : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
      LocFam Q1 Q2 r (i + 1) (fun z => f z i ξ))
    (x : CE L) (hx : x ∈ genAlg L S) : LocSumFam Q1 Q2 r (fun z => ceLift (f z) (hf z) x) := by
  unfold genAlg at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, ξ, hξ, rfl⟩ := Set.mem_iUnion.1 hy
    simp only [ceLift_gen]
    exact locSumFam_of_locFam (hgen i ξ hξ)
  | algebraMap c =>
    simp only [AlgHom.commutes]
    exact locSumFam_of_locFam (locFam_const hr ⟨isDeg_algebraMap c, isCr_algebraMap c⟩)
  | add x y _ _ hx hy =>
    simp only [map_add]
    exact locSumFam_add hx hy
  | mul x y _ _ hx hy =>
    simp only [map_mul]
    exact locSumFam_mul hr hQ hx hy

theorem locFam_ceLift (hr : 1 ≤ r) (hQ : ∀ lam ε v, 0 ≤ Q1 lam ε v ∧ 0 ≤ Q2 lam ε v)
    (S : GenSys L) (f : E → ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m) (hf : ∀ z, GenHom (f z))
    (hgen : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
      LocFam Q1 Q2 r (i + 1) (fun z => f z i ξ))
    {n : ℕ} (x : CE L) (hx : x ∈ genAlg L S) (hd : ∀ z, IsDeg n (ceLift (f z) (hf z) x)) :
    LocFam Q1 Q2 r n (fun z => ceLift (f z) (hf z) x) :=
  locFam_of_locSumFam hr (locSumFam_ceLift hr hQ S f hf hgen x hx) hd

end Sum

section AmbLoc

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

noncomputable def QA1 (S : GenSys L) (lam ε : ℝ) (v : Amb r S m) : ℝ :=
  ∑ t : Fin m, ∑ k : Fin (Module.finrank ℝ (S t)), ‖Wj lam ε (v t k : Jet r m × Jet r m).1‖

noncomputable def QA2 (S : GenSys L) (lam ε : ℝ) (v : Amb r S m) : ℝ :=
  ∑ t : Fin m, ∑ k : Fin (Module.finrank ℝ (S t)), ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖

theorem QA_nonneg (S : GenSys L) (lam ε : ℝ) (v : Amb r S m) :
    0 ≤ QA1 S lam ε v ∧ 0 ≤ QA2 S lam ε v :=
  ⟨Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _,
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _⟩

theorem le_QA1 (S : GenSys L) (lam ε : ℝ) (v : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    ‖Wj lam ε (v t k : Jet r m × Jet r m).1‖ ≤ QA1 S lam ε v := by
  unfold QA1
  calc ‖Wj lam ε (v t k : Jet r m × Jet r m).1‖
      ≤ ∑ k' : Fin (Module.finrank ℝ (S t)), ‖Wj lam ε (v t k' : Jet r m × Jet r m).1‖ :=
        Finset.single_le_sum
          (f := fun k' : Fin (Module.finrank ℝ (S t)) => ‖Wj lam ε (v t k' : Jet r m × Jet r m).1‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ t' : Fin m, ∑ k' : Fin (Module.finrank ℝ (S t')),
          ‖Wj lam ε (v t' k' : Jet r m × Jet r m).1‖ :=
        Finset.single_le_sum (f := fun t' : Fin m => ∑ k' : Fin (Module.finrank ℝ (S t')),
            ‖Wj lam ε (v t' k' : Jet r m × Jet r m).1‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ t)

theorem le_QA2 (S : GenSys L) (lam ε : ℝ) (v : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖ ≤ QA2 S lam ε v := by
  unfold QA2
  calc ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖
      ≤ ∑ k' : Fin (Module.finrank ℝ (S t)), ‖Wj lam ε (v t k' : Jet r m × Jet r m).2‖ :=
        Finset.single_le_sum
          (f := fun k' : Fin (Module.finrank ℝ (S t)) => ‖Wj lam ε (v t k' : Jet r m × Jet r m).2‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ k)
    _ ≤ ∑ t' : Fin m, ∑ k' : Fin (Module.finrank ℝ (S t')),
          ‖Wj lam ε (v t' k' : Jet r m × Jet r m).2‖ :=
        Finset.single_le_sum (f := fun t' : Fin m => ∑ k' : Fin (Module.finrank ℝ (S t')),
            ‖Wj lam ε (v t' k' : Jet r m × Jet r m).2‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ t)

noncomputable def coordL (S : GenSys L) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    Amb r S m →L[ℝ] CrForms r m (t + 1) :=
  (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (Module.finrank ℝ (S t)) => CrForms r m (t + 1)) k).comp
    (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun t : Fin m => Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1)) t)

theorem locFam_genVal (hr : 1 ≤ r) (S : GenSys L) (i : ℕ) (ξ : Module.Dual ℝ (L i)) :
    LocFam (QA1 S) (QA2 S) r (i + 1) (fun z : Amb r S m => genVal hr S z i ξ) := by
  by_cases h : i < m
  · have hs : LocFam (QA1 S) (QA2 S) r (i + 1) (fun z : Amb r S m =>
        ∑ k : Fin (Module.finrank ℝ (S i)),
          (genBasis S i).repr (retr S i ξ) k • wRep hr (z ⟨i, h⟩ k)) :=
      locFam_sum hr _ fun k _ => locFam_smul hr _
        (locFam_clm hr (coordL S ⟨i, h⟩ k) fun lam ε v _ _ =>
          ⟨le_QA1 S lam ε v ⟨i, h⟩ k,
            (le_QA2 S lam ε v ⟨i, h⟩ k).trans (le_add_of_nonneg_left (QA_nonneg S lam ε v).1)⟩)
    refine locFam_congr hs fun z x hx => ?_
    show cutL (rawVal hr S z i ξ) x = _
    rw [cutL_eqOn _ x hx, rawVal_lt hr S z h]
  · refine locFam_congr (locFam_zero hr (i + 1)) fun z x hx => ?_
    show cutL (rawVal hr S z i ξ) x = _
    rw [cutL_eqOn _ x hx, rawVal_ge hr S z h]

theorem locFam_eval (hr : 1 ≤ r) (S : GenSys L) {n : ℕ} (x : CE L) (hx : x ∈ genAlg L S)
    (hd : ∀ z : Amb r S m, IsDeg n (ceLift (genVal hr S z) (genHom_genVal hr S z) x)) :
    LocFam (QA1 S) (QA2 S) r n
      (fun z : Amb r S m => ceLift (genVal hr S z) (genHom_genVal hr S z) x) :=
  locFam_ceLift hr (QA_nonneg S) S (fun z => genVal hr S z) (fun z => genHom_genVal hr S z)
    (fun i ξ _ => locFam_genVal hr S i ξ) x hx hd

theorem loc_Gfam (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    Loc (QA1 S) (QA2 S) (Gfam hr δ S hcl t k) := by
  obtain ⟨a, _, hFa, hl⟩ := locFam_eval (m := m) hr S _ (hcl _ _ (genBasis S t k).2)
    (fun z y _ => ceLift_mem_deg _ _ (δ.deg _ _ (A83DGA.gen_mem_ceDeg _ _)) y)
    (n := (t : ℕ) + 1 + 1)
  have e : Gfam hr δ S hcl t k = a := funext fun z => Subtype.ext
    ((((smoothFam_defect hr δ S hcl t k).choose_spec.2 z).2).symm.trans (hFa z).2)
  rw [e]
  exact hl

end AmbLoc

end IntLInfty.Kan.A83Loc

namespace IntLInfty.Kan.A83H2

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83H IntLInfty.Kan.A83W
  IntLInfty.Kan.A83E IntLInfty.Kan.A83G1 IntLInfty.Kan.A83Loc
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

noncomputable def sK (m r : ℕ) (lam ε : ℝ) : ℝ := ‖cB m‖ * (((m : ℝ) + 1) ^ r * (1 / lam + r * ε))

theorem sK_nonneg {lam ε : ℝ} (hl : 0 < lam) (hε : 0 ≤ ε) : 0 ≤ sK m r lam ε :=
  mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (mul_nonneg (by positivity)
    (add_nonneg (one_div_nonneg.2 hl.le) (mul_nonneg (Nat.cast_nonneg r) hε)))

theorem cdo {om : Ω m} (h : IsCr r om) : ContDiffOn ℝ r om (simplex m) :=
  contDiffOn_of_coeff fun I => (h I).1

theorem kop_iter_w {lam ε : ℝ} (hl : 0 < lam) (hε0 : 0 < ε) {n : ℕ} {β : Ω m}
    (hβ : ContDiffOn ℝ r β (simplex m)) {k : ℕ} (hk : k ≤ r) {y : Fin m → ℝ}
    (hy : y ∈ simplex m) :
    ε ^ k * (Real.exp (-(lam * ‖y‖)) * ‖iteratedFDerivWithin ℝ k (Kop n β) (simplex m) y‖) ≤
      sK m r lam ε * ‖Wj lam ε (jet r β).1‖ := by
  have hA : 0 ≤ ‖Wj lam ε (jet r β).1‖ := norm_nonneg _
  have hD : ∀ i ≤ r, ∀ z ∈ simplex m, ε ^ i * (Real.exp (-(lam * ‖z‖)) *
      ‖iteratedFDerivWithin ℝ i β (simplex m) z‖) ≤ (m : ℝ) ^ i * ‖Wj lam ε (jet r β).1‖ := by
    intro i hi z hz
    have h := scaled_iter_le hβ hi ⟨z, hz⟩ (c := ε ^ i * Real.exp (-(lam * ‖z‖)))
      (B := ‖Wj lam ε (jet r β).1‖) (mul_pos (pow_pos hε0 i) (Real.exp_pos _)) hA
      (fun I β' => wcomp_le β hε0.le hi ⟨z, hz⟩ I β')
    calc _ = (ε ^ i * Real.exp (-(lam * ‖z‖))) *
          ‖iteratedFDerivWithin ℝ i β (simplex m) z‖ := by ring
      _ ≤ _ := h
  have hB : 0 ≤ ‖cB m‖ := ContinuousLinearMap.opNorm_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hP1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ r := one_le_pow₀ (by linarith)
  have hr0 : (0 : ℝ) ≤ (r : ℝ) * ε := mul_nonneg (Nat.cast_nonneg r) hε0.le
  unfold sK
  rcases k with _ | j
  · have hK := Kop_wbound (n := n) hl (Nat.zero_le r) hβ (M := ‖Wj lam ε (jet r β).1‖)
      (M' := ‖Wj lam ε (jet r β).1‖)
      (fun z hz => by have := hD 0 (Nat.zero_le r) z hz; simpa using this)
      (fun z hz => by have := hD 0 (Nat.zero_le r) z hz; simpa using this) hy
    simp only [pow_zero, one_mul, Nat.cast_zero, zero_mul, add_zero] at hK ⊢
    refine hK.trans ?_
    have h3 : 1 / lam ≤ ((m : ℝ) + 1) ^ r * (1 / lam + r * ε) := by
      have : 0 < 1 / lam := one_div_pos.2 hl
      nlinarith
    have h2 : ‖Wj lam ε (jet r β).1‖ / lam ≤
        ((m : ℝ) + 1) ^ r * (1 / lam + r * ε) * ‖Wj lam ε (jet r β).1‖ := by
      calc ‖Wj lam ε (jet r β).1‖ / lam = 1 / lam * ‖Wj lam ε (jet r β).1‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right h3 hA
    calc ‖cB m‖ * (‖Wj lam ε (jet r β).1‖ / lam)
        ≤ ‖cB m‖ * (((m : ℝ) + 1) ^ r * (1 / lam + r * ε) * ‖Wj lam ε (jet r β).1‖) :=
          mul_le_mul_of_nonneg_left h2 hB
      _ = _ := by ring
  · have hεj : 0 < ε ^ j := pow_pos hε0 j
    have hεj1 : 0 < ε ^ (j + 1) := pow_pos hε0 (j + 1)
    have hK := Kop_wbound (n := n) hl hk hβ
      (M := (m : ℝ) ^ (j + 1) * ‖Wj lam ε (jet r β).1‖ / ε ^ (j + 1))
      (M' := (m : ℝ) ^ j * ‖Wj lam ε (jet r β).1‖ / ε ^ j)
      (fun z hz => by
        rw [le_div_iff₀ hεj1]
        have := hD (j + 1) hk z hz
        linarith [this])
      (fun z hz => by
        rw [Nat.add_sub_cancel, le_div_iff₀ hεj]
        have := hD j (by omega) z hz
        linarith [this]) hy
    have hj' : ((j + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hk
    have p1 : (m : ℝ) ^ (j + 1) ≤ ((m : ℝ) + 1) ^ r :=
      (pow_le_pow_left₀ hm (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hk)
    have p2 : (m : ℝ) ^ j ≤ ((m : ℝ) + 1) ^ r :=
      (pow_le_pow_left₀ hm (by linarith) _).trans (pow_le_pow_right₀ (by linarith) (by omega))
    have p3 : ((j + 1 : ℕ) : ℝ) * (m : ℝ) ^ j ≤ r * ((m : ℝ) + 1) ^ r :=
      mul_le_mul hj' p2 (by positivity) (Nat.cast_nonneg r)
    have e1 : ε ^ (j + 1) * (‖cB m‖ * ((m : ℝ) ^ (j + 1) * ‖Wj lam ε (jet r β).1‖ / ε ^ (j + 1) /
        lam + ((j + 1 : ℕ) : ℝ) * ((m : ℝ) ^ j * ‖Wj lam ε (jet r β).1‖ / ε ^ j))) =
        ‖cB m‖ * ((m : ℝ) ^ (j + 1) * ‖Wj lam ε (jet r β).1‖ / lam +
          (((j + 1 : ℕ) : ℝ) * (m : ℝ) ^ j) * (ε * ‖Wj lam ε (jet r β).1‖)) := by
      have h1 : ε ^ (j + 1) = ε ^ j * ε := pow_succ ε j
      have hne : ε ^ j ≠ 0 := hεj.ne'
      have hne1 : ε ^ (j + 1) ≠ 0 := hεj1.ne'
      have hl' : lam ≠ 0 := hl.ne'
      field_simp
      rw [h1]
      ring
    calc ε ^ (j + 1) * (Real.exp (-(lam * ‖y‖)) *
          ‖iteratedFDerivWithin ℝ (j + 1) (Kop n β) (simplex m) y‖)
        ≤ ε ^ (j + 1) * (‖cB m‖ * ((m : ℝ) ^ (j + 1) * ‖Wj lam ε (jet r β).1‖ / ε ^ (j + 1) /
          lam + ((j + 1 : ℕ) : ℝ) * ((m : ℝ) ^ j * ‖Wj lam ε (jet r β).1‖ / ε ^ j))) :=
          mul_le_mul_of_nonneg_left hK hεj1.le
      _ = _ := e1
      _ ≤ ‖cB m‖ * (((m : ℝ) + 1) ^ r * ‖Wj lam ε (jet r β).1‖ / lam +
          (r * ((m : ℝ) + 1) ^ r) * (ε * ‖Wj lam ε (jet r β).1‖)) := by
          apply mul_le_mul_of_nonneg_left _ hB
          apply add_le_add
          · exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right p1 hA) hl.le
          · exact mul_le_mul_of_nonneg_right p3 (mul_nonneg hε0.le hA)
      _ = ‖cB m‖ * (((m : ℝ) + 1) ^ r * (1 / lam + r * ε)) * ‖Wj lam ε (jet r β).1‖ := by ring

theorem Wj_Kop_le {lam ε : ℝ} (hl : 0 < lam) (hε0 : 0 < ε) {n : ℕ} {β : Ω m}
    (hβ : ContDiffOn ℝ r β (simplex m)) (hKβ : ContDiffOn ℝ r (Kop n β) (simplex m)) :
    ‖Wj lam ε (jet r (Kop n β)).1‖ ≤ sK m r lam ε * ‖Wj lam ε (jet r β).1‖ := by
  refine jet_norm_le (mul_nonneg (sK_nonneg hl hε0.le) (norm_nonneg _)) fun I k β' y => ?_
  have hk : (k : ℕ) ≤ r := Nat.lt_succ_iff.mp k.2
  rw [Wj_apply]
  have e0 := (Real.exp_pos (-(lam * ‖(y : Fin m → ℝ)‖))).le
  have hJ : |(jet r (Kop n β)).1 I k β' y| ≤
      ‖iteratedFDerivWithin ℝ k (Kop n β) (simplex m) y‖ := abs_jetComp_coeff_le hKβ hk I β' y
  calc |ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) * (jet r (Kop n β)).1 I k β' y)|
      = ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) *
          |(jet r (Kop n β)).1 I k β' y|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hε0.le _), abs_of_nonneg e0]
    _ ≤ ε ^ (k : ℕ) * (Real.exp (-(lam * ‖(y : Fin m → ℝ)‖)) *
          ‖iteratedFDerivWithin ℝ k (Kop n β) (simplex m) y‖) := by gcongr
    _ ≤ _ := kop_iter_w hl hε0 hβ hk y.2

theorem extD_Kop_eqOn (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    FormEqOn (extD (Kop n β)) (β + ((-1 : ℝ)) • Kop (n + 1) (extD β)) := by
  intro x hx
  have h := Kop_hom hr hC hD x hx
  show extD (Kop n β) x = β x + ((-1 : ℝ)) • Kop (n + 1) (extD β) x
  rw [← h, neg_one_smul, add_neg_cancel_right]

theorem jet_snd_eq (om : Ω m) : (jet r om).2 = (jet r (extD om)).1 := rfl

theorem jet_Kop_snd (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    (jet r (Kop n β)).2 = (jet r β).1 + ((-1 : ℝ)) • (jet r (Kop (n + 1) (extD β))).1 := by
  have hKdC : IsCr r (Kop (n + 1) (extD β)) := isCr_Kop hr (isCr_extD hr hC) (isDeg_extD hr hC hD)
  rw [jet_snd_eq, jet_congr (extD_Kop_eqOn hr hC hD), jet_add hr hC (isCr_smul hr _ hKdC),
    jet_smul hr _ hKdC] <;> rfl

theorem Wj_sub1_le {lam ε : ℝ} (a b : Jet r m) :
    ‖Wj lam ε (a + ((-1 : ℝ)) • b)‖ ≤ ‖Wj lam ε a‖ + ‖Wj lam ε b‖ := by
  have h := Wj_add_smul_le (lam := lam) (ε := ε) a b (-1)
  rwa [abs_neg, abs_one, one_mul] at h

theorem Wj_Kop_snd_aux {lam ε : ℝ} {a b c : Jet r m} {s : ℝ}
    (h : ‖Wj lam ε b‖ ≤ s * ‖Wj lam ε c‖) :
    ‖Wj lam ε (a + ((-1 : ℝ)) • b)‖ ≤ ‖Wj lam ε a‖ + s * ‖Wj lam ε c‖ :=
  (Wj_sub1_le a b).trans (add_le_add le_rfl h)

theorem Wj_Kop_snd_le (hr : 1 ≤ r) {lam ε : ℝ} (hl : 0 < lam) (hε0 : 0 < ε) {n : ℕ} {β : Ω m}
    (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    ‖Wj lam ε (jet r (Kop n β)).2‖ ≤
      ‖Wj lam ε (jet r β).1‖ + sK m r lam ε * ‖Wj lam ε (jet r β).2‖ := by
  have hdC := isCr_extD hr hC
  have hKdC : IsCr r (Kop (n + 1) (extD β)) := isCr_Kop hr hdC (isDeg_extD hr hC hD)
  have h := Wj_Kop_le (n := n + 1) hl hε0 (cdo hdC) (cdo hKdC)
  rw [jet_Kop_snd hr hC hD, jet_snd_eq β]
  exact Wj_Kop_snd_aux h

theorem KCLM_W1 (hr : 1 ≤ r) {lam ε : ℝ} (hl : 0 < lam) (hε0 : 0 < ε) {n : ℕ}
    (w : CrForms r m (n + 1)) :
    ‖Wj lam ε (KCLM hr n w : Jet r m × Jet r m).1‖ ≤
      sK m r lam ε * ‖Wj lam ε (w : Jet r m × Jet r m).1‖ := by
  obtain ⟨om, hom, hw⟩ := exists_rep hr w
  have hv : (KCLM hr n w : Jet r m × Jet r m) = jet r (Kop n om) := KLin_val hr w hom.2 hw
  rw [hv, ← hw]
  exact Wj_Kop_le hl hε0 (cdo hom.2) (cdo (isCr_Kop hr hom.2 hom.1))

theorem KCLM_W2 (hr : 1 ≤ r) {lam ε : ℝ} (hl : 0 < lam) (hε0 : 0 < ε) {n : ℕ}
    (w : CrForms r m (n + 1)) :
    ‖Wj lam ε (KCLM hr n w : Jet r m × Jet r m).2‖ ≤
      ‖Wj lam ε (w : Jet r m × Jet r m).1‖ + sK m r lam ε * ‖Wj lam ε (w : Jet r m × Jet r m).2‖ := by
  obtain ⟨om, hom, hw⟩ := exists_rep hr w
  have hv : (KCLM hr n w : Jet r m × Jet r m) = jet r (Kop n om) := KLin_val hr w hom.2 hw
  rw [hv, ← hw]
  exact Wj_Kop_snd_le hr hl hε0 hom.2 hom.1

section AmbH

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem fderiv_Gmap (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (x v : Amb r S m) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    fderiv ℝ (Gmap hr δ S hcl) x v t k =
      KCLM hr ((t : ℕ) + 1) (fderiv ℝ (Gfam hr δ S hcl t k) x v) := by
  have hG : HasFDerivAt (Gmap hr δ S hcl) (fderiv ℝ (Gmap hr δ S hcl) x) x :=
    ((Gmap_contDiff hr δ S hcl).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hF : HasFDerivAt (Gfam hr δ S hcl t k) (fderiv ℝ (Gfam hr δ S hcl t k) x) x :=
    (((smoothFam_defect hr δ S hcl t k).choose_spec.1).differentiable
      (by simp)).differentiableAt.hasFDerivAt
  have h1 := (coordL S t k).hasFDerivAt.comp x hG
  have h2 := (KCLM hr ((t : ℕ) + 1)).hasFDerivAt.comp x hF
  have e : (coordL S t k) ∘ (Gmap hr δ S hcl) = (KCLM hr ((t : ℕ) + 1)) ∘ (Gfam hr δ S hcl t k) :=
    funext fun z => rfl
  rw [e] at h1
  have h3 := h1.unique h2
  exact congrArg (fun A : Amb r S m →L[ℝ] CrForms r m ((t : ℕ) + 1) => A v) h3

end AmbH

end IntLInfty.Kan.A83H2

namespace IntLInfty.Kan.A83H3

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83H IntLInfty.Kan.A83W
  IntLInfty.Kan.A83G1 IntLInfty.Kan.A83Loc IntLInfty.Kan.A83H2
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

theorem exists_lam_eps {Q σ : ℝ} (hQ : 0 ≤ Q) (hσ : 0 < σ) (r : ℕ) :
    ∃ lam ε : ℝ, 0 < lam ∧ 0 < ε ∧ ε ≤ 1 ∧ Q * (1 / lam + r * ε) ≤ σ := by
  set P := Q + 1 with hP
  have hP0 : 0 < P := by linarith
  have hr1 : (0 : ℝ) < r + 1 := by positivity
  have hq : 0 < σ / (2 * P * (r + 1)) := by positivity
  refine ⟨2 * P / σ, min 1 (σ / (2 * P * (r + 1))), by positivity, lt_min one_pos hq,
    min_le_left _ _, ?_⟩
  have h1 : 1 / (2 * P / σ) = σ / (2 * P) := by
    rw [one_div_div]
  have h2 : (r : ℝ) * min 1 (σ / (2 * P * (r + 1))) ≤ σ / (2 * P) := by
    calc (r : ℝ) * min 1 (σ / (2 * P * (r + 1))) ≤ r * (σ / (2 * P * (r + 1))) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg r)
      _ = σ / (2 * P) * (r / (r + 1)) := by
          rw [mul_div_assoc', div_mul_div_comm, mul_comm (r : ℝ) σ]
      _ ≤ σ / (2 * P) * 1 :=
          mul_le_mul_of_nonneg_left ((div_le_one hr1).2 (by linarith)) (by positivity)
      _ = σ / (2 * P) := mul_one _
  rw [h1]
  have h4 : σ / (2 * P) + σ / (2 * P) = σ / P := by
    rw [← add_div, div_eq_div_iff (by positivity) hP0.ne']
    ring
  have h3 : σ / (2 * P) + r * min 1 (σ / (2 * P * (r + 1))) ≤ σ / P := by linarith
  calc Q * (σ / (2 * P) + r * min 1 (σ / (2 * P * (r + 1)))) ≤ Q * (σ / P) :=
        mul_le_mul_of_nonneg_left h3 hQ
    _ ≤ P * (σ / P) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = σ := mul_div_cancel₀ σ hP0.ne'

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

noncomputable def TW (S : GenSys L) (lam ε η : ℝ) (v : Amb r S m) :
    (t : Fin m) → (Fin (Module.finrank ℝ (S t)) → Jet r m × Jet r m) :=
  fun t k => (Wj lam ε (v t k : Jet r m × Jet r m).1, η • Wj lam ε (v t k : Jet r m × Jet r m).2)

theorem TW_fst_le (S : GenSys L) (lam ε η : ℝ) (v : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    ‖Wj lam ε (v t k : Jet r m × Jet r m).1‖ ≤ ‖TW S lam ε η v‖ :=
  (norm_fst_le (TW S lam ε η v t k)).trans
    ((norm_le_pi_norm (TW S lam ε η v t) k).trans (norm_le_pi_norm (TW S lam ε η v) t))

theorem TW_snd_le (S : GenSys L) (lam ε : ℝ) {η : ℝ} (hη : 0 ≤ η) (v : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) :
    η * ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖ ≤ ‖TW S lam ε η v‖ := by
  have h := (norm_snd_le (TW S lam ε η v t k)).trans
    ((norm_le_pi_norm (TW S lam ε η v t) k).trans (norm_le_pi_norm (TW S lam ε η v) t))
  have e : ‖(TW S lam ε η v t k).2‖ = η * ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖ := by
    show ‖η • Wj lam ε (v t k : Jet r m × Jet r m).2‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη]
  rw [e] at h
  exact h

noncomputable def NA (S : GenSys L) (m : ℕ) : ℝ :=
  ∑ t : Fin m, ∑ _k : Fin (Module.finrank ℝ (S t)), (1 : ℝ)

theorem NA_nonneg (S : GenSys L) : 0 ≤ NA S m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one

theorem QA1_le (S : GenSys L) (lam ε η : ℝ) (v : Amb r S m) :
    QA1 S lam ε v ≤ NA S m * ‖TW S lam ε η v‖ := by
  unfold QA1 NA
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun k _ => by rw [one_mul]; exact TW_fst_le S lam ε η v t k

theorem QA2_le (S : GenSys L) (lam ε : ℝ) {η : ℝ} (hη : 0 ≤ η) (v : Amb r S m) :
    η * QA2 S lam ε v ≤ NA S m * ‖TW S lam ε η v‖ := by
  unfold QA2 NA
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => by rw [one_mul]; exact TW_snd_le S lam ε hη v t k

theorem norm_amb_le (S : GenSys L) (v : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) : ‖(v t k : Jet r m × Jet r m)‖ ≤ ‖v‖ :=
  (norm_le_pi_norm (v t) k).trans
    (norm_le_pi_norm (v : (t : Fin m) → (Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1))) t)

theorem amb_norm_le (S : GenSys L) (v : Amb r S m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t k, ‖(v t k : Jet r m × Jet r m)‖ ≤ C) : ‖v‖ ≤ C := by
  show ‖(v : (t : Fin m) → (Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1)))‖ ≤ C
  exact (pi_norm_le_iff_of_nonneg hC).2 fun t => (pi_norm_le_iff_of_nonneg hC).2 fun k => h t k

theorem TW_norm_le (S : GenSys L) (lam ε η : ℝ) (v : Amb r S m) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t k, ‖Wj lam ε (v t k : Jet r m × Jet r m).1‖ ≤ C ∧
      ‖η • Wj lam ε (v t k : Jet r m × Jet r m).2‖ ≤ C) : ‖TW S lam ε η v‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).2 fun t => (pi_norm_le_iff_of_nonneg hC).2 fun k =>
    norm_prod_le_iff.2 (h t k)

theorem hV_holds (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (x : Amb r S m) : ∃ n : ℕ, ‖(fderiv ℝ (Gmap (m := m) hr δ S hcl) x) ^ n‖ < 1 := by
  have hloc := fun (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) =>
    loc_Gfam hr δ S hcl t k x
  choose C hC0 hC using hloc
  set Cs : ℝ := ∑ t : Fin m, ∑ k : Fin (Module.finrank ℝ (S t)), C t k with hCs
  have hCs0 : 0 ≤ Cs := Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun k _ => hC0 t k
  have hCle : ∀ t k, C t k ≤ Cs := fun t k =>
    (Finset.single_le_sum (f := fun k' => C t k') (fun k' _ => hC0 t k')
      (Finset.mem_univ k)).trans
    (Finset.single_le_sum (f := fun t' : Fin m => ∑ k' : Fin (Module.finrank ℝ (S t')), C t' k')
      (fun (t' : Fin m) _ => Finset.sum_nonneg fun k' _ => hC0 t' k') (Finset.mem_univ t))
  set N := NA S m with hN
  have hN0 : 0 ≤ N := NA_nonneg S
  set D := Cs * N + 1 with hD
  have hCN : 0 ≤ Cs * N := mul_nonneg hCs0 hN0
  have hD1 : 1 ≤ D := by linarith
  set σ := 1 / (4 * D) with hσ
  have hσ0 : 0 < σ := by rw [hσ]; exact one_div_pos.2 (by linarith)
  have hσD : σ * D = 1 / 4 := by
    rw [hσ, div_mul_eq_mul_div, one_mul, div_eq_div_iff (by linarith : (0:ℝ) < 4 * D).ne' (by norm_num)]
    ring
  have hσ1 : σ ≤ 1 := by have := mul_le_mul_of_nonneg_left hD1 hσ0.le; linarith
  have hQ : 0 ≤ ‖cB m‖ * ((m : ℝ) + 1) ^ r :=
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) (by positivity)
  obtain ⟨lam, ε, hl, hε0, hε1, hs⟩ := exists_lam_eps hQ hσ0 r
  set s := sK m r lam ε with hsdef
  have hs0 : 0 ≤ s := sK_nonneg hl hε0.le
  have hsσ : s ≤ σ := by
    have e : s = ‖cB m‖ * ((m : ℝ) + 1) ^ r * (1 / lam + r * ε) := by
      rw [hsdef]; unfold sK; ring
    rw [e]; exact hs
  have hσle : 0 ≤ σ := hσ0.le
  set θ := s * Cs * N + σ * Cs * (1 + s) * N with hθ
  have hθ0 : 0 ≤ θ := by
    have := mul_nonneg (mul_nonneg hs0 hCs0) hN0
    have := mul_nonneg (mul_nonneg (mul_nonneg hσle hCs0) (by linarith : (0 : ℝ) ≤ 1 + s)) hN0
    linarith
  have hθ1 : θ < 1 := by
    have e : θ = (s + σ * (1 + s)) * (Cs * N) := by rw [hθ]; ring
    have h1 : s + σ * (1 + s) ≤ σ + σ * 2 := by
      have : σ * s ≤ σ * 1 := mul_le_mul_of_nonneg_left (hsσ.trans hσ1) hσ0.le
      linarith
    have h2 : (s + σ * (1 + s)) * (Cs * N) ≤ (σ + σ * 2) * D :=
      mul_le_mul h1 (by linarith) hCN (by linarith)
    have h3 : (σ + σ * 2) * D = 3 / 4 := by
      rw [show (σ + σ * 2) * D = 3 * (σ * D) by ring, hσD]; norm_num
    linarith
  set V := fderiv ℝ (Gmap (m := m) hr δ S hcl) x with hV
  set c0 := (ε ^ r)⁻¹ * Real.exp lam with hc0
  have hc00 : 0 ≤ c0 := mul_nonneg (inv_nonneg.2 (pow_nonneg hε0.le r)) (Real.exp_pos lam).le
  refine exists_pow_norm_lt_one V (TW S lam ε σ) (a := c0 * (1 + σ⁻¹)) (b := 1)
    (mul_nonneg hc00 (by have := inv_nonneg.2 hσle; linarith)) zero_le_one hθ0 hθ1 ?_ ?_ ?_
  ·
    intro v
    have hX := norm_nonneg (TW S lam ε σ v)
    have ha1 : c0 ≤ c0 * (1 + σ⁻¹) := le_mul_of_one_le_right hc00 (by
      have : 0 ≤ σ⁻¹ := inv_nonneg.2 hσle
      linarith)
    have ha2 : c0 * σ⁻¹ ≤ c0 * (1 + σ⁻¹) := mul_le_mul_of_nonneg_left (by linarith) hc00
    refine amb_norm_le S v (mul_nonneg (mul_nonneg hc00 (by have := inv_nonneg.2 hσle; linarith)) hX) fun t k => norm_prod_le_iff.2 ⟨?_, ?_⟩
    · calc ‖(v t k : Jet r m × Jet r m).1‖ ≤ c0 * ‖Wj lam ε (v t k : Jet r m × Jet r m).1‖ :=
            norm_le_Wj hl.le hε0 hε1 _
        _ ≤ c0 * ‖TW S lam ε σ v‖ := mul_le_mul_of_nonneg_left (TW_fst_le S lam ε σ v t k) hc00
        _ ≤ c0 * (1 + σ⁻¹) * ‖TW S lam ε σ v‖ := mul_le_mul_of_nonneg_right ha1 hX
    · have h2 := TW_snd_le S lam ε hσle v t k
      have hσne : σ ≠ 0 := hσ0.ne'
      calc ‖(v t k : Jet r m × Jet r m).2‖ ≤ c0 * ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖ :=
            norm_le_Wj hl.le hε0 hε1 _
        _ = c0 * σ⁻¹ * (σ * ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖) := by
            rw [mul_assoc c0, ← mul_assoc σ⁻¹, inv_mul_cancel₀ hσne, one_mul]
        _ ≤ c0 * σ⁻¹ * ‖TW S lam ε σ v‖ :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hc00 (inv_nonneg.2 hσle))
        _ ≤ c0 * (1 + σ⁻¹) * ‖TW S lam ε σ v‖ := mul_le_mul_of_nonneg_right ha2 hX
  ·
    intro v
    rw [one_mul]
    refine TW_norm_le S lam ε σ v (norm_nonneg _) fun t k => ⟨?_, ?_⟩
    · exact (norm_Wj_le hl.le hε0.le hε1 _).trans
        ((norm_fst_le _).trans (norm_amb_le S v t k))
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσle]
      calc σ * ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖
          ≤ 1 * ‖Wj lam ε (v t k : Jet r m × Jet r m).2‖ :=
            mul_le_mul_of_nonneg_right hσ1 (norm_nonneg _)
        _ ≤ ‖v‖ := by
            rw [one_mul]
            exact (norm_Wj_le hl.le hε0.le hε1 _).trans
              ((norm_snd_le _).trans (norm_amb_le S v t k))
  ·
    intro v
    have hX := norm_nonneg (TW S lam ε σ v)
    have hQ1 := QA1_le S lam ε σ v
    have hQ2 := QA2_le S lam ε hσle v
    have hq := QA_nonneg S lam ε v
    refine TW_norm_le S lam ε σ (V v) (mul_nonneg hθ0 hX) fun t k => ?_
    obtain ⟨b1, b2⟩ := hC t k lam ε v hε0 hε1
    have hVv : V v t k = KCLM hr ((t : ℕ) + 1) (fderiv ℝ (Gfam hr δ S hcl t k) x v) :=
      fderiv_Gmap hr δ S hcl x v t k
    rw [hVv]
    have k1 := KCLM_W1 hr hl hε0 (fderiv ℝ (Gfam hr δ S hcl t k) x v)
    have k2 := KCLM_W2 hr hl hε0 (fderiv ℝ (Gfam hr δ S hcl t k) x v)
    set a1 := ‖Wj lam ε (fderiv ℝ (Gfam hr δ S hcl t k) x v : Jet r m × Jet r m).1‖
    set a2 := ‖Wj lam ε (fderiv ℝ (Gfam hr δ S hcl t k) x v : Jet r m × Jet r m).2‖
    have hCt := hCle t k
    have hCt0 := hC0 t k
    constructor
    · calc _ ≤ s * a1 := k1
        _ ≤ s * (C t k * QA1 S lam ε v) := mul_le_mul_of_nonneg_left b1 hs0
        _ ≤ s * (Cs * (N * ‖TW S lam ε σ v‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul hCt hQ1 hq.1 hCs0) hs0
        _ ≤ θ * ‖TW S lam ε σ v‖ := by
            have : 0 ≤ σ * Cs * (1 + s) * N * ‖TW S lam ε σ v‖ :=
              mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hσle hCs0) (by linarith)) hN0) hX
            rw [hθ]; linarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσle]
      calc σ * ‖Wj lam ε (KCLM hr ((t : ℕ) + 1) (fderiv ℝ (Gfam hr δ S hcl t k) x v) :
            Jet r m × Jet r m).2‖ ≤ σ * (a1 + s * a2) := mul_le_mul_of_nonneg_left k2 hσle
        _ ≤ σ * (C t k * QA1 S lam ε v + s * (C t k * (QA1 S lam ε v + QA2 S lam ε v))) :=
            mul_le_mul_of_nonneg_left (add_le_add b1 (mul_le_mul_of_nonneg_left b2 hs0)) hσle
        _ = C t k * ((σ * (1 + s)) * QA1 S lam ε v + s * (σ * QA2 S lam ε v)) := by ring
        _ ≤ Cs * ((σ * (1 + s)) * (N * ‖TW S lam ε σ v‖) + s * (N * ‖TW S lam ε σ v‖)) :=
            mul_le_mul hCt (add_le_add
              (mul_le_mul_of_nonneg_left hQ1 (mul_nonneg hσle (by linarith)))
              (mul_le_mul_of_nonneg_left hQ2 hs0))
              (add_nonneg (mul_nonneg (mul_nonneg hσle (by linarith)) hq.1)
                (mul_nonneg hs0 (mul_nonneg hσle hq.2))) hCs0
        _ = θ * ‖TW S lam ε σ v‖ := by rw [hθ]; ring

end IntLInfty.Kan.A83H3

namespace IntLInfty.Kan.A83CVtail

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83H3 IntLInfty.Kan.A83DGA
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

theorem G_eq_Gmap (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S : GenSys L)
    (hcl : (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S))
    (G : ∀ m, Amb r S m → Amb r S m)
    (hG : (∀ (m : ℕ) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I))))
     (m : ℕ) :
    G m = Gmap (m := m) hr δ S hcl := by
  funext z t k
  apply Subtype.ext
  have hφgen : ∀ i (ξ : Module.Dual ℝ (L i)),
      ceLift (genVal hr S z) (genHom_genVal hr S z) (gen L i ξ) = genVal hr S z i ξ :=
    fun i ξ => ceLift_gen _ _ i ξ
  have h1 : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
      IsDeg (i + 1) (ceLift (genVal hr S z) (genHom_genVal hr S z) (gen L i ξ)) ∧
        IsCr r (ceLift (genVal hr S z) (genHom_genVal hr S z) (gen L i ξ)) := fun i ξ _ => by
    rw [hφgen]; exact ⟨fun x _ => genHom_genVal hr S z i ξ x, isCr_genVal hr S z i ξ⟩
  have h2 : ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
      jet r (ceLift (genVal hr S z) (genHom_genVal hr S z) (gen L t (genBasis S t k))) =
        (z t k : Jet r m × Jet r m) := fun t k => by
    rw [hφgen]; exact jet_genVal_basis hr S z t k
  rw [hG m z _ h1 h2 t k, Gmap_val hr δ S hcl z t k]
  have hC := ((smoothFam_defect hr δ S hcl t k).choose_spec.2 z).1.2
  symm
  apply jet_congr
  intro y hy
  exact (C1 r hr).2.2.2.2.2.2.2.2.1 m _ _ hC y hy

theorem solution_core (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S : GenSys L)
    (hcl : (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S))
    (G : ∀ m, Amb r S m → Amb r S m)
    (hG : (∀ (m : ℕ) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I))))
    (hGc : ∀ m, ContDiff ℝ ∞ (G m)) (m : ℕ) (x : Amb r S m) :
    ∃ n : ℕ, ‖(fderiv ℝ (G m) x) ^ n‖ < 1  := by
  rw [G_eq_Gmap r hr L δ S hcl G hG m]
  exact hV_holds hr δ S hcl x

end IntLInfty.Kan.A83CVtail

open IntLInfty.Kan in
open scoped ContDiff in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) (S : GenSys L)
    (hcl : (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S))
    (G : ∀ m, Amb r S m → Amb r S m)
    (hG : (∀ (m : ℕ) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        (G m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I))))
    (hGc : ∀ m, ContDiff ℝ ∞ (G m)) (m : ℕ) (x : Amb r S m) :
    ∃ n : ℕ, ‖(fderiv ℝ (G m) x) ^ n‖ < 1 :=
  IntLInfty.Kan.A83CVtail.solution_core r hr L δ S hcl G hG hGc m x
