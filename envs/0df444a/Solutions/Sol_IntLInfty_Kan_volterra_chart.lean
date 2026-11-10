-- Prove2me | solution 1 for IntLInfty.Kan.volterra_chart
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T04:08:40.12826+00:00
-- url     : https://prove2.me/submissions/f7cbc830-5fe4-4e81-ac60-70cd29ca4647

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ
import Theorems.Thm_IntLInfty_Kan_crForms_eq_jet_image
import Theorems.Thm_IntLInfty_Kan_crForms_exterior_calculus
import Theorems.Thm_IntLInfty_Kan_generator_lift_dga
import Theorems.Thm_IntLInfty_Kan_integ_iff_generator_condition
import Theorems.Thm_IntLInfty_Kan_cone_homotopy_operator
import Theorems.Thm_IntLInfty_Kan_faceCr_continuousLinear

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

theorem extD_add :
    ∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (ω + ω') x = extD ω x + extD ω' x :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.1

theorem extD_smul :
    ∀ {m r : ℕ} (hr : 1 ≤ r) (c : ℝ) {ω : Ω m} (hω : IsCr r ω) {x : Fin m → ℝ}
      (hx : x ∈ simplex m), extD (c • ω) x = c • extD ω x :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.1

theorem isDeg_add :
    ∀ {m : ℕ} {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω'), IsDeg n (ω + ω') :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.1

theorem isDeg_smul :
    ∀ {m : ℕ} {n : ℕ} (c : ℝ) {ω : Ω m} (h : IsDeg n ω), IsDeg n (c • ω) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.1

theorem isCr_add :
    ∀ {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω'), IsCr r (ω + ω') :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.1

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

theorem formEqOn_of_jet :
    ∀ {m r : ℕ} {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω')
      (h : jet r ω = jet r ω'), FormEqOn ω ω' :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem pull_isCr :
    ∀ {m r : ℕ} (hr : 1 ≤ r) (i : Fin (m + 2)) {ω : Ω (m + 1)} (hC : IsCr r ω),
      IsCr r (pull m i ω) :=
  IntLInfty.Kan.crForms_exterior_calculus.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem exists_rep {m r : ℕ} (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) :
    ∃ ϖ : Ω m, (IsDeg n ϖ ∧ IsCr r ϖ) ∧ jet r ϖ = w := by
  have h : (w : Jet r m × Jet r m) ∈ (CrForms r m n : Set (Jet r m × Jet r m)) := w.2
  rw [crForms_eq_image hr n] at h
  obtain ⟨ϖ, hϖ, e⟩ := h
  exact ⟨ϖ, hϖ, e⟩

end IntLInfty.Kan.A83

namespace IntLInfty.Kan.A83
open IntLInfty.Kan

theorem isCr_sub {m r : ℕ} (hr : 1 ≤ r) {ω ω' : Ω m} (h : IsCr r ω) (h' : IsCr r ω') : IsCr r (ω - ω') := by
  have e : ω - ω' = ω + (-1 : ℝ) • ω' := by funext x; simp [sub_eq_add_neg]
  rw [e]; exact isCr_add hr h (isCr_smul hr _ h')

theorem isDeg_sub {m : ℕ} {n : ℕ} {ω ω' : Ω m} (h : IsDeg n ω) (h' : IsDeg n ω') : IsDeg n (ω - ω') := by
  have e : ω - ω' = ω + (-1 : ℝ) • ω' := by funext x; simp [sub_eq_add_neg]
  rw [e]; exact isDeg_add h (isDeg_smul _ h')

open BoundedContinuousFunction in
theorem jet_complete (r m : ℕ) : CompleteSpace (Jet r m × Jet r m) := by
  have : CompleteSpace (Jet r m) := inferInstanceAs (CompleteSpace ((I : Finset (Fin m)) →
    (k : Fin (r + 1)) → (Fin (k : ℕ) → Fin m) → (simplex m →ᵇ ℝ)))
  infer_instance

theorem crForms_complete (r m n : ℕ) : CompleteSpace (CrForms r m n) := by
  haveI := jet_complete r m
  exact (Submodule.isClosed_topologicalClosure _).completeSpace_coe

theorem faceCr_val {m r : ℕ} (hr : 1 ≤ r) {n : ℕ} (i : Fin (m + 2)) (w : CrForms r (m + 1) n)
    {ω : Ω (m + 1)} (hD : IsDeg n ω) (hC : IsCr r ω) (h : jet r ω = w) :
    (faceCr r m n i w : Jet r m × Jet r m) = jet r (pull m i ω) :=
  (faceCr_continuousLinear r hr n).2.2.1 m i w ω hD hC h

noncomputable def faceLin {m r : ℕ} (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) :
    CrForms r (m + 1) n →ₗ[ℝ] CrForms r m n where
  toFun := faceCr r m n i
  map_add' w w' := by
    obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr n).1 m i
    rw [← hF, ← hF, ← hF, map_add]
  map_smul' c w := by
    obtain ⟨F, hF⟩ := (faceCr_continuousLinear r hr n).1 m i
    rw [← hF, ← hF, map_smul]
    rfl

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

theorem cB_apply (m : ℕ) (x : Fin m → ℝ) (a : Alg m) :
    cB m x a = CliffordAlgebra.contractLeft (Module.Dual.eval ℝ (Fin m → ℝ) x) a := rfl

section generic

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set E}

theorem clm_coneInt_eq_zero {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (L : F →L[ℝ] G) (hconv : Convex ℝ S) (h0 : (0 : E) ∈ S) {f : E → F} (hf : ContinuousOn f S)
    (hz : ∀ y ∈ S, L (f y) = 0) (p : ℕ) {x : E} (hx : x ∈ S) : L (coneInt p f x) = 0 := by
  unfold coneInt
  rw [← L.intervalIntegral_comp_comm (intervalIntegrable_cone hconv h0 hf p hx)]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : G))]
  · simp
  · intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only
    rw [map_smul, hz _ (hconv.smul_mem_of_zero_mem h0 hx ht), smul_zero]

end generic

theorem isCompact_simplex (m : ℕ) : IsCompact (simplex m) :=
  Metric.isCompact_of_isClosed_isBounded (A83.isClosed_simplex m)
    ((Metric.isBounded_Icc (0 : Fin m → ℝ) 1).subset fun x hx =>
      ⟨fun i => hx.1 i, fun i =>
        (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2⟩)

theorem zero_mem_simplex (m : ℕ) : (0 : Fin m → ℝ) ∈ simplex m :=
  ⟨fun _ => le_refl 0, by simp⟩

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

theorem coneInt_mem_alg {m p : ℕ} {S : Set (Fin m → ℝ)} (V : Submodule ℝ (Alg m))
    (hconv : Convex ℝ S) (h0 : (0 : Fin m → ℝ) ∈ S) {f : (Fin m → ℝ) → Alg m}
    (hf : ContinuousOn f S) (hfV : ∀ y ∈ S, f y ∈ V) {x : Fin m → ℝ} (hx : x ∈ S) :
    coneInt p f x ∈ V := by
  by_contra hnot
  obtain ⟨φ, hφ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  apply hφ
  have hz := clm_coneInt_eq_zero (LinearMap.toContinuousLinearMap φ) hconv h0 hf (fun y hy => by
    have hm : φ (f y) ∈ V.map φ := Submodule.mem_map_of_mem (hfV y hy)
    rw [hmap, Submodule.mem_bot] at hm
    simpa using hm) p hx
  simpa using hz

theorem contract_mem (m : ℕ) (d : Module.Dual ℝ (Module.Dual ℝ (Fin m → ℝ))) (i : ℕ) (a : Alg m)
    (ha : a ∈ ⋀[ℝ]^i (Module.Dual ℝ (Fin m → ℝ))) :
    CliffordAlgebra.contractLeft d a ∈ ⋀[ℝ]^(i - 1) (Module.Dual ℝ (Fin m → ℝ)) ∧
      (i = 0 → CliffordAlgebra.contractLeft d a = 0) := by
  have ha' : a ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] Alg m) ^ i :=
    ha
  clear ha
  induction ha' using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [CliffordAlgebra.contractLeft_algebraMap]
    exact ⟨Submodule.zero_mem _, fun _ => rfl⟩
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact ⟨Submodule.add_mem _ hx.1 hy.1, fun h => by rw [hx.2 h, hy.2 h, add_zero]⟩
  | mem_mul m' hm i x hxi ih =>
    obtain ⟨φ, rfl⟩ := hm
    refine ⟨?_, fun h => absurd h (Nat.succ_ne_zero i)⟩
    rw [CliffordAlgebra.contractLeft_ι_mul, Nat.succ_sub_one]
    refine Submodule.sub_mem _ (Submodule.smul_mem _ _ hxi) ?_
    rcases i with _ | j
    · rw [ih.2 rfl, mul_zero]
      exact Submodule.zero_mem _
    · have h1 := ih.1
      rw [Nat.add_sub_cancel] at h1
      show _ ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] Alg m) ^ (j + 1)
      rw [pow_succ']
      exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ φ) h1

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

theorem extD_sub (hr : 1 ≤ r) {ω ω' : Ω m} (hω : IsCr r ω) (hω' : IsCr r ω') {x : Fin m → ℝ}
    (hx : x ∈ simplex m) : extD (ω - ω') x = extD ω x - extD ω' x := by
  have e : ω - ω' = ω + (-1 : ℝ) • ω' := by funext y; simp [sub_eq_add_neg]
  rw [e, extD_add hr hω (isCr_smul hr _ hω') hx, extD_smul hr _ hω' hx]
  simp [sub_eq_add_neg]

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

theorem smul_mem_simplex {y : Fin m → ℝ} (hy : y ∈ simplex m) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • y ∈ simplex m :=
  (A83.convex_simplex m).smul_mem_of_zero_mem (zero_mem_simplex m) hy ht

theorem Kop_congr (n : ℕ) {β β' : Ω m} (h : FormEqOn β β') :
    FormEqOn (Kop n β) (Kop n β') := by
  intro y hy
  simp only [Kop, coneInt]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only [h _ (smul_mem_simplex hy ht)]

theorem coneInt_add' (n : ℕ) {β β' : Ω m} (hβ : ContinuousOn β (simplex m))
    (hβ' : ContinuousOn β' (simplex m)) {y : Fin m → ℝ} (hy : y ∈ simplex m) :
    coneInt n (β + β') y = coneInt n β y + coneInt n β' y := by
  simp only [coneInt, Pi.add_apply, smul_add]
  exact intervalIntegral.integral_add
    (intervalIntegrable_cone (A83.convex_simplex m) (zero_mem_simplex m) hβ n hy)
    (intervalIntegrable_cone (A83.convex_simplex m) (zero_mem_simplex m) hβ' n hy)

theorem coneInt_smul' (n : ℕ) (c : ℝ) (β : Ω m) (y : Fin m → ℝ) :
    coneInt n (c • β) y = c • coneInt n β y := by
  simp only [coneInt, Pi.smul_apply]
  rw [← intervalIntegral.integral_smul]
  congr 1
  funext t
  rw [smul_comm]

theorem Kop_add (n : ℕ) {β β' : Ω m} (hβ : ContinuousOn β (simplex m))
    (hβ' : ContinuousOn β' (simplex m)) : FormEqOn (Kop n (β + β')) (Kop n β + Kop n β') := by
  intro y hy
  simp only [Kop, Pi.add_apply, coneInt_add' n hβ hβ' hy, map_add]

theorem Kop_smul (n : ℕ) (c : ℝ) (β : Ω m) : FormEqOn (Kop n (c • β)) (c • Kop n β) := by
  intro y _
  simp only [Kop, Pi.smul_apply, coneInt_smul', map_smul]

theorem Kop_sub (n : ℕ) {β β' : Ω m} (hβ : ContinuousOn β (simplex m))
    (hβ' : ContinuousOn β' (simplex m)) : FormEqOn (Kop n (β - β')) (Kop n β - Kop n β') := by
  intro y hy
  have e : β - β' = β + (-1 : ℝ) • β' := by funext z; simp [sub_eq_add_neg]
  have hc : ContinuousOn ((-1 : ℝ) • β') (simplex m) := hβ'.const_smul (-1 : ℝ)
  rw [e, Kop_add n hβ hc y hy, Pi.add_apply, Kop_smul n (-1) β' y hy]
  simp [sub_eq_add_neg]

theorem jet_zero' (hr : 1 ≤ r) : jet r (0 : Ω m) = 0 := by
  have := jet_smul hr (0 : ℝ) (isCr_zero (r := r) (m := m))
  simpa using this

end IntLInfty.Kan.A83Proj

namespace IntLInfty.Kan.A83Leib

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc

attribute [local instance] algNAG algNS algFD algComplete

variable {m : ℕ}

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

def SmoothFam (r n : ℕ) (F : E → Ω m) : Prop :=
  ∃ a : E → CrForms r m n, ContDiff ℝ ∞ a ∧
    ∀ z, (IsDeg n (F z) ∧ IsCr r (F z)) ∧ jet r (F z) = a z

theorem smoothFam_zero (hr : 1 ≤ r) (n : ℕ) : SmoothFam (m := m) r n (fun _ : E => 0) := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.1 <;> assumption)

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

theorem smoothFam_congr {n : ℕ} {F G : E → Ω m} (hF : SmoothFam r n F)
    (h : ∀ z, FormEqOn (G z) (F z)) : SmoothFam r n G := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.1 <;> assumption)

theorem smoothFam_rep (hr : 1 ≤ r) {n : ℕ} {a : E → CrForms r m n} (ha : ContDiff ℝ ∞ a) :
    SmoothFam r n (fun z => wRep hr (a z)) :=
  ⟨a, ha, fun z => wRep_spec hr (a z)⟩

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

theorem extPow_eq_zero_of_lt {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {p : ℕ} (hp : Module.finrank ℝ V < p) {a : ExteriorAlgebra ℝ V} (ha : a ∈ ⋀[ℝ]^p V) :
    a = 0 := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.1 <;> assumption)

end IntLInfty.Kan.A83Defect

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

theorem alg_eq_zero_of_lt {p : ℕ} (hp : m < p) {a : Alg m}
    (ha : a ∈ ⋀[ℝ]^p (Module.Dual ℝ (Fin m → ℝ))) : a = 0 := by
  first
  | exact IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  | (apply IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.1 <;> assumption)

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

noncomputable def defB (δ : LInfty L) (S : GenSys L) (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω m)
    (hf : GenHom f) (j : Σ t : Fin m, Fin (Module.finrank ℝ (S t))) : Ω m :=
  extD (f j.1 (genBasis S j.1 j.2 : Module.Dual ℝ (L j.1))) -
    ceLift f hf (δ.δ (gen L j.1 (genBasis S j.1 j.2 : Module.Dual ℝ (L j.1))))

theorem isCr_genVal (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) : IsCr r (genVal hr S z i ξ) := by
  have e : FormEqOn (rawVal hr S z i ξ) (genVal hr S z i ξ) :=
    fun x hx => (cutL_eqOn (rawVal hr S z i ξ) x hx).symm
  refine A83DGA.isCr_of_formEqOn e ?_
  by_cases h : i < m
  · rw [rawVal_lt hr S z h]
    exact isCr_sum hr _ _ fun k _ => isCr_smul hr _ (A83Wedge.wRep_spec hr _).1.2
  · rw [rawVal_ge hr S z h]; exact isCr_zero

theorem genVal_ge (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) {i : ℕ} (h : m ≤ i)
    (ξ : Module.Dual ℝ (L i)) : genVal hr S z i ξ = 0 := by
  show cutL (rawVal hr S z i ξ) = 0
  rw [rawVal_ge hr S z (by omega), map_zero]

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83IntegK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83Leib IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83Defect

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ} {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem integ_iff_K (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) (z : Amb r S m) :
    z ∈ integ r δ S m ↔ ∀ j : Σ t : Fin m, Fin (Module.finrank ℝ (S t)),
      FormEqOn (Kop ((j.1 : ℕ) + 1) (defB δ S (genVal hr S z) (genHom_genVal hr S z) j)) 0 :=
  IntLInfty.Kan.integ_iff_generator_condition.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 hr (fun _ n β => Kop n β) (fun _ _ _ _ => rfl) δ S hcl z
    (genVal hr S z) (genHom_genVal hr S z) (isCr_genVal hr S z) (fun i hi ξ => genVal_ge hr S z hi ξ)
    (jet_genVal_basis hr S z) (ceLift (genVal hr S z) (genHom_genVal hr S z)) (ceLift_gen _ _)

end IntLInfty.Kan.A83IntegK

namespace IntLInfty.Kan.A83Top

open IntLInfty.Kan
open scoped TensorProduct

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

variable [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Top

namespace IntLInfty.Kan.A83KK

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem cB_cB (y : Fin m → ℝ) (a : Alg m) : cB m y (cB m y a) = 0 := by
  rw [cB_apply, cB_apply]
  exact CliffordAlgebra.contractLeft_contractLeft _ _

theorem Kop_Kop (p n : ℕ) (β : Ω m) : Kop p (Kop n β) = 0 := by
  funext y
  have key : ∀ s : ℝ, s ^ p • Kop n β (s • y) = cB m y (s ^ p • s • coneInt n β (s • y)) := by
    intro s
    simp only [Kop, map_smul, FunLike.coe_smul, Pi.smul_apply]
  show cB m y (∫ s in (0 : ℝ)..1, s ^ p • Kop n β (s • y)) = 0
  simp_rw [key]
  by_cases hi : IntervalIntegrable
      (fun s : ℝ => cB m y (s ^ p • s • coneInt n β (s • y))) MeasureTheory.volume 0 1
  · rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hi]
    simp [cB_cB]
  · rw [intervalIntegral.integral_undef hi, map_zero]

theorem contDiffOn_Kop (r n : ℕ) {β : Ω m} (hβ : ContDiffOn ℝ r β (simplex m)) :
    ContDiffOn ℝ r (Kop n β) (simplex m) :=
  ContDiffOn.clm_apply ((cB m).contDiff.contDiffOn)
    (contDiffOn_coneInt (isCompact_simplex m) (A83.convex_simplex m) (zero_mem_simplex m)
      (A83.uniqueDiffOn_simplex m) r β n hβ)

theorem isDeg_Kop {n : ℕ} {β : Ω m} (hβc : ContinuousOn β (simplex m)) (hD : IsDeg (n + 1) β) :
    IsDeg n (Kop n β) := by
  intro x hx
  have hmem := coneInt_mem_alg (p := n) (⋀[ℝ]^(n + 1) (Module.Dual ℝ (Fin m → ℝ)))
    (A83.convex_simplex m) (zero_mem_simplex m) hβc hD hx
  have := (contract_mem m (Module.Dual.eval ℝ (Fin m → ℝ) x) (n + 1) _ hmem).1
  simpa [Kop, cB_apply] using this

theorem extD_Kop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    FormEqOn (extD (Kop n β)) (β - Kop (n + 1) (extD β)) := fun x hx => by
  rw [Pi.sub_apply, ← Kop_hom hr hC hD x hx, add_sub_cancel_right]

theorem isCr_Kop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    IsCr r (Kop n β) := ((IntLInfty.Kan.A83Poinc.C1 r hr).1 m n β hC hD).2.1

theorem Kop_dKop (hr : 1 ≤ r) {n : ℕ} {β : Ω m} (hC : IsCr r β) (hD : IsDeg (n + 1) β) :
    FormEqOn (Kop n (extD (Kop n β))) (Kop n β) := by
  intro y hy
  have hβc : ContinuousOn β (simplex m) :=
    (contDiffOn_of_coeff (r := r) fun I => (hC I).1).continuousOn
  have hKc : ContinuousOn (Kop (n + 1) (extD β)) (simplex m) :=
    (contDiffOn_Kop r (n + 1) (contDiffOn_of_coeff fun I => (hC I).2)).continuousOn
  rw [Kop_congr n (extD_Kop hr hC hD) y hy, Kop_sub n hβc hKc y hy, Pi.sub_apply, Kop_Kop,
    Pi.zero_apply, sub_zero]

end IntLInfty.Kan.A83KK

namespace IntLInfty.Kan.A83KL

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc
  IntLInfty.Kan.A83Proj IntLInfty.Kan.A83KK
open Filter Topology
open scoped BoundedContinuousFunction

attribute [local instance] algNAG algNS algFD algComplete

variable {m r : ℕ}

theorem contOn_of_isCr {ω : Ω m} (hω : IsCr r ω) : ContinuousOn ω (simplex m) :=
  (contDiffOn_of_coeff (r := r) fun I => (hω I).1).continuousOn

noncomputable def KCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m (n + 1) →L[ℝ] CrForms r m n :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose m n

theorem KLin_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m (n + 1)) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (KCLM hr n w : Jet r m × Jet r m) = jet r (Kop n ω) :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose_spec.choose_spec.1 m n w ω hC h

noncomputable def dCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m n →L[ℝ] CrForms r m (n + 1) :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose_spec.choose m n

theorem dLin_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) {ω : Ω m}
    (hC : IsCr r ω) (h : jet r ω = w) :
    (dCLM hr n w : Jet r m × Jet r m) = jet r (extD ω) :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose_spec.choose_spec.2.1 m n w ω hC h

noncomputable def HCLM (hr : 1 ≤ r) (n : ℕ) : CrForms r m n →L[ℝ] CrForms r m n :=
  (KCLM hr n).comp (dCLM hr n)

theorem HCLM_val (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n) {ω : Ω m} (hD : IsDeg n ω)
    (hC : IsCr r ω) (h : jet r ω = w) :
    (HCLM hr n w : Jet r m × Jet r m) = jet r (Kop n (extD ω)) := by
  show (KCLM hr n (dCLM hr n w) : Jet r m × Jet r m) = _
  exact KLin_val hr _ (isCr_extD hr hC) (dLin_val hr w hC h).symm

theorem HCLM_idem (hr : 1 ≤ r) (n : ℕ) : (HCLM (m := m) hr n).comp (HCLM hr n) = HCLM hr n := by
  ext1 w
  obtain ⟨ω, hω, hw⟩ := exists_rep hr w
  have hD1 : IsDeg (n + 1) (extD ω) := isDeg_extD hr hω.2 hω.1
  have hC1 : IsCr r (extD ω) := isCr_extD hr hω.2
  have hKD : IsDeg n (Kop n (extD ω)) := isDeg_Kop (contOn_of_isCr hC1) hD1
  have hKC : IsCr r (Kop n (extD ω)) := isCr_Kop hr hC1 hD1
  apply Subtype.ext
  show (HCLM hr n (HCLM hr n w) : Jet r m × Jet r m) = HCLM hr n w
  rw [HCLM_val hr (HCLM hr n w) hKD hKC (HCLM_val hr w hω.1 hω.2 hw).symm,
    HCLM_val hr w hω.1 hω.2 hw]
  exact jet_congr (Kop_dKop hr hC1 hD1)

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

theorem jet_sub' (hr : 1 ≤ r) {a b : Ω m} (ha : IsCr r a) (hb : IsCr r b) :
    jet r (a - b) = jet r a - jet r b := by
  have e : a - b = a + (-1 : ℝ) • b := by funext x; simp [sub_eq_add_neg]
  rw [e, jet_add hr ha (isCr_smul hr _ hb), jet_smul hr _ hb]
  simp [sub_eq_add_neg]

noncomputable def HAmb (hr : 1 ≤ r) (S : GenSys L) : Amb r S m →L[ℝ] Amb r S m where
  toFun z := fun t k => HCLM hr ((t : ℕ) + 1) (z t k)
  map_add' z w := funext fun t => funext fun k => map_add (HCLM hr ((t : ℕ) + 1)) (z t k) (w t k)
  map_smul' c z := funext fun t => funext fun k => map_smul (HCLM hr ((t : ℕ) + 1)) c (z t k)
  cont := continuous_pi fun t => continuous_pi fun k =>
    (HCLM hr ((t : ℕ) + 1)).continuous.comp ((continuous_apply k).comp (continuous_apply t))

theorem HAmb_apply (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (t : Fin m)
    (k : Fin (Module.finrank ℝ (S t))) : HAmb hr S z t k = HCLM hr ((t : ℕ) + 1) (z t k) := rfl

theorem HAmb_idem (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) :
    HAmb hr S (HAmb hr S z) = HAmb hr S z :=
  funext fun t => funext fun k =>
    ContinuousLinearMap.ext_iff.1 (HCLM_idem (m := m) hr ((t : ℕ) + 1)) (z t k)

theorem Kd_sub_K (hr : 1 ≤ r) {n : ℕ} {g c : Ω m} (hgC : IsCr r g) (hcC : IsCr r c)
    (hcD : IsDeg (n + 1) c) :
    FormEqOn (Kop n (extD (g - Kop n c))) (Kop n (extD g - c)) := by
  have hKC : IsCr r (Kop n c) := isCr_Kop hr hcC hcD
  have h1 : FormEqOn (extD (g - Kop n c)) (extD g - extD (Kop n c)) :=
    fun x hx => extD_sub hr hgC hKC hx
  intro y hy
  rw [Kop_congr n h1 y hy, Kop_sub n (contOn_of_isCr (isCr_extD hr hgC))
      (contOn_of_isCr (isCr_extD hr hKC)) y hy, Kop_sub n (contOn_of_isCr (isCr_extD hr hgC))
      (contOn_of_isCr hcC) y hy, Pi.sub_apply, Pi.sub_apply, Kop_dKop hr hcC hcD y hy]

theorem defB_spec (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    IsDeg ((t : ℕ) + 1 + 1) (defB δ S (genVal hr S z) (genHom_genVal hr S z) ⟨t, k⟩) ∧
      IsCr r (defB δ S (genVal hr S z) (genHom_genVal hr S z) ⟨t, k⟩) := by
  have hgC := isCr_genVal hr S z t (genBasis S t k : Module.Dual ℝ (L t))
  have hgD : IsDeg ((t : ℕ) + 1) (genVal hr S z t (genBasis S t k : Module.Dual ℝ (L t))) :=
    fun x _ => genHom_genVal hr S z t _ x
  have hc : IsDeg ((t : ℕ) + 1 + 1) (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t))))) ∧
      IsCr r (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t))))) :=
    ((smoothFam_defect hr δ S hcl t k).choose_spec.2 z).1
  exact ⟨isDeg_sub (isDeg_extD hr hgC hgD) hc.1, isCr_sub hr (isCr_extD hr hgC) hc.2⟩

theorem HAmb_sub_val (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    (HAmb hr S (z - Gmap hr δ S hcl z) t k : Jet r m × Jet r m) =
      jet r (Kop ((t : ℕ) + 1) (defB δ S (genVal hr S z) (genHom_genVal hr S z) ⟨t, k⟩)) := by
  have hgC := isCr_genVal hr S z t (genBasis S t k : Module.Dual ℝ (L t))
  have hgD : IsDeg ((t : ℕ) + 1) (genVal hr S z t (genBasis S t k : Module.Dual ℝ (L t))) :=
    fun x _ => genHom_genVal hr S z t _ x
  have hc : IsDeg ((t : ℕ) + 1 + 1) (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t))))) ∧
      IsCr r (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t))))) :=
    ((smoothFam_defect hr δ S hcl t k).choose_spec.2 z).1
  have hKC := isCr_Kop hr hc.2 hc.1
  have hKD := isDeg_Kop (contOn_of_isCr hc.2) hc.1
  have hj : jet r (genVal hr S z t (genBasis S t k : Module.Dual ℝ (L t)) -
      Kop ((t : ℕ) + 1) (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t)))))) =
      ((z - Gmap hr δ S hcl z) t k : Jet r m × Jet r m) := by
    rw [jet_sub' hr hgC hKC, jet_genVal_basis hr S z t k, ← Gmap_val hr δ S hcl z t k]
    rfl
  rw [HAmb_apply, HCLM_val hr _ (isDeg_sub hgD hKD) (isCr_sub hr hgC hKC) hj]
  exact jet_congr (Kd_sub_K hr hgC hc.2 hc.1)

theorem integ_iff_H (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) :
    z ∈ integ r δ S m ↔ HAmb hr S (z - Gmap hr δ S hcl z) = 0 := by
  rw [integ_iff_K hr δ S hcl z]
  constructor
  · intro h
    refine funext fun t => funext fun k => Subtype.ext ?_
    rw [HAmb_sub_val hr δ S hcl z t k]
    exact (jet_congr (h ⟨t, k⟩)).trans (jet_zero' hr)
  · intro h j
    obtain ⟨t, k⟩ := j
    have h1 := HAmb_sub_val hr δ S hcl z t k
    rw [h] at h1
    have hB := defB_spec hr δ S hcl z t k
    exact formEqOn_of_jet (isCr_Kop hr hB.2 hB.1) isCr_zero (h1.symm.trans (jet_zero' hr).symm)

theorem amb_complete (S : GenSys L) : CompleteSpace (Amb r S m) := by
  haveI : ∀ n, CompleteSpace (CrForms r m n) := fun n => crForms_complete r m n
  exact inferInstanceAs (CompleteSpace ((t : Fin m) →
    (Fin (Module.finrank ℝ (S t)) → CrForms r m (t + 1))))

end IntLInfty.Kan.A83H

namespace IntLInfty.Kan.A83KM

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

noncomputable def pullAlg (m : ℕ) (i : Fin (m + 2)) : Ω (m + 1) →ₐ[ℝ] Ω m where
  toFun := pull m i
  map_one' := funext fun _ => map_one (ExteriorAlgebra.map (cofaceLin m i).dualMap)
  map_mul' a b := funext fun x =>
    map_mul (ExteriorAlgebra.map (cofaceLin m i).dualMap) (a (coface m i x)) (b (coface m i x))
  map_zero' := funext fun _ => map_zero (ExteriorAlgebra.map (cofaceLin m i).dualMap)
  map_add' a b := funext fun x =>
    map_add (ExteriorAlgebra.map (cofaceLin m i).dualMap) (a (coface m i x)) (b (coface m i x))
  commutes' c := funext fun _ => (ExteriorAlgebra.map (cofaceLin m i).dualMap).commutes c

theorem gen_expand {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (t : ℕ)
    (k : Fin (Module.finrank ℝ (S' t))) :
    (⟨gen L t (genBasis S' t k), gen_mem_genAlg S (h t (genBasis S' t k).2)⟩ : genAlg L S) =
      ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l •
        (⟨gen L t (genBasis S t l), gen_mem_genAlg S (genBasis S t l).2⟩ : genAlg L S) := by
  have e1 : ((genBasis S' t k : S' t) : Module.Dual ℝ (L t)) =
      ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l •
        ((genBasis S t l : S t) : Module.Dual ℝ (L t)) := by
    have := congrArg (fun v : S t => (v : Module.Dual ℝ (L t)))
      ((genBasis S t).sum_repr (Submodule.inclusion (h t) (genBasis S' t k)))
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finset_sum]
  simp only [SetLike.val_smul]
  rw [e1, map_sum]
  simp only [map_smul]

theorem jet_zero'' {r m : ℕ} (hr : 1 ≤ r) : jet r (0 : Ω m) = 0 := by
  have := jet_smul hr (0 : ℝ) (isCr_zero (r := r) (m := m))
  simpa using this

theorem gen_mem_ceDeg (i : ℕ) (ξ : Module.Dual ℝ (L i)) : gen L i ξ ∈ ceDeg L (i + 1) :=
  Submodule.subset_span ⟨1, fun _ => i, fun _ => ξ, by simp, by simp⟩

end IntLInfty.Kan.A83KM

namespace IntLInfty.Kan.A83Kan

open IntLInfty.Kan
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Kan

namespace IntLInfty.Kan.A83Comp

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83Comp

namespace IntLInfty.Kan.A83K2

open IntLInfty.Kan IntLInfty.Kan.A83

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]

end IntLInfty.Kan.A83K2

namespace IntLInfty.Kan.A83K2V

open IntLInfty.Kan IntLInfty.Kan.A83
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

noncomputable def valC {r m : ℕ} (S : GenSys L) (w : Amb r S m) (t : ℕ) :
    Module.Dual ℝ (L t) →ₗ[ℝ] CrForms r m (t + 1) :=
  if h : t < m then
    ∑ k : Fin (Module.finrank ℝ (S t)), LinearMap.smulRight
      ((Finsupp.lapply k).comp ((genBasis S t).repr.toLinearMap.comp (A83Ev.retr S t)))
      (w ⟨t, h⟩ k)
  else 0

theorem valC_lt {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : t < m)
    (ξ : Module.Dual ℝ (L t)) :
    valC S w t ξ = ∑ k : Fin (Module.finrank ℝ (S t)),
      (genBasis S t).repr (A83Ev.retr S t ξ) k • w ⟨t, h⟩ k := by
  simp only [valC, h, ↓reduceDIte, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply, Finsupp.lapply_apply,
    LinearEquiv.coe_coe]

theorem valC_ge {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : ¬ t < m)
    (ξ : Module.Dual ℝ (L t)) : valC S w t ξ = 0 := by
  simp only [valC, h, ↓reduceDIte, LinearMap.zero_apply]

theorem valC_of_mem {r m : ℕ} (S : GenSys L) (w : Amb r S m) {t : ℕ} (h : t < m)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S t) :
    valC S w t ξ = ∑ k : Fin (Module.finrank ℝ (S t)),
      (genBasis S t).repr ⟨ξ, hξ⟩ k • w ⟨t, h⟩ k := by
  have e : A83Ev.retr S t ξ = ⟨ξ, hξ⟩ := A83Ev.retr_spec S t ⟨ξ, hξ⟩
  rw [valC_lt S w h, e]

theorem valC_add {r m : ℕ} (S : GenSys L) (w w' : Amb r S m) (t : ℕ)
    (ξ : Module.Dual ℝ (L t)) : valC S (w + w') t ξ = valC S w t ξ + valC S w' t ξ := by
  by_cases h : t < m
  · rw [valC_lt S _ h, valC_lt S _ h, valC_lt S _ h, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => smul_add _ _ _
  · rw [valC_ge S _ h, valC_ge S _ h, valC_ge S _ h, add_zero]

theorem valC_smul {r m : ℕ} (S : GenSys L) (c : ℝ) (w : Amb r S m) (t : ℕ)
    (ξ : Module.Dual ℝ (L t)) : valC S (c • w) t ξ = c • valC S w t ξ := by
  by_cases h : t < m
  · rw [valC_lt S _ h, valC_lt S _ h, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_comm (_ : ℝ) c (w ⟨t, h⟩ k)
  · rw [valC_ge S _ h, valC_ge S _ h, smul_zero]

theorem valC_res {r m : ℕ} {S S' : GenSys L} (hS : ∀ i, S' i ≤ S i) (w : Amb r S m) (t : ℕ)
    {ξ : Module.Dual ℝ (L t)} (hξ : ξ ∈ S' t) : valC S' (res hS w) t ξ = valC S w t ξ := by
  by_cases h : t < m
  · have e1 : (⟨ξ, hS t hξ⟩ : S t) = Submodule.inclusion (hS t) ⟨ξ, hξ⟩ := rfl
    rw [valC_of_mem S' (res hS w) h hξ, valC_of_mem S w h (hS t hξ), e1]
    conv_rhs => rw [← (genBasis S' t).sum_repr ⟨ξ, hξ⟩]
    simp only [res, map_sum, map_smul, Finsupp.coe_finset_sum, Finsupp.coe_smul,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  · rw [valC_ge S' _ h, valC_ge S _ h]

theorem valC_face {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (i : Fin (m + 2)) (w : Amb r S (m + 1))
    {t : ℕ} (h : t < m) (ξ : Module.Dual ℝ (L t)) :
    valC S (faceAmb r S m i w) t ξ = faceLin (r := r) (m := m) hr (t + 1) i (valC S w t ξ) := by
  rw [valC_lt S _ h, valC_lt S _ (Nat.lt_succ_of_lt h), map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul]
  rfl

theorem crForms_eq_zero_of_lt {r m n : ℕ} (hr : 1 ≤ r) (h : m < n) (w : CrForms r m n) : w = 0 := by
  have hs := A83Wedge.wRep_spec hr w
  have e : FormEqOn (A83Wedge.wRep hr w) 0 := fun x hx =>
    A83Defect.extPow_eq_zero_of_lt
      (by simp only [Subspace.dual_finrank_eq, Module.finrank_fin_fun]; exact h) (hs.1.1 x hx)
  apply Subtype.ext
  rw [← hs.2, jet_congr e, A83KM.jet_zero'' hr]
  rfl

end IntLInfty.Kan.A83K2V

namespace IntLInfty.Kan.A83K2F

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Wedge
  IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83K2 IntLInfty.Kan.A83K2V
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem jet_sum_aux {r M : ℕ} (hr : 1 ≤ r) {ι : Type} (s : Finset ι) (f : ι → Ω M)
    (h : ∀ k, IsCr r (f k)) : jet r (∑ k ∈ s, f k) = ∑ k ∈ s, jet r (f k) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp only [Finset.sum_empty]
    exact A83Proj.jet_zero' hr
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      jet_add hr (h a) (isCr_sum hr s f fun k _ => h k), ih]

theorem jet_genVal {r M : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S M) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) :
    jet r (genVal hr S z i ξ) = (valC S z i ξ : Jet r M × Jet r M) := by
  by_cases h : i < M
  · have e : FormEqOn (genVal hr S z i ξ) (rawVal hr S z i ξ) := cutL_eqOn (rawVal hr S z i ξ)
    rw [jet_congr e, rawVal_lt hr S z h, valC_lt S z h,
      jet_sum_aux hr _ _ fun k => isCr_smul hr _ (wRep_spec hr (z ⟨i, h⟩ k)).1.2,
      Submodule.coe_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [jet_smul hr _ (wRep_spec hr (z ⟨i, h⟩ k)).1.2, (wRep_spec hr _).2, Submodule.coe_smul]
  · rw [genVal_ge hr S z (by omega) ξ, valC_ge S z h, A83Proj.jet_zero' hr]
    rfl

theorem genVal_res {r M : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (z : Amb r S M) (i : ℕ) {ξ : Module.Dual ℝ (L i)} (hξ : ξ ∈ S' i) :
    FormEqOn (genVal hr S' (res h z) i ξ) (genVal hr S z i ξ) :=
  formEqOn_of_jet (isCr_genVal hr S' _ i ξ) (isCr_genVal hr S z i ξ) (by
    rw [jet_genVal, jet_genVal, valC_res h z i hξ])

theorem ceLift_eqOn_gen {M : ℕ} (S : GenSys L) (f g : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω M)
    (hf : GenHom f) (hg : GenHom g)
    (hfg : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → FormEqOn (f i ξ) (g i ξ)) :
    ∀ a (_ : a ∈ Algebra.adjoin ℝ (⋃ i, (gen L i : Module.Dual ℝ (L i) → CE L) ''
      (S i : Set (Module.Dual ℝ (L i))))), FormEqOn (ceLift f hf a) (ceLift g hg a) := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, ξ, hξ, rfl⟩ := Set.mem_iUnion.1 hy
    intro x hx
    rw [ceLift_gen, ceLift_gen]
    exact hfg i ξ hξ x hx
  | algebraMap c =>
    intro x hx
    exact congrFun (((ceLift f hf).commutes c).trans ((ceLift g hg).commutes c).symm) x
  | add y w hy hw ihy ihw =>
    intro x hx
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, ihy x hx, ihw x hx]
  | mul y w hy hw ihy ihw =>
    intro x hx
    rw [map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, ihy x hx, ihw x hx]

end IntLInfty.Kan.A83K2F

namespace IntLInfty.Kan.A83K2F

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Wedge
  IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83K2 IntLInfty.Kan.A83K2V
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83K2F

namespace IntLInfty.Kan.A83K2F

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Wedge
  IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83K2 IntLInfty.Kan.A83K2V IntLInfty.Kan.A83Comp
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83K2F

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj

attribute [local instance] algNAG algNS algFD

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL

attribute [local instance] algNAG algNS algFD

theorem faceCr_KCLM {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2)) (hi : i ≠ 0)
    (w : CrForms r (m + 1) (n + 1)) :
    faceCr r m n i (KCLM hr n w) = KCLM hr n (faceCr r m (n + 1) i w) :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose_spec.choose_spec.2.2.2.2.2.2.1 m n i hi w

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem pull_genVal_face {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (i : Fin (m + 2))
    (z : Amb r S (m + 1)) (j : ℕ) (ξ : Module.Dual ℝ (L j)) :
    FormEqOn (pull m i (genVal hr S z j ξ)) (genVal hr S (faceAmb r S m i z) j ξ) := by
  refine formEqOn_of_jet (pull_isCr hr i (isCr_genVal hr S z j ξ)) (isCr_genVal hr S _ j ξ) ?_
  rw [jet_genVal hr S (faceAmb r S m i z) j ξ, ← faceCr_val hr i (valC S z j ξ)
    (fun x _ => genHom_genVal hr S z j ξ x) (isCr_genVal hr S z j ξ) (jet_genVal hr S z j ξ)]
  refine congrArg Subtype.val ?_
  by_cases h : j < m
  · rw [valC_face hr S i z h ξ]; rfl
  · exact (crForms_eq_zero_of_lt hr (by omega) _).trans (crForms_eq_zero_of_lt hr (by omega) _).symm

theorem pull_ceLift_eqOn {M : ℕ} (S : GenSys L) (i0 : Fin (M + 2))
    (f : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω (M + 1)) (g : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω M)
    (hf : GenHom f) (hg : GenHom g)
    (hfg : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → FormEqOn (pull M i0 (f i ξ)) (g i ξ)) :
    ∀ a (_ : a ∈ Algebra.adjoin ℝ (⋃ i, (gen L i : Module.Dual ℝ (L i) → CE L) ''
      (S i : Set (Module.Dual ℝ (L i))))),
      FormEqOn (pull M i0 (ceLift f hf a)) (ceLift g hg a) := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, ξ, hξ, rfl⟩ := Set.mem_iUnion.1 hy
    intro x hx
    rw [ceLift_gen, ceLift_gen]
    exact hfg i ξ hξ x hx
  | algebraMap c =>
    intro x hx
    have e1 : pull M i0 (ceLift f hf (algebraMap ℝ (CE L) c)) = algebraMap ℝ (Ω M) c := by
      show pullAlg M i0 _ = _
      rw [AlgHom.commutes, AlgHom.commutes]
    rw [e1, AlgHom.commutes]
  | add y w hy hw ihy ihw =>
    intro x hx
    have e : pull M i0 (ceLift f hf (y + w)) =
        pull M i0 (ceLift f hf y) + pull M i0 (ceLift f hf w) := by
      show pullAlg M i0 _ = pullAlg M i0 _ + pullAlg M i0 _
      rw [map_add, map_add]
    rw [e, map_add, Pi.add_apply, Pi.add_apply, ihy x hx, ihw x hx]
  | mul y w hy hw ihy ihw =>
    intro x hx
    have e : pull M i0 (ceLift f hf (y * w)) =
        pull M i0 (ceLift f hf y) * pull M i0 (ceLift f hf w) := by
      show pullAlg M i0 _ = pullAlg M i0 _ * pullAlg M i0 _
      rw [map_mul, map_mul]
    rw [e, map_mul, Pi.mul_apply, Pi.mul_apply, ihy x hx, ihw x hx]

theorem Gfam_face {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (i : Fin (m + 2)) (z : Amb r S (m + 1)) (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    faceCr r m ((t : ℕ) + 1 + 1) i (Gfam hr δ S hcl t.castSucc k z) =
      Gfam hr δ S hcl t k (faceAmb r S m i z) := by
  have hz := (smoothFam_defect hr δ S hcl t.castSucc k).choose_spec.2 z
  have hf := (smoothFam_defect hr δ S hcl t k).choose_spec.2 (faceAmb r S m i z)
  apply Subtype.ext
  rw [faceCr_val hr (n := (t : ℕ) + 1 + 1) i (Gfam hr δ S hcl t.castSucc k z) hz.1.1 hz.1.2 hz.2]
  show _ = ((smoothFam_defect hr δ S hcl t k).choose (faceAmb r S m i z) : Jet r m × Jet r m)
  rw [← hf.2]
  exact jet_congr (pull_ceLift_eqOn S i _ _ _ _ (fun j ξ _ => pull_genVal_face hr S i z j ξ) _
    (hcl _ _ (genBasis S t k).2))

theorem Gmap_face {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (i : Fin (m + 2)) (hi : i ≠ 0) (z : Amb r S (m + 1)) :
    faceAmb r S m i (Gmap hr δ S hcl z) = Gmap hr δ S hcl (faceAmb r S m i z) := by
  funext t k
  show faceCr r m ((t : ℕ) + 1) i (KCLM hr ((t : ℕ) + 1) (Gfam hr δ S hcl t.castSucc k z)) =
    KCLM hr ((t : ℕ) + 1) (Gfam hr δ S hcl t k (faceAmb r S m i z))
  rw [faceCr_KCLM hr _ i hi, Gfam_face]

end IntLInfty.Kan.A83K1

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.deprecated false

namespace IntLInfty.Kan.A83Fib

open scoped ContDiff
open Filter Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end IntLInfty.Kan.A83Fib

namespace IntLInfty.Kan.A83K1c

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
open scoped ContDiff

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83K1c

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev IntLInfty.Kan.A83DGA
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem gen_expand_val {S S' : GenSys L} (h : ∀ i, S' i ≤ S i) (t : ℕ)
    (k : Fin (Module.finrank ℝ (S' t))) :
    gen L t (genBasis S' t k : Module.Dual ℝ (L t)) =
      ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l •
        gen L t (genBasis S t l : Module.Dual ℝ (L t)) := by
  have := congrArg Subtype.val (gen_expand h t k)
  rw [AddSubmonoidClass.coe_finset_sum] at this
  simpa only [SetLike.val_smul] using this

theorem Gfam_res {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (hcl' : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S' i → δ.δ (gen L i ξ) ∈ genAlg L S')
    (z : Amb r S m) (t : Fin m) (k : Fin (Module.finrank ℝ (S' t))) :
    ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l •
        Gfam hr δ S hcl t l z = Gfam hr δ S' hcl' t k (res h z) := by
  apply Subtype.ext
  have hf := (smoothFam_defect hr δ S' hcl' t k).choose_spec.2 (res h z)
  show _ = ((smoothFam_defect hr δ S' hcl' t k).choose (res h z) : Jet r m × Jet r m)
  rw [← hf.2, Submodule.coe_sum]
  simp only [Submodule.coe_smul]
  have hl : ∀ l, ((Gfam hr δ S hcl t l z : CrForms r m _) : Jet r m × Jet r m) =
      jet r (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t l : Module.Dual ℝ (L t))))) :=
    fun l => ((smoothFam_defect hr δ S hcl t l).choose_spec.2 z).2.symm
  have hc : ∀ l, IsCr r (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S t l : Module.Dual ℝ (L t))))) :=
    fun l => ((smoothFam_defect hr δ S hcl t l).choose_spec.2 z).1.2
  simp only [hl]
  have e2 : A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
      (δ.δ (gen L t (genBasis S' t k : Module.Dual ℝ (L t)))) =
      ∑ l, (genBasis S t).repr (Submodule.inclusion (h t) (genBasis S' t k)) l •
        A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
          (δ.δ (gen L t (genBasis S t l : Module.Dual ℝ (L t)))) := by
    rw [gen_expand_val h t k, map_sum, map_sum]
    simp only [map_smul]
  symm
  calc jet r (A83DGA.ceLift (genVal hr S' (res h z)) (genHom_genVal hr S' (res h z))
        (δ.δ (gen L t (genBasis S' t k : Module.Dual ℝ (L t)))))
      = jet r (A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z)
        (δ.δ (gen L t (genBasis S' t k : Module.Dual ℝ (L t))))) :=
        jet_congr (ceLift_eqOn_gen S' _ _ _ _ (fun i ξ hξ => genVal_res hr h z i hξ) _
          (hcl' _ _ (genBasis S' t k).2))
    _ = _ := by
        rw [e2, jet_sum_aux hr _ _ fun l => isCr_smul hr _ (hc l)]
        exact Finset.sum_congr rfl fun l _ => jet_smul hr _ (hc l)

theorem Gmap_res {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (hcl' : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S' i → δ.δ (gen L i ξ) ∈ genAlg L S')
    (z : Amb r S m) : res h (Gmap hr δ S hcl z) = Gmap hr δ S' hcl' (res h z) := by
  funext t k
  show _ = KCLM hr ((t : ℕ) + 1) (Gfam hr δ S' hcl' t k (res h z))
  rw [← Gfam_res hr δ h hcl hcl' z t k, map_sum]
  simp only [map_smul]
  rfl

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem ceLift_prod_apply {M : ℕ} (F : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω M) (hF : A83DGA.GenHom F)
    (x : Fin M → ℝ) {k : ℕ} (dd : Fin k → ℕ) (ξ : ∀ t, Module.Dual ℝ (L (dd t))) :
    A83DGA.ceLift F hF (List.ofFn fun t => gen L (dd t) (ξ t)).prod x =
      (List.ofFn fun t => F (dd t) (ξ t) x).prod := by
  have e := map_list_prod ((Pi.evalRingHom (fun _ : Fin M → ℝ =>
      ExteriorAlgebra ℝ (Module.Dual ℝ (Fin M → ℝ))) x).comp
      (A83DGA.ceLift F hF).toRingHom) (List.ofFn fun t => gen L (dd t) (ξ t))
  rw [List.map_ofFn] at e
  refine e.trans (congrArg List.prod (List.ofFn_inj.2 (funext fun t => ?_)))
  show A83DGA.ceLift F hF (gen L (dd t) (ξ t)) x = F (dd t) (ξ t) x
  rw [A83DGA.ceLift_gen]

theorem genVal_affine {r M : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z v : Amb r S M) (s : ℝ) (i : ℕ)
    (ξ : Module.Dual ℝ (L i)) :
    FormEqOn (genVal hr S (z + s • v) i ξ)
      ((1 - s) • genVal hr S z i ξ + s • genVal hr S (z + v) i ξ) := by
  have c1 := isCr_genVal hr S z i ξ
  have c2 := isCr_genVal hr S (z + v) i ξ
  refine formEqOn_of_jet (isCr_genVal hr S _ i ξ)
    (isCr_add hr (isCr_smul hr _ c1) (isCr_smul hr _ c2)) ?_
  rw [jet_add hr (isCr_smul hr _ c1) (isCr_smul hr _ c2), jet_smul hr _ c1, jet_smul hr _ c2,
    jet_genVal, jet_genVal, jet_genVal, valC_add, valC_smul, valC_add]
  simp only [Submodule.coe_add, Submodule.coe_smul]
  (module)

theorem genVal_eqOn_low {r M : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z v : Amb r S M) {i : ℕ}
    {ξ : Module.Dual ℝ (L i)} (hv : valC S v i ξ = 0) :
    FormEqOn (genVal hr S z i ξ) (genVal hr S (z + v) i ξ) :=
  formEqOn_of_jet (isCr_genVal hr S z i ξ) (isCr_genVal hr S _ i ξ) (by
    rw [jet_genVal, jet_genVal, valC_add, hv, add_zero])

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F IntLInfty.Kan.A83Top IntLInfty.Kan.A83K1c
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete IntLInfty.Kan.A83H.amb_complete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem cB_mul_of_rad {M : ℕ} (y : Fin M → ℝ) {u w : Alg M}
    (hu : u ∈ LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin M → ℝ) →ₗ[ℝ] Alg M))
    (hcu : cB M y u = 0) (hcw : cB M y w = 0) : cB M y (u * w) = 0 := by
  obtain ⟨φ, rfl⟩ := hu
  rw [cB_apply] at hcu hcw ⊢
  rw [CliffordAlgebra.contractLeft_ι_mul, hcw, mul_zero, sub_zero]
  rw [CliffordAlgebra.contractLeft_ι] at hcu
  have h0 : (Module.Dual.eval ℝ (Fin M → ℝ) y) φ = 0 :=
    (ExteriorAlgebra.algebraMap_leftInverse (Module.Dual ℝ (Fin M → ℝ))).injective
      (by rw [hcu, map_zero])
  rw [h0, zero_smul]

theorem ceLift_quad_rad {M : ℕ} (F0 F1 Fs : ∀ i, Module.Dual ℝ (L i) →ₗ[ℝ] Ω M)
    (h0 : A83DGA.GenHom F0) (h1 : A83DGA.GenHom F1) (hs : A83DGA.GenHom Fs) (s : ℝ)
    (x y : Fin M → ℝ)
    (hlin : ∀ i ξ, Fs i ξ x = (1 - s) • F0 i ξ x + s • F1 i ξ x)
    (hrad : ∀ i ξ, cB M y (F1 i ξ x - F0 i ξ x) = 0)
    (hdeg : ∀ i ξ, F1 i ξ x - F0 i ξ x ∈
      LinearMap.range (ExteriorAlgebra.ι ℝ : Module.Dual ℝ (Fin M → ℝ) →ₗ[ℝ] Alg M))
    {a : CE L} (ha : a ∈ ceDeg L 2) :
    cB M y (A83DGA.ceLift Fs hs a x -
      ((1 - s) • A83DGA.ceLift F0 h0 a x + s • A83DGA.ceLift F1 h1 a x)) = 0 := by
  induction ha using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨k, dd, ξ, hsum, rfl⟩ := hz
    rw [ceLift_prod_apply, ceLift_prod_apply, ceLift_prod_apply]
    rcases k with _ | _ | _ | k
    · simp at hsum
    · simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      rw [hlin, sub_self, map_zero]
    · simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one]
      rw [hlin, hlin]
      set a0 := F0 (dd 0) (ξ 0) x
      set a1 := F0 (dd (Fin.succ 0)) (ξ (Fin.succ 0)) x
      set b0 := F1 (dd 0) (ξ 0) x
      set b1 := F1 (dd (Fin.succ 0)) (ξ (Fin.succ 0)) x
      have e : ((1 - s) • a0 + s • b0) * ((1 - s) • a1 + s • b1) -
          ((1 - s) • (a0 * a1) + s • (b0 * b1)) = (s ^ 2 - s) • ((b0 - a0) * (b1 - a1)) := by
        simp only [mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, smul_smul]
        (module)
      rw [e, map_smul, cB_mul_of_rad y (hdeg _ _) (hrad _ _) (hrad _ _), smul_zero]
    · exfalso
      have hle : ∑ t : Fin (k + 3), (1 : ℕ) ≤ ∑ t, (dd t + 1) :=
        Finset.sum_le_sum fun t _ => Nat.le_add_left 1 _
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hle
      omega
  | zero =>
    simp only [map_zero, Pi.zero_apply, smul_zero, add_zero, sub_zero]
  | add z w _ _ ihz ihw =>
    simp only [map_add, Pi.add_apply]
    generalize A83DGA.ceLift Fs hs z x = A at ihz ⊢
    generalize A83DGA.ceLift F0 h0 z x = B at ihz ⊢
    generalize A83DGA.ceLift F1 h1 z x = C at ihz ⊢
    generalize A83DGA.ceLift Fs hs w x = A' at ihw ⊢
    generalize A83DGA.ceLift F0 h0 w x = B' at ihw ⊢
    generalize A83DGA.ceLift F1 h1 w x = C' at ihw ⊢
    rw [show A + A' - ((1 - s) • (B + B') + s • (C + C')) =
      (A - ((1 - s) • B + s • C)) + (A' - ((1 - s) • B' + s • C')) by module, map_add, ihz, ihw,
      add_zero]
  | smul c z _ ihz =>
    simp only [map_smul, Pi.smul_apply]
    generalize A83DGA.ceLift Fs hs z x = A at ihz ⊢
    generalize A83DGA.ceLift F0 h0 z x = B at ihz ⊢
    generalize A83DGA.ceLift F1 h1 z x = C at ihz ⊢
    rw [show c • A - ((1 - s) • c • B + s • c • C) = c • (A - ((1 - s) • B + s • C)) by module,
      map_smul, ihz, smul_zero]

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F IntLInfty.Kan.A83H
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete IntLInfty.Kan.A83H.amb_complete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem HCLM_KCLM {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) :
    (HCLM (m := m) hr n).comp (KCLM hr n) = KCLM hr n := by
  refine ContinuousLinearMap.ext fun w => ?_
  obtain ⟨om, hom, hw⟩ := exists_rep hr w
  have hK : (KCLM hr n w : Jet r m × Jet r m) = jet r (Kop n om) := KLin_val hr w hom.2 hw
  apply Subtype.ext
  show (HCLM hr n (KCLM hr n w) : Jet r m × Jet r m) = KCLM hr n w
  rw [HCLM_val hr (KCLM hr n w) (isDeg_Kop (contOn_of_isCr hom.2) hom.1) (isCr_Kop hr hom.2 hom.1)
    hK.symm, hK]
  exact jet_congr (Kop_dKop hr hom.2 hom.1)

theorem HAmb_Gmap {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) : HAmb hr S (Gmap hr δ S hcl z) = Gmap hr δ S hcl z :=
  funext fun t => funext fun k =>
    ContinuousLinearMap.ext_iff.1 (HCLM_KCLM (m := m) hr ((t : ℕ) + 1)) (Gfam hr δ S hcl t k z)

theorem hI_H {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z v : Amb r S m) :
    HAmb hr S (fderiv ℝ (Gmap hr δ S hcl) z v) = fderiv ℝ (Gmap hr δ S hcl) z v := by
  have hG := (Gmap_contDiff (m := m) hr δ S hcl).differentiable (by simp)
  have h := (HAmb hr S).hasFDerivAt.comp z (hG z).hasFDerivAt
  have e : (⇑(HAmb hr S) ∘ Gmap hr δ S hcl) = Gmap hr δ S hcl :=
    funext fun w => HAmb_Gmap (m := m) hr δ S hcl w
  rw [e] at h
  exact (ContinuousLinearMap.ext_iff.1 h.fderiv v).symm

theorem valC_HAmb {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (w : Amb r S m) (t : ℕ)
    (ξ : Module.Dual ℝ (L t)) :
    valC S (HAmb hr S w) t ξ = HCLM hr (t + 1) (valC S w t ξ) := by
  by_cases h : t < m
  · rw [valC_lt S _ h, valC_lt S _ h, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    rfl
  · rw [valC_ge S _ h, valC_ge S _ h, map_zero]

theorem rep_rad_of_H {r m : ℕ} (hr : 1 ≤ r) {n : ℕ} (w : CrForms r m n)
    (hw : HCLM hr n w = w) :
    ∃ om : Ω m, IsCr r om ∧ jet r om = (w : Jet r m × Jet r m) ∧
      ∀ (x : Fin m → ℝ) (c : ℝ), cB m x (om (c • x)) = 0 := by
  obtain ⟨om, hom, hw'⟩ := exists_rep hr w
  have hC1 : IsCr r (extD om) := isCr_extD hr hom.2
  have hD1 : IsDeg (n + 1) (extD om) := isDeg_extD hr hom.2 hom.1
  refine ⟨Kop n (extD om), isCr_Kop hr hC1 hD1, ?_, fun x c => ?_⟩
  · rw [← HCLM_val hr w hom.1 hom.2 hw', hw]
  · show cB m x (cB m (c • x) (coneInt n (extD om) (c • x))) = 0
    rw [map_smul, ContinuousLinearMap.smul_apply, map_smul, cB_cB, smul_zero]

theorem valC_zero_of_pos {r m : ℕ} (S : GenSys L) (hS : ∀ t, 0 < t → Module.finrank ℝ (S t) = 0)
    (v : Amb r S m) {i : ℕ} (hi : i ≠ 0) (ξ : Module.Dual ℝ (L i)) : valC S v i ξ = 0 := by
  by_cases hm : i < m
  · rw [valC_lt _ _ hm]
    refine Finset.sum_eq_zero fun k _ => ?_
    exfalso
    have h0 := hS i (Nat.pos_of_ne_zero hi)
    have := k.isLt
    omega
  · exact valC_ge _ _ hm ξ

theorem Gmap_affine_H {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (hS : ∀ t, 0 < t → Module.finrank ℝ (S t) = 0)
    (z v : Amb r S m) (hv : HAmb hr S v = v) (s : ℝ) :
    Gmap hr δ S hcl (z + s • v) =
      (1 - s) • Gmap hr δ S hcl z + s • Gmap hr δ S hcl (z + v) := by
  funext t k
  have ht0 : (t : ℕ) = 0 := by
    by_contra hne
    have h0 := hS _ (Nat.pos_of_ne_zero hne)
    have := k.isLt
    omega
  have hdiff : ∀ i (ξ : Module.Dual ℝ (L i)), ∃ om : Ω m,
      FormEqOn (genVal hr S (z + v) i ξ - genVal hr S z i ξ) om ∧
      (∀ (x : Fin m → ℝ) (c : ℝ), cB m x (om (c • x)) = 0) ∧
      (i ≠ 0 → om = 0) := by
    intro i ξ
    by_cases hi : i = 0
    · have hfix : HCLM hr (i + 1) (valC S v i ξ) = valC S v i ξ := by
        rw [← valC_HAmb, hv]
      obtain ⟨om, homC, homj, homr⟩ := rep_rad_of_H hr _ hfix
      refine ⟨om, formEqOn_of_jet (isCr_sub hr (isCr_genVal hr S _ i ξ) (isCr_genVal hr S z i ξ))
        homC ?_, homr, fun h => absurd hi h⟩
      rw [jet_sub' hr (isCr_genVal hr S _ i ξ) (isCr_genVal hr S z i ξ), jet_genVal, jet_genVal,
        homj, valC_add]
      simp only [Submodule.coe_add, add_sub_cancel_left]
    · refine ⟨0, fun x hx => ?_, fun x c => by simp, fun _ => rfl⟩
      rw [Pi.sub_apply, ← genVal_eqOn_low hr S z v (valC_zero_of_pos S hS v hi ξ) x hx, sub_self]
      rfl
  have hA := fun w => (smoothFam_defect hr δ S hcl t k).choose_spec.2 w
  apply Subtype.ext
  show (Gmap hr δ S hcl (z + s • v) t k : Jet r m × Jet r m) =
    (1 - s) • (Gmap hr δ S hcl z t k : Jet r m × Jet r m) +
      s • (Gmap hr δ S hcl (z + v) t k : Jet r m × Jet r m)
  rw [Gmap_val, Gmap_val, Gmap_val]
  set b := δ.δ (gen L t (genBasis S t k : Module.Dual ℝ (L t))) with hb
  set As := A83DGA.ceLift (genVal hr S (z + s • v)) (genHom_genVal hr S (z + s • v)) b
  set A0 := A83DGA.ceLift (genVal hr S z) (genHom_genVal hr S z) b
  set A1 := A83DGA.ceLift (genVal hr S (z + v)) (genHom_genVal hr S (z + v)) b
  have cs : IsDeg ((t : ℕ) + 1 + 1) As ∧ IsCr r As := (hA (z + s • v)).1
  have c0 : IsDeg ((t : ℕ) + 1 + 1) A0 ∧ IsCr r A0 := (hA z).1
  have c1 : IsDeg ((t : ℕ) + 1 + 1) A1 ∧ IsCr r A1 := (hA (z + v)).1
  have k0 := isCr_Kop hr c0.2 c0.1
  have k1 := isCr_Kop hr c1.2 c1.1
  rw [← jet_smul hr _ k0, ← jet_smul hr _ k1, ← jet_add hr (isCr_smul hr _ k0) (isCr_smul hr _ k1)]
  refine jet_congr fun x hx => ?_
  have hb2 : b ∈ ceDeg L 2 := by
    have h := δ.deg _ _ (A83DGA.gen_mem_ceDeg _ (genBasis S t k : Module.Dual ℝ (L t)))
    rw [show (t : ℕ) + 1 + 1 = 2 by omega] at h
    exact h
  have cA0 := contOn_of_isCr c0.2
  have cA1 := contOn_of_isCr c1.2
  have cAs := contOn_of_isCr cs.2
  have cM : ContinuousOn ((1 - s) • A0 + s • A1) (simplex m) :=
    (cA0.const_smul _).add (cA1.const_smul _)
  have e1 := Kop_sub ((t : ℕ) + 1) cAs cM x hx
  have e2 := Kop_add ((t : ℕ) + 1) (cA0.const_smul (1 - s)) (cA1.const_smul s) x hx
  have e3 := Kop_smul ((t : ℕ) + 1) (1 - s) A0 x hx
  have e4 := Kop_smul ((t : ℕ) + 1) s A1 x hx
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply] at e1 e2 e3 e4 ⊢
  rw [e2, e3, e4] at e1
  rw [← sub_eq_zero, ← e1]
  have hseg : segment ℝ 0 x ⊆ simplex m :=
    (A83.convex_simplex m).segment_subset (zero_mem_simplex m) hx
  show cB m x (coneInt ((t : ℕ) + 1) (As - ((1 - s) • A0 + s • A1)) x) = 0
  refine clm_coneInt_eq_zero (cB m x) (convex_segment 0 x) (left_mem_segment ℝ 0 x)
    ((cAs.sub cM).mono hseg) (fun y hy => ?_) _ (right_mem_segment ℝ 0 x)
  obtain ⟨a, c, _, _, _, rfl⟩ := hy
  rw [smul_zero, zero_add]
  have hy' : c • x ∈ simplex m := hseg ⟨a, c, by assumption, by assumption, by assumption,
    by rw [smul_zero, zero_add]⟩
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
  refine ceLift_quad_rad _ _ _ _ _ _ s (c • x) x
    (fun i ξ => genVal_affine hr S z v s i ξ (c • x) hy') (fun i ξ => ?_) (fun i ξ => ?_) hb2
  · obtain ⟨om, home, homr, -⟩ := hdiff i ξ
    have := home (c • x) hy'
    simp only [Pi.sub_apply] at this
    rw [this]
    exact homr x c
  · obtain ⟨om, home, -, hom0⟩ := hdiff i ξ
    have := home (c • x) hy'
    simp only [Pi.sub_apply] at this
    rw [this]
    by_cases hi : i = 0
    · subst hi
      have h1 := Submodule.sub_mem _ (genHom_genVal hr S (z + v) 0 ξ (c • x))
        (genHom_genVal hr S z 0 ξ (c • x))
      rw [this, zero_add] at h1
      have h2 : om (c • x) ∈ LinearMap.range (ExteriorAlgebra.ι ℝ :
          Module.Dual ℝ (Fin m → ℝ) →ₗ[ℝ] Alg m) ^ 1 := h1
      rwa [pow_one] at h2
    · rw [hom0 hi]
      exact Submodule.zero_mem _

theorem add_fderiv_of_affine {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (hf : Differentiable ℝ f) (z v : E)
    (haff : ∀ s : ℝ, f (z + s • v) = (1 - s) • f z + s • f (z + v)) :
    f (z + v) = f z + fderiv ℝ f z v := by
  have hγ : HasDerivAt (fun s : ℝ => z + s • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add z
  have h1 := (hf (z + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
  have e : (f ∘ fun s : ℝ => z + s • v) = fun s => (1 - s) • f z + s • f (z + v) :=
    funext fun s => haff s
  rw [e] at h1
  have h2 : HasDerivAt (fun s : ℝ => (1 - s) • f z + s • f (z + v)) (f (z + v) - f z) 0 := by
    have := ((hasDerivAt_id' (0 : ℝ)).smul_const (f (z + v) - f z)).const_add (f z)
    rw [one_smul] at this
    have ef : (fun s : ℝ => f z + s • (f (z + v) - f z)) =
        fun s => (1 - s) • f z + s • f (z + v) := funext fun s => by module
    rwa [ef] at this
  have h3 := h1.unique h2
  rw [zero_smul, add_zero] at h3
  rw [h3]
  abel

theorem hA_H {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (hS : ∀ t, 0 < t → Module.finrank ℝ (S t) = 0)
    (z v : Amb r S m) (hv : HAmb hr S v = v) :
    Gmap hr δ S hcl (z + v) = Gmap hr δ S hcl z + fderiv ℝ (Gmap hr δ S hcl) z v :=
  add_fderiv_of_affine _ ((Gmap_contDiff (m := m) hr δ S hcl).differentiable (by simp)) z v
    (Gmap_affine_H hr δ S hcl hS z v hv)

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83K1

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83KK IntLInfty.Kan.A83KL IntLInfty.Kan.A83Ev
  IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G IntLInfty.Kan.A83KM IntLInfty.Kan.A83K2V
  IntLInfty.Kan.A83K2F IntLInfty.Kan.A83H IntLInfty.Kan.A83Comp
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete IntLInfty.Kan.A83H.amb_complete

set_option linter.unusedSectionVars false

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem faceCr_dCLM {r m : ℕ} (hr : 1 ≤ r) (n : ℕ) (i : Fin (m + 2))
    (w : CrForms r (m + 1) n) :
    faceCr r m (n + 1) i (dCLM hr n w) = dCLM hr n (faceCr r m n i w) :=
  ((IntLInfty.Kan.A83Poinc.C1 r hr).2.2.2.2.2.2.2.2.2).choose_spec.choose_spec.2.2.2.2.2.2.2 m n i w

theorem faceAmb_HAmb {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (i : Fin (m + 2)) (hi : i ≠ 0)
    (z : Amb r S (m + 1)) :
    faceAmb r S m i (HAmb hr S z) = HAmb hr S (faceAmb r S m i z) := by
  funext t k
  show faceCr r m ((t : ℕ) + 1) i (KCLM hr ((t : ℕ) + 1) (dCLM hr ((t : ℕ) + 1) (z t.castSucc k))) =
    KCLM hr ((t : ℕ) + 1) (dCLM hr ((t : ℕ) + 1) (faceCr r m ((t : ℕ) + 1) i (z t.castSucc k)))
  rw [faceCr_KCLM hr _ i hi, faceCr_dCLM]

theorem res_HAmb {r m : ℕ} (hr : 1 ≤ r) {S S' : GenSys L} (h : ∀ i, S' i ≤ S i)
    (z : Amb r S m) : res h (HAmb hr S z) = HAmb hr S' (res h z) := by
  funext t k
  show ∑ l, _ • HCLM hr ((t : ℕ) + 1) (z t l) = HCLM hr ((t : ℕ) + 1) (∑ l, _ • z t l)
  simp only [map_sum, map_smul]

end IntLInfty.Kan.A83K1

namespace IntLInfty.Kan.A83CHtail

open IntLInfty.Kan IntLInfty.Kan.A83 IntLInfty.Kan.A83Poinc IntLInfty.Kan.A83Cone IntLInfty.Kan.A83Proj
  IntLInfty.Kan.A83DGA IntLInfty.Kan.A83Ev IntLInfty.Kan.A83IntegK IntLInfty.Kan.A83G
open scoped ContDiff

attribute [local instance] algNAG algNS algFD algComplete

variable {L : ℕ → Type} [∀ i, AddCommGroup (L i)] [∀ i, Module ℝ (L i)]
  [∀ i, FiniteDimensional ℝ (L i)]

theorem gen_agree {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m)
    (h1 : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ)))
    (h2 : ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) :
    ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → FormEqOn (φ (gen L i ξ)) (genVal hr S z i ξ) := by
  intro i ξ hξ
  by_cases hi : i < m
  · let t : Fin m := ⟨i, hi⟩
    have hb : ∀ k : Fin (Module.finrank ℝ (S t)),
        FormEqOn (φ (gen L i (genBasis S t k))) (genVal hr S z i (genBasis S t k)) := fun k =>
      formEqOn_of_jet (h1 i _ (genBasis S t k).2).2 (isCr_genVal hr S z i _)
        ((h2 t k).trans (jet_genVal_basis hr S z t k).symm)
    have hξ' : ξ = ∑ k, (genBasis S t).repr ⟨ξ, hξ⟩ k • (genBasis S t k : Module.Dual ℝ (L i)) := by
      have := congrArg Subtype.val ((genBasis S t).sum_repr ⟨ξ, hξ⟩)
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    intro x hx
    rw [hξ', map_sum, map_sum, map_sum, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hb k x hx]
  · intro x hx
    rw [genVal_ge hr S z (by omega) ξ, Pi.zero_apply]
    exact alg_eq_zero_of_lt (p := i + 1) (by omega) ((h1 i ξ hξ).1 x hx)

theorem phi_agree {r m : ℕ} (hr : 1 ≤ r) (S : GenSys L) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m)
    (h1 : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ)))
    (h2 : ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) :
    ∀ a, a ∈ genAlg L S → FormEqOn (φ a) (ceLift (genVal hr S z) (genHom_genVal hr S z) a) := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨i, ξ, hξ, rfl⟩ := Set.mem_iUnion.1 hy
    intro x hx
    rw [ceLift_gen]
    exact gen_agree hr S z φ h1 h2 i ξ hξ x hx
  | algebraMap c =>
    intro x hx
    exact congrFun ((φ.commutes c).trans ((ceLift (genVal hr S z) (genHom_genVal hr S z)).commutes c).symm) x
  | add y w hy hw ihy ihw =>
    intro x hx
    rw [map_add, map_add, Pi.add_apply, Pi.add_apply, ihy x hx, ihw x hx]
  | mul y w hy hw ihy ihw =>
    intro x hx
    rw [map_mul, map_mul, Pi.mul_apply, Pi.mul_apply, ihy x hx, ihw x hx]

theorem Gmap_isGmap {r m : ℕ} (hr : 1 ≤ r) (δ : LInfty L) (S : GenSys L)
    (hcl : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
    (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m)
    (h1 : ∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ)))
    (h2 : ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m))
    (t : Fin m) (k : Fin (Module.finrank ℝ (S t))) :
    (Gmap hr δ S hcl z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I)) := by
  rw [Gmap_val]
  have hC := ((smoothFam_defect hr δ S hcl t k).choose_spec.2 z).1.2
  have hag := phi_agree hr S z φ h1 h2 _ (hcl t _ (genBasis S t k).2)
  apply jet_congr
  intro y hy
  rw [(C1 r hr).2.2.2.2.2.2.2.2.1 m _ _ hC y hy]
  refine congrArg _ (Finset.sum_congr rfl fun I _ => ?_)
  refine congrArg (· • formBasis m I) (intervalIntegral.integral_congr fun s hs => ?_)
  rw [Set.uIcc_of_le zero_le_one] at hs
  simp only [coeff, hag _ (smul_mem_simplex hy hs)]

end IntLInfty.Kan.A83CHtail

open IntLInfty.Kan in
open scoped ContDiff in
theorem solution (r : ℕ) (hr : 1 ≤ r) (L : ℕ → Type) [∀ i, AddCommGroup (L i)]
    [∀ i, Module ℝ (L i)] [∀ i, FiniteDimensional ℝ (L i)] (δ : LInfty L) :
    ∃ (G : ∀ (S : GenSys L) (m : ℕ), Amb r S m → Amb r S m)
      (H : ∀ (S : GenSys L) (m : ℕ), Amb r S m →L[ℝ] Amb r S m),
    ∀ S : GenSys L, (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S) →
      (∀ (m : ℕ) (z : Amb r S m) (φ : CE L →ₐ[ℝ] Ω m),
      (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i →
        IsDeg (i + 1) (φ (gen L i ξ)) ∧ IsCr r (φ (gen L i ξ))) →
      (∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        jet r (φ (gen L t (genBasis S t k))) = (z t k : Jet r m × Jet r m)) →
      ∀ (t : Fin m) (k : Fin (Module.finrank ℝ (S t))),
        (G S m z t k : Jet r m × Jet r m) = jet r (fun y =>
          CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℝ (Module.Dual ℝ (Fin m → ℝ))))
            (Module.Dual.eval ℝ (Fin m → ℝ) y)
            (∑ I : Finset (Fin m), (∫ s in (0 : ℝ)..1,
              s ^ ((t : ℕ) + 1) * coeff (φ (δ.δ (gen L t (genBasis S t k)))) I (s • y)) •
                formBasis m I))) ∧
      (∀ m, CompleteSpace (Amb r S m)) ∧
      (∀ m, ContDiff ℝ ∞ (G S m)) ∧
      (∀ m z, H S m (H S m z) = H S m z) ∧
      (∀ m z, H S m (G S m z) = G S m z) ∧
      (∀ m z v, H S m (fderiv ℝ (G S m) z v) = fderiv ℝ (G S m) z v) ∧
      (∀ m z, z ∈ integ r δ S m ↔ H S m (z - G S m z) = 0) ∧
      (∀ m (i : Fin (m + 2)), i ≠ 0 → ∀ z,
        faceAmb r S m i (G S (m + 1) z) = G S m (faceAmb r S m i z)) ∧
      (∀ m (i : Fin (m + 2)), i ≠ 0 → ∀ z,
        faceAmb r S m i (H S (m + 1) z) = H S m (faceAmb r S m i z)) ∧
      ((∀ t, 0 < t → Module.finrank ℝ (S t) = 0) → ∀ m z v, H S m v = v →
        G S m (z + v) = G S m z + fderiv ℝ (G S m) z v) ∧
      (∀ (S' : GenSys L) (h : ∀ i, S' i ≤ S i), (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S' i → δ.δ (gen L i ξ) ∈ genAlg L S') →
        ∀ m z, res h (G S m z) = G S' m (res h z) ∧ res h (H S m z) = H S' m (res h z)) := by
  classical
  refine ⟨fun S m => if hS : (∀ i (ξ : Module.Dual ℝ (L i)), ξ ∈ S i → δ.δ (gen L i ξ) ∈ genAlg L S)
      then A83G.Gmap (m := m) hr δ S hS else id, fun S m => A83H.HAmb (m := m) hr S, ?_⟩
  intro S hcl
  simp only [dif_pos hcl]
  refine ⟨fun m z φ h1 h2 t k => A83CHtail.Gmap_isGmap hr δ S hcl z φ h1 h2 t k,
    fun m => A83H.amb_complete (r := r) (m := m) S,
    fun m => A83G.Gmap_contDiff hr δ S hcl,
    fun m z => A83H.HAmb_idem hr S z,
    fun m z => A83K1.HAmb_Gmap hr δ S hcl z,
    fun m z v => A83K1.hI_H hr δ S hcl z v,
    fun m z => A83H.integ_iff_H hr δ S hcl z,
    fun m i hi z => A83K1.Gmap_face hr δ S hcl i hi z,
    fun m i hi z => A83K1.faceAmb_HAmb hr S i hi z,
    fun hS m z v hv => A83K1.hA_H hr δ S hcl hS z v hv,
    fun S' h hcl' m z => ?_⟩
  simp only [dif_pos hcl']
  exact ⟨A83K1.Gmap_res hr δ h hcl hcl' z, A83K1.res_HAmb hr h z⟩

