-- Prove2me | solution 1 for HunterPDE.Semigroup.lumer_phillips
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-10T02:59:08.711979+00:00
-- url     : https://prove2.me/submissions/ab0158dc-9772-4b6e-a16b-69be958a387f

import Mathlib
import Definitions.Def_HunterPDE_Semigroup_C0Semigroup
import Definitions.Def_HunterPDE_Semigroup_Resolvent

/- BEGIN WHOLE MODULE SemigroupContinuity -/
section
open Filter Set
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem contraction_apply (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    {t : ℝ} (ht : 0 ≤ t) (x : X) : ‖T t x‖ ≤ ‖x‖ :=
  (T t).le_opNorm x |>.trans (by nlinarith [hT.2 t ht, norm_nonneg x])

theorem semigroup_apply (T : ℝ → X →L[𝕜] X) (hT : IsC0Semigroup T)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    T (s+t) x = T s (T t x) := by rw [← hT.2.1 s t hs ht]; rfl

theorem contraction_difference (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (x : X) :
    ‖T s x - T t x‖ ≤ ‖T |s-t| x - x‖ := by
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have he : T s x - T t x = T t (T (s-t) x - x) := by
      rw [map_sub, ← semigroup_apply T hT.1 ht (sub_nonneg.mpr h)]
      congr 2; simp only [add_sub_cancel]
    rw [he]
    exact contraction_apply T hT ht _
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    rw [norm_sub_rev]
    have he : T t x - T s x = T s (T (t-s) x - x) := by
      rw [map_sub, ← semigroup_apply T hT.1 hs (sub_nonneg.mpr h)]
      congr 2; simp only [add_sub_cancel]
    rw [he]
    exact contraction_apply T hT hs _

theorem semigroup_tendsto_zero_ge (T : ℝ → X →L[𝕜] X) (hT : IsC0Semigroup T)
    (x : X) : Tendsto (fun t => T t x) (𝓝[≥] 0) (𝓝 x) := by
  rw [← Ioi_insert, nhdsWithin_insert, tendsto_sup]
  exact ⟨by simpa only [hT.1, one_apply_eq_self] using (tendsto_pure_nhds (fun t => T t x) (0 : ℝ)), hT.2.2 x⟩

theorem contraction_continuousOn (T : ℝ → X →L[𝕜] X)
    (hT : IsContractionSemigroup T) (x : X) : ContinuousOn (fun t => T t x) (Ici 0) := by
  intro t ht
  have ha' : Tendsto (fun s : ℝ => |s-t|) (𝓝[Ici 0] t) (𝓝[≥] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((continuous_id.sub (continuous_const (y := t))).abs.continuousAt (x := t)).tendsto.mono_left nhdsWithin_le_nhds
    · exact Eventually.of_forall (fun s => by simpa only [mem_Ici] using (abs_nonneg (s-t)))
  have hb : Tendsto (fun s : ℝ => T |s-t| x-x) (𝓝[Ici 0] t) (𝓝 (0 : X)) := by
    simpa only [sub_self, Function.comp_apply] using ((semigroup_tendsto_zero_ge T hT.1 x).comp ha').sub (tendsto_const_nhds (x := x))
  change Tendsto (fun s => T s x) (𝓝[Ici 0] t) (𝓝 (T t x))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _))
    ((show ∀ᶠ s in 𝓝[Ici 0] t, s ∈ Ici 0 from eventually_mem_nhdsWithin).mono
      (fun s hs => contraction_difference T hT hs ht x))
  simpa using hb.norm
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE SemigroupContinuity -/

/- BEGIN WHOLE MODULE WeightedOrbit -/
section
open Filter Set MeasureTheory
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

def extendedOrbit (T : ℝ → X →L[𝕜] X) (x : X) (t : ℝ) : X := T (max t 0) x

omit [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X] in
theorem extendedOrbit_continuous (T : ℝ → X →L[𝕜] X)
    (hT : IsContractionSemigroup T) (x : X) : Continuous (extendedOrbit T x) :=
  (contraction_continuousOn T hT x).comp_continuous
    (continuous_id.max continuous_const) (fun t => by change 0 ≤ max t 0; exact le_max_right _ _)

theorem weighted_orbit_translate (T : ℝ → X →L[𝕜] X)
    (hT : IsContractionSemigroup T) (v : X) (lam b h : ℝ) (hb : 0 ≤ b) (hh : 0 ≤ h) :
    T h (∫ s in (0:ℝ)..b, Real.exp (-lam*s) • extendedOrbit T v s) =
      Real.exp (lam*h) • ∫ s in h..(b+h), Real.exp (-lam*s) • extendedOrbit T v s := by
  let f : ℝ → X := fun s => Real.exp (-lam*s) • extendedOrbit T v s
  have hf : Continuous f := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (extendedOrbit_continuous T hT v)
  change T h (∫ s in (0:ℝ)..b, f s) = Real.exp (lam*h) • ∫ s in h..(b+h), f s
  have hshift := intervalIntegral.integral_comp_add_right f h (a := 0) (b := b)
  simp only [zero_add] at hshift
  rw [← hshift]
  rw [← intervalIntegral.integral_smul]
  rw [← (T h).intervalIntegral_comp_comm (hf.intervalIntegrable 0 b)]
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := (uIcc_of_le hb ▸ hs).1
  dsimp [f, extendedOrbit]
  rw [max_eq_left hs0, max_eq_left (by positivity : 0 ≤ s+h),
    (T h).map_smul_of_tower, semigroup_apply T hT.1 hs0 hh]
  rw [← semigroup_apply T hT.1 hs0 hh, add_comm s h, semigroup_apply T hT.1 hh hs0,
    smul_smul, ← Real.exp_add]
  congr 1
  congr 1
  ring

theorem weighted_orbit_derivative (T : ℝ → X →L[𝕜] X)
    (hT : IsContractionSemigroup T) (v : X) (lam b : ℝ) (hb : 0 ≤ b) :
    let y := ∫ s in (0:ℝ)..b, Real.exp (-lam*s) • extendedOrbit T v s
    Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h y-y)) (𝓝[>] 0)
      (𝓝 (lam • y + Real.exp (-lam*b) • T b v-v)) := by
  let f : ℝ → X := fun s => Real.exp (-lam*s) • extendedOrbit T v s
  let F : ℝ → X := fun t => ∫ s in (0:ℝ)..t, f s
  have hf : Continuous f := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    (extendedOrbit_continuous T hT v)
  have hF : ∀ t, HasDerivAt F (f t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hd : HasDerivAt (fun h : ℝ => Real.exp (lam*h) • (F (b+h)-F h))
      (lam • F b + f b-f 0) 0 := by
    have he := ((hasDerivAt_id (0:ℝ)).const_mul lam).exp
    have hg0 : HasDerivAt (fun h : ℝ => F (b+h)) (f b) 0 := by
      simpa only [add_zero, one_smul, Function.comp_def] using
        (hF (b+0)).scomp 0 ((hasDerivAt_id (0:ℝ)).const_add b)
    have hg := hg0.sub (hF 0)
    convert! he.smul hg using 1
    simp only [id_eq, mul_zero, Real.exp_zero, mul_one, one_mul, add_zero,
        show F 0 = 0 by simp [F], sub_zero, one_smul, Pi.sub_apply]
    abel
  have hl := hd.tendsto_slope_zero_right
  have hlim : Tendsto (fun h : ℝ => h⁻¹ •
      (Real.exp (lam*h) • (F (b+h)-F h)-F b)) (𝓝[>] 0)
      (𝓝 (lam • F b + Real.exp (-lam*b) • T b v-v)) := by
    simpa [f, F, extendedOrbit, max_eq_left hb, hT.1.1] using hl
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < h := hh
  have ht := weighted_orbit_translate T hT v lam b h hb hp.le
  have hi : F h + (∫ s in h..(b+h), f s) = F (b+h) :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable 0 h) (hf.intervalIntegrable h (b+h))
  have hi' : (∫ s in h..(b+h), f s) = F (b+h)-F h := by
    dsimp [F]; exact eq_sub_of_add_eq' hi
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  change _ = ((h⁻¹ : ℝ) : 𝕜) • (T h (F b)-F b)
  change T h (F b) = Real.exp (lam*h) • ∫ s in h..(b+h), f s at ht
  rw [ht, hi']
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE WeightedOrbit -/

/- BEGIN WHOLE MODULE DerivativeDissipative -/
section
open Filter Set
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem derivative_dissipative (T : ℝ → X →L[𝕜] X)
    (hT : ∀ t : ℝ, 0 ≤ t → ‖T t‖ ≤ 1) (x g : X)
    (hg : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h x-x))
      (𝓝[>] 0) (𝓝 g)) (lam : ℝ) (hlam : 0 < lam) :
    lam * ‖x‖ ≤ ‖(lam : 𝕜) • x-g‖ := by
  have he : ∀ᶠ h : ℝ in 𝓝[>] 0,
      lam * ‖x‖ ≤ ‖(lam : 𝕜) • x - ((h⁻¹ : ℝ) : 𝕜) • (T h x-x)‖ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hp : 0 < h := hh
    have hn : ‖T h x‖ ≤ ‖x‖ := (T h).le_opNorm x |>.trans (by
      nlinarith [hT h hp.le, norm_nonneg x])
    have hi : ((1+lam*h : ℝ) : 𝕜) • x = T h x + (h : 𝕜) •
        ((lam : 𝕜) • x - ((h⁻¹ : ℝ) : 𝕜) • (T h x-x)) := by
      simp only [smul_sub, smul_smul, RCLike.ofReal_inv, mul_inv_cancel₀
        (show (h : 𝕜) ≠ 0 by exact_mod_cast hp.ne'), one_smul]
      push_cast
      module
    have hb := norm_add_le (T h x) ((h : 𝕜) •
      ((lam : 𝕜) • x - ((h⁻¹ : ℝ) : 𝕜) • (T h x-x)))
    rw [← hi, norm_smul, RCLike.norm_ofReal, abs_of_pos (by positivity : 0 < 1+lam*h),
      norm_smul, RCLike.norm_ofReal, abs_of_pos hp] at hb
    nlinarith
  have hl := ((tendsto_const_nhds (x := (lam : 𝕜) • x)).sub hg).norm
  exact ge_of_tendsto hl he

theorem generator_dissipative (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    (A : X →ₗ.[𝕜] X) (hA : IsGenerator T A) : IsDissipative A := by
  intro lam hlam x
  exact derivative_dissipative T hT.2 x (A x) ((hA x (A x)).mpr ⟨x.property,rfl⟩) lam hlam
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE DerivativeDissipative -/

/- BEGIN WHOLE MODULE ResolventBounds -/
section
open Filter
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

noncomputable def shiftedMap (A : X →ₗ.[𝕜] X) (lam : ℝ) : A.domain →ₗ[𝕜] X :=
  (lam : 𝕜) • A.domain.subtype - A.toFun

@[simp] theorem shiftedMap_apply (A : X →ₗ.[𝕜] X) (lam : ℝ) (x : A.domain) :
    shiftedMap A lam x = (lam : 𝕜) • (x : X) - A x := rfl

theorem shiftedMap_injective (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    {lam : ℝ} (hlam : 0 < lam) : Function.Injective (shiftedMap A lam) := by
  intro x y hxy
  have h := hA lam hlam (x - y)
  have hz : shiftedMap A lam (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  change lam * ‖((x - y : A.domain) : X)‖ ≤ ‖shiftedMap A lam (x - y)‖ at h
  rw [hz, norm_zero] at h
  have : ‖((x - y : A.domain) : X)‖ = 0 := by nlinarith [norm_nonneg ((x - y : A.domain) : X)]
  apply sub_eq_zero.mp
  apply Subtype.ext
  exact norm_eq_zero.mp this

noncomputable def resolventEquiv (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) :
    A.domain ≃ₗ[𝕜] X :=
  LinearEquiv.ofBijective (shiftedMap A lam) ⟨shiftedMap_injective A hA hlam, hs⟩

noncomputable def resolventLinear (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) : X →ₗ[𝕜] X :=
  A.domain.subtype.comp (resolventEquiv A hA lam hlam hs).symm.toLinearMap

theorem resolventLinear_bound (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) (x : X) :
    ‖resolventLinear A hA lam hlam hs x‖ ≤ lam⁻¹ * ‖x‖ := by
  have h := hA lam hlam ((resolventEquiv A hA lam hlam hs).symm x)
  have he : shiftedMap A lam ((resolventEquiv A hA lam hlam hs).symm x) = x :=
    (resolventEquiv A hA lam hlam hs).apply_symm_apply x
  change lam * ‖resolventLinear A hA lam hlam hs x‖ ≤
    ‖shiftedMap A lam ((resolventEquiv A hA lam hlam hs).symm x)‖ at h
  rw [he] at h
  exact (le_inv_mul_iff₀ hlam).2 h

noncomputable def resolventCLM (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) : X →L[𝕜] X :=
  (resolventLinear A hA lam hlam hs).mkContinuous lam⁻¹
    (resolventLinear_bound A hA lam hlam hs)

theorem resolventCLM_bound (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) (x : X) :
    ‖resolventCLM A hA lam hlam hs x‖ ≤ lam⁻¹ * ‖x‖ :=
  resolventLinear_bound A hA lam hlam hs x

theorem resolventCLM_norm (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) :
    ‖resolventCLM A hA lam hlam hs‖ ≤ lam⁻¹ :=
  ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr hlam.le)
    (resolventCLM_bound A hA lam hlam hs)

theorem resolventCLM_mem (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) (x : X) :
    resolventCLM A hA lam hlam hs x ∈ A.domain :=
  ((resolventEquiv A hA lam hlam hs).symm x).property

theorem resolventCLM_right (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) (x : X) :
    (lam : 𝕜) • resolventCLM A hA lam hlam hs x -
      A ⟨_, resolventCLM_mem A hA lam hlam hs x⟩ = x :=
  (resolventEquiv A hA lam hlam hs).apply_symm_apply x

theorem resolventCLM_left (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam : ℝ) (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) (x : A.domain) :
    resolventCLM A hA lam hlam hs ((lam : 𝕜) • (x : X) - A x) = x :=
  congrArg Subtype.val ((resolventEquiv A hA lam hlam hs).symm_apply_apply x)

theorem resolventCLM_identity (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hs : Function.Surjective (shiftedMap A lam))
    (ht : Function.Surjective (shiftedMap A mu)) (x : X) :
    resolventCLM A hA lam hlam hs x - resolventCLM A hA mu hmu ht x =
      ((mu - lam : ℝ) : 𝕜) •
        resolventCLM A hA lam hlam hs (resolventCLM A hA mu hmu ht x) := by
  let R := resolventCLM A hA lam hlam hs
  let S := resolventCLM A hA mu hmu ht
  have hr := resolventCLM_left A hA lam hlam hs
    ⟨S x, resolventCLM_mem A hA mu hmu ht x⟩
  have ht' := resolventCLM_right A hA mu hmu ht x
  change (mu : 𝕜) • S x - A ⟨S x, _⟩ = x at ht'
  have he : (lam : 𝕜) • S x - A ⟨S x, resolventCLM_mem A hA mu hmu ht x⟩ =
      x + ((lam - mu : ℝ) : 𝕜) • S x := by
    rw [RCLike.ofReal_sub]
    calc
      (lam : 𝕜) • S x - A ⟨S x, _⟩ =
        ((mu : 𝕜) • S x - A ⟨S x, _⟩) + ((lam : 𝕜) - mu) • S x := by module
      _ = _ := by rw [ht']
  change R ((lam : 𝕜) • S x - A ⟨S x, _⟩) = S x at hr
  rw [he, map_add, map_smul] at hr
  change R x - S x = ((mu - lam : ℝ) : 𝕜) • R (S x)
  calc
    R x - S x = R x - (R x + ((lam - mu : ℝ) : 𝕜) • R (S x)) :=
      congrArg (fun v => R x - v) hr.symm
    _ = _ := by rw [RCLike.ofReal_sub, RCLike.ofReal_sub]; module

theorem resolventCLM_commute (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    (lam mu : ℝ) (hlam : 0 < lam) (hmu : 0 < mu)
    (hs : Function.Surjective (shiftedMap A lam))
    (ht : Function.Surjective (shiftedMap A mu)) :
    Commute (resolventCLM A hA lam hlam hs) (resolventCLM A hA mu hmu ht) := by
  by_cases heq : lam = mu
  · subst mu
    exact Commute.refl _
  · apply ContinuousLinearMap.ext
    intro x
    have h1 := resolventCLM_identity A hA lam mu hlam hmu hs ht x
    have h2 := resolventCLM_identity A hA mu lam hmu hlam ht hs x
    have hn : ((mu - lam : ℝ) : 𝕜) ≠ 0 := by
      exact_mod_cast sub_ne_zero.mpr (Ne.symm heq)
    apply (smul_right_injective _ hn)
    change ((mu - lam : ℝ) : 𝕜) •
        resolventCLM A hA lam hlam hs (resolventCLM A hA mu hmu ht x) =
      ((mu - lam : ℝ) : 𝕜) •
        resolventCLM A hA mu hmu ht (resolventCLM A hA lam hlam hs x)
    rw [← h1]
    have hc : ((mu - lam : ℝ) : 𝕜) = -((lam - mu : ℝ) : 𝕜) := by push_cast; ring
    rw [hc, neg_smul, ← h2]
    abel

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ResolventBounds -/

/- BEGIN WHOLE MODULE ResolventClosed -/
section
open Set
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem mdissipative_closed (A : X →ₗ.[𝕜] X) (hA : IsMDissipative A) : A.IsClosed := by
  obtain ⟨hd,lam,hp,hs⟩ := hA
  let R := resolventCLM A hd lam hp hs
  have he : (A.graph : Set (X × X)) = {p | R ((lam : 𝕜) • p.1-p.2) = p.1} := by
    ext p
    change p ∈ A.graph ↔ R ((lam : 𝕜) • p.1-p.2) = p.1
    rw [LinearPMap.mem_graph_iff']
    constructor
    · rintro ⟨y,rfl⟩
      exact resolventCLM_left A hd lam hp hs y
    · intro hx
      have hm : p.1 ∈ A.domain := by rw [← hx]; exact resolventCLM_mem A hd lam hp hs _
      refine ⟨⟨p.1,hm⟩,?_⟩
      have hr := resolventCLM_right A hd lam hp hs ((lam : 𝕜) • p.1-p.2)
      change (lam : 𝕜) • R ((lam : 𝕜) • p.1-p.2) - A ⟨R ((lam : 𝕜) • p.1-p.2),_⟩ = _ at hr
      have hy : A ⟨p.1,hm⟩ = p.2 := by simpa only [hx, sub_right_inj] using hr
      exact Prod.ext rfl hy
  change IsClosed (A.graph : Set (X × X))
  rw [he]
  exact isClosed_eq (R.continuous.comp ((continuous_const.smul continuous_fst).sub continuous_snd)) continuous_fst
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ResolventClosed -/

/- BEGIN WHOLE MODULE SemigroupNecessity -/
section
open Filter Set MeasureTheory
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

theorem generator_dense (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    (A : X →ₗ.[𝕜] X) (hA : IsGenerator T A) : Dense (A.domain : Set X) := by
  intro x
  let f := extendedOrbit T x
  have hf : Continuous f := extendedOrbit_continuous T hT x
  have hd : HasDerivAt (fun h => ∫ s in (0:ℝ)..h, f s) x 0 := by
    have := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 0)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter (hf.continuousAt (x := 0))
    simpa [f,extendedOrbit,hT.1.1] using this
  have hl : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • ∫ s in (0:ℝ)..h, f s)
      (𝓝[>] 0) (𝓝 x) := by
    simpa [RCLike.real_smul_eq_coe_smul (K := 𝕜)] using hd.tendsto_slope_zero_right
  apply mem_closure_of_tendsto hl
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 < h := hh
  have hder := weighted_orbit_derivative T hT x 0 h hp.le
  simp only [neg_zero, zero_mul, Real.exp_zero, one_smul, zero_smul, zero_add] at hder
  obtain ⟨hm,_⟩ := (hA _ _).mp hder
  exact A.domain.smul_mem _ hm

theorem generator_surjective_one (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    (A : X →ₗ.[𝕜] X) (hA : IsGenerator T A) :
    Function.Surjective (fun x : A.domain => (x : X)-A x) := by
  have hn : ‖(Real.exp (-1) : ℝ) • T 1‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      Real.exp (-1) * ‖T 1‖ ≤ Real.exp (-1) * 1 :=
        mul_le_mul_of_nonneg_left (hT.2 1 (by norm_num)) (Real.exp_pos _).le
      _ < 1 := by simp
  obtain ⟨u,hu⟩ := isUnit_one_sub_of_norm_lt_one hn
  intro g
  let v := (↑u⁻¹ : X →L[𝕜] X) g
  have hv : v-Real.exp (-1) • T 1 v = g := by
    change (1-Real.exp (-1) • T 1) v = g
    rw [← hu]
    change ((↑u : X →L[𝕜] X) * ↑u⁻¹) g = g
    simp
  let y := ∫ s in (0:ℝ)..1, Real.exp (-s) • extendedOrbit T v s
  have hd := weighted_orbit_derivative T hT v 1 1 (by norm_num)
  simp only [neg_mul, one_mul, neg_mul, mul_one, one_smul] at hd
  obtain ⟨hm,he⟩ := (hA y (y+Real.exp (-1) • T 1 v-v)).mp hd
  refine ⟨⟨y,hm⟩,?_⟩
  change y-A ⟨y,hm⟩ = g
  rw [he]
  calc
    y-(y+Real.exp (-1) • T 1 v-v) = v-Real.exp (-1) • T 1 v := by abel
    _ = g := hv

theorem semigroup_necessity (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    (A : X →ₗ.[𝕜] X) (hA : IsGenerator T A) :
    (A.IsClosed ∧ Dense (A.domain : Set X)) ∧ IsMDissipative A := by
  have hm : IsMDissipative A := ⟨generator_dissipative T hT A hA,1,by norm_num,by
    simpa only [RCLike.ofReal_one, one_smul] using generator_surjective_one T hT A hA⟩
  exact ⟨⟨mdissipative_closed A hm,generator_dense T hT A hA⟩,hm⟩
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE SemigroupNecessity -/

/- BEGIN WHOLE MODULE ResolventSequence -/
section
open Filter
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

theorem shiftedMap_surjective_near (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    {lam mu : ℝ} (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam))
    (hnear : |lam - mu| < lam) : Function.Surjective (shiftedMap A mu) := by
  let R := resolventCLM A hA lam hlam hs
  have hR : ‖R‖ ≤ lam⁻¹ := resolventCLM_norm A hA lam hlam hs
  have hnorm : ‖((lam - mu : ℝ) : 𝕜) • R‖ < 1 := by
    rw [norm_smul, RCLike.norm_ofReal]
    calc
      |lam - mu| * ‖R‖ ≤ |lam - mu| * lam⁻¹ := mul_le_mul_of_nonneg_left hR (abs_nonneg _)
      _ < 1 := by rw [← div_eq_mul_inv, div_lt_one hlam]; exact hnear
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hnorm
  intro g
  let y := (↑u⁻¹ : X →L[𝕜] X) g
  have hy : (1 - ((lam - mu : ℝ) : 𝕜) • R) y = g := by
    rw [← hu]
    change ((↑u : X →L[𝕜] X) * ↑u⁻¹) g = g
    simp
  refine ⟨⟨R y, resolventCLM_mem A hA lam hlam hs y⟩, ?_⟩
  have hr := resolventCLM_right A hA lam hlam hs y
  change (lam : 𝕜) • R y - A ⟨R y, _⟩ = y at hr
  change y - ((lam - mu : ℝ) : 𝕜) • R y = g at hy
  change (mu : 𝕜) • R y - A ⟨R y, _⟩ = g
  rw [RCLike.ofReal_sub] at hy
  calc
    (mu : 𝕜) • R y - A ⟨R y, _⟩ =
      ((lam : 𝕜) • R y - A ⟨R y, _⟩) - ((lam : 𝕜) - mu) • R y := by module
    _ = g := by rw [hr]; exact hy

theorem shiftedMap_surjective_geometric (A : X →ₗ.[𝕜] X) (hA : IsDissipative A)
    {lam : ℝ} (hlam : 0 < lam) (hs : Function.Surjective (shiftedMap A lam)) (n : ℕ) :
    Function.Surjective (shiftedMap A ((3 / 2 : ℝ)^n * lam)) := by
  induction n with
  | zero => simpa using hs
  | succ n ih =>
      apply shiftedMap_surjective_near A hA (mul_pos (pow_pos (by norm_num) _) hlam) ih
      rw [pow_succ]
      have hn : 0 < (3 / 2 : ℝ)^n * lam := mul_pos (pow_pos (by norm_num) _) hlam
      rw [abs_of_nonpos (by nlinarith [pow_pos (show (0 : ℝ) < 3 / 2 by norm_num) n])]
      nlinarith

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ResolventSequence -/

/- BEGIN WHOLE MODULE DenseStrongLimit -/
section
open Filter
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem strong_identity_of_dense (F : ℕ → X →L[𝕜] X)
    (hF : ∀ n x, ‖F n x‖ ≤ ‖x‖) (s : Set X) (hs : Dense s)
    (hlim : ∀ x ∈ s, Tendsto (fun n => F n x) atTop (𝓝 x)) (x : X) :
    Tendsto (fun n => F n x) atTop (𝓝 x) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hs.exists_dist_lt x (show 0 < ε / 3 by positivity)
  have hev := (Metric.tendsto_nhds.mp (hlim y hy)) (ε / 3) (by positivity)
  filter_upwards [hev] with n hn
  have hc : dist (F n x) (F n y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using hF n (x - y)
  have hxy' : dist y x < ε / 3 := by simpa only [dist_comm] using hxy
  calc
    dist (F n x) x ≤ dist (F n x) (F n y) + dist (F n y) y + dist y x :=
      by linarith [dist_triangle (F n x) (F n y) x, dist_triangle (F n y) y x]
    _ < ε := by linarith

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE DenseStrongLimit -/

/- BEGIN WHOLE MODULE ResolventStrong -/
section
open Filter
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem strong_scaled_resolvent (A : X →ₗ.[𝕜] X) (hd : Dense (A.domain : Set X))
    (l : ℕ → ℝ) (hl : ∀ n, 0 < l n) (hlinf : Tendsto l atTop atTop)
    (R : ℕ → X →L[𝕜] X) (hR : ∀ n x, ‖R n x‖ ≤ (l n)⁻¹ * ‖x‖)
    (hleft : ∀ n (x : A.domain), R n ((l n : 𝕜) • (x : X) - A x) = x) (x : X) :
    Tendsto (fun n => (l n : 𝕜) • R n x) atTop (𝓝 x) := by
  let F : ℕ → X →L[𝕜] X := fun n => (l n : 𝕜) • R n
  have hF : ∀ n x, ‖F n x‖ ≤ ‖x‖ := by
    intro n x
    change ‖(l n : 𝕜) • R n x‖ ≤ ‖x‖
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (hl n)]
    calc
      l n * ‖R n x‖ ≤ l n * ((l n)⁻¹ * ‖x‖) := mul_le_mul_of_nonneg_left (hR n x) (hl n).le
      _ = ‖x‖ := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (hl n)), one_mul]
  apply strong_identity_of_dense F hF (A.domain : Set X) hd
  intro y hy
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he : ∀ n, F n y - y = R n (A ⟨y, hy⟩) := by
    intro n
    have h := hleft n ⟨y, hy⟩
    rw [map_sub, map_smul] at h
    change F n y - R n (A ⟨y, hy⟩) = y at h
    exact (sub_eq_iff_eq_add.mpr ((sub_eq_iff_eq_add.mp h).trans (add_comm _ _)))
  simp_rw [he]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hR n (A ⟨y, hy⟩))
    (by simpa using (tendsto_inv_atTop_zero.comp hlinf).mul_const ‖A ⟨y, hy⟩‖)

theorem yosida_tendsto (A : X →ₗ.[𝕜] X) (hd : Dense (A.domain : Set X))
    (l : ℕ → ℝ) (hl : ∀ n, 0 < l n) (hlinf : Tendsto l atTop atTop)
    (R : ℕ → X →L[𝕜] X) (hR : ∀ n x, ‖R n x‖ ≤ (l n)⁻¹ * ‖x‖)
    (hleft : ∀ n (x : A.domain), R n ((l n : 𝕜) • (x : X) - A x) = x)
    (x : A.domain) :
    Tendsto (fun n => (((l n)^2 : ℝ) : 𝕜) • R n (x : X) - (l n : 𝕜) • (x : X))
      atTop (𝓝 (A x)) := by
  convert strong_scaled_resolvent A hd l hl hlinf R hR hleft (A x) using 1
  funext n
  have h := hleft n x
  rw [map_sub, map_smul] at h
  have he : (l n : 𝕜) • R n (x : X) - (x : X) = R n (A x) := by
    calc
      (l n : 𝕜) • R n (x : X) - (x : X) =
        (l n : 𝕜) • R n (x : X) - ((l n : 𝕜) • R n (x : X) - R n (A x)) :=
          congrArg (fun v => (l n : 𝕜) • R n (x : X) - v) h.symm
      _ = _ := by abel
  calc
    (((l n)^2 : ℝ) : 𝕜) • R n (x : X) - (l n : 𝕜) • (x : X) =
        (l n : 𝕜) • ((l n : 𝕜) • R n (x : X) - (x : X)) := by
          push_cast
          module
    _ = _ := by rw [he]

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ResolventStrong -/

/- BEGIN WHOLE MODULE OperatorExponential -/
section
open Filter
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

noncomputable local instance : NormedAlgebra ℝ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℝ 𝕜 (X →L[𝕜] X)

omit [CompleteSpace X] in
theorem operator_exp_norm_le (B : X →L[𝕜] X) :
    ‖NormedSpace.exp B‖ ≤ Real.exp ‖B‖ := by
  rw [NormedSpace.exp_eq_tsum 𝕜]
  have hs := NormedSpace.norm_expSeries_summable' (𝕂 := 𝕜) B
  calc
    ‖∑' n : ℕ, ((n.factorial : 𝕜)⁻¹) • B^n‖ ≤
        ∑' n : ℕ, ‖((n.factorial : 𝕜)⁻¹) • B^n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) * ‖B‖^n := by
      apply Summable.tsum_le_tsum _ hs
      · simpa only [smul_eq_mul] using
          NormedSpace.expSeries_summable' (𝕂 := ℝ) ‖B‖
      · intro n
        rw [norm_smul, norm_inv, RCLike.norm_natCast]
        have hp : ‖B^n‖ ≤ ‖B‖^n := by
          rcases n with _ | n
          · simp only [pow_zero]
            exact ContinuousLinearMap.norm_id_le
          · exact norm_pow_le' B (Nat.succ_pos n)
        exact mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = Real.exp ‖B‖ := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum ℝ]
      rfl

omit [CompleteSpace X] in
theorem operator_exp_real_one (t : ℝ) :
    NormedSpace.exp ((t : 𝕜) • (1 : X →L[𝕜] X)) = (Real.exp t : 𝕜) • (1 : X →L[𝕜] X) := by
  change NormedSpace.exp (algebraMap ℝ (X →L[𝕜] X) t) =
    algebraMap ℝ (X →L[𝕜] X) (Real.exp t)
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.algebraMap_exp_comm t).symm

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE OperatorExponential -/

/- BEGIN WHOLE MODULE YosidaExponential -/
section
namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

noncomputable local instance : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 (X →L[𝕜] X)

theorem exp_sub_scalar_norm_le (B : X →L[𝕜] X) (c : ℝ) :
    ‖NormedSpace.exp (B - (c : 𝕜) • 1)‖ ≤ Real.exp (‖B‖ - c) := by
  have hc : Commute B (((-c : ℝ) : 𝕜) • (1 : X →L[𝕜] X)) := by
    exact (Commute.one_right B).smul_right _
  have he : B - (c : 𝕜) • (1 : X →L[𝕜] X) = B + ((-c : ℝ) : 𝕜) • 1 := by
    simp only [RCLike.ofReal_neg, neg_smul, sub_eq_add_neg]
  rw [he, NormedSpace.exp_add_of_commute hc, operator_exp_real_one]
  have hb : ‖(Real.exp (-c) : 𝕜) • (1 : X →L[𝕜] X)‖ ≤ Real.exp (-c) := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (ContinuousLinearMap.norm_id_le)
  calc
    ‖NormedSpace.exp B * ((Real.exp (-c) : 𝕜) • 1)‖ ≤
        ‖NormedSpace.exp B‖ * ‖(Real.exp (-c) : 𝕜) • (1 : X →L[𝕜] X)‖ := norm_mul_le _ _
    _ ≤ Real.exp ‖B‖ * Real.exp (-c) :=
      mul_le_mul (operator_exp_norm_le B) hb (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (‖B‖ - c) := by rw [← Real.exp_add]; rfl

theorem yosida_exp_contraction (R : X →L[𝕜] X) {l : ℝ} (hl : 0 < l)
    (hR : ‖R‖ ≤ l⁻¹) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : 𝕜) • (((l^2 : ℝ) : 𝕜) • R - (l : 𝕜) • 1))‖ ≤ 1 := by
  have he : (t : 𝕜) • (((l^2 : ℝ) : 𝕜) • R - (l : 𝕜) • (1 : X →L[𝕜] X)) =
      ((t*l^2 : ℝ) : 𝕜) • R - ((t*l : ℝ) : 𝕜) • 1 := by
    push_cast
    module
  rw [he]
  apply (exp_sub_scalar_norm_le _ (t*l)).trans
  apply Real.exp_le_one_iff.mpr
  have hb : ‖((t*l^2 : ℝ) : 𝕜) • R‖ ≤ t*l := by
    rw [norm_smul, RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    calc
      t*l^2*‖R‖ ≤ t*l^2*l⁻¹ := mul_le_mul_of_nonneg_left hR (by positivity)
      _ = t*l := by field_simp
  linarith

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE YosidaExponential -/

/- BEGIN WHOLE MODULE YosidaApproximation -/
section
open Filter
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]

theorem exists_yosida_sequence (A : X →ₗ.[𝕜] X) (hd : Dense (A.domain : Set X))
    (hA : IsMDissipative A) :
    ∃ B : ℕ → X →L[𝕜] X,
      (∀ n m, Commute (B n) (B m)) ∧
      (∀ (n : ℕ) (t : ℝ), 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • B n)‖ ≤ 1) ∧
      (∀ x : A.domain, Tendsto (fun n => B n x) atTop (𝓝 (A x))) := by
  obtain ⟨hdis, l, hl, hs⟩ := hA
  let v : ℕ → ℝ := fun n => (3/2 : ℝ)^n*l
  have hv : ∀ n, 0 < v n := fun n => mul_pos (pow_pos (by norm_num) n) hl
  have hsur : ∀ n, Function.Surjective (shiftedMap A (v n)) :=
    shiftedMap_surjective_geometric A hdis hl hs
  let R : ℕ → X →L[𝕜] X := fun n => resolventCLM A hdis (v n) (hv n) (hsur n)
  let B : ℕ → X →L[𝕜] X := fun n => (((v n)^2 : ℝ) : 𝕜) • R n - (v n : 𝕜) • 1
  refine ⟨B, ?_, ?_, ?_⟩
  · intro n m
    have hc : Commute (R n) (R m) :=
      resolventCLM_commute A hdis (v n) (v m) (hv n) (hv m) (hsur n) (hsur m)
    exact ((hc.smul_left _).smul_right _).sub_right
      ((Commute.one_right _).smul_right _) |>.sub_left
        (((Commute.one_left _).smul_left _).sub_right
          ((Commute.one_left _).smul_left _))
  · intro n t ht
    exact yosida_exp_contraction (R n) (hv n)
      (resolventCLM_norm A hdis (v n) (hv n) (hsur n)) ht
  · intro x
    have hvlim : Tendsto v atTop atTop :=
      (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 3/2 by norm_num)).atTop_mul_const hl
    exact yosida_tendsto A hd v hv hvlim R
      (fun n => resolventCLM_bound A hdis (v n) (hv n) (hsur n))
      (fun n => resolventCLM_left A hdis (v n) (hv n) (hsur n)) x

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE YosidaApproximation -/

/- BEGIN WHOLE MODULE ExponentialOrbit -/
section
open Filter Set
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

noncomputable local instance : NormedAlgebra ℝ (X →L[𝕜] X) :=
  { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
noncomputable local instance : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ ℝ (X →L[𝕜] X)

theorem operator_exp_hasDerivAt (B : X →L[𝕜] X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : 𝕜) • B))
      (NormedSpace.exp ((t : 𝕜) • B) * B) t := by
  simpa only [RCLike.real_smul_eq_coe_smul (K := 𝕜)] using
    (hasDerivAt_exp_smul_const B t)

theorem operator_exp_orbit_hasDerivAt (B : X →L[𝕜] X) (x : X) (t : ℝ) :
    HasDerivAt (fun s : ℝ => NormedSpace.exp ((s : 𝕜) • B) x)
      (NormedSpace.exp ((t : 𝕜) • B) (B x)) t := by
  exact ((ContinuousLinearMap.apply 𝕜 X x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (operator_exp_hasDerivAt B t)

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ExponentialOrbit -/

/- BEGIN WHOLE MODULE DuhamelBound -/
section
open Filter Set
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

noncomputable local instance : NormedAlgebra ℝ (X →L[𝕜] X) :=
  { ContinuousLinearMap.toNormedSpace, ContinuousLinearMap.algebra with }
noncomputable local instance : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ ℝ (X →L[𝕜] X)

theorem duhamel_difference_bound (B C : X →L[𝕜] X) (hBC : Commute B C)
    (hB : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • B)‖ ≤ 1)
    (hC : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • C)‖ ≤ 1)
    (x : X) {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp ((t : 𝕜) • C) x - NormedSpace.exp ((t : 𝕜) • B) x‖ ≤
      t * ‖C x - B x‖ := by
  let F : ℝ → X →L[𝕜] X := fun s =>
    NormedSpace.exp (((t-s : ℝ) : 𝕜) • B) * NormedSpace.exp ((s : 𝕜) • C)
  have hder : ∀ s : ℝ, HasDerivAt (fun r => F r x) (F s (C x - B x)) s := by
    intro s
    have h1 := (operator_exp_hasDerivAt B (t-s)).scomp s ((hasDerivAt_id s).const_sub t)
    have h2 := operator_exp_hasDerivAt C s
    have hp := h1.mul h2
    have hc : Commute B (NormedSpace.exp ((s : 𝕜) • C)) := (hBC.smul_right _).exp_right
    have he :
        (-1 : ℝ) • (NormedSpace.exp (((t-s : ℝ) : 𝕜) • B) * B) *
            NormedSpace.exp ((s : 𝕜) • C) +
          NormedSpace.exp (((t-s : ℝ) : 𝕜) • B) *
            (NormedSpace.exp ((s : 𝕜) • C) * C) = F s * (C - B) := by
      rw [neg_one_smul]
      dsimp [F]
      calc
        _ = NormedSpace.exp (((t-s : ℝ) : 𝕜) • B) *
          (NormedSpace.exp ((s : 𝕜) • C) * C - B * NormedSpace.exp ((s : 𝕜) • C)) := by noncomm_ring
        _ = _ := by rw [hc.eq]; noncomm_ring
    have hv := ((ContinuousLinearMap.apply 𝕜 X x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s hp
    convert hv using 1
    · rfl
    · exact congrArg (fun L : X →L[𝕜] X => L x) he.symm
  have hnorm : ∀ s ∈ Ico 0 t, ‖F s (C x - B x)‖ ≤ ‖C x - B x‖ := by
    intro s hs
    dsimp [F]
    change ‖NormedSpace.exp (((t-s : ℝ) : 𝕜) • B)
      (NormedSpace.exp ((s : 𝕜) • C) (C x - B x))‖ ≤ _
    calc
      _ ≤ ‖NormedSpace.exp ((s : 𝕜) • C) (C x - B x)‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hB (t-s) (by linarith [hs.2])))
      _ ≤ ‖C x - B x‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_of_le_one_left (norm_nonneg _) (hC s hs.1))
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun s (_ : s ∈ Icc 0 t) => (hder s).hasDerivWithinAt) hnorm t ⟨ht, le_rfl⟩
  simpa [F, mul_comm] using h

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE DuhamelBound -/

/- BEGIN WHOLE MODULE SemigroupOrbit -/
section
open Filter Set MeasureTheory
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

theorem orbit_right_derivative (T : ℝ → X →L[𝕜] X) (hT : IsC0Semigroup T)
    (x g : X) (hg : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h x-x))
      (𝓝[>] 0) (𝓝 g)) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => T s x) (T t g) (Ioi t) t := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mpr
  have hs : Tendsto (fun s : ℝ => s-t) (𝓝[>] t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using ((tendsto_id : Tendsto (fun s : ℝ => s) (𝓝 t) (𝓝 t)).sub_const t).mono_left nhdsWithin_le_nhds
    · exact (show ∀ᶠ s in 𝓝[>] t, s ∈ Ioi t from self_mem_nhdsWithin).mono (fun s hs => by change 0 < s-t; exact sub_pos.mpr hs)
  have hh := (T t).continuous.tendsto g |>.comp (hg.comp hs)
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_apply, slope_def_module, RCLike.real_smul_eq_coe_smul (K := 𝕜),
    map_smul, map_sub]
  rw [← semigroup_apply T hT ht (sub_nonneg.mpr (le_of_lt hs))]
  simp only [add_sub_cancel]

theorem orbit_integral_identity [CompleteSpace X] (T : ℝ → X →L[𝕜] X)
    (hT : IsContractionSemigroup T) (x g : X)
    (hg : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h x-x)) (𝓝[>] 0) (𝓝 g))
    {t : ℝ} (ht : 0 ≤ t) : T t x-x = ∫ s in (0:ℝ)..t, T s g := by
  have hc := contraction_continuousOn T hT x
  have hd := contraction_continuousOn T hT g
  have hi : IntervalIntegrable (fun s => T s g) volume 0 t :=
    (hd.mono (by intro s hs; exact hs.1)).intervalIntegrable_of_Icc ht
  simpa only [hT.1.1, one_apply_eq_self] using
    (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
      (hc.mono (by intro s hs; exact hs.1))
      (fun s hs => orbit_right_derivative T hT.1 x g hg hs.1.le) hi).symm
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE SemigroupOrbit -/

/- BEGIN WHOLE MODULE ExponentialSemigroup -/
section
open Filter Set MeasureTheory
open scoped Topology

namespace HunterPDE.Semigroup.Proof

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X]
  [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X]

noncomputable local instance : NormedAlgebra ℚ (X →L[𝕜] X) :=
  NormedAlgebra.restrictScalars ℚ 𝕜 (X →L[𝕜] X)

theorem operator_exp_isContractionSemigroup (B : X →L[𝕜] X)
    (hB : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • B)‖ ≤ 1) :
    IsContractionSemigroup (fun t : ℝ => NormedSpace.exp ((t : 𝕜) • B)) := by
  refine ⟨⟨?_, ?_, ?_⟩, hB⟩
  · simp
  · intro s t _ _
    rw [← NormedSpace.exp_add_of_commute (((Commute.refl B).smul_left _).smul_right _)]
    congr 1
    push_cast
    module
  · intro x
    have h := (operator_exp_orbit_hasDerivAt B x 0).continuousAt.tendsto
    simpa using h.mono_left nhdsWithin_le_nhds

theorem operator_exp_orbit_integral (B : X →L[𝕜] X)
    (hB : ∀ t : ℝ, 0 ≤ t → ‖NormedSpace.exp ((t : 𝕜) • B)‖ ≤ 1)
    (x : X) {t : ℝ} (ht : 0 ≤ t) :
    NormedSpace.exp ((t : 𝕜) • B) x - x =
      ∫ s in (0:ℝ)..t, NormedSpace.exp ((s : 𝕜) • B) (B x) := by
  apply orbit_integral_identity _ (operator_exp_isContractionSemigroup B hB) x (B x) _ ht
  have h := (operator_exp_orbit_hasDerivAt B x 0).tendsto_slope_zero_right
  simpa only [zero_add, RCLike.ofReal_zero, zero_smul, NormedSpace.exp_zero,
    one_apply_eq_self, RCLike.real_smul_eq_coe_smul (K := 𝕜)] using h

end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ExponentialSemigroup -/

/- BEGIN WHOLE MODULE UniformContractionCauchy -/
section
open Filter Set
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem uniform_cauchy_of_dense (F : ℕ → ℝ → X →L[𝕜] X)
    (hF : ∀ n t, 0 ≤ t → ∀ x, ‖F n t x‖ ≤ ‖x‖)
    (K : Submodule 𝕜 X) (hK : Dense (K : Set X)) (B : ℕ → X →L[𝕜] X)
    (hB : ∀ x : K, CauchySeq (fun n => B n x))
    (hd : ∀ n m t, 0 ≤ t → ∀ x : K,
      ‖F n t x-F m t x‖ ≤ t*‖B n x-B m x‖) (x : X) (b : ℝ) (hb : 0 ≤ b) :
    UniformCauchySeqOn (fun n t => F n t x) atTop (Icc 0 b) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  obtain ⟨y,hy,hxy⟩ := hK.exists_dist_lt x (show 0 < ε/4 by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (hB ⟨y,hy⟩) (ε/(2*(b+1))) (by positivity)
  refine ⟨N,fun m hm n hn t ht => ?_⟩
  have h1 : dist (F m t x) (F m t y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using hF m t ht.1 (x-y)
  have h2 : dist (F n t y) (F n t x) ≤ dist x y := by
    rw [dist_comm (F n t y) (F n t x)]
    simpa only [dist_eq_norm, ← map_sub] using hF n t ht.1 (x-y)
  have h3 : dist (F m t y) (F n t y) < ε/2 := by
    have hmn := hN m hm n hn
    rw [dist_eq_norm] at hmn ⊢
    have hb1 : 0 < b+1 := by positivity
    have hbound : ‖B m y-B n y‖*(2*(b+1)) < ε :=
      (lt_div_iff₀ (by positivity)).mp hmn
    have hh := hd m n t ht.1 ⟨y,hy⟩
    have hnon := norm_nonneg (B m y-B n y)
    nlinarith [mul_nonneg (show 0 ≤ b-t by linarith [ht.2]) hnon]
  calc
    dist (F m t x) (F n t x) ≤ dist (F m t x) (F m t y) +
      dist (F m t y) (F n t y) + dist (F n t y) (F n t x) := by
        linarith [dist_triangle (F m t x) (F m t y) (F n t x),
          dist_triangle (F m t y) (F n t y) (F n t x)]
    _ < ε := by linarith
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE UniformContractionCauchy -/

/- BEGIN WHOLE MODULE ContractionLimit -/
section
open Filter Set
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem exists_contraction_limit (F : ℕ → ℝ → X →L[𝕜] X)
    (hF : ∀ n t, 0 ≤ t → ∀ x, ‖F n t x‖ ≤ ‖x‖)
    (hc : ∀ t, 0 ≤ t → ∀ x, CauchySeq (fun n => F n t x)) :
    ∃ T : ℝ → X →L[𝕜] X,
      (∀ t, 0 ≤ t → ∀ x, Tendsto (fun n => F n t x) atTop (𝓝 (T t x))) ∧
      ∀ t, ‖T t‖ ≤ 1 := by
  let f : ℝ → X → X := fun t x => limUnder atTop (fun n => F n (max t 0) x)
  have hf : ∀ t x, Tendsto (fun n => F n (max t 0) x) atTop (𝓝 (f t x)) :=
    fun t x => (hc (max t 0) (le_max_right _ _) x).tendsto_limUnder
  have hn : ∀ t x, ‖f t x‖ ≤ ‖x‖ := fun t x =>
    le_of_tendsto (hf t x).norm (Eventually.of_forall (fun n => hF n _ (le_max_right _ _) x))
  let L : ℝ → X →ₗ[𝕜] X := fun t =>
    { toFun := f t
      map_add' := fun x y => tendsto_nhds_unique (hf t (x+y))
        (by simpa only [map_add] using (hf t x).add (hf t y))
      map_smul' := fun c x => tendsto_nhds_unique (hf t (c • x))
        (by simpa only [map_smul, RingHom.id_apply] using (hf t x).const_smul c) }
  let T : ℝ → X →L[𝕜] X := fun t => (L t).mkContinuous 1 (fun x => by simpa [L] using hn t x)
  refine ⟨T,?_,?_⟩
  · intro t ht x
    simpa only [max_eq_left ht, T, L, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] using hf t x
  · intro t
    exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simpa [T,L] using hn t x)

omit [CompleteSpace X] in
theorem contraction_limit_apply (F : ℕ → X →L[𝕜] X) (G : X →L[𝕜] X)
    (hF : ∀ n x, ‖F n x‖ ≤ ‖x‖)
    (hf : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x)))
    (u : ℕ → X) (x : X) (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => F n (u n)) atTop (𝓝 (G x)) := by
  have hz : Tendsto (fun n => F n (u n)-F n x) atTop (𝓝 (0 : X)) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n => ‖u n-x‖) atTop (𝓝 0) by simpa using (hu.sub_const x).norm)
    simpa only [← map_sub] using hF n (u n-x)
  simpa using hz.add (hf x)
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE ContractionLimit -/

/- BEGIN WHOLE MODULE SemigroupLimit -/
section
open Filter Set
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

theorem exists_semigroup_limit (F : ℕ → ℝ → X →L[𝕜] X)
    (hF : ∀ n, IsContractionSemigroup (F n))
    (hc : ∀ x b, 0 ≤ b → UniformCauchySeqOn (fun n t => F n t x) atTop (Icc 0 b)) :
    ∃ T : ℝ → X →L[𝕜] X, IsContractionSemigroup T ∧
      (∀ t, 0 ≤ t → ∀ x, Tendsto (fun n => F n t x) atTop (𝓝 (T t x))) ∧
      (∀ x b, 0 ≤ b → TendstoUniformlyOn (fun n t => F n t x)
        (fun t => T t x) atTop (Icc 0 b)) := by
  obtain ⟨T,ht,hbound⟩ := exists_contraction_limit F
    (fun n t hp x => contraction_apply (F n) (hF n) hp x)
    (fun t hp x => (hc x t hp).cauchySeq ⟨hp,le_rfl⟩)
  have hu : ∀ x b, 0 ≤ b → TendstoUniformlyOn (fun n t => F n t x)
      (fun t => T t x) atTop (Icc 0 b) := fun x b hb =>
    (hc x b hb).tendstoUniformlyOn_of_tendsto (fun t ht' => ht t ht'.1 x)
  have hzero : T 0 = 1 := by
    ext x
    exact tendsto_nhds_unique (ht 0 le_rfl x)
      (by simpa only [(hF _).1.1, one_apply_eq_self] using
        (tendsto_const_nhds (x := x) : Tendsto (fun _ : ℕ => x) atTop (𝓝 x)))
  have hadd : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → T s * T t = T (s+t) := by
    intro s t hs ht'
    ext x
    have hv := contraction_limit_apply (fun n => F n s) (T s)
      (fun n y => contraction_apply (F n) (hF n) hs y) (ht s hs)
      (fun n => F n t x) (T t x) (ht t ht' x)
    have hv' : Tendsto (fun n => F n (s+t) x) atTop (𝓝 (T s (T t x))) := by
      simpa only [semigroup_apply (F _) (hF _).1 hs ht'] using hv
    exact tendsto_nhds_unique hv' (ht (s+t) (add_nonneg hs ht') x)
  have hz : ∀ x : X, Tendsto (fun h : ℝ => T h x) (𝓝[>] 0) (𝓝 x) := by
    intro x
    have hcont : ContinuousOn (fun t => T t x) (Icc 0 1) :=
      (hu x 1 zero_le_one).continuousOn (Eventually.frequently (Eventually.of_forall
        (fun n => (contraction_continuousOn (F n) (hF n) x).mono
          (fun _ hs => hs.1))))
    have hge : ContinuousWithinAt (fun t => T t x) (Ici 0) 0 :=
      (hcont 0 ⟨le_rfl,zero_le_one⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one)
    simpa only [ContinuousWithinAt,hzero,one_apply_eq_self] using
      hge.mono (show Ioi (0:ℝ) ⊆ Ici 0 from fun s hs => by change 0 ≤ s; exact hs.le)
  exact ⟨T,⟨⟨hzero,hadd,hz⟩,fun t _ => hbound t⟩,ht,hu⟩
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE SemigroupLimit -/

/- BEGIN WHOLE MODULE OrbitIntegralLimit -/
section
open Filter Set MeasureTheory
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

omit [IsScalarTower ℝ 𝕜 X] [CompleteSpace X] in
theorem extended_orbit_integral (T : ℝ → X →L[𝕜] X) (x : X)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in (0:ℝ)..t, extendedOrbit T x s) = ∫ s in (0:ℝ)..t, T s x := by
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [extendedOrbit,max_eq_left ((uIcc_of_le ht ▸ hs).1)]

omit [IsScalarTower ℝ 𝕜 X] [CompleteSpace X] in
theorem orbit_integral_limit (F : ℕ → ℝ → X →L[𝕜] X)
    (hF : ∀ n, IsContractionSemigroup (F n)) (T : ℝ → X →L[𝕜] X)
    (hlim : ∀ t, 0 ≤ t → ∀ x, Tendsto (fun n => F n t x) atTop (𝓝 (T t x)))
    (u : ℕ → X) (g : X) (hu : Tendsto u atTop (𝓝 g)) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n => ∫ s in (0:ℝ)..t, F n s (u n)) atTop
      (𝓝 (∫ s in (0:ℝ)..t, T s g)) := by
  obtain ⟨C,hC⟩ := (Metric.isBounded_range_of_tendsto u hu).exists_norm_le
  have hseq : ∀ s, Tendsto (fun n => extendedOrbit (F n) (u n) s) atTop
      (𝓝 (extendedOrbit T g s)) := fun s =>
    contraction_limit_apply (fun n => F n (max s 0)) (T (max s 0))
      (fun n x => contraction_apply (F n) (hF n) (le_max_right _ _) x)
      (hlim (max s 0) (le_max_right _ _)) u g hu
  have hd := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc 0 t))
    (fun _ : ℝ => C)
    (fun n => (extendedOrbit_continuous (F n) (hF n) (u n)).aestronglyMeasurable)
    (integrable_const C)
    (fun n => Eventually.of_forall (fun s =>
      (contraction_apply (F n) (hF n) (le_max_right s 0) (u n)).trans (hC _ (mem_range_self n))))
    (Eventually.of_forall hseq)
  have he : ∀ S : ℝ → X →L[𝕜] X, ∀ x : X,
      (∫ s in Ioc 0 t, extendedOrbit S x s) = ∫ s in (0:ℝ)..t, S s x := by
    intro S x
    rw [← intervalIntegral.integral_of_le ht]
    exact extended_orbit_integral S x ht
  simpa only [he] using hd
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE OrbitIntegralLimit -/

/- BEGIN WHOLE MODULE GeneratorIdentification -/
section
open Filter Set MeasureTheory
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]

theorem generator_from_inclusion (A : X →ₗ.[𝕜] X) (hm : IsMDissipative A)
    (T : ℝ → X →L[𝕜] X) (hT : IsContractionSemigroup T)
    (hi : ∀ y : A.domain, Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h y-y))
      (𝓝[>] 0) (𝓝 (A y))) : IsGenerator T A := by
  intro x g
  constructor
  · intro hg
    obtain ⟨hd,lam,hp,hs⟩ := hm
    let y : A.domain := ⟨resolventCLM A hd lam hp hs ((lam : 𝕜) • x-g),
      resolventCLM_mem A hd lam hp hs _⟩
    have hy : (lam : 𝕜) • (y : X)-A y = (lam : 𝕜) • x-g :=
      resolventCLM_right A hd lam hp hs _
    have hdiff : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h (x-y)-(x-y)))
        (𝓝[>] 0) (𝓝 (g-A y)) := by
      convert hg.sub (hi y) using 1
      ext h
      simp only [map_sub, smul_sub]
      abel
    have hineq := derivative_dissipative T hT.2 (x-y) (g-A y) hdiff lam hp
    have he : (lam : 𝕜) • (x-y) - (g-A y) = 0 := by
      rw [smul_sub]
      calc
        (lam : 𝕜) • x-(lam : 𝕜) • (y : X)-(g-A y) =
            ((lam : 𝕜) • x-g)-((lam : 𝕜) • (y : X)-A y) := by abel
        _ = 0 := by rw [hy,sub_self]
    rw [he,norm_zero] at hineq
    have hxy : x = (y : X) := sub_eq_zero.mp (norm_eq_zero.mp (by
      nlinarith [norm_nonneg (x-(y:X))]))
    refine ⟨hxy ▸ y.property,?_⟩
    have hAy : A y = g := by rw [hxy] at hy; exact (sub_right_inj.mp hy)
    simpa only [hxy] using hAy
  · rintro ⟨hx,rfl⟩
    exact hi ⟨x,hx⟩

variable [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

theorem derivative_of_orbit_integral (T : ℝ → X →L[𝕜] X)
    (hT : IsContractionSemigroup T) (x g : X)
    (hi : ∀ t, 0 ≤ t → T t x-x = ∫ s in (0:ℝ)..t, T s g) :
    Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • (T h x-x)) (𝓝[>] 0) (𝓝 g) := by
  let f := extendedOrbit T g
  have hf : Continuous f := extendedOrbit_continuous T hT g
  have hd : HasDerivAt (fun h => ∫ s in (0:ℝ)..h, f s) g 0 := by
    have := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 0)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter (hf.continuousAt (x := 0))
    simpa [f,extendedOrbit,hT.1.1] using this
  have hl : Tendsto (fun h : ℝ => ((h⁻¹ : ℝ) : 𝕜) • ∫ s in (0:ℝ)..h, f s)
      (𝓝[>] 0) (𝓝 g) := by
    simpa [RCLike.real_smul_eq_coe_smul (K := 𝕜)] using hd.tendsto_slope_zero_right
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp : 0 ≤ h := le_of_lt hh
  rw [hi h hp]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [f,extendedOrbit,max_eq_left ((uIcc_of_le hp ▸ hs).1)]
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE GeneratorIdentification -/

/- BEGIN WHOLE MODULE SemigroupGeneration -/
section
open Filter Set MeasureTheory
open scoped Topology
namespace HunterPDE.Semigroup.Proof
variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedSpace ℝ X] [IsScalarTower ℝ 𝕜 X] [CompleteSpace X]

theorem semigroup_generation (A : X →ₗ.[𝕜] X) (hd : Dense (A.domain : Set X))
    (hm : IsMDissipative A) :
    ∃ T : ℝ → X →L[𝕜] X, IsContractionSemigroup T ∧ IsGenerator T A := by
  obtain ⟨B,hcomm,hbound,hconv⟩ := exists_yosida_sequence A hd hm
  let F : ℕ → ℝ → X →L[𝕜] X := fun n t => NormedSpace.exp ((t : 𝕜) • B n)
  have hF : ∀ n, IsContractionSemigroup (F n) := fun n =>
    operator_exp_isContractionSemigroup (B n) (hbound n)
  have hc : ∀ x b, 0 ≤ b → UniformCauchySeqOn (fun n t => F n t x) atTop (Icc 0 b) := by
    intro x b hb
    apply uniform_cauchy_of_dense F
      (fun n t ht y => contraction_apply (F n) (hF n) ht y) A.domain hd B
      (fun y => (hconv y).cauchySeq) _ x b hb
    intro n m t ht y
    exact duhamel_difference_bound (B m) (B n) (hcomm m n) (hbound m) (hbound n) y ht
  obtain ⟨T,hT,hlim,_⟩ := exists_semigroup_limit F hF hc
  refine ⟨T,hT,generator_from_inclusion A hm T hT ?_⟩
  intro x
  apply derivative_of_orbit_integral T hT x (A x)
  intro t ht
  have hleft := (hlim t ht x).sub_const (x : X)
  have hright := orbit_integral_limit F hF T hlim (fun n => B n x) (A x) (hconv x) ht
  have hid : (fun n => F n t x-(x : X)) =
      (fun n => ∫ s in (0:ℝ)..t, F n s (B n x)) := by
    funext n
    exact operator_exp_orbit_integral (B n) (hbound n) x ht
  rw [hid] at hleft
  exact tendsto_nhds_unique hleft hright
end HunterPDE.Semigroup.Proof
end
/- END WHOLE MODULE SemigroupGeneration -/

/- BEGIN WHOLE MODULE LumerRoot -/
section
namespace HunterPDE.Semigroup

/-- Theorem 5.38 (Lumer–Phillips) of Hunter, *Notes on PDEs* (p. 147). An operator
`A : D(A) ⊂ X → X` in a Banach space `X` (over `𝕜 = ℝ` or `ℂ`) is the generator of a contraction
semigroup on `X` if and only if (1) `A` is closed and densely defined; (2) `A` is m-dissipative
(Definition 5.37). "Generator" is Definition 5.30: the generator's domain is exactly where the
right difference quotient converges, so the left side says `A` equals, domain included, the
generator of some strongly continuous contraction semigroup. -/
theorem lumer_phillips {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (A : X →ₗ.[𝕜] X) :
    (∃ T : ℝ → X →L[𝕜] X, IsContractionSemigroup T ∧ IsGenerator T A) ↔
      (A.IsClosed ∧ Dense (A.domain : Set X)) ∧ IsMDissipative A  := by
  let : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  let := IsScalarTower.restrictScalars ℝ 𝕜 X
  constructor
  · rintro ⟨T,hT,hA⟩
    exact Proof.semigroup_necessity T hT A hA
  · rintro ⟨⟨_,hd⟩,hm⟩
    exact Proof.semigroup_generation A hd hm

end HunterPDE.Semigroup

theorem solution {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [CompleteSpace X] (A : X →ₗ.[𝕜] X) :
    (∃ T : ℝ → X →L[𝕜] X, HunterPDE.Semigroup.IsContractionSemigroup T ∧ HunterPDE.Semigroup.IsGenerator T A) ↔
      (A.IsClosed ∧ Dense (A.domain : Set X)) ∧ HunterPDE.Semigroup.IsMDissipative A  := HunterPDE.Semigroup.lumer_phillips A
end
/- END WHOLE MODULE LumerRoot -/

