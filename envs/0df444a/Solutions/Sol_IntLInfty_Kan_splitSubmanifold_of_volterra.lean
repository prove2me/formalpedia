-- Prove2me | solution 1 for IntLInfty.Kan.splitSubmanifold_of_volterra
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-10T03:47:07.951729+00:00
-- url     : https://prove2.me/submissions/033d3b59-669c-468c-837b-7ccbe4668d36

import Mathlib
import Definitions.Def_IntLInfty_Kan_CE
import Definitions.Def_IntLInfty_Kan_Forms
import Definitions.Def_IntLInfty_Kan_Manifold
import Definitions.Def_IntLInfty_Kan_Integ

set_option autoImplicit false

namespace IntLInfty.Kan.A83Graph

open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedComplemented_fix (P : E →L[ℝ] E) (hP : ∀ x, P (P x) = P x) :
    (LinearMap.ker ((ContinuousLinearMap.id ℝ E - P : E →L[ℝ] E) : E →ₗ[ℝ] E)).ClosedComplemented := by
  refine ⟨(P.codRestrict _ fun x => ?_), fun x => ?_⟩
  · simp [hP]
  · apply Subtype.ext
    have hx := x.2
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_id',
      ContinuousLinearMap.coe_coe, Pi.sub_apply, id_eq, sub_eq_zero] at hx
    show P (x : E) = x
    exact hx.symm

end IntLInfty.Kan.A83Graph

namespace IntLInfty.Kan.A83IFT

open IntLInfty.Kan
open scoped ContDiff

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Inverse function theorem form of a split submanifold: a level set `Ψ⁻¹(F)` of a `C^∞` map
whose derivative is invertible at every point of the set, with `F` closed complemented. -/
theorem isSplitSubmanifold_of_preimage (Ψ : E → E) (hΨ : ContDiff ℝ ∞ Ψ) (F : Submodule ℝ E)
    (hF : F.ClosedComplemented) (M : Set E) (hM : ∀ z, z ∈ M ↔ Ψ z ∈ F)
    (hinv : ∀ x ∈ M, ∃ e : E ≃L[ℝ] E, HasFDerivAt Ψ (e : E →L[ℝ] E) x) :
    IsSplitSubmanifold M := by
  intro x hx
  obtain ⟨e, he⟩ := hinv x hx
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff : Differentiable ℝ Ψ := hΨ.differentiable (by simp)
  set U : Set E := (fderiv ℝ Ψ) ⁻¹' Set.range ((↑) : (E ≃L[ℝ] E) → E →L[ℝ] E) with hUdef
  have hU : IsOpen U :=
    ContinuousLinearEquiv.isOpen.preimage (hΨ.continuous_fderiv (by simp))
  have hxU : x ∈ U := ⟨e, he.fderiv.symm⟩
  let φ0 := (hΨ.contDiffAt (x := x)).toOpenPartialHomeomorph Ψ he hn
  let φ := φ0.restrOpen U hU
  have hφ : ∀ z, φ z = Ψ z := fun z => rfl
  have hsrc : φ.source = φ0.source ∩ U := φ0.restrOpen_source U hU
  refine ⟨F, hF, φ, ?_, ?_, ?_, ?_⟩
  · rw [hsrc]
    exact ⟨(hΨ.contDiffAt (x := x)).mem_toOpenPartialHomeomorph_source he hn, hxU⟩
  · exact (show ContDiffOn ℝ ∞ Ψ φ.source from hΨ.contDiffOn)
  · intro y hy
    have hs : φ.symm y ∈ φ.source := φ.map_target hy
    rw [hsrc] at hs
    obtain ⟨e', he'⟩ := hs.2
    have hfd : HasFDerivAt φ (e' : E →L[ℝ] E) (φ.symm y) := by
      have := (hdiff (φ.symm y)).hasFDerivAt
      rw [← he'] at this
      exact this
    exact (φ.contDiffAt_symm hy hfd (hΨ.contDiffAt)).contDiffWithinAt
  · ext w
    constructor
    · rintro ⟨z, ⟨hzM, hzs⟩, rfl⟩
      exact ⟨(hM z).1 hzM, φ.map_source hzs⟩
    · rintro ⟨hwF, hwt⟩
      refine ⟨φ.symm w, ⟨(hM _).2 ?_, φ.map_target hwt⟩, φ.right_inv hwt⟩
      rw [← hφ, φ.right_inv hwt]
      exact hwF

/-- `1 - V` is invertible as soon as some power of `V` is a strict contraction (Volterra-type operators). -/
theorem exists_equiv_one_sub (V : E →L[ℝ] E) (n : ℕ) (hn : ‖V ^ n‖ < 1) :
    ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = 1 - V := by
  set u : (E →L[ℝ] E)ˣ := Units.oneSub (V ^ n) hn with hu
  set S : E →L[ℝ] E := ∑ i ∈ Finset.range n, V ^ i with hS
  have hSV : Commute S V := Commute.sum_left _ _ _ fun i _ => (Commute.refl V).pow_left i
  have hR : (1 - V) * S = (u : E →L[ℝ] E) := by
    rw [hu, Units.val_oneSub, hS, mul_neg_geom_sum]
  have hL : S * (1 - V) = (u : E →L[ℝ] E) := by
    rw [hu, Units.val_oneSub, hS, geom_sum_mul_neg]
  have hSu : Commute S (u : E →L[ℝ] E) := by
    rw [← hR]; exact (Commute.one_right S |>.sub_right hSV).mul_right (Commute.refl S)
  have hSu' : Commute S (↑u⁻¹ : E →L[ℝ] E) := hSu.units_inv_right
  let U : (E →L[ℝ] E)ˣ :=
    { val := 1 - V
      inv := ↑u⁻¹ * S
      val_inv := by
        rw [← mul_assoc, mul_assoc (1 - V), ← hSu'.eq, ← mul_assoc, hR, Units.mul_inv]
      inv_val := by
        rw [mul_assoc, hL, Units.inv_mul] }
  exact ⟨ContinuousLinearEquiv.unitsEquiv ℝ E U, rfl⟩

end IntLInfty.Kan.A83IFT

open scoped ContDiff in
open IntLInfty.Kan in
theorem solution {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (G : E → E) (hG : ContDiff ℝ ∞ G) (H : E →L[ℝ] E) (hH : ∀ z, H (H z) = H z)
    (M : Set E) (hM : ∀ z, z ∈ M ↔ H (z - G z) = 0)
    (hV : ∀ x ∈ M, ∃ n : ℕ, ‖(fderiv ℝ G x) ^ n‖ < 1) : IsSplitSubmanifold M := by
  have hF : (LinearMap.ker (H : E →ₗ[ℝ] E)).ClosedComplemented := by
    have h := IntLInfty.Kan.A83Graph.closedComplemented_fix (E := E)
      (ContinuousLinearMap.id ℝ E - H) (fun x => by
        simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply, map_sub, hH,
          sub_self, sub_zero])
    have e : (ContinuousLinearMap.id ℝ E - (ContinuousLinearMap.id ℝ E - H) : E →L[ℝ] E) = H :=
      sub_sub_cancel _ _
    rwa [e] at h
  refine IntLInfty.Kan.A83IFT.isSplitSubmanifold_of_preimage (fun w => w - G w)
    (contDiff_id.sub hG) _ hF M (fun z => by rw [hM z]; exact LinearMap.mem_ker.symm) ?_
  intro x hx
  obtain ⟨n, hn⟩ := hV x hx
  obtain ⟨e, he⟩ := IntLInfty.Kan.A83IFT.exists_equiv_one_sub _ n hn
  refine ⟨e, ?_⟩
  rw [he]
  have hG' : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable (by simp)).differentiableAt.hasFDerivAt
  exact (hasFDerivAt_id x).sub hG'
