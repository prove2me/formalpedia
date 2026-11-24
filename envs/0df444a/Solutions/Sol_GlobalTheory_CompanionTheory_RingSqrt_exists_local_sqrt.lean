-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RingSqrt.exists_local_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:26.631447+00:00
-- url     : https://prove2.me/submissions/2a22a658-9254-4b04-83ad-0d8fb761cdb4

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalUniqueSquareRootNearOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RingSqrt
namespace GlobalTheory.CompanionTheory.RingSqrt
theorem _root_.solution : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V),
    Continuous ψ → Continuous ψ.symm →
    ∃ (r : B → B) (U : Set B), U ∈ nhds (1 : B) ∧ Filter.Tendsto r (nhds 1) (nhds 1) ∧
      (∀ᶠ h in nhds (1 : B), r h * r h = h) ∧ ∀ x ∈ U, ∀ y ∈ U, x * x = y * y → x = y := by
  intro B V _ _ _ _ _ _ ψ hψ hψs
  let L : V → (V →L[ℝ] V) := fun x =>
    AddMonoidHom.toRealLinearMap
      { toFun := fun y => ψ (ψ.symm x * ψ.symm y)
        map_zero' := by simp
        map_add' := by intro a b; simp [mul_add] }
      (hψ.comp (continuous_const.mul hψs))
  have hL : ∀ x y, L x y = ψ (ψ.symm x * ψ.symm y) := fun _ _ => rfl
  let A : V →L[ℝ] (V →L[ℝ] V) := AddMonoidHom.toRealLinearMap
      { toFun := L
        map_zero' := by ext y; simp [hL]
        map_add' := by intro a b; ext y; simp [hL, add_mul] }
      (continuous_clm_apply.2 fun y => hψ.comp (hψs.mul continuous_const))
  have hA : ∀ x y, A x y = ψ (ψ.symm x * ψ.symm y) := fun _ _ => rfl
  obtain ⟨Q, hQdef⟩ : ∃ Q : V → V, Q = fun y => y + y + A y y := ⟨_, rfl⟩
  have hQ : ∀ y, (1 + ψ.symm y) * (1 + ψ.symm y) = 1 + ψ.symm (Q y) := by
    intro y
    simp only [hQdef, hA, map_add, AddEquiv.symm_apply_apply, mul_add, add_mul, one_mul, mul_one]
    abel
  have hQ0 : Q 0 = 0 := by simp [hQdef]
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 (2 : ℝ) two_ne_zero)
  have hder : HasStrictFDerivAt Q (e : V →L[ℝ] V) 0 := by
    have h1 : HasStrictFDerivAt (fun y : V => y) (ContinuousLinearMap.id ℝ V) 0 :=
      hasStrictFDerivAt_id 0
    have h2 := A.hasStrictFDerivAt.clm_apply h1
    have h3 := (h1.add h1).add h2
    rw [hQdef]
    refine h3.congr_fderiv ?_
    ext v
    simp [e, two_smul, Units.smul_def]
  have hsub : Filter.Tendsto (fun h : B => ψ (h - 1)) (𝓝 1) (𝓝 0) := by
    have hc : Continuous fun h : B => ψ (h - 1) := hψ.comp (continuous_id.sub continuous_const)
    simpa using hc.tendsto 1
  have hg : Filter.Tendsto (hder.localInverse Q e 0) (𝓝 0) (𝓝 0) := by
    have := hder.localInverse_tendsto
    rwa [hQ0] at this
  have hr : ∀ᶠ y in 𝓝 (0 : V), Q (hder.localInverse Q e 0 y) = y := by
    have := hder.eventually_right_inverse
    rwa [hQ0] at this
  refine ⟨fun h => 1 + ψ.symm (hder.localInverse Q e 0 (ψ (h - 1))),
    (fun x => ψ (x - 1)) ⁻¹' (hder.toOpenPartialHomeomorph Q).source, ?_, ?_, ?_, ?_⟩
  · exact hsub ((hder.toOpenPartialHomeomorph Q).open_source.mem_nhds
      hder.mem_toOpenPartialHomeomorph_source)
  · have h0 : Filter.Tendsto (fun h : B => ψ.symm (hder.localInverse Q e 0 (ψ (h - 1))))
        (𝓝 1) (𝓝 0) := by
      have := (hψs.tendsto 0).comp (hg.comp hsub)
      simpa [Function.comp_def] using this
    simpa using (tendsto_const_nhds (x := (1 : B))).add h0
  · filter_upwards [hsub hr] with h hh
    rw [hQ, hh]
    simp
  · intro x hx y hy hxy
    have key : Q (ψ (x - 1)) = Q (ψ (y - 1)) := by
      have e1 := hQ (ψ (x - 1))
      have e2 := hQ (ψ (y - 1))
      simp only [AddEquiv.symm_apply_apply, add_sub_cancel] at e1 e2
      exact ψ.symm.injective (add_left_cancel (e1.symm.trans (hxy.trans e2)))
    have h1 : ψ (x - 1) = ψ (y - 1) := (hder.toOpenPartialHomeomorph Q).injOn hx hy key
    exact sub_left_inj.1 (ψ.injective h1)
end GlobalTheory.CompanionTheory.RingSqrt
