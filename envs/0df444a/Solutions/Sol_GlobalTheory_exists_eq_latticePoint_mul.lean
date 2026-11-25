-- Prove2me | solution 1 for GlobalTheory.exists_eq_latticePoint_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:26:28.626543+00:00
-- url     : https://prove2.me/submissions/fb298ddd-c0c8-4214-95cf-d4b78fe801b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_WeierstrassCurvePointOfLatticeAddOfGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsNumeratorOfInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsMulEqPolynomialWeierstrassP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddMonoidHomEqZeroOfEventually
import Theorems.Thm_GlobalTheory_latticeIsogeny_latticePoint
import Theorems.Thm_GlobalTheory_addMonoidHom_eq_zero_of_eventually
import Theorems.Thm_GlobalTheory_derivWeierstrassP_eq_zero_iff
import Theorems.Thm_GlobalTheory_eventually_notMem_periodLattice
import Theorems.Thm_GlobalTheory_latticePointEquiv_mk
import Theorems.Thm_GlobalTheory_latticePoint_eq_iff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.latticePointEquiv_mk


attribute [local simp] GlobalTheory.latticeIsogeny_latticePoint

set_option autoImplicit false
open Filter PeriodPair Polynomial WeierstrassCurve UpperHalfPlane
open scoped Topology
noncomputable section
open GlobalTheory
variable {L L' : PeriodPair} {α : ℂ}
namespace GlobalTheory
theorem _root_.solution (ψ : ℂ →+ (latticeCurve L').toAffine.Point) {F : ℂ → ℂ}
    {z₀ : ℂ} (hF : AnalyticAt ℂ F z₀) (h : ∀ᶠ z in 𝓝 z₀, ∃ y h', ψ z = .some (F z) y h') :
    ∃ α : ℂ, ∀ z, ψ z = latticePoint L' (α * z) := by
  obtain ⟨z₁, h4, hF₁, h₁⟩ : ∃ z₁, (4 • ψ) z₁ ≠ 0 ∧ AnalyticAt ℂ F z₁ ∧
      ∀ᶠ z in 𝓝 z₁, ∃ y h', ψ z = .some (F z) y h' := by
    by_contra hc
    have h2 := addMonoidHom_eq_zero_of_eventually (4 • ψ) (z₀ := z₀) (by
      filter_upwards [hF.eventually_analyticAt, h.eventually_nhds] with z h1 h2
      by_contra h3
      exact hc ⟨z, h3, h1, h2⟩) (z₀ / 4)
    rw [AddMonoidHom.nsmul_apply, ← map_nsmul, show 4 • (z₀ / 4) = z₀ by simp; ring] at h2
    obtain ⟨y, h', e⟩ := h.self_of_nhds
    exact Affine.Point.some_ne_zero _ (e.symm.trans h2)
  obtain ⟨w, hw⟩ := latticePoint_surjective L' (ψ z₁)
  have hw4 : w + w + (w + w) ∉ L'.lattice := fun hc ↦ h4 (by
    rw [AddMonoidHom.nsmul_apply, ← hw, ← latticePointHom_apply, ← map_nsmul,
      latticePointHom_apply, latticePoint_eq_zero_iff]
    convert hc using 1
    simp; ring)
  have hw2 : w + w ∉ L'.lattice := fun hc ↦ hw4 (add_mem hc hc)
  have hw1 : w ∉ L'.lattice := fun hc ↦ hw2 (add_mem hc hc)
  have hwF : ℘[L'] w = F z₁ := by
    obtain ⟨y, h', e⟩ := h₁.self_of_nhds
    rw [e, latticePoint_of_notMem L' hw1, Affine.Point.some.injEq] at hw
    exact hw.1
  have hP := L'.analyticOnNhd_weierstrassP w hw1
  have hP' : deriv ℘[L'] w ≠ 0 := by simpa [derivWeierstrassP_eq_zero_iff L' hw1] using hw2
  obtain ⟨g, hg, hg0, hg1⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (F z₁) ∧ g (F z₁) = w ∧
      ∀ᶠ x in 𝓝 (F z₁), ℘[L'] (g x) = x := by
    rw [← hwF]
    exact ⟨_, hP.analyticAt_localInverse hP', HasStrictFDerivAt.localInverse_apply_image ..,
      HasStrictDerivAt.eventually_right_inverse ..⟩
  let H : ℂ → ℂ := fun t ↦ g (F (z₁ + t))
  have hH : AnalyticAt ℂ H 0 :=
    (hg.comp hF₁).comp_of_eq (f := fun t ↦ z₁ + t) (by fun_prop) (by simp)
  have hH0 : H 0 = w := by simp [H, hg0]
  have hc := hH.continuousAt
  have hc' : ContinuousAt (fun t ↦ H (-t)) 0 :=
    ContinuousAt.comp_of_eq (f := fun t : ℂ ↦ -t) hc (by fun_prop) (by simp)
  have ev : ∀ {f : ℂ → ℂ}, ContinuousAt f 0 → f 0 ∉ L'.lattice → ∀ᶠ t in 𝓝 0, f t ∉ L'.lattice :=
    fun hf h0 ↦ hf.eventually (eventually_notMem_periodLattice L' h0)
  have ht : Tendsto (fun t ↦ z₁ + t) (𝓝 0) (𝓝 z₁) := Continuous.tendsto' (by fun_prop) _ _ (by simp)
  have s1 : ∀ᶠ t in 𝓝 0, ψ (z₁ + t) = latticePoint L' (H t) ∨
      ψ (z₁ + t) = latticePoint L' (-H t) := by
    filter_upwards [ht.eventually h₁, ht.eventually (hF₁.continuousAt.eventually hg1),
      ev hc (hH0 ▸ hw1)] with t ⟨y, h', e⟩ e' h3
    rw [latticePoint_neg, e, latticePoint_of_notMem L' h3]
    exact Affine.Point.X_eq_iff.mp e'.symm
  have s2 : ∀ᶠ t in 𝓝 0, ψ t = latticePoint L' (H t - w) := by
    filter_upwards [s1, (continuous_neg.tendsto' 0 0 neg_zero).eventually s1,
      ev (f := fun t ↦ -H t + H (-t) - (w + w)) ((hc.neg.add hc').sub continuousAt_const)
        (by simpa [hH0, -neg_add_rev] using hw2),
      ev (f := fun t ↦ -H t + -H (-t) - (w + w)) ((hc.neg.add hc'.neg).sub continuousAt_const)
        (fun hh ↦ hw4 (by convert neg_mem hh using 1; simp [hH0]; ring))] with t a b c d
    have key : ψ (z₁ + t) + ψ (z₁ + -t) = latticePoint L' (w + w) := by
      rw [latticePoint_add, hw, ← map_add, ← map_add]; congr 1; ring
    rcases a with a | a
    · rw [← latticePointHom_apply, map_sub, latticePointHom_apply, latticePointHom_apply, ← a, hw,
        map_add, add_sub_cancel_left]
    · rcases b with b | b <;> rw [a, b, ← latticePoint_add, latticePoint_eq_iff] at key
      exacts [(c key).elim, (d key).elim]
  let u : ℂ → ℂ := fun t ↦ H t - w
  have hu : AnalyticAt ℂ u 0 := by fun_prop
  have hu0 : u 0 = 0 := by simp [u, hH0]
  have t1 : Tendsto (fun p : ℂ × ℂ ↦ p.1) (𝓝 (0, 0)) (𝓝 0) := continuous_fst.tendsto _
  have t2 : Tendsto (fun p : ℂ × ℂ ↦ p.2) (𝓝 (0, 0)) (𝓝 0) := continuous_snd.tendsto _
  have t3 : Tendsto (fun p : ℂ × ℂ ↦ p.1 + p.2) (𝓝 (0, 0)) (𝓝 0) := by simpa using t1.add t2
  have tu : Tendsto u (𝓝 0) (𝓝 0) := by simpa [hu0] using hu.continuousAt.tendsto
  have s3 : ∀ᶠ p : ℂ × ℂ in 𝓝 (0, 0), u (p.1 + p.2) = u p.1 + u p.2 := by
    have t4 : Tendsto (fun p : ℂ × ℂ ↦ u (p.1 + p.2) - (u p.1 + u p.2)) (𝓝 (0, 0)) (𝓝 0) := by
      simpa using (tu.comp t3).sub ((tu.comp t1).add (tu.comp t2))
    filter_upwards [t1.eventually s2, t2.eventually s2, t3.eventually s2,
      t4.eventually (L'.compl_lattice_sdiff_singleton_mem_nhds 0)] with p a b c d
    rw [map_add, a, b, ← latticePoint_add, eq_comm, latticePoint_eq_iff] at c
    by_contra hne
    exact d ⟨c, fun e ↦ hne (sub_eq_zero.mp e)⟩
  have s4 : ∀ᶠ s in 𝓝 0, deriv (fun t ↦ u t - deriv u 0 * t) s = 0 := by
    filter_upwards [s3.curry_nhds, hu.eventually_analyticAt] with s a b
    have d1 : HasDerivAt (fun t ↦ u (s + t)) (deriv u s) 0 :=
      HasDerivAt.comp_const_add s 0 (by simpa using b.differentiableAt.hasDerivAt)
    have d2 := d1.unique ((hu.differentiableAt.hasDerivAt.const_add (u s)).congr_of_eventuallyEq a)
    have d3 := (b.differentiableAt.hasDerivAt.sub ((hasDerivAt_id s).const_mul (deriv u 0))).deriv
    simpa [d2] using! d3
  have s5 := analyticOrderAt_eq_top.mp ((analyticOrderAt_deriv_eq_top_iff_of_eq_zero
    (f := fun t ↦ u t - deriv u 0 * t) (z₀ := 0) (by fun_prop) (by simp [hu0])).mp
      (analyticOrderAt_eq_top.mpr s4))
  refine ⟨deriv u 0, fun z ↦ sub_eq_zero.mp (addMonoidHom_eq_zero_of_eventually
    (ψ - (latticePointHom L').comp (AddMonoidHom.mulLeft (deriv u 0))) (z₀ := 0) ?_ z)⟩
  filter_upwards [s2, s5] with t a b
  change ψ t - latticePoint L' (deriv u 0 * t) = 0
  rw [a, ← sub_eq_zero.mp b, sub_self]
end GlobalTheory
