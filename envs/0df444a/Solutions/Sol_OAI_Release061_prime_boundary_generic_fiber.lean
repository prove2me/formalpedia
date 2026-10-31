-- Prove2me | solution 1 for OAI.Release061.prime_boundary_generic_fiber
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T22:07:01.44698+00:00
-- url     : https://prove2.me/submissions/336a2541-4780-4c5a-9a37-dcfd1fcf0a59

import Mathlib
import Definitions.Def_SymmetricDomains
import Definitions.Def_OAIQ025S000
import Definitions.Def_OAIQ025S001
import Definitions.Def_OAIQ025S002
import Theorems.Thm_OAI_Release061_NashPatch_principal_rank_dichotomy
import Theorems.Thm_OAI_Release061_isSemialgebraic_centered_nash_cover

section
-- module Solutions.OAIQ025_SD.Compat
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_Basic
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace Release061

theorem IsAffineAlgebraic.isClosed {n : ℕ} {V : Set (Affine n)}
    (hV : IsAffineAlgebraic V) : IsClosed V := by
  obtain ⟨P, rfl⟩ := hV
  have heq : {z | ∀ p ∈ P, MvPolynomial.eval z p = 0} =
      ⋂ p ∈ P, {z | MvPolynomial.eval z p = 0} := by ext; simp
  rw [heq]
  exact isClosed_biInter fun p _ => isClosed_eq p.continuous_eval continuous_const

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialIntegralCoordinates
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


theorem locally_uniform_subsequence_of_equicontinuous
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [SigmaCompactSpace X]
    (F : ℕ → X → ℂ) (hF : Equicontinuous F)
    (hbound : ∀ i x, ‖F i x‖ ≤ 1) :
    ∃ f : X → ℂ, Continuous f ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        TendstoLocallyUniformly (fun i => F (φ i)) f Filter.atTop := by
  let A : Set (X → ℂ) := closure (Set.range F)
  have hRange : (Set.range F).Equicontinuous := equicontinuous_iff_range.mp hF
  have hAe : A.Equicontinuous := Set.Equicontinuous.closure hRange
  have hAb : ∀ f ∈ A, ∀ x, ‖f x‖ ≤ 1 := by
    intro f hf x
    have hsub : Set.range F ⊆ {g : X → ℂ | ‖g x‖ ≤ 1} := by
      rintro _ ⟨i, rfl⟩
      exact hbound i x
    exact (closure_minimal hsub (isClosed_le (continuous_apply x).norm continuous_const)) hf
  have hAc : IsCompact A := by
    apply (isCompact_univ_pi fun _x : X => isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      isClosed_closure
    intro f hf
    simpa [Set.mem_pi, Metric.mem_closedBall, dist_zero_right] using hAb f hf
  let S : Set C(X, ℂ) := {f | (f : X → ℂ) ∈ A}
  have himage : ContinuousMap.toFun '' S = A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hAe.continuous_of_mem hf⟩, hf, rfl⟩
  have hSc : IsCompact S := by
    apply ArzelaAscoli.isCompact_of_equicontinuous S
    · rwa [himage]
    · exact hAe.comp (fun f : S => (⟨f.1, f.2⟩ : A))
  let G : ℕ → C(X, ℂ) := fun i => ⟨F i, hF.continuous i⟩
  have hGS : ∀ i, G i ∈ S := fun i => subset_closure (Set.mem_range_self i)
  obtain ⟨f, hf, φ, hφ, hconv⟩ := hSc.tendsto_subseq hGS
  exact ⟨f, f.continuous, hAb _ hf, φ, hφ,
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hconv⟩

theorem equicontinuous_of_bounded_differentiableOn
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {W : Set E} (hW : IsOpen W) (F : ι → E → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) W)
    (hb : ∀ i x, x ∈ W → ‖F i x‖ ≤ 1) :
    Equicontinuous (fun i (x : W) => F i x) := by
  intro p
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW p p.property
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have ht : Filter.Tendsto (fun x : W => (2 / r) * dist (x : E) p)
      (nhds p) (nhds 0) := by
    simpa using ((continuous_subtype_val.dist
      (continuous_const : Continuous (fun _ : W => (p : E)))).const_mul (2 / r)).tendsto p
  have hsmall := (tendsto_order.mp ht).2 ε hε
  have hball : ∀ᶠ x : W in nhds p, (x : E) ∈ Metric.ball (p : E) r :=
    continuousAt_subtype_val.preimage_mem_nhds (Metric.ball_mem_nhds (p : E) hr)
  filter_upwards [hsmall, hball] with x hx hxr i
  have hmaps : Set.MapsTo (F i) (Metric.ball (p : E) r)
      (Metric.closedBall (F i p) 2) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm_sub]
    exact (norm_sub_le _ _).trans (by linarith [hb i z (hrW hz), hb i p p.property])
  have := (Complex.dist_le_div_mul_dist_of_mapsTo_ball
    ((hd i).mono hrW) hmaps hxr).trans_lt hx
  simpa [dist_comm] using this

theorem maximum_propagation_on_ball
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : E} {r : ℝ} (hr : 0 < r) (F : ℕ → E → ℂ) (f : E → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) (Metric.ball p r))
    (hb : ∀ i x, x ∈ Metric.ball p r → ‖F i x‖ ≤ 1)
    (hc : TendstoLocallyUniformlyOn F f Filter.atTop (Metric.ball p r))
    (hp : f p = 1) : Set.EqOn f (fun _ => 1) (Metric.ball p r) := by
  intro x hx
  by_cases hxp : x = p
  · simpa [hxp] using hp
  let R : ℝ := r / dist x p
  have hdpos : 0 < dist x p := dist_pos.mpr hxp
  have hR : 0 < R := div_pos hr hdpos
  let L : ℂ →ᵃ[ℂ] E := AffineMap.lineMap p x
  have hL : Set.MapsTo L (Metric.ball (0 : ℂ) R) (Metric.ball p r) := by
    intro z hz
    simpa [L, R, div_pos, lt_div_iff₀ hdpos, dist_comm p] using hz
  have hcL := hc.comp L hL L.differentiable.continuous.continuousOn
  have hdL : DifferentiableOn ℂ (f ∘ L) (Metric.ball (0 : ℂ) R) :=
    hcL.differentiableOn (Filter.Eventually.of_forall fun i =>
      (hd i).comp L.differentiable.differentiableOn hL) Metric.isOpen_ball
  have hbL : ∀ z ∈ Metric.ball (0 : ℂ) R, ‖(f ∘ L) z‖ ≤ 1 := by
    intro z hz
    exact le_of_tendsto (hcL.tendsto_at hz).norm
      (Filter.Eventually.of_forall fun i => hb i (L z) (hL hz))
  have hL0 : (f ∘ L) 0 = 1 := by simpa [L] using hp
  have hmax : IsMaxOn (norm ∘ (f ∘ L)) (Metric.ball (0 : ℂ) R) 0 := by
    intro z hz
    change ‖(f ∘ L) z‖ ≤ ‖(f ∘ L) 0‖
    rw [hL0, norm_one]
    exact hbL z hz
  have hone : (1 : ℂ) ∈ Metric.ball (0 : ℂ) R := by
    simpa [R, lt_div_iff₀ hdpos] using hx
  have heq := Complex.eq_const_of_exists_max hdL (Metric.mem_ball_self hR) hmax hone
  simpa [L, hp] using heq

theorem eq_one_of_local_maximum_propagation
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : X → ℂ) (hf : Continuous f) (p : X) (hp : f p = 1)
    (hloc : ∀ q, f q = 1 → ∀ᶠ x in nhds q, f x = 1) : ∀ x, f x = 1 := by
  have hclosed : IsClosed {x | f x = 1} := isClosed_eq hf continuous_const
  have hopen : IsOpen {x | f x = 1} := isOpen_iff_mem_nhds.mpr hloc
  have heq := (show IsClopen {x | f x = 1} from ⟨hclosed, hopen⟩).eq_univ ⟨p, hp⟩
  intro x
  have : x ∈ {x | f x = 1} := by rw [heq]; trivial
  exact this

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AnalyticImplicitScalar
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061


theorem monic_root_norm_lt_coeff_sum {K : Type*} [NormedField K]
    {p : Polynomial K} (hp : p.Monic) {z : K} (hz : p.IsRoot z) :
    ‖z‖₊ < (∑ j ∈ Finset.range p.natDegree, ‖p.coeff j‖₊) + 1 := by
  apply (hz.norm_lt_cauchyBound hp.ne_zero).trans_le
  simp only [Polynomial.cauchyBound, hp.leadingCoeff, nnnorm_one, div_one]
  exact add_le_add (Finset.sup_le fun j hj =>
    Finset.single_le_sum (f := fun j => ‖p.coeff j‖₊) (fun _ _ => zero_le) hj) le_rfl

theorem finite_fiber_of_integral_coordinates {k : Type*} [Field k]
    {n d : ℕ} {V : Set (Fin n → k)} (P : Fin d → MvPolynomial (Fin n) k)
    (Q : Fin n → Polynomial (MvPolynomial (Fin d) k))
    (hQ : ∀ i, (Q i).Monic)
    (hroot : ∀ z ∈ V, ∀ i,
      Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
        (z i) (Q i) = 0) (y : Fin d → k) :
    {z ∈ V | (fun j => MvPolynomial.eval z (P j)) = y}.Finite := by
  let p := fun i => (Q i).map (MvPolynomial.eval y)
  have hp : ∀ i, (p i).Monic := fun i => (hQ i).map _
  apply (Set.Finite.pi fun i => Polynomial.finite_setOfPred_isRoot (hp i).ne_zero).subset
  intro z hz i _
  change (p i).IsRoot (z i)
  have h := hroot z hz.1 i
  rw [hz.2] at h
  simpa only [p, Polynomial.IsRoot.def, Polynomial.eval_map] using h

theorem isCompact_preimage_of_integral_coordinates
    {n d : ℕ} {V : Set (Fin n → ℂ)} (hV : IsClosed V)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (Q : Fin n → Polynomial (MvPolynomial (Fin d) ℂ))
    (hQ : ∀ i, (Q i).Monic)
    (hroot : ∀ z ∈ V, ∀ i,
      Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
        (z i) (Q i) = 0) {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    IsCompact {z ∈ V | (fun j => MvPolynomial.eval z (P j)) ∈ K} := by
  classical
  let B : (Fin d → ℂ) → NNReal := fun y =>
    ∑ i : Fin n, ((∑ j ∈ Finset.range (Q i).natDegree,
      ‖MvPolynomial.eval y ((Q i).coeff j)‖₊) + 1)
  have hB : Continuous B := by
    apply continuous_finsetSum
    intro i _
    apply Continuous.add _ continuous_const
    apply continuous_finsetSum
    intro j _
    exact ((Q i).coeff j).continuous_eval.nnnorm
  obtain ⟨R, hR⟩ := hK.bddAbove_image hB.continuousOn
  have hbound : ∀ z ∈ V, (fun j => MvPolynomial.eval z (P j)) ∈ K → ‖z‖ ≤ (R : ℝ) := by
    intro z hz hzK
    apply (pi_norm_le_iff_of_nonneg R.2).mpr
    intro i
    let y := fun j => MvPolynomial.eval z (P j)
    have hp : ((Q i).map (MvPolynomial.eval y)).Monic := (hQ i).map _
    have hzroot : ((Q i).map (MvPolynomial.eval y)).IsRoot (z i) := by
      simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hroot z hz i
    have hh := monic_root_norm_lt_coeff_sum hp hzroot
    rw [(hQ i).natDegree_map] at hh
    simp only [Polynomial.coeff_map] at hh
    have hsum : ((∑ j ∈ Finset.range (Q i).natDegree,
        ‖MvPolynomial.eval y ((Q i).coeff j)‖₊) + 1) ≤ B y :=
      Finset.single_le_sum (f := fun i : Fin n =>
        (∑ j ∈ Finset.range (Q i).natDegree,
          ‖MvPolynomial.eval y ((Q i).coeff j)‖₊) + 1)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    exact_mod_cast hh.le.trans (hsum.trans (hR (Set.mem_image_of_mem B hzK)))
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  constructor
  · exact hV.inter (hK.isClosed.preimage (continuous_pi fun i => (P i).continuous_eval))
  · exact Metric.isBounded_iff_subset_ball 0 |>.2
      ⟨(R : ℝ) + 1, fun z hz => by simpa [Metric.mem_ball, dist_zero_right] using
        (hbound z hz.1 hz.2).trans_lt (lt_add_one _)⟩

theorem finite_fiber_localization
    {X Y : Type*} [TopologicalSpace X] [RegularSpace X] [T1Space X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsProperMap f)
    (q : X) (hfin : (f ⁻¹' {f q}).Finite)
    {W : Set X} (hW : IsOpen W) (hqW : q ∈ W) :
    ∃ B : Set Y, IsOpen B ∧ f q ∈ B ∧
      ∃ Ω C : Set X, IsOpen Ω ∧ q ∈ Ω ∧ Ω ⊆ W ∧ IsClosed C ∧
        Ω = C ∩ f ⁻¹' B ∧ (Ω ∩ f ⁻¹' {f q}) = {q} := by
  let H : Set X := W ∩ (f ⁻¹' {f q} \ {q})ᶜ
  have hHo : IsOpen H := hW.inter (hfin.sdiff.isClosed.isOpen_compl)
  have hqH : q ∈ H := by simp [H, hqW]
  obtain ⟨O, ⟨hqO, hOo⟩, hclO⟩ :=
    (hasBasis_opens_closure q).mem_iff.mp (hHo.mem_nhds hqH)
  have hclfiber : ∀ x ∈ closure O, f x = f q → x = q := by
    intro x hx hfx
    have h := (hclO hx).2
    by_contra hne
    exact h ⟨hfx, hne⟩
  let B := (f '' (closure O \ O))ᶜ
  have hBo : IsOpen B := (hf.isClosedMap _ (isClosed_closure.sdiff hOo)).isOpen_compl
  have hqB : f q ∈ B := by
    rintro ⟨x, hx, hfx⟩
    have h : x = q := hclfiber x hx.1 hfx
    exact hx.2 (h ▸ hqO)
  refine ⟨B, hBo, hqB, O ∩ f ⁻¹' B, closure O,
    hOo.inter (hBo.preimage hf.continuous), ⟨hqO, hqB⟩,
    fun x hx => (hclO (subset_closure hx.1)).1, isClosed_closure, ?_, ?_⟩
  · ext x
    constructor
    · exact fun hx => ⟨subset_closure hx.1, hx.2⟩
    · intro hx
      refine ⟨?_, hx.2⟩
      by_contra hnot
      exact hx.2 ⟨x, ⟨hx.1, hnot⟩, rfl⟩
  · ext x
    constructor
    · intro hx
      exact hclfiber x (subset_closure hx.1.1) hx.2
    · rintro rfl
      exact ⟨⟨hqO, hqB⟩, rfl⟩

open Set Filter Topology

theorem analytic_local_inverse
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {a : E} (hf : AnalyticAt ℂ f a)
    (i : E ≃L[ℂ] F) (hi : HasFDerivAt f (i : E →L[ℂ] F) a) :
    ∃ e : OpenPartialHomeomorph E F, (e : E → F) = f ∧ a ∈ e.source ∧
      AnalyticAt ℂ e.symm (f a) := by
  have hs : HasStrictFDerivAt f (i : E →L[ℂ] F) a := by
    simpa only [hi.fderiv] using hf.hasStrictFDerivAt
  let e := hs.toOpenPartialHomeomorph f
  refine ⟨e, hs.toOpenPartialHomeomorph_coe, hs.mem_toOpenPartialHomeomorph_source, ?_⟩
  obtain ⟨p, hp⟩ := hf
  have he : (e : E → F) = f := hs.toOpenPartialHomeomorph_coe
  have hpe : HasFPowerSeriesAt e p a := he ▸ hp
  have hcoeff : p 1 = (continuousMultilinearCurryFin1 ℂ E F).symm
      (i : E →L[ℂ] F) := by
    apply (continuousMultilinearCurryFin1 ℂ E F).injective
    simpa using hp.hasFDerivAt.unique hi
  simpa only [he] using
    (e.hasFPowerSeriesAt_symm hs.mem_toOpenPartialHomeomorph_source hpe hcoeff).analyticAt

theorem analytic_implicit_scalar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {F : E × ℂ → ℂ} {a : E} {b : ℂ}
    (hF : AnalyticAt ℂ F (a, b)) (hzero : F (a, b) = 0)
    (L : E × ℂ →L[ℂ] ℂ) (hL : HasFDerivAt F L (a, b))
    (hsimple : L (0, 1) ≠ 0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, F (y, g y) = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), F p = 0 → p.2 = g p.1) := by
  let G : E × ℂ → E × ℂ := fun p => (p.1, F p)
  have hG : AnalyticAt ℂ G (a, b) :=
    ((ContinuousLinearMap.fst ℂ E ℂ).analyticAt (a, b)).prod hF
  have hdG : HasFDerivAt G (triangularDifferentialEquiv L hsimple : _ →L[ℂ] _) (a, b) :=
    hasFDerivAt_fst.prodMk hL
  obtain ⟨e, he, hmem, hia⟩ := analytic_local_inverse hG
    (triangularDifferentialEquiv L hsimple) hdG
  have hGab : G (a, b) = (a, 0) := by simp [G, hzero]
  rw [hGab] at hia
  let g : E → ℂ := fun y => (e.symm (y, 0)).2
  have hiac : AnalyticAt ℂ (fun y : E => e.symm (y, 0)) a :=
    hia.comp (f := fun y : E => (y, 0))
      ((ContinuousLinearMap.inl ℂ E ℂ).analyticAt a)
  have hg : AnalyticAt ℂ g a :=
    ((ContinuousLinearMap.snd ℂ E ℂ).analyticAt _).comp hiac
  have hsource : e.symm (a, 0) = (a, b) := by
    rw [← hGab, ← he]
    exact e.left_inv hmem
  refine ⟨g, hg, congrArg Prod.snd hsource, ?_, ?_⟩
  · have hright := e.eventually_right_inverse' hmem
    rw [he, hGab] at hright
    have ht : Tendsto (fun y : E => (y, (0 : ℂ))) (𝓝 a) (𝓝 (a, 0)) :=
      (continuous_id.prodMk continuous_const).continuousAt.tendsto
    filter_upwards [ht.eventually hright] with y hy
    have hfst : (e.symm (y, 0)).1 = y := congrArg Prod.fst hy
    have hsnd : F (e.symm (y, 0)) = 0 := congrArg Prod.snd hy
    change F (y, (e.symm (y, 0)).2) = 0
    have hpair : (y, (e.symm (y, 0)).2) = e.symm (y, 0) :=
      Prod.ext hfst.symm rfl
    rw [hpair]
    exact hsnd
  · have hleft := e.eventually_left_inverse hmem
    rw [he] at hleft
    filter_upwards [hleft] with p hp hz
    have hGp : G p = (p.1, 0) := by simp [G, hz]
    rw [hGp] at hp
    exact (congrArg Prod.snd hp).symm

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DifferentiableCauchyTransform
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology


theorem IsAffineAlgebraic.zeroLocus_vanishingIdeal
    {n : ℕ} {V : Set (Affine n)} (hV : IsAffineAlgebraic V) :
    MvPolynomial.zeroLocus ℂ (MvPolynomial.vanishingIdeal ℂ V) = V := by
  apply Set.Subset.antisymm _ (MvPolynomial.zeroLocus_vanishingIdeal_le V)
  obtain ⟨P, rfl⟩ := hV
  intro z hz p hp
  exact hz p (fun w hw => hw p hp)

theorem polynomial_analytic_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (a : Fin d → ℂ) (b : ℂ)
    (hroot : Polynomial.eval₂ (MvPolynomial.eval a) b P = 0)
    (hsimple : Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative ≠ 0) :
    ∃ g : (Fin d → ℂ) → ℂ, AnalyticAt ℂ g a ∧ g a = b ∧
      (∀ᶠ y in 𝓝 a, Polynomial.eval₂ (MvPolynomial.eval y) (g y) P = 0) ∧
      (∀ᶠ p in 𝓝 (a, b), Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P = 0 →
        p.2 = g p.1) := by
  let F : ((Fin d → ℂ) × ℂ) → ℂ := fun p =>
    Polynomial.eval₂ (MvPolynomial.eval p.1) p.2 P
  have hF : AnalyticAt ℂ F (a, b) := by
    have hpoly : ∀ j : ℕ, AnalyticAt ℂ
        (fun p : ((Fin d → ℂ) × ℂ) => MvPolynomial.eval p.1 (P.coeff j)) (a, b) := by
      intro j
      exact (AnalyticOnNhd.eval_mvPolynomial (P.coeff j) _ (Set.mem_univ _)).comp
        ((ContinuousLinearMap.fst ℂ (Fin d → ℂ) ℂ).analyticAt _)
    simp only [F, Polynomial.eval₂_eq_sum_range]
    exact
      Finset.analyticAt_fun_sum (Finset.range (P.natDegree + 1)) (fun j _ =>
        (hpoly j).mul (((ContinuousLinearMap.snd ℂ (Fin d → ℂ) ℂ).analyticAt _).pow j))
  let L := fderiv ℂ F (a,b)
  have hL : HasFDerivAt F L (a,b) := hF.differentiableAt.hasFDerivAt
  have hv : L (0,1) = Polynomial.eval₂ (MvPolynomial.eval a) b P.derivative := by
    have h1 : HasDerivAt (fun z => F (a,z)) (L (0,1)) b :=
      hL.comp_hasDerivAt b ((hasDerivAt_const b a).prodMk (hasDerivAt_id b))
    have h2 := (P.map (MvPolynomial.eval a)).hasDerivAt b
    simp only [Polynomial.derivative_map, Polynomial.eval_map] at h2
    exact h1.unique h2
  exact analytic_implicit_scalar hF hroot L hL (hv ▸ hsimple)

open Set Filter Metric MeasureTheory
open scoped Topology

theorem differentiableAt_intervalIntegral_of_continuousOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {x : E} {r a b : ℝ} (hr : 0 < r)
    (F : E → ℝ → ℂ) (F' : E → ℝ → E →L[ℂ] ℂ)
    (hc : ContinuousOn (Function.uncurry F) (closedBall x r ×ˢ uIcc a b))
    (hc' : ContinuousOn (Function.uncurry F') (closedBall x r ×ˢ uIcc a b))
    (hd : ∀ y ∈ closedBall x r, ∀ t ∈ uIcc a b, HasFDerivAt (F · t) (F' y t) y) :
    DifferentiableAt ℂ (fun y => ∫ t in a..b, F y t) x := by
  let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x r).prod isCompact_uIcc).exists_bound_of_continuousOn hc'
  have hsec : ∀ y ∈ closedBall x r, ContinuousOn (F y) (uIcc a b) := by
    intro y hy
    exact hc.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hy, ht⟩)
  have hsec' : ContinuousOn (F' x) (uIcc a b) :=
    hc'.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ ht => ⟨mem_closedBall_self hr.le, ht⟩)
  have hfint : IntervalIntegrable (F x) volume a b :=
    (hsec x (mem_closedBall_self hr.le)).intervalIntegrable
  have hfmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) (volume.restrict (uIoc a b)) := by
    filter_upwards [closedBall_mem_nhds x hr] with y hy
    exact (hsec y hy).intervalIntegrable.aestronglyMeasurable_restrict_uIoc
  have hbound : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b →
      ∀ y ∈ closedBall x r, ‖F' y t‖ ≤ C :=
    Filter.Eventually.of_forall fun t ht y hy => hC (y, t) ⟨hy, uIoc_subset_uIcc ht⟩
  have hdiff : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc a b →
      ∀ y ∈ closedBall x r, HasFDerivAt (F · t) (F' y t) y :=
    Filter.Eventually.of_forall fun t ht y hy => hd y hy t (uIoc_subset_uIcc ht)
  have hderiv : HasFDerivAt (fun y => ∫ t in a..b, F y t)
      (∫ t in a..b, F' x t) x :=
    intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (closedBall_mem_nhds x hr) hfmeas hfint
      hsec'.intervalIntegrable.aestronglyMeasurable_restrict_uIoc hbound
      (intervalIntegrable_const (c := C)) hdiff
  exact hderiv.differentiableAt

theorem differentiableAt_circleIntegral_of_analyticOnNhd
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {x : E} {r R : ℝ} {c : ℂ} (hr : 0 < r) (hR : 0 ≤ R)
    (f : E × ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall x r ×ˢ sphere c R)) :
    DifferentiableAt ℂ (fun y => ∮ z in C(c, R), f (y, z)) x := by
  let ι : E →L[ℂ] E × ℂ := ContinuousLinearMap.inl ℂ E ℂ
  let F : E → ℝ → ℂ := fun y t => deriv (circleMap c R) t * f (y, circleMap c R t)
  let F' : E → ℝ → E →L[ℂ] ℂ := fun y t =>
    deriv (circleMap c R) t • (fderiv ℂ f (y, circleMap c R t)).comp ι
  have hcont : ContinuousOn f (closedBall x r ×ˢ sphere c R) := hf.continuousOn
  have hdercont : ContinuousOn (fderiv ℂ f) (closedBall x r ×ˢ sphere c R) := by
    intro p hp
    exact ((hf p hp).contDiffAt (n := 1)).continuousAt_fderiv (by decide) |>.continuousWithinAt
  have hparam : Continuous (fun p : E × ℝ => (p.1, circleMap c R p.2)) :=
    continuous_fst.prodMk ((continuous_circleMap c R).comp continuous_snd)
  have hmap : MapsTo (fun p : E × ℝ => (p.1, circleMap c R p.2))
      (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) (closedBall x r ×ˢ sphere c R) :=
    fun p hp => ⟨hp.1, circleMap_mem_sphere c hR p.2⟩
  have hdc : Continuous (fun p : E × ℝ => deriv (circleMap c R) p.2) := by
    simp only [deriv_circleMap]
    exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
  have hc : ContinuousOn (Function.uncurry F) (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) :=
    hdc.continuousOn.mul (hcont.comp hparam.continuousOn hmap)
  have hc' : ContinuousOn (Function.uncurry F') (closedBall x r ×ˢ uIcc 0 (2 * Real.pi)) :=
    hdc.continuousOn.smul ((hdercont.comp hparam.continuousOn hmap).clm_comp continuousOn_const)
  have hd : ∀ y ∈ closedBall x r, ∀ t ∈ uIcc 0 (2 * Real.pi),
      HasFDerivAt (F · t) (F' y t) y := by
    intro y hy t _
    have hp := (hf (y, circleMap c R t) ⟨hy, circleMap_mem_sphere c hR t⟩).differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun y : E => (y, circleMap c R t)) ι y :=
      (hasFDerivAt_id y).prodMk (hasFDerivAt_const _ _)
    exact (hp.comp y hi).const_mul _
  change DifferentiableAt ℂ (fun y => ∫ t in 0..2 * Real.pi, F y t) x
  exact differentiableAt_intervalIntegral_of_continuousOn hr F F' hc hc' hd

theorem differentiableOn_cauchyTransform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (f : E × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (A ×ˢ sphere c R)) :
    DifferentiableOn ℂ (fun p : E × ℂ =>
      (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(c, R), (w - p.2)⁻¹ * f (p.1, w))
      (A ×ˢ ball c R) := by
  intro p hp
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hA.prod isOpen_ball).mem_nhds hp)
  let F : (E × ℂ) × ℂ → ℂ := fun q => (q.2 - q.1.2)⁻¹ * f (q.1.1, q.2)
  have hF : AnalyticOnNhd ℂ F (closedBall p r ×ˢ sphere c R) := by
    intro q hq
    have hqq := hsub hq.1
    have hne : q.2 - q.1.2 ≠ 0 := sub_ne_zero.mpr
      (Metric.sphere_disjoint_ball.ne_of_mem hq.2 hqq.2)
    let π₁ : (E × ℂ) × ℂ →L[ℂ] E :=
      (ContinuousLinearMap.fst ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ (E × ℂ) ℂ)
    let π₂ : (E × ℂ) × ℂ →L[ℂ] ℂ :=
      (ContinuousLinearMap.snd ℂ E ℂ).comp (ContinuousLinearMap.fst ℂ (E × ℂ) ℂ)
    let π₃ : (E × ℂ) × ℂ →L[ℂ] ℂ := ContinuousLinearMap.snd ℂ (E × ℂ) ℂ
    have ha : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => q.2 - q.1.2) q :=
      (π₃.analyticAt q).sub (π₂.analyticAt q)
    have hb : AnalyticAt ℂ (fun q : (E × ℂ) × ℂ => f (q.1.1, q.2)) q :=
      (hf (q.1.1, q.2) ⟨hqq.1, hq.2⟩).comp (f := (π₁.prod π₃))
        ((π₁.prod π₃).analyticAt q)
    exact (ha.inv hne).mul hb
  exact ((differentiableAt_circleIntegral_of_analyticOnNhd hr hR.le F hF).const_mul
    (2 * Real.pi * Complex.I)⁻¹).differentiableWithinAt

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialRemovableLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


theorem bounded_removable_finite
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {U E : Set ℂ} (hU : IsOpen U) (hE : E.Finite)
    (f : ℂ → F) (hf : DifferentiableOn ℂ f (U \ E))
    {B : ℝ} (hb : ∀ z ∈ U \ E, ‖f z‖ ≤ B) :
    ∃ g : ℂ → F, AnalyticOnNhd ℂ g U ∧
      (∀ z ∈ U \ E, g z = f z) ∧ (∀ z ∈ U, ‖g z‖ ≤ B) := by
  classical
  let g : ℂ → F := fun z => if z ∈ E then limUnder (𝓝[≠] z) f else f z
  have heq : ∀ z ∈ U \ E, g z = f z := fun z hz => ite_eq_right hz.2
  have hreg : ∀ z ∈ U \ E, AnalyticAt ℂ g z := by
    intro z hz
    have hh : ∀ᶠ w in 𝓝 z, g w = f w := by
      filter_upwards [(hU.sdiff hE.isClosed).mem_nhds hz] with w hw
      exact heq w hw
    exact (hf.analyticAt ((hU.sdiff hE.isClosed).mem_nhds hz)).congr (Filter.EventuallyEq.symm hh)
  have hpunct : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∈ U \ E := by
    intro z hz
    have hv : U \ (E \ {z}) ∈ 𝓝 z :=
      (hU.sdiff (hE.subset (Set.sdiff_subset : E \ {z} ⊆ E)).isClosed).mem_nhds ⟨hz, by simp⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hv] with w hw hw'
    refine ⟨hw'.1, ?_⟩
    intro hwE
    exact hw'.2 ⟨hwE, hw⟩
  have hlim : ∀ z ∈ U, z ∈ E → Tendsto f (𝓝[≠] z) (𝓝 (g z)) := by
    intro z hz hzE
    change Tendsto f (𝓝[≠] z) (𝓝 (if z ∈ E then _ else _))
    rw [ite_eq_left hzE]
    apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under
    · filter_upwards [hpunct z hz] with w hw
      exact hf.differentiableAt ((hU.sdiff hE.isClosed).mem_nhds hw)
    · refine ⟨B + ‖f z‖, ?_⟩
      change ∀ᶠ w in 𝓝[≠] z, ‖f w - f z‖ ≤ B + ‖f z‖
      filter_upwards [hpunct z hz] with w hw
      exact (norm_sub_le _ _).trans (add_le_add (hb w hw) le_rfl)
  refine ⟨g, ?_, heq, ?_⟩
  · intro z hz
    by_cases hzE : z ∈ E
    · have hc : ContinuousAt g z := by
        rw [← continuousWithinAt_compl_self]
        apply (hlim z hz hzE).congr'
        filter_upwards [hpunct z hz] with w hw
        exact (heq w hw).symm
      apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hc
      filter_upwards [hpunct z hz] with w hw
      exact (hreg w hw).differentiableAt
    · exact hreg z ⟨hz, hzE⟩
  · intro z hz
    by_cases hzE : z ∈ E
    · exact le_of_tendsto (hlim z hz hzE).norm
        ((hpunct z hz).mono fun w hw => hb w hw)
    · rw [heq z ⟨hz, hzE⟩]
      exact hb z ⟨hz, hzE⟩

theorem bounded_removable_finite_fibers
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    {A : Set E} (hA : IsOpen A) {c : ℂ} {R S : ℝ} (hR : 0 < R) (hRS : R < S)
    (Z : Set (E × ℂ)) (hfinite : ∀ a ∈ A, {z | (a, z) ∈ Z}.Finite)
    (hboundary : ∀ a ∈ A, ∀ z ∈ sphere c R, (a, z) ∉ Z)
    (f : E × ℂ → ℂ) (hf : AnalyticOnNhd ℂ f ((A ×ˢ ball c S) \ Z))
    {B : ℝ} (hb : ∀ p ∈ (A ×ˢ ball c S) \ Z, ‖f p‖ ≤ B) :
    ∃ g : E × ℂ → ℂ, DifferentiableOn ℂ g (A ×ˢ ball c R) ∧
      EqOn g f ((A ×ˢ ball c R) \ Z) ∧ (∀ p ∈ A ×ˢ ball c R, ‖g p‖ ≤ B) := by
  let g : E × ℂ → ℂ := fun p =>
    (2 * Real.pi * Complex.I)⁻¹ * ∮ w in C(c, R), (w - p.2)⁻¹ * f (p.1, w)
  have hfb : AnalyticOnNhd ℂ f (A ×ˢ sphere c R) := by
    intro p hp
    exact hf p ⟨⟨hp.1, sphere_subset_ball hRS hp.2⟩, hboundary p.1 hp.1 p.2 hp.2⟩
  have hproperties : ∀ a ∈ A, ∃ ga : ℂ → ℂ,
      (∀ z ∈ ball c R, g (a, z) = ga z) ∧
      (∀ z ∈ ball c S \ {z | (a, z) ∈ Z}, ga z = f (a, z)) ∧
      (∀ z ∈ ball c S, ‖ga z‖ ≤ B) := by
    intro a ha
    have hd : DifferentiableOn ℂ (fun z => f (a, z)) (ball c S \ {z | (a, z) ∈ Z}) := by
      intro z hz
      exact ((hf (a, z) ⟨⟨ha, hz.1⟩, hz.2⟩).differentiableAt.comp z
        ((differentiableAt_const a).prodMk differentiableAt_id)).differentiableWithinAt
    obtain ⟨ga, hga, heq, hbound⟩ := bounded_removable_finite isOpen_ball (hfinite a ha)
      (fun z => f (a, z)) hd (fun z hz => hb (a, z) ⟨⟨ha, hz.1⟩, hz.2⟩)
    refine ⟨ga, ?_, heq, hbound⟩
    intro z hz
    have hcauchy : (2 * Real.pi * Complex.I)⁻¹ *
        (∮ w in C(c, R), (w - z)⁻¹ * ga w) = ga z := by
      simpa only [smul_eq_mul] using
        Complex.two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
          (s := ∅) Set.countable_empty hz
          (hga.continuousOn.mono (closedBall_subset_ball hRS))
          (fun w hw => (hga w ((ball_subset_ball hRS.le) hw.1)).differentiableAt)
    change (2 * Real.pi * Complex.I)⁻¹ *
        (∮ w in C(c, R), (w - z)⁻¹ * f (a, w)) = ga z
    rw [← hcauchy]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro w hw
    dsimp only
    rw [heq w ⟨sphere_subset_ball hRS hw, hboundary a ha w hw⟩]
  refine ⟨g, differentiableOn_cauchyTransform hA hR f hfb, ?_, ?_⟩
  · intro p hp
    obtain ⟨ga, heq, heqf, _⟩ := hproperties p.1 hp.1.1
    exact (heq p.2 hp.1.2).trans (heqf p.2 ⟨ball_subset_ball hRS.le hp.1.2, hp.2⟩)
  · intro p hp
    obtain ⟨ga, heq, _, hbound⟩ := hproperties p.1 hp.1
    rw [heq p.2 hp.2]
    exact hbound p.2 (ball_subset_ball hRS.le hp.2)

theorem eval_linePolynomial {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (x v : Fin n → ℂ) (z : ℂ) :
    (linePolynomial P x v).eval z = MvPolynomial.eval (x + z • v) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [linePolynomial]
  | add p q hp hq => simpa [linePolynomial] using congrArg₂ (· + ·) hp hq
  | mul_X p i hp =>
    change Polynomial.eval z ((MvPolynomial.eval₂Hom Polynomial.C
      (fun j => Polynomial.C (x j) + Polynomial.X * Polynomial.C (v j)))
      (p * MvPolynomial.X i)) = _
    simp only [map_mul, MvPolynomial.eval₂Hom_X', Polynomial.eval_mul,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X,
      MvPolynomial.eval_X, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact congrArg (fun w => w * (x i + z * v i)) hp

theorem exists_eval_ne_zero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    ∃ x : Fin n → ℂ, MvPolynomial.eval x P ≠ 0 := by
  by_contra! h
  exact hP (MvPolynomial.funext (fun x => by simpa using h x))

theorem polynomial_eventually_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, p.eval w ≠ 0 := by
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  have hclosed : IsClosed ({w | p.IsRoot w} \ {z}) :=
    (hfin.subset sdiff_subset).isClosed
  have hn : ({w | p.IsRoot w} \ {z})ᶜ ∈ 𝓝 z := hclosed.isOpen_compl.mem_nhds (by simp)
  filter_upwards [mem_nhdsWithin_of_mem_nhds hn, self_mem_nhdsWithin] with w hw hwz
  exact fun heq => hw ⟨heq, hwz⟩

theorem exists_polynomial_root_free_sphere {p : Polynomial ℂ} (hp : p ≠ 0)
    {T : ℝ} (hT : 0 < T) :
    ∃ R : ℝ, 0 < R ∧ R < T ∧ ∀ z ∈ sphere (0 : ℂ) R, p.eval z ≠ 0 := by
  have hfin := Polynomial.finite_setOfPred_isRoot hp
  have hclosed : IsClosed ({w | p.IsRoot w} \ {0}) :=
    (hfin.subset sdiff_subset).isClosed
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp
    (hclosed.isOpen_compl.mem_nhds (show (0 : ℂ) ∉ {w | p.IsRoot w} \ {0} by simp))
  let R := min T ε / 2
  have hR : 0 < R := half_pos (lt_min hT hε)
  have hRT : R < T := (half_lt_self (lt_min hT hε)).trans_le (min_le_left _ _)
  have hRε : R < ε := (half_lt_self (lt_min hT hε)).trans_le (min_le_right _ _)
  refine ⟨R, hR, hRT, ?_⟩
  intro z hz heq
  have hnorm : ‖z‖ = R := by simpa only [mem_sphere, dist_zero_right] using hz
  have hz0 : z ≠ 0 := by
    intro h
    have hh : 0 = R := by simpa [h] using hnorm
    exact hR.ne' hh.symm
  exact hsub (show z ∈ ball 0 ε by simpa only [mem_ball, dist_zero_right, hnorm] using hRε)
    ⟨heq, hz0⟩

theorem dense_polynomial_nonzero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0) :
    Dense {x | MvPolynomial.eval x P ≠ 0} := by
  obtain ⟨q, hq⟩ := exists_eval_ne_zero P hP
  intro x
  let v := q - x
  have hp : linePolynomial P x v ≠ 0 := by
    intro h
    have hh := eval_linePolynomial P x v 1
    simp only [h, Polynomial.eval_zero, one_smul] at hh
    exact hq (by simpa [v] using hh.symm)
  have hc : Continuous (fun z : ℂ => x + z • v) := continuous_const.add (continuous_id.smul continuous_const)
  have ht : Tendsto (fun z : ℂ => x + z • v) (𝓝[≠] 0) (𝓝 x) := by
    simpa using hc.continuousAt.tendsto.mono_left (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  exact mem_closure_of_tendsto ht ((polynomial_eventually_ne_zero hp 0).mono fun z hz => by
    simpa only [eval_linePolynomial, Set.mem_ofPred_eq] using hz)

theorem finite_polynomial_line_roots {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (x v : Fin n → ℂ) {R : ℝ} (hR : 0 < R)
    (h : ∀ z ∈ sphere (0 : ℂ) R, MvPolynomial.eval (x + z • v) P ≠ 0) :
    {z : ℂ | MvPolynomial.eval (x + z • v) P = 0}.Finite := by
  have hpnz : linePolynomial P x v ≠ 0 := by
    intro he
    have hz : (R : ℂ) ∈ sphere 0 R := by
      simp only [mem_sphere, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    have hn := h (R : ℂ) hz
    rw [← eval_linePolynomial, he, Polynomial.eval_zero] at hn
    exact hn rfl
  simpa only [Polynomial.IsRoot.def, eval_linePolynomial] using
    (Polynomial.finite_setOfPred_isRoot hpnz)

theorem bounded_polynomial_removable_local {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {x | MvPolynomial.eval x P = 0}))
    {B : ℝ} (hb : ∀ x ∈ U \ {x | MvPolynomial.eval x P = 0}, ‖f x‖ ≤ B)
    {a : Fin n → ℂ} (ha : a ∈ U) :
    ∃ A : Set (Fin n → ℂ), IsOpen A ∧ a ∈ A ∧ A ⊆ U ∧
      ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g A ∧
        EqOn g f (A \ {x | MvPolynomial.eval x P = 0}) ∧
        ∀ x ∈ A, ‖g x‖ ≤ B := by
  obtain ⟨q, hq⟩ := exists_eval_ne_zero P hP
  let v := q - a
  let L : ((Fin n → ℂ) × ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.fst ℂ _ _ + (ContinuousLinearMap.snd ℂ _ _).smulRight v
  have hLv : ∀ p, L p = p.1 + p.2 • v := fun _ => rfl
  have hp : linePolynomial P a v ≠ 0 := by
    intro h
    have hh := eval_linePolynomial P a v 1
    simp only [h, Polynomial.eval_zero, one_smul] at hh
    exact hq (by simpa [v] using hh.symm)
  have hc : Continuous (fun z : ℂ => a + z • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  obtain ⟨S, hS, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    ((hU.preimage hc).mem_nhds (show (0 : ℂ) ∈ (fun z => a + z • v) ⁻¹' U by simpa using ha))
  obtain ⟨R, hR, hRS, hRf⟩ := exists_polynomial_root_free_sphere hp hS
  obtain ⟨A₁, V₁, hA₁, _, ha₁, hV₁, hprod₁⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := a)) (isCompact_closedBall (0 : ℂ) S)
      (hU.preimage L.continuous) (by
        rintro ⟨x, z⟩ ⟨hx, hz⟩
        have hx' : x = a := mem_singleton_iff.mp hx
        subst x
        exact hsub hz)
  obtain ⟨A₂, V₂, hA₂, _, ha₂, hV₂, hprod₂⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := a)) (isCompact_sphere (0 : ℂ) R)
      (isOpen_ne_fun (P.continuous_eval.comp L.continuous) continuous_const) (by
        rintro ⟨x, z⟩ ⟨hx, hz⟩
        have hx' : x = a := mem_singleton_iff.mp hx
        subst x
        change MvPolynomial.eval (a + z • v) P ≠ 0
        rw [← eval_linePolynomial]
        exact hRf z hz)
  let A := A₁ ∩ A₂
  have hA : IsOpen A := hA₁.inter hA₂
  have haA : a ∈ A := ⟨ha₁ (mem_singleton a), ha₂ (mem_singleton a)⟩
  have hmap : MapsTo L (A ×ˢ ball (0 : ℂ) S) U := by
    intro p hp
    exact hprod₁ ⟨hp.1.1, hV₁ (ball_subset_closedBall hp.2)⟩
  let Z : Set ((Fin n → ℂ) × ℂ) := {p | MvPolynomial.eval (L p) P = 0}
  have havoid : ∀ x ∈ A, ∀ z ∈ sphere (0 : ℂ) R, (x, z) ∉ Z := by
    intro x hx z hz
    exact hprod₂ ⟨hx.2, hV₂ hz⟩
  have hfinite : ∀ x ∈ A, {z | (x, z) ∈ Z}.Finite := by
    intro x hx
    exact finite_polynomial_line_roots P x v hR (havoid x hx)
  have hfl : AnalyticOnNhd ℂ (f ∘ L) ((A ×ˢ ball (0 : ℂ) S) \ Z) :=
    hf.comp (fun p _ => L.analyticAt p) (fun p hp => ⟨hmap hp.1, hp.2⟩)
  obtain ⟨g, hg, heq, hbound⟩ := bounded_removable_finite_fibers hA hR hRS Z hfinite havoid
    (f ∘ L) hfl (fun p hp => hb (L p) ⟨hmap hp.1, hp.2⟩)
  refine ⟨A, hA, haA, ?_, (fun x => g (x, 0)), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hLv, zero_smul, add_zero] using hmap (show (x, 0) ∈ A ×ˢ ball 0 S from
      ⟨hx, mem_ball_self hS⟩)
  · intro x hx
    have hgx := hg.differentiableAt ((hA.prod isOpen_ball).mem_nhds
      (show (x, (0 : ℂ)) ∈ A ×ˢ ball 0 R from ⟨hx, mem_ball_self hR⟩))
    exact (hgx.comp x (differentiableAt_id.prodMk (differentiableAt_const 0))).differentiableWithinAt
  · intro x hx
    have hz : (x, (0 : ℂ)) ∉ Z := by simpa only [Z, mem_ofPred_eq, hLv, zero_smul, add_zero] using hx.2
    simpa only [Function.comp_apply, hLv, zero_smul, add_zero] using heq
      (show (x, (0 : ℂ)) ∈ (A ×ˢ ball 0 R) \ Z from ⟨⟨hx.1, mem_ball_self hR⟩, hz⟩)
  · intro x hx
    exact hbound (x, 0) ⟨hx, mem_ball_self hR⟩

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_IntegralPrimitive
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology


theorem glue_dense_differentiable_extensions
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U D : Set E} (hD : Dense D) (f : E → ℂ) {B : ℝ}
    (hlocal : ∀ x ∈ U, ∃ A : Set E, IsOpen A ∧ x ∈ A ∧
      ∃ g : E → ℂ, DifferentiableOn ℂ g A ∧ EqOn g f (A ∩ D) ∧
        ∀ y ∈ A, ‖g y‖ ≤ B) :
    ∃ g : E → ℂ, DifferentiableOn ℂ g U ∧ EqOn g f (U ∩ D) ∧
      ∀ x ∈ U, ‖g x‖ ≤ B := by
  let g : E → ℂ := fun x => limUnder (𝓝[D] x) f
  have hvalue {A : Set E} (hA : IsOpen A) (ga : E → ℂ)
      (hga : DifferentiableOn ℂ ga A) (heq : EqOn ga f (A ∩ D))
      {x : E} (hx : x ∈ A) : g x = ga x := by
    have : (𝓝[D] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hD x)
    have ht : Tendsto ga (𝓝[D] x) (𝓝 (ga x)) :=
      (hga.differentiableAt (hA.mem_nhds hx)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hevent : ga =ᶠ[𝓝[D] x] f := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hA.mem_nhds hx), self_mem_nhdsWithin] with y hy hyD
      exact heq ⟨hy, hyD⟩
    exact (ht.congr' hevent).limUnder_eq
  refine ⟨g, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨A, hA, hxA, ga, hga, heq, _⟩ := hlocal x hx
    have hh : g =ᶠ[𝓝 x] ga := Filter.Eventually.mono (hA.mem_nhds hxA) (fun y hy => hvalue hA ga hga heq hy)
    exact ((hga.differentiableAt (hA.mem_nhds hxA)).congr_of_eventuallyEq hh).differentiableWithinAt
  · intro x hx
    obtain ⟨A, hA, hxA, ga, hga, heq, _⟩ := hlocal x hx.1
    exact (hvalue hA ga hga heq hxA).trans (heq ⟨hxA, hx.2⟩)
  · intro x hx
    obtain ⟨A, hA, hxA, ga, hga, heq, hb⟩ := hlocal x hx
    rw [hvalue hA ga hga heq hxA]
    exact hb x hxA

theorem bounded_polynomial_removable {n : ℕ}
    (P : MvPolynomial (Fin n) ℂ) (hP : P ≠ 0)
    {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (hf : AnalyticOnNhd ℂ f (U \ {x | MvPolynomial.eval x P = 0}))
    {B : ℝ} (hb : ∀ x ∈ U \ {x | MvPolynomial.eval x P = 0}, ‖f x‖ ≤ B) :
    ∃ g : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ g U ∧
      EqOn g f (U \ {x | MvPolynomial.eval x P = 0}) ∧
      ∀ x ∈ U, ‖g x‖ ≤ B := by
  apply glue_dense_differentiable_extensions (dense_polynomial_nonzero P hP) f
  intro a ha
  obtain ⟨A, hA, haA, _, g, hg, heq, hb⟩ :=
    bounded_polynomial_removable_local P hP hU f hf hb ha
  exact ⟨A, hA, haA, g, hg, heq, hb⟩

open Polynomial

theorem resultant_derivative_ne_zero_of_generic_separable
    {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (p : R[X])
    (hp : (p.map (algebraMap R K)).Separable) :
    p.resultant p.derivative ≠ 0 := by
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have h := Polynomial.resultant_ne_zero (p.map (algebraMap R K))
    ((p.map (algebraMap R K)).derivative) hp
  rw [Polynomial.derivative_map,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.natDegree_map_eq_of_injective hinj,
    Polynomial.resultant_map_map] at h
  exact fun hz => h (by rw [hz, map_zero])

theorem separable_map_of_resultant_ne_zero
    {R K : Type*} [CommRing R] [Field K]
    (p : R[X]) (hp : p.Monic) (e : R →+* K)
    (hd : e (p.resultant p.derivative) ≠ 0) :
    (p.map e).Separable := by
  by_cases hdeg : p.natDegree = 0
  · rw [eq_one_of_monic_natDegree_zero hp hdeg, Polynomial.map_one]
    exact Polynomial.separable_one
  obtain ⟨a, b, _, _, hab⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    p p.derivative le_rfl le_rfl (Or.inl hdeg)
  have hh := congrArg (Polynomial.map e) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C] at hh
  refine ⟨C ((e (p.resultant p.derivative))⁻¹) * a.map e,
    C ((e (p.resultant p.derivative))⁻¹) * b.map e, ?_⟩
  rw [Polynomial.derivative_map]
  calc
    _ = C ((e (p.resultant p.derivative))⁻¹) *
        (p.map e * a.map e + p.derivative.map e * b.map e) := by ring
    _ = 1 := by rw [hh, ← C_mul, inv_mul_cancel₀ hd, C_1]

theorem integral_minpoly_resultant_ne_zero
    {R S K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
    (x : S) (hx : IsIntegral R x) :
    (minpoly R x).resultant (minpoly R x).derivative ≠ 0 := by
  apply resultant_derivative_ne_zero_of_generic_separable (K := K)
  exact (((minpoly.monic hx).irreducible_iff_irreducible_map_fraction_map).mp
    (minpoly.irreducible hx)).separable

theorem polynomial_analytic_sheets {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (hP : P.Monic)
    (a : Fin d → ℂ) (ha : (P.map (MvPolynomial.eval a)).Separable) :
    ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → ℂ) (W : Set (Fin d → ℂ)),
      I.card = P.natDegree ∧ IsOpen W ∧ a ∈ W ∧
      (∀ i, AnalyticOnNhd ℂ (g i) W) ∧ (∀ i, g i a = i.val) ∧
      ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
        ∀ z : ℂ, Polynomial.eval₂ (MvPolynomial.eval y) z P = 0 ↔
          ∃ i, g i y = z := by
  classical
  let I : Finset ℂ := (P.map (MvPolynomial.eval a)).roots.toFinset
  have hcard : I.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots ha),
      IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ (hP ▸ isUnit_one)]
  have hi (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P = 0 := by
    have h := Polynomial.mem_roots (hP.map (MvPolynomial.eval a)).ne_zero |>.mp
      (Multiset.mem_toFinset.mp i.property)
    simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using h
  have hs (i : I) : Polynomial.eval₂ (MvPolynomial.eval a) i.val P.derivative ≠ 0 := by
    simpa only [Polynomial.eval₂_id, Polynomial.derivative_map,
      Polynomial.eval_map] using
      ha.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := i.val)
        (by simpa only [Polynomial.eval₂_id, Polynomial.eval_map] using hi i)
  choose g hg hga hgr _hgu using fun i : I => polynomial_analytic_root P a i.val (hi i) (hs i)
  have hgi : ∀ᶠ y in 𝓝 a, Function.Injective (fun i => g i y) := by
    have hj : ∀ i j : I, ∀ᶠ y in 𝓝 a, i ≠ j → g i y ≠ g j y := by
      intro i j
      by_cases hij : i = j
      · exact Filter.Eventually.of_forall fun _ h => (h hij).elim
      · have hval : g i a ≠ g j a := by
          rw [hga, hga]
          exact fun h => hij (Subtype.ext h)
        exact ((hg i).continuousAt.ne_iff_eventually_ne (hg j).continuousAt).mp hval |>.mono
          (fun _ hh _ => hh)
    filter_upwards [Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (hj i))] with y hy
    intro i j hij
    by_contra h
    exact hy i j h hij
  have hall : ∀ᶠ y in 𝓝 a,
      (∀ i, AnalyticAt ℂ (g i) y) ∧
      (∀ i, Polynomial.eval₂ (MvPolynomial.eval y) (g i y) P = 0) ∧
      Function.Injective (fun i => g i y) := by
    exact (Filter.eventually_all.mpr (fun i => (hg i).eventually_analyticAt)).and
      ((Filter.eventually_all.mpr hgr).and hgi)
  obtain ⟨W, hWsub, hW, haW⟩ := _root_.mem_nhds_iff.mp hall
  refine ⟨I, g, W, hcard, hW, haW, fun i y hy => (hWsub hy).1 i, hga, ?_⟩
  intro y hy
  have hyroot := (hWsub hy).2.1
  have hyinj := (hWsub hy).2.2
  refine ⟨hyinj, ?_⟩
  let J : Finset ℂ := Finset.univ.image (fun i : I => g i y)
  let K : Finset ℂ := (P.map (MvPolynomial.eval y)).roots.toFinset
  have hJK : J ⊆ K := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hP.map _).ne_zero).mpr
      (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hyroot i))
  have hJcard : J.card = I.card := by
    rw [Finset.card_image_of_injective _ hyinj]
    simp
  have hKcard : K.card ≤ P.natDegree := by
    exact (Multiset.toFinset_card_le _).trans (le_of_eq
      (IsAlgClosed.card_roots_map_eq_natDegree_of_isUnit_leadingCoeff _ (hP ▸ isUnit_one)))
  have hJKeq : J = K := Finset.eq_of_subset_of_card_le hJK (by rw [hJcard, hcard]; exact hKcard)
  intro z
  constructor
  · intro hz
    have hzK : z ∈ K := Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hP.map _).ne_zero).mpr
        (by simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using hz))
    rw [← hJKeq] at hzK
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hzK
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    exact hyroot i

open Polynomial Algebra
open scoped nonZeroDivisors

theorem exists_integral_primitive
    {R S K E : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field E] [Algebra R S] [FaithfulSMul R S]
    [Algebra R K] [IsFractionRing R K] [Algebra S E] [IsFractionRing S E]
    [Algebra R E] [Algebra K E] [IsScalarTower R S E] [IsScalarTower R K E]
    [Algebra.IsAlgebraic R S] [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ∃ t : S, Algebra.adjoin K {algebraMap S E t} = ⊤ := by
  let b := Field.powerBasisOfFiniteOfSeparable K E
  obtain ⟨s, t, ht⟩ := IsLocalization.exists_integer_multiple
    (algebraMapSubmonoid S R⁰) b.gen
  obtain ⟨r, hr, hrs⟩ := s.property
  have hr0 : (r : R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
  have hrK : algebraMap R K r ≠ 0 :=
    fun h => hr0 (IsFractionRing.injective R K (h.trans (map_zero _).symm))
  have ht' : algebraMap S E t = (algebraMap R K r) • b.gen := by
    rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K E]
    rw [IsScalarTower.algebraMap_apply R S E, hrs]
    simpa only [Algebra.smul_def] using ht
  refine ⟨t, b.adjoin_eq_top_of_gen_mem_adjoin ?_⟩
  have hmem := (Algebra.adjoin K {algebraMap S E t}).smul_mem
    (Algebra.self_mem_adjoin_singleton K (algebraMap S E t)) (algebraMap R K r)⁻¹
  have hs : (algebraMap R K r)⁻¹ • algebraMap S E t = b.gen := by
    rw [ht', smul_smul, inv_mul_cancel₀ hrK, one_smul]
  rwa [hs] at hmem

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteAlgebraGenericSheets
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors


theorem primitive_polynomial_representation
    {R S K E : Type*} [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Field K] [Field E] [Algebra R S] [Algebra R K] [IsFractionRing R K]
    [Algebra S E] [IsFractionRing S E] [Algebra R E] [Algebra K E]
    [IsScalarTower R S E] [IsScalarTower R K E]
    (t : S) (ht : Algebra.adjoin K {algebraMap S E t} = ⊤) (x : S) :
    ∃ r : R, r ≠ 0 ∧ ∃ q : R[X], r • x = aeval t q := by
  have hx : algebraMap S E x ∈ Algebra.adjoin K {algebraMap S E t} := by
    rw [ht]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, hp⟩ := hx
  obtain ⟨r, hr, hq⟩ := IsLocalization.integerNormalization_spec R⁰ p
  refine ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr,
    IsLocalization.integerNormalization R⁰ p, ?_⟩
  apply IsFractionRing.injective S E
  have he := congrArg (aeval (algebraMap S E t)) hq
  rw [Polynomial.aeval_map_algebraMap] at he
  rw [AlgHom.map_smul_of_tower] at he
  change (aeval (algebraMap S E t)) p = algebraMap S E x at hp
  rw [hp] at he
  rw [Polynomial.aeval_algebraMap_apply] at he
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply R S E]
  simpa only [Algebra.smul_def] using he.symm

theorem finite_integral_primitive_representations
    {R S : Type*} [CommRing R] [IsDomain R] [CharZero R]
    [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Module.Finite R S] :
    ∃ t : S, ∀ x : S, ∃ r : R, r ≠ 0 ∧ ∃ q : R[X], r • x = aeval t q := by
  let := FractionRing.liftAlgebra (R := R) (K := FractionRing S)
  obtain ⟨t, ht⟩ := exists_integral_primitive (R := R) (S := S)
    (K := FractionRing R) (E := FractionRing S)
  exact ⟨t, primitive_polynomial_representation (K := FractionRing R)
    (E := FractionRing S) t ht⟩

theorem extend_algHom_of_integral
    {k A B : Type*} [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    [FaithfulSMul A B] [Algebra.IsIntegral A B] [Algebra.FiniteType k B]
    (e : A →ₐ[k] k) :
    ∃ f : B →ₐ[k] k, ∀ a : A, f (algebraMap A B a) = e a := by
  let m := RingHom.ker e
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective e
    (fun x => ⟨algebraMap k A x, e.commutes x⟩)
  let := hm
  have hker : RingHom.ker (algebraMap A B) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := B) m (by rw [hker]; exact bot_le)
  let := hQmax
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  let : Module.Finite k (B ⧸ Q) := finite_of_finite_type_of_isJacobsonRing k (B ⧸ Q)
  let f : B →ₐ[k] k := IsAlgClosed.lift.comp (Ideal.Quotient.mkₐ k Q)
  refine ⟨f, fun a => ?_⟩
  have ham : a - algebraMap k A (e a) ∈ m := by
    change e (a - algebraMap k A (e a)) = 0
    rw [map_sub, e.commutes]; simp
  have haQ : algebraMap A B (a - algebraMap k A (e a)) ∈ Q := by
    change a - algebraMap k A (e a) ∈ Ideal.comap (algebraMap A B) Q
    rw [hQ]; exact ham
  have hz : f (algebraMap A B (a - algebraMap k A (e a))) = 0 := by
    change IsAlgClosed.lift (Ideal.Quotient.mk Q _) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr haQ, map_zero]
  rw [map_sub, map_sub, ← IsScalarTower.algebraMap_apply k A B, f.commutes] at hz
  exact sub_eq_zero.mp hz

open Polynomial Algebra

theorem realize_specialized_minpoly_root
    {k R S : Type*} [Field k] [IsAlgClosed k]
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra k R] [Algebra k S] [Algebra R S]
    [IsScalarTower k R S] [Module.IsTorsionFree R S]
    [Algebra.IsIntegral R S] [Algebra.FiniteType k S]
    (e : R →ₐ[k] k) (t : S) (z : k)
    (hz : (minpoly R t).eval₂ e z = 0) :
    ∃ f : S →ₐ[k] k, (∀ r : R, f (algebraMap R S r) = e r) ∧ f t = z := by
  let A := Algebra.adjoin R ({t} : Set S)
  have ht : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  let eqv := minpoly.equivAdjoin ht
  let l := AdjoinRoot.liftAlgHom (minpoly R t) e z hz
  let ea : A →ₐ[k] k := l.comp (eqv.symm.restrictScalars k).toAlgHom
  let : Algebra.IsIntegral A S := Algebra.IsIntegral.tower_top R
  have hinj : Function.Injective (algebraMap A S) := Subtype.val_injective
  let : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hinj
  obtain ⟨f, hf⟩ := extend_algHom_of_integral (B := S) ea
  refine ⟨f, ?_, ?_⟩
  · intro r
    rw [IsScalarTower.algebraMap_apply R A S, hf]
    change l (eqv.symm (algebraMap R A r)) = e r
    rw [eqv.symm.commutes]
    exact AdjoinRoot.liftAlgHom_of (minpoly R t) e z hz r
  · let ta : A := ⟨t, Algebra.self_mem_adjoin_singleton R t⟩
    have hta : eqv (AdjoinRoot.root (minpoly R t)) = ta := by
      apply Subtype.ext
      simp [eqv, minpoly.equivAdjoin, AdjoinRoot.Minpoly.toAdjoin, ta]
    have hta' : eqv.symm ta = AdjoinRoot.root (minpoly R t) := by
      exact (eqv.symm_apply_eq).mpr hta.symm
    change f (algebraMap A S ta) = z
    rw [hf]
    change l (eqv.symm ta) = z
    rw [hta']
    exact AdjoinRoot.liftAlgHom_root (minpoly R t) e z hz

theorem algHom_aeval_of_base
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] [Algebra R S]
    (f : S →ₐ[k] k) (e : R →+* k)
    (hf : ∀ r, f (algebraMap R S r) = e r) (t : S) (q : R[X]) :
    f (aeval t q) = q.eval₂ e (f t) := by
  have heq : f.toRingHom.comp (algebraMap R S) = e := RingHom.ext hf
  change f.toRingHom (q.eval₂ (algebraMap R S) t) = _
  rw [Polynomial.hom_eval₂, heq]
  rfl

theorem analyticAt_polynomial_substitution {d : ℕ}
    (q : Polynomial (MvPolynomial (Fin d) ℂ))
    {g : (Fin d → ℂ) → ℂ} {a : Fin d → ℂ} (hg : AnalyticAt ℂ g a) :
    AnalyticAt ℂ (fun y => q.eval₂ (MvPolynomial.eval y) (g y)) a := by
  simp only [Polynomial.eval₂_eq_sum_range]
  exact Finset.analyticAt_fun_sum (Finset.range (q.natDegree + 1)) (fun j _ =>
    (AnalyticOnNhd.eval_mvPolynomial (q.coeff j) a (Set.mem_univ a)).mul (hg.pow j))

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiniteProperMapOpen
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem finite_algebra_generic_sheets_constant_degree {d n : ℕ}
    {S : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (MvPolynomial (Fin d) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S]
    [FaithfulSMul (MvPolynomial (Fin d) ℂ) S]
    [Module.Finite (MvPolynomial (Fin d) ℂ) S]
    (x : Fin n → S) (hx : Algebra.adjoin ℂ (Set.range x) = ⊤) :
    ∃ (D : MvPolynomial (Fin d) ℂ) (r : ℕ), D ≠ 0 ∧ 0 < r ∧
      ∀ a : Fin d → ℂ, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (W : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen W ∧ a ∈ W ∧
        (∀ i, AnalyticOnNhd ℂ (g i) W) ∧
        ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
          ∀ z : Fin n → ℂ,
            (∃ f : S →ₐ[ℂ] ℂ,
              (∀ r, f (algebraMap (MvPolynomial (Fin d) ℂ) S r) = MvPolynomial.eval y r) ∧
              (∀ j, f (x j) = z j)) ↔ ∃ i, g i y = z := by
  classical
  let R := MvPolynomial (Fin d) ℂ
  have : Algebra.FiniteType ℂ S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType ℂ R) (inferInstance : Algebra.FiniteType R S)
  obtain ⟨t, ht⟩ := finite_integral_primitive_representations (R := R) (S := S)
  choose r hr q hq using fun j => ht (x j)
  let p := minpoly R t
  have hi : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  have hp : p.Monic := minpoly.monic hi
  have hdisc : p.resultant p.derivative ≠ 0 :=
    integral_minpoly_resultant_ne_zero (K := FractionRing R) t hi
  let D := p.resultant p.derivative * ∏ j, r j
  have hD : D ≠ 0 := mul_ne_zero hdisc (Finset.prod_ne_zero_iff.mpr (fun j _ => hr j))
  refine ⟨D, p.natDegree, hD, minpoly.natDegree_pos hi, fun a ha => ?_⟩
  have hda : MvPolynomial.eval a (p.resultant p.derivative) ≠ 0 := by
    exact left_ne_zero_of_mul (by simpa only [D, map_mul] using ha)
  have hra : ∀ j, MvPolynomial.eval a (r j) ≠ 0 := by
    have h := right_ne_zero_of_mul (by simpa only [D, map_mul] using ha)
    rw [map_prod] at h
    exact fun j => Finset.prod_ne_zero_iff.mp h j (Finset.mem_univ j)
  obtain ⟨I, w, W₀, hcard, hW₀, haW₀, hw, _hwa, hsheets⟩ :=
    polynomial_analytic_sheets p hp a (separable_map_of_resultant_ne_zero p hp _ hda)
  let H : Set (Fin d → ℂ) := {y | ∀ j, MvPolynomial.eval y (r j) ≠ 0}
  have hH : IsOpen H := by
    have hH : H = ⋂ j, {y | MvPolynomial.eval y (r j) ≠ 0} := by
      ext y; simp [H]
    rw [hH]
    exact isOpen_iInter_of_finite (fun j => isOpen_ne.preimage
      (MvPolynomial.continuous_eval (r j)))
  let W := W₀ ∩ H
  let g : I → (Fin d → ℂ) → (Fin n → ℂ) := fun i y j =>
    (q j).eval₂ (MvPolynomial.eval y) (w i y) / MvPolynomial.eval y (r j)
  have hformula (y : Fin d → ℂ) (hy : y ∈ W) (f : S →ₐ[ℂ] ℂ)
      (hf : ∀ b : R, f (algebraMap R S b) = MvPolynomial.eval y b) :
      ∀ j, f (x j) = (q j).eval₂ (MvPolynomial.eval y) (f t) /
        MvPolynomial.eval y (r j) := by
    intro j
    apply (eq_div_iff (hy.2 j)).mpr
    have hh := congrArg f (hq j)
    rw [Algebra.smul_def, map_mul, hf, algHom_aeval_of_base f _ hf] at hh
    simpa only [mul_comm] using hh
  have hroot (y : Fin d → ℂ) (f : S →ₐ[ℂ] ℂ)
      (hf : ∀ b : R, f (algebraMap R S b) = MvPolynomial.eval y b) :
      p.eval₂ (MvPolynomial.eval y) (f t) = 0 := by
    rw [← algHom_aeval_of_base f _ hf, minpoly.aeval, map_zero]
  have hpoint (y : Fin d → ℂ) (hy : y ∈ W) (i : I) :
      ∃ f : S →ₐ[ℂ] ℂ,
        (∀ b : R, f (algebraMap R S b) = MvPolynomial.eval y b) ∧
        f t = w i y ∧ ∀ j, f (x j) = g i y j := by
    have hwi : p.eval₂ (MvPolynomial.eval y) (w i y) = 0 :=
      ((hsheets y hy.1).2 _).mpr ⟨i, rfl⟩
    obtain ⟨f, hf, hft⟩ := realize_specialized_minpoly_root
      (S := S) (MvPolynomial.aeval y) t (w i y) hwi
    refine ⟨f, hf, hft, fun j => ?_⟩
    rw [hformula y hy f hf j, hft]
  refine ⟨I, g, W, hcard, hW₀.inter hH, ⟨haW₀, hra⟩, ?_, ?_⟩
  · intro i y hy
    exact AnalyticAt.pi (fun j =>
      (analyticAt_polynomial_substitution (q j) (hw i y hy.1)).div
        (AnalyticOnNhd.eval_mvPolynomial (r j) y (Set.mem_univ y)) (hy.2 j))
  · intro y hy
    refine ⟨?_, fun z => ?_⟩
    · intro i j hij
      obtain ⟨f, _hf, hft, hfx⟩ := hpoint y hy i
      obtain ⟨f', _hf', hft', hfx'⟩ := hpoint y hy j
      have he : f = f' := AlgHom.ext_of_adjoin_eq_top hx (by
        rintro _ ⟨k, rfl⟩
        rw [hfx, hfx']
        exact congrFun hij k)
      apply (hsheets y hy.1).1
      change w i y = w j y
      rw [← hft, ← hft', he]
    · constructor
      · rintro ⟨f, hf, hfz⟩
        obtain ⟨i, hi⟩ := ((hsheets y hy.1).2 (f t)).mp (hroot y f hf)
        refine ⟨i, funext (fun j => ?_)⟩
        change (q j).eval₂ (MvPolynomial.eval y) (w i y) /
          MvPolynomial.eval y (r j) = z j
        rw [hi, ← hformula y hy f hf j, hfz]
      · rintro ⟨i, rfl⟩
        obtain ⟨f, hf, _hft, hfx⟩ := hpoint y hy i
        exact ⟨f, hf, hfx⟩

theorem continuous_affineCharacter {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ))
    (t : MvPolynomial (Fin n) ℂ ⧸ I) :
    Continuous (fun z : MvPolynomial.zeroLocus ℂ I => affineCharacter I z t) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective ℂ I t
  exact (MvPolynomial.continuous_eval p).comp continuous_subtype_val

theorem adjoin_quotientCoordinate {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    Algebra.adjoin ℂ (range (quotientCoordinate I)) = ⊤ := by
  have he : range (quotientCoordinate I) =
      (Ideal.Quotient.mkₐ ℂ I) '' range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℂ) :=
    Set.range_comp _ _
  rw [he, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top]
  exact (AlgHom.range_eq_top _).mpr (Ideal.Quotient.mkₐ_surjective ℂ I)

theorem affineCharacter_normalization {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ I))
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ I) (P j) = g (MvPolynomial.X j))
    (z : MvPolynomial.zeroLocus ℂ I) :
    (affineCharacter I z).comp g = MvPolynomial.aeval (fun j => MvPolynomial.eval z.val (P j)) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
  rw [← hP j, affineCharacter_mk]

theorem polynomial_root_near_of_small_eval (p : Polynomial ℂ) (hp : p.Monic)
    (b : ℂ) (ε : ℝ) (hε : 0 < ε) (hb : ‖p.eval b‖ < ε ^ p.natDegree) :
    ∃ z : ℂ, p.eval z = 0 ∧ dist z b < ε := by
  classical
  by_contra! h
  have hs : p.Splits := IsAlgClosed.splits p
  have hprod : (p.roots.map (fun _ => ε)).prod ≤
      (p.roots.map (fun z => ‖b - z‖)).prod := by
    apply Multiset.prod_map_le_prod_map₀
    · intro z _; exact hε.le
    · intro z hz
      have hr : p.eval z = 0 := (Polynomial.mem_roots hp.ne_zero).mp hz
      simpa only [dist_eq_norm, norm_sub_rev] using h z hr
  have he : (p.roots.map (fun z => ‖b - z‖)).prod = ‖p.eval b‖ := by
    rw [hs.eval_eq_prod_roots_of_monic hp]
    exact p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun z => b-z)
  rw [he, Multiset.map_const', Multiset.prod_replicate, ← hs.natDegree_eq_card_roots] at hprod
  exact (not_le_of_gt hb) hprod

theorem polynomial_eventually_exists_near_root {d : ℕ}
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (hP : P.Monic)
    (a : Fin d → ℂ) (b : ℂ)
    (hb : P.eval₂ (MvPolynomial.eval a) b = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 a, ∃ z : ℂ,
      P.eval₂ (MvPolynomial.eval y) z = 0 ∧ dist z b < ε := by
  have hc : Continuous (fun y : Fin d → ℂ => P.eval₂ (MvPolynomial.eval y) b) := by
    simp only [Polynomial.eval₂_eq_sum_range]
    exact continuous_finsetSum _ (fun j _ =>
      (MvPolynomial.continuous_eval (P.coeff j)).mul continuous_const)
  have he : ∀ᶠ y in 𝓝 a, ‖P.eval₂ (MvPolynomial.eval y) b‖ < ε ^ P.natDegree :=
    hc.norm.continuousAt.eventually (gt_mem_nhds (by
      change ‖P.eval₂ (MvPolynomial.eval a) b‖ < _
      rw [hb, _root_.norm_zero]; positivity))
  filter_upwards [he] with y hy
  obtain ⟨z, hz, hzb⟩ := polynomial_root_near_of_small_eval
    (P.map (MvPolynomial.eval y)) (hP.map _) b ε hε
      (by simpa only [Polynomial.eval_map, hP.natDegree_map] using hy)
  exact ⟨z, by simpa only [Polynomial.eval_map] using hz, hzb⟩

theorem finite_proper_map_open_at_of_root_realization
    {X : Type*} [TopologicalSpace X] {d : ℕ}
    (π : X → (Fin d → ℂ)) (hπ : IsProperMap π) (q : X)
    (hfin : Set.Finite {x : X | π x = π q})
    (s : X → ℂ) (hs : Continuous s)
    (hsep : ∀ x, π x = π q → s x = s q → x = q)
    (P : Polynomial (MvPolynomial (Fin d) ℂ)) (hP : P.Monic)
    (hq : P.eval₂ (MvPolynomial.eval (π q)) (s q) = 0)
    (hreal : ∀ y z, P.eval₂ (MvPolynomial.eval y) z = 0 →
      ∃ x, π x = y ∧ s x = z)
    {N : Set X} (hN : IsOpen N) (hqN : q ∈ N) :
    π '' N ∈ 𝓝 (π q) := by
  classical
  let B : Set ℂ := s '' ({x : X | π x = π q} ∩ Nᶜ)
  have hB : B.Finite := (hfin.inter_of_left Nᶜ).image s
  have hqB : s q ∉ B := by
    rintro ⟨x, ⟨hx, hxN⟩, he⟩
    have hxe := hsep x hx he
    exact hxN (hxe ▸ hqN)
  obtain ⟨ε, hε, hεB⟩ := Metric.mem_nhds_iff.mp (hB.isClosed.isOpen_compl.mem_nhds hqB)
  let F := s ⁻¹' Metric.closedBall (s q) (ε / 2) ∩ Nᶜ
  have hF : IsClosed F := (Metric.isClosed_closedBall.preimage hs).inter hN.isClosed_compl
  have hπF : IsClosed (π '' F) := hπ.isClosedMap F hF
  have haF : π q ∉ π '' F := by
    rintro ⟨x, ⟨hx, hxN⟩, hxa⟩
    have hxB : s x ∈ B := ⟨x, ⟨hxa, hxN⟩, rfl⟩
    have hxball : s x ∈ Metric.ball (s q) ε := by
      change dist (s x) (s q) < ε
      change dist (s x) (s q) ≤ ε / 2 at hx
      exact lt_of_le_of_lt hx (by linarith)
    exact hεB hxball hxB
  have h₁ : ∀ᶠ y in 𝓝 (π q), y ∉ π '' F := hπF.isOpen_compl.mem_nhds haF
  have h₂ := polynomial_eventually_exists_near_root P hP (π q) (s q) hq (ε / 2) (by positivity)
  filter_upwards [h₁, h₂] with y hy hroot
  obtain ⟨z, hz, hzb⟩ := hroot
  obtain ⟨x, hxy, hxz⟩ := hreal y z hz
  refine ⟨x, ?_, hxy⟩
  by_contra hxN
  apply hy
  refine ⟨x, ⟨?_, hxN⟩, hxy⟩
  change dist (s x) (s q) ≤ ε / 2
  rw [hxz]
  exact hzb.le

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiberPolynomialNatDegree
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem exists_algHom_separating_element
    {k S I : Type*} [Field k] [Infinite k] [CommRing S] [Algebra k S]
    [Finite I] (f : I → (S →ₐ[k] k)) (hf : Function.Injective f) :
    ∃ t : S, Function.Injective (fun i => f i t) := by
  classical
  let J := {ij : I × I // ij.1 ≠ ij.2}
  let L : J → Module.Dual k S := fun ij =>
    (f ij.val.1).toLinearMap - (f ij.val.2).toLinearMap
  have hL : ∀ ij : J, ∃ x, L ij x ≠ 0 := by
    intro ij
    by_contra! h
    have he : f ij.val.1 = f ij.val.2 := by
      ext x
      exact sub_eq_zero.mp (h x)
    exact ij.property (hf he)
  obtain ⟨t, ht⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists L hL
  refine ⟨t, fun i j hij => ?_⟩
  by_contra hne
  exact ht ⟨(i,j), hne⟩ (sub_eq_zero.mpr hij)

theorem normalization_proper_finite {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ I))
    (hgi : g.toRingHom.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ I) (P j) = g (MvPolynomial.X j)) :
    IsProperMap (fun z : MvPolynomial.zeroLocus ℂ I =>
      fun j => MvPolynomial.eval z.val (P j)) ∧
    ∀ y : Fin d → ℂ, {z : MvPolynomial.zeroLocus ℂ I |
      (fun j => MvPolynomial.eval z.val (P j)) = y}.Finite := by
  choose Q hQ hQr using fun i : Fin n => hgi (quotientCoordinate I i)
  have hroot : ∀ z ∈ MvPolynomial.zeroLocus ℂ I, ∀ i,
      Polynomial.eval₂ (MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)))
        (z i) (Q i) = 0 := by
    intro z hz i
    let e := affineCharacter I ⟨z, hz⟩
    have heg : e.toRingHom.comp g.toRingHom =
        MvPolynomial.eval (fun j => MvPolynomial.eval z (P j)) :=
      congrArg AlgHom.toRingHom (affineCharacter_normalization I g P hP ⟨z, hz⟩)
    have hh := congrArg e.toRingHom (hQr i)
    rw [map_zero, Polynomial.hom_eval₂, heg] at hh
    simpa only [e, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, affineCharacter_coordinate] using hh
  constructor
  · apply isProperMap_iff_isCompact_preimage.mpr
    refine ⟨continuous_pi fun j => (P j).continuous_eval.comp continuous_subtype_val, ?_⟩
    intro K hK
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have heq : (Subtype.val : MvPolynomial.zeroLocus ℂ I → (Fin n → ℂ)) ''
        ((fun z : MvPolynomial.zeroLocus ℂ I => fun j => MvPolynomial.eval z.val (P j)) ⁻¹' K) =
        {z ∈ MvPolynomial.zeroLocus ℂ I | (fun j => MvPolynomial.eval z (P j)) ∈ K} := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩; exact ⟨w.property, hw⟩
      · rintro ⟨hz, hKz⟩; exact ⟨⟨z, hz⟩, hKz, rfl⟩
    rw [heq]
    have hclosed : IsClosed (MvPolynomial.zeroLocus ℂ I) := by
      have he : MvPolynomial.zeroLocus ℂ I = ⋂ p ∈ I,
          {z : Fin n → ℂ | MvPolynomial.eval z p = 0} := by
        ext z; simp only [MvPolynomial.zeroLocus, mem_iInter, mem_ofPred_eq]; rfl
      rw [he]
      exact isClosed_iInter fun p => isClosed_iInter fun _ =>
        isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
    exact isCompact_preimage_of_integral_coordinates hclosed P Q hQ hroot hK
  · intro y
    have hf := (finite_fiber_of_integral_coordinates P Q hQ hroot y).preimage
      (f := (Subtype.val : MvPolynomial.zeroLocus ℂ I → (Fin n → ℂ)))
      Subtype.val_injective.injOn
    simpa only [Set.preimage_ofPred_eq, Subtype.coe_prop, true_and] using hf

theorem finite_algebra_complex_points_isOpenMap {d : ℕ}
    {S X : Type*} [CommRing S] [IsDomain S] [Algebra ℂ S]
    [Algebra (MvPolynomial (Fin d) ℂ) S]
    [IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) S]
    [Module.IsTorsionFree (MvPolynomial (Fin d) ℂ) S]
    [Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) S]
    [Algebra.FiniteType ℂ S] [TopologicalSpace X]
    (e : X ≃ (S →ₐ[ℂ] ℂ))
    (he : ∀ t : S, Continuous (fun x => e x t))
    (π : X → (Fin d → ℂ))
    (hbase : ∀ x r, e x (algebraMap (MvPolynomial (Fin d) ℂ) S r) = MvPolynomial.eval (π x) r)
    (hπ : IsProperMap π) (hfin : ∀ y, Set.Finite {x | π x = y}) :
    IsOpenMap π := by
  classical
  let R := MvPolynomial (Fin d) ℂ
  intro N hN
  apply isOpen_iff_mem_nhds.mpr
  rintro a ⟨q, hq, rfl⟩
  let F := {x | π x = π q}
  have : Finite F := (hfin (π q)).to_subtype
  obtain ⟨t, ht⟩ := exists_algHom_separating_element
    (fun x : F => e x.val) (e.injective.comp Subtype.val_injective)
  let s := fun x => e x t
  have hsep : ∀ x, π x = π q → s x = s q → x = q := by
    intro x hx hs
    exact congrArg Subtype.val (ht (a₁ := ⟨x, hx⟩) (a₂ := ⟨q, rfl⟩) hs)
  have htint : IsIntegral R t := Algebra.IsIntegral.isIntegral t
  have hroot : (minpoly R t).eval₂ (MvPolynomial.eval (π q)) (s q) = 0 := by
    rw [← algHom_aeval_of_base (e q) _ (hbase q), minpoly.aeval, map_zero]
  apply finite_proper_map_open_at_of_root_realization π hπ q (hfin (π q)) s (he t)
    hsep (minpoly R t) (minpoly.monic htint) hroot ?_ hN hq
  intro y b hb
  obtain ⟨f, hf, hfb⟩ := realize_specialized_minpoly_root (S := S)
    (MvPolynomial.aeval y) t b hb
  let x := e.symm f
  have hex : e x = f := e.apply_symm_apply f
  refine ⟨x, ?_, ?_⟩
  · ext j
    have he' := hbase x (MvPolynomial.X j)
    rw [hex, hf] at he'
    simpa only [MvPolynomial.aeval_X, MvPolynomial.eval_X] using he'.symm
  · change e x t = b
    rw [hex, hfb]

theorem normalization_isOpenMap {n d : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (g : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ I))
    (hg : Function.Injective g) (hgi : g.toRingHom.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ I) (P j) = g (MvPolynomial.X j)) :
    IsOpenMap (fun z : MvPolynomial.zeroLocus ℂ I =>
      fun j => MvPolynomial.eval z.val (P j)) := by
  let normalizationAlgebra : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    g.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    normalizationAlgebra.toSMul
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    IsScalarTower.of_algHom g
  let : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ I)).mpr hg
  let : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ I) := ⟨hgi⟩
  obtain ⟨hπ, hfin⟩ := normalization_proper_finite I g hgi P hP
  apply finite_algebra_complex_points_isOpenMap (affineCharacterEquiv I)
    (continuous_affineCharacter I) _ ?_ hπ hfin
  intro z r
  exact DFunLike.congr_fun (affineCharacter_normalization I g P hP z) r

theorem normalization_analytic_sheets {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime]
    (G : MvPolynomial (Fin d) ℂ →ₐ[ℂ] (MvPolynomial (Fin n) ℂ ⧸ J))
    (hG : Function.Injective G) (hGi : G.toRingHom.IsIntegral)
    (P : Fin d → MvPolynomial (Fin n) ℂ)
    (hP : ∀ j, (Ideal.Quotient.mkₐ ℂ J) (P j) = G (MvPolynomial.X j)) :
    ∃ (D : MvPolynomial (Fin d) ℂ) (r : ℕ), D ≠ 0 ∧ 0 < r ∧
      ∀ a : Fin d → ℂ, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (W : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen W ∧ a ∈ W ∧
        (∀ i, AnalyticOnNhd ℂ (g i) W) ∧
        ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
          ∀ z : Fin n → ℂ,
            (z ∈ MvPolynomial.zeroLocus ℂ J ∧
              (fun j => MvPolynomial.eval z (P j)) = y) ↔ ∃ i, g i y = z := by
  let normalizationAlgebra : Algebra (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    G.toRingHom.toAlgebra
  let : SMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    normalizationAlgebra.toSMul
  let : Module (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    @Algebra.toModule _ _ _ _ normalizationAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    IsScalarTower.of_algHom G
  let : FaithfulSMul (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    (faithfulSMul_iff_algebraMap_injective (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ J)).mpr hG
  let : Algebra.IsIntegral (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) := ⟨hGi⟩
  let : Algebra.FiniteType (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (MvPolynomial (Fin d) ℂ)
      (MvPolynomial (Fin n) ℂ ⧸ J)
  let : Module.Finite (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J) :=
    Algebra.IsIntegral.finite
  obtain ⟨D, r, hD, hr, hh⟩ := finite_algebra_generic_sheets_constant_degree (d := d)
    (quotientCoordinate J) (adjoin_quotientCoordinate J)
  refine ⟨D, r, hD, hr, fun a ha => ?_⟩
  obtain ⟨I, g, W, hcard, hW, haW, hg, hs⟩ := hh a ha
  refine ⟨I, g, W, hcard, hW, haW, hg, fun y hy => ⟨(hs y hy).1, fun z => ?_⟩⟩
  rw [← (hs y hy).2 z]
  constructor
  · rintro ⟨hz, hzy⟩
    refine ⟨affineCharacter J ⟨z, hz⟩, ?_, fun j => affineCharacter_coordinate J ⟨z,hz⟩ j⟩
    intro b
    have he := DFunLike.congr_fun (affineCharacter_normalization J G P hP ⟨z,hz⟩) b
    rw [hzy] at he
    exact he
  · rintro ⟨f, hf, hfz⟩
    let w := pointOfCharacter J f
    have hw : w.val = z := funext hfz
    refine ⟨hw ▸ w.property, funext fun j => ?_⟩
    have he := DFunLike.congr_fun (affineCharacter_normalization J G P hP w) (MvPolynomial.X j)
    have hef : affineCharacter J w = f := (affineCharacterEquiv J).apply_symm_apply f
    rw [hef] at he
    change f (algebraMap (MvPolynomial (Fin d) ℂ) (MvPolynomial (Fin n) ℂ ⧸ J)
      (MvPolynomial.X j)) = _ at he
    rw [hf, MvPolynomial.eval_X, MvPolynomial.aeval_X, hw] at he
    exact he.symm

theorem fiberPolynomial_eq_prod {X Y K : Type*} [Fintype K]
    (π : X → Y) (hfin : ∀ y, (π ⁻¹' {y}).Finite) (h : X → ℂ) (y : Y)
    (s : K → X) (hinj : Function.Injective s)
    (hs : ∀ x, π x = y ↔ ∃ j, s j = x) :
    fiberPolynomial π hfin h y = ∏ j, (Polynomial.X - C (h (s j))) := by
  classical
  unfold fiberPolynomial
  symm
  apply Finset.prod_bij (fun j _ => s j)
  · intro j _
    exact (hfin y).mem_toFinset.mpr ((hs (s j)).mpr ⟨j,rfl⟩)
  · intro j _ k _ hjk
    exact hinj hjk
  · intro x hx
    obtain ⟨j, hj⟩ := (hs x).mp ((hfin y).mem_toFinset.mp hx)
    exact ⟨j, Finset.mem_univ _, hj⟩
  · intro j _
    rfl

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ProperEventuallyFiberSubset
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem fiber_card_of_sheets {X Y K : Type*} [Fintype K]
    (π : X → Y) (hfin : ∀ y, (π ⁻¹' {y}).Finite) (y : Y)
    (s : K → X) (hinj : Function.Injective s)
    (hs : ∀ x, π x = y ↔ ∃ j, s j = x) :
    (hfin y).toFinset.card = Fintype.card K := by
  classical
  rw [← Finset.card_univ]
  symm
  apply Finset.card_bij (fun j _ => s j)
  · intro j _
    exact (hfin y).mem_toFinset.mpr ((hs (s j)).mpr ⟨j,rfl⟩)
  · intro j _ k _ hjk
    exact hinj hjk
  · intro x hx
    obtain ⟨j,hj⟩ := (hs x).mp ((hfin y).mem_toFinset.mp hx)
    exact ⟨j,Finset.mem_univ _,hj⟩

theorem coeff_X_sub_C_mul_all (p : Polynomial ℂ) (r : ℂ) (k : ℕ) :
    ((X - C r) * p).coeff k = (if k = 0 then 0 else p.coeff (k-1)) - r * p.coeff k := by
  cases k with
  | zero => simp [sub_mul]
  | succ k => simp [coeff_X_sub_C_mul]

theorem analyticAt_coeff_prod_X_sub_C {E J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (I : Finset J) (f : J → E → ℂ) {a : E}
    (hf : ∀ j ∈ I, AnalyticAt ℂ (f j) a) (k : ℕ) :
    AnalyticAt ℂ (fun y => (∏ j ∈ I, (X - C (f j y))).coeff k) a := by
  classical
  induction I using Finset.induction_on generalizing k with
  | empty => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : Polynomial ℂ).coeff k) a)
  | @insert j I hj ih =>
    simp only [Finset.prod_insert hj, coeff_X_sub_C_mul_all]
    by_cases hk : k = 0
    · subst k
      simpa using ((hf j (Finset.mem_insert_self _ _)).fun_mul
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) 0)).fun_neg
    · simpa [hk] using (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) (k-1)).fun_sub
        ((hf j (Finset.mem_insert_self _ _)).fun_mul
          (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) k))

theorem norm_coeff_prod_X_sub_C_le {J : Type*} (I : Finset J) (f : J → ℂ)
    (hf : ∀ j ∈ I, ‖f j‖ ≤ 1) (k : ℕ) :
    ‖(∏ j ∈ I, (X - C (f j))).coeff k‖ ≤ (2 : ℝ) ^ I.card := by
  classical
  induction I using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, coeff_one]
    split_ifs <;> simp
  | @insert j I hj ih =>
    simp only [Finset.prod_insert hj, coeff_X_sub_C_mul_all, Finset.card_insert_of_notMem hj,
      pow_succ]
    have hI := fun k => ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)) k
    have hmul : ‖f j * (∏ l ∈ I, (X - C (f l))).coeff k‖ ≤ (2 : ℝ) ^ I.card := by
      rw [norm_mul]
      exact (mul_le_mul (hf j (Finset.mem_insert_self _ _)) (hI k)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _)
    have hfirst : ‖if k = 0 then 0 else (∏ l ∈ I, (X - C (f l))).coeff (k-1)‖ ≤
        (2 : ℝ) ^ I.card := by
      split_ifs <;> simp_all
    exact (norm_sub_le _ _).trans (by nlinarith [hfirst, hmul])

theorem exists_vector_prod_X_sub_C {J : Type*} (I : Finset J) (f : J → ℂ)
    {r : ℕ} (hr : I.card = r) :
    ∃ v : (Fin r → ℂ),
      (∀ j, ∃ x ∈ I, v j = f x) ∧
      (∏ x ∈ I, (X - C (f x))) = ∏ j : Fin r, (X - C (v j)) := by
  classical
  let e : I ≃ Fin r := Finset.equivFinOfCardEq hr
  refine ⟨fun j => f (e.symm j).val, fun j => ⟨(e.symm j).val, (e.symm j).property, rfl⟩, ?_⟩
  rw [← Finset.prod_coe_sort]
  exact Fintype.prod_equiv e _ _ (fun j => by simp)

theorem continuous_coeff_prod_fin (r k : ℕ) :
    Continuous (fun v : Fin r → ℂ => (∏ j : Fin r, (X - C (v j))).coeff k) := by
  rw [continuous_iff_continuousAt]
  intro v
  have ha : ∀ j : Fin r, AnalyticAt ℂ (fun w : Fin r → ℂ => w j) v :=
    fun j => (ContinuousLinearMap.proj j : (Fin r → ℂ) →L[ℂ] ℂ).analyticAt _
  exact (analyticAt_coeff_prod_X_sub_C (E := Fin r → ℂ) (J := Fin r) Finset.univ (fun j w => w j)
    (fun j _ => ha j) k).continuousAt

theorem tendsto_coeff_prod_of_values_coalesce {A J : Type*}
    (l : Filter A) (I : A → Finset J) (h : A → J → ℂ) {r : ℕ}
    (hr : ∀ᶠ y in l, (I y).card = r) (b : ℂ)
    (hb : ∀ ε > 0, ∀ᶠ y in l, ∀ j ∈ I y, dist (h y j) b < ε) (k : ℕ) :
    Filter.Tendsto (fun y => (∏ j ∈ I y, (X - C (h y j))).coeff k) l
      (nhds (((X - C b) ^ r).coeff k)) := by
  classical
  let c : (Fin r → ℂ) → ℂ := fun v => (∏ j : Fin r, (X - C (v j))).coeff k
  have hc : ContinuousAt c (fun _ => b) := (continuous_coeff_prod_fin r k).continuousAt
  rw [Metric.continuousAt_iff] at hc
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hcδ⟩ := hc ε hε
  filter_upwards [hr, hb δ hδ] with y hyr hyb
  obtain ⟨v, hv, hprod⟩ := exists_vector_prod_X_sub_C (I y) (h y) hyr
  have hvδ : dist v (fun _ => b) < δ := by
    apply (dist_pi_lt_iff hδ).mpr
    intro j
    obtain ⟨x, hx, hj⟩ := hv j
    rw [hj]
    exact hyb x hx
  have ht := hcδ hvδ
  change dist ((∏ j : Fin r, (X - C (v j))).coeff k)
    ((∏ _j : Fin r, (X - C b)).coeff k) < ε at ht
  rw [← hprod] at ht
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using ht

theorem ScalarAnalyticAt.continuousAt {n : ℕ} {V : Set (Fin n → ℂ)}
    {h : V → ℂ} {q : V} (hh : ScalarAnalyticAt h q) : ContinuousAt h q := by
  obtain ⟨F,hF,he⟩ := hh
  exact (hF.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq he

theorem ScalarAnalyticAt.congr {n : ℕ} {V : Set (Fin n → ℂ)}
    {h g : V → ℂ} {q : V} (hh : ScalarAnalyticAt h q) (he : g =ᶠ[𝓝 q] h) :
    ScalarAnalyticAt g q := by
  obtain ⟨F,hF,hFe⟩ := hh
  exact ⟨F,hF,he.trans hFe⟩

theorem scalarAnalyticAt_const {n : ℕ} {V : Set (Fin n → ℂ)} (b : ℂ) (q : V) :
    ScalarAnalyticAt (fun _ : V => b) q :=
  ⟨fun _ => b, analyticAt_const, Filter.EventuallyEq.rfl⟩

theorem ScalarAnalyticAt.comp {n d : ℕ} {V : Set (Fin n → ℂ)}
    {h : V → ℂ} {s : (Fin d → ℂ) → V} {a : Fin d → ℂ}
    (hh : ScalarAnalyticAt h (s a))
    (hs : AnalyticAt ℂ (fun y => (s y).val) a) :
    AnalyticAt ℂ (fun y => h (s y)) a := by
  obtain ⟨F,hF,he⟩ := hh
  have hsc : ContinuousAt s a := by
    exact (Topology.IsEmbedding.subtypeVal.isInducing.continuousAt_iff).mpr hs.continuousAt
  apply (hF.comp (f := fun y => (s y).val) hs).congr
  exact (he.comp_tendsto hsc.tendsto).symm

theorem scalarAnalyticAt_padded {n : ℕ} {V : Set (Fin n → ℂ)}
    {B Ω C : Set V} [DecidablePred (· ∈ Ω)]
    (hΩ : IsOpen Ω) (hC : IsClosed C) (hΩC : Ω = C ∩ B)
    {h : V → ℂ} (hh : ∀ q ∈ Ω, ScalarAnalyticAt h q) (b : ℂ) :
    ∀ q ∈ B, ScalarAnalyticAt (Ω.piecewise h (fun _ => b)) q := by
  intro q hq
  by_cases hqΩ : q ∈ Ω
  · apply (hh q hqΩ).congr
    filter_upwards [hΩ.mem_nhds hqΩ] with x hx
    exact piecewise_eq_of_mem _ _ _ hx
  · have hqC : q ∉ C := fun hc => hqΩ (hΩC ▸ ⟨hc,hq⟩)
    apply (scalarAnalyticAt_const b q).congr
    filter_upwards [hC.isOpen_compl.mem_nhds hqC] with x hx
    apply piecewise_eq_of_notMem
    exact fun hxΩ => hx ((hΩC ▸ hxΩ).1)

theorem fiberPolynomial_coeff_analyticAt_of_sheets {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → (Fin d → ℂ))
    (hfin : ∀ y, ((fun x : V => π x.val) ⁻¹' {y}).Finite)
    (h : V → ℂ) {a : Fin d → ℂ}
    (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
    {W : Set (Fin d → ℂ)} (hW : IsOpen W) (haW : a ∈ W)
    (hg : ∀ i, AnalyticOnNhd ℂ (g i) W)
    (hs : ∀ y ∈ W, Function.Injective (fun i => g i y) ∧
      ∀ z : Fin n → ℂ, (z ∈ V ∧ π z = y) ↔ ∃ i, g i y = z)
    (hh : ∀ x : V, π x.val = a → ScalarAnalyticAt h x) (k : ℕ) :
    AnalyticAt ℂ (fun y => (fiberPolynomial (fun x : V => π x.val) hfin h y).coeff k) a := by
  classical
  have hgV : ∀ i y, y ∈ W → g i y ∈ V := fun i y hy =>
    (((hs y hy).2 (g i y)).mpr ⟨i,rfl⟩).1
  let s : I → (Fin d → ℂ) → V := fun i y =>
    if hy : y ∈ W then ⟨g i y, hgV i y hy⟩ else ⟨g i a, hgV i a haW⟩
  have hse : ∀ i y, y ∈ W → (s i y).val = g i y := fun i y hy => by
    simp only [s, dite_eq_left hy]
  have hsa : ∀ i, AnalyticAt ℂ (fun y => h (s i y)) a := by
    intro i
    apply ScalarAnalyticAt.comp
    · apply hh
      rw [hse i a haW]
      exact (((hs a haW).2 (g i a)).mpr ⟨i,rfl⟩).2
    · apply (hg i a haW).congr
      filter_upwards [hW.mem_nhds haW] with y hy
      exact (hse i y hy).symm
  have hprod : ∀ y ∈ W,
      fiberPolynomial (fun x : V => π x.val) hfin h y =
        ∏ i : I, (Polynomial.X - C (h (s i y))) := by
    intro y hy
    apply fiberPolynomial_eq_prod
    · intro i j hij
      apply (hs y hy).1
      simpa only [hse i y hy, hse j y hy] using congrArg Subtype.val hij
    · intro x
      constructor
      · intro hx
        obtain ⟨i,hi⟩ := ((hs y hy).2 x.val).mp ⟨x.property,hx⟩
        exact ⟨i, Subtype.ext ((hse i y hy).trans hi)⟩
      · rintro ⟨i,rfl⟩
        rw [hse i y hy]
        exact (((hs y hy).2 (g i y)).mpr ⟨i,rfl⟩).2
  apply (analyticAt_coeff_prod_X_sub_C (E := Fin d → ℂ) (J := I)
    Finset.univ (fun i y => h (s i y)) (fun i _ => hsa i) k).congr
  filter_upwards [hW.mem_nhds haW] with y hy
  exact congrArg (fun p : Polynomial ℂ => p.coeff k) (hprod y hy).symm

theorem proper_eventually_fiber_subset {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (hπ : IsProperMap π) {a : Y} {O : Set X} (hO : IsOpen O)
    (ha : π ⁻¹' {a} ⊆ O) :
    ∀ᶠ y in 𝓝 a, ∀ x, π x = y → x ∈ O := by
  have hc : IsClosed (π '' Oᶜ) := hπ.isClosedMap _ hO.isClosed_compl
  have hn : a ∉ π '' Oᶜ := by
    rintro ⟨x, hx, hxa⟩
    exact hx (ha hxa)
  filter_upwards [hc.isOpen_compl.mem_nhds hn] with y hy x hx
  by_contra hxO
  exact hy ⟨x, hxO, hx⟩

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_FiberCardAmbientSheets
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem continuousOn_padded {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (_hπ : Continuous π) {B : Set Y} (_hB : IsOpen B)
    {Ω C : Set X} [DecidablePred (· ∈ Ω)] (hΩ : IsOpen Ω) (hC : IsClosed C)
    (hΩC : Ω = C ∩ π ⁻¹' B) {h : X → ℂ} (hh : ContinuousOn h Ω) (b : ℂ) :
    ContinuousOn (Ω.piecewise h (fun _ => b)) (π ⁻¹' B) := by
  classical
  intro x hx
  apply ContinuousAt.continuousWithinAt
  by_cases hxΩ : x ∈ Ω
  · have he : Ω.piecewise h (fun _ => b) =ᶠ[𝓝 x] h :=
      by
        filter_upwards [hΩ.mem_nhds hxΩ] with z hz
        exact piecewise_eq_of_mem Ω h _ hz
    exact ((hh x hxΩ).continuousAt (hΩ.mem_nhds hxΩ)).congr_of_eventuallyEq he
  · have hxC : x ∉ C := fun hc => hxΩ (hΩC.symm ▸ ⟨hc, hx⟩)
    have he : Ω.piecewise h (fun _ => b) =ᶠ[𝓝 x] (fun _ => b) := by
      filter_upwards [hC.isOpen_compl.mem_nhds hxC] with z hz
      exact piecewise_eq_of_notMem Ω h _ (fun h => hz ((hΩC ▸ h).1))
    exact continuousAt_const.congr_of_eventuallyEq he

theorem proper_eventually_fiber_values_close {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {π : X → Y}
    (hπ : IsProperMap π) {a : Y} {B : Set Y} (hB : IsOpen B) (ha : a ∈ B)
    (h : X → ℂ) (hh : ContinuousOn h (π ⁻¹' B)) (b : ℂ)
    (hfiber : ∀ x, π x = a → h x = b) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 a, ∀ x, π x = y → dist (h x) b < ε := by
  have hO : IsOpen ((π ⁻¹' B) ∩ h ⁻¹' Metric.ball b ε) :=
    hh.isOpen_inter_preimage (hB.preimage hπ.continuous) Metric.isOpen_ball
  have haO : π ⁻¹' {a} ⊆ (π ⁻¹' B) ∩ h ⁻¹' Metric.ball b ε := by
    intro x hx
    refine ⟨?_, ?_⟩
    · change π x ∈ B
      change π x = a at hx
      rwa [hx]
    · change dist (h x) b < ε
      rw [hfiber x hx, dist_self]
      exact hε
  exact (proper_eventually_fiber_subset hπ hO haO).mono fun _ hy x hx => (hy x hx).2

theorem extended_fiber_coefficients {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : V → (Fin d → ℂ))
    (hπ : IsProperMap π) (hfin : ∀ y, (π ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ)
    (hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r)
    {B : Set (Fin d → ℂ)} (hB : IsOpen B) {a : Fin d → ℂ} (ha : a ∈ B)
    (h : V → ℂ) (hh : ContinuousOn h (π ⁻¹' B))
    (hb : ∀ x, π x ∈ B → ‖h x‖ ≤ 1)
    (hholo : ∀ k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin h y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}))
    (b : ℂ) (hcoalesce : ∀ x, π x = a → h x = b) :
    ∃ c : Fin r → (Fin d → ℂ) → ℂ,
      (∀ j, DifferentiableOn ℂ (c j) B) ∧
      (∀ j y, y ∈ B → ‖c j y‖ ≤ (2 : ℝ)^r) ∧
      (∀ j y, y ∈ B → MvPolynomial.eval y D ≠ 0 →
        c j y = (fiberPolynomial π hfin h y).coeff j) ∧
      ∀ j, c j a = ((Polynomial.X - C b)^r).coeff j := by
  classical
  have hbound : ∀ k y, y ∈ B \ {y | MvPolynomial.eval y D = 0} →
      ‖(fiberPolynomial π hfin h y).coeff k‖ ≤ (2 : ℝ)^r := by
    intro k y hy
    have hc := hcard y hy.2
    unfold fiberPolynomial
    rw [← hc]
    apply norm_coeff_prod_X_sub_C_le
    intro x hx
    have hxy : π x = y := (hfin y).mem_toFinset.mp hx
    exact hb x (hxy.symm ▸ hy.1)
  choose c hcd hce hcb using fun j : Fin r =>
    bounded_polynomial_removable D hD hB (fun y => (fiberPolynomial π hfin h y).coeff j)
      (hholo j) (hbound j)
  refine ⟨c, hcd, hcb, fun j y hy hDy => hce j ⟨hy,hDy⟩, fun j => ?_⟩
  let S := {y : Fin d → ℂ | MvPolynomial.eval y D ≠ 0}
  have hSd : Dense S := dense_polynomial_nonzero D hD
  have : (𝓝[S] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hSd a)
  have hcT : Filter.Tendsto (c j) (𝓝[S] a) (𝓝 (c j a)) :=
    ((hcd j a ha).differentiableAt (hB.mem_nhds ha)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hrT : ∀ᶠ y in 𝓝[S] a, (hfin y).toFinset.card = r := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact hcard y hy
  have hbT : ∀ ε > 0, ∀ᶠ y in 𝓝[S] a,
      ∀ x ∈ (hfin y).toFinset, dist (h x) b < ε := by
    intro ε hε
    have ht := proper_eventually_fiber_values_close hπ hB ha h hh b hcoalesce ε hε
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds ht] with y hy x hx
    exact hy x ((hfin y).mem_toFinset.mp hx)
  have hT := tendsto_coeff_prod_of_values_coalesce (𝓝[S] a)
    (fun y => (hfin y).toFinset) (fun _ x => h x) hrT b hbT j.val
  have he : (fun y => (∏ x ∈ (hfin y).toFinset,
      (Polynomial.X - C (h x))).coeff j.val) =ᶠ[𝓝[S] a] c j := by
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB.mem_nhds ha)] with y hyS hyB
    exact (hce j ⟨hyB,hyS⟩).symm
  exact tendsto_nhds_unique hcT (hT.congr' he)

theorem fiber_card_of_ambient_sheets {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : (Fin n → ℂ) → (Fin d → ℂ))
    (hfin : ∀ y, ((fun x : V => π x.val) ⁻¹' {y}).Finite)
    (a : Fin d → ℂ) (I : Finset ℂ) (g : I → (Fin n → ℂ))
    (hi : Function.Injective g)
    (hg : ∀ z, (z ∈ V ∧ π z = a) ↔ ∃ i, g i = z) :
    (hfin a).toFinset.card = I.card := by
  have hgV : ∀ i, g i ∈ V := fun i => ((hg (g i)).mpr ⟨i,rfl⟩).1
  let s : I → V := fun i => ⟨g i, hgV i⟩
  have hsi : Function.Injective s := fun i j hij => hi (congrArg Subtype.val hij)
  have hse : ∀ x : V, π x.val = a ↔ ∃ i, s i = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨i,hi⟩ := (hg x.val).mp ⟨x.property,hx⟩
      exact ⟨i,Subtype.ext hi⟩
    · rintro ⟨i,rfl⟩
      exact ((hg (g i)).mpr ⟨i,rfl⟩).2
  simpa using fiber_card_of_sheets (fun x : V => π x.val) hfin a s hsi hse

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PrimeZeroLocusMaximum
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem coeff_pow_X_sub_C_pred {r : ℕ} (hr : 0 < r) (b : ℂ) :
    ((Polynomial.X - C b)^r).coeff (r-1) = -(r : ℂ) * b := by
  have he := Polynomial.prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin r))
    (fun _ => b) (by simpa using hr)
  simpa [nsmul_eq_mul] using he

theorem norm_finite_average_le_one {X : Type*} (F : Finset X) {r : ℕ}
    (hr : 0 < r) (hcard : F.card = r) (h : X → ℂ)
    (hb : ∀ x ∈ F, ‖h x‖ ≤ 1) : ‖(∑ x ∈ F, h x) / (r : ℂ)‖ ≤ 1 := by
  rw [norm_div, Complex.norm_natCast]
  apply (div_le_one (by positivity : (0:ℝ) < r)).mpr
  calc
    ‖∑ x ∈ F, h x‖ ≤ ∑ x ∈ F, ‖h x‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ F, (1:ℝ) := Finset.sum_le_sum hb
    _ = r := by simp [hcard]

theorem extended_fiber_average {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π : V → (Fin d → ℂ))
    (hπ : IsProperMap π) (hfin : ∀ y, (π ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ) (hr : 0 < r)
    (hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r)
    {B : Set (Fin d → ℂ)} (hB : IsOpen B) {a : Fin d → ℂ} (ha : a ∈ B)
    (h : V → ℂ) (hh : ContinuousOn h (π ⁻¹' B))
    (hb : ∀ x, π x ∈ B → ‖h x‖ ≤ 1)
    (hholo : ∀ k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin h y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}))
    (b : ℂ) (hcoalesce : ∀ x, π x = a → h x = b) :
    ∃ c : (Fin d → ℂ) → ℂ,
      DifferentiableOn ℂ c B ∧ (∀ y ∈ B, ‖c y‖ ≤ 1) ∧
      (∀ y ∈ B, MvPolynomial.eval y D ≠ 0 →
        c y = (∑ x ∈ (hfin y).toFinset, h x) / (r : ℂ)) ∧ c a = b := by
  classical
  obtain ⟨c,hcd,_,hce,hcq⟩ := extended_fiber_coefficients V π hπ hfin D hD r hcard
    hB ha h hh hb hholo b hcoalesce
  let j : Fin r := ⟨r-1, by omega⟩
  let g := fun y => -(c j y) / (r : ℂ)
  have hgd : DifferentiableOn ℂ g B := by
    dsimp [g]
    convert! (hcd j).neg.mul_const (r : ℂ)⁻¹ using 1
    all_goals try with_reducible_and_instances rfl
  have hge : ∀ y ∈ B, MvPolynomial.eval y D ≠ 0 →
      g y = (∑ x ∈ (hfin y).toFinset, h x)/(r : ℂ) := by
    intro y hy hDy
    have he := Polynomial.prod_X_sub_C_coeff_card_pred (hfin y).toFinset h
      (by rw [hcard y hDy]; exact hr)
    change -(c j y) / (r : ℂ) = _
    rw [hce j y hy hDy]
    change -((∏ x ∈ (hfin y).toFinset, (X - C (h x))).coeff (r-1))/(r : ℂ) = _
    rw [← hcard y hDy, he, neg_neg]
  have hgb : ∀ y ∈ B, ‖g y‖ ≤ 1 := by
    intro y hy
    let S := {y : Fin d → ℂ | MvPolynomial.eval y D ≠ 0}
    have hdense : Dense S := dense_polynomial_nonzero D hD
    have : (𝓝[S] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hdense y)
    have ht : Tendsto g (𝓝[S] y) (𝓝 (g y)) :=
      ((hgd y hy).differentiableAt (hB.mem_nhds hy)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto ht.norm
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (hB.mem_nhds hy)] with z hzS hzB
    rw [hge z hzB hzS]
    apply norm_finite_average_le_one _ hr (hcard z hzS) h
    intro x hx
    have hxz : π x = z := (hfin z).mem_toFinset.mp hx
    exact hb x (hxz.symm ▸ hzB)
  refine ⟨g,hgd,hgb,hge,?_⟩
  change -(c j a)/(r : ℂ) = b
  rw [hcq j]
  change -(((X - C b)^r).coeff (r-1))/(r : ℂ) = b
  rw [coeff_pow_X_sub_C_pred hr b]
  have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
  field_simp

theorem holomorphic_maximum_subsequence_on_ball {d : ℕ}
    {a : Fin d → ℂ} {R : ℝ} (hR : 0 < R)
    (F : ℕ → (Fin d → ℂ) → ℂ)
    (hd : ∀ i, DifferentiableOn ℂ (F i) (Metric.ball a R))
    (hb : ∀ i y, y ∈ Metric.ball a R → ‖F i y‖ ≤ 1)
    (ha : Tendsto (fun i => F i a) atTop (𝓝 1)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ y ∈ Metric.ball a R, Tendsto (fun i => F (φ i) y) atTop (𝓝 1) := by
  classical
  let B := Metric.ball a R
  let : LocallyCompactSpace B := Metric.isOpen_ball.locallyCompactSpace
  have he : Equicontinuous (fun i (y : B) => F i y) :=
    equicontinuous_of_bounded_differentiableOn Metric.isOpen_ball F hd hb
  obtain ⟨f,_,_,φ,hφ,hconv⟩ := locally_uniform_subsequence_of_equicontinuous
    (fun i (y : B) => F i y) he (fun i y => hb i y y.property)
  let g : (Fin d → ℂ) → ℂ := fun y => if hy : y ∈ B then f ⟨y,hy⟩ else 0
  have hconv' : TendstoLocallyUniformlyOn (fun i => F (φ i)) g atTop B := by
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
    simpa only [g, Function.comp_def, Subtype.coe_prop, dite_true] using hconv
  have haB : a ∈ B := Metric.mem_ball_self hR
  have hga : g a = 1 := tendsto_nhds_unique (hconv'.tendsto_at haB) (ha.comp hφ.tendsto_atTop)
  have hge := maximum_propagation_on_ball hR (fun i => F (φ i)) g
    (fun i => hd (φ i)) (fun i => hb (φ i)) hconv' hga
  refine ⟨φ,hφ,fun y hy => ?_⟩
  simpa only [hge hy] using hconv'.tendsto_at hy

theorem unit_disc_finset_sum_eq_card {X : Type*} (F : Finset X) (v : X → ℂ)
    (hv : ∀ x ∈ F, ‖v x‖ ≤ 1) (hs : ∑ x ∈ F, v x = (F.card : ℂ)) :
    ∀ x ∈ F, v x = 1 := by
  have hre : ∑ x ∈ F, (v x).re = ∑ _x ∈ F, (1 : ℝ) := by
    simpa using congrArg Complex.re hs
  have hres : ∀ x ∈ F, (v x).re = 1 :=
    (Finset.sum_eq_sum_iff_of_le (fun x hx => (Complex.re_le_norm (v x)).trans (hv x hx))).mp hre
  intro x hx
  apply Complex.ext
  · simpa using hres x hx
  · have hsq := Complex.sq_norm_sub_sq_re (v x)
    have hnorm := hv x hx
    have hn := norm_nonneg (v x)
    have hi : (v x).im = 0 := by nlinarith [hres x hx, sq_nonneg (v x).im]
    simpa using hi

theorem scalar_maximum_local_of_finite_analytic_map {n d : ℕ}
    (V : Set (Fin n → ℂ)) (π₀ : (Fin n → ℂ) → (Fin d → ℂ))
    (hπ : IsProperMap (fun x : V => π₀ x.val))
    (hπo : IsOpenMap (fun x : V => π₀ x.val))
    (hfin : ∀ y, ((fun x : V => π₀ x.val) ⁻¹' {y}).Finite)
    (D : MvPolynomial (Fin d) ℂ) (hD : D ≠ 0) (r : ℕ) (hr : 0 < r)
    (hsheets : ∀ a, MvPolynomial.eval a D ≠ 0 →
      ∃ (I : Finset ℂ) (g : I → (Fin d → ℂ) → (Fin n → ℂ))
        (A : Set (Fin d → ℂ)),
        I.card = r ∧ IsOpen A ∧ a ∈ A ∧ (∀ i, AnalyticOnNhd ℂ (g i) A) ∧
        ∀ y ∈ A, Function.Injective (fun i => g i y) ∧
          ∀ z, (z ∈ V ∧ π₀ z = y) ↔ ∃ i, g i y = z)
    {W : Set V} (hW : IsOpen W) (h : ℕ → V → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    (f : V → ℂ) (hfc : ContinuousOn f W)
    (ht : ∀ x ∈ W, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : V} (hq : q ∈ W) (hfq : f q = 1) : ∀ᶠ x in 𝓝 q, f x = 1 := by
  classical
  let π : V → (Fin d → ℂ) := fun x => π₀ x.val
  obtain ⟨B,hB,hqB,Ω,C,hΩ,hqΩ,hΩW,hC,hΩC,hfiber⟩ :=
    finite_fiber_localization hπ q (hfin (π q)) hW hq
  let H : ℕ → V → ℂ := fun i => Ω.piecewise (h i) (fun _ => h i q)
  have hHhol : ∀ i x, π x ∈ B → ScalarAnalyticAt (H i) x := by
    intro i
    exact scalarAnalyticAt_padded hΩ hC hΩC (fun x hx => hh i x (hΩW hx)) (h i q)
  have hHc : ∀ i, ContinuousOn (H i) (π ⁻¹' B) :=
    fun i x hx => (hHhol i x hx).continuousAt.continuousWithinAt
  have hHb : ∀ i x, π x ∈ B → ‖H i x‖ ≤ 1 := by
    intro i x _
    by_cases hx : x ∈ Ω
    · simpa only [H, piecewise_eq_of_mem Ω (h i) _ hx] using hb i x (hΩW hx)
    · simpa only [H, piecewise_eq_of_notMem Ω (h i) _ hx] using hb i q hq
  have hHq : ∀ i x, π x = π q → H i x = h i q := by
    intro i x hx
    by_cases hxΩ : x ∈ Ω
    · have hxq : x = q := by
        have : x ∈ Ω ∩ π ⁻¹' {π q} := ⟨hxΩ,hx⟩
        rw [hfiber] at this
        exact this
      simp [H, hxq, hqΩ]
    · simp [H, hxΩ]
  have hcard : ∀ y, MvPolynomial.eval y D ≠ 0 → (hfin y).toFinset.card = r := by
    intro y hy
    obtain ⟨I,g,A,hIr,_,hyA,_,hs⟩ := hsheets y hy
    exact (fiber_card_of_ambient_sheets V π₀ hfin y I (fun i => g i y)
      (hs y hyA).1 (hs y hyA).2).trans hIr
  have hcoef : ∀ i k, AnalyticOnNhd ℂ (fun y => (fiberPolynomial π hfin (H i) y).coeff k)
      (B \ {y | MvPolynomial.eval y D = 0}) := by
    intro i k a ha
    obtain ⟨I,g,A,_,hA,haA,hg,hs⟩ := hsheets a ha.2
    apply fiberPolynomial_coeff_analyticAt_of_sheets V π₀ hfin (H i) I g hA haA hg hs
    intro x hx
    apply hHhol i x
    change π₀ x.val ∈ B
    rw [hx]
    exact ha.1
  choose c hcd hcb hce hcq using fun i => extended_fiber_average V π hπ hfin D hD r hr
    hcard hB hqB (H i) (hHc i) (hHb i) (hcoef i) (h i q) (hHq i)
  obtain ⟨R,hR,hRB⟩ := Metric.mem_nhds_iff.mp (hB.mem_nhds hqB)
  have hcqt : Tendsto (fun i => c i (π q)) atTop (𝓝 1) := by
    have heq : (fun i => c i (π q)) = (fun i => h i q) := funext hcq
    rw [heq]
    simpa only [hfq] using ht q hq
  obtain ⟨φ,hφ,hmax⟩ := holomorphic_maximum_subsequence_on_ball hR c
    (fun i => (hcd i).mono hRB) (fun i y hy => hcb i y (hRB hy)) hcqt
  let F : V → ℂ := Ω.piecewise f (fun _ => f q)
  have hFc : ContinuousOn F (π ⁻¹' B) :=
    continuousOn_padded hπ.continuous hB hΩ hC hΩC (hfc.mono hΩW) (f q)
  have hHt : ∀ x, Tendsto (fun i => H i x) atTop (𝓝 (F x)) := by
    intro x
    by_cases hx : x ∈ Ω
    · simpa only [H,F,piecewise_eq_of_mem Ω _ _ hx] using ht x (hΩW hx)
    · simpa only [H,F,piecewise_eq_of_notMem Ω _ _ hx] using ht q hq
  have hFb : ∀ x, π x ∈ B → ‖F x‖ ≤ 1 := by
    intro x hx
    exact le_of_tendsto (hHt x).norm (Filter.Eventually.of_forall fun i => hHb i x hx)
  have he : EqOn F (fun _ => 1)
      ((π ⁻¹' Metric.ball (π q) R) ∩ (π ⁻¹' {y | MvPolynomial.eval y D ≠ 0})) := by
    intro x hx
    let A := (hfin (π x)).toFinset
    have hsumt : Tendsto (fun i => (∑ z ∈ A, H (φ i) z)/(r : ℂ)) atTop
        (𝓝 ((∑ z ∈ A, F z)/(r : ℂ))) :=
      (tendsto_finsetSum A (fun z _ => (hHt z).comp hφ.tendsto_atTop)).div_const _
    have hsumt' : Tendsto (fun i => (∑ z ∈ A, H (φ i) z)/(r : ℂ)) atTop (𝓝 1) := by
      have heq : (fun i => c (φ i) (π x)) =
          (fun i => (∑ z ∈ A, H (φ i) z)/(r : ℂ)) :=
        funext (fun i => hce (φ i) (π x) (hRB hx.1) hx.2)
      rw [← heq]
      exact hmax (π x) hx.1
    have hsum : (∑ z ∈ A, F z) = (A.card : ℂ) := by
      have heq := tendsto_nhds_unique hsumt hsumt'
      have hrC : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr)
      rw [div_eq_one_iff_eq hrC] at heq
      simpa only [A, hcard (π x) hx.2] using heq
    have hv : ∀ z ∈ A, ‖F z‖ ≤ 1 := by
      intro z hz
      have hzx : π z = π x := (hfin (π x)).mem_toFinset.mp hz
      exact hFb z (hzx.symm ▸ hRB hx.1)
    exact unit_disc_finset_sum_eq_card A F hv hsum x
      ((hfin (π x)).mem_toFinset.mpr rfl)
  have hd : Dense (π ⁻¹' {y | MvPolynomial.eval y D ≠ 0}) :=
    (dense_polynomial_nonzero D hD).preimage hπo
  have hcl : π ⁻¹' Metric.ball (π q) R ⊆
      closure ((π ⁻¹' Metric.ball (π q) R) ∩ (π ⁻¹' {y | MvPolynomial.eval y D ≠ 0})) :=
    fun x hx => (Metric.isOpen_ball.preimage hπ.continuous).inter_closure ⟨hx,hd x⟩
  have he' : EqOn F (fun _ => 1) (π ⁻¹' Metric.ball (π q) R) :=
    he.of_subset_closure (hFc.mono (preimage_mono hRB)) continuousOn_const inter_subset_left hcl
  have hball : π ⁻¹' Metric.ball (π q) R ∈ 𝓝 q :=
    hπ.continuous.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ hR)
  filter_upwards [hΩ.mem_nhds hqΩ,hball] with x hxΩ hxB
  have := he' hxB
  simpa only [F,piecewise_eq_of_mem Ω f _ hxΩ] using this

theorem prime_zeroLocus_maximum_local {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    {W : Set (MvPolynomial.zeroLocus ℂ I)} (hW : IsOpen W)
    (h : ℕ → MvPolynomial.zeroLocus ℂ I → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    (f : MvPolynomial.zeroLocus ℂ I → ℂ) (hfc : ContinuousOn f W)
    (ht : ∀ x ∈ W, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : MvPolynomial.zeroLocus ℂ I} (hq : q ∈ W) (hfq : f q = 1) :
    ∀ᶠ x in 𝓝 q, f x = 1 := by
  obtain ⟨d, _, g, hg, hgi⟩ := exists_integral_inj_algHom_of_quotient I Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ I (g (MvPolynomial.X j))
  obtain ⟨hπ,hfin⟩ := normalization_proper_finite I g hgi P hP
  have ho := normalization_isOpenMap I g hg hgi P hP
  obtain ⟨D,r,hD,hr,hs⟩ := normalization_analytic_sheets I g hg hgi P hP
  exact scalar_maximum_local_of_finite_analytic_map _ _ hπ ho hfin D hD r hr hs
    hW h hh hb f hfc ht hq hfq

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ScalarEquicontinuousHolomorphy
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem zeroLocus_closed {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsClosed (MvPolynomial.zeroLocus ℂ I) := by
  have he : MvPolynomial.zeroLocus ℂ I = ⋂ p ∈ I,
      {z : Fin n → ℂ | MvPolynomial.eval z p = 0} := by
    ext z; simp only [MvPolynomial.zeroLocus, mem_iInter, mem_ofPred_eq]; rfl
  rw [he]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_eq (MvPolynomial.continuous_eval p) continuous_const

theorem zeroLocus_eq_union_minimalPrimes {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    MvPolynomial.zeroLocus ℂ I = ⋃ J : I.minimalPrimes, MvPolynomial.zeroLocus ℂ J.val := by
  ext x
  constructor
  · intro hx
    have hIx : I ≤ MvPolynomial.vanishingIdeal ℂ ({x} : Set (Fin n → ℂ)) := by
      intro p hp
      exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mpr (hx p hp)
    obtain ⟨J,hJ,hJx⟩ := Ideal.exists_minimalPrimes_le hIx
    refine mem_iUnion.mpr ⟨⟨J,hJ⟩, ?_⟩
    intro p hp
    exact (MvPolynomial.mem_vanishingIdeal_singleton_iff x p).mp (hJx hp)
  · intro hx
    rcases mem_iUnion.mp hx with ⟨J,hxJ⟩
    exact MvPolynomial.zeroLocus_anti_mono J.property.le hxJ

theorem ScalarAnalyticAt.restrict {n : ℕ} {S T : Set (Fin n → ℂ)}
    (hST : S ⊆ T) {h : T → ℂ} {q : S}
    (hh : ScalarAnalyticAt h ⟨q.val,hST q.property⟩) :
    ScalarAnalyticAt (fun x : S => h ⟨x.val,hST x.property⟩) q := by
  obtain ⟨F,hF,he⟩ := hh
  refine ⟨F,hF,?_⟩
  exact he.comp_tendsto (continuous_subtype_val.subtype_mk (fun x => hST x.property)).continuousAt

theorem scalarAnalyticAt_of_open_extension {n : ℕ} {S T : Set (Fin n → ℂ)}
    (hST : S ⊆ T) (hSo : IsOpen ((Subtype.val : T → Fin n → ℂ) ⁻¹' S))
    {h : S → ℂ} {H : T → ℂ} (hH : ∀ x : S, H (Set.inclusion hST x) = h x)
    {q : S} (hh : ScalarAnalyticAt h q) : ScalarAnalyticAt H (Set.inclusion hST q) := by
  obtain ⟨F,hF,he⟩ := hh
  refine ⟨F,hF,?_⟩
  rw [← (Topology.IsOpenEmbedding.inclusion hST hSo).map_nhds_eq q]
  change ∀ᶠ x : S in 𝓝 q, H (Set.inclusion hST x) = F x.val
  filter_upwards [he] with x hx
  rw [hH]
  exact hx

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_AmbientInverse
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem zeroLocus_maximum_local {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    {W : Set (MvPolynomial.zeroLocus ℂ I)} (hW : IsOpen W)
    (h : ℕ → MvPolynomial.zeroLocus ℂ I → ℂ)
    (hh : ∀ i x, x ∈ W → ScalarAnalyticAt (h i) x)
    (hb : ∀ i x, x ∈ W → ‖h i x‖ ≤ 1)
    (f : MvPolynomial.zeroLocus ℂ I → ℂ) (hfc : ContinuousOn f W)
    (ht : ∀ x ∈ W, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : MvPolynomial.zeroLocus ℂ I} (hq : q ∈ W) (hfq : f q = 1) :
    ∀ᶠ x in 𝓝 q, f x = 1 := by
  have : Finite I.minimalPrimes :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).to_subtype
  let T : I.minimalPrimes → Set (MvPolynomial.zeroLocus ℂ I) :=
    fun J => {x | x.val ∈ MvPolynomial.zeroLocus ℂ J.val}
  have hT : ⋃ J, T J = univ := by
    apply eq_univ_of_forall
    intro x
    have hx := (zeroLocus_eq_union_minimalPrimes I).subset x.property
    rcases mem_iUnion.mp hx with ⟨J,hJ⟩
    exact mem_iUnion.mpr ⟨J,hJ⟩
  have he : 𝓝 q = ⨆ J, 𝓝[T J] q := by
    rw [← nhdsWithin_iUnion, hT, nhdsWithin_univ]
  rw [he, Filter.eventually_iSup]
  intro J
  by_cases hqJ : q ∈ T J
  · let : J.val.IsPrime := J.property.isPrime
    have hJI : MvPolynomial.zeroLocus ℂ J.val ⊆ MvPolynomial.zeroLocus ℂ I :=
      MvPolynomial.zeroLocus_anti_mono J.property.le
    let s : MvPolynomial.zeroLocus ℂ J.val → MvPolynomial.zeroLocus ℂ I :=
      fun x => ⟨x.val, hJI x.property⟩
    have hs : Continuous s := continuous_subtype_val.subtype_mk _
    have hem := prime_zeroLocus_maximum_local J.val (hW.preimage hs)
      (fun i x => h i (s x))
      (fun i x hx => (hh i (s x) hx).restrict hJI)
      (fun i x hx => hb i (s x) hx) (fun x => f (s x))
      (hfc.comp hs.continuousOn (fun _ hx => hx))
      (fun x hx => ht (s x) hx) (q := ⟨q.val,hqJ⟩) hq hfq
    rw [← eventually_nhds_subtype_iff (T J) ⟨q,hqJ⟩ (fun x => f x = 1)]
    let g : T J → MvPolynomial.zeroLocus ℂ J.val := fun x => ⟨x.val.val,x.property⟩
    have hg : Continuous g := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
    exact (hg.continuousAt (x := (⟨q,hqJ⟩ : T J))).eventually hem
  · have heq : 𝓝[T J] q = ⊥ := by
      rw [← notMem_closure_iff_nhdsWithin_eq_bot]
      have hclosed : IsClosed (T J) := (zeroLocus_closed J.val).preimage continuous_subtype_val
      simpa only [hclosed.closure_eq] using hqJ
    simp [heq]

theorem scalar_maximum_local_of_holomorphy {n : ℕ}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (h : ℕ → U → ℂ) (hh : ∀ i q, ScalarAnalyticAt (h i) q)
    (hb : ∀ i q, ‖h i q‖ ≤ 1) (f : U → ℂ) (hfc : Continuous f)
    (ht : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : U} (hfq : f q = 1) : ∀ᶠ x in 𝓝 q, f x = 1 := by
  classical
  let I := MvPolynomial.vanishingIdeal ℂ V
  have hUI : U ⊆ MvPolynomial.zeroLocus ℂ I := by
    simpa only [I, hV.zeroLocus_vanishingIdeal] using hUV
  have hUo : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) := by
    rw [show MvPolynomial.zeroLocus ℂ I = V from hV.zeroLocus_vanishingIdeal]
    exact hU
  let H : ℕ → MvPolynomial.zeroLocus ℂ I → ℂ :=
    fun i x => if hx : x.val ∈ U then h i ⟨x.val,hx⟩ else 0
  let F : MvPolynomial.zeroLocus ℂ I → ℂ :=
    fun x => if hx : x.val ∈ U then f ⟨x.val,hx⟩ else 0
  have hH : ∀ i (x : U), H i (Set.inclusion hUI x) = h i x := by
    intro i x
    simp only [H, Set.inclusion, x.property, dite_true]
  have hF : ∀ x : U, F (Set.inclusion hUI x) = f x := by
    intro x
    simp only [F, Set.inclusion, x.property, dite_true]
  have hHg : ∀ i x, x.val ∈ U → ScalarAnalyticAt (H i) x := by
    intro i x hx
    exact scalarAnalyticAt_of_open_extension hUI hUo (hH i) (hh i ⟨x.val,hx⟩)
  have hHb : ∀ i x, x.val ∈ U → ‖H i x‖ ≤ 1 := by
    intro i x hx
    simpa only [← hH i ⟨x.val,hx⟩] using hb i ⟨x.val,hx⟩
  have hFc : ContinuousOn F ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U) := by
    intro x hx
    have hcat : ContinuousAt F (Set.inclusion hUI ⟨x.val,hx⟩) := by
      rw [ContinuousAt, ← (Topology.IsOpenEmbedding.inclusion hUI hUo).map_nhds_eq]
      change Tendsto (F ∘ Set.inclusion hUI) (𝓝 (⟨x.val,hx⟩ : U)) (𝓝 (F x))
      have hFx : F x = f ⟨x.val,hx⟩ := hF ⟨x.val,hx⟩
      simpa only [Function.comp_def, hF, hFx] using
        (hfc.continuousAt (x := (⟨x.val,hx⟩ : U))).tendsto
    exact hcat.continuousWithinAt
  have hHt : ∀ x, x.val ∈ U → Tendsto (fun i => H i x) atTop (𝓝 (F x)) := by
    intro x hx
    simpa only [← hH _ ⟨x.val,hx⟩, ← hF ⟨x.val,hx⟩] using ht ⟨x.val,hx⟩
  have he := zeroLocus_maximum_local I hUo H hHg hHb F hFc hHt
    (q := Set.inclusion hUI q) q.property (by simpa only [hF] using hfq)
  have he' := (Topology.IsEmbedding.inclusion hUI).continuous.continuousAt.eventually he
  simpa only [hF] using he'

theorem scalar_maximum_of_holomorphy {n : ℕ}
    {V U : Set (Affine n)} (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U)) (hconn : IsPreconnected U)
    (h : ℕ → U → ℂ) (hh : ∀ i q, ScalarAnalyticAt (h i) q)
    (hb : ∀ i q, ‖h i q‖ ≤ 1) (f : U → ℂ) (hfc : Continuous f)
    (ht : ∀ x, Tendsto (fun i => h i x) atTop (𝓝 (f x)))
    {q : U} (hfq : f q = 1) : ∀ x, f x = 1 := by
  let : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  exact eq_one_of_local_maximum_propagation f hfc q hfq
    (fun _ hx => scalar_maximum_local_of_holomorphy hV hUV hU h hh hb f hfc ht hx)

theorem finite_sheet_isolating_neighborhood
    {X Y K : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [Finite K]
    (s : K → Y → X) {a : Y} (hs : ∀ i, ContinuousAt (s i) a)
    (hi : Function.Injective (fun i => s i a)) (i : K) :
    ∃ O : Set X, IsOpen O ∧ s i a ∈ O ∧ ∃ B : Set Y, IsOpen B ∧ a ∈ B ∧
      ∀ y ∈ B, ∀ j, s j y ∈ O ↔ j = i := by
  classical
  let A : Set X := Set.range (fun j => s j a)
  obtain ⟨U,hU,hUdisj⟩ := (Set.finite_range (fun j => s j a)).t2_separation
  have ha : s i a ∈ A := mem_range_self i
  let O := U (s i a)
  have hO : IsOpen O := (hU _).2
  have hsO : ∀ᶠ y in 𝓝 a, s i y ∈ O := (hs i).preimage_mem_nhds (hO.mem_nhds ((hU _).1))
  have hsnot : ∀ j, ∀ᶠ y in 𝓝 a, j ≠ i → s j y ∉ O := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall (fun _ hj => False.elim (hj hji))
    · have haj : s j a ∈ A := mem_range_self j
      have hDis : Disjoint (U (s j a)) O := hUdisj haj ha (fun he => hji (hi he))
      filter_upwards [(hs j).preimage_mem_nhds (((hU _).2).mem_nhds ((hU _).1))] with y hy _
      exact Set.disjoint_left.mp hDis hy
  have hE : ∀ᶠ y in 𝓝 a, ∀ j, s j y ∈ O ↔ j = i := by
    filter_upwards [hsO, Filter.eventually_all.mpr hsnot] with y hy hnot
    intro j
    constructor
    · intro hj
      by_contra hji
      exact hnot j hji hj
    · rintro rfl
      exact hy
  obtain ⟨B,hBE,hBo,haB⟩ := mem_nhds_iff.mp hE
  exact ⟨O,hO,(hU _).1,B,hBo,haB,hBE⟩

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ZeroLocusPolynomialSmooth
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra


theorem finite_analytic_sheets_chart {n d : ℕ} {K : Type*} [Finite K]
    (V : Set (Affine n)) (π : Affine n → Affine d)
    (hπ : AnalyticOnNhd ℂ π univ)
    {A : Set (Affine d)} (hA : IsOpen A)
    (g : K → Affine d → Affine n) (hg : ∀ i, AnalyticOnNhd ℂ (g i) A)
    (hsheets : ∀ y ∈ A, Function.Injective (fun i => g i y) ∧
      ∀ z, z ∈ V ∧ π z = y ↔ ∃ i, g i y = z)
    {q : Affine n} (hq : q ∈ V) (hqa : π q ∈ A) :
    ∃ W : Set (Affine n), W ⊆ V ∧ IsOpen ((Subtype.val : V → Affine n) ⁻¹' W) ∧ q ∈ W ∧
      ∃ D : Set (Affine d), IsOpen D ∧ Nonempty (Biholomorph W D) := by
  obtain ⟨i,hi⟩ := (hsheets (π q) hqa).2 q |>.mp ⟨hq,rfl⟩
  obtain ⟨O,hO,hqO,B,hB,haB,hiso⟩ := finite_sheet_isolating_neighborhood g
    (fun j => (hg j (π q) hqa).continuousAt) (hsheets (π q) hqa).1 i
  let D := B ∩ A
  have hD : IsOpen D := hB.inter hA
  let W := V ∩ π ⁻¹' D ∩ O
  have hWV : W ⊆ V := fun _ hx => hx.1.1
  have hWo : IsOpen ((Subtype.val : V → Affine n) ⁻¹' W) := by
    have he : (Subtype.val : V → Affine n) ⁻¹' W =
        (fun x : V => π x.val) ⁻¹' D ∩ (Subtype.val : V → Affine n) ⁻¹' O := by
      ext x
      simp only [W, mem_preimage, mem_inter_iff, x.property, true_and]
    rw [he]
    exact (hD.preimage (hπ.continuous.comp continuous_subtype_val)).inter
      (hO.preimage continuous_subtype_val)
  have hqW : q ∈ W := ⟨⟨hq,⟨haB,hqa⟩⟩,hi ▸ hqO⟩
  have hgy : ∀ y ∈ D, g i y ∈ V ∧ π (g i y) = y := by
    intro y hy
    exact (hsheets y hy.2).2 (g i y) |>.mpr ⟨i,rfl⟩
  have hgW : MapsTo (g i) D W := by
    intro y hy
    exact ⟨⟨(hgy y hy).1, by change π (g i y) ∈ D; rw [(hgy y hy).2]; exact hy⟩,
      (hiso y hy.1 i).mpr rfl⟩
  have hgπ : ∀ z ∈ W, g i (π z) = z := by
    intro z hz
    obtain ⟨j,hj⟩ := (hsheets (π z) hz.1.2.2).2 z |>.mp ⟨hz.1.1,rfl⟩
    have hji : j = i := (hiso (π z) hz.1.2.1 j).mp (by rw [hj]; exact hz.2)
    simpa only [hji] using hj
  exact ⟨W,hWV,hWo,hqW,D,hD,⟨biholomorphOfAmbientInverse W D π (g i)
    (hπ.mono (subset_univ _)) ((hg i).mono inter_subset_right)
    (fun _ hz => hz.1.2) hgW hgπ (fun y hy => (hgy y hy).2)⟩⟩

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_DiscRelationCompactLocal
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Release061
open Set Filter Topology
open Set Filter Metric MeasureTheory
open scoped Topology
open Polynomial
open Polynomial Algebra
open scoped nonZeroDivisors
open Polynomial Algebra

theorem peakLinear_re {n : ℕ} (p q : Affine n) :
    (peakLinear p q).re = coordinateEnergy q - coordinateEnergy p - coordinateEnergy (q-p) := by
  simp only [peakLinear, coordinateEnergy, Complex.re_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Complex.mul_re, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im,
    Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring

theorem coordinateEnergy_nonneg {n : ℕ} (z : Affine n) : 0 ≤ coordinateEnergy z :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem sq_norm_le_coordinateEnergy {n : ℕ} (z : Affine n) : ‖z‖^2 ≤ coordinateEnergy z := by
  have h : ‖z‖ ≤ Real.sqrt (coordinateEnergy z) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply (Real.le_sqrt (norm_nonneg _) (coordinateEnergy_nonneg z)).mpr
    exact Finset.single_le_sum (fun j _ => sq_nonneg ‖z j‖) (Finset.mem_univ i)
  exact (Real.le_sqrt (norm_nonneg _) (coordinateEnergy_nonneg z)).mp h

theorem coordinateEnergy_continuous {n : ℕ} : Continuous (@coordinateEnergy n) := by
  unfold coordinateEnergy
  fun_prop

 theorem peakLinear_analytic {n : ℕ} (p : Affine n) : AnalyticOnNhd ℂ (peakLinear p) univ := by
  intro q _
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul (analyticAt_const.mul (((ContinuousLinearMap.proj i : (Affine n) →L[ℂ] ℂ).analyticAt q).sub analyticAt_const))

theorem HolomorphicOnSubset.entire_scalar_comp {n m : ℕ} {S : Set (Affine n)}
    {F : S → Affine m} (hF : HolomorphicOnSubset S F)
    {h : Affine m → ℂ} (hh : AnalyticOnNhd ℂ h univ) (q : S) :
    ScalarAnalyticAt (fun x => h (F x)) q := by
  obtain ⟨W,hW,hqW,G,hG,he⟩ := hF q
  refine ⟨h ∘ G,(hh (G q) (mem_univ _)).comp (hG q hqW),?_⟩
  filter_upwards [continuous_subtype_val.continuousAt.preimage_mem_nhds (hW.mem_nhds hqW)] with x hx
  exact congrArg h (he x hx).symm

end Release061

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ParameterPeakMaximizer
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Complex Filter Metric
open scoped Topology

theorem parameterPeak_norm {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p q : Affine n) :
    ‖parameterPeak P a p q‖ =
      parameterPotential P a q / parameterPotential P a p *
        Real.exp (-coordinateEnergy (q-p)) := by
  simp only [parameterPeak,norm_mul,norm_div,Complex.norm_exp,Complex.add_re,
    peakLinear_re,map_sub,Complex.sub_re,parameterPotential]
  rw [show coordinateEnergy q-coordinateEnergy p-coordinateEnergy (q-p)+
      ((a q).re-(a p).re) = (coordinateEnergy q+(a q).re)-
        (coordinateEnergy p+(a p).re)-coordinateEnergy (q-p) by ring,
    Real.exp_sub,Real.exp_sub,Real.exp_neg]
  ring

theorem parameterPeak_analytic {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) (p : Affine n) :
    AnalyticOnNhd ℂ (parameterPeak P a p) univ := by
  intro q _
  have hsub : AnalyticAt ℂ (fun x : Affine n => x-p) q := analyticAt_id.sub analyticAt_const
  have ha := (a.analyticAt (q-p)).comp (f := fun x : Affine n => x-p) (x := q) hsub
  exact (((AnalyticOnNhd.eval_mvPolynomial P) q (mem_univ _)).mul analyticAt_const).mul
    (((peakLinear_analytic p q (mem_univ _)).add
      ha).cexp)

theorem parameterPeak_self {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {p : Affine n} (hp : MvPolynomial.eval p P ≠ 0) :
    parameterPeak P a p p = 1 := by simp [parameterPeak,peakLinear,hp]

theorem parameterPeak_bound {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {K : Set (Affine n)} {p : Affine n}
    (hp : MvPolynomial.eval p P ≠ 0) (hmax : IsMaxOn (parameterPotential P a) K p) :
    ∀ q ∈ K, ‖parameterPeak P a p q‖ ≤ Real.exp (-(dist q p)^2) := by
  intro q hq
  rw [parameterPeak_norm]
  have hpp : 0 < parameterPotential P a p :=
    mul_pos (norm_pos_iff.mpr hp) (Real.exp_pos _)
  have hh := (div_le_one hpp).mpr (hmax hq)
  calc
    _ ≤ 1 * Real.exp (-coordinateEnergy (q-p)) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ ≤ Real.exp (-(dist q p)^2) := by
      rw [one_mul,dist_eq_norm]
      exact Real.exp_le_exp.mpr (neg_le_neg (sq_norm_le_coordinateEnergy _))

theorem exists_parameterPeak_maximizer {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (a : Affine n →L[ℂ] ℂ) {K : Set (Affine n)} (hK : IsCompact K)
    (hne : ∃ q ∈ K, MvPolynomial.eval q P ≠ 0) :
    ∃ p ∈ K, MvPolynomial.eval p P ≠ 0 ∧ IsMaxOn (parameterPotential P a) K p := by
  have hw : Continuous (parameterPotential P a) :=
    (MvPolynomial.continuous_eval P).norm.mul
      (Real.continuous_exp.comp (coordinateEnergy_continuous.add
        (Complex.continuous_re.comp a.continuous)))
  obtain ⟨q,hq,hqP⟩ := hne
  obtain ⟨p,hp,hmax⟩ := hK.exists_isMaxOn ⟨q,hq⟩ hw.continuousOn
  refine ⟨p,hp,?_,hmax⟩
  have hpw : 0 < parameterPotential P a p :=
    (mul_pos (norm_pos_iff.mpr hqP) (Real.exp_pos _)).trans_le (hmax hq)
  intro hzero
  simp [parameterPotential,hzero] at hpw

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_BoundaryParameterPeakMaximizer
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology _root_.OAI.Release061.Wiener.instFactLtRealOfNat_solutions
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter
open scoped Topology

theorem strict_peak_point_not_mem {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton)
    {p : Affine n} {h : Affine n → ℂ} (hh : AnalyticOnNhd ℂ h univ)
    (hpp : h p = 1)
    (hpeak : ∀ q ∈ U, ‖h q‖ ≤ Real.exp (-(dist q p)^2)) : p ∉ U := by
  intro hp
  let f : U → ℂ := fun q => h q.val
  have hg : ∀ (j : ℕ) (q : U), ScalarAnalyticAt (f) q := fun _ q =>
    (holomorphicOnSubset_val U).entire_scalar_comp hh q
  have hb : ∀ (j : ℕ) (q : U), ‖f q‖ ≤ 1 := by
    intro _ q
    exact (hpeak q.val q.property).trans
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _)))
  have hfc : Continuous f := hh.continuous.comp continuous_subtype_val
  have he : ∀ q : U, f q = 1 := scalar_maximum_of_holomorphy hV hUV hU hc
    (fun _ => f) hg hb f hfc (fun _ => tendsto_const_nhds) (q := ⟨p,hp⟩) hpp
  have hall : ∀ q ∈ U, q = p := by
    intro q hq
    have hle : 1 ≤ Real.exp (-(dist q p)^2) := by
      simpa only [show h q = 1 from he ⟨q,hq⟩,norm_one] using hpeak q hq
    have hsq : 0 ≤ -(dist q p)^2 := Real.exp_le_exp.mp (by simpa using hle)
    have hd : dist q p = 0 := by nlinarith [sq_nonneg (dist q p)]
    exact dist_eq_zero.mp hd
  exact hn (fun x hx y hy => (hall x hx).trans (hall y hy).symm)

end

open Set

theorem parameterPeak_maximizer_boundary {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton)
    (P : MvPolynomial (Fin n) ℂ) (a : Affine n →L[ℂ] ℂ)
    {p : Affine n} (hp : p ∈ closure U) (hpP : MvPolynomial.eval p P ≠ 0)
    (hm : IsMaxOn (parameterPotential P a) (closure U) p) :
    p ∈ closure U \ U := by
  exact ⟨hp, strict_peak_point_not_mem hV hUV hU hc hn
    (parameterPeak_analytic P a p) (parameterPeak_self P a hpP)
    (fun q hq => parameterPeak_bound P a hpP hm q (subset_closure hq))⟩

theorem exists_boundary_parameterPeak_maximizer {n : ℕ} {V U : Set (Affine n)}
    (hV : IsAffineAlgebraic V) (hUV : U ⊆ V)
    (hU : IsOpen ((Subtype.val : V → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (P : MvPolynomial (Fin n) ℂ) (hP : ∃ q ∈ U, MvPolynomial.eval q P ≠ 0)
    (a : Affine n →L[ℂ] ℂ) :
    ∃ p ∈ closure U \ U, MvPolynomial.eval p P ≠ 0 ∧
      IsMaxOn (parameterPotential P a) (closure U) p := by
  obtain ⟨q,hq,hqP⟩ := hP
  obtain ⟨p,hp,hpP,hm⟩ := exists_parameterPeak_maximizer P a hb.isCompact_closure
    ⟨q,subset_closure hq,hqP⟩
  exact ⟨p,parameterPeak_maximizer_boundary hV hUV hU hc hn P a hp hpP hm,hpP,hm⟩
end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_ClosedMaximizerRelation
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set MeasureTheory _root_.Module Filter
open scoped Topology ENNReal

theorem isClosed_maximizer_relation {X P : Type*} [TopologicalSpace X]
    [TopologicalSpace P] {K : Set X} (hK : IsClosed K)
    {w : P → X → ℝ} (hw : Continuous (Function.uncurry w)) :
    IsClosed {z : X × P | z.1 ∈ K ∧ ∀ q ∈ K, w z.2 q ≤ w z.2 z.1} := by
  have hc : IsClosed {z : X × P | ∀ q ∈ K, w z.2 q ≤ w z.2 z.1} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro q
    apply isClosed_iInter
    intro _hq
    exact isClosed_le (hw.comp (continuous_snd.prodMk continuous_const))
      (hw.comp (continuous_snd.prodMk continuous_fst))
  exact (hK.preimage continuous_fst).inter hc

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PolynomialSignSetInf
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.PolynomialSignSet
open Set
open scoped Classical

lemma iff_set {X ι : Type*} {c : X → ι → ℝ} {P Q : X → Prop}
    (hP : PolynomialSignSet c {x | P x}) (hQ : PolynomialSignSet c {x | Q x}) :
    PolynomialSignSet c {x | P x ↔ Q x} := by
  convert (hP.inter hQ).union (hP.compl.inter hQ.compl) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff,mem_compl_iff]
  tauto

lemma norm_lt_polynomial {X ι κ : Type*} [Fintype κ] {c : X → ι → ℝ}
    (p : κ → MvPolynomial ι ℝ) (q : MvPolynomial ι ℝ) :
    PolynomialSignSet c {x | ‖fun k => MvPolynomial.eval (c x) (p k)‖ <
      MvPolynomial.eval (c x) q} := by
  have h := (PolynomialSignSet.positive (c := c) q).inter
    (PolynomialSignSet.forall_finite (fun k x =>
      0 < MvPolynomial.eval (c x) (q+p k) ∧ 0 < MvPolynomial.eval (c x) (q-p k))
      (fun k => (PolynomialSignSet.positive (q+p k)).inter
        (PolynomialSignSet.positive (q-p k))))
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_inter_iff,mem_ofPred_eq,MvPolynomial.eval_add,MvPolynomial.eval_sub]
  constructor
  · intro hx
    have hq : 0 < MvPolynomial.eval (c x) q := (norm_nonneg _).trans_lt hx
    refine ⟨hq,fun k => ?_⟩
    have hk := (pi_norm_lt_iff hq).mp hx k
    rw [Real.norm_eq_abs,abs_lt] at hk
    constructor <;> linarith [hk.1,hk.2]
  · rintro ⟨hq,h⟩
    apply (pi_norm_lt_iff hq).mpr
    intro k
    rw [Real.norm_eq_abs,abs_lt]
    constructor <;> linarith [(h k).1,(h k).2]

end Release061.PolynomialSignSet

namespace Release061.SignElimination
open Set Metric
open scoped Classical

lemma polynomialSignSet_forall_one {X ι : Type*} {c : X → ι → ℝ}
    {P : X × ℝ → Prop}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | P z}) : PolynomialSignSet c {x | ∀ t : ℝ, P (x,t)} := by
  convert (polynomialSignSet_projection_one h.compl).compl using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp

lemma polynomialSignSet_graph_of_sublevel {X ι : Type*} {c : X → ι → ℝ}
    {f : X → ℝ}
    (h : PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | f z.1 < z.2}) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = f z.1} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × ℝ => fun o => Option.elim o z.2 (d z.1)
  have hh : PolynomialSignSet e {z | f z.1.1 < z.2} :=
    h.coordinate_preimage (fun z : (X × ℝ) × ℝ => (z.1.1,z.2))
      (fun o => Option.elim o none (fun i => some (some i))) (by
        intro z o; cases o <;> rfl)
  have ht : PolynomialSignSet e {z | z.1.2 < z.2} := by
    convert PolynomialSignSet.positive (c := e)
      (MvPolynomial.X none-MvPolynomial.X (some none)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp [e,d]
  have hq := polynomialSignSet_forall_one (hh.iff_set ht)
  convert hq using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_ofPred_eq]
  constructor
  · intro hz t
    rw [hz]
  · intro hz
    exact le_antisymm (le_of_not_gt (fun hlt => (lt_irrefl _) ((hz z.2).mp hlt)))
      (le_of_not_gt (fun hlt => (lt_irrefl _) ((hz (f z.1)).mpr hlt)))

lemma polynomialSignSet_near_fiber {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (p : κ → MvPolynomial ι ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | ∃ y ∈ A z.1, dist (fun k => MvPolynomial.eval (c z.1) (p k)) y < z.2} := by
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  let e := fun z : (X × ℝ) × (κ → ℝ) => Sum.elim (d z.1) z.2
  have ha : PolynomialSignSet e {z | z.2 ∈ A z.1.1} :=
    hA.coordinate_preimage (fun z : (X × ℝ) × (κ → ℝ) => (z.1.1,z.2)) (Sum.map some id)
      (by intro z i; cases i <;> rfl)
  have hn : PolynomialSignSet e {z | dist
      (fun k => MvPolynomial.eval (c z.1.1) (p k)) z.2 < z.1.2} := by
    convert PolynomialSignSet.norm_lt_polynomial (c := e)
      (fun k => MvPolynomial.rename (fun i => Sum.inl (some i)) (p k)-MvPolynomial.X (Sum.inr k))
      (MvPolynomial.X (Sum.inl none)) using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [mem_ofPred_eq,dist_eq_norm,MvPolynomial.eval_sub,MvPolynomial.eval_X,
      MvPolynomial.eval_rename]
    rfl
  exact polynomialSignSet_projection_finite (ha.inter hn)

lemma polynomialSignSet_infDist_graph {X ι κ : Type*} [Fintype κ]
    {c : X → ι → ℝ} (A : X → Set (κ → ℝ))
    (hA : PolynomialSignSet (fun z : X × (κ → ℝ) => Sum.elim (c z.1) z.2)
      {z | z.2 ∈ A z.1}) (p : κ → MvPolynomial ι ℝ) :
    PolynomialSignSet (fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1))
      {z | z.2 = infDist (fun k => MvPolynomial.eval (c z.1) (p k)) (A z.1)} := by
  have hne : PolynomialSignSet c {x | (A x).Nonempty} :=
    polynomialSignSet_projection_finite hA
  let d := fun z : X × ℝ => fun o => Option.elim o z.2 (c z.1)
  have hemp : PolynomialSignSet d {z | ¬ (A z.1).Nonempty} :=
    hne.compl.coordinate_preimage Prod.fst some (by intros; rfl)
  have ht : PolynomialSignSet d {z | 0 < z.2} := by
    simpa only [MvPolynomial.eval_X,d,Option.elim_none] using
      (PolynomialSignSet.positive (c := d) (MvPolynomial.X none))
  have hsub := (hemp.inter ht).union (polynomialSignSet_near_fiber A hA p)
  apply polynomialSignSet_graph_of_sublevel (f := fun x => infDist (fun k => MvPolynomial.eval (c x) (p k)) (A x))
  convert hsub using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_ofPred_eq,mem_union,mem_inter_iff]
  by_cases he : (A z.1).Nonempty
  · simp only [he,not_true_eq_false,false_and,false_or,infDist_lt_iff he]
  · have ha := Set.not_nonempty_iff_eq_empty.mp he
    simp [ha]

end Release061.SignElimination

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_NormalOffsetFamilyJoint
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061.PolynomialSignSet
open Set Metric Filter Topology Classical SignElimination

lemma closure {κ : Type*} [Fintype κ] {A : Set (κ → ℝ)}
    (hA : PolynomialSignSet id A) : PolynomialSignSet id (_root_.closure A) := by
  by_cases hne : A.Nonempty
  · let d := fun z : (κ → ℝ) × (κ → ℝ) => Sum.elim z.1 z.2
    have ha : PolynomialSignSet d {z | z.2 ∈ A} :=
      hA.coordinate_preimage (fun z : (κ → ℝ) × (κ → ℝ) => z.2) Sum.inr
        (by intros; rfl)
    have hg := polynomialSignSet_infDist_graph (c := id) (fun _ : κ → ℝ => A) ha
      (fun k => MvPolynomial.X k)
    have he : PolynomialSignSet id {x : κ → ℝ | 0 = infDist x A} := by
      convert hg.polynomial_preimage (fun x : κ → ℝ => (x,0))
        (fun o => Option.elim o 0 MvPolynomial.X) (d := id) ?_ using 1
      · ext x
        simp only [mem_preimage,mem_ofPred_eq,MvPolynomial.eval_X,id_eq]
      · intro x o
        cases o <;> simp
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    exact (mem_closure_iff_infDist_zero hne).trans eq_comm
  · rw [not_nonempty_iff_eq_empty.mp hne,closure_empty]
    exact .empty

end Release061.PolynomialSignSet

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CriticalAffineBundleNeighborhood
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem exists_continuousLinearEquiv_prod_ker
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : E →L[ℝ] X) (hA : Function.Surjective A) :
    ∃ e : E ≃L[ℝ] X × LinearMap.ker A.toLinearMap, ∀ v, (e v).1 = A v := by
  obtain ⟨R,hR⟩ := ContinuousLinearMap.HasRightInverse.of_surjective_of_finiteDimensional hA
  let K := LinearMap.ker A.toLinearMap
  let L : E →ₗ[ℝ] X × K :=
    { toFun := fun v => (A v,⟨v-R (A v),by change A (v-R (A v)) = 0; rw [map_sub,hR,sub_self]⟩)
      map_add' := by intro v w; ext <;> simp [map_add]; abel
      map_smul' := by intro c v; ext <;> simp [map_smul,smul_sub] }
  have hinj : Function.Injective L := by
    intro v w he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg (fun p : X × K => (p.2 : E)) he
    change A v = A w at h1
    change v-R (A v) = w-R (A w) at h2
    rw [h1] at h2
    exact sub_left_injective h2
  have hsurj : Function.Surjective L := by
    rintro ⟨x,k⟩
    refine ⟨R x+k,?_⟩
    have hk : A k = 0 := k.property
    have ha : A (R x+k) = x := by rw [map_add,hR,hk,add_zero]
    apply Prod.ext
    · exact ha
    · apply Subtype.ext
      change R x+(k : E)-R (A (R x+k)) = k
      rw [ha]
      abel
  exact ⟨(LinearEquiv.ofBijective L ⟨hinj,hsurj⟩).toContinuousLinearEquiv,fun _ => rfl⟩

theorem exists_continuousLinearEquiv_prod_fin
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (A : E →L[ℝ] X) (hA : Function.Surjective A) :
    ∃ r : ℕ, ∃ e : E ≃L[ℝ] X × (Fin r → ℝ), ∀ v, (e v).1 = A v := by
  obtain ⟨e,he⟩ := exists_continuousLinearEquiv_prod_ker A hA
  let r := Module.finrank ℝ (LinearMap.ker A.toLinearMap)
  let v : LinearMap.ker A.toLinearMap ≃L[ℝ] (Fin r → ℝ) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [r])
  refine ⟨r,e.trans ((ContinuousLinearEquiv.refl ℝ X).prodCongr v),?_⟩
  exact he

variable {E X K : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup K] [NormedSpace ℝ K] [FiniteDimensional ℝ K]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in
lemma criticalBundleLinear_contDiffAt {A : X → E →L[ℝ] X} (e : E ≃L[ℝ] X × K)
    {x : X} (hA : ContDiffAt ℝ 1 A x) : ContDiffAt ℝ 1 (criticalBundleLinear A e) x := by
  have he : criticalBundleLinear A e = fun y =>
      (ContinuousLinearMap.inl ℝ X K).comp (A y) + (ContinuousLinearMap.inr ℝ X K).comp
        ((ContinuousLinearMap.snd ℝ X K).comp e.toContinuousLinearMap) := by
    funext y
    ext v <;> simp [criticalBundleLinear]
  rw [he]
  exact (contDiffAt_const.clm_comp hA).add contDiffAt_const

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in
lemma criticalBundleParam_contDiffAt {A : X → E →L[ℝ] X} (e : E ≃L[ℝ] X × K)
    {b : X → X} {p : X × K} (hA : ContDiffAt ℝ 1 A p.1) (hb : ContDiffAt ℝ 1 b p.1)
    (hi : (criticalBundleLinear A e p.1).IsInvertible) :
    ContDiffAt ℝ 1 (criticalBundleParam A e b) p := by
  have h := hi.contDiffAt_map_inverse.comp p.1 (criticalBundleLinear_contDiffAt e hA)
  exact (h.comp p contDiffAt_fst).clm_apply ((hb.comp p contDiffAt_fst).prodMk contDiffAt_snd)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in
lemma criticalBundleParam_fibre {A : X → E →L[ℝ] X} (e : E ≃L[ℝ] X × K)
    {b : X → X} {x : X} (hi : (criticalBundleLinear A e x).IsInvertible) :
    range (fun k : K => criticalBundleParam A e b (x,k)) = {a | A x a = b x} := by
  ext a
  constructor
  · rintro ⟨k,rfl⟩
    exact congrArg Prod.fst (hi.self_apply_inverse (b x,k))
  · intro ha
    refine ⟨(e a).2,?_⟩
    have he : (b x,(e a).2) = criticalBundleLinear A e x a := by
      apply Prod.ext
      · exact ha.symm
      · rfl
    change (criticalBundleLinear A e x).inverse (b x,(e a).2) = a
    rw [he]
    exact hi.inverse_apply_self a

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ K] in

theorem critical_affine_bundle_neighborhood
    (A : X → E →L[ℝ] X) (B : Set X) (hB : IsOpen B)
    (hA : ∀ x ∈ B, ContDiffAt ℝ 1 A x) (b : X → X)
    (hb : ∀ x ∈ B, ContDiffAt ℝ 1 b x) {x₀ : X} (hx₀ : x₀ ∈ B)
    (e : E ≃L[ℝ] X × K) (he : ∀ v, (e v).1 = A x₀ v) :
    ∃ W : Set X, IsOpen W ∧ x₀ ∈ W ∧ W ⊆ B ∧
      (∀ x ∈ W, (criticalBundleLinear A e x).IsInvertible) ∧
      ContDiffOn ℝ 1 (criticalBundleParam A e b) (W ×ˢ univ) ∧
      ∀ x ∈ W, range (fun k : K => criticalBundleParam A e b (x,k)) = {a | A x a = b x} := by
  let C : X → E →L[ℝ] E := fun x => e.symm.toContinuousLinearMap.comp (criticalBundleLinear A e x)
  have hC (x : X) (hx : x ∈ B) : ContinuousAt C x :=
    (contDiffAt_const.clm_comp (criticalBundleLinear_contDiffAt e (hA x hx))).continuousAt
  have hC₀ : C x₀ = ContinuousLinearMap.id ℝ E := by
    ext v
    change e.symm (A x₀ v,(e v).2) = v
    rw [← he]
    exact e.symm_apply_apply v
  let W : Set X := {x | x ∈ B ∧ (C x).det ≠ 0}
  have hWo : IsOpen W := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    exact inter_mem (hB.mem_nhds hx.1)
      (((ContinuousLinearMap.continuous_det.continuousAt.comp (hC x hx.1)).eventually_ne hx.2))
  have hWi (x : X) (hx : x ∈ W) : (criticalBundleLinear A e x).IsInvertible := by
    let v := (C x).toContinuousLinearEquivOfDetNeZero hx.2
    refine ⟨v.trans e,?_⟩
    apply ContinuousLinearMap.ext
    intro a
    change e (C x a) = criticalBundleLinear A e x a
    exact e.apply_symm_apply _
  refine ⟨W,hWo,?_,fun _ hx => hx.1,hWi,?_,fun x hx => criticalBundleParam_fibre e (hWi x hx)⟩
  · exact ⟨hx₀,by rw [hC₀]; change LinearMap.det (LinearMap.id : E →ₗ[ℝ] E) ≠ 0; rw [LinearMap.det_id]; exact one_ne_zero⟩
  · intro p hp
    exact (criticalBundleParam_contDiffAt e (hA p.1 hp.1.1) (hb p.1 hp.1.1) (hWi p.1 hp.1)).contDiffWithinAt

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_RealCriticalMatrix
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

lemma realCriticalMatrix_apply {d N : ℕ} (q : (Fin d → ℝ) → (Fin N → ℂ))
    (x : Fin d → ℝ) (a : (Fin N → ℂ) →L[ℂ] ℂ) :
    realCriticalMatrix q x a =
      (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d))
        ((Complex.reCLM.comp (a.restrictScalars ℝ)).comp (fderiv ℝ q x)) := rfl

lemma realCriticalMatrix_surjective {d N : ℕ} (q : (Fin d → ℝ) → (Fin N → ℂ))
    {x : Fin d → ℝ} (hq : Function.Injective (fderiv ℝ q x)) :
    Function.Surjective (realCriticalMatrix q x) := by
  let v := ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)
  intro t
  obtain ⟨l,hl⟩ := LinearMap.dualMap_surjective_of_injective hq (v.symm t).toLinearMap
  let l' : (Fin N → ℂ) →L[ℝ] ℝ := l.toContinuousLinearMap
  refine ⟨(StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)) l',?_⟩
  change v (((ContinuousLinearMap.compL ℝ (Fin d → ℝ) (Fin N → ℂ) ℝ).flip (fderiv ℝ q x))
    ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)).symm
      ((StrongDual.extendRCLikeL (𝕜 := ℂ) (F := Fin N → ℂ)) l'))) = t
  rw [ContinuousLinearEquiv.symm_apply_apply]
  change v (l'.comp (fderiv ℝ q x)) = t
  have he : l'.comp (fderiv ℝ q x) = v.symm t := by
    apply ContinuousLinearMap.ext
    intro z
    exact congrArg (fun L : (Fin d → ℝ) →ₗ[ℝ] ℝ => L z) hl
  rw [he,v.apply_symm_apply]

lemma realCriticalMatrix_contDiffAt {d N : ℕ} (q : (Fin d → ℝ) → (Fin N → ℂ))
    {x : Fin d → ℝ} (hq : ContDiffAt ℝ 2 q x) :
    ContDiffAt ℝ 1 (realCriticalMatrix q) x := by
  have hq' : ContDiffAt ℝ 1 (fderiv ℝ q) x := hq.fderiv_right (by norm_num)
  let L := (ContinuousLinearMap.compL ℝ (Fin d → ℝ) (Fin N → ℂ) ℝ).flip
  have hL0 : ContDiff ℝ 1 (fun v : (Fin d → ℝ) →L[ℝ] (Fin N → ℂ) => L v) := by
    apply ContinuousLinearMap.contDiff
  have hL : ContDiffAt ℝ 1 (fun y => L (fderiv ℝ q y)) x :=
    hL0.contDiffAt.comp x hq'
  exact contDiffAt_const.clm_comp (hL.clm_comp contDiffAt_const)

lemma realCriticalConstant_contDiffAt {d : ℕ} (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hf : ContDiffAt ℝ 2 f x) :
    ContDiffAt ℝ 1 (realCriticalConstant f) x := by
  exact (((ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)).contDiff.contDiffAt).comp x
    (hf.fderiv_right (by norm_num))).neg

theorem realCriticalMatrix_eq_iff {d N : ℕ}
    (q : (Fin d → ℝ) → (Fin N → ℂ)) (f : (Fin d → ℝ) → ℝ)
    {x : Fin d → ℝ} (hq : DifferentiableAt ℝ q x) (hf : DifferentiableAt ℝ f x)
    (a : (Fin N → ℂ) →L[ℂ] ℂ) :
    realCriticalMatrix q x a = realCriticalConstant f x ↔
      fderiv ℝ (fun y => f y + (a (q y)).re) x = 0 := by
  have hd : HasFDerivAt (fun y => f y + (a (q y)).re)
      (fderiv ℝ f x + (Complex.reCLM.comp (a.restrictScalars ℝ)).comp (fderiv ℝ q x)) x :=
    hf.hasFDerivAt.add (((Complex.reCLM.comp (a.restrictScalars ℝ)).hasFDerivAt).comp x hq.hasFDerivAt)
  rw [hd.fderiv,realCriticalMatrix_apply,realCriticalConstant,← map_neg,
    (ContinuousLinearEquiv.piRing (𝕜 := ℝ) (E := ℝ) (Fin d)).injective.eq_iff]
  exact eq_neg_iff_add_eq_zero.trans (by rw [add_comm])

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicOffsetLimitsFamily
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter

namespace Release061
open Set Filter Topology Metric MeasureTheory Classical
open SignElimination

theorem isSemialgebraic_iff_polynomialSignSet {n : ℕ} {S : Set (Affine n)} :
    IsSemialgebraic S ↔ PolynomialSignSet realCoordinates S := by
  constructor
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'
  · intro h
    induction h with
    | zero p => exact .zero p
    | positive p => exact .positive p
    | compl _ ih => exact ih.compl
    | union _ _ ih ih' => exact ih.union ih'

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicBoundaryFiniteNash
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric
open SignElimination
open scoped Classical

lemma isSemialgebraic_real_image {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    PolynomialSignSet id (complexRealEquiv n '' S) := by
  have hh := (isSemialgebraic_iff_polynomialSignSet.mp hS).coordinate_preimage
    (complexRealEquiv n).symm finSumFinEquiv
    (d := id) (by intro x j; cases j <;> rfl)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  simp only [mem_image,mem_preimage]
  constructor
  · rintro ⟨z,hz,rfl⟩
    simpa using hz
  · intro hx
    exact ⟨_,hx,(complexRealEquiv n).apply_symm_apply x⟩

lemma isSemialgebraic_of_real_image {n : ℕ} {S : Set (Affine n)}
    (hS : PolynomialSignSet id (complexRealEquiv n '' S)) : IsSemialgebraic S := by
  apply isSemialgebraic_iff_polynomialSignSet.mpr
  have hh := hS.coordinate_preimage (complexRealEquiv n) finSumFinEquiv.symm
    (d := realCoordinates) (by intros; rfl)
  simpa only [Set.preimage_image_eq _ (complexRealEquiv n).injective] using hh

lemma IsSemialgebraic.closure {n : ℕ} {S : Set (Affine n)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (closure S) := by
  apply isSemialgebraic_of_real_image
  change PolynomialSignSet id ((complexRealEquiv n).toHomeomorph '' _root_.closure S)
  rw [(complexRealEquiv n).toHomeomorph.image_closure]
  exact (isSemialgebraic_real_image hS).closure

lemma IsSemialgebraic.inter {n : ℕ} {S T : Set (Affine n)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S ∩ T) := by
  exact isSemialgebraic_iff_polynomialSignSet.mpr
    ((isSemialgebraic_iff_polynomialSignSet.mp hS).inter
      (isSemialgebraic_iff_polynomialSignSet.mp hT))

lemma IsSemialgebraic.diff {n : ℕ} {S T : Set (Affine n)}
    (hS : IsSemialgebraic S) (hT : IsSemialgebraic T) : IsSemialgebraic (S \ T) :=
  hS.inter hT.compl

namespace NashPatch
variable {n : ℕ}

lemma analytic_complexMap (p : NashPatch (n+n)) : AnalyticOnNhd ℝ p.complexMap p.domain := by
  intro x hx
  exact ((complexRealEquiv n).symm.analyticAt _).comp (p.analytic_toFun x hx)

lemma injective_fderiv_complexMap (p : NashPatch (n+n)) {x : Fin p.dim → ℝ} (hx : x ∈ p.domain) :
    Function.Injective (fderiv ℝ p.complexMap x) := by
  have he := ((complexRealEquiv n).symm.hasFDerivAt.comp x
    (p.analytic_toFun x hx).differentiableAt.hasFDerivAt).fderiv
  change Function.Injective (fderiv ℝ ((complexRealEquiv n).symm ∘ p.toFun) x)
  rw [he]
  exact (complexRealEquiv n).symm.injective.comp (p.injective_fderiv x hx)

end NashPatch

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_MaximizerBundleBorel
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical ContDiff

lemma coordinateEnergy_contDiff {N : ℕ} {r : ℕ∞ω} : ContDiff ℝ r (@coordinateEnergy N) := by
  unfold coordinateEnergy
  exact ContDiff.sum (fun i _ => (ContinuousLinearMap.proj i : (Fin N → ℂ) →L[ℝ] ℂ).contDiff.norm_sq ℂ)

lemma parameterLogBase_contDiffAt {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    {z : Affine N} (hz : MvPolynomial.eval z P ≠ 0) {r : ℕ∞ω} :
    ContDiffAt ℝ r (parameterLogBase P) z := by
  have hP : ContDiffAt ℝ r (fun z => MvPolynomial.eval z P) z :=
    (((AnalyticOnNhd.eval_mvPolynomial P) z (mem_univ z)).restrictScalars (𝕜 := ℝ)).contDiffAt
  exact ((hP.norm ℂ hz).log (norm_ne_zero_iff.mpr hz)).add coordinateEnergy_contDiff.contDiffAt

lemma parameterPotential_eq_exp {N : ℕ} (P : MvPolynomial (Fin N) ℂ)
    (a : Affine N →L[ℂ] ℂ) {z : Affine N} (hz : MvPolynomial.eval z P ≠ 0) :
    parameterPotential P a z = Real.exp (parameterLogBase P z + (a z).re) := by
  rw [parameterLogBase,add_assoc,Real.exp_add,Real.exp_log (norm_pos_iff.mpr hz)]
  rfl

theorem actual_maximizer_critical {d N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (K : Set (Affine N)) (hqK : MapsTo q B K)
    (hP : ∀ x ∈ B, MvPolynomial.eval (q x) P ≠ 0)
    {x : Fin d → ℝ} (hx : x ∈ B) (hq : DifferentiableAt ℝ q x)
    (a : Affine N →L[ℂ] ℂ) (hmax : IsMaxOn (parameterPotential P a) K (q x)) :
    realCriticalMatrix q x a = realCriticalConstant (parameterLogBase P ∘ q) x := by
  apply (realCriticalMatrix_eq_iff q (parameterLogBase P ∘ q) hq
    ((parameterLogBase_contDiffAt P (hP x hx) (r := 1)).differentiableAt one_ne_zero |>.comp x hq) a).2
  apply IsLocalMax.fderiv_eq_zero
  filter_upwards [hB.mem_nhds hx] with y hy
  apply Real.exp_le_exp.mp
  simpa only [Function.comp_apply,← parameterPotential_eq_exp P a (hP y hy),
    ← parameterPotential_eq_exp P a (hP x hx)] using (show parameterPotential P a (q y) ≤ parameterPotential P a (q x) from hmax (hqK hy))

theorem actual_critical_bundle {d N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hq : ContDiffOn ℝ 2 q B)
    (hP : ∀ x ∈ B, MvPolynomial.eval (q x) P ≠ 0)
    {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ B) (hi : Function.Injective (fderiv ℝ q x₀)) :
    ∃ (r : ℕ) (e : (Affine N →L[ℂ] ℂ) ≃L[ℝ]
        ((Fin d → ℝ) × (Fin r → ℝ))) (W : Set (Fin d → ℝ)),
      IsOpen W ∧ x₀ ∈ W ∧ W ⊆ B ∧
      ContDiffOn ℝ 1 (criticalBundleParam (realCriticalMatrix q) e
        (realCriticalConstant (parameterLogBase P ∘ q))) (W ×ˢ univ) ∧
      ∀ x ∈ W, range (fun k => criticalBundleParam (realCriticalMatrix q) e
          (realCriticalConstant (parameterLogBase P ∘ q)) (x,k)) =
        {a | fderiv ℝ (fun y => parameterLogBase P (q y) + (a (q y)).re) x = 0} := by
  obtain ⟨r,e,he⟩ := exists_continuousLinearEquiv_prod_fin (realCriticalMatrix q x₀)
    (realCriticalMatrix_surjective q hi)
  have hq' (x : Fin d → ℝ) (hx : x ∈ B) : ContDiffAt ℝ 2 q x :=
    (hq x hx).contDiffAt (hB.mem_nhds hx)
  have hf (x : Fin d → ℝ) (hx : x ∈ B) :
      ContDiffAt ℝ 2 (parameterLogBase P ∘ q) x :=
    (parameterLogBase_contDiffAt P (hP x hx)).comp x (hq' x hx)
  obtain ⟨W,hWo,hx₀W,hWB,_,hpar,hfib⟩ := critical_affine_bundle_neighborhood
    (realCriticalMatrix q) B hB (fun x hx => realCriticalMatrix_contDiffAt q (hq' x hx))
    (realCriticalConstant (parameterLogBase P ∘ q))
    (fun x hx => realCriticalConstant_contDiffAt _ (hf x hx)) hx₀ e he
  refine ⟨r,e,W,hWo,hx₀W,hWB,hpar,?_⟩
  intro x hx
  rw [hfib x hx]
  ext a
  exact realCriticalMatrix_eq_iff q _ ((hq' x (hWB hx)).differentiableAt (by norm_num))
    ((hf x (hWB hx)).differentiableAt (by norm_num)) a

lemma parameterPotential_joint_continuous {N : ℕ} (P : MvPolynomial (Fin N) ℂ) :
    Continuous (Function.uncurry (parameterPotential P)) := by
  unfold parameterPotential Function.uncurry
  exact ((MvPolynomial.continuous_eval P).comp continuous_snd).norm.mul
    (Real.continuous_exp.comp ((coordinateEnergy_continuous.comp continuous_snd).add
      (Complex.continuous_re.comp (continuous_fst.clm_apply continuous_snd))))

lemma measurableSet_continuousOn_preimage
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y]
    {W : Set X} (hW : MeasurableSet W) {f : X → Y} (hf : ContinuousOn f W)
    {T : Set Y} (hT : MeasurableSet T) : MeasurableSet {x | x ∈ W ∧ f x ∈ T} := by
  classical
  let y₀ : Y := Classical.choice inferInstance
  have hg : Measurable (W.piecewise f (fun _ => y₀)) :=
    hf.measurable_piecewise continuousOn_const hW
  convert hW.inter (hT.preimage hg) using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  by_cases hx : x ∈ W <;> simp [hx]

theorem actual_maximizer_bundle_borel
    {X K : Type*} [TopologicalSpace X] [TopologicalSpace K]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology X] [SecondCountableTopology K]
    {N : ℕ} (P : MvPolynomial (Fin N) ℂ) {C : Set (Affine N)} (hC : IsClosed C)
    {W : Set X} (hW : MeasurableSet W) (q : X → Affine N) (hq : ContinuousOn q W)
    (A : X × K → (Affine N →L[ℂ] ℂ)) (hA : ContinuousOn A (W ×ˢ univ)) :
    MeasurableSet {p : X × K | p.1 ∈ W ∧ q p.1 ∈ C ∧
      IsMaxOn (parameterPotential P (A p)) C (q p.1)} := by
  have hc := isClosed_maximizer_relation hC (parameterPotential_joint_continuous P)
  have hh := measurableSet_continuousOn_preimage (hW.prod MeasurableSet.univ)
    ((hq.comp continuousOn_fst (fun _ hp => hp.1)).prodMk hA) hc.measurableSet
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  simp only [mem_ofPred_eq,mem_prod,mem_univ,and_true,IsMaxOn,IsMaxFilter,Filter.eventually_principal]
  rfl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_CriticalCountableCharts
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

namespace ActualCriticalChart
variable {d N : ℕ} {P : MvPolynomial (Fin N) ℂ} {q : (Fin d → ℝ) → Affine N}

lemma measurableSet_maxLocus (c : ActualCriticalChart P q) {K : Set (Affine N)} (hK : IsClosed K) :
    MeasurableSet (c.maxLocus K) :=
  actual_maximizer_bundle_borel P hK c.isOpen_base.measurableSet q c.continuous_q
    c.param c.smooth_param.continuousOn

lemma differentiableOn_param_maxLocus (c : ActualCriticalChart P q) (K : Set (Affine N)) :
    DifferentiableOn ℝ c.param (c.maxLocus K) :=
  (c.smooth_param.differentiableOn one_ne_zero).mono (fun _ hp => ⟨hp.1,mem_univ _⟩)

end ActualCriticalChart

theorem actual_critical_countable_charts {d N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (B : Set (Fin d → ℝ)) (hB : IsOpen B)
    (q : (Fin d → ℝ) → Affine N) (hq : ContDiffOn ℝ 2 q B)
    (hP : ∀ x ∈ B, MvPolynomial.eval (q x) P ≠ 0)
    (hi : ∀ x ∈ B, Function.Injective (fderiv ℝ q x)) :
    ∃ C : Set (ActualCriticalChart P q), C.Countable ∧
      (∀ c ∈ C, c.base ⊆ B) ∧ B ⊆ ⋃ c ∈ C, c.base := by
  have hex (x : B) : ∃ c : ActualCriticalChart P q, x.val ∈ c.base ∧ c.base ⊆ B := by
    obtain ⟨r,e,W,hWo,hxW,hWB,hpar,hfib⟩ := actual_critical_bundle P B hB q hq hP x.property
      (hi x.val x.property)
    exact ⟨⟨r,e,W,hWo,hq.continuousOn.mono hWB,hpar,hfib⟩,hxW,hWB⟩
  choose c hc hcB using hex
  obtain ⟨T,hTc,hT⟩ := (HereditarilyLindelofSpace.isLindelof B).elim_countable_subcover
    (fun x : B => (c x).base) (fun x => (c x).isOpen_base) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,hc ⟨x,hx⟩⟩)
  refine ⟨c '' T,hTc.image c,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact hcB x
  · intro x hx
    obtain ⟨y,hyT,hxy⟩ := mem_iUnion₂.mp (hT hx)
    exact mem_iUnion₂.mpr ⟨c y,mem_image_of_mem c hyT,hxy⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SupportedPositiveFiberVarying
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set MeasureTheory Filter
open scoped Topology

theorem haar_image_null_of_equiv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) (ν : Measure F) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (e : E ≃L[ℝ] F) {A : E → F} {S : Set E}
    (hA : DifferentiableOn ℝ A S) (hS : μ S = 0) : ν (A '' S) = 0 := by
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    (e.symm.differentiable.comp_differentiableOn hA) hS
  apply (Measure.absolutelyContinuous_isAddHaarMeasure ν (μ.map e))
  change (Measure.map e.toHomeomorph μ) (A '' S) = 0
  rw [e.toHomeomorph.measurableEmbedding.map_apply]
  suffices he : e.toHomeomorph ⁻¹' (A '' S) = (e.symm ∘ A) '' S by rwa [he]
  ext y
  simp only [mem_preimage,mem_image,Function.comp_apply]
  constructor
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,by rw [hxy]; exact e.symm_apply_apply y⟩
  · rintro ⟨x,hx,hxy⟩
    exact ⟨x,hx,by rw [← hxy]; exact (e.apply_symm_apply _).symm⟩

theorem supported_positive_fiber_varying
    {I P : Type*} [Countable I]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [MeasurableSpace P] [BorelSpace P]
    (ρ : Measure P) [ρ.IsAddHaarMeasure]
    (E F : I → Type*)
    [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, NormedAddCommGroup (F i)] [∀ i, NormedSpace ℝ (F i)]
    [∀ i, FiniteDimensional ℝ (F i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)]
    [∀ i, MeasurableSpace (F i)] [∀ i, BorelSpace (F i)]
    (μ : ∀ i, Measure (E i)) (ν : ∀ i, Measure (F i))
    [∀ i, (μ i).IsAddHaarMeasure] [∀ i, (ν i).IsAddHaarMeasure]
    (e : ∀ i, (E i × F i) ≃L[ℝ] P)
    (S : ∀ i, Set (E i × F i)) (hS : ∀ i, MeasurableSet (S i))
    (A : ∀ i, E i × F i → P) (hA : ∀ i, DifferentiableOn ℝ (A i) (S i))
    (bad : ∀ i, Set (E i)) (hbad : ∀ i, μ i (bad i) = 0)
    (T : Set P) (hT : ρ T ≠ 0) (hcover : T ⊆ ⋃ i, A i '' S i) :
    ∃ i x, x ∉ bad i ∧ ν i (Prod.mk x ⁻¹' S i) ≠ 0 := by
  by_contra hn
  push Not at hn
  have hzero (i : I) : (μ i |>.prod (ν i)) (S i) = 0 := by
    apply Measure.measure_prod_null_of_ae_null (hS i)
    filter_upwards [show ∀ᵐ x ∂μ i, x ∉ bad i from by
      rw [ae_iff]
      simpa only [not_not,Set.ofPred_mem_eq] using hbad i] with x hx
    exact hn i x hx
  have himage (i : I) : ρ (A i '' S i) = 0 :=
    haar_image_null_of_equiv ((μ i).prod (ν i)) ρ (e i) (hA i) (hzero i)
  exact hT (measure_mono_null hcover (measure_iUnion_null himage))

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PositiveMaximizerFiber
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology MeasureTheory
open scoped Classical

theorem actual_positive_maximizer_fiber
    {I : Type*} [Countable I] {N : ℕ}
    (P : MvPolynomial (Fin N) ℂ) (K : Set (Affine N)) (hK : IsClosed K)
    (d : I → ℕ) (B : ∀ i, Set (Fin (d i) → ℝ)) (hB : ∀ i, IsOpen (B i))
    (q : ∀ i, (Fin (d i) → ℝ) → Affine N)
    (hq : ∀ i, ContDiffOn ℝ 2 (q i) (B i))
    (hqK : ∀ i, MapsTo (q i) (B i) K)
    (hP : ∀ i x, x ∈ B i → MvPolynomial.eval (q i x) P ≠ 0)
    (hi : ∀ i x, x ∈ B i → Function.Injective (fderiv ℝ (q i) x))
    (bad : ∀ i, Set (Fin (d i) → ℝ)) (hbad : ∀ i, volume (bad i) = 0)
    (hcover : ∀ a : Affine N →L[ℂ] ℂ, ∃ i x, x ∈ B i ∧
      IsMaxOn (parameterPotential P a) K (q i x)) :
    ∃ i, ∃ (c : ActualCriticalChart P (q i)) (x : Fin (d i) → ℝ), c.base ⊆ B i ∧ x ∈ c.base ∧ x ∉ bad i ∧
      volume (Prod.mk x ⁻¹' c.maxLocus K) ≠ 0 := by
  choose C hCc hCB hcov using fun i => actual_critical_countable_charts P (B i) (hB i)
    (q i) (hq i) (hP i) (hi i)
  let : ∀ i, Countable (C i) := fun i => (hCc i).to_subtype
  let J := (i : I) × C i
  let E : J → Type := fun j => Fin (d j.1) → ℝ
  let F : J → Type := fun j => Fin j.2.val.fiberDim → ℝ
  let S (j : J) := j.2.val.maxLocus K
  let A (j : J) := j.2.val.param
  let : MeasurableSpace (Affine N →L[ℂ] ℂ) := borel _
  let ρ : Measure (Affine N →L[ℂ] ℂ) := Measure.addHaar
  have hρ : ρ univ ≠ 0 := by
    exact (isOpen_univ.measure_pos ρ Set.univ_nonempty).ne'
  have hall : univ ⊆ ⋃ j : J, A j '' S j := by
    intro a _
    obtain ⟨i,x,hx,hm⟩ := hcover a
    obtain ⟨c,hc,hxc⟩ := mem_iUnion₂.mp (hcov i hx)
    have hcrit := actual_maximizer_critical P (B i) (hB i) (q i) K (hqK i) (hP i) hx
      (((hq i x hx).contDiffAt ((hB i).mem_nhds hx)).differentiableAt (by norm_num)) a hm
    have heq := (realCriticalMatrix_eq_iff (q i) (parameterLogBase P ∘ q i)
      (((hq i x hx).contDiffAt ((hB i).mem_nhds hx)).differentiableAt (by norm_num))
      (((parameterLogBase_contDiffAt P (hP i x hx) (r := 1)).differentiableAt one_ne_zero).comp x
        (((hq i x hx).contDiffAt ((hB i).mem_nhds hx)).differentiableAt (by norm_num))) a).mp hcrit
    have har : a ∈ range (fun k => c.param (x,k)) := (c.range_param x hxc).symm ▸ heq
    obtain ⟨k,hk⟩ := har
    refine mem_iUnion.mpr ⟨⟨i,c,hc⟩,⟨(x,k),?_,hk⟩⟩
    exact ⟨hxc,hqK i hx,by simpa only [hk] using hm⟩
  obtain ⟨j,x,hxgood,hxpos⟩ := supported_positive_fiber_varying ρ E F
    (fun _ => volume) (fun _ => volume) (fun j => j.2.val.split.symm)
    S (fun j => j.2.val.measurableSet_maxLocus hK) A
    (fun j => j.2.val.differentiableOn_param_maxLocus K) (fun j => bad j.1)
    (fun j => hbad j.1) univ hρ hall
  have hxbase : x ∈ j.2.val.base := by
    by_contra hn
    apply hxpos
    have he : Prod.mk x ⁻¹' S j = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro k hk
      exact hn hk.1
    rw [he,measure_empty]
  exact ⟨j.1,j.2.val,x,hCB j.1 j.2.val j.2.property,hxbase,hxgood,hxpos⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PrimeZeroLocusFixed
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology
open scoped Classical

theorem prime_zeroLocus_fixed_charts {n : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) [J.IsPrime] :
    ∃ (d : ℕ) (Q : MvPolynomial (Fin n) ℂ), Q ∉ J ∧
      ∀ q ∈ MvPolynomial.zeroLocus ℂ J, MvPolynomial.eval q Q ≠ 0 →
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ J ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ J → Affine n) ⁻¹' W) ∧ q ∈ W ∧
          ∃ B : Set (Affine d), IsOpen B ∧ Nonempty (Biholomorph W B) := by
  obtain ⟨d,_,G,hG,hGi⟩ := exists_integral_inj_algHom_of_quotient J Ideal.IsPrime.ne_top'
  choose P hP using fun j : Fin d => Ideal.Quotient.mkₐ_surjective ℂ J (G (MvPolynomial.X j))
  obtain ⟨D,r,hD,_,hs⟩ := normalization_analytic_sheets J G hG hGi P hP
  let Q := MvPolynomial.bind₁ P D
  have hcomp : (Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.bind₁ P) = G := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa using hP j
  have hQ : Q ∉ J := by
    intro hQ
    have he : (Ideal.Quotient.mkₐ ℂ J) Q = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hQ
    change ((Ideal.Quotient.mkₐ ℂ J).comp (MvPolynomial.bind₁ P)) D = 0 at he
    rw [hcomp] at he
    exact hD (hG (he.trans (map_zero G).symm))
  refine ⟨d,Q,hQ,fun q hq hqQ => ?_⟩
  let π : Affine n → Affine d := fun z j => MvPolynomial.eval z (P j)
  have hπ : AnalyticOnNhd ℂ π univ :=
    AnalyticOnNhd.pi (fun j => AnalyticOnNhd.eval_mvPolynomial (P j))
  have hqD : MvPolynomial.eval (π q) D ≠ 0 := by
    convert! hqQ using 1
    all_goals try with_reducible_and_instances rfl
    exact (MvPolynomial.aeval_bind₁ q P D).symm
  obtain ⟨I,g,A,_,hA,hqa,hg,hsheets⟩ := hs (π q) hqD
  obtain ⟨W,hWV,hW,hqW,B,hB,hWB⟩ :=
    finite_analytic_sheets_chart _ π hπ hA g hg hsheets hq hqa
  exact ⟨W,hWV,hW,hqW,B,hB,hWB⟩

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_SemialgebraicPolynomialNonzero
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
attribute [-simp] _root_.OAI.Release061.Biholomorph.ambientAut_apply _root_.OAI.Release061.Biholomorph.ambientAut_iterate _root_.OAI.Release061.Biholomorph.ambientMap_apply _root_.OAI.Release061.Biholomorph.autTransport_apply _root_.OAI.Release061.Biholomorph.autTransport_inv _root_.OAI.Release061.Biholomorph.autTransport_mul _root_.OAI.Release061.Biholomorph.autTransport_one _root_.OAI.Release061.Biholomorph.autTransport_symm_cancel _root_.OAI.Release061.Biholomorph.complexGeneratorField_tmul _root_.OAI.Release061.Biholomorph.coordinateField_apply _root_.OAI.Release061.Biholomorph.derivativeAt_one _root_.OAI.Release061.Biholomorph.flatTangentialRotation_apply _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_of_not_mem _root_.OAI.Release061.Biholomorph.infinitesimalGenerator_one _root_.OAI.Release061.Biholomorph.inv_apply _root_.OAI.Release061.Biholomorph.linearAut_apply _root_.OAI.Release061.Biholomorph.linearAut_inv_apply _root_.OAI.Release061.Biholomorph.mapDerivativeEquiv_apply _root_.OAI.Release061.Biholomorph.mul_apply _root_.OAI.Release061.Biholomorph.one_apply _root_.OAI.Release061.Biholomorph.pushForwardGenerator_apply _root_.OAI.Release061.Biholomorph.translationAut_apply _root_.OAI.Release061.Biholomorph.translationAut_inv_apply _root_.OAI.Release061.Biholomorph.translationAut_zero _root_.OAI.Release061.Biholomorph.weightedScaleCLE_apply _root_.OAI.Release061.NashBoundaryChart.oldOffset_oldPosition _root_.OAI.Release061.NashBoundaryChart.oldParameter_oldPosition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

open Set
open scoped Classical

theorem complex_polynomial_real_syntax {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    ∃ A B : MvPolynomial (Fin n ⊕ Fin n) ℝ, ∀ z : Affine n,
      MvPolynomial.eval (realCoordinates z) A = (MvPolynomial.eval z P).re ∧
      MvPolynomial.eval (realCoordinates z) B = (MvPolynomial.eval z P).im := by
  induction P using MvPolynomial.induction_on with
  | C a => exact ⟨MvPolynomial.C a.re,MvPolynomial.C a.im,by simp⟩
  | add P Q hp hq =>
    obtain ⟨A,B,h⟩ := hp
    obtain ⟨C,D,k⟩ := hq
    exact ⟨A+C,B+D,by intro z; simp only [map_add,Complex.add_re,Complex.add_im,(h z).1,(h z).2,(k z).1,(k z).2]; trivial⟩
  | mul_X P j hp =>
    obtain ⟨A,B,h⟩ := hp
    refine ⟨A*MvPolynomial.X (.inl j)-B*MvPolynomial.X (.inr j),
      A*MvPolynomial.X (.inr j)+B*MvPolynomial.X (.inl j),?_⟩
    intro z
    simp only [map_sub,map_mul,map_add,MvPolynomial.eval_X,Complex.mul_re,Complex.mul_im]
    rw [(h z).1,(h z).2]
    exact ⟨rfl,by dsimp [realCoordinates]⟩

lemma isSemialgebraic_polynomial_zero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IsSemialgebraic {z : Affine n | MvPolynomial.eval z P = 0} := by
  obtain ⟨A,B,h⟩ := complex_polynomial_real_syntax P
  convert (IsSemialgebraic.zero A).inter (IsSemialgebraic.zero B) using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,(h z).1,(h z).2,Complex.ext_iff,Complex.zero_re,Complex.zero_im]

lemma isSemialgebraic_polynomial_nonzero {n : ℕ} (P : MvPolynomial (Fin n) ℂ) :
    IsSemialgebraic {z : Affine n | MvPolynomial.eval z P ≠ 0} :=
  (isSemialgebraic_polynomial_zero P).compl

end Release061

end

end OAI
end

section
-- module Solutions.OAIQ025_SD.SymmetricDomains_PrimeBoundaryGenericFiber
attribute [-instance] _root_.OAI.Complexification.ratLieAlgebra _root_.OAI.Release061.Biholomorph.automorphismGroup _root_.OAI.Release061.Biholomorph.automorphismInv _root_.OAI.Release061.Biholomorph.automorphismMetrizable _root_.OAI.Release061.Biholomorph.automorphismMul _root_.OAI.Release061.Biholomorph.automorphismOne _root_.OAI.Release061.Biholomorph.automorphismSecondCountable _root_.OAI.Release061.Biholomorph.automorphismTopologicalGroup _root_.OAI.Release061.Biholomorph.automorphismTopology
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set MeasureTheory
open scoped Classical

theorem finite_patch_exception_polynomial {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (Q : MvPolynomial (Fin n) ℂ) (hQ : Q ∉ I) (C : Finset (NashPatch (n+n)))
    (hC : ∀ p : C,
      (∃ R : MvPolynomial (Fin n) ℂ, R ∉ I ∧
        ∀ x ∈ p.val.domain, MvPolynomial.eval (p.val.complexMap x) R = 0) ∨
      volume {x | x ∈ p.val.domain ∧ p.val.complexRank x < m} = 0) :
    ∃ P : MvPolynomial (Fin n) ℂ, P ∉ I ∧
      (∀ z, MvPolynomial.eval z P ≠ 0 → MvPolynomial.eval z Q ≠ 0) ∧
      ∀ p : C, volume {x | x ∈ p.val.domain ∧ p.val.complexRank x < m ∧
        MvPolynomial.eval (p.val.complexMap x) P ≠ 0} = 0 := by
  have hchoose (p : C) : ∃ R : MvPolynomial (Fin n) ℂ, R ∉ I ∧
      (volume {x | x ∈ p.val.domain ∧ p.val.complexRank x < m} = 0 ∨
        ∀ x ∈ p.val.domain, MvPolynomial.eval (p.val.complexMap x) R = 0) := by
    rcases hC p with ⟨R,hR,hv⟩ | hn
    · exact ⟨R,hR,Or.inr hv⟩
    · exact ⟨1,Ideal.one_notMem I,Or.inl hn⟩
  choose R hRI hR using hchoose
  let P := Q * ∏ p : C, R p
  have hPn : P ∉ I := by
    intro hp
    rcases ((inferInstance : I.IsPrime).mul_mem_iff_mem_or_mem).mp hp with h | h
    · exact hQ h
    · obtain ⟨p,_,hp⟩ := Ideal.IsPrime.prod_mem_iff.mp h
      exact hRI p hp
  have hfactor (z : Affine n) (hz : MvPolynomial.eval z P ≠ 0) :
      MvPolynomial.eval z Q ≠ 0 ∧ ∀ p : C, MvPolynomial.eval z (R p) ≠ 0 := by
    have hh : MvPolynomial.eval z Q * ∏ p : C, MvPolynomial.eval z (R p) ≠ 0 := by
      simpa only [P,map_mul,map_prod] using hz
    exact ⟨(mul_ne_zero_iff.mp hh).1,fun p =>
      (Finset.prod_ne_zero_iff.mp (mul_ne_zero_iff.mp hh).2) p (Finset.mem_univ p)⟩
  refine ⟨P,hPn,fun z hz => (hfactor z hz).1,?_⟩
  intro p
  rcases hR p with hn | hv
  · exact measure_mono_null (t := {x | x ∈ p.val.domain ∧ p.val.complexRank x < m})
      (fun _ hx => ⟨hx.1,hx.2.1⟩) hn
  · have he : {x | x ∈ p.val.domain ∧ p.val.complexRank x < m ∧
        MvPolynomial.eval (p.val.complexMap x) P ≠ 0} = (∅ : Set (Fin p.val.dim → ℝ)) := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (hfactor _ hx.2.2).2 p (hv x hx.1)
    rw [he,measure_empty]

end

open Set Filter Topology MeasureTheory
open scoped Classical

theorem prime_boundary_generic_fiber_oai {n : ℕ} {U : Set (Affine n)}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) [I.IsPrime]
    (hI : I = MvPolynomial.vanishingIdeal ℂ U)
    (hU : IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' U))
    (hc : IsPreconnected U) (hn : ¬ U.Subsingleton) (hb : Bornology.IsBounded U)
    (hs : IsSemialgebraic U) :
    ∃ (m : ℕ) (P : MvPolynomial (Fin n) ℂ) (C : Finset (NashPatch (n+n))),
      (∃ u ∈ U, MvPolynomial.eval u P ≠ 0) ∧
      (∀ p ∈ C, 0 ∈ p.domain ∧ ∀ x ∈ p.domain,
        p.complexMap x ∈ closure U \ U ∧
        ∃ W : Set (Affine n), W ⊆ MvPolynomial.zeroLocus ℂ I ∧
          IsOpen ((Subtype.val : MvPolynomial.zeroLocus ℂ I → Affine n) ⁻¹' W) ∧ p.complexMap x ∈ W ∧
          ∃ B : Set (Affine m), IsOpen B ∧ Nonempty (Biholomorph W B)) ∧
      ∀ (bad : ∀ p : C, Set (Fin p.val.dim → ℝ)), (∀ p, volume (bad p) = 0) →
        ∃ p : C, ∃ (c : ActualCriticalChart P p.val.complexMap) (x : Fin p.val.dim → ℝ),
          x ∈ p.val.domain ∧ x ∈ c.base ∧ m ≤ p.val.complexRank x ∧
          MvPolynomial.eval (p.val.complexMap x) P ≠ 0 ∧ x ∉ bad p ∧
          volume (Prod.mk x ⁻¹' c.maxLocus (closure U)) ≠ 0 := by
  have hV : IsAffineAlgebraic (MvPolynomial.zeroLocus ℂ I) := ⟨I,rfl⟩
  have hUV : U ⊆ MvPolynomial.zeroLocus ℂ I := by
    rw [hI]
    exact MvPolynomial.zeroLocus_vanishingIdeal_le U
  have hcl : closure U ⊆ MvPolynomial.zeroLocus ℂ I := closure_minimal hUV hV.isClosed
  obtain ⟨m,Q,hQ,hcharts⟩ := prime_zeroLocus_fixed_charts I
  let S := (closure U \ U) ∩ {z : Affine n | MvPolynomial.eval z Q ≠ 0}
  have hS : IsSemialgebraic S := (hs.closure.diff hs).inter (isSemialgebraic_polynomial_nonzero Q)
  obtain ⟨C,h0,hC⟩ := isSemialgebraic_centered_nash_cover hS
  have hpS (p : C) {x : Fin p.val.dim → ℝ} (hx : x ∈ p.val.domain) : p.val.complexMap x ∈ S :=
    (hC _).mpr ⟨p.val,p.property,mem_image_of_mem _ hx⟩
  have hAlt (p : C) := p.val.principal_rank_dichotomy I Q hcharts (h0 _ p.property)
    (fun _ hx => hcl (hpS p hx).1.1) (fun _ hx => (hpS p hx).2)
  obtain ⟨P,hPI,hPQ,hbadRank⟩ := finite_patch_exception_polynomial I Q hQ C hAlt
  have hP : ∃ u ∈ U, MvPolynomial.eval u P ≠ 0 := by
    by_contra! hv
    apply hPI
    rw [hI]
    exact hv
  refine ⟨m,P,C,hP,?_,?_⟩
  · intro p hp
    refine ⟨h0 p hp,fun x hx => ?_⟩
    have hh := hpS ⟨p,hp⟩ hx
    exact ⟨hh.1,hcharts _ (hcl hh.1.1) hh.2⟩
  · intro bad hbad
    let B (p : C) : Set (Fin p.val.dim → ℝ) :=
      {x | x ∈ p.val.domain ∧ MvPolynomial.eval (p.val.complexMap x) P ≠ 0}
    have hBo (p : C) : IsOpen (B p) := by
      apply isOpen_iff_mem_nhds.mpr
      intro x hx
      exact inter_mem (p.val.isOpen_domain.mem_nhds hx.1)
        (((MvPolynomial.continuous_eval P).continuousAt.comp
          (p.val.analytic_complexMap x hx.1).continuousAt).eventually_ne hx.2)
    let E (p : C) : Set (Fin p.val.dim → ℝ) := bad p ∪
      {x | x ∈ p.val.domain ∧ p.val.complexRank x < m ∧ MvPolynomial.eval (p.val.complexMap x) P ≠ 0}
    have hE (p : C) : volume (E p) = 0 := measure_union_null (hbad p) (hbadRank p)
    have hcover (a : Affine n →L[ℂ] ℂ) :
        ∃ p : C, ∃ x, x ∈ B p ∧ IsMaxOn (parameterPotential P a) (closure U) (p.val.complexMap x) := by
      obtain ⟨z,hz,hzP,hm⟩ := exists_boundary_parameterPeak_maximizer hV hUV hU hc hn hb P hP a
      obtain ⟨p,hp,x,hx,rfl⟩ := (hC z).mp ⟨hz,hPQ z hzP⟩
      exact ⟨⟨p,hp⟩,x,⟨hx,hzP⟩,hm⟩
    obtain ⟨p,c,x,hcB,hxc,hxE,hpos⟩ := actual_positive_maximizer_fiber P (closure U) isClosed_closure
      (fun p : C => p.val.dim) B hBo (fun p => p.val.complexMap)
      (fun p x hx => (p.val.analytic_complexMap x hx.1).contDiffAt.contDiffWithinAt)
      (fun p _ hx => (hpS p hx.1).1.1) (fun _ _ hx => hx.2)
      (fun p _ hx => p.val.injective_fderiv_complexMap hx.1) E hE hcover
    have hxB := hcB hxc
    refine ⟨p,c,x,hxB.1,hxc,?_,hxB.2,?_,hpos⟩
    · apply Nat.le_of_not_gt
      intro hr
      exact hxE (Or.inr ⟨hxB.1,hr,hxB.2⟩)
    · exact fun hx => hxE (Or.inl hx)

end Release061

end

end OAI
end

theorem solution : type_of% @OAI.Release061.prime_boundary_generic_fiber_oai := @OAI.Release061.prime_boundary_generic_fiber_oai
