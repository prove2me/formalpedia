-- Prove2me | solution 1 for OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization_s01
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:12:17.936202+00:00
-- url     : https://prove2.me/submissions/fc3e4448-70bc-4b52-b3e7-ab33c89fd7ce

import Mathlib
import Definitions.Def_Q223SES008

section
-- module Solutions.Q223_SES.Compat
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : c) :
    dite c a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_PolynomialCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
open scoped BigOperators
variable {𝕜 ι E : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

lemma polynomialDifferential_C (L : ι → E →L[𝕜] 𝕜) (c : 𝕜) (x : E) :
    polynomialDifferential L (C c) x = 0 := by
  ext v
  simp [polynomialDifferential]

lemma polynomialDifferential_add (L : ι → E →L[𝕜] 𝕜) (p q : MvPolynomial ι 𝕜) (x : E) :
    polynomialDifferential L (p + q) x =
      polynomialDifferential L p x + polynomialDifferential L q x := by
  ext v
  simp [polynomialDifferential, add_mul, Finset.sum_add_distrib]

lemma polynomialDifferential_mul (L : ι → E →L[𝕜] 𝕜) (p q : MvPolynomial ι 𝕜) (x : E) :
    polynomialDifferential L (p * q) x =
      eval (fun i => L i x) p • polynomialDifferential L q x +
        eval (fun i => L i x) q • polynomialDifferential L p x := by
  ext v
  simp [polynomialDifferential, Derivation.leibniz, smul_eq_mul, add_mul, mul_assoc,
    Finset.sum_add_distrib, Finset.mul_sum]

lemma polynomialDifferential_X (L : ι → E →L[𝕜] 𝕜) (i : ι) (x : E) :
    polynomialDifferential L (X i) x = L i := by
  classical
  ext v
  simp [polynomialDifferential, pderiv_X, Pi.single_apply, apply_ite, ite_apply]

theorem hasFDerivAt_polynomialEval (L : ι → E →L[𝕜] 𝕜) (p : MvPolynomial ι 𝕜) (x : E) :
    HasFDerivAt (fun y => eval (fun i => L i y) p) (polynomialDifferential L p x) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa [polynomialDifferential_C] using hasFDerivAt_const (𝕜 := 𝕜) c x
  | add p q hp hq =>
      simpa [polynomialDifferential_add, Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa [polynomialDifferential_mul, polynomialDifferential_X, Pi.mul_def] using
        hp.mul ((L i).hasFDerivAt (x := x))

theorem analyticAt_polynomial_eval (p : MvPolynomial ι 𝕜) (x : ι → 𝕜) :
    AnalyticAt 𝕜 (fun y => eval y p) x := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa using analyticAt_const (𝕜 := 𝕜) (E := ι → 𝕜) (v := c) (x := x)
  | add p q hp hq => simpa [Pi.add_def] using hp.add hq
  | mul_X p i hp =>
      simpa [Pi.mul_def] using hp.mul ((ContinuousLinearMap.proj (R := 𝕜) i).analyticAt x)

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped BigOperators Matrix ContDiff
open MvPolynomial
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

omit [DecidableEq σ] in
lemma augmentedPolynomial_hasFDerivAt (P : Algebra.SubmersivePresentation F S ι σ)
    (x : ι → F) : HasFDerivAt (augmentedPolynomial P) (augmentedDerivative P x) x := by
  have h₁ := (hasFDerivAt_pi.mpr fun i : σ =>
    hasFDerivAt_polynomialEval (fun a : ι => ContinuousLinearMap.proj (R := F) a)
      (P.relation i) x)
  have h₂ : HasFDerivAt (fun y : ι → F => fun i : {i : ι // i ∉ Set.range P.map} => y i.val)
      (ContinuousLinearMap.pi fun i : {i : ι // i ∉ Set.range P.map} =>
        ContinuousLinearMap.proj (R := F) i.val) x :=
    hasFDerivAt_pi.mpr fun i => (ContinuousLinearMap.proj (R := F) i.val).hasFDerivAt (x := x)
  apply (h₁.prodMk h₂).congr_fderiv
  ext v
  all_goals simp [augmentedDerivative, augmentedLinear, polynomialDifferential,
    Matrix.mulVec, dotProduct]

omit [DecidableEq σ] in
lemma augmentedPolynomial_analyticAt (P : Algebra.SubmersivePresentation F S ι σ)
    (x : ι → F) : AnalyticAt F (augmentedPolynomial P) x := by
  exact (AnalyticAt.pi fun i => analyticAt_polynomial_eval (P.relation i) x).prod
    (AnalyticAt.pi fun i => (ContinuousLinearMap.proj (R := F) i.val).analyticAt x)

theorem exists_analytic_augmented_inverse
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ ψ : ((σ → F) × ({i : ι // i ∉ Set.range P.map} → F)) → (ι → F),
      ψ (augmentedPolynomial P (fun a => ρ (P.val a))) = (fun a => ρ (P.val a)) ∧
      AnalyticAt F ψ (augmentedPolynomial P (fun a => ρ (P.val a))) ∧
      ∀ᶠ y in nhds (augmentedPolynomial P (fun a => ρ (P.val a))),
        augmentedPolynomial P (ψ y) = y := by
  let x : ι → F := fun a => ρ (P.val a)
  let f := augmentedPolynomial P
  let e' := augmentedDerivativeEquiv P ρ
  have hd : HasFDerivAt f (e' : (ι → F) →L[F] _) x := by
    convert! augmentedPolynomial_hasFDerivAt P x using 1
    all_goals try with_reducible_and_instances rfl
  have hc : ContDiffAt F ω f x := (augmentedPolynomial_analyticAt P x).contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let e := hc.toOpenPartialHomeomorph f hd hn
  let ψ := hc.localInverse hd hn
  refine ⟨ψ, hc.localInverse_apply_image hd hn, (hc.to_localInverse hd hn).analyticAt, ?_⟩
  have hm : f x ∈ e.target := hc.image_mem_toOpenPartialHomeomorph_target hd hn
  filter_upwards [e.open_target.mem_nhds hm] with y hy
  exact e.right_inv hy

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Analytic_PointCharts
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.jetIndexFinite _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
section
namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open MvPolynomial
variable {F S ι σ : Type*} [CommRing F] [CommRing S] [Algebra F S]

lemma presentationPoint_apply (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (s : S) :
    presentationPoint P x hx s = eval x (P.σ s) := by
  simp [presentationPoint]

lemma presentationPoint_aeval (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (f : MvPolynomial ι F) :
    presentationPoint P x hx (aeval P.val f) = eval x f := by
  have he : (P.quotientEquiv.restrictScalars F).symm (aeval P.val f) =
      Ideal.Quotient.mk P.ker f := by
    apply (P.quotientEquiv.restrictScalars F).injective
    simp
  simp only [presentationPoint, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [he]
  simp

lemma presentationPoint_val (P : Algebra.Presentation F S ι σ)
    (x : ι → F) (hx : ∀ i, eval x (P.relation i) = 0) (i : ι) :
    presentationPoint P x hx (P.val i) = x i := by
  simpa using presentationPoint_aeval P x hx (X i)

lemma presentationPoint_at_point (P : Algebra.Presentation F S ι σ) (ρ : S →ₐ[F] F) :
    presentationPoint P (fun a => ρ (P.val a)) (evaluation_relations P ρ) = ρ := by
  ext s
  obtain ⟨f, rfl⟩ := P.aeval_val_surjective s
  rw [presentationPoint_aeval]
  change aeval (fun a => ρ (P.val a)) f = _
  rw [← MvPolynomial.comp_aeval]
  rfl

end

noncomputable section
open MvPolynomial
open scoped BigOperators Matrix ContDiff
variable {F ι σ S : Type*} [RCLike F] [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra F S]

theorem exists_analytic_zero_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ γ : ({i : ι // i ∉ Set.range P.map} → F) → (ι → F),
      γ (fun i => ρ (P.val i.val)) = (fun a => ρ (P.val a)) ∧
      AnalyticAt F γ (fun i => ρ (P.val i.val)) ∧
      ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
        (∀ i, eval (γ z) (P.relation i) = 0) ∧ (∀ i, γ z i.val = z i) := by
  obtain ⟨ψ, hbase, han, hinv⟩ := exists_analytic_augmented_inverse P ρ
  have he : augmentedPolynomial P (fun a => ρ (P.val a)) =
      (0, fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)) := by
    ext a
    · exact evaluation_relations P.toPresentation ρ a
    · rfl
  rw [he] at hbase han hinv
  let γ : ({i : ι // i ∉ Set.range P.map} → F) → (ι → F) := fun z => ψ (0, z)
  have hz : AnalyticAt F (fun z : ({i : ι // i ∉ Set.range P.map} → F) =>
      ((0 : σ → F), z)) (fun i => ρ (P.val i.val)) :=
    analyticAt_const.prod analyticAt_id
  refine ⟨γ, hbase, han.comp hz, ?_⟩
  filter_upwards [hz.continuousAt.eventually hinv] with z hz'
  constructor
  · intro i
    exact congrArg (fun y => y.1 i) hz'
  · intro i
    exact congrArg (fun y => y.2 i) hz'

theorem exists_analytic_point_chart
    (P : Algebra.SubmersivePresentation F S ι σ) (ρ : S →ₐ[F] F) :
    ∃ q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F),
      q (fun i => ρ (P.val i.val)) = ρ ∧
      (∀ s : S, AnalyticAt F (fun z => q z s) (fun i => ρ (P.val i.val))) ∧
      ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
        ∀ i, q z (P.val i.val) = z i := by
  classical
  obtain ⟨γ, hbase, han, hrel⟩ := exists_analytic_zero_chart P ρ
  let q : ({i : ι // i ∉ Set.range P.map} → F) → (S →ₐ[F] F) := fun z =>
    if h : ∀ i, eval (γ z) (P.relation i) = 0 then
      presentationPoint P.toPresentation (γ z) h else ρ
  have heq : ∀ᶠ z in nhds (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i.val)),
      ∀ s, q z s = eval (γ z) (P.σ s) := by
    filter_upwards [hrel] with z hz
    intro s
    simp only [q, dite_eq_left hz.1]
    exact presentationPoint_apply P.toPresentation (γ z) hz.1 s
  refine ⟨q, ?_, ?_, ?_⟩
  · have hzero : ∀ i, eval (γ (fun i => ρ (P.val i.val))) (P.relation i) = 0 := by
      rw [hbase]
      exact evaluation_relations P.toPresentation ρ
    simp only [q, dite_eq_left hzero]
    simpa only [hbase] using presentationPoint_at_point P.toPresentation ρ
  · intro s
    have h := (analyticAt_polynomial_eval (P.σ s) _).comp han
    apply h.congr
    filter_upwards [heq] with z hz
    exact (hz s).symm
  · filter_upwards [hrel] with z hz
    intro i
    simp only [q, dite_eq_left hz.1]
    rw [presentationPoint_val]
    exact hz.2 i

end
end MaximalSeshadri.AlgebraicJets

namespace MaximalSeshadri.AlgebraicJets
noncomputable section
open scoped Topology ContDiff
open MvPolynomial
variable {ι σ S : Type*} [Fintype ι] [Fintype σ]
  [DecidableEq ι] [DecidableEq σ] [CommRing S] [Algebra ℂ S]

theorem exists_binary_point_chart
    (P : Algebra.SubmersivePresentation ℂ S ι σ)
    (e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2) (ρ : S →ₐ[ℂ] ℂ) :
    ∃ q : (ℂ × ℂ) → (S →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : S, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q z (P.val (e.symm i)) = ρ (P.val (e.symm i)) +
          (if i = 0 then z.2 else z.1) := by
  obtain ⟨q₀, hbase, han, hc⟩ := exists_analytic_point_chart P ρ
  let α (z : ℂ × ℂ) (i : {i : ι // i ∉ Set.range P.map}) :=
    ρ (P.val i) + (if e i = 0 then z.2 else z.1)
  have hα : AnalyticAt ℂ α 0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.add analyticAt_const
    by_cases h : e i = 0
    · simpa only [ite_eq_left h] using (analyticAt_snd (𝕜 := ℂ) (p := (0 : ℂ × ℂ)))
    · simpa only [ite_eq_right h] using (analyticAt_fst (𝕜 := ℂ) (p := (0 : ℂ × ℂ)))
  have hα₀ : α 0 = (fun i : {i : ι // i ∉ Set.range P.map} => ρ (P.val i)) := by
    ext i
    simp [α]
  refine ⟨fun z => q₀ (α z), ?_, ?_, ?_⟩
  · change q₀ (α 0) = ρ
    rw [hα₀, hbase]
  · intro s
    have h : AnalyticAt ℂ (fun z => q₀ z s) (α 0) := by
      rw [hα₀]
      exact han s
    exact h.comp hα
  · have hcp : ∀ᶠ z in 𝓝 (α 0), ∀ i, q₀ z (P.val i.val) = z i := by
      rw [hα₀]
      exact hc
    have hpull := hα.continuousAt.eventually hcp
    filter_upwards [hpull] with z hz
    intro i
    simpa [α] using hz (e.symm i)

end
end MaximalSeshadri.AlgebraicJets


end
end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_LocalQuadratic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                        
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial IsLocalRing

attribute [local instance] RingHom.ker_isPrime

lemma pair_square_eq (A : Type*) [CommRing A] (x y : A) :
    (Ideal.span ({x,y} : Set A)) ^ 2 = Ideal.span ({x^2,x*y,y^2} : Set A) := by
  rw [pow_two, Ideal.span_pair_mul_span_pair]
  congr 1
  ext t
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, pow_two, mul_comm y x]
  tauto

lemma mem_pair_square {A : Type*} [CommRing A] (x y f : A)
    (hf : f ∈ (Ideal.span ({x,y} : Set A)) ^ 2) :
    ∃ a b c : A, f = a*x^2 + b*x*y + c*y^2 := by
  rw [pair_square_eq, Ideal.mem_span_insert] at hf
  obtain ⟨a, g, hg, hfg⟩ := hf
  obtain ⟨b,c,hg⟩ := Ideal.mem_span_pair.mp hg
  refine ⟨a,b,c,?_⟩
  rw [← hg] at hfg
  simpa only [mul_add, add_assoc, mul_assoc] using hfg

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]
  [Algebra (MvPolynomial (Fin 2) K) A] [IsScalarTower K (MvPolynomial (Fin 2) K) A]

theorem etale_coordinates_generate_local [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0) :
    maximalIdeal (Localization.AtPrime (RingHom.ker ρ)) = Ideal.span
      (Set.range fun i : Fin 2 => algebraMap A (Localization.AtPrime (RingHom.ker ρ))
        (algebraMap (MvPolynomial (Fin 2) K) A (X i))) := by
  let R := MvPolynomial (Fin 2) K
  let q := RingHom.ker ρ
  let p := q.under R
  have hp : p = idealOfVars (Fin 2) K := by
    rw [MaximalSeshadri.AlgebraicJets.idealOfVars_eq_ker_constantCoeff]
    change RingHom.ker (ρ.toRingHom.comp (algebraMap R A)) = _
    have heq : ρ.toRingHom.comp (algebraMap R A) = constantCoeff := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp only [RingHom.comp_apply, constantCoeff_C]
        change ρ (algebraMap R A (algebraMap K R c)) = c
        rw [← IsScalarTower.algebraMap_apply K R A]
        exact ρ.commutes c
      · intro i
        simp only [RingHom.comp_apply, constantCoeff_X]
        change ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0
        exact hρ i
    rw [heq]
  let Rp := Localization.AtPrime p
  let Aq := Localization.AtPrime q
  let : Algebra Rp Aq := Localization.AtPrime.algebraOfLiesOver p q
  let : Algebra.EssFiniteType Rp Aq := Algebra.EssFiniteType.of_comp R Rp Aq
  let : Algebra.FormallyEtale R Aq := Algebra.FormallyEtale.comp R A Aq
  let : Algebra.FormallyEtale Rp Aq := Algebra.FormallyEtale.of_restrictScalars (R := R)
  have hmax : (maximalIdeal Rp).map (algebraMap Rp Aq) = maximalIdeal Aq :=
    Algebra.FormallyUnramified.map_maximalIdeal
  rw [← hmax, ← IsLocalization.AtPrime.map_eq_maximalIdeal p Rp, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq R Rp Aq, hp, idealOfVars, Ideal.map_span]
  congr 1
  rw [← Set.range_comp]
  congr 1

theorem etale_quadratic_local [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0)
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) :
    let B := Localization.AtPrime (RingHom.ker ρ)
    let x := algebraMap A B (algebraMap (MvPolynomial (Fin 2) K) A (X 0))
    let y := algebraMap A B (algebraMap (MvPolynomial (Fin 2) K) A (X 1))
    ∃ a b c : B, algebraMap A B f = a*x^2 + b*x*y + c*y^2 := by
  dsimp only
  apply mem_pair_square
  have hm := etale_coordinates_generate_local ρ hρ
  have hr (g : Fin 2 → Localization.AtPrime (RingHom.ker ρ)) :
      Set.range g = {g 0,g 1} := by
    ext t
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  rw [hr] at hm
  rw [← hm, ← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ρ), ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hf

theorem etale_quadratic_neighborhood [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0)
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) :
    let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
    let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
    ∃ d a b c : A, ρ d ≠ 0 ∧ d*f = a*x^2 + b*x*y + c*y^2 := by
  dsimp only
  let B := Localization.AtPrime (RingHom.ker ρ)
  let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
  have hmem : algebraMap A B f ∈
      ((Ideal.span ({x,y} : Set A))^2).map (algebraMap A B) := by
    rw [Ideal.map_pow, Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [pair_square_eq, Ideal.mem_span_insert]
    obtain ⟨a,b,c,heq⟩ := etale_quadratic_local ρ hρ f hf
    refine ⟨a, b*(algebraMap A B x * algebraMap A B y) +
      c*(algebraMap A B y)^2, Ideal.mem_span_pair.mpr ⟨b,c,rfl⟩, ?_⟩
    simpa only [add_assoc, mul_assoc] using heq
  obtain ⟨d, hd, hdf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (RingHom.ker ρ).primeCompl B _ f).mp hmem
  obtain ⟨a,b,c,heq⟩ := mem_pair_square x y _ hdf
  exact ⟨d,a,b,c,hd,heq⟩

theorem etale_linear_neighborhood [Algebra.Etale (MvPolynomial (Fin 2) K) A]
    (ρ : A →ₐ[K] K)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) K) A (X i)) = 0)
    (f : A) (hf : ρ f = 0) :
    let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
    let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
    ∃ d a b : A, ρ d ≠ 0 ∧ d*f = a*x + b*y := by
  let B := Localization.AtPrime (RingHom.ker ρ)
  let x := algebraMap (MvPolynomial (Fin 2) K) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) K) A (X 1)
  have heq : (Ideal.span ({x,y} : Set A)).map (algebraMap A B) = maximalIdeal B := by
    rw [etale_coordinates_generate_local ρ hρ, Ideal.map_span]
    simp only [Set.image_insert_eq, Set.image_singleton]
    congr 1
    ext t
    simp only [Set.mem_range, Fin.exists_fin_two, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hmem : algebraMap A B f ∈ (Ideal.span ({x,y} : Set A)).map (algebraMap A B) := by
    rw [heq, ← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker ρ)]
    exact Ideal.mem_map_of_mem _ hf
  obtain ⟨d,hd,hdf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (RingHom.ker ρ).primeCompl B _ f).mp hmem
  obtain ⟨a,b,heq⟩ := Ideal.mem_span_pair.mp hdf
  exact ⟨d,a,b,hd,heq.symm⟩

end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_EtaleAnalytic
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section

open MvPolynomial
open scoped Topology ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem etale_tangent_separates
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq₀ : q 0 = ρ)
    (hq : ∀ s : A, AnalyticAt ℂ (fun z => q z s) 0)
    (v : ℂ × ℂ)
    (hv : ∀ i : Fin 2, fderiv ℂ (fun z => q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i))) 0 v = 0) :
    ∀ s : A, fderiv ℂ (fun z => q z s) 0 v = 0 := by
  intro s
  let x := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)
  let f := s - algebraMap ℂ A (ρ s)
  have hf : ρ f = 0 := by simp [f]
  obtain ⟨d,a,b,hd,heq⟩ := etale_linear_neighborhood ρ hρ f hf
  have hfun : (fun z => q z d * (q z s - ρ s)) =
      (fun z => q z a * q z x + q z b * q z y) := by
    funext z
    have h := congrArg (q z) heq
    simpa [f, x, y] using h
  have hD := (hq d).differentiableAt.hasFDerivAt.mul
    ((hq s).differentiableAt.hasFDerivAt.sub_const (ρ s))
  change HasFDerivAt (fun z => q z d * (q z s - ρ s)) _ _ at hD
  rw [hfun] at hD
  have hE := ((hq a).differentiableAt.hasFDerivAt.mul
    (hq x).differentiableAt.hasFDerivAt).add
    ((hq b).differentiableAt.hasFDerivAt.mul (hq y).differentiableAt.hasFDerivAt)
  have hh := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L v) (hD.unique hE)
  simp only [hq₀, hρ 0, hρ 1, x, y, sub_self, add_zero,
    add_apply, smul_apply, smul_eq_mul,
    hv 0, hv 1, mul_zero, zero_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left hd

theorem etale_coordinates_analytic_inverse
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq₀ : q 0 = ρ)
    (hq : ∀ s : A, AnalyticAt ℂ (fun z => q z s) 0)
    (u w : A)
    (hu : ∀ᶠ z in 𝓝 0, q z u = ρ u + z.1)
    (hw : ∀ᶠ z in 𝓝 0, q z w = ρ w + z.2) :
    ∃ ψ : (ℂ × ℂ) → (ℂ × ℂ), ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧
      (∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q (ψ z) (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
          if i = 0 then z.2 else z.1) ∧
      (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt ψ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
      ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn ψ V := by
  let F : (ℂ × ℂ) → (ℂ × ℂ) := fun z =>
    (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0)))
  have hF₀ : F 0 = 0 := by simp [F, hq₀, hρ]
  have hF : AnalyticAt ℂ F 0 := (hq _).prod (hq _)
  have hinj : Function.Injective (fderiv ℂ F 0) := by
    change Function.Injective (fderiv ℂ F 0).toLinearMap
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hder := ((hq (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1))).differentiableAt.hasFDerivAt).prodMk
      ((hq (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))).differentiableAt.hasFDerivAt)
    have hder' := hder.fderiv
    change fderiv ℂ F 0 = _ at hder'
    rw [hder'] at hv
    have hc : ∀ i : Fin 2, fderiv ℂ (fun z => q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i))) 0 v = 0 := by
      intro i
      fin_cases i
      · exact congrArg Prod.snd hv
      · exact congrArg Prod.fst hv
    have hs := etale_tangent_separates ρ hρ q hq₀ hq v hc
    have hdu : HasFDerivAt (fun z => q z u) (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
      exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.const_add (ρ u)).congr_of_eventuallyEq hu
    have hdw : HasFDerivAt (fun z => q z w) (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
      exact ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.const_add (ρ w)).congr_of_eventuallyEq hw
    apply Prod.ext
    · change (ContinuousLinearMap.fst ℂ ℂ ℂ) v = 0
      rw [← hdu.fderiv]
      exact hs u
    · change (ContinuousLinearMap.snd ℂ ℂ ℂ) v = 0
      rw [← hdw.fderiv]
      exact hs w
  have hbij : Function.Bijective (fderiv ℂ F 0) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (fderiv ℂ F 0).toLinearMap)).mp hinj⟩
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ F 0).toLinearMap hbij).toContinuousLinearEquiv
  have hder : HasFDerivAt F (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := hF.differentiableAt.hasFDerivAt
  have hcont : ContDiffAt ℂ ω F 0 := hF.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let T := hcont.toOpenPartialHomeomorph F hder hn
  let ψ := hcont.localInverse hder hn
  have hψ₀ : ψ 0 = 0 := by simpa only [hF₀] using hcont.localInverse_apply_image hder hn
  have hψ : AnalyticAt ℂ ψ 0 := by simpa only [hF₀] using (hcont.to_localInverse hder hn).analyticAt
  have ht : (0 : ℂ × ℂ) ∈ T.target := by
    simpa only [hF₀] using hcont.image_mem_toOpenPartialHomeomorph_target hder hn
  have hright : ∀ᶠ z in 𝓝 0, F (ψ z) = z := by
    filter_upwards [T.open_target.mem_nhds ht] with z hz
    exact T.right_inv hz
  refine ⟨ψ,hψ₀,hψ,?_,⟨e.symm, ?_⟩,T.target,T.open_target,ht,T.symm.injOn⟩
  swap
  · have hderψ : HasFDerivAt F (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (ψ 0) := by
      simpa only [hψ₀] using hder
    have hc := hderψ.comp (0 : ℂ × ℂ) hψ.differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun z => F (ψ z)) (ContinuousLinearMap.id ℂ (ℂ × ℂ)) 0 :=
      (hasFDerivAt_id (0 : ℂ × ℂ)).congr_of_eventuallyEq hright
    have heq := hc.unique hi
    apply hψ.differentiableAt.hasFDerivAt.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    simpa using DFunLike.congr_fun heq v
  filter_upwards [T.open_target.mem_nhds ht] with z hz
  have heq := T.right_inv hz
  change F (ψ z) = z at heq
  intro i
  fin_cases i
  · simpa [F] using congrArg Prod.snd heq
  · simpa [F] using congrArg Prod.fst heq

end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Geometry_EtaleRealization
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                          
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets
open scoped Topology

lemma polynomial_binary_standardSmooth :
    Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) := by
  let b := KaehlerDifferential.mvPolynomialBasis ℂ (Fin 2)
  have : Algebra.IsStandardSmooth ℂ (MvPolynomial (Fin 2) ℂ) :=
    Algebra.IsStandardSmooth.of_basis_kaehlerDifferential b (by
      rintro _ ⟨i,rfl⟩
      exact ⟨X i, (KaehlerDifferential.mvPolynomialBasis_apply ℂ (Fin 2) i).symm⟩)
  rw [Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth]
  rw [rank_eq_card_basis b]
  simp

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem exists_etale_analytic_chart
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0) :
    ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
          if i = 0 then z.2 else z.1 := by
  classical
  have : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ (MvPolynomial (Fin 2) ℂ) :=
    polynomial_binary_standardSmooth
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 (MvPolynomial (Fin 2) ℂ) A :=
    Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp inferInstance
  have : Algebra.IsStandardSmoothOfRelativeDimension 2 ℂ A :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 2 0 ℂ (MvPolynomial (Fin 2) ℂ) A
  obtain ⟨ι,σ,hσ,hι,P,hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := 2) (R := ℂ) (S := A)
  let : Fintype ι := Fintype.ofFinite ι
  let : Fintype σ := Fintype.ofFinite σ
  have hcard : Fintype.card {i : ι // i ∉ Set.range P.map} = 2 := by
    rw [← hP]
    change Fintype.card ((Set.range P.map)ᶜ : Set ι) = P.dimension
    simp only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card,
      Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
  let e : {i : ι // i ∉ Set.range P.map} ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcard
  obtain ⟨q,hq₀,hq,hcoord⟩ := exists_binary_point_chart P e ρ
  have hu : ∀ᶠ z in 𝓝 0, q z (P.val (e.symm 1)) = ρ (P.val (e.symm 1)) + z.1 := by
    filter_upwards [hcoord] with z hz
    simpa using hz 1
  have hw : ∀ᶠ z in 𝓝 0, q z (P.val (e.symm 0)) = ρ (P.val (e.symm 0)) + z.2 := by
    filter_upwards [hcoord] with z hz
    simpa using hz 0
  obtain ⟨ψ,hψ₀,hψ,hψcoord,-,-⟩ :=
    etale_coordinates_analytic_inverse ρ hρ q hq₀ hq _ _ hu hw
  refine ⟨fun z => q (ψ z), by simp [hψ₀,hq₀], ?_, hψcoord⟩
  intro s
  exact (hq s).comp_of_eq hψ hψ₀
end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Jets_AnalyticNode
attribute [-instance] _root_.OAI.MaximalSeshadri.AlgebraicJets.rationalKer_isMaximal _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.Geometry.schemeHasExt _root_.OAI.MaximalSeshadri.Geometry.sheafHomModule _root_.OAI.MaximalSeshadri.Geometry.sheafLinear _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.MaximalSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.MaximalSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_additive _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_flasque _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_mono _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.MaximalSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeExact.map_mono _root_.OAI.MaximalSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.MaximalSeshadri.TildeExact.preservesHomology _root_.OAI.MaximalSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.MaximalSeshadri.TildeFlasque.tilde_injective_isFlasque
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                      
section

namespace MaximalSeshadri.AnalyticNode
noncomputable section

open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_square_root {f : E → ℂ} {p : E}
    (hf : AnalyticAt ℂ f p) (hfp : f p ≠ 0) :
    ∃ g : E → ℂ, AnalyticAt ℂ g p ∧ g p ≠ 0 ∧ ∀ z, (g z)^2 = f z := by
  have hsquare (w : ℂ) : w.sqrt^2 = w := by
    rw [Complex.sqrt, ← Complex.cpow_nat_mul]
    norm_num
  have hs : AnalyticAt ℂ Complex.sqrt 1 := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [Complex.isOpen_slitPlane.mem_nhds Complex.one_mem_slitPlane] with z hz
    exact Complex.differentiableAt_sqrt hz
  let g : E → ℂ := fun z => Complex.sqrt (f z / f p) * Complex.sqrt (f p)
  have heq (z : E) : (g z)^2 = f z := by
    simp only [g, mul_pow, hsquare]
    exact div_mul_cancel₀ _ hfp
  refine ⟨g, ?_, ?_, heq⟩
  · have hquot : AnalyticAt ℂ (fun z => f z / f p) p := hf.div_const
    have han : AnalyticAt ℂ Complex.sqrt (f p / f p) := by simpa [hfp] using hs
    have hcomp : AnalyticAt ℂ (fun z => Complex.sqrt (f z / f p)) p :=
      AnalyticAt.comp (g := Complex.sqrt) (f := fun z => f z / f p) han hquot
    exact hcomp.mul analyticAt_const
  · intro hz
    apply hfp
    rw [← heq p, hz, zero_pow (by decide)]

lemma exists_nonzero_shear (a b c : ℂ) (h : b^2 - 4*a*c ≠ 0) :
    ∃ t : ℂ, a + t*b + t^2*c ≠ 0 := by
  by_cases ha : a ≠ 0
  · exact ⟨0, by simpa using ha⟩
  have ha : a = 0 := not_ne_iff.mp ha
  have hb : b ≠ 0 := by
    intro hb
    simp [ha, hb] at h
  by_cases hbc : b+c ≠ 0
  · exact ⟨1, by simpa [ha] using hbc⟩
  refine ⟨-1, ?_⟩
  have hbc : b+c = 0 := not_ne_iff.mp hbc
  intro heq
  simp only [ha, zero_add, neg_mul, one_mul, neg_one_sq, one_mul] at heq
  apply hb
  linear_combination (hbc - heq) / 2

lemma nodeLinear_bijective (a b d : ℂ) (ha : a ≠ 0) (hd : d ≠ 0) :
    Function.Bijective (nodeLinear a b d) := by
  have hi : Function.Injective (nodeLinear a b d) := by
    change Function.Injective (nodeLinear a b d).toLinearMap
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    have h₁ := congrArg Prod.fst hz
    have h₂ := congrArg Prod.snd hz
    change 2*a*z.1+(b+d)*z.2 = 0 at h₁
    change 2*a*z.1+(b-d)*z.2 = 0 at h₂
    have hzz : 2*d*z.2 = 0 := by linear_combination h₁-h₂
    have hz₂ : z.2 = 0 := (mul_eq_zero.mp hzz).resolve_left (mul_ne_zero (by norm_num) hd)
    rw [hz₂, mul_zero, add_zero] at h₁
    have hz₁ : z.1 = 0 := (mul_eq_zero.mp h₁).resolve_left (mul_ne_zero (by norm_num) ha)
    exact Prod.ext hz₁ hz₂
  exact ⟨hi, (LinearMap.injective_iff_surjective (f := (nodeLinear a b d).toLinearMap)).mp hi⟩

theorem analytic_node_inverse
    (a b c : (ℂ × ℂ) → ℂ)
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hc : AnalyticAt ℂ c 0)
    (ha₀ : a 0 ≠ 0) (hdisc : (b 0)^2 - 4*a 0*c 0 ≠ 0) :
    ∃ (ψ : (ℂ × ℂ) → (ℂ × ℂ)) (u : (ℂ × ℂ) → ℂ),
      ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, a (ψ z)*(ψ z).1^2 + b (ψ z)*(ψ z).1*(ψ z).2 +
        c (ψ z)*(ψ z).2^2 = u z*z.1*z.2) ∧
      (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt ψ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
      ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn ψ V := by
  let Δ : (ℂ × ℂ) → ℂ := fun z => (b z)^2-4*a z*c z
  have hΔ : AnalyticAt ℂ Δ 0 := (hb.pow 2).sub ((analyticAt_const.mul ha).mul hc)
  obtain ⟨d, hd, hd₀, hd₂⟩ := analytic_square_root hΔ hdisc
  let H : (ℂ × ℂ) → (ℂ × ℂ) := fun z =>
    (2*a z*z.1+(b z+d z)*z.2, 2*a z*z.1+(b z-d z)*z.2)
  have hH₀ : H 0 = 0 := by simp [H]
  have hH : AnalyticAt ℂ H 0 := by
    exact (((analyticAt_const.mul ha).mul analyticAt_fst).add
      ((hb.add hd).mul analyticAt_snd)).prod
      (((analyticAt_const.mul ha).mul analyticAt_fst).add
        ((hb.sub hd).mul analyticAt_snd))
  have hder : HasFDerivAt H (nodeLinear (a 0) (b 0) (d 0)) 0 := by
    have hfst := ((hasFDerivAt_const (2 : ℂ) (0 : ℂ × ℂ)).mul
      ha.differentiableAt.hasFDerivAt).mul
      (ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt
    have hplus := (hb.differentiableAt.hasFDerivAt.add
      hd.differentiableAt.hasFDerivAt).mul (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt
    have hminus := (hb.differentiableAt.hasFDerivAt.sub
      hd.differentiableAt.hasFDerivAt).mul (ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt
    apply ((hfst.add hplus).prodMk (hfst.add hminus)).congr_fderiv
    ext <;> simp [nodeLinear]
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (nodeLinear (a 0) (b 0) (d 0)).toLinearMap
      (nodeLinear_bijective _ _ _ ha₀ hd₀)).toContinuousLinearEquiv
  have hder' : HasFDerivAt H (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := hder
  have hcont : ContDiffAt ℂ ω H 0 := hH.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let T := hcont.toOpenPartialHomeomorph H hder' hn
  let ψ := hcont.localInverse hder' hn
  have hψ₀ : ψ 0 = 0 := by
    simpa only [hH₀] using hcont.localInverse_apply_image hder' hn
  have hψ : AnalyticAt ℂ ψ 0 := by
    simpa only [hH₀] using (hcont.to_localInverse hder' hn).analyticAt
  have htarget : (0 : ℂ × ℂ) ∈ T.target := by
    simpa only [hH₀] using hcont.image_mem_toOpenPartialHomeomorph_target hder' hn
  have hright : ∀ᶠ z in 𝓝 0, H (ψ z) = z := by
    filter_upwards [T.open_target.mem_nhds htarget] with z hz
    exact T.right_inv hz
  let u : (ℂ × ℂ) → ℂ := fun z => (4*a (ψ z))⁻¹
  have haψ : AnalyticAt ℂ (fun z => a (ψ z)) 0 :=
    ha.comp_of_eq hψ hψ₀
  have hua : AnalyticAt ℂ u 0 := (analyticAt_const.mul haψ).inv (by simp [hψ₀, ha₀])
  refine ⟨ψ,u,hψ₀,hψ,hua,by simp [u,hψ₀,ha₀], ?_,
    ⟨e.symm, ?_⟩, T.target,T.open_target,htarget,T.symm.injOn⟩
  swap
  · have hderψ : HasFDerivAt H (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (ψ 0) := by
      simpa only [hψ₀] using hder'
    have hc := hderψ.comp (0 : ℂ × ℂ) hψ.differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun z => H (ψ z)) (ContinuousLinearMap.id ℂ (ℂ × ℂ)) 0 :=
      (hasFDerivAt_id (0 : ℂ × ℂ)).congr_of_eventuallyEq hright
    have heq := hc.unique hi
    apply hψ.differentiableAt.hasFDerivAt.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    simpa using DFunLike.congr_fun heq v
  have haneq : ∀ᶠ z in 𝓝 0, a (ψ z) ≠ 0 := haψ.continuousAt.eventually_ne
    (by simpa [hψ₀] using ha₀)
  filter_upwards [hright, haneq] with z hz haz
  have hprod : (H (ψ z)).1*(H (ψ z)).2 = 4*a (ψ z)*
      (a (ψ z)*(ψ z).1^2 + b (ψ z)*(ψ z).1*(ψ z).2 + c (ψ z)*(ψ z).2^2) := by
    have heq := hd₂ (ψ z)
    dsimp only [Δ] at heq
    dsimp only [H]
    linear_combination -(ψ z).2^2 * heq
  rw [hz] at hprod
  dsimp only [u]
  field_simp [haz]
  linear_combination -hprod

lemma shearLinear_apply (t : ℂ) (z : ℂ × ℂ) :
    shearLinear t z = (z.1, t*z.1+z.2) := rfl

lemma shearLinear_bijective (t : ℂ) : Function.Bijective (shearLinear t) := by
  constructor
  · intro z w h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change z.1 = w.1 at h₁
    change t*z.1+z.2 = t*w.1+w.2 at h₂
    exact Prod.ext h₁ (by rw [h₁] at h₂; exact add_left_cancel h₂)
  · intro z
    exact ⟨(z.1, z.2-t*z.1), by simp [shearLinear_apply]⟩

theorem analytic_node_normal_form
    (a b c : (ℂ × ℂ) → ℂ)
    (ha : AnalyticAt ℂ a 0) (hb : AnalyticAt ℂ b 0) (hc : AnalyticAt ℂ c 0)
    (hdisc : (b 0)^2 - 4*a 0*c 0 ≠ 0) :
    ∃ (ψ : (ℂ × ℂ) → (ℂ × ℂ)) (u : (ℂ × ℂ) → ℂ),
      ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
      (∀ᶠ z in 𝓝 0, a (ψ z)*(ψ z).1^2 + b (ψ z)*(ψ z).1*(ψ z).2 +
        c (ψ z)*(ψ z).2^2 = u z*z.1*z.2) ∧
      (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt ψ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
      ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn ψ V := by
  obtain ⟨t, ht⟩ := exists_nonzero_shear (a 0) (b 0) (c 0) hdisc
  let S : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (shearLinear t).toLinearMap
      (shearLinear_bijective t)).toContinuousLinearEquiv
  have hS (z : ℂ × ℂ) : S z = (z.1,t*z.1+z.2) := rfl
  let A : (ℂ × ℂ) → ℂ := fun z => a (S z)+t*b (S z)+t^2*c (S z)
  let B : (ℂ × ℂ) → ℂ := fun z => b (S z)+2*t*c (S z)
  let C : (ℂ × ℂ) → ℂ := fun z => c (S z)
  have hSA : AnalyticAt ℂ A 0 := by
    exact ((ha.comp_of_eq (S.analyticAt 0) (map_zero S)).add
      (analyticAt_const.mul (hb.comp_of_eq (S.analyticAt 0) (map_zero S)))).add
      (analyticAt_const.mul (hc.comp_of_eq (S.analyticAt 0) (map_zero S)))
  have hSB : AnalyticAt ℂ B 0 := by
    exact (hb.comp_of_eq (S.analyticAt 0) (map_zero S)).add
      (analyticAt_const.mul (hc.comp_of_eq (S.analyticAt 0) (map_zero S)))
  have hSC : AnalyticAt ℂ C 0 := hc.comp_of_eq (S.analyticAt 0) (map_zero S)
  have hA₀ : A 0 ≠ 0 := by simpa [A] using ht
  have hABC : (B 0)^2-4*A 0*C 0 ≠ 0 := by
    have heq : (B 0)^2-4*A 0*C 0 = (b 0)^2-4*a 0*c 0 := by simp [A,B,C] <;> ring
    rwa [heq]
  obtain ⟨ψ,u,hψ₀,hψ,hu,hu₀,heq,⟨e,he⟩,V,hV,hV₀,hinj⟩ :=
    analytic_node_inverse A B C hSA hSB hSC hA₀ hABC
  refine ⟨S ∘ ψ,u,by simp [hψ₀],(S.analyticAt (ψ 0)).comp hψ,hu,hu₀,?_,
    ⟨e.trans S, ?_⟩,V,hV,hV₀,?_⟩
  · filter_upwards [heq] with z hz
    convert hz using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Function.comp_apply,A,B,C,hS]
    ring
  · exact S.hasFDerivAt.comp 0 he
  · intro z hz w hw h
    exact hinj hz hw (S.injective h)

end
end MaximalSeshadri.AnalyticNode

end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_QuadraticDiscriminant
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                               
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets
variable {K A : Type} [Field K] [CommRing A] [Algebra K A]

lemma taylor_mul_square (ρ : A →ₐ[K] K) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ) (d f : A)
    (hf : f ∈ (RingHom.ker ρ)^2) : τ (d*f) = ρ d • τ f := by
  have hd : d - algebraMap K A (ρ d) ∈ RingHom.ker ρ := by
    simp only [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have hm : (d - algebraMap K A (ρ d))*f ∈ (RingHom.ker ρ)^3 := by
    rw [show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
    exact Ideal.mul_mem_mul hd hf
  have hz := hτ hm
  change τ ((d-algebraMap K A (ρ d))*f) = 0 at hz
  calc
    τ (d*f) = τ ((ρ d) • f) := by
      rw [Algebra.smul_def (ρ d) f]
      simpa only [sub_mul, map_sub, sub_eq_zero] using hz
    _ = _ := map_smul τ (ρ d) f

lemma discriminant_smul (c : K) (f : JetAlgebra (Fin 2) K 3) :
    discriminant (c • f) = c^2 * discriminant f := by
  simp only [discriminant, map_smul, smul_eq_mul]
  ring

lemma discriminant_quadratic (a b c : K) :
    discriminant (Ideal.Quotient.mk _
      (C a * (X 0 : MvPolynomial (Fin 2) K)^2 + C b * X 0 * X 1 + C c * (X 1 : MvPolynomial (Fin 2) K)^2)) =
      b^2 - 4*a*c := by
  have h20ne02 : exponent20 ≠ exponent02 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp [exponent20, exponent02] at this
  have h11ne20 : exponent11 ≠ exponent20 := by
    intro h
    have := DFunLike.congr_fun h 1
    simp [exponent11, exponent20] at this
  have h11ne02 : exponent11 ≠ exponent02 := by
    intro h
    have := DFunLike.congr_fun h 0
    simp [exponent11, exponent02] at this
  have hXX : (X 0 : MvPolynomial (Fin 2) K) * X 1 = monomial exponent11 1 := by
    rw [X, X, monomial_mul_monomial]
    simp [exponent11]
  let p : MvPolynomial (Fin 2) K := C a * X 0^2 + C b * X 0 * X 1 + C c * X 1^2
  change (p.coeff exponent11)^2 - 4*p.coeff exponent20*p.coeff exponent02 = _
  dsimp only [p]
  simp only [mul_assoc (C b), hXX, MvPolynomial.coeff_add,
    coeff_C_mul, coeff_X_pow, coeff_monomial]
  simp only [show Finsupp.single (0 : Fin 2) 2 = exponent20 from rfl,
    show Finsupp.single (1 : Fin 2) 2 = exponent02 from rfl]
  simp [h20ne02, h20ne02.symm, h11ne20, h11ne20.symm, h11ne02, h11ne02.symm]

theorem quadratic_coefficients_nondegenerate
    (ρ : A →ₐ[K] K) (τ : A →ₐ[K] JetAlgebra (Fin 2) K 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
    (x y f d a b c : A) (hx : ρ x = 0) (hy : ρ y = 0)
    (hxf : τ x = Ideal.Quotient.mk _ (X 0))
    (hyf : τ y = Ideal.Quotient.mk _ (X 1))
    (hf : f ∈ (RingHom.ker ρ)^2) (hd : ρ d ≠ 0)
    (hdf : d*f = a*x^2 + b*x*y + c*y^2)
    (hdisc : discriminant (τ f) ≠ 0) :
    (ρ b)^2 - 4*ρ a*ρ c ≠ 0 := by
  have hxx : x^2 ∈ (RingHom.ker ρ)^2 := by
    rw [pow_two, pow_two]
    exact Ideal.mul_mem_mul hx hx
  have hxy : x*y ∈ (RingHom.ker ρ)^2 := by
    rw [pow_two]
    exact Ideal.mul_mem_mul hx hy
  have hyy : y^2 ∈ (RingHom.ker ρ)^2 := by
    rw [pow_two, pow_two]
    exact Ideal.mul_mem_mul hy hy
  have heq := congrArg τ hdf
  rw [taylor_mul_square ρ τ hτ d f hf, map_add, map_add,
    taylor_mul_square ρ τ hτ a (x^2) hxx, mul_assoc b x y,
    taylor_mul_square ρ τ hτ b (x*y) hxy, taylor_mul_square ρ τ hτ c (y^2) hyy,
    map_pow, map_pow, map_mul, hxf, hyf] at heq
  have heq' : ρ d • τ f = Ideal.Quotient.mk _
      (C (ρ a)*(X 0 : MvPolynomial (Fin 2) K)^2 + C (ρ b)*X 0*X 1 + C (ρ c)*X 1^2) := by
    have hq (k : K) (p : MvPolynomial (Fin 2) K) :
        k • Ideal.Quotient.mk ((idealOfVars (Fin 2) K)^3) p =
        Ideal.Quotient.mk _ (C k * p) := by
      change k • (Ideal.Quotient.mkₐ K ((idealOfVars (Fin 2) K)^3)) p =
        (Ideal.Quotient.mkₐ K ((idealOfVars (Fin 2) K)^3)) (C k * p)
      rw [← MvPolynomial.smul_eq_C_mul]
      exact (map_smul (Ideal.Quotient.mkₐ K ((idealOfVars (Fin 2) K)^3)) k p).symm
    rw [heq]
    simp only [← map_pow, ← map_mul, hq, ← map_add, mul_assoc]
  have hdsc := congrArg discriminant heq'
  rw [discriminant_smul, discriminant_quadratic] at hdsc
  rw [← hdsc]
  exact mul_ne_zero (pow_ne_zero _ hd) hdisc

end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
end

section
-- module Solutions.Q223_SES.Seshadri_Nodal_EtaleNode
attribute [-instance] _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesEpis _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.MaximalSeshadri.ClosedPushforward.preservesHomology _root_.OAI.MaximalSeshadri.Geometry.complexUncountable _root_.OAI.MaximalSeshadri.Geometry.opensMap_final _root_.OAI.MaximalSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.MaximalSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.MaximalSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.MaximalSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.MaximalSeshadri.ReesGrading.polynomial_isReduced
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticNode
open scoped Topology ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem etale_ordinary_node_realization_s01_oai
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (τ : A →ₐ[ℂ] JetAlgebra (Fin 2) ℂ 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
      Ideal.Quotient.mk _ (X i))
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) (hdisc : discriminant (τ f) ≠ 0) :
    ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
        (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt
          (fun z => (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
            q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))))
          (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
        ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  let x := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)
  obtain ⟨d,a,b,c,hd,hdf⟩ := etale_quadratic_neighborhood ρ hρ f hf
  have hΔ : (ρ b)^2-4*ρ a*ρ c ≠ 0 :=
    quadratic_coefficients_nondegenerate ρ τ hτ x y f d a b c
      (hρ 0) (hρ 1) (hcoord 0) (hcoord 1) hf hd hdf hdisc
  obtain ⟨q,hq₀,hq,hqc⟩ := exists_etale_analytic_chart ρ hρ
  have hΔ' : (q 0 b)^2-4*q 0 c*q 0 a ≠ 0 := by
    rw [hq₀]
    convert hΔ using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨ψ,u,hψ₀,hψ,hu,hu₀,heq,⟨e,he⟩,V,hV,hV₀,hinj⟩ :=
    analytic_node_normal_form (fun z => q z c) (fun z => q z b) (fun z => q z a)
      (hq c) (hq b) (hq a) hΔ'
  have hqd : AnalyticAt ℂ (fun z => q (ψ z) d) 0 := (hq d).comp_of_eq hψ hψ₀
  have hqd₀ : q (ψ 0) d ≠ 0 := by simpa [hψ₀,hq₀] using hd
  have hqdne : ∀ᶠ z in 𝓝 0, q (ψ z) d ≠ 0 := hqd.continuousAt.eventually_ne hqd₀
  have hqcψ : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q (ψ z) (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
        if i = 0 then (ψ z).2 else (ψ z).1 := by
    have hh : ∀ᶠ z in 𝓝 (ψ 0), ∀ i : Fin 2,
        q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
          if i = 0 then z.2 else z.1 := by simpa only [hψ₀] using hqc
    exact hψ.continuousAt.eventually hh
  have hpair : (fun z => (q (ψ z) y,q (ψ z) x)) =ᶠ[𝓝 0] ψ := by
    filter_upwards [hqcψ] with z hz
    exact Prod.ext (by simpa [y] using hz 1) (by simpa [x] using hz 0)
  obtain ⟨W,hW,hWo,hW₀⟩ := eventually_nhds_iff.mp hpair
  refine ⟨fun z => q (ψ z), by simp [hψ₀,hq₀], ?_,
    (fun z => u z / q (ψ z) d), hu.div hqd hqd₀,
    div_ne_zero hu₀ hqd₀, ?_, ⟨e,he.congr_of_eventuallyEq hpair⟩,
    V ∩ W,hV.inter hWo,⟨hV₀,hW₀⟩,?_⟩
  · intro s
    exact (hq s).comp_of_eq hψ hψ₀
  · filter_upwards [hqcψ,heq,hqdne] with z hz hze hdne
    have h := congrArg (q (ψ z)) hdf
    simp only [map_mul,map_add,map_pow] at h
    change q (ψ z) d * q (ψ z) f =
      q (ψ z) a*(q (ψ z) x)^2 + q (ψ z) b*q (ψ z) x*q (ψ z) y +
        q (ψ z) c*(q (ψ z) y)^2 at h
    rw [show q (ψ z) x = (ψ z).2 by simpa [x] using hz 0,
      show q (ψ z) y = (ψ z).1 by simpa [y] using hz 1] at h
    field_simp [hdne]
    linear_combination h + hze
  · intro z hz w hw heqw
    apply hinj hz.1 hw.1
    rw [← hW z hz.2, ← hW w hw.2]
    exact congrArg (fun r : A →ₐ[ℂ] ℂ => (r y,r x)) heqw
end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
end

theorem solution : type_of% @OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization_s01_oai := @OAI.MaximalSeshadri.QuadraticJets.etale_ordinary_node_realization_s01_oai
