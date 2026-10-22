-- Prove2me | solution 1 for JHolomorphic.isAlmostComplexOn_tangent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T12:03:27.974514+00:00
-- url     : https://prove2.me/submissions/1821b016-2412-49b2-9c85-8ec1d1cb7912

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Tactic.LinearCombination



namespace JHolomorphic

open scoped ContDiff

/-- The tangent almost complex structure `J^T(x, y)(a, b) = (J(x) a, J(x) b + DJ(x)[y] a)` on
`O × E` is almost complex. -/
theorem isAlmostComplexOn_tangent_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) :
    IsAlmostComplexOn
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (O ×ˢ Set.univ) := by
  obtain ⟨hO, hJs, hJ2⟩ := hJ
  have hmap : Set.MapsTo (fun x : E × E => x.1) (O ×ˢ Set.univ) O := fun x hx => hx.1
  have hA : ContDiffOn ℝ ∞ (fun x : E × E => J x.1) (O ×ˢ Set.univ) :=
    hJs.comp contDiffOn_fst hmap
  have hDJ : ContDiffOn ℝ ∞ (fderiv ℝ J) O := hJs.fderiv_of_isOpen hO (by simp)
  have hB : ContDiffOn ℝ ∞ (fun x : E × E => fderiv ℝ J x.1 x.2) (O ×ˢ Set.univ) :=
    (hDJ.comp contDiffOn_fst hmap).clm_apply contDiffOn_snd
  refine ⟨hO.prod isOpen_univ, ?_, ?_⟩
  · have h1 := hA.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ E E))
    have h2 := (hA.clm_comp (contDiffOn_const (c := ContinuousLinearMap.snd ℝ E E))).add
      (hB.clm_comp (contDiffOn_const (c := ContinuousLinearMap.fst ℝ E E)))
    have h3 := (h1.prodMk h2)
    have h4 := ((ContinuousLinearMap.prodL ℝ :
      ((E × E →L[ℝ] E) × (E × E →L[ℝ] E)) ≃L[ℝ] (E × E →L[ℝ] E × E))
      ).toContinuousLinearMap.contDiff.comp_contDiffOn h3
    exact h4
  · rintro ⟨x, y⟩ ⟨hx, -⟩
    -- `D(J ∘ J)(x) = 0` since `J ∘ J = -1` near `x`
    have hdiff : DifferentiableAt ℝ J x :=
      (hJs.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    have hev : (fun z => (J z).comp (J z)) =ᶠ[nhds x] fun _ => -ContinuousLinearMap.id ℝ E :=
      Filter.eventually_of_mem (hO.mem_nhds hx) hJ2
    have hD : fderiv ℝ (fun z => (J z).comp (J z)) x = 0 := by
      rw [hev.fderiv_eq]; simp
    rw [fderiv_clm_comp hdiff hdiff] at hD
    have hDy := congrArg (fun L => L y) hD
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply] at hDy
    refine ContinuousLinearMap.ext fun ab => ?_
    obtain ⟨a, b⟩ := ab
    refine Prod.ext ?_ ?_
    · have hJx := congrArg (fun L => L a) (hJ2 x hx)
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply] at hJx
      simp [hJx]
    · have hJb := congrArg (fun L => L b) (hJ2 x hx)
      have hJa := congrArg (fun L => L a) hDy
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.zero_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.id_apply] at hJb hJa
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.prod_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Prod.snd_neg]
      rw [map_add, hJb, add_assoc, hJa, add_zero]

end JHolomorphic

open JHolomorphic

open MeasureTheory
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) :
    IsAlmostComplexOn
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (O ×ˢ Set.univ) :=
  JHolomorphic.isAlmostComplexOn_tangent_aux J O hJ
