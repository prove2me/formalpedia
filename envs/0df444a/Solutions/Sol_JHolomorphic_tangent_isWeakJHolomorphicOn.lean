-- Prove2me | solution 1 for JHolomorphic.tangent_isWeakJHolomorphicOn
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T14:00:32.558551+00:00
-- url     : https://prove2.me/submissions/d7547034-c3b5-4ee9-8b81-08d0caed431f

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Theorems.Thm_JHolomorphic_exists_weakPartials_hasWeakPartialsOn
import Theorems.Thm_JHolomorphic_contDiffOn_of_hasWeakPartialsOn
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_integral_contDiff_one
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_congr_ae
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_ae_eq_mixed
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_prodMk
import Theorems.Thm_JHolomorphic_HasWeakPartialsOn_clm_apply
import Theorems.Thm_JHolomorphic_IntegrableOn_continuousOn_clm_apply



namespace JHolomorphic

open MeasureTheory Filter Topology
open scoped ContDiff

theorem tangent_isWeakJHolomorphicOn_aux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    IsJHolomorphicOn J U u ∧
      IsWeakJHolomorphicOn p
        (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
          ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
            (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
        (O ×ˢ Set.univ) U (fun z => (u z, fderiv ℝ u z 1)) := by
  obtain ⟨hcont, hmaps, us0, ut0, hw0, hLp0, hae0⟩ := hu
  obtain ⟨us, ut, uss, ust, uts, utt, h1, h2, h3, hLp⟩ :=
    exists_weakPartials_hasWeakPartialsOn p hp J O hJ U hU u
      ⟨hcont, hmaps, us0, ut0, hw0, hLp0, hae0⟩
  obtain ⟨hC1, hae⟩ :=
    contDiffOn_of_hasWeakPartialsOn p hp U hU u us ut uss ust uts utt hcont h1 h2 h3 hLp
  obtain ⟨hO, hJs, hJ2⟩ := hJ
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith)
  -- integrability and `L^p` on compact subsets
  have intK : ∀ f : ℂ → E, (∀ K ⊆ U, IsCompact K → MemLp f (ENNReal.ofReal p) (volume.restrict K)) →
      ∀ K ⊆ U, IsCompact K → IntegrableOn f K := by
    intro f hf K hKU hK
    haveI : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact (hf K hKU hK).integrable hp1
  have contK : ∀ f : ℂ → E, ContinuousOn f U → ∀ K ⊆ U, IsCompact K → IntegrableOn f K :=
    fun f hf K hKU hK => (hf.mono hKU).integrableOn_compact hK
  have memLpK : ∀ f : ℂ → E, ContinuousOn f U →
      ∀ K ⊆ U, IsCompact K → MemLp f (ENNReal.ofReal p) (volume.restrict K) := by
    intro f hf K hKU hK
    haveI : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKU)
    exact (memLp_top_of_bound ((hf.mono hKU).aestronglyMeasurable hK.measurableSet) C
      ((ae_restrict_iff' hK.measurableSet).mpr (ae_of_all _ hC))).mono_exponent le_top
  -- classical partials
  set Us : ℂ → E := fun z => fderiv ℝ u z 1 with hUs
  set Ut : ℂ → E := fun z => fderiv ℝ u z Complex.I with hUt
  have hDu : ContinuousOn (fderiv ℝ u) U := hC1.continuousOn_fderiv_of_isOpen hU le_rfl
  have hUsc : ContinuousOn Us U := hDu.clm_apply continuousOn_const
  have hUtc : ContinuousOn Ut U := hDu.clm_apply continuousOn_const
  have hJu : ContinuousOn (fun z => J (u z)) U := hJs.continuousOn.comp hcont hmaps
  have hus : ∀ᵐ z ∂(volume.restrict U), us z = Us z := hae.mono fun z hz => hz.1.symm
  have hut : ∀ᵐ z ∂(volume.restrict U), ut z = Ut z := hae.mono fun z hz => hz.2.symm
  -- the weak partials of `u`, `uₛ`, `uₜ` in classical form
  have h1' : HasWeakPartialsOn U u Us Ut := h1.congr_ae hU (ae_of_all _ fun _ => rfl) hus hut
  have h2' : HasWeakPartialsOn U Us uss ust :=
    h2.congr_ae hU hus (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
  have h3' : HasWeakPartialsOn U Ut uts utt :=
    h3.congr_ae hU hut (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
  have iuss := intK uss fun K hKU hK => (hLp K hKU hK).2.2.1
  have iust := intK ust fun K hKU hK => (hLp K hKU hK).2.2.2.1
  have iuts := intK uts fun K hKU hK => (hLp K hKU hK).2.2.2.2.1
  have iutt := intK utt fun K hKU hK => (hLp K hKU hK).2.2.2.2.2
  -- the equation everywhere on `U`
  have hu0 := HasWeakPartialsOn.ae_eq hU hw0 h1' fun K hKU hK =>
    ⟨intK us0 (fun K hKU hK => (hLp0 K hKU hK).2.1) K hKU hK,
      intK ut0 (fun K hKU hK => (hLp0 K hKU hK).2.2) K hKU hK,
      contK Us hUsc K hKU hK, contK Ut hUtc K hKU hK⟩
  have hEq : Set.EqOn (fun z => Us z + J (u z) (Ut z)) (fun _ => 0) U := by
    refine Measure.eqOn_open_of_ae_eq (μ := volume) ?_ hU (hUsc.add (hJu.clm_apply hUtc)) continuousOn_const
    filter_upwards [hae0, hu0] with z hz hz'
    rw [← hz'.1, ← hz'.2]; exact hz
  have hhol : IsJHolomorphicOn J U u := fun z hz =>
    ⟨(hC1.differentiableOn one_ne_zero z hz).differentiableAt (hU.mem_nhds hz), hEq hz⟩
  refine ⟨hhol, hcont.prodMk hUsc, fun z hz => ⟨hmaps hz, trivial⟩,
    fun z => (Us z, uss z), fun z => (Ut z, ust z), ?_, ?_, ?_⟩
  · exact HasWeakPartialsOn.prodMk h1' h2' fun K hKU hK =>
      ⟨contK u hcont K hKU hK, contK Us hUsc K hKU hK, contK Ut hUtc K hKU hK,
        contK Us hUsc K hKU hK, iuss K hKU hK, iust K hKU hK⟩
  · intro K hKU hK
    refine ⟨memLp_prod_iff.mpr ⟨memLpK u hcont K hKU hK, memLpK Us hUsc K hKU hK⟩,
      memLp_prod_iff.mpr ⟨memLpK Us hUsc K hKU hK, (hLp K hKU hK).2.2.1⟩,
      memLp_prod_iff.mpr ⟨memLpK Ut hUtc K hKU hK, (hLp K hKU hK).2.2.2.1⟩⟩
  · -- the second component, from the weak Leibniz rule for `uₜ = J(u) uₛ`
    have hA : ContDiffOn ℝ 1 (fun z => J (u z)) U :=
      (hJs.of_le (by exact_mod_cast le_top)).comp hC1 hmaps
    have hL := HasWeakPartialsOn.clm_apply hU hA h2' fun K hKU hK =>
      ⟨contK Us hUsc K hKU hK, iuss K hKU hK, iust K hKU hK⟩
    have hUtJ : ∀ z ∈ U, J (u z) (Us z) = Ut z := by
      intro z hz
      have h0 := hEq hz
      have hJJ := congrArg (fun L => L (Ut z)) (hJ2 (u z) (hmaps hz))
      simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
        ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] at hJJ h0
      rw [eq_neg_of_add_eq_zero_left h0, map_neg, hJJ, neg_neg]
    have hL' : HasWeakPartialsOn U Ut
        (fun z => fderiv ℝ (fun z => J (u z)) z 1 (Us z) + J (u z) (uss z))
        (fun z => fderiv ℝ (fun z => J (u z)) z Complex.I (Us z) + J (u z) (ust z)) :=
      hL.congr_ae hU ((ae_restrict_iff' hU.measurableSet).mpr (ae_of_all _ hUtJ))
        (ae_of_all _ fun _ => rfl) (ae_of_all _ fun _ => rfl)
    have hdA : ContinuousOn (fun z => fderiv ℝ (fun z => J (u z)) z 1) U :=
      (hA.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
    have hts := HasWeakPartialsOn.ae_eq hU h3' hL' fun K hKU hK =>
      ⟨iuts K hKU hK, iutt K hKU hK,
        (contK _ (hdA.clm_apply hUsc) K hKU hK).add
          (IntegrableOn.continuousOn_clm_apply hK (hJu.mono hKU) (iuss K hKU hK)),
        (contK _ (((hA.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply
          continuousOn_const).clm_apply hUsc) K hKU hK).add
          (IntegrableOn.continuousOn_clm_apply hK (hJu.mono hKU) (iust K hKU hK))⟩
    have hmix := HasWeakPartialsOn.ae_eq_mixed hU h1' h2' h3' fun K hKU hK =>
      ⟨iust K hKU hK, iuts K hKU hK⟩
    rw [ae_restrict_iff' hU.measurableSet] at hts hmix ⊢
    filter_upwards [hts, hmix] with z hz hz' hzU
    have hx : u z ∈ O := hmaps hzU
    -- the chain rule for `J ∘ u`
    have hdJ : DifferentiableAt ℝ J (u z) :=
      (hJs.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hx)
    have hdu : DifferentiableAt ℝ u z :=
      (hC1.differentiableOn one_ne_zero z hzU).differentiableAt (hU.mem_nhds hzU)
    have hch : fderiv ℝ (fun z => J (u z)) z 1 = fderiv ℝ J (u z) (Us z) := by
      rw [show (fun z => J (u z)) = J ∘ u from rfl, fderiv_comp z hdJ hdu]
      rfl
    -- `DJ(x)[y]` anticommutes with `J(x)`
    have hev : (fun y => (J y).comp (J y)) =ᶠ[𝓝 (u z)] fun _ => -ContinuousLinearMap.id ℝ E :=
      Filter.eventually_of_mem (hO.mem_nhds hx) hJ2
    have hD : fderiv ℝ (fun y => (J y).comp (J y)) (u z) = 0 := by
      rw [hev.fderiv_eq]; simp
    rw [fderiv_clm_comp hdJ hdJ] at hD
    have hDy := congrArg (fun L => L (Us z) (Us z)) hD
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.zero_apply] at hDy
    have hJJ := congrArg (fun L => L (uss z)) (hJ2 (u z) hx)
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply] at hJJ
    have hst : ust z = fderiv ℝ J (u z) (Us z) (Us z) + J (u z) (uss z) := by
      rw [hz' hzU, (hz hzU).1, hch]
    refine Prod.ext (by simpa using hEq hzU) ?_
    simp only [Prod.snd_add, Prod.snd_zero, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    rw [hst, map_add, hJJ, ← hUtJ z hzU]
    have h' : ∀ a b c : E, a + (b + -a + c) = b + c := fun a b c => by abel
    rw [h']
    exact hDy

end JHolomorphic

open JHolomorphic

open MeasureTheory
open scoped ContDiff

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 2 < p)
    (J : E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U)
    (u : ℂ → E) (hu : IsWeakJHolomorphicOn p J O U u) :
    IsJHolomorphicOn J U u ∧
      IsWeakJHolomorphicOn p
        (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
          ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
            (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
        (O ×ˢ Set.univ) U (fun z => (u z, fderiv ℝ u z 1)) :=
  tangent_isWeakJHolomorphicOn_aux p hp J O hJ U hU u hu
