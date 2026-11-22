-- Prove2me | solution 1 for NestedSA.NASA.theorem_2_a
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:51:35.202091+00:00
-- url     : https://prove2.me/submissions/1ad7e68f-27c5-41e9-841e-2458807ede24

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic
import Definitions.Def_NestedSA_NASA_Model
import Theorems.Thm_NestedSA_NASA_lemma_2
import Theorems.Thm_NestedSA_NASA_lemma_4
import Theorems.Thm_NestedSA_NASA_eq_3_21

open MeasureTheory ProbabilityTheory
open NestedSA.NASA
open scoped RealInnerProductSpace ENNReal

/-! ### Section 1: Elementary deterministic helpers -/

private lemma nasa_proj_cont {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) : Continuous P := by
  have hvi : ∀ w, ∀ y ∈ X, ⟪w - P w, y - P w⟫ ≤ 0 := by
    intro w
    have hmem := (hP w).1
    have hne : Nonempty X := ⟨⟨P w, hmem⟩⟩
    have hbdd : BddBelow (Set.range fun y : X => ‖w - (y : EuclideanSpace ℝ (Fin n))‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨y, rfl⟩
      exact norm_nonneg _
    have heq : ‖w - P w‖ = ⨅ y : X, ‖w - (y : EuclideanSpace ℝ (Fin n))‖ := by
      apply le_antisymm
      · exact le_ciInf (fun y => (hP w).2 y y.2)
      · exact ciInf_le hbdd (⟨P w, hmem⟩ : X)
    exact (norm_eq_iInf_iff_real_inner_le_zero hX_cvx hmem).1 heq
  have hlip : ∀ w w', ‖P w - P w'‖ ≤ ‖w - w'‖ := by
    intro w w'
    have h1 := hvi w (P w') (hP w').1
    have h2 := hvi w' (P w) (hP w).1
    have h3 : ‖P w - P w'‖ ^ 2 ≤ ⟪w - w', P w - P w'⟫ := by
      have e : ⟪w - w', P w - P w'⟫ - ‖P w - P w'‖ ^ 2 =
          -⟪w - P w, P w' - P w⟫ - ⟪w' - P w', P w - P w'⟫ := by
        rw [← real_inner_self_eq_norm_sq]
        simp only [inner_sub_left, inner_sub_right, real_inner_comm]
        ring
      linarith
    have h4 : ⟪w - w', P w - P w'⟫ ≤ ‖w - w'‖ * ‖P w - P w'‖ := real_inner_le_norm _ _
    rcases eq_or_lt_of_le (norm_nonneg (P w - P w')) with h | h
    · rw [← h]; exact norm_nonneg _
    · nlinarith
  apply LipschitzWith.continuous (K := 1)
  apply LipschitzWith.of_dist_le_mul
  intro w w'
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_one, one_mul]
  exact hlip w w'

private lemma nasa_gradF_cont {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) : Continuous (gradF f g) := by
  have hF : ContDiff ℝ 1 (fun y => f (g y)) := hf.comp hg
  have hc := hF.continuous_fderiv (by norm_num)
  unfold gradF
  have : (fun x => gradient (fun y => f (g y)) x) =
      fun x => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
        (fderiv ℝ (fun y => f (g y)) x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.comp hc

private lemma nasa_gradf_cont {m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (hf : ContDiff ℝ 1 f) : Continuous (gradient f) := by
  have hc := hf.continuous_fderiv (by norm_num)
  have : gradient f =
      fun u => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm (fderiv ℝ f u) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.continuous.comp hc

private lemma nasa_fderivg_bound {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (Lf Lg Ldf Ldg : ℝ)
    (hA2 : Assumption2 f g Lf Lg Ldf Ldg) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ g x‖ ≤ Lg := by
  have hlip : LipschitzWith ⟨Lg, hA2.Lg_nonneg⟩ g := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_eq_norm, dist_eq_norm]
    exact hA2.lip_g y z
  exact norm_fderiv_le_of_lipschitz ℝ hlip

private lemma nasa_gradF_eq_adjoint {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (x : EuclideanSpace ℝ (Fin n)) :
    gradF f g x = (ContinuousLinearMap.adjoint (fderiv ℝ g x)) (gradient f (g x)) := by
  have hfd : DifferentiableAt ℝ f (g x) := (hf.differentiable (by norm_num)) (g x)
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by norm_num)) x
  apply ext_inner_right ℝ
  intro v
  rw [gradF, gradient, InnerProductSpace.toDual_symm_apply,
    fderiv_fun_comp x hfd hgd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, gradient, InnerProductSpace.toDual_symm_apply]

private lemma nasa_norm_d_le {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n))
    (β : ℝ) (hβ : 0 < β) :
    ‖ybar P x z β - x‖ ≤ ‖z‖ / β := by
  have h321 := eq_3_21 X hX_cl hX_cvx P hP x hx z β hβ
  have hcs : -⟪z, ybar P x z β - x⟫ ≤ ‖z‖ * ‖ybar P x z β - x‖ := by
    have := real_inner_le_norm (-z) (ybar P x z β - x)
    rw [inner_neg_left, norm_neg] at this
    exact this
  have hle : β * ‖ybar P x z β - x‖ ^ 2 ≤ ‖z‖ * ‖ybar P x z β - x‖ := by linarith
  rw [le_div_iff₀ hβ]
  rcases eq_or_lt_of_le (norm_nonneg (ybar P x z β - x)) with hd | hd
  · rw [← hd, zero_mul]; exact norm_nonneg z
  · nlinarith

private lemma nasa_sq_norm_convex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(1 - t) • u + t • v‖ ^ 2 ≤ (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 := by
  have hexp : (1 - t) * ‖u‖ ^ 2 + t * ‖v‖ ^ 2 - ‖(1 - t) • u + t • v‖ ^ 2 =
      t * (1 - t) * ‖u - v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq ((1 - t) • u + t • v), ← real_inner_self_eq_norm_sq (u - v),
      ← real_inner_self_eq_norm_sq u, ← real_inner_self_eq_norm_sq v]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_comm v u]
    ring
  have hnn : 0 ≤ t * (1 - t) * ‖u - v‖ ^ 2 := by
    have : 0 ≤ 1 - t := by linarith
    positivity
  linarith

private lemma nasa_sq_norm_add_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have hpar : ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (u + v), ← real_inner_self_eq_norm_sq (u - v),
      ← real_inner_self_eq_norm_sq u, ← real_inner_self_eq_norm_sq v]
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      real_inner_comm v u]
    ring
  have := sq_nonneg ‖u - v‖
  linarith

private lemma nasa_sq_norm_sub_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have := nasa_sq_norm_add_le u (-v)
  rw [norm_neg, ← sub_eq_add_neg] at this
  exact this

/-! ### Section 2: Polymorphic adjoint measurability, conditional independence & expectation helpers -/

private noncomputable def nasaAdjCLM {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] :
    (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).toLinearIsometry.toContinuousLinearMap

private lemma nasaAdjCLM_apply {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (w : F) :
    nasaAdjCLM L w = (ContinuousLinearMap.adjoint L) w := rfl

private lemma nasa_stronglyMeasurable_adjoint_apply {n m : ℕ} {Ω : Type*} {m' : MeasurableSpace Ω}
    {A : Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))}
    {w : Ω → EuclideanSpace ℝ (Fin m)}
    (hA : StronglyMeasurable[m'] A) (hw : StronglyMeasurable[m'] w) :
    StronglyMeasurable[m'] (fun ω => (ContinuousLinearMap.adjoint (A ω)) (w ω)) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have heq : (fun ω => (ContinuousLinearMap.adjoint (A ω)) (w ω)) =
      ∑ i : Fin n, (fun ω => ⟪A ω (b i), w ω⟫ • b i) := by
    funext ω
    rw [Finset.sum_apply, ← b.sum_repr' ((ContinuousLinearMap.adjoint (A ω)) (w ω))]
    congr 1
    funext i
    rw [ContinuousLinearMap.adjoint_inner_right]
  rw [heq]
  refine Finset.stronglyMeasurable_sum Finset.univ fun i _ => ?_
  have h1 : StronglyMeasurable[m'] (fun ω => A ω (b i)) :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin m)) (b i)).continuous.comp_stronglyMeasurable hA
  have h2 : StronglyMeasurable[m'] (fun ω => ⟪A ω (b i), w ω⟫) := h1.inner hw
  exact (continuous_id.smul continuous_const).comp_stronglyMeasurable h2

private lemma nasa_condIndep_ae_indep {Ω E F : Type*} {m' : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [SecondCountableTopology F]
    [MeasurableSpace F] [BorelSpace F]
    {X X' : Ω → E} {Y Y' : Ω → F}
    (hX'm : Measurable X') (hY'm : Measurable Y')
    (hX_eq : X =ᵐ[μ] X') (hY_eq : Y =ᵐ[μ] Y')
    (hci : CondIndepFun m' hm' X Y μ) :
    ∀ᵐ ω ∂μ, IndepFun X' Y' (condExpKernel μ m' ω) := by
  have hX_ae : ∀ᵐ ω ∂(μ.trim hm'), X =ᵐ[condExpKernel μ m' ω] X' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rwa [condExpKernel_comp_trim hm']
  have hY_ae : ∀ᵐ ω ∂(μ.trim hm'), Y =ᵐ[condExpKernel μ m' ω] Y' := by
    refine Measure.ae_ae_of_ae_comp ?_
    rwa [condExpKernel_comp_trim hm']
  have hci' : Kernel.IndepFun X' Y' (condExpKernel μ m') (μ.trim hm') :=
    Kernel.IndepFun.congr' hci hX_ae hY_ae
  have hcp := (Kernel.indepFun_iff_compProd_map_prod_eq_compProd_prod_map_map hX'm hY'm).mp hci'
  have hae_trim : (condExpKernel μ m').map (fun y => (X' y, Y' y)) =ᵐ[μ.trim hm']
      (condExpKernel μ m').map X' ×ₖ (condExpKernel μ m').map Y' :=
    Kernel.ae_eq_of_compProd_eq hcp
  have hae : ∀ᵐ ω ∂μ, ((condExpKernel μ m').map (fun y => (X' y, Y' y))) ω =
      ((condExpKernel μ m').map X' ×ₖ (condExpKernel μ m').map Y') ω :=
    ae_of_ae_trim hm' hae_trim
  filter_upwards [hae] with ω hω
  rw [Kernel.map_apply _ (hX'm.prodMk hY'm), Kernel.prod_apply,
    Kernel.map_apply _ hX'm, Kernel.map_apply _ hY'm] at hω
  exact (indepFun_iff_map_prod_eq_prod_map_map hX'm.aemeasurable hY'm.aemeasurable).mpr hω

private lemma nasa_v_props_abstract {Ω E F : Type*} {m' : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology (E →L[ℝ] F)] [MeasurableSpace (E →L[ℝ] F)] [BorelSpace (E →L[ℝ] F)]
    {J : Ω → (E →L[ℝ] F)} {s : Ω → F}
    {Jbar : Ω → (E →L[ℝ] F)} {sbar : Ω → F} {σJ σs : ℝ}
    (hJ2 : MemLp J 2 μ) (hs2 : MemLp s 2 μ)
    (hci : CondIndepFun m' hm' s J μ)
    (hceJ : μ[J | m'] =ᵐ[μ] Jbar) (hces : μ[s | m'] =ᵐ[μ] sbar)
    (hJsq : μ[fun ω => ‖J ω‖ ^ 2 | m'] ≤ᵐ[μ] fun _ => σJ ^ 2)
    (hssq : μ[fun ω => ‖s ω‖ ^ 2 | m'] ≤ᵐ[μ] fun _ => σs ^ 2)
    (h_adj_sm : ∀ {A : Ω → (E →L[ℝ] F)} {w : Ω → F},
      StronglyMeasurable A → StronglyMeasurable w →
      StronglyMeasurable (fun ω => (ContinuousLinearMap.adjoint (A ω)) (w ω))) :
    MemLp (fun ω => (ContinuousLinearMap.adjoint (J ω)) (s ω)) 2 μ ∧
    ∫ ω, ‖(ContinuousLinearMap.adjoint (J ω)) (s ω)‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 ∧
    μ[fun ω => (ContinuousLinearMap.adjoint (J ω)) (s ω) | m'] =ᵐ[μ]
      fun ω => (ContinuousLinearMap.adjoint (Jbar ω)) (sbar ω) := by
  let v : Ω → E := fun ω => (ContinuousLinearMap.adjoint (J ω)) (s ω)
  have hs_asm := hs2.aestronglyMeasurable
  have hJ_asm := hJ2.aestronglyMeasurable
  obtain ⟨s', hs'_sm, hs_ae⟩ : ∃ s', StronglyMeasurable s' ∧ s =ᵐ[μ] s' :=
    ⟨hs_asm.mk s, hs_asm.stronglyMeasurable_mk, hs_asm.ae_eq_mk⟩
  obtain ⟨J', hJ'_sm, hJ_ae⟩ : ∃ J', StronglyMeasurable J' ∧ J =ᵐ[μ] J' :=
    ⟨hJ_asm.mk J, hJ_asm.stronglyMeasurable_mk, hJ_asm.ae_eq_mk⟩
  have hs'm : Measurable s' := hs'_sm.measurable
  have hJ'm : Measurable J' := hJ'_sm.measurable
  let v' : Ω → E := fun ω => (ContinuousLinearMap.adjoint (J' ω)) (s' ω)
  have hv'_sm : StronglyMeasurable v' := h_adj_sm hJ'_sm hs'_sm
  have hv_ae : v =ᵐ[μ] v' := by
    filter_upwards [hJ_ae, hs_ae] with ω hJω hsω
    simp only [v, v', hJω, hsω]
  have hv_asm : AEStronglyMeasurable v μ := hv'_sm.aestronglyMeasurable.congr hv_ae.symm
  have hind_ae : ∀ᵐ ω ∂μ, IndepFun J' s' (condExpKernel μ m' ω) := by
    filter_upwards [nasa_condIndep_ae_indep hm' μ hs'm hJ'm hs_ae hJ_ae hci] with ω hω
    exact hω.symm
  have hJ'_int : Integrable J' μ := (hJ2.integrable one_le_two).congr hJ_ae
  have hs'_int : Integrable s' μ := (hs2.integrable one_le_two).congr hs_ae
  have hJ'_sq_int : Integrable (fun y => ‖J' y‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hJ_asm).mp hJ2).congr (by filter_upwards [hJ_ae] with y hy; simp [hy])
  have hs'_sq_int : Integrable (fun y => ‖s' y‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hs_asm).mp hs2).congr (by filter_upwards [hs_ae] with y hy; simp [hy])
  have hJ'_k_int := hJ'_int.condExpKernel_ae (m := m')
  have hs'_k_int := hs'_int.condExpKernel_ae (m := m')
  have hJ'_sq_k_int := hJ'_sq_int.condExpKernel_ae (m := m')
  have hs'_sq_k_int := hs'_sq_int.condExpKernel_ae (m := m')
  have hce_J : (fun ω => ∫ y, J' y ∂condExpKernel μ m' ω) =ᵐ[μ] Jbar :=
    (condExp_ae_eq_integral_condExpKernel hm' hJ'_int).symm.trans
      ((condExp_congr_ae hJ_ae.symm).trans hceJ)
  have hce_s : (fun ω => ∫ y, s' y ∂condExpKernel μ m' ω) =ᵐ[μ] sbar :=
    (condExp_ae_eq_integral_condExpKernel hm' hs'_int).symm.trans
      ((condExp_congr_ae hs_ae.symm).trans hces)
  have hce_Jsq : (fun ω => ∫ y, ‖J' y‖ ^ 2 ∂condExpKernel μ m' ω) ≤ᵐ[μ] fun _ => σJ ^ 2 := by
    have h1 := condExp_ae_eq_integral_condExpKernel hm' hJ'_sq_int
    have h2 : μ[fun y => ‖J y‖ ^ 2 | m'] =ᵐ[μ] μ[fun y => ‖J' y‖ ^ 2 | m'] :=
      condExp_congr_ae (by filter_upwards [hJ_ae] with y hy; simp [hy])
    filter_upwards [h1, h2, hJsq] with ω h1ω h2ω h3ω
    rw [← h1ω, ← h2ω]; exact h3ω
  have hce_ssq : (fun ω => ∫ y, ‖s' y‖ ^ 2 ∂condExpKernel μ m' ω) ≤ᵐ[μ] fun _ => σs ^ 2 := by
    have h1 := condExp_ae_eq_integral_condExpKernel hm' hs'_sq_int
    have h2 : μ[fun y => ‖s y‖ ^ 2 | m'] =ᵐ[μ] μ[fun y => ‖s' y‖ ^ 2 | m'] :=
      condExp_congr_ae (by filter_upwards [hs_ae] with y hy; simp [hy])
    filter_upwards [h1, h2, hssq] with ω h1ω h2ω h3ω
    rw [← h1ω, ← h2ω]; exact h3ω
  have h_prod_ae : ∀ᵐ ω ∂μ,
      ∫⁻ y, ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) ∂condExpKernel μ m' ω ≤
        ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := by
    filter_upwards [hind_ae, hJ'_sq_k_int, hs'_sq_k_int, hce_Jsq, hce_ssq] with ω hω hJi hsi hJle hsle
    have hind_sq : IndepFun (fun y => ‖J' y‖ ^ 2) (fun y => ‖s' y‖ ^ 2) (condExpKernel μ m' ω) :=
      hω.comp (measurable_norm.pow_const 2) (measurable_norm.pow_const 2)
    have hprod_int : Integrable (fun y => ‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) (condExpKernel μ m' ω) :=
      hind_sq.integrable_mul hJi hsi
    have hprod_eq : ∫ y, ‖J' y‖ ^ 2 * ‖s' y‖ ^ 2 ∂condExpKernel μ m' ω =
        (∫ y, ‖J' y‖ ^ 2 ∂condExpKernel μ m' ω) * (∫ y, ‖s' y‖ ^ 2 ∂condExpKernel μ m' ω) :=
      hind_sq.integral_fun_mul_eq_mul_integral hJi.aestronglyMeasurable hsi.aestronglyMeasurable
    have h_ofReal : ∫⁻ y, ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) ∂condExpKernel μ m' ω =
        ENNReal.ofReal (∫ y, ‖J' y‖ ^ 2 * ‖s' y‖ ^ 2 ∂condExpKernel μ m' ω) :=
      (ofReal_integral_eq_lintegral_ofReal hprod_int (ae_of_all _ (fun y => by positivity))).symm
    rw [h_ofReal, hprod_eq]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul hJle hsle (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _)
  have h_lint_prod : ∫⁻ y, ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) ∂μ ≤
      ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := by
    have hmeas : Measurable (fun y => ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((hJ'm.norm.pow_const 2).mul (hs'm.norm.pow_const 2))
    have hbind : ∫⁻ y, ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) ∂μ =
        ∫⁻ ω, (∫⁻ y, ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) ∂condExpKernel μ m' ω) ∂(μ.trim hm') := by
      conv_lhs => rw [← condExpKernel_comp_trim (μ := μ) hm']
      exact Measure.lintegral_bind (Kernel.aemeasurable _) hmeas.aemeasurable
    rw [hbind, lintegral_trim hm' hmeas.lintegral_kernel]
    calc ∫⁻ ω, ∫⁻ y, ENNReal.ofReal (‖J' y‖ ^ 2 * ‖s' y‖ ^ 2) ∂condExpKernel μ m' ω ∂μ
        ≤ ∫⁻ _, ENNReal.ofReal (σJ ^ 2 * σs ^ 2) ∂μ := lintegral_mono_ae h_prod_ae
      _ = ENNReal.ofReal (σJ ^ 2 * σs ^ 2) := by simp
  have hv'_norm_le : ∀ y, ‖v' y‖ ^ 2 ≤ ‖J' y‖ ^ 2 * ‖s' y‖ ^ 2 := by
    intro y
    have h1 : ‖v' y‖ ≤ ‖J' y‖ * ‖s' y‖ := by
      calc ‖v' y‖ = ‖(ContinuousLinearMap.adjoint (J' y)) (s' y)‖ := rfl
        _ ≤ ‖ContinuousLinearMap.adjoint (J' y)‖ * ‖s' y‖ := ContinuousLinearMap.le_opNorm _ _
        _ = ‖J' y‖ * ‖s' y‖ := by rw [LinearIsometryEquiv.norm_map]
    calc ‖v' y‖ ^ 2 ≤ (‖J' y‖ * ‖s' y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖J' y‖ ^ 2 * ‖s' y‖ ^ 2 := mul_pow _ _ 2
  have hv'_sq_lint : ∫⁻ y, ENNReal.ofReal (‖v' y‖ ^ 2) ∂μ ≤ ENNReal.ofReal (σJ ^ 2 * σs ^ 2) :=
    (lintegral_mono (fun y => ENNReal.ofReal_le_ofReal (hv'_norm_le y))).trans h_lint_prod
  have hv'_sq_int : Integrable (fun y => ‖v' y‖ ^ 2) μ := by
    refine ⟨(hv'_sm.norm.pow 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun y => sq_nonneg ‖v' y‖))]
    exact lt_of_le_of_lt hv'_sq_lint ENNReal.ofReal_lt_top
  have hv_sq_int : Integrable (fun y => ‖v y‖ ^ 2) μ :=
    hv'_sq_int.congr (by filter_upwards [hv_ae] with y hy; simp [hy])
  have hv_memLp : MemLp v 2 μ := (memLp_two_iff_integrable_sq_norm hv_asm).mpr hv_sq_int
  have hv_sq_bound : ∫ y, ‖v y‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := by
    have heq : ∫ y, ‖v y‖ ^ 2 ∂μ = ∫ y, ‖v' y‖ ^ 2 ∂μ :=
      integral_congr_ae (by filter_upwards [hv_ae] with y hy; simp [hy])
    rw [heq, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      ofReal_integral_eq_lintegral_ofReal hv'_sq_int (ae_of_all _ (fun y => sq_nonneg _))]
    exact hv'_sq_lint
  have hv_ce : μ[v | m'] =ᵐ[μ] fun ω => (ContinuousLinearMap.adjoint (Jbar ω)) (sbar ω) := by
    have hv'_int : Integrable v' μ := (hv_memLp.integrable one_le_two).congr hv_ae
    have h1 : μ[v | m'] =ᵐ[μ] fun ω => ∫ y, v' y ∂condExpKernel μ m' ω :=
      (condExp_congr_ae hv_ae).trans (condExp_ae_eq_integral_condExpKernel hm' hv'_int)
    refine h1.trans ?_
    filter_upwards [hind_ae, hJ'_k_int, hs'_k_int, hce_J, hce_s] with ω hω hJi hsi hJeq hseq
    have hbilin : ∫ y, (nasaAdjCLM (E := E) (F := F)) (J' y) (s' y) ∂condExpKernel μ m' ω =
        (nasaAdjCLM (E := E) (F := F)) (∫ y, J' y ∂condExpKernel μ m' ω)
          (∫ y, s' y ∂condExpKernel μ m' ω) :=
      hω.integral_bilin hJi hsi (nasaAdjCLM (E := E) (F := F))
    rw [show (∫ y, v' y ∂condExpKernel μ m' ω) =
        ∫ y, (nasaAdjCLM (E := E) (F := F)) (J' y) (s' y) ∂condExpKernel μ m' ω from rfl,
      hbilin, hJeq, hseq, nasaAdjCLM_apply]
  exact ⟨hv_memLp, hv_sq_bound, hv_ce⟩

private lemma nasa_integral_inner_eq_zero {d : ℕ} {Ω : Type*} {m' : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (hm' : m' ≤ mΩ) (μ : Measure Ω) [IsProbabilityMeasure μ]
    {w Δ : Ω → EuclideanSpace ℝ (Fin d)}
    (hw_sm : StronglyMeasurable[m'] w) (hw2 : MemLp w 2 μ)
    (hΔ2 : MemLp Δ 2 μ) (hΔ0 : μ[Δ | m'] =ᵐ[μ] 0) :
    Integrable (fun ω => ⟪w ω, Δ ω⟫) μ ∧ ∫ ω, ⟪w ω, Δ ω⟫ ∂μ = 0 := by
  have hw_sq : Integrable (fun ω => ‖w ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2
  have hΔ_sq : Integrable (fun ω => ‖Δ ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hΔ2.aestronglyMeasurable).mp hΔ2
  have hint : Integrable (fun ω => ⟪w ω, Δ ω⟫) μ := by
    refine Integrable.mono' ((hw_sq.add hΔ_sq).div_const 2)
      (hw2.aestronglyMeasurable.inner hΔ2.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
    have hcs : |⟪w ω, Δ ω⟫| ≤ ‖w ω‖ * ‖Δ ω‖ := abs_real_inner_le_norm _ _
    have ham : ‖w ω‖ * ‖Δ ω‖ ≤ (‖w ω‖ ^ 2 + ‖Δ ω‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖w ω‖ - ‖Δ ω‖)]
    rw [Real.norm_eq_abs]
    exact hcs.trans ham
  refine ⟨hint, ?_⟩
  have hpull : μ[fun ω => (innerSL ℝ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
      (w ω) (Δ ω) | m'] =ᵐ[μ]
      fun ω => (innerSL ℝ : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
        (w ω) (μ[Δ | m'] ω) :=
    condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ) hw_sm hint (hΔ2.integrable one_le_two)
  have hzero : μ[fun ω => ⟪w ω, Δ ω⟫ | m'] =ᵐ[μ] 0 := by
    filter_upwards [hpull, hΔ0] with ω h1 h2
    simp only [innerSL_apply_apply] at h1
    rw [h1, h2]
    simp
  rw [← integral_condExp hm', integral_congr_ae hzero]
  simp

private lemma nasa_integrable_inner_of_memLp {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {w Δ : Ω → EuclideanSpace ℝ (Fin d)}
    (hw2 : MemLp w 2 μ) (hΔ2 : MemLp Δ 2 μ) :
    Integrable (fun ω => ⟪w ω, Δ ω⟫) μ := by
  have hw_sq : Integrable (fun ω => ‖w ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw2.aestronglyMeasurable).mp hw2
  have hΔ_sq : Integrable (fun ω => ‖Δ ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hΔ2.aestronglyMeasurable).mp hΔ2
  refine Integrable.mono' ((hw_sq.add hΔ_sq).div_const 2)
    (hw2.aestronglyMeasurable.inner hΔ2.aestronglyMeasurable) (ae_of_all _ fun ω => ?_)
  have hcs : |⟪w ω, Δ ω⟫| ≤ ‖w ω‖ * ‖Δ ω‖ := abs_real_inner_le_norm _ _
  have ham : ‖w ω‖ * ‖Δ ω‖ ≤ (‖w ω‖ ^ 2 + ‖Δ ω‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖w ω‖ - ‖Δ ω‖)]
  rw [Real.norm_eq_abs]
  exact hcs.trans ham

private lemma nasa_memLp_of_lip {d₁ d₂ : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    {h : EuclideanSpace ℝ (Fin d₁) → EuclideanSpace ℝ (Fin d₂)}
    {L : ℝ} (_hL : 0 ≤ L) (hcont : Continuous h) (hlip : ∀ a b, ‖h a - h b‖ ≤ L * ‖a - b‖)
    {y : Ω → EuclideanSpace ℝ (Fin d₁)} (hy : MemLp y 2 μ) :
    MemLp (fun ω => h (y ω)) 2 μ := by
  have hy_sq : Integrable (fun ω => ‖y ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hy.aestronglyMeasurable).mp hy
  have h_asm : AEStronglyMeasurable (fun ω => h (y ω)) μ :=
    hcont.comp_aestronglyMeasurable hy.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm h_asm]
  refine Integrable.mono' ((integrable_const (2 * ‖h 0‖ ^ 2)).add (hy_sq.const_mul (2 * L ^ 2)))
    (h_asm.norm.pow 2) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 : ‖h (y ω)‖ ≤ ‖h 0‖ + L * ‖y ω‖ := by
    have hlip0 := hlip (y ω) 0
    rw [sub_zero] at hlip0
    have htri : ‖h (y ω)‖ ≤ ‖h (y ω) - h 0‖ + ‖h 0‖ := norm_le_norm_sub_add (h (y ω)) (h 0)
    linarith
  have h2 : ‖h (y ω)‖ ^ 2 ≤ (‖h 0‖ + L * ‖y ω‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (‖h 0‖ - L * ‖y ω‖)]

/-! ### Section 3: Proposition 1(a)-(b) bundled helper -/

private lemma nasa_prop1_bundle {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (γ : ℝ) (hγ : 0 < γ)
    (hτ_one : ∀ k, τ k ≤ 1) (hτ0 : τ 0 = 1 / a) :
    let d : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => ybar P (x k ω) (z k ω) β - x k ω
    let v : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
      fun k ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)
    let barv : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
      fun k ω => (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω))
    let rFn : ℕ → Ω → ℝ := fun k ω =>
      rTerm P f g a b γ β Lf Lg Ldf Ldg τ (fun i => x i ω) (fun i => z i ω)
        (fun i => u i ω) (fun i => G i ω) (fun i => s i ω) (fun i => J i ω) k
    (∀ k, StronglyMeasurable[ℱ k] (x (k + 1))) ∧
    (∀ k, StronglyMeasurable[ℱ k] (barv k)) ∧
    (∀ k, MemLp (x k) 2 μ) ∧
    (∀ k, MemLp (z k) 2 μ) ∧
    (∀ k, MemLp (u k) 2 μ) ∧
    (∀ k, MemLp (d k) 2 μ) ∧
    (∀ k, MemLp (v k) 2 μ) ∧
    (∀ k, MemLp (barv k) 2 μ) ∧
    (∀ k, μ[fun ω => barv k ω - v k ω | ℱ k] =ᵐ[μ] 0) ∧
    (∀ k, ∫ ω, ‖barv k ω - v k ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2) ∧
    (∀ k, Integrable (rFn k) μ) ∧
    (∀ N, 1 ≤ N → ∑ k ∈ Finset.range N, ∫ ω, rFn k ω ∂μ ≤
      sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ k ∈ Finset.range N, τ k ^ 2) := by
  intro d v barv rFn
  have hΩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : μ Set.univ = 0 := by simp [Measure.eq_zero_of_isEmpty μ]
    simp at h0
  obtain ⟨ω₀⟩ := hΩ
  have ha : 0 < a := (hrun ω₀).a_pos
  have hβ : 0 < β := (hrun ω₀).β_pos
  have hτpos : ∀ k, 0 < τ k := (hrun ω₀).τ_pos
  have hτle : ∀ k, τ k ≤ 1 / a := (hrun ω₀).τ_le
  have haτ_pos : ∀ k, 0 < a * τ k := fun k => mul_pos ha (hτpos k)
  have haτ_le1 : ∀ k, a * τ k ≤ 1 := fun k => by
    have := mul_le_mul_of_nonneg_left (hτle k) ha.le
    rwa [mul_one_div_cancel ha.ne'] at this
  have haτ0 : a * τ 0 = 1 := by rw [hτ0, mul_one_div_cancel ha.ne']
  have hP_cont : Continuous P := nasa_proj_cont X hX_cvx P hP
  have hg_cont : Continuous g := hA2.contDiff_g.continuous
  have hgradf_cont : Continuous (gradient f) := nasa_gradf_cont f hA2.contDiff_f
  have hfderivg_cont : Continuous (fderiv ℝ g) := hA2.contDiff_g.continuous_fderiv (by norm_num)
  have hxX : ∀ k ω, x k ω ∈ X := by
    intro k ω
    induction k with
    | zero => rw [(hrun ω).init_x]; exact (hrun ω).x0_mem
    | succ k ih =>
      rw [(hrun ω).step_x k]
      exact hX_cvx.add_smul_sub_mem ih (hP _).1 ⟨(hτpos k).le, hτ_one k⟩
  have hd_sm : ∀ k, StronglyMeasurable[ℱ k] (d k) := fun k =>
    (hP_cont.comp_stronglyMeasurable ((hA1.adapted_x k).sub ((hA1.adapted_z k).const_smul β⁻¹))).sub
      (hA1.adapted_x k)
  have hx_succ_sm : ∀ k, StronglyMeasurable[ℱ k] (x (k + 1)) := fun k => by
    have heq : x (k + 1) = fun ω => x k ω + τ k • d k ω := funext fun ω => (hrun ω).step_x k
    rw [heq]
    exact (hA1.adapted_x k).add ((hd_sm k).const_smul (τ k))
  have hbarv_sm : ∀ k, StronglyMeasurable[ℱ k] (barv k) := fun k =>
    nasa_stronglyMeasurable_adjoint_apply
      (hfderivg_cont.comp_stronglyMeasurable (hx_succ_sm k))
      (hgradf_cont.comp_stronglyMeasurable (hA1.adapted_u k))
  have hv_all := fun k => nasa_v_props_abstract (ℱ.le k) μ
    (hA1.memLp_J k) (hA1.memLp_s k) (hA1.condIndep_sJ k)
    (hA1.condExp_J k) (hA1.condExp_s k) (hA1.condExp_J_sq k) (hA1.condExp_s_sq k)
    (fun hA hw => nasa_stronglyMeasurable_adjoint_apply hA hw)
  have hv_memLp : ∀ k, MemLp (v k) 2 μ := fun k => (hv_all k).1
  have hv_sq_le : ∀ k, ∫ ω, ‖v k ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := fun k => (hv_all k).2.1
  have hv_ce : ∀ k, μ[v k | ℱ k] =ᵐ[μ] barv k := fun k => (hv_all k).2.2
  have hz_memLp : ∀ k, MemLp (z k) 2 μ := by
    intro k
    induction k with
    | zero =>
      have : z 0 = fun _ => z0 := funext fun ω => (hrun ω).init_z
      rw [this]; exact memLp_const z0
    | succ k ih =>
      have heq : z (k + 1) = fun ω => (1 - a * τ k) • z k ω + (a * τ k) • v k ω :=
        funext fun ω => (hrun ω).step_z k
      rw [heq]
      exact (ih.const_smul (1 - a * τ k)).add ((hv_memLp k).const_smul (a * τ k))
  have hz_sq_int : ∀ k, Integrable (fun ω => ‖z k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hz_memLp k).aestronglyMeasurable).mp (hz_memLp k)
  have hv_sq_int : ∀ k, Integrable (fun ω => ‖v k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hv_memLp k).aestronglyMeasurable).mp (hv_memLp k)
  have hz_sq_le : ∀ k, 1 ≤ k → ∫ ω, ‖z k ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    induction j with
    | zero =>
      have h1 : ∀ ω, z 1 ω = v 0 ω := fun ω => by
        rw [(hrun ω).step_z 0, haτ0, sub_self, zero_smul, zero_add, one_smul]
      simp_rw [h1]
      exact hv_sq_le 0
    | succ j ih =>
      have hpt : ∀ ω, ‖z (j + 2) ω‖ ^ 2 ≤
          (1 - a * τ (j + 1)) * ‖z (j + 1) ω‖ ^ 2 + (a * τ (j + 1)) * ‖v (j + 1) ω‖ ^ 2 := fun ω => by
        rw [(hrun ω).step_z (j + 1)]
        exact nasa_sq_norm_convex (z (j + 1) ω) (v (j + 1) ω) (haτ_pos (j + 1)).le (haτ_le1 (j + 1))
      have hint_rhs : Integrable (fun ω => (1 - a * τ (j + 1)) * ‖z (j + 1) ω‖ ^ 2 +
          (a * τ (j + 1)) * ‖v (j + 1) ω‖ ^ 2) μ :=
        ((hz_sq_int (j + 1)).const_mul _).add ((hv_sq_int (j + 1)).const_mul _)
      have hmono := integral_mono (hz_sq_int (j + 2)) hint_rhs hpt
      rw [integral_add ((hz_sq_int (j + 1)).const_mul _) ((hv_sq_int (j + 1)).const_mul _),
        integral_const_mul, integral_const_mul] at hmono
      have h1 : 0 ≤ 1 - a * τ (j + 1) := by linarith [haτ_le1 (j + 1)]
      have h2 : 0 ≤ a * τ (j + 1) := (haτ_pos (j + 1)).le
      have hih := ih (by omega)
      have hvle := hv_sq_le (j + 1)
      nlinarith
  have hd_norm_le : ∀ k ω, ‖d k ω‖ ≤ ‖z k ω‖ / β := fun k ω =>
    nasa_norm_d_le X hX_cl hX_cvx P hP (x k ω) (hxX k ω) (z k ω) β hβ
  have hd_memLp : ∀ k, MemLp (d k) 2 μ := fun k => by
    have hsm : AEStronglyMeasurable (d k) μ := ((hd_sm k).mono (ℱ.le k)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hsm]
    refine Integrable.mono' ((hz_sq_int k).div_const (β ^ 2)) (hsm.norm.pow 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (hd_norm_le k ω) 2
    rwa [div_pow] at h1
  have hd_sq_int : ∀ k, Integrable (fun ω => ‖d k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hd_memLp k).aestronglyMeasurable).mp (hd_memLp k)
  have hx_memLp : ∀ k, MemLp (x k) 2 μ := by
    intro k
    induction k with
    | zero =>
      have : x 0 = fun _ => x0 := funext fun ω => (hrun ω).init_x
      rw [this]; exact memLp_const x0
    | succ k ih =>
      have heq : x (k + 1) = fun ω => x k ω + τ k • d k ω := funext fun ω => (hrun ω).step_x k
      rw [heq]
      exact ih.add ((hd_memLp k).const_smul (τ k))
  have hu_memLp : ∀ k, MemLp (u k) 2 μ := by
    intro k
    induction k with
    | zero =>
      have : u 0 = fun _ => u0 := funext fun ω => (hrun ω).init_u
      rw [this]; exact memLp_const u0
    | succ k ih =>
      have heq : u (k + 1) = fun ω => (1 - b * τ k) • u k ω + (b * τ k) • G (k + 1) ω :=
        funext fun ω => (hrun ω).step_u k
      rw [heq]
      exact (ih.const_smul (1 - b * τ k)).add ((hA1.memLp_G k).const_smul (b * τ k))
  have hgx_memLp : ∀ k, MemLp (fun ω => g (x k ω)) 2 μ := fun k =>
    nasa_memLp_of_lip μ hA2.Lg_nonneg hg_cont hA2.lip_g (hx_memLp k)
  have hgradf_u_memLp : ∀ k, MemLp (fun ω => gradient f (u k ω)) 2 μ := fun k =>
    nasa_memLp_of_lip μ hA2.Ldf_nonneg hgradf_cont hA2.lip_gradf (hu_memLp k)
  have hbarv_memLp : ∀ k, MemLp (barv k) 2 μ := fun k => by
    have hsm : AEStronglyMeasurable (barv k) μ := ((hbarv_sm k).mono (ℱ.le k)).aestronglyMeasurable
    rw [memLp_two_iff_integrable_sq_norm hsm]
    have hgu_sq : Integrable (fun ω => ‖gradient f (u k ω)‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (hgradf_u_memLp k).aestronglyMeasurable).mp (hgradf_u_memLp k)
    refine Integrable.mono' (hgu_sq.const_mul (Lg ^ 2)) (hsm.norm.pow 2) (ae_of_all _ fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h1 : ‖barv k ω‖ ≤ Lg * ‖gradient f (u k ω)‖ := by
      calc ‖barv k ω‖ ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))‖ * ‖gradient f (u k ω)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖fderiv ℝ g (x (k + 1) ω)‖ * ‖gradient f (u k ω)‖ := by rw [LinearIsometryEquiv.norm_map]
        _ ≤ Lg * ‖gradient f (u k ω)‖ :=
            mul_le_mul_of_nonneg_right (nasa_fderivg_bound f g Lf Lg Ldf Ldg hA2 _) (norm_nonneg _)
    calc ‖barv k ω‖ ^ 2 ≤ (Lg * ‖gradient f (u k ω)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = Lg ^ 2 * ‖gradient f (u k ω)‖ ^ 2 := mul_pow _ _ 2
  let ΔF : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => barv k ω - v k ω
  have hΔF_memLp : ∀ k, MemLp (ΔF k) 2 μ := fun k => (hbarv_memLp k).sub (hv_memLp k)
  have hΔF_sq_int : ∀ k, Integrable (fun ω => ‖ΔF k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hΔF_memLp k).aestronglyMeasurable).mp (hΔF_memLp k)
  have hΔF_ce0 : ∀ k, μ[ΔF k | ℱ k] =ᵐ[μ] 0 := fun k => by
    have hsub : μ[ΔF k | ℱ k] =ᵐ[μ] μ[barv k | ℱ k] - μ[v k | ℱ k] :=
      condExp_sub ((hbarv_memLp k).integrable one_le_two) ((hv_memLp k).integrable one_le_two) _
    have hbar_ce : μ[barv k | ℱ k] = barv k :=
      condExp_of_stronglyMeasurable (ℱ.le k) (hbarv_sm k) ((hbarv_memLp k).integrable one_le_two)
    filter_upwards [hsub, hv_ce k] with ω h1 h2
    simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
    rw [h1, hbar_ce, h2, sub_self]
  have hΔF_sq_le : ∀ k, ∫ ω, ‖ΔF k ω‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2 := fun k => by
    have horth := (nasa_integral_inner_eq_zero (ℱ.le k) μ (hbarv_sm k)
      (hbarv_memLp k) (hΔF_memLp k) (hΔF_ce0 k)).2
    have hbarv_sq_int : Integrable (fun ω => ‖barv k ω‖ ^ 2) μ :=
      (memLp_two_iff_integrable_sq_norm (hbarv_memLp k).aestronglyMeasurable).mp (hbarv_memLp k)
    have hinner_int : Integrable (fun ω => ⟪barv k ω, ΔF k ω⟫) μ :=
      nasa_integrable_inner_of_memLp μ (hbarv_memLp k) (hΔF_memLp k)
    have hident : ∀ ω, ‖v k ω‖ ^ 2 = ‖barv k ω‖ ^ 2 - 2 * ⟪barv k ω, ΔF k ω⟫ + ‖ΔF k ω‖ ^ 2 := fun ω => by
      have hv_eq : v k ω = barv k ω - ΔF k ω := by simp [ΔF]
      rw [hv_eq, norm_sub_sq_real]
    have hsub_int : Integrable (fun ω => ‖barv k ω‖ ^ 2 - 2 * ⟪barv k ω, ΔF k ω⟫) μ :=
      hbarv_sq_int.sub (hinner_int.const_mul 2)
    have hint_eq : ∫ ω, ‖v k ω‖ ^ 2 ∂μ =
        ∫ ω, ‖barv k ω‖ ^ 2 ∂μ - 2 * ∫ ω, ⟪barv k ω, ΔF k ω⟫ ∂μ + ∫ ω, ‖ΔF k ω‖ ^ 2 ∂μ := by
      simp_rw [hident]
      rw [integral_add hsub_int (hΔF_sq_int k),
        integral_sub hbarv_sq_int (hinner_int.const_mul 2), integral_const_mul]
    have hbar_nn : 0 ≤ ∫ ω, ‖barv k ω‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have hvle := hv_sq_le k
    linarith
  let Δg : ℕ → Ω → EuclideanSpace ℝ (Fin m) := fun k ω => g (x (k + 1) ω) - G (k + 1) ω
  have hΔg_memLp : ∀ k, MemLp (Δg k) 2 μ := fun k => (hgx_memLp (k + 1)).sub (hA1.memLp_G k)
  have hΔg_sq_int : ∀ k, Integrable (fun ω => ‖Δg k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hΔg_memLp k).aestronglyMeasurable).mp (hΔg_memLp k)
  have hΔg_ce0 : ∀ k, μ[Δg k | ℱ k] =ᵐ[μ] 0 := fun k => by
    have hsub : μ[Δg k | ℱ k] =ᵐ[μ] μ[fun ω => g (x (k + 1) ω) | ℱ k] - μ[G (k + 1) | ℱ k] :=
      condExp_sub ((hgx_memLp (k + 1)).integrable one_le_two) ((hA1.memLp_G k).integrable one_le_two) _
    have hgx_ce : μ[fun ω => g (x (k + 1) ω) | ℱ k] = fun ω => g (x (k + 1) ω) :=
      condExp_of_stronglyMeasurable (ℱ.le k) (hg_cont.comp_stronglyMeasurable (hx_succ_sm k))
        ((hgx_memLp (k + 1)).integrable one_le_two)
    filter_upwards [hsub, hA1.condExp_G k] with ω h1 h2
    simp only [Pi.sub_apply, Pi.zero_apply] at h1 ⊢
    rw [h1, hgx_ce, h2, sub_self]
  have hΔg_sq_le : ∀ k, ∫ ω, ‖Δg k ω‖ ^ 2 ∂μ ≤ σG ^ 2 := fun k => by
    have hrev : ∀ ω, ‖Δg k ω‖ ^ 2 = ‖G (k + 1) ω - g (x (k + 1) ω)‖ ^ 2 := fun ω => by
      simp [Δg, norm_sub_rev]
    simp_rw [hrev]
    rw [← integral_condExp (ℱ.le k)]
    have h1 := integral_mono_ae integrable_condExp (integrable_const (σG ^ 2)) (hA1.condExp_G_var k)
    simpa using h1
  have hz_diff_sq_int : ∀ k, Integrable (fun ω => ‖z (k + 1) ω - z k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm ((hz_memLp (k + 1)).sub (hz_memLp k)).aestronglyMeasurable).mp
      ((hz_memLp (k + 1)).sub (hz_memLp k))
  have hz_diff_sum_le : ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        2 * ‖z0‖ ^ 2 + 4 * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
    intro N hN
    have hterm0 : ∫ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ∂μ ≤ 2 * ‖z0‖ ^ 2 + 2 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ 0 ^ 2 := by
      have hpt : ∀ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ≤ 2 * ‖v 0 ω‖ ^ 2 + 2 * ‖z0‖ ^ 2 := fun ω => by
        rw [(hrun ω).step_z 0, (hrun ω).init_z, haτ0, sub_self, zero_smul, zero_add, one_smul]
        exact nasa_sq_norm_sub_le (v 0 ω) z0
      have hmono : ∫ ω, ‖z 1 ω - z 0 ω‖ ^ 2 ∂μ ≤ ∫ ω, (2 * ‖v 0 ω‖ ^ 2 + 2 * ‖z0‖ ^ 2) ∂μ :=
        integral_mono (hz_diff_sq_int 0)
          (((hv_sq_int 0).const_mul 2).add (integrable_const (2 * ‖z0‖ ^ 2))) hpt
      rw [integral_add ((hv_sq_int 0).const_mul 2) (integrable_const _), integral_const_mul] at hmono
      simp only [integral_const, probReal_univ, one_smul] at hmono
      have hv0 := hv_sq_le 0
      have hsq : a ^ 2 * τ 0 ^ 2 = 1 := by
        have := congrArg (· ^ 2) haτ0
        nlinarith
      have hrew : 2 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ 0 ^ 2 = 2 * (σJ ^ 2 * σs ^ 2) := by
        linear_combination 2 * σJ ^ 2 * σs ^ 2 * hsq
      linarith
    have hterm_pos : ∀ k, 1 ≤ k →
        ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤ 4 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ k ^ 2 := fun k hk => by
      have hpt : ∀ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ≤
          (2 * (a * τ k) ^ 2) * ‖v k ω‖ ^ 2 + (2 * (a * τ k) ^ 2) * ‖z k ω‖ ^ 2 := fun ω => by
        have hdiff : z (k + 1) ω - z k ω = (a * τ k) • (v k ω - z k ω) := by
          rw [(hrun ω).step_z k]
          module
        rw [hdiff, norm_smul, Real.norm_of_nonneg (haτ_pos k).le, mul_pow]
        have h2 := nasa_sq_norm_sub_le (v k ω) (z k ω)
        nlinarith [sq_nonneg (a * τ k)]
      have hmono : ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
          ∫ ω, ((2 * (a * τ k) ^ 2) * ‖v k ω‖ ^ 2 + (2 * (a * τ k) ^ 2) * ‖z k ω‖ ^ 2) ∂μ :=
        integral_mono (hz_diff_sq_int k)
          (((hv_sq_int k).const_mul _).add ((hz_sq_int k).const_mul _)) hpt
      rw [integral_add ((hv_sq_int k).const_mul _) ((hz_sq_int k).const_mul _),
        integral_const_mul, integral_const_mul] at hmono
      have hvk := hv_sq_le k
      have hzk := hz_sq_le k hk
      nlinarith [sq_nonneg (a * τ k)]
    obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
    rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have hrest : ∑ k ∈ Finset.range M, ∫ ω, ‖z (k + 1 + 1) ω - z (k + 1) ω‖ ^ 2 ∂μ ≤
        ∑ k ∈ Finset.range M, 4 * a ^ 2 * σJ ^ 2 * σs ^ 2 * τ (k + 1) ^ 2 :=
      Finset.sum_le_sum fun k _ => hterm_pos (k + 1) (by omega)
    rw [← Finset.mul_sum] at hrest
    have hnn0 : 0 ≤ a ^ 2 * σJ ^ 2 * σs ^ 2 * τ 0 ^ 2 := by positivity
    linarith
  have hr_int_and_eq : ∀ k, Integrable (rFn k) μ ∧
      ∫ ω, rFn k ω ∂μ =
        τ k ^ 2 / 2 * ((a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf) *
            (∫ ω, ‖d k ω‖ ^ 2 ∂μ) + γ * b ^ 2 * (∫ ω, ‖Δg k ω‖ ^ 2 ∂μ))
        + Leta β / 2 * (∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ) := by
    intro k
    have h1 : Integrable (fun ω => ⟪g (x (k + 1) ω) - u k ω, Δg k ω⟫) μ ∧
        ∫ ω, ⟪g (x (k + 1) ω) - u k ω, Δg k ω⟫ ∂μ = 0 :=
      nasa_integral_inner_eq_zero (ℱ.le k) μ
        (show StronglyMeasurable[ℱ k] (fun ω => g (x (k + 1) ω) - u k ω) from
          (hg_cont.comp_stronglyMeasurable (hx_succ_sm k)).sub (hA1.adapted_u k))
        ((hgx_memLp (k + 1)).sub (hu_memLp k)) (hΔg_memLp k) (hΔg_ce0 k)
    have h2 : Integrable (fun ω => ⟪d k ω, ΔF k ω⟫) μ ∧
        ∫ ω, ⟪d k ω, ΔF k ω⟫ ∂μ = 0 :=
      nasa_integral_inner_eq_zero (ℱ.le k) μ (hd_sm k) (hd_memLp k) (hΔF_memLp k) (hΔF_ce0 k)
    set C1 := a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf
    have ha1 : Integrable (fun ω => τ k ^ 2 / 2 * (C1 * ‖d k ω‖ ^ 2 + γ * b ^ 2 * ‖Δg k ω‖ ^ 2)) μ :=
      (((hd_sq_int k).const_mul C1).add ((hΔg_sq_int k).const_mul (γ * b ^ 2))).const_mul _
    have ha2 : Integrable (fun ω => τ k * (γ * b * (1 - b * τ k) * ⟪g (x (k + 1) ω) - u k ω, Δg k ω⟫ +
        a * ⟪d k ω, ΔF k ω⟫)) μ :=
      ((h1.1.const_mul _).add (h2.1.const_mul _)).const_mul _
    have ha12 : Integrable (fun ω =>
        τ k ^ 2 / 2 * (C1 * ‖d k ω‖ ^ 2 + γ * b ^ 2 * ‖Δg k ω‖ ^ 2) +
        τ k * (γ * b * (1 - b * τ k) * ⟪g (x (k + 1) ω) - u k ω, Δg k ω⟫ + a * ⟪d k ω, ΔF k ω⟫)) μ :=
      ha1.add ha2
    have ha3 : Integrable (fun ω => Leta β / 2 * ‖z (k + 1) ω - z k ω‖ ^ 2) μ :=
      (hz_diff_sq_int k).const_mul _
    have hr_eq : ∀ ω, rFn k ω =
        τ k ^ 2 / 2 * (C1 * ‖d k ω‖ ^ 2 + γ * b ^ 2 * ‖Δg k ω‖ ^ 2)
        + τ k * (γ * b * (1 - b * τ k) * ⟪g (x (k + 1) ω) - u k ω, Δg k ω⟫ + a * ⟪d k ω, ΔF k ω⟫)
        + Leta β / 2 * ‖z (k + 1) ω - z k ω‖ ^ 2 := fun _ => rfl
    refine ⟨show Integrable (fun ω => rFn k ω) μ from by simp_rw [hr_eq]; exact ha12.add ha3, ?_⟩
    simp_rw [hr_eq]
    rw [integral_add ha12 ha3, integral_add ha1 ha2,
      integral_const_mul, integral_add ((hd_sq_int k).const_mul C1) ((hΔg_sq_int k).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_const_mul, integral_add (h1.1.const_mul _) (h2.1.const_mul _),
      integral_const_mul, integral_const_mul, h1.2, h2.2,
      integral_const_mul]
    ring
  have hr_sum_le : ∀ N : ℕ, 1 ≤ N →
      ∑ k ∈ Finset.range N, ∫ ω, rFn k ω ∂μ ≤
        sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
    intro N hN
    set C1 := a * LgradF Lf Lg Ldf Ldg + Leta β + γ * Lg ^ 2 + 2 * a * Lg ^ 2 * Ldf
    set M0 := max (σJ ^ 2 * σs ^ 2) (‖z0‖ ^ 2)
    have hLeta_nn : 0 ≤ Leta β := by unfold Leta; positivity
    have hLF_nn : 0 ≤ LgradF Lf Lg Ldf Ldg := by
      unfold LgradF
      have := hA2.Lf_nonneg; have := hA2.Lg_nonneg; have := hA2.Ldf_nonneg; have := hA2.Ldg_nonneg
      positivity
    have hC1_nn : 0 ≤ C1 := by
      have := hA2.Lg_nonneg; have := hA2.Ldf_nonneg
      positivity
    have hd_exp_le : ∀ k, ∫ ω, ‖d k ω‖ ^ 2 ∂μ ≤ M0 / β ^ 2 := fun k => by
      have h1 : ∫ ω, ‖d k ω‖ ^ 2 ∂μ ≤ (∫ ω, ‖z k ω‖ ^ 2 ∂μ) / β ^ 2 := by
        have hpt : ∀ ω, ‖d k ω‖ ^ 2 ≤ ‖z k ω‖ ^ 2 / β ^ 2 := fun ω => by
          have := pow_le_pow_left₀ (norm_nonneg _) (hd_norm_le k ω) 2
          rwa [div_pow] at this
        have hmono := integral_mono (hd_sq_int k) ((hz_sq_int k).div_const (β ^ 2)) hpt
        rwa [integral_div] at hmono
      apply h1.trans
      apply div_le_div_of_nonneg_right _ (sq_nonneg β)
      cases k with
      | zero =>
        have h0 : ∀ ω, ‖z 0 ω‖ ^ 2 = ‖z0‖ ^ 2 := fun ω => by rw [(hrun ω).init_z]
        simp_rw [h0]
        simp [M0]
      | succ j =>
        exact (hz_sq_le (j + 1) (by omega)).trans (le_max_left _ _)
    have hsum_eq : ∑ k ∈ Finset.range N, ∫ ω, rFn k ω ∂μ =
        ∑ k ∈ Finset.range N, (τ k ^ 2 / 2 * (C1 * (∫ ω, ‖d k ω‖ ^ 2 ∂μ) +
            γ * b ^ 2 * (∫ ω, ‖Δg k ω‖ ^ 2 ∂μ)))
        + Leta β / 2 * ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ := by
      simp_rw [(hr_int_and_eq _).2]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hsum_eq]
    have hpart1 : ∑ k ∈ Finset.range N, (τ k ^ 2 / 2 * (C1 * (∫ ω, ‖d k ω‖ ^ 2 ∂μ) +
          γ * b ^ 2 * (∫ ω, ‖Δg k ω‖ ^ 2 ∂μ))) ≤
        1 / 2 * (C1 * M0 / β ^ 2 + γ * b ^ 2 * σG ^ 2) * ∑ k ∈ Finset.range N, τ k ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have hdk := hd_exp_le k
      have hgk := hΔg_sq_le k
      have hγb : 0 ≤ γ * b ^ 2 := by positivity
      have hinner : C1 * (∫ ω, ‖d k ω‖ ^ 2 ∂μ) + γ * b ^ 2 * (∫ ω, ‖Δg k ω‖ ^ 2 ∂μ) ≤
          C1 * (M0 / β ^ 2) + γ * b ^ 2 * σG ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hdk hC1_nn) (mul_le_mul_of_nonneg_left hgk hγb)
      have hτ2 : 0 ≤ τ k ^ 2 / 2 := by positivity
      have := mul_le_mul_of_nonneg_left hinner hτ2
      linarith [show τ k ^ 2 / 2 * (C1 * (M0 / β ^ 2) + γ * b ^ 2 * σG ^ 2) =
          1 / 2 * (C1 * M0 / β ^ 2 + γ * b ^ 2 * σG ^ 2) * τ k ^ 2 by ring]
    have hSτ_ge : 1 / a ^ 2 ≤ ∑ k ∈ Finset.range N, τ k ^ 2 := by
      have hmem : (0 : ℕ) ∈ Finset.range N := Finset.mem_range.mpr (by omega)
      have hle : τ 0 ^ 2 ≤ ∑ k ∈ Finset.range N, τ k ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (τ k)) hmem
      rwa [hτ0, one_div_pow] at hle
    have hpart2 : Leta β / 2 * ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
        1 / 2 * (4 * Leta β * (max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2)) *
          ∑ k ∈ Finset.range N, τ k ^ 2 := by
      have hzsum := hz_diff_sum_le N hN
      have h1 : Leta β / 2 * ∑ k ∈ Finset.range N, ∫ ω, ‖z (k + 1) ω - z k ω‖ ^ 2 ∂μ ≤
          Leta β * ‖z0‖ ^ 2 + 2 * Leta β * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
        have := mul_le_mul_of_nonneg_left hzsum (by linarith : 0 ≤ Leta β / 2)
        linarith
      have hmax : 1 ≤ 2 * max 1 (a ^ 2 / 2) * ∑ k ∈ Finset.range N, τ k ^ 2 := by
        have hm1 : a ^ 2 / 2 ≤ max 1 (a ^ 2 / 2) := le_max_right _ _
        have hSnn : 0 ≤ ∑ k ∈ Finset.range N, τ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        calc (1 : ℝ) = 2 * (a ^ 2 / 2) * (1 / a ^ 2) := by field_simp
          _ ≤ 2 * (a ^ 2 / 2) * ∑ k ∈ Finset.range N, τ k ^ 2 :=
              mul_le_mul_of_nonneg_left hSτ_ge (by positivity)
          _ ≤ 2 * max 1 (a ^ 2 / 2) * ∑ k ∈ Finset.range N, τ k ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) hSnn
      have hz0_le : Leta β * ‖z0‖ ^ 2 ≤
          2 * Leta β * max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
        have := mul_le_mul_of_nonneg_left hmax (mul_nonneg hLeta_nn (sq_nonneg ‖z0‖))
        linarith
      have h24_le : 2 * Leta β * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 ≤
          48 * Leta β * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
        have hSnn : 0 ≤ ∑ k ∈ Finset.range N, τ k ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
        have hnn : 0 ≤ Leta β * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 := by positivity
        linarith
      have heq_rhs : 1 / 2 * (4 * Leta β * (max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 +
            24 * a ^ 2 * σJ ^ 2 * σs ^ 2)) * ∑ k ∈ Finset.range N, τ k ^ 2 =
          2 * Leta β * max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 +
          48 * Leta β * a ^ 2 * σJ ^ 2 * σs ^ 2 * ∑ k ∈ Finset.range N, τ k ^ 2 := by ring
      linarith
    have hcomb : 1 / 2 * (C1 * M0 / β ^ 2 + γ * b ^ 2 * σG ^ 2) * ∑ k ∈ Finset.range N, τ k ^ 2 +
        1 / 2 * (4 * Leta β * (max 1 (a ^ 2 / 2) * ‖z0‖ ^ 2 + 24 * a ^ 2 * σJ ^ 2 * σs ^ 2)) *
          ∑ k ∈ Finset.range N, τ k ^ 2 =
        sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ k ∈ Finset.range N, τ k ^ 2 := by
      unfold sigmaHatSq
      simp only [C1, M0]
      ring
    linarith
  exact ⟨hx_succ_sm, hbarv_sm, hx_memLp, hz_memLp, hu_memLp, hd_memLp, hv_memLp, hbarv_memLp,
    hΔF_ce0, hΔF_sq_le, fun k => (hr_int_and_eq k).1, hr_sum_le⟩

/-! ### Section 4: Pathwise δ bound and tracking-error recursion -/

private lemma nasa_delta_bound {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (ht1 : t ≤ 1) (hat1 : a * t ≤ 1)
    (xk xk1 dk : EuclideanSpace ℝ (Fin n)) (uk : EuclideanSpace ℝ (Fin m))
    (hstep : xk1 = xk + t • dk) :
    let barvk := (ContinuousLinearMap.adjoint (fderiv ℝ g xk1)) (gradient f uk)
    let δk := (1 - a * t) • (gradF f g xk1 - gradF f g xk) + (a * t) • (gradF f g xk1 - barvk)
    ‖(a * t)⁻¹ • δk‖ ^ 2 ≤ L1 a Lf Lg Ldf Ldg * ‖dk‖ ^ 2 + L2 Lg Ldf * ‖g xk - uk‖ ^ 2 := by
  intro barvk δk
  have hat_pos : 0 < a * t := mul_pos ha ht
  let u1 : EuclideanSpace ℝ (Fin n) := ((1 - a * t) / (a * t)) • (gradF f g xk1 - gradF f g xk)
  let u2 : EuclideanSpace ℝ (Fin n) := gradF f g xk1 - barvk
  have hsplit : (a * t)⁻¹ • δk = u1 + u2 := by
    simp only [δk, u1, u2, smul_add, smul_smul]
    rw [inv_mul_cancel₀ hat_pos.ne', one_smul, div_eq_inv_mul]
  rw [hsplit]
  have hdx : xk1 - xk = t • dk := by rw [hstep]; abel
  have h1 : ‖u1‖ ≤ LgradF Lf Lg Ldf Ldg / a * ‖dk‖ := by
    have h1mt : 0 ≤ 1 - a * t := by linarith
    have hdiv_nn : 0 ≤ (1 - a * t) / (a * t) := div_nonneg h1mt hat_pos.le
    have hlip := lemma_2 f g Lf Lg Ldf Ldg hA2 xk1 xk
    rw [hdx, norm_smul, Real.norm_of_nonneg ht.le] at hlip
    have hLF_nn : 0 ≤ LgradF Lf Lg Ldf Ldg := by
      unfold LgradF
      have := hA2.Lf_nonneg; have := hA2.Lg_nonneg; have := hA2.Ldf_nonneg; have := hA2.Ldg_nonneg
      positivity
    calc ‖u1‖ = (1 - a * t) / (a * t) * ‖gradF f g xk1 - gradF f g xk‖ := by
          simp only [u1, norm_smul, Real.norm_of_nonneg hdiv_nn]
      _ ≤ (1 - a * t) / (a * t) * (LgradF Lf Lg Ldf Ldg * (t * ‖dk‖)) :=
          mul_le_mul_of_nonneg_left hlip hdiv_nn
      _ = (1 - a * t) * (LgradF Lf Lg Ldf Ldg / a * ‖dk‖) := by field_simp [ht.ne', ha.ne']
      _ ≤ 1 * (LgradF Lf Lg Ldf Ldg / a * ‖dk‖) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = LgradF Lf Lg Ldf Ldg / a * ‖dk‖ := one_mul _
  have h2 : ‖u2‖ ≤ Lg * Ldf * (Lg * ‖dk‖ + ‖g xk - uk‖) := by
    have hu2_eq : u2 = (ContinuousLinearMap.adjoint (fderiv ℝ g xk1))
        (gradient f (g xk1) - gradient f uk) := by
      simp only [u2, barvk, map_sub]
      rw [nasa_gradF_eq_adjoint f g hA2.contDiff_f hA2.contDiff_g]
    rw [hu2_eq]
    have hgx_step : ‖g xk1 - uk‖ ≤ Lg * ‖dk‖ + ‖g xk - uk‖ := by
      have htri : ‖g xk1 - uk‖ ≤ ‖g xk1 - g xk‖ + ‖g xk - uk‖ := by
        have := norm_add_le (g xk1 - g xk) (g xk - uk)
        simpa [sub_add_sub_cancel] using this
      have hlipg := hA2.lip_g xk1 xk
      rw [hdx, norm_smul, Real.norm_of_nonneg ht.le] at hlipg
      have hτ1 : Lg * (t * ‖dk‖) ≤ Lg * ‖dk‖ :=
        mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) ht1) hA2.Lg_nonneg
      linarith
    calc ‖(ContinuousLinearMap.adjoint (fderiv ℝ g xk1)) (gradient f (g xk1) - gradient f uk)‖
        ≤ ‖ContinuousLinearMap.adjoint (fderiv ℝ g xk1)‖ * ‖gradient f (g xk1) - gradient f uk‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ g xk1‖ * ‖gradient f (g xk1) - gradient f uk‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ Lg * (Ldf * ‖g xk1 - uk‖) :=
          mul_le_mul (nasa_fderivg_bound f g Lf Lg Ldf Ldg hA2 _) (hA2.lip_gradf _ _)
            (norm_nonneg _) hA2.Lg_nonneg
      _ = Lg * Ldf * ‖g xk1 - uk‖ := by ring
      _ ≤ Lg * Ldf * (Lg * ‖dk‖ + ‖g xk - uk‖) :=
          mul_le_mul_of_nonneg_left hgx_step (mul_nonneg hA2.Lg_nonneg hA2.Ldf_nonneg)
  have h1sq : ‖u1‖ ^ 2 ≤ LgradF Lf Lg Ldf Ldg ^ 2 / a ^ 2 * ‖dk‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hrew : (LgradF Lf Lg Ldf Ldg / a * ‖dk‖) ^ 2 =
        LgradF Lf Lg Ldf Ldg ^ 2 / a ^ 2 * ‖dk‖ ^ 2 := by ring
    linarith
  have h2sq : ‖u2‖ ^ 2 ≤ 2 * Lg ^ 4 * Ldf ^ 2 * ‖dk‖ ^ 2 + 2 * Lg ^ 2 * Ldf ^ 2 * ‖g xk - uk‖ ^ 2 := by
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hab : (Lg * ‖dk‖ + ‖g xk - uk‖) ^ 2 ≤ 2 * (Lg * ‖dk‖) ^ 2 + 2 * ‖g xk - uk‖ ^ 2 := by
      nlinarith [sq_nonneg (Lg * ‖dk‖ - ‖g xk - uk‖)]
    have := mul_le_mul_of_nonneg_left hab (sq_nonneg (Lg * Ldf))
    nlinarith
  have hadd := nasa_sq_norm_add_le u1 u2
  have hcomb : 2 * (LgradF Lf Lg Ldf Ldg ^ 2 / a ^ 2 * ‖dk‖ ^ 2) +
      2 * (2 * Lg ^ 4 * Ldf ^ 2 * ‖dk‖ ^ 2 + 2 * Lg ^ 2 * Ldf ^ 2 * ‖g xk - uk‖ ^ 2) =
      L1 a Lf Lg Ldf Ldg * ‖dk‖ ^ 2 + L2 Lg Ldf * ‖g xk - uk‖ ^ 2 := by
    unfold L1 L2; ring
  linarith

private lemma nasa_e_decomp_alg {E : Type*} [AddCommGroup E] [Module ℝ E]
    (t : ℝ) (g0 g1 z0 bv v1 : E) :
    g1 - ((1 - t) • z0 + t • v1) =
      ((1 - t) • (g0 - z0) + ((1 - t) • (g1 - g0) + t • (g1 - bv))) + t • (bv - v1) := by
  module

private lemma nasa_Gamma_props (a : ℝ) (τ : ℕ → ℝ) (hτ0 : τ 0 = 1 / a)
    (haτ : ∀ k, 1 ≤ k → a * τ k ≤ 1 / Real.sqrt 2) :
    Gamma a τ 1 = 1 ∧
    (∀ k, 1 ≤ k → Gamma a τ (k + 1) = Gamma a τ k * (1 - a * τ k)) ∧
    (∀ k, 1 ≤ k → 0 < Gamma a τ k) := by
  have h1 : Gamma a τ 1 = 1 := by simp [Gamma, Gamma1, hτ0]
  have hsucc : ∀ k, 1 ≤ k → Gamma a τ (k + 1) = Gamma a τ k * (1 - a * τ k) := by
    intro k hk
    simp only [Gamma]
    rw [Finset.prod_Ico_succ_top hk, mul_assoc]
  have hpos : ∀ k, 1 ≤ k → 0 < Gamma a τ k := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    induction j with
    | zero => rw [h1]; exact zero_lt_one
    | succ j ih =>
      rw [hsucc (j + 1) (by omega)]
      have h1' : a * τ (j + 1) ≤ 1 / Real.sqrt 2 := haτ (j + 1) (by omega)
      have hsqrt : (1 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt zero_le_one]; norm_num
      have hlt : 1 / Real.sqrt 2 < 1 := by rw [div_lt_one (by positivity)]; exact hsqrt
      exact mul_pos (ih (by omega)) (by linarith)
  exact ⟨h1, hsucc, hpos⟩

private lemma nasa_e_step_bound {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n)))
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (ha : 0 < a) (hτpos : ∀ k, 0 < τ k) (hτ_one : ∀ k, τ k ≤ 1) (haτ_le1 : ∀ k, a * τ k ≤ 1)
    (hx_succ_sm : ∀ k, StronglyMeasurable[ℱ k] (x (k + 1)))
    (hbarv_sm : ∀ k, StronglyMeasurable[ℱ k]
      (fun ω => (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω))))
    (hx_memLp : ∀ k, MemLp (x k) 2 μ) (hz_memLp : ∀ k, MemLp (z k) 2 μ)
    (hu_memLp : ∀ k, MemLp (u k) 2 μ)
    (hd_memLp : ∀ k, MemLp (fun ω => ybar P (x k ω) (z k ω) β - x k ω) 2 μ)
    (hv_memLp : ∀ k, MemLp (fun ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)) 2 μ)
    (hbarv_memLp : ∀ k, MemLp
      (fun ω => (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω))) 2 μ)
    (hΔF_ce0 : ∀ k, μ[fun ω =>
      (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω)) -
        (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω) | ℱ k] =ᵐ[μ] 0)
    (hΔF_sq_le : ∀ k, ∫ ω, ‖(ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω)) -
        (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)‖ ^ 2 ∂μ ≤ σJ ^ 2 * σs ^ 2) :
    (∀ k, Integrable (fun ω => ‖gradF f g (x k ω) - z k ω‖ ^ 2) μ) ∧
    (∀ k, ∫ ω, ‖gradF f g (x (k + 1) ω) - z (k + 1) ω‖ ^ 2 ∂μ ≤
      (1 - a * τ k) * ∫ ω, ‖gradF f g (x k ω) - z k ω‖ ^ 2 ∂μ +
      (a * τ k * (L1 a Lf Lg Ldf Ldg * ∫ ω, ‖ybar P (x k ω) (z k ω) β - x k ω‖ ^ 2 ∂μ +
        L2 Lg Ldf * ∫ ω, ‖g (x k ω) - u k ω‖ ^ 2 ∂μ) +
        a ^ 2 * τ k ^ 2 * σJ ^ 2 * σs ^ 2)) := by
  have haτ_pos : ∀ k, 0 < a * τ k := fun k => mul_pos ha (hτpos k)
  have hg_cont : Continuous g := hA2.contDiff_g.continuous
  have hgradF_cont : Continuous (gradF f g) := nasa_gradF_cont f g hA2.contDiff_f hA2.contDiff_g
  let d : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => ybar P (x k ω) (z k ω) β - x k ω
  let v : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω => (ContinuousLinearMap.adjoint (J (k + 1) ω)) (s (k + 1) ω)
  let barv : ℕ → Ω → EuclideanSpace ℝ (Fin n) :=
    fun k ω => (ContinuousLinearMap.adjoint (fderiv ℝ g (x (k + 1) ω))) (gradient f (u k ω))
  let ΔF : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => barv k ω - v k ω
  let e : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => gradF f g (x k ω) - z k ω
  have hd_sq_int : ∀ k, Integrable (fun ω => ‖d k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hd_memLp k).aestronglyMeasurable).mp (hd_memLp k)
  have hgx_memLp : ∀ k, MemLp (fun ω => g (x k ω)) 2 μ := fun k =>
    nasa_memLp_of_lip μ hA2.Lg_nonneg hg_cont hA2.lip_g (hx_memLp k)
  have hgradF_memLp : ∀ k, MemLp (fun ω => gradF f g (x k ω)) 2 μ := fun k => by
    have hLF_nn : 0 ≤ LgradF Lf Lg Ldf Ldg := by
      unfold LgradF
      have := hA2.Lf_nonneg; have := hA2.Lg_nonneg; have := hA2.Ldf_nonneg; have := hA2.Ldg_nonneg
      positivity
    exact nasa_memLp_of_lip μ hLF_nn hgradF_cont
      (fun a' b' => lemma_2 f g Lf Lg Ldf Ldg hA2 a' b') (hx_memLp k)
  have he_memLp : ∀ k, MemLp (e k) 2 μ := fun k => (hgradF_memLp k).sub (hz_memLp k)
  have he_sq_int : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (he_memLp k).aestronglyMeasurable).mp (he_memLp k)
  have hgu_diff_sq_int : ∀ k, Integrable (fun ω => ‖g (x k ω) - u k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm ((hgx_memLp k).sub (hu_memLp k)).aestronglyMeasurable).mp
      ((hgx_memLp k).sub (hu_memLp k))
  have hΔF_memLp : ∀ k, MemLp (ΔF k) 2 μ := fun k => (hbarv_memLp k).sub (hv_memLp k)
  have hΔF_sq_int : ∀ k, Integrable (fun ω => ‖ΔF k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hΔF_memLp k).aestronglyMeasurable).mp (hΔF_memLp k)
  refine ⟨he_sq_int, fun k => ?_⟩
  let δk : Ω → EuclideanSpace ℝ (Fin n) := fun ω =>
    (1 - a * τ k) • (gradF f g (x (k + 1) ω) - gradF f g (x k ω)) +
      (a * τ k) • (gradF f g (x (k + 1) ω) - barv k ω)
  have hδ_sm : StronglyMeasurable[ℱ k] δk := by
    have h1 : StronglyMeasurable[ℱ k]
        (fun ω => (1 - a * τ k) • (gradF f g (x (k + 1) ω) - gradF f g (x k ω))) :=
      ((hgradF_cont.comp_stronglyMeasurable (hx_succ_sm k)).sub
        (hgradF_cont.comp_stronglyMeasurable (hA1.adapted_x k))).const_smul (1 - a * τ k)
    have h2 : StronglyMeasurable[ℱ k]
        (fun ω => (a * τ k) • (gradF f g (x (k + 1) ω) - barv k ω)) :=
      ((hgradF_cont.comp_stronglyMeasurable (hx_succ_sm k)).sub (hbarv_sm k)).const_smul (a * τ k)
    exact h1.add h2
  have hδ_memLp : MemLp δk 2 μ := by
    have h1 : MemLp (fun ω => (1 - a * τ k) • (gradF f g (x (k + 1) ω) - gradF f g (x k ω))) 2 μ :=
      ((hgradF_memLp (k + 1)).sub (hgradF_memLp k)).const_smul (1 - a * τ k)
    have h2 : MemLp (fun ω => (a * τ k) • (gradF f g (x (k + 1) ω) - barv k ω)) 2 μ :=
      ((hgradF_memLp (k + 1)).sub (hbarv_memLp k)).const_smul (a * τ k)
    exact h1.add h2
  let w : Ω → EuclideanSpace ℝ (Fin n) := fun ω => (1 - a * τ k) • e k ω + δk ω
  have hw_sm : StronglyMeasurable[ℱ k] w := by
    have h1 : StronglyMeasurable[ℱ k] (fun ω => (1 - a * τ k) • e k ω) :=
      ((hgradF_cont.comp_stronglyMeasurable (hA1.adapted_x k)).sub (hA1.adapted_z k)).const_smul (1 - a * τ k)
    exact h1.add hδ_sm
  have hw_memLp : MemLp w 2 μ := by
    have h1 : MemLp (fun ω => (1 - a * τ k) • e k ω) 2 μ := (he_memLp k).const_smul (1 - a * τ k)
    exact h1.add hδ_memLp
  have hw_sq_int : Integrable (fun ω => ‖w ω‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm hw_memLp.aestronglyMeasurable).mp hw_memLp
  have horth := nasa_integral_inner_eq_zero (ℱ.le k) μ hw_sm hw_memLp (hΔF_memLp k) (hΔF_ce0 k)
  have he_decomp : ∀ ω, e (k + 1) ω = w ω + (a * τ k) • ΔF k ω := fun ω => by
    simp only [e, w, δk, ΔF]
    rw [(hrun ω).step_z k]
    exact nasa_e_decomp_alg (a * τ k) (gradF f g (x k ω)) (gradF f g (x (k + 1) ω))
      (z k ω) (barv k ω) (v k ω)
  have hexp : ∀ ω, ‖e (k + 1) ω‖ ^ 2 =
      ‖w ω‖ ^ 2 + 2 * (a * τ k) * ⟪w ω, ΔF k ω⟫ + (a * τ k) ^ 2 * ‖ΔF k ω‖ ^ 2 := fun ω => by
    rw [he_decomp ω, norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_of_nonneg (haτ_pos k).le, mul_pow]
    ring
  have h12_int : Integrable (fun ω => ‖w ω‖ ^ 2 + 2 * (a * τ k) * ⟪w ω, ΔF k ω⟫) μ :=
    hw_sq_int.add (horth.1.const_mul _)
  have he_int_eq : ∫ ω, ‖e (k + 1) ω‖ ^ 2 ∂μ =
      ∫ ω, ‖w ω‖ ^ 2 ∂μ + (a * τ k) ^ 2 * ∫ ω, ‖ΔF k ω‖ ^ 2 ∂μ := by
    simp_rw [hexp]
    rw [integral_add h12_int ((hΔF_sq_int k).const_mul _),
      integral_add hw_sq_int (horth.1.const_mul _),
      integral_const_mul, horth.2, mul_zero, add_zero, integral_const_mul]
  have hw_pt : ∀ ω, ‖w ω‖ ^ 2 ≤
      (1 - a * τ k) * ‖e k ω‖ ^ 2 +
        a * τ k * (L1 a Lf Lg Ldf Ldg * ‖d k ω‖ ^ 2 + L2 Lg Ldf * ‖g (x k ω) - u k ω‖ ^ 2) := fun ω => by
    have hw_eq : w ω = (1 - a * τ k) • e k ω + (a * τ k) • ((a * τ k)⁻¹ • δk ω) := by
      simp only [w, smul_smul, mul_inv_cancel₀ (haτ_pos k).ne', one_smul]
    rw [hw_eq]
    have hcvx := nasa_sq_norm_convex (e k ω) ((a * τ k)⁻¹ • δk ω) (haτ_pos k).le (haτ_le1 k)
    have hdb0 : ‖(a * τ k)⁻¹ • δk ω‖ ^ 2 ≤
        L1 a Lf Lg Ldf Ldg * ‖d k ω‖ ^ 2 + L2 Lg Ldf * ‖g (x k ω) - u k ω‖ ^ 2 :=
      nasa_delta_bound f g Lf Lg Ldf Ldg hA2 a (τ k) ha (hτpos k) (hτ_one k) (haτ_le1 k)
        (x k ω) (x (k + 1) ω) (d k ω) (u k ω) ((hrun ω).step_x k)
    have hdb := mul_le_mul_of_nonneg_left hdb0 (haτ_pos k).le
    linarith only [hcvx, hdb]
  have hterm2_int : Integrable (fun ω =>
      a * τ k * (L1 a Lf Lg Ldf Ldg * ‖d k ω‖ ^ 2 + L2 Lg Ldf * ‖g (x k ω) - u k ω‖ ^ 2)) μ :=
    (((hd_sq_int k).const_mul _).add ((hgu_diff_sq_int k).const_mul _)).const_mul _
  have hrhs_int : Integrable (fun ω => (1 - a * τ k) * ‖e k ω‖ ^ 2 +
      a * τ k * (L1 a Lf Lg Ldf Ldg * ‖d k ω‖ ^ 2 + L2 Lg Ldf * ‖g (x k ω) - u k ω‖ ^ 2)) μ :=
    ((he_sq_int k).const_mul _).add hterm2_int
  have hw_int_le := integral_mono hw_sq_int hrhs_int hw_pt
  rw [integral_add ((he_sq_int k).const_mul _) hterm2_int,
    integral_const_mul, integral_const_mul,
    integral_add ((hd_sq_int k).const_mul _) ((hgu_diff_sq_int k).const_mul _),
    integral_const_mul, integral_const_mul] at hw_int_le
  have hΔ_le : (a * τ k) ^ 2 * ∫ ω, ‖ΔF k ω‖ ^ 2 ∂μ ≤ a ^ 2 * τ k ^ 2 * σJ ^ 2 * σs ^ 2 := by
    have h1 := mul_le_mul_of_nonneg_left (hΔF_sq_le k) (sq_nonneg (a * τ k))
    have h2 : (a * τ k) ^ 2 * (σJ ^ 2 * σs ^ 2) = a ^ 2 * τ k ^ 2 * σJ ^ 2 * σs ^ 2 := by ring
    linarith only [h1, h2]
  linarith only [he_int_eq, hw_int_le, hΔ_le]

private lemma nasa_unroll_scalar (a : ℝ) (τ E B : ℕ → ℝ) (hτ0 : τ 0 = 1 / a) (ha : 0 < a)
    (haτ : ∀ k, 1 ≤ k → a * τ k ≤ 1 / Real.sqrt 2)
    (hstep : ∀ k, E (k + 1) ≤ (1 - a * τ k) * E k + B k) :
    (∀ k, 1 ≤ k → 0 < Gamma a τ k) ∧
    (∀ k, 1 ≤ k → E k / Gamma a τ k ≤ ∑ j ∈ Finset.range k, B j / Gamma a τ (j + 1)) := by
  obtain ⟨hGamma1, hGamma_succ, hGamma_pos⟩ := nasa_Gamma_props a τ hτ0 haτ
  have haτ0 : a * τ 0 = 1 := by rw [hτ0, mul_one_div_cancel ha.ne']
  refine ⟨hGamma_pos, ?_⟩
  intro k hk
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  induction j with
  | zero =>
    rw [hGamma1, div_one, Finset.sum_range_one, hGamma1, div_one]
    have h0 := hstep 0
    rw [haτ0, sub_self, zero_mul] at h0
    linarith
  | succ j ih =>
    have hG_pos := hGamma_pos (j + 2) (by omega)
    have hGj_pos := hGamma_pos (j + 1) (by omega)
    have hdiv := div_le_div_of_nonneg_right (hstep (j + 1)) hG_pos.le
    rw [add_div] at hdiv
    rw [Finset.sum_range_succ]
    have hcancel : (1 - a * τ (j + 1)) * E (j + 1) / Gamma a τ (j + 2) =
        E (j + 1) / Gamma a τ (j + 1) := by
      rw [hGamma_succ (j + 1) (by omega)]
      have hne : 1 - a * τ (j + 1) ≠ 0 := by
        have h1 : a * τ (j + 1) ≤ 1 / Real.sqrt 2 := haτ (j + 1) (by omega)
        have hsqrt : (1 : ℝ) < Real.sqrt 2 := by rw [Real.lt_sqrt zero_le_one]; norm_num
        have hlt : 1 / Real.sqrt 2 < 1 := by rw [div_lt_one (by positivity)]; exact hsqrt
        linarith
      field_simp [hne, hGj_pos.ne']
    rw [hcancel] at hdiv
    linarith only [hdiv, ih (by omega)]

/-! ### Section 5: Main theorem -/

theorem solution {n m : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℕ mΩ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Lf Lg Ldf Ldg : ℝ) (hA2 : Assumption2 f g Lf Lg Ldf Ldg)
    (hF_bdd : BddBelow ((fun x => f (g x)) '' X))
    (a b β : ℝ) (τ : ℕ → ℝ) (x0 z0 : EuclideanSpace ℝ (Fin n)) (u0 : EuclideanSpace ℝ (Fin m))
    (x z : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (u G s : ℕ → Ω → EuclideanSpace ℝ (Fin m))
    (J : ℕ → Ω → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m)))
    (hrun : IsStochRun X P a b β τ x0 z0 u0 x z u G s J)
    (σG σJ σs : ℝ) (hA1 : Assumption1 μ ℱ f g x z u G s J σG σJ σs)
    (c γ : ℝ) (hc : 0 < c) (hγ : 0 < γ) (hcβ : c ≤ a * β) (hcγ : 2 * c ≤ γ * b)
    (h316 : Lg ^ 2 * (a * Ldf + γ) ^ 2 ≤ 2 * (a * β - c) * (γ * b - 2 * c))
    (hτ_one : ∀ k, τ k ≤ 1) (hbτ : ∀ k, b * τ k ≤ 1) (hτ0 : τ 0 = 1 / a)
    (cbar : ℝ) (hcbar : 0 < cbar)
    (h330 : ∀ k N : ℕ, 1 ≤ N →
      ∑ i ∈ Finset.Icc (k + 1) N, τ i * Gamma a τ i ≤ cbar * Gamma a τ (k + 1))
    (haτ : ∀ k, 1 ≤ k → a * τ k ≤ 1 / Real.sqrt 2) :
    ∀ N : ℕ, 2 ≤ N →
      (∀ k, Integrable (fun ω => ‖gradF f g (x k ω) - z k ω‖ ^ 2) μ) ∧
      ∑ k ∈ Finset.Icc 1 N, τ k * ∫ ω, ‖gradF f g (x k ω) - z k ω‖ ^ 2 ∂μ ≤
        a * cbar * (1 / c * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) *
            sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 + 2 * a * σJ ^ 2 * σs ^ 2) *
          (∑ k ∈ Finset.range N, τ k ^ 2)
        + a * cbar / c * max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf) * W P f g X a γ β x0 z0 u0 := by
  have hΩ : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h0 : μ Set.univ = 0 := by simp [Measure.eq_zero_of_isEmpty μ]
    simp at h0
  obtain ⟨ω₀⟩ := hΩ
  have ha : 0 < a := (hrun ω₀).a_pos
  have hτpos : ∀ k, 0 < τ k := (hrun ω₀).τ_pos
  have hτle : ∀ k, τ k ≤ 1 / a := (hrun ω₀).τ_le
  have haτ_pos : ∀ k, 0 < a * τ k := fun k => mul_pos ha (hτpos k)
  have haτ_le1 : ∀ k, a * τ k ≤ 1 := fun k => by
    have := mul_le_mul_of_nonneg_left (hτle k) ha.le
    rwa [mul_one_div_cancel ha.ne'] at this
  have hg_cont : Continuous g := hA2.contDiff_g.continuous
  obtain ⟨hx_succ_sm, hbarv_sm, hx_memLp, hz_memLp, hu_memLp, hd_memLp, hv_memLp, hbarv_memLp,
      hΔF_ce0, hΔF_sq_le, hr_int, hr_sum_le⟩ :=
    nasa_prop1_bundle μ ℱ X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 a b β τ x0 z0 u0
      x z u G s J hrun σG σJ σs hA1 γ hγ hτ_one hτ0
  obtain ⟨he_sq_int, he_step⟩ :=
    nasa_e_step_bound μ ℱ X P f g Lf Lg Ldf Ldg hA2 a b β τ x0 z0 u0
      x z u G s J hrun σG σJ σs hA1 ha hτpos hτ_one haτ_le1
      hx_succ_sm hbarv_sm hx_memLp hz_memLp hu_memLp hd_memLp hv_memLp hbarv_memLp
      hΔF_ce0 hΔF_sq_le
  let d : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => ybar P (x k ω) (z k ω) β - x k ω
  let e : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun k ω => gradF f g (x k ω) - z k ω
  let rFn : ℕ → Ω → ℝ := fun k ω =>
    rTerm P f g a b γ β Lf Lg Ldf Ldg τ (fun i => x i ω) (fun i => z i ω)
      (fun i => u i ω) (fun i => G i ω) (fun i => s i ω) (fun i => J i ω) k
  let B : ℕ → ℝ := fun k =>
    a * τ k * (L1 a Lf Lg Ldf Ldg * ∫ ω, ‖d k ω‖ ^ 2 ∂μ +
      L2 Lg Ldf * ∫ ω, ‖g (x k ω) - u k ω‖ ^ 2 ∂μ) +
    a ^ 2 * τ k ^ 2 * σJ ^ 2 * σs ^ 2
  obtain ⟨hGamma_pos, he_unroll⟩ :=
    nasa_unroll_scalar a τ (fun k => ∫ ω, ‖e k ω‖ ^ 2 ∂μ) B hτ0 ha haτ he_step
  have hd_sq_int : ∀ k, Integrable (fun ω => ‖d k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm (hd_memLp k).aestronglyMeasurable).mp (hd_memLp k)
  have hgx_memLp : ∀ k, MemLp (fun ω => g (x k ω)) 2 μ := fun k =>
    nasa_memLp_of_lip μ hA2.Lg_nonneg hg_cont hA2.lip_g (hx_memLp k)
  have hgu_diff_sq_int : ∀ k, Integrable (fun ω => ‖g (x k ω) - u k ω‖ ^ 2) μ := fun k =>
    (memLp_two_iff_integrable_sq_norm ((hgx_memLp k).sub (hu_memLp k)).aestronglyMeasurable).mp
      ((hgx_memLp k).sub (hu_memLp k))
  have hB_nn : ∀ k, 0 ≤ B k := fun k => by
    have hL1_nn : 0 ≤ L1 a Lf Lg Ldf Ldg := by unfold L1; positivity
    have hL2_nn : 0 ≤ L2 Lg Ldf := by unfold L2; positivity
    have hd_nn : 0 ≤ ∫ ω, ‖d k ω‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have hgu_nn : 0 ≤ ∫ ω, ‖g (x k ω) - u k ω‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have h1 : 0 ≤ a * τ k * (L1 a Lf Lg Ldf Ldg * ∫ ω, ‖d k ω‖ ^ 2 ∂μ +
        L2 Lg Ldf * ∫ ω, ‖g (x k ω) - u k ω‖ ^ 2 ∂μ) :=
      mul_nonneg (haτ_pos k).le (add_nonneg (mul_nonneg hL1_nn hd_nn) (mul_nonneg hL2_nn hgu_nn))
    have h2 : 0 ≤ a ^ 2 * τ k ^ 2 * σJ ^ 2 * σs ^ 2 := by positivity
    linarith
  intro N hN
  refine ⟨he_sq_int, ?_⟩
  have hsum1 : ∑ k ∈ Finset.Icc 1 N, τ k * ∫ ω, ‖e k ω‖ ^ 2 ∂μ ≤
      ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range k,
        (τ k * Gamma a τ k) * (B j / Gamma a τ (j + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hGk := hGamma_pos k hk.1
    have hmul := mul_le_mul_of_nonneg_left (he_unroll k hk.1) (mul_nonneg (hτpos k).le hGk.le)
    rw [Finset.mul_sum] at hmul
    have hlhs : τ k * Gamma a τ k * ((∫ ω, ‖e k ω‖ ^ 2 ∂μ) / Gamma a τ k) =
        τ k * ∫ ω, ‖e k ω‖ ^ 2 ∂μ := by field_simp [hGk.ne']
    linarith
  have hswap : ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.range k,
        (τ k * Gamma a τ k) * (B j / Gamma a τ (j + 1)) =
      ∑ j ∈ Finset.range N, (∑ k ∈ Finset.Icc (j + 1) N, τ k * Gamma a τ k) *
        (B j / Gamma a τ (j + 1)) := by
    have h1 : ∀ k ∈ Finset.Icc 1 N,
        ∑ j ∈ Finset.range k, (τ k * Gamma a τ k) * (B j / Gamma a τ (j + 1)) =
          ∑ j ∈ Finset.range N, if j < k then (τ k * Gamma a τ k) * (B j / Gamma a τ (j + 1)) else 0 := by
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    rw [Finset.sum_mul, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_Icc, Finset.mem_filter]
    omega
  have hsum2 : ∑ j ∈ Finset.range N, (∑ k ∈ Finset.Icc (j + 1) N, τ k * Gamma a τ k) *
        (B j / Gamma a τ (j + 1)) ≤
      ∑ j ∈ Finset.range N, cbar * B j := by
    apply Finset.sum_le_sum
    intro j _
    have hG := hGamma_pos (j + 1) (by omega)
    have hle := mul_le_mul_of_nonneg_right (h330 j N (by omega)) (div_nonneg (hB_nn j) hG.le)
    have hcancel : cbar * Gamma a τ (j + 1) * (B j / Gamma a τ (j + 1)) = cbar * B j := by
      field_simp [hG.ne']
    linarith
  have hL4_exp : ∑ j ∈ Finset.range N, τ j *
        (∫ ω, ‖d j ω‖ ^ 2 ∂μ + ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ) ≤
      1 / c * (W P f g X a γ β x0 z0 u0 +
        sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ j ∈ Finset.range N, τ j ^ 2) := by
    have hpt : ∀ ω, ∑ j ∈ Finset.range N, τ j * (‖d j ω‖ ^ 2 + ‖g (x j ω) - u j ω‖ ^ 2) ≤
        1 / c * (W P f g X a γ β x0 z0 u0 + ∑ j ∈ Finset.range N, rFn j ω) := by
      intro ω
      have hL4 := lemma_4 X hX_cl hX_cvx P hP f g Lf Lg Ldf Ldg hA2 hF_bdd a b β τ x0 z0 u0
        (fun i => x i ω) (fun i => z i ω) (fun i => u i ω) (fun i => G i ω) (fun i => s i ω)
        (fun i => J i ω) (hrun ω) c γ hc hγ hcβ hcγ h316 hτ_one hbτ N (by omega)
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
      linarith
    have hterm_int : ∀ j, Integrable (fun ω => τ j * (‖d j ω‖ ^ 2 + ‖g (x j ω) - u j ω‖ ^ 2)) μ :=
      fun j => ((hd_sq_int j).add (hgu_diff_sq_int j)).const_mul (τ j)
    have hintL : Integrable (fun ω => ∑ j ∈ Finset.range N, τ j * (‖d j ω‖ ^ 2 + ‖g (x j ω) - u j ω‖ ^ 2)) μ :=
      integrable_finsetSum _ fun j _ => hterm_int j
    have hintR : Integrable (fun ω => 1 / c * (W P f g X a γ β x0 z0 u0 + ∑ j ∈ Finset.range N, rFn j ω)) μ :=
      ((integrable_const _).add (integrable_finsetSum _ fun j _ => hr_int j)).const_mul _
    have hmono := integral_mono hintL hintR hpt
    have hlhs_eq : ∫ ω, ∑ j ∈ Finset.range N, τ j * (‖d j ω‖ ^ 2 + ‖g (x j ω) - u j ω‖ ^ 2) ∂μ =
        ∑ j ∈ Finset.range N, τ j * (∫ ω, ‖d j ω‖ ^ 2 ∂μ + ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ) := by
      rw [integral_finsetSum _ fun j _ => hterm_int j]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_add (hd_sq_int j) (hgu_diff_sq_int j)]
    have hrhs_eq : ∫ ω, 1 / c * (W P f g X a γ β x0 z0 u0 + ∑ j ∈ Finset.range N, rFn j ω) ∂μ =
        1 / c * (W P f g X a γ β x0 z0 u0 + ∑ j ∈ Finset.range N, ∫ ω, rFn j ω ∂μ) := by
      rw [integral_const_mul, integral_add (integrable_const _)
          (integrable_finsetSum _ fun j _ => hr_int j),
        integral_finsetSum _ fun j _ => hr_int j]
      simp only [integral_const, probReal_univ, one_smul]
      rfl
    rw [hlhs_eq, hrhs_eq] at hmono
    have hrsum := hr_sum_le N (by omega)
    exact hmono.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  set Lmax := max (L1 a Lf Lg Ldf Ldg) (L2 Lg Ldf)
  have hLmax_nn : 0 ≤ Lmax := (show 0 ≤ L2 Lg Ldf by unfold L2; positivity).trans (le_max_right _ _)
  have hsum3 : ∑ j ∈ Finset.range N, cbar * B j ≤
      a * cbar * Lmax * (∑ j ∈ Finset.range N, τ j *
          (∫ ω, ‖d j ω‖ ^ 2 ∂μ + ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ)) +
        a ^ 2 * cbar * σJ ^ 2 * σs ^ 2 * ∑ j ∈ Finset.range N, τ j ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have hd_nn : 0 ≤ ∫ ω, ‖d j ω‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have hgu_nn : 0 ≤ ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    have h1 : L1 a Lf Lg Ldf Ldg * ∫ ω, ‖d j ω‖ ^ 2 ∂μ + L2 Lg Ldf * ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ ≤
        Lmax * (∫ ω, ‖d j ω‖ ^ 2 ∂μ + ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ) := by
      have hm1 : L1 a Lf Lg Ldf Ldg * ∫ ω, ‖d j ω‖ ^ 2 ∂μ ≤ Lmax * ∫ ω, ‖d j ω‖ ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hd_nn
      have hm2 : L2 Lg Ldf * ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ ≤ Lmax * ∫ ω, ‖g (x j ω) - u j ω‖ ^ 2 ∂μ :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hgu_nn
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hcbar.le (haτ_pos j).le)
    simp only [B]
    linarith
  have hchain : ∑ k ∈ Finset.Icc 1 N, τ k * ∫ ω, ‖e k ω‖ ^ 2 ∂μ ≤
      a * cbar * Lmax * (1 / c * (W P f g X a γ β x0 z0 u0 +
        sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ j ∈ Finset.range N, τ j ^ 2)) +
      a ^ 2 * cbar * σJ ^ 2 * σs ^ 2 * ∑ j ∈ Finset.range N, τ j ^ 2 := by
    have h4 := mul_le_mul_of_nonneg_left hL4_exp (mul_nonneg (mul_nonneg ha.le hcbar.le) hLmax_nn)
    linarith
  have hSτ_nn : 0 ≤ ∑ j ∈ Finset.range N, τ j ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hslack : 0 ≤ a ^ 2 * cbar * σJ ^ 2 * σs ^ 2 * ∑ j ∈ Finset.range N, τ j ^ 2 := by positivity
  have hrew : a * cbar * Lmax * (1 / c * (W P f g X a γ β x0 z0 u0 +
          sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 * ∑ j ∈ Finset.range N, τ j ^ 2)) +
        a ^ 2 * cbar * σJ ^ 2 * σs ^ 2 * ∑ j ∈ Finset.range N, τ j ^ 2 +
        a ^ 2 * cbar * σJ ^ 2 * σs ^ 2 * ∑ j ∈ Finset.range N, τ j ^ 2 =
      a * cbar * (1 / c * Lmax * sigmaHatSq a b γ β Lf Lg Ldf Ldg σG σJ σs z0 +
          2 * a * σJ ^ 2 * σs ^ 2) * (∑ k ∈ Finset.range N, τ k ^ 2) +
        a * cbar / c * Lmax * W P f g X a γ β x0 z0 u0 := by ring
  linarith
