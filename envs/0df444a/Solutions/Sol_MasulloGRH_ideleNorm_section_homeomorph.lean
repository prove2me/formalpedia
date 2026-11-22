-- Prove2me | solution 1 for MasulloGRH.ideleNorm_section_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T12:23:53.709423+00:00
-- url     : https://prove2.me/submissions/13227996-ba49-44aa-9f68-20dd312ce99a

import Mathlib
import Definitions.Def_MasulloGRH_IdeleNorm

open NumberField IsDedekindDomain
open scoped NNReal

set_option autoImplicit false

namespace Sol_MasulloGRH_ideleNorm_section_homeomorph

open MasulloGRH

variable {F : Type*} [Field F] [NumberField F]

/-- The finite component at `v` of an idele times that of its inverse is `1`. -/
lemma fin_mul_inv (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    (g : AdeleRing (𝓞 F) F).2 v * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.2 v) h
  exact h2

/-- The component at an infinite place `w` of an idele times that of its inverse is `1`. -/
lemma inf_mul_inv (g : IdeleGroup F) (w : InfinitePlace F) :
    (g : AdeleRing (𝓞 F) F).1 w * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := by
  have h : (g : AdeleRing (𝓞 F) F) * ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F) = 1 := g.mul_inv
  have h2 := congrArg (fun a : AdeleRing (𝓞 F) F => a.1 w) h
  exact h2

/-- If the `v`-components of an idele and of its inverse are both `v`-integral, the `v`-component
has norm `1`. -/
lemma norm_fin_eq_one_of_mem (g : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F))
    (h1 : (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F)
    (h2 : ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) :
    ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have a1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h1)
  have a2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    Valued.toNormedField.norm_le_one_iff.mpr ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp h2)
  have hm : ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, fin_mul_inv, norm_one]
  refine le_antisymm a1 ?_
  calc (1 : ℝ) = ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ := hm.symm
    _ ≤ ‖(g : AdeleRing (𝓞 F) F).2 v‖ * 1 := mul_le_mul_of_nonneg_left a2 (norm_nonneg _)
    _ = _ := mul_one _

/-- All but finitely many finite components of an idele have norm `1`. -/
lemma finite_mulSupport_fin (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  have h1 : ∀ᶠ v in Filter.cofinite,
      (g : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := (g : AdeleRing (𝓞 F) F).2.2
  have h2 : ∀ᶠ v in Filter.cofinite,
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F :=
    ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2.2
  have h3 := h1.and h2
  rw [Filter.eventually_cofinite] at h3
  refine h3.subset ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  simp only [Set.mem_ofPred_eq]
  intro h
  exact hv (norm_fin_eq_one_of_mem g v h.1 h.2)

/-- The idelic norm is multiplicative. -/
lemma ideleNorm_mul (g h : IdeleGroup F) : ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F, ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := fun w => rfl
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F), ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := fun v => rfl
  simp only [e1, e2, norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (finite_mulSupport_fin g) (finite_mulSupport_fin h)]
  ring

/-- The idelic norm is positive. -/
lemma ideleNorm_pos (g : IdeleGroup F) : 0 < ideleNorm g := by
  unfold ideleNorm
  apply mul_pos
  · refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr ?_) _
    intro h0
    have := inf_mul_inv g w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  · refine finprod_induction (0 < ·) zero_lt_one (fun _ _ => mul_pos) fun v => norm_pos_iff.mpr ?_
    intro h0
    have := fin_mul_inv g v
    rw [h0, zero_mul] at this
    exact zero_ne_one this

/-- The finite adeles that are integral at every place form an open set. -/
lemma isOpen_integral :
    IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

/-- The idelic norm is continuous at `1`: on the open neighbourhood of ideles `g` such that `g` and
`g⁻¹` are integral at all finite places it equals the (continuous) archimedean part. -/
lemma continuousAt_ideleNorm_one : ContinuousAt (ideleNorm (F := F)) 1 := by
  let U : Set (FiniteAdeleRing (𝓞 F) F) := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  have hU : IsOpen U := isOpen_integral
  have h1 : (1 : FiniteAdeleRing (𝓞 F) F) ∈ U := fun v => (v.adicCompletionIntegers F).one_mem
  have hval : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).2) :=
    continuous_snd.comp Units.continuous_val
  have hinv : Continuous (fun g : IdeleGroup F => ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2) :=
    continuous_snd.comp Units.continuous_coe_inv
  have hfst : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).1) :=
    continuous_fst.comp Units.continuous_val
  have hw : ∀ w : InfinitePlace F, Continuous (fun a : InfiniteAdeleRing F => a w) :=
    fun w => continuous_apply w
  have hInf : Continuous (fun g : IdeleGroup F =>
      ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult) :=
    continuous_finsetProd _ fun w _ => ((hw w).comp hfst).norm.pow _
  refine hInf.continuousAt.congr ?_
  filter_upwards [hval.continuousAt (hU.mem_nhds h1), hinv.continuousAt (hU.mem_nhds h1)]
    with g hg hginv
  unfold ideleNorm
  rw [finprod_eq_one_of_forall_eq_one (fun v => norm_fin_eq_one_of_mem g v (hg v) (hginv v)),
    mul_one]

/-- The idelic norm is continuous. -/
lemma continuous_ideleNorm : Continuous (ideleNorm (F := F)) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  have h : (ideleNorm (F := F)) = fun g => ideleNorm g₀ * ideleNorm (g₀⁻¹ * g) := by
    funext g
    rw [← ideleNorm_mul, mul_inv_cancel_left]
  rw [h]
  refine continuousAt_const.mul ?_
  have hm : ContinuousAt (fun g : IdeleGroup F => g₀⁻¹ * g) g₀ :=
    (continuous_const.mul continuous_id).continuousAt
  refine ContinuousAt.comp (g := ideleNorm) ?_ hm
  rw [inv_mul_cancel]
  exact continuousAt_ideleNorm_one

end Sol_MasulloGRH_ideleNorm_section_homeomorph

open MasulloGRH Sol_MasulloGRH_ideleNorm_section_homeomorph

theorem solution (F : Type*) [Field F] [NumberField F]
    (s : ℝ≥0ˣ →* IdeleGroup F) (hs : Continuous s)
    (hsec : ∀ t : ℝ≥0ˣ, ideleNorm (s t) = ((t : ℝ≥0) : ℝ)) :
    ∃ θ : (ℝ≥0ˣ × {g : IdeleGroup F // ideleNorm g = 1}) ≃ₜ IdeleGroup F,
      ∀ (t : ℝ≥0ˣ) (g : {g : IdeleGroup F // ideleNorm g = 1}),
        θ (t, g) = s t * (g : IdeleGroup F) := by
  -- the idelic norm as a map to the group of positive reals
  let N : IdeleGroup F → ℝ≥0ˣ := fun g =>
    Units.mk0 (⟨ideleNorm g, (ideleNorm_pos g).le⟩ : ℝ≥0)
      (fun h => (ideleNorm_pos g).ne' (congrArg NNReal.toReal h))
  have hNval : ∀ g, (((N g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = ideleNorm g := fun g => rfl
  have hNcont : Continuous N := by
    rw [Units.isEmbedding_val₀.continuous_iff]
    exact continuous_ideleNorm.subtype_mk _
  have hker : ∀ g, ideleNorm ((s (N g))⁻¹ * g) = 1 := by
    intro g
    have h1 : ideleNorm (s (N g)) * ideleNorm ((s (N g))⁻¹ * g) = ideleNorm g := by
      rw [← ideleNorm_mul, mul_inv_cancel_left]
    rw [hsec, hNval] at h1
    exact mul_left_cancel₀ (ideleNorm_pos g).ne' (h1.trans (mul_one _).symm)
  refine ⟨{ toFun := fun p => s p.1 * (p.2 : IdeleGroup F)
            invFun := fun g => (N g, ⟨(s (N g))⁻¹ * g, hker g⟩)
            left_inv := ?_
            right_inv := ?_
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · rintro ⟨t, g, hg⟩
    have ht : N (s t * g) = t := by
      apply Units.ext
      apply NNReal.eq
      rw [hNval, ideleNorm_mul, hsec, hg, mul_one]
    refine Prod.ext ht (Subtype.ext ?_)
    change (s (N (s t * g)))⁻¹ * (s t * g) = g
    rw [ht, inv_mul_cancel_left]
  · intro g
    exact mul_inv_cancel_left _ _
  · exact (hs.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  · exact hNcont.prodMk (((hs.comp hNcont).inv.mul continuous_id).subtype_mk hker)
