-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.AdelicEpstein.integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/18b92bd0-100b-5564-862d-7fb247210bf4

import Definitions.Def_LanglandsTunnell_CubicInduction_AdelicEpstein
import Definitions.Def_LanglandsTunnell_CubicInduction_Growth
import Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
import Definitions.Def_NumberField_AdelicFourier
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_IdeleBox
import Definitions.Def_RatIdele_Normalizer
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_NumberField_HeightOneSpectrum
import Definitions.Def_NumberField_Completion_Finite
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import Theorems.Thm_LanglandsTunnell_CubicInduction_AdelicEpstein_exists_forall_epstein_eq_div_sub_one_add_of_pureTensor
import Theorems.Thm_LanglandsTunnell_CubicInduction_measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
import Theorems.Thm_NumberField_AdeleRing_distribHaarChar_algebraMap
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "NumberField.InfinitePlace.Completion.ext"
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor

set_option autoImplicit false

section Brick1

open MeasureTheory Set Filter
open scoped ENNReal Pointwise

namespace FundamentalDomainDomination

variable {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [MeasurableConstSMul G α]
  [Countable G] {μ : Measure α} [SMulInvariantMeasure G α μ] {F S : Set α}

omit [MeasurableConstSMul G α] [Countable G] [SMulInvariantMeasure G α μ] in

private theorem iUnion_smul_ae_eq_univ_of_ae_covers (hS : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ S) :
    (⋃ g : G, g • S : Set α) =ᵐ[μ] (univ : Set α) :=
  eventuallyEq_univ.2 <| hS.mono fun x ⟨g, hg⟩ => mem_iUnion.2 ⟨g⁻¹, ⟨g • x, hg, inv_smul_smul g x⟩⟩

private theorem setLIntegral_le_of_ae_covers (hF : IsFundamentalDomain G F μ)
    (hS : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ S) (f : α → ℝ≥0∞) (hf : ∀ (g : G) (x : α), f (g • x) = f x) :
    ∫⁻ x in F, f x ∂μ ≤ ∫⁻ x in S, f x ∂μ := by
  have hcover : (F ∩ ⋃ g : G, g • S : Set α) =ᵐ[μ] F := by
    simpa only [inter_univ] using
      (EventuallyEq.refl _ F).inter (iUnion_smul_ae_eq_univ_of_ae_covers (μ := μ) hS)
  calc ∫⁻ x in F, f x ∂μ = ∫⁻ x in F ∩ ⋃ g : G, g • S, f x ∂μ := setLIntegral_congr hcover.symm
    _ = ∫⁻ x in ⋃ g : G, (F ∩ g • S), f x ∂μ := by rw [inter_iUnion]
    _ ≤ ∑' g : G, ∫⁻ x in F ∩ g • S, f x ∂μ := lintegral_iUnion_le _ _
    _ = ∑' g : G, ∫⁻ x in g • S ∩ F, f (g⁻¹ • x) ∂μ := by
        refine tsum_congr fun g => ?_
        rw [inter_comm]
        exact lintegral_congr fun x => (hf g⁻¹ x).symm
    _ = ∫⁻ x in S, f x ∂μ := (hF.setLIntegral_eq_tsum' f S).symm

private theorem measure_le_of_ae_covers (hF : IsFundamentalDomain G F μ)
    (hS : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ S) : μ F ≤ μ S := by
  simpa only [MeasureTheory.setLIntegral_one] using
    setLIntegral_le_of_ae_covers hF hS (fun _ => 1) (fun _ _ => rfl)

private theorem integrableOn_of_norm_le_of_ae_covers {E : Type*} [NormedAddCommGroup E]
    (hF : IsFundamentalDomain G F μ) (hS : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ S) {h : α → E}
    (hh : AEStronglyMeasurable h (μ.restrict F)) (b : α → ℝ≥0∞)
    (hb : ∀ (g : G) (x : α), b (g • x) = b x) (hle : ∀ x, (‖h x‖₊ : ℝ≥0∞) ≤ b x)
    (hfin : ∫⁻ x in S, b x ∂μ < ⊤) : IntegrableOn h F μ := by
  refine ⟨hh, ?_⟩
  rw [HasFiniteIntegral]
  calc ∫⁻ x in F, (‖h x‖₊ : ℝ≥0∞) ∂μ ≤ ∫⁻ x in F, b x ∂μ := lintegral_mono fun x => hle x
    _ ≤ ∫⁻ x in S, b x ∂μ := setLIntegral_le_of_ae_covers hF hS b hb
    _ < ⊤ := hfin

end FundamentalDomainDomination

end Brick1

section Brick2

open MeasureTheory Filter Topology

namespace PoleLimit

variable {X : Type*} [MeasurableSpace X]

private theorem mul_integral_mul_add (ν : Measure X) (f : X → ℂ) (c : ℂ) (R : X → ℂ) (B : X → ℝ) (s : ℝ) (hs : s ≠ 0)
    (hf : Integrable f ν) (hR : AEStronglyMeasurable R ν) (hRB : ∀ x, ‖R x‖ ≤ B x)
    (hfB : Integrable (fun x => ‖f x‖ * B x) ν) :
    (s : ℂ) * ∫ x, f x * (c / (s : ℂ) + R x) ∂ν = c * ∫ x, f x ∂ν + (s : ℂ) * ∫ x, f x * R x ∂ν := by
  have hfR : Integrable (fun x => f x * R x) ν := by
    refine Integrable.mono' hfB (hf.aestronglyMeasurable.mul hR) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hRB x) (norm_nonneg _)
  have h1 : Integrable (fun x => f x * (c / (s : ℂ))) ν := hf.mul_const _
  have hsplit : (fun x => f x * (c / (s : ℂ) + R x)) = fun x => f x * (c / (s : ℂ)) + f x * R x := by
    funext x; ring
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
  rw [hsplit, integral_add h1 hfR, integral_mul_const]
  field_simp

private theorem norm_integral_mul_le (ν : Measure X) (f : X → ℂ) (R : X → ℂ) (B : X → ℝ) (hRB : ∀ x, ‖R x‖ ≤ B x)
    (hfB : Integrable (fun x => ‖f x‖ * B x) ν) : ‖∫ x, f x * R x ∂ν‖ ≤ ∫ x, ‖f x‖ * B x ∂ν :=
  norm_integral_le_of_norm_le hfB (Eventually.of_forall fun x => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hRB x) (norm_nonneg _))

private theorem tendsto_mul_integral_of_expansion (ν : Measure X) (f : X → ℂ) (E R : ℝ → X → ℂ) (c : ℂ) (B : X → ℝ)
    (hE : ∀ σ ∈ Set.Ioc (1 : ℝ) 2, ∀ x, E σ x = c / ((σ - 1 : ℝ) : ℂ) + R σ x)
    (hRB : ∀ σ ∈ Set.Ioc (1 : ℝ) 2, ∀ x, ‖R σ x‖ ≤ B x)
    (hRm : ∀ σ ∈ Set.Ioc (1 : ℝ) 2, AEStronglyMeasurable (R σ) ν)
    (hf : Integrable f ν) (hfB : Integrable (fun x => ‖f x‖ * B x) ν) :
    Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * ∫ x, f x * E σ x ∂ν) (𝓝[>] 1) (𝓝 (c * ∫ x, f x ∂ν)) := by
  have hmem : Set.Ioc (1 : ℝ) 2 ∈ 𝓝[>] (1 : ℝ) := Ioc_mem_nhdsGT one_lt_two
  have heq : ∀ᶠ σ in 𝓝[>] (1 : ℝ), ((σ - 1 : ℝ) : ℂ) * ∫ x, f x * E σ x ∂ν =
      c * ∫ x, f x ∂ν + ((σ - 1 : ℝ) : ℂ) * ∫ x, f x * R σ x ∂ν := by
    filter_upwards [hmem] with σ hσ
    have hs : σ - 1 ≠ 0 := (sub_pos.mpr hσ.1).ne'
    have hfun : (fun x => f x * E σ x) = fun x => f x * (c / ((σ - 1 : ℝ) : ℂ) + R σ x) :=
      funext fun x => by rw [hE σ hσ x]
    rw [hfun]
    exact mul_integral_mul_add ν f c (R σ) B (σ - 1) hs hf (hRm σ hσ) (hRB σ hσ) hfB
  refine (tendsto_congr' heq).mpr ?_
  have h0 : Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * ∫ x, f x * R σ x ∂ν) (𝓝[>] 1) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun σ => (σ - 1) * ∫ x, ‖f x‖ * B x ∂ν) ?_ ?_
    · filter_upwards [hmem] with σ hσ
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (sub_pos.mpr hσ.1)]
      exact mul_le_mul_of_nonneg_left (norm_integral_mul_le ν f (R σ) B (hRB σ hσ) hfB) (sub_pos.mpr hσ.1).le
    · have h : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] (1 : ℝ)) (𝓝 (1 - 1)) :=
        ((continuous_sub_right (1 : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
      rw [sub_self] at h
      simpa using h.mul_const (∫ x, ‖f x‖ * B x ∂ν)
  simpa using (tendsto_const_nhds (x := c * ∫ x, f x ∂ν)).add h0

end PoleLimit

end Brick2

section Brick3

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicVolume MeasureTheory
open LanglandsTunnell.CubicInduction.AdelicEpstein

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL centralScalarGL componentAt3 archPlaceComponent3 matrixSize matrixSize_nonneg archGauge3 finGauge3 gauge3 one_le_gauge3 gauge3_pos SlabL2.ideleNormDetSlab SlabL2.slabMeasure SlabL2.domainMeasure SlabL2.IsSlabDomain measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc"
namespace SlabPoleGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem continuous_det :
    Continuous (Matrix.GeneralLinearGroup.det : AdelicGL 3 (𝓞 ℚ) ℚ → 𝔸ˣ) :=
  Units.continuous_iff.2 ⟨Units.continuous_val.matrix_det, Units.continuous_coe_inv.matrix_det⟩

private theorem continuous_ideleNorm_det :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) :=
  (TateGlobal.continuous_ideleNorm ℚ).comp continuous_det

private theorem measurableSet_ideleNormDetSlab (a b : ℝ) :
    @MeasurableSet _ (NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ) (SlabL2.ideleNormDetSlab a b) := by
  letI := NumberField.AdelicHaar.glBorel (Fin 3) (𝓞 ℚ) ℚ
  haveI := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  exact continuous_ideleNorm_det.measurable measurableSet_Icc

private theorem ofReal_ne_zero' {t : ℝ} (ht : t ≠ 0) : ofReal t ≠ 0 := by
  unfold ofReal
  simpa using ht

private theorem norm_ofReal' (t : ℝ) : ‖ofReal t‖ = |t| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).dist_eq
    (ofReal t) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  have h' : InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (ofReal t) = t :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply t
  rw [h', Real.norm_eq_abs] at h
  exact h.symm

private theorem archIdele_of_ne_zero' {t : ℝ} (ht : t ≠ 0) :
    archIdele t = TateGlobal.archUnitHom Rat.infinitePlace (Units.mk0 (ofReal t) (ofReal_ne_zero' ht)) := by
  unfold archIdele
  rw [dif_neg ht]

private theorem archIdele_snd' (t : ℝ) : ((archIdele t : 𝔸ˣ) : 𝔸).2 = 1 := by
  unfold archIdele
  split_ifs
  · rfl
  · exact archCentralUnit_snd _ _

private theorem archIdele_fst_infinitePlace {t : ℝ} (ht : t ≠ 0) :
    ((archIdele t : 𝔸ˣ) : 𝔸).1 Rat.infinitePlace = ofReal t := by
  rw [archIdele_of_ne_zero' ht, TateGlobal.archUnitHom_apply, archCentralUnit_fst_self, Units.val_mk0]

private theorem archPlaceComponent3_centralScalarGL_apply (w : InfinitePlace ℚ) (z : 𝔸ˣ) (i j : Fin 3) :
    (archPlaceComponent3 ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ z) : Matrix (Fin 3) (Fin 3) w.Completion) i j =
      if i = j then (z : 𝔸).1 w else 0 := by
  show archEval ℚ w (adeleArch (𝓞 ℚ) ℚ (Matrix.scalar (Fin 3) (z : 𝔸) i j)) = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · rfl
  · rw [map_zero, map_zero]

private theorem coe_archPlaceComponent3_centralScalarGL (w : InfinitePlace ℚ) (z : 𝔸ˣ) :
    (archPlaceComponent3 ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ z) : Matrix (Fin 3) (Fin 3) w.Completion) =
      (z : 𝔸).1 w • (1 : Matrix (Fin 3) (Fin 3) w.Completion) := by
  ext i j
  rw [archPlaceComponent3_centralScalarGL_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero]

private theorem componentAt3_centralScalarGL_archIdele (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) (t : ℝ) :
    componentAt3 (𝓞 ℚ) ℚ v (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele t)) = 1 := by
  refine Units.ext ?_
  ext i j
  show finAdeleEval (𝓞 ℚ) ℚ v (adeleFin (𝓞 ℚ) ℚ (Matrix.scalar (Fin 3) ((archIdele t : 𝔸ˣ) : 𝔸) i j)) =
    (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j
  rw [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · rw [adeleFin_apply, archIdele_snd', map_one]
  · rw [map_zero, map_zero]

private theorem finGauge3_centralScalarGL_archIdele_mul (t : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    finGauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele t) * g) = finGauge3 ℚ g := by
  unfold finGauge3
  refine finprod_congr fun v => ?_
  rw [map_mul, componentAt3_centralScalarGL_archIdele, one_mul]

private theorem matrixSize_mul_le_of_coe_eq_smul {L : Type*} [NormedField L] (C K : GL (Fin 3) L) (a : L) (ha : a ≠ 0)
    (hC : (C : Matrix (Fin 3) (Fin 3) L) = a • (1 : Matrix (Fin 3) (Fin 3) L)) :
    matrixSize (C * K) ≤ max ‖a‖ ‖a‖⁻¹ * matrixSize K := by
  have hCK : ((C * K : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = a • (K : Matrix (Fin 3) (Fin 3) L) := by
    rw [Units.val_mul, hC, Matrix.smul_mul, Matrix.one_mul]
  have hCinv : ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = a⁻¹ • (1 : Matrix (Fin 3) (Fin 3) L) := by
    have h1 : (C : Matrix (Fin 3) (Fin 3) L) * ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hC, Matrix.smul_mul, Matrix.one_mul] at h1
    calc ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)
        = a⁻¹ • (a • ((C⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L)) := by rw [inv_smul_smul₀ ha]
      _ = a⁻¹ • (1 : Matrix (Fin 3) (Fin 3) L) := by rw [h1]
  have hCKinv : (((C * K)⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) =
      a⁻¹ • ((K⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
    rw [mul_inv_rev, Units.val_mul, hCinv, Matrix.mul_smul, Matrix.mul_one]
  have hm : 0 ≤ max ‖a‖ ‖a‖⁻¹ := le_max_of_le_left (norm_nonneg a)
  unfold matrixSize
  rw [hCK, hCKinv, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Matrix.smul_apply, Matrix.smul_apply, norm_smul, norm_smul, norm_inv, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

private theorem one_le_max_self_inv {s : ℝ} (hs : 0 < s) : 1 ≤ max s s⁻¹ := by
  rcases le_total 1 s with h | h
  · exact le_max_of_le_left h
  · exact le_max_of_le_right ((one_le_inv₀ hs).2 h)

private theorem
    matrixSize_archPlaceComponent3_centralScalarGL_archIdele_mul_le (w : InfinitePlace ℚ) {s : ℝ} (hs : 0 < s)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    matrixSize (archPlaceComponent3 ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g)) ≤
      max s s⁻¹ * matrixSize (archPlaceComponent3 ℚ w g) := by
  obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
  have hz : ((archIdele s : 𝔸ˣ) : 𝔸).1 Rat.infinitePlace = ofReal s := archIdele_fst_infinitePlace hs.ne'
  have hn : ‖ofReal s‖ = s := by rw [norm_ofReal', abs_of_pos hs]
  rw [map_mul]
  have h := matrixSize_mul_le_of_coe_eq_smul (archPlaceComponent3 ℚ Rat.infinitePlace
    (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s))) (archPlaceComponent3 ℚ Rat.infinitePlace g) (ofReal s)
    (ofReal_ne_zero' hs.ne') (by rw [coe_archPlaceComponent3_centralScalarGL, hz])
  rwa [hn] at h

private theorem archGauge3_centralScalarGL_archIdele_mul_le {s : ℝ} (hs : 0 < s) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    archGauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ≤ max s s⁻¹ * archGauge3 ℚ g := by
  have hm : 1 ≤ max s s⁻¹ := one_le_max_self_inv hs
  unfold archGauge3
  have hsum : ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g))
      ≤ max s s⁻¹ * ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w g) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun w _ => matrixSize_archPlaceComponent3_centralScalarGL_archIdele_mul_le w hs g
  have hS : 0 ≤ ∑ w : InfinitePlace ℚ, matrixSize (archPlaceComponent3 ℚ w g) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  nlinarith

private theorem finGauge3_nonneg (g : AdelicGL 3 (𝓞 ℚ) ℚ) : 0 ≤ finGauge3 ℚ g := by
  unfold finGauge3
  exact finprod_nonneg fun v => NNReal.coe_nonneg _

private theorem gauge3_centralScalarGL_archIdele_mul_le {s : ℝ} (hs : 0 < s) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    gauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ≤ max s s⁻¹ * gauge3 ℚ g := by
  have hm : 1 ≤ max s s⁻¹ := one_le_max_self_inv hs
  have hA := archGauge3_centralScalarGL_archIdele_mul_le hs g
  have hF := finGauge3_nonneg g
  have hG := one_le_gauge3 ℚ g
  unfold gauge3 at hG ⊢
  rw [finGauge3_centralScalarGL_archIdele_mul]
  refine max_le ?_ ?_
  · nlinarith
  · calc archGauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) * finGauge3 ℚ g
        ≤ (max s s⁻¹ * archGauge3 ℚ g) * finGauge3 ℚ g := mul_le_mul_of_nonneg_right hA hF
      _ = max s s⁻¹ * (archGauge3 ℚ g * finGauge3 ℚ g) := by ring
      _ ≤ max s s⁻¹ * max 1 (archGauge3 ℚ g * finGauge3 ℚ g) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (le_trans zero_le_one hm)

end LanglandsTunnell.CubicInduction.SlabPoleGlue

end

namespace LanglandsTunnell
namespace CubicInduction
p2m_export "LanglandsTunnell.CubicInduction" "AdelicGL globalPointsGL centralScalarGL componentAt3 archPlaceComponent3 matrixSize matrixSize_nonneg archGauge3 finGauge3 gauge3 one_le_gauge3 gauge3_pos SlabL2.ideleNormDetSlab SlabL2.slabMeasure SlabL2.domainMeasure SlabL2.IsSlabDomain measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc"
namespace SlabPoleGlue
p2m_open "LanglandsTunnell.CubicInduction LanglandsTunnell"

end LanglandsTunnell.CubicInduction.SlabPoleGlue

end Brick3

section Brick4

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Filter Topology
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.AdelicEpstein"

namespace EpsteinMeasurability

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

private theorem measurable_tsum_of_countable {α ι : Type*} [MeasurableSpace α] [Countable ι] {f : ι → α → ℂ}
    (hf : ∀ i, Measurable (f i)) : Measurable fun x => ∑' i, f i x := by
  set S : Set α := {x | ∑' i, (‖f i x‖₊ : ENNReal) ≠ ⊤} with hS_def
  have hS_iff : ∀ x, x ∈ S ↔ Summable fun i => f i x := by
    intro x
    rw [← summable_norm_iff, hS_def, Set.mem_setOf_eq, ENNReal.tsum_coe_ne_top_iff_summable,
      ← NNReal.summable_coe]
    simp only [coe_nnnorm]
  have hS : MeasurableSet S :=
    ((Measurable.ennreal_tsum fun i => (hf i).nnnorm.coe_nnreal_ennreal) (measurableSet_singleton ⊤)).compl
  have hf' : ∀ i, Measurable fun x => S.indicator (f i) x := fun i => (hf i).indicator hS
  have heq : (fun x => ∑' i, f i x) = fun x => ∑' i, S.indicator (f i) x := by
    funext x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]
    · rw [tsum_eq_zero_of_not_summable (fun h => hx ((hS_iff x).2 h))]
      simp only [Set.indicator_of_notMem hx, tsum_zero]
  have hsum : ∀ x, Summable fun i => S.indicator (f i) x := by
    intro x
    by_cases hx : x ∈ S
    · exact ((hS_iff x).1 hx).congr fun i => (Set.indicator_of_mem hx (f i)).symm
    · simp only [Set.indicator_of_notMem hx, summable_zero]
  rw [heq]
  refine measurable_of_tendsto_metrizable' (f := fun s : Finset ι => fun x => ∑ i ∈ s, S.indicator (f i) x) atTop
    (fun s => Finset.measurable_sum s fun i _ => hf' i) ?_
  rw [tendsto_pi_nhds]
  exact fun x => (hsum x).hasSum

private scoped instance : SecondCountableTopology (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  RestrictedProduct.secondCountableTopology fun v : HeightOneSpectrum (𝓞 ℚ) =>
    Valued.isOpen_valuationSubring (v.adicCompletion ℚ)

private scoped instance (v : InfinitePlace ℚ) : SecondCountableTopology v.Completion := by
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal
    Rat.isReal_infinitePlace).toHomeomorph.secondCountableTopology

private scoped instance : SecondCountableTopology (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (SecondCountableTopology ((v : InfinitePlace ℚ) → v.Completion))

private scoped instance : SecondCountableTopology 𝔸 :=
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ))

private scoped instance : SecondCountableTopology (Matrix (Fin 3) (Fin 3) 𝔸) :=
  inferInstanceAs (SecondCountableTopology (Fin 3 → Fin 3 → 𝔸))

private scoped instance : SecondCountableTopology (Matrix (Fin 3) (Fin 3) 𝔸)ᵐᵒᵖ :=
  MulOpposite.opHomeomorph.symm.secondCountableTopology

private scoped instance : SecondCountableTopology (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  Units.isEmbedding_embedProduct.isInducing.secondCountableTopology

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

private theorem continuous_ofReal : Continuous ofReal :=
  (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous

open scoped Classical in
private theorem measurable_coe_archIdele : Measurable fun t : ℝ => ((archIdele t : 𝔸ˣ) : 𝔸) := by
  have hbr : Continuous (Y := 𝔸) fun t : ℝ =>
      ((Function.update (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace (ofReal t),
        (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : 𝔸) :=
    (continuous_const.update Rat.infinitePlace continuous_ofReal).prodMk continuous_const
  have heq : (fun t : ℝ => ((archIdele t : 𝔸ˣ) : 𝔸)) = fun t : ℝ => if t = 0 then (1 : 𝔸) else
      ((Function.update (1 : InfiniteAdeleRing ℚ) Rat.infinitePlace (ofReal t),
        (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) : 𝔸) := by
    funext t
    unfold archIdele
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const hbr.measurable

private theorem continuous_vecMul_coe (ξ : Fin 3 → ℚ) (i : Fin 3) :
    Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸) i :=
  (continuous_apply i).comp (continuous_const.matrix_vecMul Units.continuous_val)

open scoped Classical in
private theorem
    measurable_of_mem_pureTensorSet {φ : 𝔸 → ℂ} (hφ : φ ∈ AdelicFourier.pureTensorSet ℚ) : Measurable φ := by
  obtain ⟨g, h, hloc, -, rfl⟩ := hφ
  have hc : Continuous (X := 𝔸) fun x => g (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x.1) * h x.2 :=
    (g.continuous.comp ((AdelicBox.continuous_ringEquiv_mixedSpace ℚ).comp continuous_fst)).mul
      (hloc.continuous.comp continuous_snd)
  exact hc.measurable

variable [MeasurableSpace Ẑˣ]
    (hmeas : @Measurable Ẑˣ 𝔸 _ (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ) fun u => ((finUnitIdele u : 𝔸ˣ) : 𝔸))
    {Φ : (Fin 3 → 𝔸) → ℂ}
    (hΦ : ∃ Φc : Fin 3 → (𝔸 → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
      Φ = fun x => ∏ i, Φc i (x i))

include hmeas in

private theorem measurable_point_apply (ξ : Fin 3 → ℚ) (i : Fin 3) :
    Measurable fun p : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × Ẑˣ => point p.1.2 p.2 p.1.1 ξ i := by
  simp only [point, Units.val_mul]
  exact ((measurable_coe_archIdele.comp measurable_fst.snd).mul (hmeas.comp measurable_snd)).mul
    ((continuous_vecMul_coe ξ i).measurable.comp measurable_fst.fst)

include hmeas hΦ in
private theorem measurable_latticeSum :
    Measurable fun p : (AdelicGL 3 (𝓞 ℚ) ℚ × ℝ) × Ẑˣ => latticeSum Φ p.1.2 p.2 p.1.1 := by
  obtain ⟨Φc, hΦc, rfl⟩ := hΦ
  simp only [latticeSum]
  exact measurable_tsum_of_countable fun ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0} =>
    Finset.measurable_prod Finset.univ fun i _ =>
      (measurable_of_mem_pureTensorSet (hΦc i)).comp (measurable_point_apply hmeas ξ.1 i)

include hmeas hΦ in

private theorem stronglyMeasurable_integral_latticeSum (du : Measure Ẑˣ) [IsFiniteMeasure du] :
    StronglyMeasurable fun p : AdelicGL 3 (𝓞 ℚ) ℚ × ℝ => ∫ u, latticeSum Φ p.2 u p.1 ∂du :=
  (measurable_latticeSum hmeas hΦ).stronglyMeasurable.integral_prod_right'

private scoped instance : SFinite scaleMeasure :=
  inferInstanceAs (SFinite ((volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal t⁻¹))

include hmeas hΦ in

private theorem stronglyMeasurable_integral_scale (du : Measure Ẑˣ) [IsFiniteMeasure du] (σ : ℝ) :
    StronglyMeasurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ t u g ∂du ∂scaleMeasure := by
  have hw : Measurable fun p : AdelicGL 3 (𝓞 ℚ) ℚ × ℝ => ((p.2 ^ (3 * σ) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_snd.pow_const _)
  exact (hw.stronglyMeasurable.mul (stronglyMeasurable_integral_latticeSum hmeas hΦ du)).integral_prod_right'

include hmeas hΦ in

private theorem stronglyMeasurable_epstein_of_continuous (du : Measure Ẑˣ) [IsFiniteMeasure du] (σ : ℝ)
    (hdet : Continuous fun g : AdelicGL 3 (𝓞 ℚ) ℚ => TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) :
    StronglyMeasurable (epstein du Φ σ) := by
  have hpref : Measurable fun g : AdelicGL 3 (𝓞 ℚ) ℚ =>
      ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (hdet.measurable.pow_const _)
  exact hpref.stronglyMeasurable.mul (stronglyMeasurable_integral_scale hmeas hΦ du σ)

end EpsteinMeasurability
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

end Brick4
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

section CentralLiftBlock

noncomputable section

namespace RationalIdeleNorm

open NumberField NumberField.AdeleRing

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

private theorem mult_ratInfinitePlace : Rat.infinitePlace.mult = 1 :=
  InfinitePlace.mult_isReal ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩

private theorem prod_infinitePlace_rat (f : InfinitePlace ℚ → ℝ) : ∏ w : InfinitePlace ℚ, f w = f Rat.infinitePlace :=
  Fintype.prod_unique f

private theorem ideleNorm_eq_norm_fst_of_snd_eq_one (a : 𝔸ˣ) (ha : (a : 𝔸).2 = 1) :
    TateGlobal.ideleNorm ℚ a = ‖(a : 𝔸).1 Rat.infinitePlace‖ := by
  rw [TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one ℚ a ha, prod_infinitePlace_rat,
    mult_ratInfinitePlace, pow_one]

private theorem ideleNorm_mul_eq_norm_fst (a u : 𝔸ˣ) (ha : (a : 𝔸).2 = 1) (harch : (u : 𝔸).1 = 1)
    (hfin : finitePartUnits (𝓞 ℚ) ℚ u ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) :
    TateGlobal.ideleNorm ℚ (a * u) = ‖(a : 𝔸).1 Rat.infinitePlace‖ := by
  rw [TateGlobal.ideleNorm_mul, ideleNorm_eq_norm_fst_of_snd_eq_one a ha,
    TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ u harch hfin, mul_one]

end RationalIdeleNorm
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

open MeasureTheory NumberField NumberField.AdelicFourier NumberField.AdelicLevel NumberField.AdelicVolume
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.LanglandsTunnell.CubicInduction"
open scoped NNReal
open LanglandsTunnell.CubicInduction.AdelicEpstein

namespace CentralLift

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

private theorem det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ) =
      Units.map (algebraMap ℚ 𝔸).toMonoidHom (Matrix.GeneralLinearGroup.det γ) := by
  ext
  exact ((algebraMap ℚ 𝔸).map_det (γ : Matrix (Fin 3) (Fin 3) ℚ)).symm

private theorem ideleNorm_det_globalPointsGL (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ)) = 1 := by
  letI : MeasurableSpace 𝔸 := borel 𝔸
  haveI : BorelSpace 𝔸 := ⟨rfl⟩
  rw [det_globalPointsGL, TateGlobal.ideleNorm, AdeleRing.distribHaarChar_algebraMap ℚ]
  simp

private theorem adelicDiag_vecMul (ξ : Fin 3 → ℚ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    adelicDiag (Matrix.vecMul ξ (γ : Matrix (Fin 3) (Fin 3) ℚ)) =
      Matrix.vecMul (adelicDiag ξ) ((globalPointsGL 3 (𝓞 ℚ) ℚ γ : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) := by
  funext i
  exact (algebraMap ℚ 𝔸).map_vecMul (γ : Matrix (Fin 3) (Fin 3) ℚ) ξ i

private theorem point_globalPointsGL_mul (t : ℝ) (u : Ẑˣ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) :
    point t u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) ξ = point t u g (Matrix.vecMul ξ (γ : Matrix (Fin 3) (Fin 3) ℚ)) := by
  funext i
  simp only [point, adelicDiag_vecMul, Matrix.vecMul_vecMul, Units.val_mul]

private theorem vecMul_ne_zero {ξ : Fin 3 → ℚ} (hξ : ξ ≠ 0) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    Matrix.vecMul ξ (γ : Matrix (Fin 3) (Fin 3) ℚ) ≠ 0 := by
  intro h
  apply hξ
  have h' :=
    congrArg (fun v => Matrix.vecMul v ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ)) h
  simpa [Matrix.vecMul_vecMul, Matrix.zero_vecMul, Matrix.vecMul_one] using h'

private def vecMulEquiv (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) :
    {ξ : Fin 3 → ℚ // ξ ≠ 0} ≃ {ξ : Fin 3 → ℚ // ξ ≠ 0} where
  toFun ξ := ⟨Matrix.vecMul ξ.1 (γ : Matrix (Fin 3) (Fin 3) ℚ), vecMul_ne_zero ξ.2 γ⟩
  invFun ξ := ⟨Matrix.vecMul ξ.1 ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 3) ℚ) : Matrix (Fin 3) (Fin 3) ℚ),
    vecMul_ne_zero ξ.2 γ⁻¹⟩
  left_inv ξ := by
    ext1
    simp [Matrix.vecMul_vecMul, Matrix.vecMul_one]
  right_inv ξ := by
    ext1
    simp [Matrix.vecMul_vecMul, Matrix.vecMul_one]

private theorem latticeSum_globalPointsGL_mul (Φ : (Fin 3 → 𝔸) → ℂ) (t : ℝ) (u : Ẑˣ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    latticeSum Φ t u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = latticeSum Φ t u g := by
  unfold latticeSum
  simp only [point_globalPointsGL_mul]
  exact (vecMulEquiv γ).tsum_eq fun ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0} => Φ (point t u g ξ.1)

private theorem epstein_globalPointsGL_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epstein du Φ σ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = epstein du Φ σ g := by
  unfold epstein
  simp only [latticeSum_globalPointsGL_mul, map_mul, TateGlobal.ideleNorm_mul, ideleNorm_det_globalPointsGL, one_mul]

private theorem ideleNorm_pow (z : 𝔸ˣ) (n : ℕ) : TateGlobal.ideleNorm ℚ (z ^ n) = TateGlobal.ideleNorm ℚ z ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero]
    have h := TateGlobal.ideleNorm_mul (F := ℚ) (1 : 𝔸ˣ) 1
    rw [mul_one] at h
    have hpos := TateGlobal.ideleNorm_pos (F := ℚ) (1 : 𝔸ˣ)
    exact mul_left_cancel₀ hpos.ne' (h.symm.trans (mul_one _).symm)
  | succ n ih => rw [pow_succ, TateGlobal.ideleNorm_mul, ih, pow_succ]

private theorem det_centralScalarGL (z : 𝔸ˣ) :
    Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z) = z ^ 3 := by
  unfold centralScalarGL
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]

private theorem ideleNorm_det_centralScalarGL_mul (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ z * g)) =
      TateGlobal.ideleNorm ℚ z ^ 3 * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) := by
  rw [map_mul, TateGlobal.ideleNorm_mul, det_centralScalarGL, ideleNorm_pow]

private theorem vecMul_scalar_mul (c : 𝔸) (v : Fin 3 → 𝔸) (M : Matrix (Fin 3) (Fin 3) 𝔸) :
    Matrix.vecMul v (Matrix.scalar (Fin 3) c * M) = fun i => c * Matrix.vecMul v M i := by
  funext i
  simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Finset.mul_sum]
  simp [Finset.sum_ite_eq, mul_comm, mul_left_comm]

private theorem point_centralScalarGL_mul (z : 𝔸ˣ) (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) :
    point t u (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) ξ = fun i => (z : 𝔸) * point t u g ξ i := by
  funext i
  have hmat : ((centralScalarGL 3 (𝓞 ℚ) ℚ z * g : AdelicGL 3 (𝓞 ℚ) ℚ) : Matrix (Fin 3) (Fin 3) 𝔸) =
      Matrix.scalar (Fin 3) (z : 𝔸) * (g : Matrix (Fin 3) (Fin 3) 𝔸) := rfl
  simp only [point, hmat, vecMul_scalar_mul]
  ring

private theorem finUnitIdele_mul (k u : Ẑˣ) : finUnitIdele (k * u) = finUnitIdele k * finUnitIdele u := by
  unfold finUnitIdele
  rw [Subgroup.coe_mul, map_mul]

private theorem point_centralScalarGL_finUnitIdele_mul (k : Ẑˣ) (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ)
    (ξ : Fin 3 → ℚ) :
    point t u (centralScalarGL 3 (𝓞 ℚ) ℚ (finUnitIdele k) * g) ξ = point t (k * u) g ξ := by
  rw [point_centralScalarGL_mul]
  funext i
  simp only [point, finUnitIdele_mul, Units.val_mul]
  ring

private theorem latticeSum_centralScalarGL_finUnitIdele_mul (Φ : (Fin 3 → 𝔸) → ℂ) (k : Ẑˣ) (t : ℝ) (u : Ẑˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    latticeSum Φ t u (centralScalarGL 3 (𝓞 ℚ) ℚ (finUnitIdele k) * g) = latticeSum Φ t (k * u) g := by
  unfold latticeSum
  simp only [point_centralScalarGL_finUnitIdele_mul]

private theorem integral_mul_left_eq_self_of_isMulLeftInvariant [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ)
    [du.IsMulLeftInvariant] (F : Ẑˣ → ℂ) (k : Ẑˣ) : ∫ u, F (k * u) ∂du = ∫ u, F u ∂du := by
  by_cases hdu : du = 0
  · simp [hdu]
  have hae : ∀ c : Ẑˣ, AEMeasurable (fun u : Ẑˣ => c * u) du := by
    intro c
    by_contra h
    have hmap := Measure.map_of_not_aemeasurable h
    rw [map_mul_left_eq_self du c] at hmap
    exact hdu hmap
  by_cases hF : AEStronglyMeasurable F du
  · have h := integral_map (hae k) (f := F) (by rwa [map_mul_left_eq_self du k])
    rw [map_mul_left_eq_self du k] at h
    exact h.symm
  · have hFk : ¬ AEStronglyMeasurable (fun u => F (k * u)) du := by
      intro hFk
      apply hF
      have hFk' : AEStronglyMeasurable (fun u => F (k * u)) (Measure.map (fun u : Ẑˣ => k⁻¹ * u) du) := by
        rwa [map_mul_left_eq_self du k⁻¹]
      have h := hFk'.comp_aemeasurable (hae k⁻¹)
      refine h.congr (Filter.Eventually.of_forall fun u => ?_)
      simp [Function.comp, mul_inv_cancel_left]
    rw [integral_non_aestronglyMeasurable hF, integral_non_aestronglyMeasurable hFk]

private theorem ideleNorm_finUnitIdele (k : Ẑˣ) : TateGlobal.ideleNorm ℚ (finUnitIdele k) = 1 := by
  refine TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles ℚ (finUnitIdele k) rfl ?_
  have h : AdeleRing.finitePartUnits (𝓞 ℚ) ℚ (finUnitIdele k) = (k : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
    Units.ext rfl
  rw [h]
  exact k.2

private theorem epstein_centralScalarGL_finUnitIdele_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) [du.IsMulLeftInvariant]
    (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (k : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epstein du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (finUnitIdele k) * g) = epstein du Φ σ g := by
  unfold epstein
  rw [ideleNorm_det_centralScalarGL_mul, ideleNorm_finUnitIdele, one_pow, one_mul]
  congr 2
  funext t
  rw [show (∫ u, latticeSum Φ t u (centralScalarGL 3 (𝓞 ℚ) ℚ (finUnitIdele k) * g) ∂du) =
      ∫ u, latticeSum Φ t (k * u) g ∂du from by simp only [latticeSum_centralScalarGL_finUnitIdele_mul]]
  exact congrArg (fun x => ((t ^ (3 * σ) : ℝ) : ℂ) * x)
    (integral_mul_left_eq_self_of_isMulLeftInvariant du (fun u => latticeSum Φ t u g) k)

private def principalIdele (q : ℚˣ) : 𝔸ˣ := Units.map (algebraMap ℚ 𝔸).toMonoidHom q

private theorem centralScalarGL_principalIdele (q : ℚˣ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ (principalIdele q) =
      globalPointsGL 3 (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.scalar (Fin 3) q) := by
  ext i j
  show Matrix.scalar (Fin 3) (algebraMap ℚ 𝔸 q) i j = (Matrix.scalar (Fin 3) (q : ℚ)).map (algebraMap ℚ 𝔸) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.map_apply]
  split_ifs <;> simp

private theorem epstein_centralScalarGL_principalIdele_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ)
    (σ : ℝ) (q : ℚˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epstein du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (principalIdele q) * g) = epstein du Φ σ g := by
  rw [centralScalarGL_principalIdele, epstein_globalPointsGL_mul]

private theorem _root_.CentralLift.ofReal_ne_zero {t : ℝ} (ht : t ≠ 0) : ofReal t ≠ 0 := by
  unfold ofReal
  simpa using ht

p2m_export "CentralLift" "ofReal_ne_zero"
private theorem _root_.CentralLift.ofReal_mul (s t : ℝ) : ofReal (s * t) = ofReal s * ofReal t := by
  unfold ofReal
  exact map_mul _ _ _

p2m_export "CentralLift" "ofReal_mul"
private theorem norm_ofReal (t : ℝ) : ‖ofReal t‖ = |t| := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).dist_eq
    (ofReal t) 0
  rw [map_zero, dist_zero_right, dist_zero_right] at h
  have h' : InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (ofReal t) = t :=
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply t
  rw [h', Real.norm_eq_abs] at h
  exact h.symm

private theorem archIdele_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    archIdele t = TateGlobal.archUnitHom Rat.infinitePlace (Units.mk0 (ofReal t) (ofReal_ne_zero ht)) := by
  unfold archIdele
  rw [dif_neg ht]

private theorem archIdele_mul {s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0) : archIdele (s * t) = archIdele s * archIdele t := by
  rw [archIdele_of_ne_zero (mul_ne_zero hs ht), archIdele_of_ne_zero hs, archIdele_of_ne_zero ht, ← map_mul]
  congr 1
  exact Units.ext (by simp [ofReal_mul])

private theorem archIdele_snd (t : ℝ) : ((archIdele t : 𝔸ˣ) : 𝔸).2 = 1 := by
  unfold archIdele
  split_ifs
  · rfl
  · exact archCentralUnit_snd _ _

private theorem ideleNorm_archIdele {s : ℝ} (hs : 0 < s) : TateGlobal.ideleNorm ℚ (archIdele s) = s := by
  rw [RationalIdeleNorm.ideleNorm_eq_norm_fst_of_snd_eq_one _ (archIdele_snd s), archIdele_of_ne_zero hs.ne',
    TateGlobal.archUnitHom_apply, archCentralUnit_fst_self, Units.val_mk0, norm_ofReal, abs_of_pos hs]

private theorem point_centralScalarGL_archIdele_mul {s : ℝ} (hs : s ≠ 0) {t : ℝ} (ht : t ≠ 0) (u : Ẑˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) :
    point t u (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ξ = point (s * t) u g ξ := by
  rw [point_centralScalarGL_mul]
  funext i
  simp only [point, archIdele_mul hs ht, Units.val_mul]
  ring

private theorem latticeSum_centralScalarGL_archIdele_mul (Φ : (Fin 3 → 𝔸) → ℂ) {s : ℝ} (hs : s ≠ 0)
    {t : ℝ} (ht : t ≠ 0)
    (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    latticeSum Φ t u (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) = latticeSum Φ (s * t) u g := by
  unfold latticeSum
  simp only [point_centralScalarGL_archIdele_mul hs ht]

private theorem ae_pos_scaleMeasure : ∀ᵐ t ∂scaleMeasure, (0 : ℝ) < t :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioi)

private theorem integral_scaleMeasure_comp_mul {s : ℝ} (hs : 0 < s) (σ : ℝ) (G : ℝ → ℂ) :
    ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * G (s * t) ∂scaleMeasure =
      ((s ^ (-(3 * σ)) : ℝ) : ℂ) * ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * G t ∂scaleMeasure := by
  have hd : Measurable fun t : ℝ => Real.toNNReal t⁻¹ := measurable_real_toNNReal.comp measurable_inv
  have hsc : scaleMeasure =
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ((Real.toNNReal t⁻¹ : ℝ≥0) : ENNReal) := rfl
  rw [hsc, integral_withDensity_eq_integral_smul hd, integral_withDensity_eq_integral_smul hd]
  have hs3 : s ^ (3 * σ) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  have key : ∀ t ∈ Set.Ioi (0 : ℝ),
      Real.toNNReal t⁻¹ • (((t ^ (3 * σ) : ℝ) : ℂ) * G (s * t)) =
        ((s * s ^ (-(3 * σ)) : ℝ) : ℂ) *
          (Real.toNNReal (s * t)⁻¹ • ((((s * t) ^ (3 * σ) : ℝ) : ℂ) * G (s * t))) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    rw [NNReal.smul_def, NNReal.smul_def, Complex.real_smul, Complex.real_smul, Real.coe_toNNReal',
      Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr ht'.le), max_eq_left (inv_nonneg.mpr (mul_pos hs ht').le),
      Real.mul_rpow hs.le ht'.le, Real.rpow_neg hs.le, mul_inv]
    push_cast
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht'.ne'
    have hs3C : ((s ^ (3 * σ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs3
    field_simp
  have h3 : ∫ t in Set.Ioi (0 : ℝ), Real.toNNReal (s * t)⁻¹ • ((((s * t) ^ (3 * σ) : ℝ) : ℂ) * G (s * t)) =
      s⁻¹ • ∫ t in Set.Ioi (s * 0), Real.toNNReal t⁻¹ • (((t ^ (3 * σ) : ℝ) : ℂ) * G t) :=
    integral_comp_mul_left_Ioi (fun x : ℝ => Real.toNNReal x⁻¹ • (((x ^ (3 * σ) : ℝ) : ℂ) * G x)) 0 hs
  rw [setIntegral_congr_fun measurableSet_Ioi key, integral_const_mul, h3, mul_zero, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul]
  congr 2
  rw [mul_comm s, mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]

private theorem epstein_centralScalarGL_archIdele_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ)
    (σ : ℝ)
    {s : ℝ} (hs : 0 < s) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epstein du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) = epstein du Φ σ g := by
  unfold epstein
  rw [ideleNorm_det_centralScalarGL_mul, ideleNorm_archIdele hs]
  have h1 : ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) *
        ∫ u, latticeSum Φ t u (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ∂du ∂scaleMeasure =
      ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ (s * t) u g ∂du ∂scaleMeasure := by
    refine integral_congr_ae (ae_pos_scaleMeasure.mono fun t ht => ?_)
    simp only [latticeSum_centralScalarGL_archIdele_mul Φ hs.ne' ht.ne']
  have h2 : ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ (s * t) u g ∂du ∂scaleMeasure =
      ((s ^ (-(3 * σ)) : ℝ) : ℂ) * ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ t u g ∂du ∂scaleMeasure :=
    integral_scaleMeasure_comp_mul hs σ fun x : ℝ => ∫ u, latticeSum Φ x u g ∂du
  rw [h1, h2]
  have hc : (s ^ 3 * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) ^ σ * s ^ (-(3 * σ)) =
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ := by
    rw [Real.mul_rpow (pow_nonneg hs.le 3) (TateGlobal.ideleNorm_pos _).le, ← Real.rpow_natCast,
      ← Real.rpow_mul hs.le, Real.rpow_neg hs.le]
    push_cast
    rw [mul_right_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs _).ne', one_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, hc]

private def normalizerUnit (z : 𝔸ˣ) : ℚˣ := Units.mk0 (RatIdele.ρ z) (RatIdele.ρ_ne_zero z)

private theorem archCoord_principalIdele (q : ℚˣ) : RatIdele.archCoord (principalIdele q) = ((q : ℚ) : ℝ) :=
  RatIdele.archCoord_principal q

private theorem archCoord_inv (x : 𝔸ˣ) : RatIdele.archCoord x⁻¹ = (RatIdele.archCoord x)⁻¹ := by
  have h := RatIdele.archCoord_mul x x⁻¹
  rw [mul_inv_cancel, RatIdele.archCoord_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem eq_archIdele_mul_finPart (y : 𝔸ˣ) :
    y = archIdele (RatIdele.archCoord y) * Units.map (finIncl (𝓞 ℚ) ℚ) (RatIdele.finPart y) := by
  rw [archIdele_of_ne_zero (RatIdele.archCoord_ne_zero y)]
  apply Units.ext
  refine Prod.ext (funext fun w => ?_) ?_
  · obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    rw [Units.val_mul]
    change _ = (_ : 𝔸).1 Rat.infinitePlace * (_ : 𝔸).1 Rat.infinitePlace
    rw [TateGlobal.archUnitHom_apply, archCentralUnit_fst_self, Units.val_mk0]
    rw [show (((Units.map (finIncl (𝓞 ℚ) ℚ) (RatIdele.finPart y) : 𝔸ˣ) : 𝔸)).1 Rat.infinitePlace = 1 from rfl,
      mul_one]
    unfold ofReal RatIdele.archCoord
    exact (RingEquiv.symm_apply_apply _ _).symm
  · rw [Units.val_mul]
    change _ = (_ : 𝔸).2 * (_ : 𝔸).2
    rw [TateGlobal.archUnitHom_apply, archCentralUnit_snd, one_mul]
    rfl

private theorem finPart_mem_unitIdeles {y : 𝔸ˣ}
    (hy : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), Valued.v ((y : 𝔸).2 v) = 1) :
    RatIdele.finPart y ∈ IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ := by
  rw [IsDedekindDomain.FiniteAdeleRing.mem_unitIdeles_iff]
  refine ⟨fun v => ?_, fun v => ?_⟩
  · simp only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, RatIdele.finPart_apply, hy v, le_refl]
  · have h := RatIdele.valued_snd_inv_mul y v
    rw [hy v, mul_one] at h
    rw [← map_inv]
    simp only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, RatIdele.finPart_apply, h, le_refl]

private theorem valued_snd_mul_principalIdele_inv (z : 𝔸ˣ) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    Valued.v (((z * (principalIdele (normalizerUnit z))⁻¹ : 𝔸ˣ) : 𝔸).2 v) = 1 := by
  have hz := (RatIdele.ρ_spec z).1 v
  have hp : Valued.v (((principalIdele (normalizerUnit z) : 𝔸ˣ) : 𝔸).2 v) = v.valuation ℚ (RatIdele.ρ z) := by
    show Valued.v ((algebraMap ℚ 𝔸 (RatIdele.ρ z)).2 v) = _
    rw [RatIdele.algebraMap_adeleRing_snd, RatIdele.valued_algebraMap_rat]
  have hinv := RatIdele.valued_snd_inv_mul (principalIdele (normalizerUnit z)) v
  rw [hp] at hinv
  rw [RatIdele.valued_snd_mul, hz, mul_comm]
  exact hinv

private theorem archCoord_mul_principalIdele_inv_pos (z : 𝔸ˣ) :
    0 < RatIdele.archCoord (z * (principalIdele (normalizerUnit z))⁻¹) := by
  have h := (RatIdele.ρ_spec z).2
  have hr : ((RatIdele.ρ z : ℚ) : ℝ) ≠ 0 := by exact_mod_cast RatIdele.ρ_ne_zero z
  rw [RatIdele.archCoord_mul, archCoord_inv, archCoord_principalIdele]
  have e : RatIdele.archCoord z * (((normalizerUnit z : ℚˣ) : ℚ) : ℝ)⁻¹ =
      (RatIdele.archCoord z * ((RatIdele.ρ z : ℚ) : ℝ)) * (((RatIdele.ρ z : ℚ) : ℝ)⁻¹) ^ 2 := by
    simp only [normalizerUnit, Units.val_mk0]
    field_simp
  rw [e]
  exact mul_pos h (by positivity)

private theorem exists_eq_principalIdele_mul_archIdele_mul_finUnitIdele (z : 𝔸ˣ) :
    ∃ (q : ℚˣ) (s : ℝ) (_ : 0 < s) (k : Ẑˣ), z = principalIdele q * (archIdele s * finUnitIdele k) := by
  refine ⟨normalizerUnit z, RatIdele.archCoord (z * (principalIdele (normalizerUnit z))⁻¹),
    archCoord_mul_principalIdele_inv_pos z,
    ⟨RatIdele.finPart (z * (principalIdele (normalizerUnit z))⁻¹),
      finPart_mem_unitIdeles (valued_snd_mul_principalIdele_inv z)⟩, ?_⟩
  have hy := eq_archIdele_mul_finPart (z * (principalIdele (normalizerUnit z))⁻¹)
  calc z = principalIdele (normalizerUnit z) * (z * (principalIdele (normalizerUnit z))⁻¹) := by
        rw [mul_comm z, mul_inv_cancel_left]
    _ = _ := congrArg (fun w => principalIdele (normalizerUnit z) * w) hy

private theorem centralScalarGL_mul (a b : 𝔸ˣ) :
    centralScalarGL 3 (𝓞 ℚ) ℚ (a * b) = centralScalarGL 3 (𝓞 ℚ) ℚ a * centralScalarGL 3 (𝓞 ℚ) ℚ b := by
  unfold centralScalarGL
  exact map_mul _ _ _

private theorem epstein_scalar_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) [du.IsMulLeftInvariant] (Φ : (Fin 3 → 𝔸) → ℂ)
    (σ : ℝ) (z : 𝔸ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epstein du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = epstein du Φ σ g := by
  obtain ⟨q, s, hs, k, rfl⟩ := exists_eq_principalIdele_mul_archIdele_mul_finUnitIdele z
  rw [centralScalarGL_mul, centralScalarGL_mul, mul_assoc, mul_assoc, epstein_centralScalarGL_principalIdele_mul,
    epstein_centralScalarGL_archIdele_mul du Φ σ hs, epstein_centralScalarGL_finUnitIdele_mul]

private theorem nnnormSum_globalPointsGL_mul (Φ : (Fin 3 → 𝔸) → ℂ) (t : ℝ) (u : Ẑˣ)
    (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) ξ)‖₊ : ENNReal) =
      ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ)‖₊ : ENNReal) := by
  simp only [point_globalPointsGL_mul]
  exact (vecMulEquiv γ).tsum_eq fun ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0} => (‖Φ (point t u g ξ.1)‖₊ : ENNReal)

private theorem nnnormSum_centralScalarGL_finUnitIdele_mul (Φ : (Fin 3 → 𝔸) → ℂ) (k : Ẑˣ) (t : ℝ) (u : Ẑˣ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0},
        (‖Φ (point t u (centralScalarGL 3 (𝓞 ℚ) ℚ (finUnitIdele k) * g) ξ)‖₊ : ENNReal) =
      ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t (k * u) g ξ)‖₊ : ENNReal) := by
  simp only [point_centralScalarGL_finUnitIdele_mul]

private theorem nnnormSum_centralScalarGL_archIdele_mul (Φ : (Fin 3 → 𝔸) → ℂ) {s : ℝ} (hs : s ≠ 0) {t : ℝ}
    (ht : t ≠ 0) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0},
        (‖Φ (point t u (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ξ)‖₊ : ENNReal) =
      ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point (s * t) u g ξ)‖₊ : ENNReal) := by
  simp only [point_centralScalarGL_archIdele_mul hs ht]

private theorem epsteinPlus_globalPointsGL_mul' [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ)
    (σ : ℝ) (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epsteinPlus du Φ σ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = epsteinPlus du Φ σ g := by
  unfold epsteinPlus
  simp only [nnnormSum_globalPointsGL_mul, map_mul, TateGlobal.ideleNorm_mul, ideleNorm_det_globalPointsGL, one_mul]

private theorem lintegral_mul_left_eq_self_of_isMulLeftInvariant [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ)
    [du.IsMulLeftInvariant] (F : Ẑˣ → ENNReal) (k : Ẑˣ) : ∫⁻ u, F (k * u) ∂du = ∫⁻ u, F u ∂du := by
  have key : ∀ (G : Ẑˣ → ENNReal) (c : Ẑˣ), ∫⁻ u, G u ∂du ≤ ∫⁻ u, G (c * u) ∂du := fun G c =>
    calc ∫⁻ u, G u ∂du = ∫⁻ u, G u ∂(Measure.map (fun u : Ẑˣ => c * u) du) := by rw [map_mul_left_eq_self du c]
      _ ≤ ∫⁻ u, G (c * u) ∂du := lintegral_map_le G _
  refine le_antisymm ?_ (key F k)
  calc ∫⁻ u, F (k * u) ∂du ≤ ∫⁻ u, F (k * (k⁻¹ * u)) ∂du := key (fun u => F (k * u)) k⁻¹
    _ = ∫⁻ u, F u ∂du := by simp only [mul_inv_cancel_left]

private theorem lintegral_scaleMeasure_comp_mul {s : ℝ} (hs : 0 < s) (σ : ℝ) (G : ℝ → ENNReal) :
    ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) * G (s * t) ∂scaleMeasure =
      ENNReal.ofReal (s ^ (-(3 * σ))) * ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) * G t ∂scaleMeasure := by
  have hd : Measurable fun t : ℝ => ((Real.toNNReal t⁻¹ : ℝ≥0) : ENNReal) :=
    (measurable_real_toNNReal.comp measurable_inv).coe_nnreal_ennreal
  have hfin : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ((Real.toNNReal t⁻¹ : ℝ≥0) : ENNReal) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.coe_lt_top
  have hsc : scaleMeasure =
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ((Real.toNNReal t⁻¹ : ℝ≥0) : ENNReal) := rfl
  rw [hsc, lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd hfin,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ hd hfin]
  simp only [Pi.mul_apply]
  have hs3 : s ^ (3 * σ) ≠ 0 := (Real.rpow_pos_of_pos hs _).ne'
  have hc0 : (0 : ℝ) ≤ s * s ^ (-(3 * σ)) := by positivity
  have key : ∀ t ∈ Set.Ioi (0 : ℝ),
      ((Real.toNNReal t⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal (t ^ (3 * σ)) * G (s * t)) =
        ENNReal.ofReal (s * s ^ (-(3 * σ))) *
          (((Real.toNNReal (s * t)⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal ((s * t) ^ (3 * σ)) * G (s * t))) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have hst : (0 : ℝ) < s * t := mul_pos hs ht'
    show ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (3 * σ)) * G (s * t)) =
      ENNReal.ofReal (s * s ^ (-(3 * σ))) *
        (ENNReal.ofReal (s * t)⁻¹ * (ENNReal.ofReal ((s * t) ^ (3 * σ)) * G (s * t)))
    have e1 : ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ (3 * σ)) * G (s * t)) =
        ENNReal.ofReal (t⁻¹ * t ^ (3 * σ)) * G (s * t) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr ht'.le), mul_assoc]
    have e2 : ENNReal.ofReal (s * s ^ (-(3 * σ)) * ((s * t)⁻¹ * (s * t) ^ (3 * σ))) * G (s * t) =
        ENNReal.ofReal (s * s ^ (-(3 * σ))) *
          (ENNReal.ofReal (s * t)⁻¹ * (ENNReal.ofReal ((s * t) ^ (3 * σ)) * G (s * t))) := by
      rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul (inv_nonneg.mpr hst.le), mul_assoc, mul_assoc]
    rw [e1, ← e2]
    congr 2
    rw [Real.mul_rpow hs.le ht'.le, Real.rpow_neg hs.le, mul_inv]
    field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi key, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hmap : Measure.map (⇑(Homeomorph.mulLeft₀ s hs.ne').toMeasurableEquiv) volume =
      ENNReal.ofReal s⁻¹ • volume := by
    show Measure.map (s * ·) volume = ENNReal.ofReal s⁻¹ • volume
    rw [Real.map_volume_mul_left hs.ne', abs_of_pos (inv_pos.mpr hs)]
  have hind : ∀ t : ℝ, (Set.Ioi (0 : ℝ)).indicator
        (fun x => ((Real.toNNReal (s * x)⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal ((s * x) ^ (3 * σ)) * G (s * x))) t =
      (Set.Ioi (0 : ℝ)).indicator
        (fun x => ((Real.toNNReal x⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal (x ^ (3 * σ)) * G x)) (s * t) := by
    intro t
    unfold Set.indicator
    simp only [Set.mem_Ioi]
    by_cases ht : 0 < t
    · simp only [ht, mul_pos hs ht, if_true]
    · have hst : ¬ 0 < s * t := fun h => ht (by nlinarith)
      simp only [ht, hst, if_false]
  have hsub : ∫⁻ t in Set.Ioi (0 : ℝ),
        ((Real.toNNReal (s * t)⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal ((s * t) ^ (3 * σ)) * G (s * t)) =
      ENNReal.ofReal s⁻¹ *
        ∫⁻ t in Set.Ioi (0 : ℝ), ((Real.toNNReal t⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal (t ^ (3 * σ)) * G t) := by
    have hF := lintegral_map_equiv (μ := volume) ((Set.Ioi (0 : ℝ)).indicator
      fun x => ((Real.toNNReal x⁻¹ : ℝ≥0) : ENNReal) * (ENNReal.ofReal (x ^ (3 * σ)) * G x))
      (Homeomorph.mulLeft₀ s hs.ne').toMeasurableEquiv
    rw [hmap, lintegral_smul_measure] at hF
    rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioi, lintegral_congr hind]
    exact hF.symm
  rw [hsub, ← mul_assoc, ← ENNReal.ofReal_mul hc0]
  congr 2
  rw [mul_comm s, mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]

private theorem epsteinPlus_centralScalarGL_finUnitIdele_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ)
    [du.IsMulLeftInvariant] (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (k : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epsteinPlus du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (finUnitIdele k) * g) = epsteinPlus du Φ σ g := by
  unfold epsteinPlus
  rw [ideleNorm_det_centralScalarGL_mul, ideleNorm_finUnitIdele, one_pow, one_mul]
  congr 1
  refine lintegral_congr fun t => ?_
  congr 1
  simp only [nnnormSum_centralScalarGL_finUnitIdele_mul]
  exact lintegral_mul_left_eq_self_of_isMulLeftInvariant du
    (fun u => ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ)‖₊ : ENNReal)) k

private theorem epsteinPlus_centralScalarGL_archIdele_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ)
    (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) {s : ℝ} (hs : 0 < s) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epsteinPlus du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) = epsteinPlus du Φ σ g := by
  unfold epsteinPlus
  rw [ideleNorm_det_centralScalarGL_mul, ideleNorm_archIdele hs]
  have h1 : ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) *
        ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0},
          (‖Φ (point t u (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ξ)‖₊ : ENNReal) ∂du ∂scaleMeasure =
      ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) *
        ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point (s * t) u g ξ)‖₊ : ENNReal) ∂du ∂scaleMeasure := by
    refine lintegral_congr_ae (ae_pos_scaleMeasure.mono fun t ht => ?_)
    simp only [nnnormSum_centralScalarGL_archIdele_mul Φ hs.ne' ht.ne']
  have h2 := lintegral_scaleMeasure_comp_mul hs σ
    fun x : ℝ => ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point x u g ξ)‖₊ : ENNReal) ∂du
  rw [h1, h2]
  have hc : (s ^ 3 * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g)) ^ σ * s ^ (-(3 * σ)) =
      TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ := by
    rw [Real.mul_rpow (pow_nonneg hs.le 3) (TateGlobal.ideleNorm_pos _).le, ← Real.rpow_natCast,
      ← Real.rpow_mul hs.le, Real.rpow_neg hs.le]
    push_cast
    rw [mul_right_comm, mul_inv_cancel₀ (Real.rpow_pos_of_pos hs _).ne', one_mul]
  have hN : (0 : ℝ) ≤ s ^ 3 * TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) :=
    (mul_pos (pow_pos hs 3) (TateGlobal.ideleNorm_pos _)).le
  rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hN _), hc]

private theorem epsteinPlus_centralScalarGL_principalIdele_mul [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ)
    (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (q : ℚˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    epsteinPlus du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (principalIdele q) * g) = epsteinPlus du Φ σ g := by
  rw [centralScalarGL_principalIdele, epsteinPlus_globalPointsGL_mul']

end CentralLift
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

end
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

end CentralLiftBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

section HandBackBlock

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped ENNReal Pointwise

namespace FundamentalDomainPoleLimit

variable {G α : Type*} [Group G] [MulAction G α]

private noncomputable def envelope (B₀ : α → ℝ) (x : α) : ℝ := ⨅ g : G, B₀ (g • x)

private theorem envelope_nonneg {B₀ : α → ℝ} (h0 : ∀ x, 0 ≤ B₀ x) (x : α) : 0 ≤ envelope (G := G) B₀ x :=
  le_ciInf fun _ => h0 _

private theorem envelope_le {B₀ : α → ℝ} (h0 : ∀ x, 0 ≤ B₀ x) (x : α) : envelope (G := G) B₀ x ≤ B₀ x :=
  (ciInf_le ⟨0, by rintro _ ⟨g, rfl⟩; exact h0 _⟩ (1 : G)).trans_eq (by rw [one_smul])

private theorem envelope_smul (B₀ : α → ℝ) (h : G)
    (x : α) : envelope (G := G) B₀ (h • x) = envelope (G := G) B₀ x := by
  unfold envelope
  simp_rw [smul_smul]
  exact Equiv.iInf_comp (g := fun g : G => B₀ (g • x)) (Equiv.mulRight h)

private theorem norm_le_envelope {R : α → ℂ} (hR : ∀ (g : G) (x : α), R (g • x) = R x) {B₀ : α → ℝ}
    (hB : ∀ x, ‖R x‖ ≤ B₀ x) (x : α) : ‖R x‖ ≤ envelope (G := G) B₀ x :=
  le_ciInf fun g => (hR g x) ▸ hB (g • x)

private theorem measurable_envelope [MeasurableSpace α] [MeasurableConstSMul G α] [Countable G] {B₀ : α → ℝ}
    (hB₀ : Measurable B₀) : Measurable (envelope (G := G) B₀) :=
  Measurable.iInf fun g => hB₀.comp (measurable_const_smul g)

private theorem setLIntegral_le_mul_of_forall_le {β : Type*} [MeasurableSpace β] {ν : Measure β} {T : Set β}
    (hT : ν T ≠ ⊤)
    {Φ : β → ℝ≥0∞} (hΦ : Measurable Φ) {K : ℝ≥0∞} (hle : ∀ x ∈ T, Φ x ≤ K) : ∫⁻ x in T, Φ x ∂ν ≤ K * ν T := by
  have hTm : MeasurableSet (toMeasurable ν T) := measurableSet_toMeasurable ν T
  have hbadm : MeasurableSet ({x | K < Φ x} ∩ toMeasurable ν T) := (measurableSet_lt measurable_const hΦ).inter hTm
  have hbad : ν ({x | K < Φ x} ∩ toMeasurable ν T) = 0 := by
    by_contra hne
    have hsub : T ⊆ toMeasurable ν T \ ({x | K < Φ x} ∩ toMeasurable ν T) := fun x hx =>
      ⟨subset_toMeasurable ν T hx, fun h => (not_lt.mpr (hle x hx)) h.1⟩
    have h1 : ν (toMeasurable ν T) ≤ ν (toMeasurable ν T) - ν ({x | K < Φ x} ∩ toMeasurable ν T) := by
      calc ν (toMeasurable ν T) = ν T := measure_toMeasurable T
        _ ≤ ν (toMeasurable ν T \ ({x | K < Φ x} ∩ toMeasurable ν T)) := measure_mono hsub
        _ = ν (toMeasurable ν T) - ν ({x | K < Φ x} ∩ toMeasurable ν T) :=
            measure_diff inter_subset_right hbadm.nullMeasurableSet
              (ne_top_of_le_ne_top ((measure_toMeasurable T).trans_ne hT) (measure_mono inter_subset_right))
    rcases eq_or_ne (ν (toMeasurable ν T)) 0 with h0 | h0
    · exact hne (le_antisymm ((measure_mono inter_subset_right).trans h0.le) zero_le)
    · exact absurd h1 (not_le.mpr (ENNReal.sub_lt_self ((measure_toMeasurable T).trans_ne hT) h0 hne))
  have hae : ∀ᵐ x ∂ν.restrict (toMeasurable ν T), Φ x ≤ K := by
    rw [ae_restrict_iff' hTm]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hbad] with x hx hxT
    exact not_lt.1 fun h => hx ⟨h, hxT⟩
  calc ∫⁻ x in T, Φ x ∂ν = ∫⁻ x in toMeasurable ν T, Φ x ∂ν := by rw [Measure.restrict_toMeasurable hT]
    _ ≤ ∫⁻ _ in toMeasurable ν T, K ∂ν := lintegral_mono_ae hae
    _ = K * ν T := by rw [lintegral_const, Measure.restrict_apply_univ, measure_toMeasurable]

private theorem norm_mul_mul_weight_le {β : Type*} {T : Set β} {φ₁ φ₂ : β → ℂ} {w h : β → ℝ}
    {C₁ C₂ C₃ c₀ : ℝ} {M N : ℕ} (hc₀ : 0 < c₀) (hMN : M ≤ N) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (hh : ∀ x ∈ T, c₀ ≤ h x) (hφ₁ : ∀ x ∈ T, ‖φ₁ x‖ * h x ^ N ≤ C₁) (hφ₂ : ∀ x ∈ T, ‖φ₂ x‖ ≤ C₂)
    (hw : ∀ x ∈ T, w x ≤ C₃ * h x ^ M) (hw0 : ∀ x, 0 ≤ w x) {x : β} (hx : x ∈ T) :
    ‖φ₁ x * φ₂ x‖ * w x ≤ C₁ * C₂ * C₃ / c₀ ^ (N - M) := by
  have hxpos : 0 < h x := hc₀.trans_le (hh x hx)
  have hN : h x ^ N = h x ^ M * h x ^ (N - M) := by rw [← pow_add, Nat.add_sub_cancel' hMN]
  have hφ₁' : ‖φ₁ x‖ ≤ C₁ / h x ^ N := by
    rw [le_div_iff₀ (pow_pos hxpos N)]
    exact hφ₁ x hx
  have hpow : h x ^ M / h x ^ N ≤ 1 / c₀ ^ (N - M) := by
    rw [hN, ← div_div, div_self (pow_pos hxpos M).ne', one_div_le_one_div (pow_pos hxpos _) (pow_pos hc₀ _)]
    exact pow_le_pow_left₀ hc₀.le (hh x hx) _
  calc ‖φ₁ x * φ₂ x‖ * w x = ‖φ₁ x‖ * ‖φ₂ x‖ * w x := by rw [norm_mul]
    _ ≤ (C₁ / h x ^ N) * C₂ * (C₃ * h x ^ M) :=
        mul_le_mul (mul_le_mul hφ₁' (hφ₂ x hx) (norm_nonneg _) (div_nonneg hC₁ (pow_nonneg hxpos.le N)))
          (hw x hx) (hw0 x) (mul_nonneg (div_nonneg hC₁ (pow_nonneg hxpos.le N)) hC₂)
    _ = C₁ * C₂ * C₃ * (h x ^ M / h x ^ N) := by ring
    _ ≤ C₁ * C₂ * C₃ * (1 / c₀ ^ (N - M)) := by gcongr
    _ = C₁ * C₂ * C₃ / c₀ ^ (N - M) := by ring

private theorem lintegral_ofReal_norm_mul_weight_lt_top {β : Type*} [MeasurableSpace β] {ν : Measure β} {T : Set β}
    (hT : ν T < ⊤) {φ₁ φ₂ : β → ℂ} (hφ₁m : Measurable φ₁) (hφ₂m : Measurable φ₂) {w h : β → ℝ}
    (hwm : Measurable w) {C₁ C₂ C₃ c₀ : ℝ} {M N : ℕ} (hc₀ : 0 < c₀) (hMN : M ≤ N) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hh : ∀ x ∈ T, c₀ ≤ h x) (hφ₁ : ∀ x ∈ T, ‖φ₁ x‖ * h x ^ N ≤ C₁)
    (hφ₂ : ∀ x ∈ T, ‖φ₂ x‖ ≤ C₂) (hw : ∀ x ∈ T, w x ≤ C₃ * h x ^ M) (hw0 : ∀ x, 0 ≤ w x) :
    ∫⁻ x in T, ENNReal.ofReal (‖φ₁ x * φ₂ x‖ * w x) ∂ν < ⊤ := by
  refine lt_of_le_of_lt (setLIntegral_le_mul_of_forall_le hT.ne ((hφ₁m.mul hφ₂m).norm.mul hwm).ennreal_ofReal
    fun x hx => ENNReal.ofReal_le_ofReal
      (norm_mul_mul_weight_le hc₀ hMN hC₁ hC₂ hC₃ hh hφ₁ hφ₂ hw hw0 hx)) ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT

private theorem lintegral_nnnorm_mul_lt_top {β : Type*} [MeasurableSpace β] {ν : Measure β} {T : Set β}
    (hT : ν T < ⊤) {φ₁ φ₂ : β → ℂ} (hφ₁m : Measurable φ₁) (hφ₂m : Measurable φ₂) {h : β → ℝ}
    {C₁ C₂ c₀ : ℝ} {N : ℕ} (hc₀ : 0 < c₀) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hh : ∀ x ∈ T, c₀ ≤ h x)
    (hφ₁ : ∀ x ∈ T, ‖φ₁ x‖ * h x ^ N ≤ C₁) (hφ₂ : ∀ x ∈ T, ‖φ₂ x‖ ≤ C₂) :
    ∫⁻ x in T, ‖φ₁ x * φ₂ x‖₊ ∂ν < ⊤ := by
  have hpt : ∀ x ∈ T, (‖φ₁ x * φ₂ x‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (C₁ * C₂ * 1 / c₀ ^ (N - 0)) := fun x hx => by
    have h1 := norm_mul_mul_weight_le (w := fun _ => (1 : ℝ)) (M := 0) hc₀ (Nat.zero_le N) hC₁ hC₂ zero_le_one hh
      hφ₁ hφ₂ (fun x _ => by rw [pow_zero, mul_one]) (fun _ => zero_le_one) hx
    rw [mul_one] at h1
    calc ((‖φ₁ x * φ₂ x‖₊ : NNReal) : ℝ≥0∞) = ‖φ₁ x * φ₂ x‖ₑ := rfl
      _ = ENNReal.ofReal ‖φ₁ x * φ₂ x‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (C₁ * C₂ * 1 / c₀ ^ (N - 0)) := ENNReal.ofReal_le_ofReal h1
  refine lt_of_le_of_lt (setLIntegral_le_mul_of_forall_le hT.ne ?_ hpt) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hT)
  exact (hφ₁m.mul hφ₂m).nnnorm.coe_nnreal_ennreal

variable [MeasurableSpace α] [MeasurableConstSMul G α] [Countable G] {μ : Measure α}
  [SMulInvariantMeasure G α μ] {F S : Set α}

private theorem integrableOn_and_tendsto (hF : IsFundamentalDomain G F μ) (hS : ∀ᵐ x ∂μ, ∃ g : G, g • x ∈ S)
    (f : α → ℂ) (hf : ∀ (g : G) (x : α), f (g • x) = f x) (hfm : AEStronglyMeasurable f (μ.restrict F))
    (E : ℝ → α → ℂ) (c : ℂ) (hE : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ (g : G) (x : α), E σ (g • x) = E σ x)
    (hEm : ∀ σ ∈ Ioc (1 : ℝ) 2, AEStronglyMeasurable (E σ) (μ.restrict F))
    (B₀ : α → ℝ) (hB₀m : Measurable B₀) (hB₀ : ∀ x, 0 ≤ B₀ x)
    (hR : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ x, ‖E σ x - c / ((σ - 1 : ℝ) : ℂ)‖ ≤ B₀ x)
    (hfin₁ : ∫⁻ x in S, ‖f x‖₊ ∂μ < ⊤) (hfin₂ : ∫⁻ x in S, ENNReal.ofReal (‖f x‖ * B₀ x) ∂μ < ⊤) :
    (∀ σ ∈ Ioc (1 : ℝ) 2, IntegrableOn (fun x => f x * E σ x) F μ) ∧
      Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * ∫ x in F, f x * E σ x ∂μ) (𝓝[>] 1)
        (𝓝 (c * ∫ x in F, f x ∂μ)) := by
  set R : ℝ → α → ℂ := fun σ x => E σ x - c / ((σ - 1 : ℝ) : ℂ) with hRdef
  set B : α → ℝ := envelope (G := G) B₀ with hBdef
  have hE' : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ x, E σ x = c / ((σ - 1 : ℝ) : ℂ) + R σ x := fun σ _ x => by
    simp only [hRdef, add_sub_cancel]
  have hRinv : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ (g : G) (x : α), R σ (g • x) = R σ x := fun σ hσ g x => by
    simp only [hRdef, hE σ hσ g x]
  have hRB : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ x, ‖R σ x‖ ≤ B x := fun σ hσ =>
    norm_le_envelope (hRinv σ hσ) (hR σ hσ)
  have hRm : ∀ σ ∈ Ioc (1 : ℝ) 2, AEStronglyMeasurable (R σ) (μ.restrict F) := fun σ hσ =>
    (hEm σ hσ).sub aestronglyMeasurable_const
  have hBm : Measurable B := measurable_envelope hB₀m
  have hfF : IntegrableOn f F μ :=
    FundamentalDomainDomination.integrableOn_of_norm_le_of_ae_covers hF hS hfm (fun x => (‖f x‖₊ : ℝ≥0∞))
      (fun g x => by simp only [hf g x]) (fun _ => le_rfl) hfin₁
  have hfBF : IntegrableOn (fun x => ‖f x‖ * B x) F μ := by
    refine FundamentalDomainDomination.integrableOn_of_norm_le_of_ae_covers hF hS
      (hfm.norm.mul (hBm.aestronglyMeasurable.mono_measure Measure.restrict_le_self))
      (fun x => ENNReal.ofReal (‖f x‖ * B x)) (fun g x => by simp only [hf g x, hBdef, envelope_smul]) ?_ ?_
    · intro x
      have h0 : 0 ≤ ‖f x‖ * B x := mul_nonneg (norm_nonneg _) (envelope_nonneg hB₀ x)
      calc ((‖‖f x‖ * B x‖₊ : NNReal) : ℝ≥0∞) = ‖‖f x‖ * B x‖ₑ := rfl
        _ = ENNReal.ofReal (‖f x‖ * B x) := Real.enorm_eq_ofReal h0
        _ ≤ ENNReal.ofReal (‖f x‖ * B x) := le_rfl
    · refine lt_of_le_of_lt (lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_) hfin₂
      exact mul_le_mul_of_nonneg_left (envelope_le hB₀ x) (norm_nonneg _)
  refine ⟨fun σ hσ => ?_, ?_⟩
  · have hsum : (fun x => f x * E σ x) = fun x => f x * (c / ((σ - 1 : ℝ) : ℂ)) + f x * R σ x :=
      funext fun x => by rw [hE' σ hσ x, mul_add]
    rw [hsum]
    refine (hfF.mul_const _).add ?_
    refine Integrable.mono' hfBF (hfm.mul (hRm σ hσ)) (Eventually.of_forall fun x => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hRB σ hσ x) (norm_nonneg _)
  · exact PoleLimit.tendsto_mul_integral_of_expansion (μ.restrict F) f E R c B hE' hRB hRm hfF hfBF

end FundamentalDomainPoleLimit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

open MeasureTheory NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

namespace SiegelSlabCovering

private def siegelType (P : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → Prop)
    (c C : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧ P c C n t k}

private theorem mem_siegelType_iff
    (P : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → Prop) (c C : ℝ)
    (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g ∈ siegelType P c C ↔ ∃ n t k : AdelicGL 3 (𝓞 ℚ) ℚ, g = n * t * k ∧ P c C n t k :=
  Iff.rfl

private theorem countable_globalPoints_range : Countable (globalPointsGL 3 (𝓞 ℚ) ℚ).range := by
  have hinj : Function.Injective
      (fun u : Matrix.GeneralLinearGroup (Fin 3) ℚ =>
        (fun i j => (u : Matrix (Fin 3) (Fin 3) ℚ) i j : Fin 3 → Fin 3 → ℚ)) := by
    intro u v huv
    apply Units.ext
    ext i j
    exact congrFun (congrFun huv i) j
  haveI hmat : Countable (Matrix.GeneralLinearGroup (Fin 3) ℚ) := hinj.countable
  have hset : ((globalPointsGL 3 (𝓞 ℚ) ℚ).range : Set (AdelicGL 3 (𝓞 ℚ) ℚ)).Countable := by
    rw [MonoidHom.coe_range]
    exact Set.countable_range _
  exact hset.to_subtype

private theorem measurableConstSMul_globalPoints_range :
    MeasurableConstSMul (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) := by
  refine ⟨fun γ => ?_⟩
  have hmul : Measurable fun x : AdelicGL 3 (𝓞 ℚ) ℚ => (γ : AdelicGL 3 (𝓞 ℚ) ℚ) * x :=
    measurable_const_mul (γ : AdelicGL 3 (𝓞 ℚ) ℚ)
  exact hmul

private theorem ae_exists_smul_mem_siegelType_inter_slab
    (P : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → Prop) (c C a b : ℝ)
    (hcov : ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ∃ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (n t k : AdelicGL 3 (𝓞 ℚ) ℚ),
      globalPointsGL 3 (𝓞 ℚ) ℚ γ * g = n * t * k ∧ P c C n t k)
    (hstab : ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (x : AdelicGL 3 (𝓞 ℚ) ℚ),
      x ∈ ideleNormDetSlab a b → globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ ideleNormDetSlab a b)
    (hslab : MeasurableSet (ideleNormDetSlab a b)) :
    ∀ᵐ x ∂(slabMeasure a b), ∃ γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range,
      γ • x ∈ siegelType P c C ∩ ideleNormDetSlab a b := by
  have hmem : ∀ᵐ x ∂(slabMeasure a b), x ∈ ideleNormDetSlab a b := by
    rw [slabMeasure_def]
    exact ae_restrict_mem hslab
  filter_upwards [hmem] with x hx
  obtain ⟨γ, n, t, k, hγ, hP⟩ := hcov x
  refine ⟨⟨globalPointsGL 3 (𝓞 ℚ) ℚ γ, MonoidHom.mem_range.mpr ⟨γ, rfl⟩⟩, ?_⟩
  show globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ siegelType P c C ∩ ideleNormDetSlab a b
  exact Set.mem_inter ((mem_siegelType_iff P c C _).mpr ⟨n, t, k, hγ, hP⟩) (hstab γ x hx)

private theorem slabMeasure_siegelType_inter_slab_lt_top
    (P : ℝ → ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → Prop) (c C a b : ℝ)
    (hfin : NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ (siegelType P c C ∩ ideleNormDetSlab a b) < ⊤) :
    slabMeasure a b (siegelType P c C ∩ ideleNormDetSlab a b) < ⊤ := by
  refine lt_of_le_of_lt ?_ hfin
  rw [slabMeasure_def]
  exact Measure.restrict_le_self _

end SiegelSlabCovering
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

open MeasureTheory Set Filter Topology NumberField
p2m_open "LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"
open LanglandsTunnell.CubicInduction.AdelicEpstein
open scoped ENNReal ComplexConjugate

namespace SlabPoleLimit

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.borelSpace_glBorel

private theorem forall_range_smul {P : AdelicGL 3 (𝓞 ℚ) ℚ → AdelicGL 3 (𝓞 ℚ) ℚ → Prop}
    (h : ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), P (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) g)
    (γ' : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : P (γ' • g) g := by
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 γ'.2
  rw [Subgroup.smul_def, smul_eq_mul, ← hγ]
  exact h γ g

private theorem smulInvariantMeasure_slabMeasure (a b : ℝ)
    (hinv : ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ,
      MeasurePreserving (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) (slabMeasure a b)
        (slabMeasure a b)) :
    SMulInvariantMeasure (globalPointsGL 3 (𝓞 ℚ) ℚ).range (AdelicGL 3 (𝓞 ℚ) ℚ) (slabMeasure a b) := by
  refine ⟨fun γ' s hs => ?_⟩
  obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 γ'.2
  have hpre : (fun x : AdelicGL 3 (𝓞 ℚ) ℚ => γ' • x) = fun x => globalPointsGL 3 (𝓞 ℚ) ℚ γ * x := by
    funext x
    rw [Subgroup.smul_def, smul_eq_mul, ← hγ]
  rw [hpre]
  exact (hinv γ).measure_preimage hs.nullMeasurableSet

private theorem integrable_and_tendsto_epstein [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ)
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : IsSlabDomain a b Φ₀)
    (hslab : MeasurableSet (ideleNormDetSlab a b))
    (hstab : ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (x : AdelicGL 3 (𝓞 ℚ) ℚ),
      x ∈ ideleNormDetSlab a b → globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ ideleNormDetSlab a b)
    (hinv : ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ,
      MeasurePreserving (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) (slabMeasure a b)
        (slabMeasure a b))
    (S : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hS : ∀ᵐ x ∂(slabMeasure a b), ∃ γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range, γ • x ∈ S)
    (hSfin : slabMeasure a b S < ⊤)
    (φ₁ φ₂ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφ₁m : Measurable φ₁) (hφ₂m : Measurable φ₂)
    (hφ₁ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      φ₁ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ₁ g)
    (hφ₂ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      φ₂ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ₂ g)
    (c : ℂ)
    (hE : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      g ∈ ideleNormDetSlab a b → epstein du Φ σ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = epstein du Φ σ g)
    (hEm : ∀ σ ∈ Ioc (1 : ℝ) 2, AEStronglyMeasurable (epstein du Φ σ) (domainMeasure a b Φ₀))
    (B₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ) (hB₀m : Measurable B₀) (hB₀0 : ∀ g, 0 ≤ B₀ g)
    (hR : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ g ∈ ideleNormDetSlab a b, ‖epstein du Φ σ g - c / ((σ - 1 : ℝ) : ℂ)‖ ≤ B₀ g)
    (ht : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ) (C₁ C₂ C₃ c₀ : ℝ) (M N : ℕ) (hc₀ : 0 < c₀) (hMN : M ≤ N) (hC₁ : 0 ≤ C₁)
    (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃) (hfloor : ∀ g ∈ S, c₀ ≤ ht g) (hdecay : ∀ g ∈ S, ‖φ₁ g‖ * ht g ^ N ≤ C₁)
    (hbdd : ∀ g ∈ S, ‖φ₂ g‖ ≤ C₂) (hgrowth : ∀ g ∈ S, B₀ g ≤ C₃ * ht g ^ M) :
    (∀ σ ∈ Ioc (1 : ℝ) 2,
        Integrable (fun g => φ₁ g * conj (φ₂ g) * epstein du Φ σ g) (domainMeasure a b Φ₀)) ∧
      Tendsto (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) * ∫ g, φ₁ g * conj (φ₂ g) * epstein du Φ σ g ∂(domainMeasure a b Φ₀))
        (𝓝[>] 1) (𝓝 (c * ∫ g, φ₁ g * conj (φ₂ g) ∂(domainMeasure a b Φ₀))) := by
  classical
  haveI := SiegelSlabCovering.countable_globalPoints_range
  haveI := SiegelSlabCovering.measurableConstSMul_globalPoints_range
  haveI := smulInvariantMeasure_slabMeasure a b hinv

  set E' : ℝ → AdelicGL 3 (𝓞 ℚ) ℚ → ℂ := fun σ g =>
    if g ∈ ideleNormDetSlab a b then epstein du Φ σ g else c / ((σ - 1 : ℝ) : ℂ) with hE'def
  have hae : ∀ σ, E' σ =ᵐ[domainMeasure a b Φ₀] epstein du Φ σ := fun σ => by
    have hmem : ∀ᵐ g ∂(domainMeasure a b Φ₀), g ∈ ideleNormDetSlab a b := by
      rw [domainMeasure_def, slabMeasure_def]
      exact ae_restrict_of_ae (ae_restrict_mem hslab)
    filter_upwards [hmem] with g hg
    exact if_pos hg
  have hφ₂m' : Measurable fun g => conj (φ₂ g) := Complex.continuous_conj.measurable.comp hφ₂m
  have hfm : Measurable fun g => φ₁ g * conj (φ₂ g) := hφ₁m.mul hφ₂m'
  have hf : ∀ (γ' : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      φ₁ (γ' • g) * conj (φ₂ (γ' • g)) = φ₁ g * conj (φ₂ g) :=
    forall_range_smul (P := fun x y => φ₁ x * conj (φ₂ x) = φ₁ y * conj (φ₂ y)) fun γ g => by
      simp only [hφ₁, hφ₂]
  have hE' : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ (γ' : (globalPointsGL 3 (𝓞 ℚ) ℚ).range) (g : AdelicGL 3 (𝓞 ℚ) ℚ),
      E' σ (γ' • g) = E' σ g := by
    intro σ hσ γ' g
    obtain ⟨γ, hγ⟩ := MonoidHom.mem_range.1 γ'.2
    have hsm : γ' • g = globalPointsGL 3 (𝓞 ℚ) ℚ γ * g := by rw [Subgroup.smul_def, smul_eq_mul, ← hγ]
    rw [hsm]
    by_cases hg : g ∈ ideleNormDetSlab a b
    · have hγg : globalPointsGL 3 (𝓞 ℚ) ℚ γ * g ∈ ideleNormDetSlab a b := hstab γ g hg
      exact (if_pos hγg).trans ((hE σ hσ γ g hg).trans (if_pos hg).symm)
    · have hγg : globalPointsGL 3 (𝓞 ℚ) ℚ γ * g ∉ ideleNormDetSlab a b := fun h => hg (by
        have h' := hstab γ⁻¹ _ h
        rwa [map_inv, ← mul_assoc, inv_mul_cancel, one_mul] at h')
      exact (if_neg hγg).trans (if_neg hg).symm
  have hEm' : ∀ σ ∈ Ioc (1 : ℝ) 2, AEStronglyMeasurable (E' σ) (domainMeasure a b Φ₀) :=
    fun σ hσ => (hEm σ hσ).congr (hae σ).symm
  have hR' : ∀ σ ∈ Ioc (1 : ℝ) 2, ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ, ‖E' σ g - c / ((σ - 1 : ℝ) : ℂ)‖ ≤ B₀ g := by
    intro σ hσ g
    by_cases hg : g ∈ ideleNormDetSlab a b
    · rw [show E' σ g = epstein du Φ σ g from if_pos hg]
      exact hR σ hσ g hg
    · rw [show E' σ g = c / ((σ - 1 : ℝ) : ℂ) from if_neg hg, sub_self, norm_zero]
      exact hB₀0 g
  have hbdd' : ∀ g ∈ S, ‖conj (φ₂ g)‖ ≤ C₂ := fun g hg => by
    rw [Complex.norm_conj]
    exact hbdd g hg
  have hfin₁ : ∫⁻ g in S, ‖φ₁ g * conj (φ₂ g)‖₊ ∂(slabMeasure a b) < ⊤ :=
    FundamentalDomainPoleLimit.lintegral_nnnorm_mul_lt_top hSfin hφ₁m hφ₂m' hc₀ hC₁ hC₂ hfloor hdecay hbdd'
  have hfin₂ : ∫⁻ g in S, ENNReal.ofReal (‖φ₁ g * conj (φ₂ g)‖ * B₀ g) ∂(slabMeasure a b) < ⊤ :=
    FundamentalDomainPoleLimit.lintegral_ofReal_norm_mul_weight_lt_top hSfin hφ₁m hφ₂m' hB₀m hc₀ hMN hC₁ hC₂ hC₃
      hfloor hdecay hbdd' hgrowth hB₀0
  have core := FundamentalDomainPoleLimit.integrableOn_and_tendsto (G := (globalPointsGL 3 (𝓞 ℚ) ℚ).range)
    (μ := slabMeasure a b) (F := Φ₀) (S := S) hΦ₀.isFundamentalDomain hS (fun g => φ₁ g * conj (φ₂ g)) hf
    hfm.aestronglyMeasurable E' c hE' (fun σ hσ => by rw [← domainMeasure_def]; exact hEm' σ hσ) B₀ hB₀m hB₀0
    hR' hfin₁ hfin₂
  beta_reduce at core
  rw [← domainMeasure_def] at core
  have hmul : ∀ σ, (fun g => φ₁ g * conj (φ₂ g) * E' σ g) =ᵐ[domainMeasure a b Φ₀]
      fun g => φ₁ g * conj (φ₂ g) * epstein du Φ σ g := fun σ => by
    filter_upwards [hae σ] with g hg
    rw [hg]
  refine ⟨fun σ hσ => Integrable.congr (core.1 σ hσ) (hmul σ), core.2.congr fun σ => ?_⟩
  rw [integral_congr_ae (hmul σ)]

end SlabPoleLimit
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

end HandBackBlock
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

section Assembly

open MeasureTheory Set Filter Topology IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.LanglandsTunnell LanglandsTunnell.CubicInduction P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.LanglandsTunnell.CubicInduction LanglandsTunnell.CubicInduction.SlabL2"
open LanglandsTunnell.CubicInduction.AdelicEpstein

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem solution
    [MeasurableSpace (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)]
    (hmeas : @Measurable (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ) (AdeleRing (𝓞 ℚ) ℚ) _
      (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (fun u => ((finUnitIdele u : (AdeleRing (𝓞 ℚ) ℚ)ˣ) : AdeleRing (𝓞 ℚ) ℚ)))
    (du : Measure (IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ)) [IsFiniteMeasure du]
    (Φ : (Fin 3 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
    (hΦ : ∃ Φc : Fin 3 → (AdeleRing (𝓞 ℚ) ℚ → ℂ), (∀ i, Φc i ∈ NumberField.AdelicFourier.pureTensorSet ℚ) ∧
          Φ = fun x => ∏ i, Φc i (x i))
    (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) (hΦ₀ : SlabL2.IsSlabDomain a b Φ₀)
    (hgm : Measurable (gauge3 ℚ))
    (Sg : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (hS : ∀ᵐ x ∂(SlabL2.slabMeasure a b), ∃ γ : GL (Fin 3) ℚ, globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ Sg)
    (hSfin : SlabL2.slabMeasure a b Sg < ⊤)
    (ht : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ) (c₀ : ℝ) (hc₀ : 0 < c₀) (hfloor : ∀ g ∈ Sg, c₀ ≤ ht g)
    (hgauge : ∃ (C₄ : ℝ) (k : ℕ), ∀ g ∈ Sg, g ∈ SlabL2.ideleNormDetSlab a b → gauge3 ℚ g ≤ C₄ * ht g ^ k)
    (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (hφc : Continuous φ)
    (hφ : ∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), φ (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = φ g)
    (hdecay : ∀ N : ℕ, ∃ C : ℝ, ∀ g ∈ Sg, ‖φ g‖ * ht g ^ N ≤ C) :
    (∀ σ ∈ Set.Ioc (1 : ℝ) 2,
        Integrable (fun g => φ g * starRingEnd ℂ (φ g) * epstein du Φ σ g) (SlabL2.domainMeasure a b Φ₀)) ∧
      Filter.Tendsto
        (fun σ : ℝ => ((σ - 1 : ℝ) : ℂ) *
          ∫ g, φ g * starRingEnd ℂ (φ g) * epstein du Φ σ g ∂(SlabL2.domainMeasure a b Φ₀))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds
          ((letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
            (((du Set.univ).toReal : ℂ) *
              (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
            (3 * (((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
              (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ)))) *
            ∫ g, φ g * starRingEnd ℂ (φ g) ∂(SlabL2.domainMeasure a b Φ₀))) := by
  classical
  haveI hBorelGL := NumberField.AdelicHaar.borelSpace_glBorel (Fin 3) (𝓞 ℚ) ℚ
  obtain ⟨ha, hab, -⟩ := id hΦ₀
  obtain ⟨Cb, M, hB3c⟩ := exists_forall_epstein_eq_div_sub_one_add_of_pureTensor hmeas du Φ hΦ
  obtain ⟨C₄, k, hC₄⟩ := hgauge

  have hslab : MeasurableSet (ideleNormDetSlab a b) := SlabPoleGlue.measurableSet_ideleNormDetSlab a b
  have hstab : ∀ (γ : Matrix.GeneralLinearGroup (Fin 3) ℚ) (x : AdelicGL 3 (𝓞 ℚ) ℚ),
      x ∈ ideleNormDetSlab a b → globalPointsGL 3 (𝓞 ℚ) ℚ γ * x ∈ ideleNormDetSlab a b := by
    intro γ x hx
    show TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (globalPointsGL 3 (𝓞 ℚ) ℚ γ * x)) ∈ Set.Icc a b
    rw [map_mul, TateGlobal.ideleNorm_mul, CentralLift.ideleNorm_det_globalPointsGL, one_mul]
    exact hx
  have hinv : ∀ γ : Matrix.GeneralLinearGroup (Fin 3) ℚ,
      MeasurePreserving (fun g : AdelicGL 3 (𝓞 ℚ) ℚ => globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) (slabMeasure a b)
        (slabMeasure a b) :=
    fun γ => measurePreserving_mul_left_globalPointsGL_restrict_setOf_ideleNorm_det_mem_Icc a b γ

  have hx : ∀ᵐ x ∂(slabMeasure a b), x ∈ ideleNormDetSlab a b := by
    unfold slabMeasure
    exact ae_restrict_mem hslab
  have hS' : ∀ᵐ x ∂(slabMeasure a b), ∃ γ : (globalPointsGL 3 (𝓞 ℚ) ℚ).range, γ • x ∈ Sg ∩ ideleNormDetSlab a b := by
    filter_upwards [hS, hx] with x hγ hxs
    obtain ⟨γ, hγ⟩ := hγ
    refine ⟨⟨globalPointsGL 3 (𝓞 ℚ) ℚ γ, γ, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul]
    exact ⟨hγ, hstab γ x hxs⟩
  have hSfin' : slabMeasure a b (Sg ∩ ideleNormDetSlab a b) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hSfin

  obtain ⟨CN, hCN⟩ := hdecay (k * M)
  obtain ⟨C0, hC0⟩ := hdecay 0
  set Cb' : ℝ := max Cb 0 with hCb'
  set C₄' : ℝ := max C₄ 0 with hC₄'
  set cab : ℝ := max ((a ^ ((1 : ℝ) / 3))⁻¹) (b ^ ((1 : ℝ) / 3)) with hcab
  have hb : 0 < b := ha.trans hab
  have hcab0 : 0 < cab := lt_max_of_lt_right (Real.rpow_pos_of_pos hb _)
  set B₀ : AdelicGL 3 (𝓞 ℚ) ℚ → ℝ := fun g => Cb' * (cab * gauge3 ℚ g) ^ M with hB₀
  have hB₀m : Measurable B₀ := ((hgm.const_mul cab).pow_const M).const_mul Cb'
  have hB₀0 : ∀ g, 0 ≤ B₀ g := fun g =>
    mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg hcab0.le (gauge3_pos ℚ g).le) M)

  have hR : ∀ σ ∈ Set.Ioc (1 : ℝ) 2, ∀ g ∈ ideleNormDetSlab a b,
      ‖epstein du Φ σ g -
          (letI : MeasurableSpace (AdeleRing (𝓞 ℚ) ℚ) := NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ;
           (((du Set.univ).toReal : ℂ) *
               (∫ x, Φ x ∂(Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)) /
             (3 * (((Measure.pi fun _ : Fin 3 => NumberField.AdelicHaar.adelicAddHaar (𝓞 ℚ) ℚ)
               (Set.univ.pi fun _ : Fin 3 => NumberField.AdelicBox.adelicBox ℚ)).toReal : ℂ)))) /
            ((σ - 1 : ℝ) : ℂ)‖ ≤ B₀ g := by
    intro σ hσ g hg
    have hr : TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b := hg
    set r : ℝ := TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) with hr_def
    have hr0 : 0 < r := ha.trans_le hr.1
    have hr3 : 0 < r ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hr0 _
    set s : ℝ := (r ^ ((1 : ℝ) / 3))⁻¹ with hs_def
    have hs0 : 0 < s := inv_pos.2 hr3
    have hr3cube : (r ^ ((1 : ℝ) / 3)) ^ 3 = r := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      norm_num
    have hnorm1 : TateGlobal.ideleNorm ℚ
        (Matrix.GeneralLinearGroup.det (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g)) = 1 := by
      rw [CentralLift.ideleNorm_det_centralScalarGL_mul, CentralLift.ideleNorm_archIdele hs0, ← hr_def, hs_def,
        inv_pow, hr3cube, inv_mul_cancel₀ hr0.ne']
    obtain ⟨R, hexp, hRb⟩ := hB3c _ hnorm1
    have hE1 : epstein du Φ σ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) = epstein du Φ σ g :=
      CentralLift.epstein_centralScalarGL_archIdele_mul du Φ σ hs0 g
    rw [← hE1, hexp σ hσ, add_sub_cancel_left]

    have hmax : max s s⁻¹ ≤ cab := by
      refine max_le ?_ ?_
      · exact (inv_anti₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_le_rpow ha.le hr.1 (by norm_num))).trans
          (le_max_left _ _)
      · rw [hs_def, inv_inv]
        exact (Real.rpow_le_rpow hr0.le hr.2 (by norm_num)).trans (le_max_right _ _)
    have hg1 : gauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ≤ cab * gauge3 ℚ g :=
      (SlabPoleGlue.gauge3_centralScalarGL_archIdele_mul_le hs0 g).trans
        (mul_le_mul_of_nonneg_right hmax (gauge3_pos ℚ g).le)
    have hg1pos : 0 ≤ gauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) := (gauge3_pos ℚ _).le
    calc ‖R σ‖ ≤ Cb * gauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ^ M := hRb σ hσ
      _ ≤ Cb' * gauge3 ℚ (centralScalarGL 3 (𝓞 ℚ) ℚ (archIdele s) * g) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hg1pos M)
      _ ≤ Cb' * (cab * gauge3 ℚ g) ^ M :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg1pos hg1 M) (le_max_right _ _)

  have hgrowth : ∀ g ∈ Sg ∩ ideleNormDetSlab a b, B₀ g ≤ Cb' * (cab * C₄') ^ M * ht g ^ (k * M) := by
    rintro g ⟨hgS, hgslab⟩
    have hht : 0 ≤ ht g := hc₀.le.trans (hfloor g hgS)
    have h4 : gauge3 ℚ g ≤ C₄' * ht g ^ k :=
      (hC₄ g hgS hgslab).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hht k))
    have h5 : cab * gauge3 ℚ g ≤ cab * C₄' * ht g ^ k := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h4 hcab0.le
    calc B₀ g = Cb' * (cab * gauge3 ℚ g) ^ M := rfl
      _ ≤ Cb' * (cab * C₄' * ht g ^ k) ^ M :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hcab0.le (gauge3_pos ℚ g).le) h5 M)
            (le_max_right _ _)
      _ = Cb' * (cab * C₄') ^ M * ht g ^ (k * M) := by rw [mul_pow, ← pow_mul, mul_assoc]

  have hφm : Measurable φ := hφc.measurable
  exact SlabPoleLimit.integrable_and_tendsto_epstein du Φ a b Φ₀ hΦ₀ hslab hstab hinv (Sg ∩ ideleNormDetSlab a b)
    hS' hSfin' φ φ hφm hφm hφ hφ _ (fun σ _ γ g _ => CentralLift.epstein_globalPointsGL_mul du Φ σ γ g)
    (fun σ _ => (EpsteinMeasurability.stronglyMeasurable_epstein_of_continuous hmeas hΦ du σ
      SlabPoleGlue.continuous_ideleNorm_det).aestronglyMeasurable)
    B₀ hB₀m hB₀0 hR ht (max CN 0) (max C0 0) (Cb' * (cab * C₄') ^ M) c₀ (k * M) (k * M) hc₀ le_rfl
    (le_max_right _ _) (le_max_right _ _)
    (mul_nonneg (le_max_right _ _) (pow_nonneg (mul_nonneg hcab0.le (le_max_right _ _)) M))
    (fun g hg => hfloor g hg.1) (fun g hg => (hCN g hg.1).trans (le_max_left _ _))
    (fun g hg => by
      have h0 := hC0 g hg.1
      rw [pow_zero, mul_one] at h0
      exact h0.trans (le_max_left _ _))
    hgrowth

end Assembly
p2m_reactivate "P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor.EpsteinMeasurability"

end S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_AdelicEpstein_integrable_and_tendsto_sub_one_mul_integral_epstein_of_pureTensor (solution)
