-- Prove2me | solution 1 for LanglandsTunnell.RankinSelberg.rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/78987c97-7664-589b-a090-e96d2c59bffb

import Definitions.Def_LanglandsTunnell_RS22GlobalIntegral
import Definitions.Def_LanglandsTunnell_RSCarrier
import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_UnipotentQuotient
import Definitions.Def_LanglandsTunnell_DeltaLift
import Definitions.Def_NumberField_AdelicVolume
import Theorems.Thm_LanglandsTunnell_Converse_integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_det_eq_prod_archDetNorm_pow_mult
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_RankinSelberg_rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
p2m_attr_erase "instance" "M4aHerbrand.Bridge.sigmaCompactSpace_finiteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_adeleRing M4aHerbrand.Bridge.sigmaCompactSpace_infiniteAdeleRing M4aHerbrand.Bridge.sigmaCompactSpace_completion M4aHerbrand.Bridge.instT2SpaceAdeleRing instCountableOfNumberField_definitions"

set_option autoImplicit false

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

open MeasureTheory NumberField NumberField.AdelicHaar IsDedekindDomain
open AutomorphicForm LanglandsTunnell LanglandsTunnell.RankinSelberg RSCarrier

open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.TateGlobal NumberField.InfinitePlace.Completion

noncomputable section

namespace Ws46
namespace RS22Split

theorem coe_finFactor (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) =
      (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g))⁻¹ * g := rfl

theorem glArch_archRealGLAt_ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    glArch (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) =
      glArch (𝓞 ℚ) ℚ g := by
  have h := (RSCarrier.finFactor g).2
  rw [mem_finiteAdelicGL2Subgroup_iff, coe_finFactor, map_mul, map_inv, inv_mul_eq_one] at h
  exact h

theorem glFin_archRealGLAt (m : GL (Fin 2) ℝ) :
    glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) m) = 1 :=
  glFin_adelicArchGLIncl ℚ _

theorem abs_det_ratArchGL2 (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| = archDetNorm (default : InfinitePlace ℚ) g := by
  unfold archDetNorm LanglandsTunnell.ratArchGL2
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  have hcoe : ((Matrix.GeneralLinearGroup.map
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace ℚ))).toRingHom
        (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g)) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal (default : InfinitePlace
          ℚ))).toRingHom.mapMatrix
        ((archComponent ℚ default (glArch (𝓞 ℚ) ℚ g) : GL (Fin 2) (default : InfinitePlace ℚ).Completion) :
          Matrix (Fin 2) (Fin 2) (default : InfinitePlace ℚ).Completion) := rfl
  rw [hcoe, ← RingHom.map_det, ← Real.norm_eq_abs]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal _).norm_map_of_map_zero (map_zero _) _

theorem ideleNorm_det_eq_archAbs_mul_finNorm (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) =
      |(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| *
        TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) := by
  have hg : archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g) *
      (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ) = g := by
    rw [coe_finFactor, mul_inv_cancel_left]
  conv_lhs => rw [← hg]
  rw [map_mul, NumberField.TateGlobal.ideleNorm_mul]
  congr 1
  have hX : glFin (𝓞 ℚ) ℚ (archRealGLAt (IsTotallyReal.isReal (default : InfinitePlace ℚ)) (ratArchGL2 g)) ∈
      finiteIntegralGL2 (𝓞 ℚ) ℚ := by
    rw [glFin_archRealGLAt]; exact one_mem _
  rw [NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult ℚ _ hX, Fintype.prod_subsingleton _ default]
  have hmult : (default : InfinitePlace ℚ).mult = 1 := by
    simp [NumberField.InfinitePlace.mult, IsTotallyReal.isReal]
  rw [hmult, pow_one, abs_det_ratArchGL2]
  unfold archDetNorm
  rw [glArch_archRealGLAt_ratArchGL2]

theorem ideleNorm_det_cpow_split (g : AdelicGL2 (𝓞 ℚ) ℚ) (z : ℂ) :
    ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) ^ z =
      (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ z) *
        ((TateGlobal.ideleNorm ℚ
          (Matrix.GeneralLinearGroup.det (RSCarrier.finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ z) := by
  rw [ideleNorm_det_eq_archAbs_mul_finNorm, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (NumberField.TateGlobal.ideleNorm_pos _).le]

theorem det_unipotent_mul (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    Matrix.GeneralLinearGroup.det ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = Matrix.GeneralLinearGroup.det g := by
  obtain ⟨x, hx⟩ := n.2
  rw [map_mul, ← hx]
  have : Matrix.GeneralLinearGroup.det (unipotentGL2Hom x : AdelicGL2 (𝓞 ℚ) ℚ) = 1 := by
    apply Units.ext
    change ((unipotentGL2 (Multiplicative.toAdd x) : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)).det = 1
    rw [unipotentGL2_coe, Matrix.det_fin_two_of]
    ring
  rw [this, one_mul]

theorem bottomRowVec_unipotent_mul (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) (t : AdeleRing (𝓞 ℚ) ℚ) :
    bottomRowVec ℚ ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) t = bottomRowVec ℚ g t := by
  obtain ⟨x, hx⟩ := n.2
  funext j
  unfold bottomRowVec
  rw [← hx]
  change t * (((unipotentGL2 (Multiplicative.toAdd x)) * g : AdelicGL2 (𝓞 ℚ) ℚ) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) 1 j = _
  rw [Units.val_mul, unipotentGL2_coe, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem rs22Kernel_unipotent_mul (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ) (s : ℂ)
    (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
      rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g := by
  rw [rs22Kernel_def, rs22Kernel_def, det_unipotent_mul, bottomRowVec_unipotent_mul]

end Ws46.RS22Split

end

open Ws46.RS22Split in
theorem solution
    [SecondCountableTopology (AdelicGL2 (𝓞 ℚ) ℚ)] :
    letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
    ∀ (μf : Measure (finiteAdelicGL2Subgroup ℚ)) [μf.IsHaarMeasure]
      (μNArch : Measure realUnipotent) [μNArch.IsHaarMeasure]
      (μNFin : Measure finUnipotent) [μNFin.IsHaarMeasure]
      (_hsplit : Measure.map (fun g : AdelicGL2 (𝓞 ℚ) ℚ => (LanglandsTunnell.ratArchGL2 g, RSCarrier.finFactor g))
          (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ) =
          RSCarrier.archMeasure.prod μf)
      (_hNsplit : Measure.map
          (fun n : adelicUnipotent ℚ => (LanglandsTunnell.ratArchGL2 n, RSCarrier.finFactor n))
          (unipotentHaar ℚ) =
          (Measure.map Subtype.val μNArch).prod (Measure.map Subtype.val μNFin))
      (s : ℂ)
      (W W' : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (WA WA' FA : GL (Fin 2) ℝ → ℂ) (Wf Wf' Ff : finiteAdelicGL2Subgroup ℚ → ℂ)
      (Φ : (Fin 2 → AdeleRing (𝓞 ℚ) ℚ) → ℂ)
      (_hW : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W g = WA (ratArchGL2 g) * Wf (finFactor g))
      (_hW' : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, W' g = WA' (ratArchGL2 g) * Wf' (finFactor g))
      (_hΦ : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, Φ (bottomRowVec ℚ g 1) = FA (ratArchGL2 g) * Ff (finFactor g))
      (_hm : Measurable fun g : AdelicGL2 (𝓞 ℚ) ℚ =>
          W g * W' g * rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g)
      (_hinv : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          W ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) * W' ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) = W g * W' g)
      (_hint : Integrable (fun p : GL (Fin 2) ℝ × finiteAdelicGL2Subgroup ℚ =>
          ((WA p.1 * (WA' p.1 * FA p.1)) *
              (((|(Matrix.GeneralLinearGroup.det p.1 : ℝ)| : ℝ) : ℂ) ^ ((s + 1) - 1 / 2))) *
            ((Wf p.2 * (Wf' p.2 * Ff p.2)) *
              ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det (p.2 : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ)
                ^ ((s + 1) - 1 / 2))))
        ((archMeasure.withDensity (HaarQuotient.density realUnipotent μNArch)).prod
          (μf.withDensity (HaarQuotient.density finUnipotent μNFin)))),
      rs22WhittakerIntegral ℚ W W' 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s =
        rsArchIntegral archMeasure μNArch (s + 1) WA (fun h => WA' h * FA h) *
          rsFinIntegral μf μNFin (s + 1) Wf (fun h => Wf' h * Ff h) := by
  letI : MeasurableSpace (GL (Fin 2) ℝ) := borel _
  intro μf _ μNArch _ μNFin _ hsplit hNsplit s W W' WA WA' FA Wf Wf' Ff Φ hW hW' hΦ hm hinv hint
  rw [rs22WhittakerIntegral_def]
  have hf : ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => W g * W' g * rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g) g =
      ((WA (ratArchGL2 g) * (fun h : GL (Fin 2) ℝ => WA' h * FA h) (ratArchGL2 g)) *
          (((|(Matrix.GeneralLinearGroup.det (ratArchGL2 g) : ℝ)| : ℝ) : ℂ) ^ ((s + 1) - 1 / 2))) *
        ((Wf (finFactor g) * (fun h : finiteAdelicGL2Subgroup ℚ => Wf' h * Ff h) (finFactor g)) *
          ((TateGlobal.ideleNorm ℚ
              (Matrix.GeneralLinearGroup.det (finFactor g : AdelicGL2 (𝓞 ℚ) ℚ)) : ℂ) ^ ((s + 1) - 1 / 2))) := by
    intro g
    simp only []
    rw [rs22Kernel_def, hW g, hW' g, hΦ g, cpowChar_apply_val, val_moduleChar_apply,
      show s + 1 / 2 = (s + 1) - 1 / 2 by ring, ideleNorm_det_cpow_split g, MonoidHom.one_apply, Units.val_one]
    ring
  have hinv' : ∀ (n : adelicUnipotent ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => W g * W' g * rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g)
          ((n : AdelicGL2 (𝓞 ℚ) ℚ) * g) =
      (fun g : AdelicGL2 (𝓞 ℚ) ℚ => W g * W' g * rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g) g := by
    intro n g
    simp only []
    rw [hinv n g, rs22Kernel_unipotent_mul]
  exact LanglandsTunnell.Converse.integral_unipotentQuotient_eq_rsArchIntegral_mul_rsFinIntegral
    μf μNArch μNFin hsplit hNsplit (s + 1) WA (fun h => WA' h * FA h) Wf (fun h => Wf' h * Ff h)
    (fun g => W g * W' g * rs22Kernel ℚ 1 (moduleChar ℚ) (moduleChar_pos ℚ) Φ s g) hf hm hinv'
    Quotient.out (fun q => Quotient.out_eq' q) hint

end S_LanglandsTunnell_RankinSelberg_rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul
end P2MW
export P2MW.S_LanglandsTunnell_RankinSelberg_rs22WhittakerIntegral_rat_eq_rsArchIntegral_mul_rsFinIntegral_of_eq_mul (solution)
