-- Prove2me | solution 1 for LanglandsTunnell.isBoundedOnSiegelWindows_weightOneLift
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5eb9eee4-bc72-5b02-b787-0e8df5894f45

import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.Bounds
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_ProductionPinsCompact
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm UpperHalfPlane
open UpperHalfPlane Matrix

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem glFin_globalPoints_apply (γ : GL (Fin 2) ℚ) (i j : Fin 2) :
    (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) i j
      = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) := rfl

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private def ratArch (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : GL (Fin 2) ℝ :=
  GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom
    (archComponent ℚ default (glArch (𝓞 ℚ) ℚ g))

private theorem ratArch_eq_one_of_glArch_eq_one {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu : glArch (𝓞 ℚ) ℚ u = 1) :
    ratArch u = 1 := by
  unfold ratArch
  rw [hu, map_one, map_one]

private theorem ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ratArch (globalPoints (𝓞 ℚ) ℚ γ) = GeneralLinearGroup.map (Rat.castHom ℝ) γ := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change ((InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom.comp
      ((archEval ℚ default).comp ((adeleArch (𝓞 ℚ) ℚ).comp (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)))))
      ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j) = (Rat.castHom ℝ) ((γ : Matrix (Fin 2) (Fin 2) ℚ) i j)
  rw [eq_ratCast, eq_ratCast]

private theorem det_ratArch_globalPoints (γ : GL (Fin 2) ℚ) :
    ((ratArch (globalPoints (𝓞 ℚ) ℚ γ)).det.val : ℝ) = (((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ) := by
  rw [ratArch_globalPoints, GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, eq_ratCast]

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix
open scoped MatrixGroups

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm NumberField.AdelicLevel MeasureTheory Complex
p2m_open "UpperHalfPlane~I"
open scoped MatrixGroups ModularForm Topology

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "ratArchGL2"
namespace P4
namespace I2
p2m_open "LanglandsTunnell"

local notation "𝔾" => GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)

end LanglandsTunnell.P4.I2

end

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane DihedralWeightOne

open scoped ModularForm MatrixGroups

namespace P2GProbe
namespace R1

variable (f : ℍ → ℂ)

private theorem norm_weightOneArchLift_le (C : ℝ)
    (hf : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2))
    (h : GL (Fin 2) ℝ) (hh : 0 < h.det.val) :
    ‖weightOneArchLift f h‖ ≤ C * Real.sqrt h.det.val := by
  have hd : denom h UpperHalfPlane.I ≠ 0 := denom_ne_zero h UpperHalfPlane.I
  have hdn : 0 < ‖denom h UpperHalfPlane.I‖ := norm_pos_iff.mpr hd

  have him : (h • UpperHalfPlane.I).im = h.det.val / ‖denom h UpperHalfPlane.I‖ ^ 2 := by
    rw [im_smul_eq_div_normSq, abs_of_pos hh, UpperHalfPlane.I_im, mul_one,
      Complex.normSq_eq_norm_sq]
  have himpos : 0 < (h • UpperHalfPlane.I).im := (h • UpperHalfPlane.I).im_pos

  have hnorm : ‖weightOneArchLift f h‖ =
      ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val := by
    unfold weightOneArchLift
    rw [ModularForm.slash_apply, σ, if_pos hh]
    simp only [ContinuousAlgEquiv.refl_apply, sub_self, zpow_zero, mul_one, _root_.zpow_neg, zpow_one,
      norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh]

  have hsq : (h • UpperHalfPlane.I).im ^ (((1 : ℤ) : ℝ) / 2) = Real.sqrt (h • UpperHalfPlane.I).im := by
    rw [Real.sqrt_eq_rpow]; norm_num
  have hspos : 0 < Real.sqrt (h • UpperHalfPlane.I).im := Real.sqrt_pos.mpr himpos
  have hpet : ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im ≤ C := by
    have h1 := hf (h • UpperHalfPlane.I)
    rw [hsq] at h1
    calc ‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im
        ≤ C / Real.sqrt (h • UpperHalfPlane.I).im * Real.sqrt (h • UpperHalfPlane.I).im :=
          mul_le_mul_of_nonneg_right h1 hspos.le
      _ = C := by field_simp

  have hsqrt_im : Real.sqrt (h • UpperHalfPlane.I).im
      = Real.sqrt h.det.val / ‖denom h UpperHalfPlane.I‖ := by
    rw [him, Real.sqrt_div hh.le, Real.sqrt_sq hdn.le]
  have hds : Real.sqrt h.det.val * Real.sqrt h.det.val = h.det.val := Real.mul_self_sqrt hh.le

  have hkey : ‖weightOneArchLift f h‖ =
      (‖f (h • UpperHalfPlane.I)‖ * Real.sqrt (h • UpperHalfPlane.I).im) * Real.sqrt h.det.val := by
    rw [hnorm, hsqrt_im, div_eq_mul_inv]
    calc ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹ * h.det.val
        = ‖f (h • UpperHalfPlane.I)‖ * ‖denom h UpperHalfPlane.I‖⁻¹
            * (Real.sqrt h.det.val * Real.sqrt h.det.val) := by rw [hds]
      _ = ‖f (h • UpperHalfPlane.I)‖ * (Real.sqrt h.det.val * ‖denom h UpperHalfPlane.I‖⁻¹)
            * Real.sqrt h.det.val := by ring
  rw [hkey]
  exact mul_le_mul_of_nonneg_right hpet (Real.sqrt_nonneg _)

end P2GProbe.R1

namespace P2GProbe
namespace R3

end P2GProbe.R3

namespace P2GProbe
namespace R4a

open LanglandsTunnell.P4.I2 CongruenceSubgroup

private theorem finiteLevelZero_le_finiteIntegralGL2 (N : Ideal (𝓞 ℚ)) :
    finiteLevelZero (𝓞 ℚ) ℚ N ≤ finiteIntegralGL2 (𝓞 ℚ) ℚ := by
  intro g hg
  rw [mem_finiteLevelZero_iff] at hg
  show g ∈ finiteLevelZero (𝓞 ℚ) ℚ ⊤
  rw [mem_finiteLevelZero_iff]
  have key : ∀ m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ),
      IsLevelZeroMatrix (𝓞 ℚ) ℚ N m → IsLevelZeroMatrix (𝓞 ℚ) ℚ ⊤ m := fun m hm =>
    ⟨hm.integral, fun v => (hm.lowerLeft v).trans
      ((idealBound_le_one N v).trans (idealBound_top v).ge)⟩
  exact ⟨key _ hg.1, key _ hg.2⟩

end P2GProbe.R4a

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 AutomorphicForm.WindowedSiegel NumberField.AdelicVolume

private theorem exists_algebraMap_eq_of_mem_integral {R : Type*} [CommRing R] [IsDedekindDomain R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {q : K}
    (hq : algebraMap K (FiniteAdeleRing R K) q ∈ integralFiniteAdeles R K) :
    ∃ r : R, algebraMap R K r = q := by
  have h : ∀ v : HeightOneSpectrum R, v.valuation K q ≤ 1 := fun v => by
    have h1 := hq v
    rw [HeightOneSpectrum.mem_adicCompletionIntegers,
      show (algebraMap K (FiniteAdeleRing R K) q) v = ((q : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1
  exact HeightOneSpectrum.mem_integers_of_valuation_le_one K q h

private theorem exists_intCast_eq_of_mem_integral {q : ℚ}
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, (n : ℚ) = q := by
  obtain ⟨r, hr⟩ := exists_algebraMap_eq_of_mem_integral hq
  exact ⟨Rat.ringOfIntegersEquiv r, by rw [← hr, Rat.ringOfIntegersEquiv_apply_coe]⟩

private theorem abs_eq_one_of_mem_integral {q : ℚ} (hq0 : q ≠ 0)
    (hq : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hq' : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) q⁻¹ ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) : |q| = 1 := by
  obtain ⟨a, ha⟩ := exists_intCast_eq_of_mem_integral hq
  obtain ⟨b, hb⟩ := exists_intCast_eq_of_mem_integral hq'
  have hab : a * b = 1 := by
    have : ((a * b : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, ha, hb, mul_inv_cancel₀ hq0]
    exact_mod_cast this
  rw [← ha]
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h1 | h1 <;> simp [h1]

private theorem archDetNorm_default_eq (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    archDetNorm (default : InfinitePlace ℚ) g = |(ratArch g).det.val| := by
  unfold archDetNorm ratArch
  rw [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe, GeneralLinearGroup.val_det_apply,
    ← Real.norm_eq_abs]
  have hiso := InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (isReal_rat_infinitePlace (default : InfinitePlace ℚ))
  exact (hiso.norm_map_of_map_zero (map_zero _) _).symm

end P2GProbe.R7

namespace P2GProbe
namespace R7

open LanglandsTunnell.P4.I2 MeasureTheory
open scoped Topology

end P2GProbe.R7

namespace P2GProbe
namespace R4a

end P2GProbe.R4a

end

namespace P2GProbe
namespace WindowBound

noncomputable section

open NumberField IsDedekindDomain AutomorphicForm NumberField.AdelicLevel Matrix UpperHalfPlane
open DihedralWeightOne AutomorphicForm.WindowedSiegel NumberField.AdelicVolume
open LanglandsTunnell.P4.I2 P2GProbe.R1 P2GProbe.R4a P2GProbe.R7
open scoped ModularForm MatrixGroups

private theorem archDetNorm_default_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    archDetNorm (default : InfinitePlace ℚ) (g * g') =
      archDetNorm (default : InfinitePlace ℚ) g * archDetNorm (default : InfinitePlace ℚ) g' := by
  unfold archDetNorm
  rw [map_mul, map_mul, Units.val_mul, Matrix.det_mul, norm_mul]

private theorem archDetNorm_default_eq_one_of_mem_U {N : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ (productionPinsCompact ℚ).U N) :
    archDetNorm (default : InfinitePlace ℚ) u = 1 := by
  rw [archDetNorm_default_eq,
    ratArch_eq_one_of_glArch_eq_one (glArch_eq_one_of_mem_productionPinsCompact_U ℚ _ hu)]
  simp

private theorem glFin_mem_finiteIntegralGL2_of_mem_U {N : Ideal (𝓞 ℚ)}
    {u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hu : u ∈ (productionPinsCompact ℚ).U N) :
    glFin (𝓞 ℚ) ℚ u ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ :=
  finiteLevelZero_le_finiteIntegralGL2 _ (finiteLevelOne_le_finiteLevelZero _ _ _
    (glFin_mem_finiteLevelOne_of_mem_productionPinsCompact_U ℚ _ hu))

private def fdet (m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) : FiniteAdeleRing (𝓞 ℚ) ℚ :=
  (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)).det

private theorem fdet_mul (m m' : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    fdet (m * m') = fdet m * fdet m' := by
  unfold fdet
  rw [Units.val_mul, Matrix.det_mul]

private theorem fdet_mul_fdet_inv (m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    fdet m * fdet m⁻¹ = 1 := by
  rw [← fdet_mul, mul_inv_cancel]
  unfold fdet
  rw [Units.val_one, Matrix.det_one]

private theorem fdet_mem_of_mem_finiteIntegralGL2 {m : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)}
    (hm : m ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ) :
    fdet m ∈ integralFiniteAdeles (𝓞 ℚ) ℚ ∧ fdet m⁻¹ ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨h₁, h₂⟩ := mem_finiteIntegralGL2_iff.mp hm
  constructor
  · unfold fdet
    rw [Matrix.det_fin_two]
    exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (h₁ 0 0) (h₁ 1 1))
      (mul_mem_integralFiniteAdeles (h₁ 0 1) (h₁ 1 0))
  · unfold fdet
    rw [Matrix.det_fin_two]
    exact sub_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles (h₂ 0 0) (h₂ 1 1))
      (mul_mem_integralFiniteAdeles (h₂ 0 1) (h₂ 1 0))

private theorem fdet_glFin_globalPoints (γ : GL (Fin 2) ℚ) :
    fdet (glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ)) =
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ : ℚˣ) : ℚ) := by
  unfold fdet
  rw [GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Matrix.det_fin_two, map_sub, map_mul,
    map_mul]
  simp only [glFin_globalPoints_apply]

private theorem fdet_identity {x s : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} {γ : GL (Fin 2) ℚ}
    {h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)} (hfin : glFin (𝓞 ℚ) ℚ h = 1)
    (hg : s * x = globalPoints (𝓞 ℚ) ℚ γ * h * u) :
    fdet (glFin (𝓞 ℚ) ℚ s) * fdet (glFin (𝓞 ℚ) ℚ x) =
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ : ℚˣ) : ℚ) *
        fdet (glFin (𝓞 ℚ) ℚ u) := by
  have h1 : glFin (𝓞 ℚ) ℚ (s * x) = glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ * h * u) := by rw [hg]
  rw [map_mul, map_mul, map_mul, hfin, mul_one] at h1
  have h2 := congrArg fdet h1
  rwa [fdet_mul, fdet_mul, fdet_glFin_globalPoints] at h2

private theorem algebraMap_det_mul_inv_det_mem {N : Ideal (𝓞 ℚ)} {x s₁ s₂ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hs₁ : glFin (𝓞 ℚ) ℚ s₁ ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hs₂ : glFin (𝓞 ℚ) ℚ s₂ ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    {γ₁ γ₂ : GL (Fin 2) ℚ} {h₁ u₁ h₂ u₂ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₁ : u₁ ∈ (productionPinsCompact ℚ).U N) (hfin₁ : glFin (𝓞 ℚ) ℚ h₁ = 1)
    (hg₁ : s₁ * x = globalPoints (𝓞 ℚ) ℚ γ₁ * h₁ * u₁)
    (hu₂ : u₂ ∈ (productionPinsCompact ℚ).U N) (hfin₂ : glFin (𝓞 ℚ) ℚ h₂ = 1)
    (hg₂ : s₂ * x = globalPoints (𝓞 ℚ) ℚ γ₂ * h₂ * u₂) :
    algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)
        (((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ) * ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)⁻¹) ∈
      integralFiniteAdeles (𝓞 ℚ) ℚ := by
  have e₁ := fdet_identity hfin₁ hg₁
  have e₂ := fdet_identity hfin₂ hg₂
  obtain ⟨hs₁i, -⟩ := fdet_mem_of_mem_finiteIntegralGL2 hs₁
  obtain ⟨-, hs₂i'⟩ := fdet_mem_of_mem_finiteIntegralGL2 hs₂
  obtain ⟨-, hu₁i'⟩ := fdet_mem_of_mem_finiteIntegralGL2 (glFin_mem_finiteIntegralGL2_of_mem_U hu₁)
  obtain ⟨hu₂i, -⟩ := fdet_mem_of_mem_finiteIntegralGL2 (glFin_mem_finiteIntegralGL2_of_mem_U hu₂)
  have hu₁c := fdet_mul_fdet_inv (glFin (𝓞 ℚ) ℚ u₁)
  have hs₂c := fdet_mul_fdet_inv (glFin (𝓞 ℚ) ℚ s₂)
  have hγ₂ : ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) ≠ 0 := (GeneralLinearGroup.det γ₂).ne_zero
  have ha₂ : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) *
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hγ₂, map_one]
  have ha₁ : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ) =
      fdet (glFin (𝓞 ℚ) ℚ s₁) * fdet (glFin (𝓞 ℚ) ℚ x) * fdet (glFin (𝓞 ℚ) ℚ u₁)⁻¹ := by
    calc algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ)
        = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ) *
            (fdet (glFin (𝓞 ℚ) ℚ u₁) * fdet (glFin (𝓞 ℚ) ℚ u₁)⁻¹) := by rw [hu₁c, mul_one]
      _ = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ) *
            fdet (glFin (𝓞 ℚ) ℚ u₁) * fdet (glFin (𝓞 ℚ) ℚ u₁)⁻¹ := by rw [mul_assoc]
      _ = fdet (glFin (𝓞 ℚ) ℚ s₁) * fdet (glFin (𝓞 ℚ) ℚ x) * fdet (glFin (𝓞 ℚ) ℚ u₁)⁻¹ := by rw [← e₁]
  have hx : fdet (glFin (𝓞 ℚ) ℚ x) =
      fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹ *
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) *
          fdet (glFin (𝓞 ℚ) ℚ u₂)) := by
    calc fdet (glFin (𝓞 ℚ) ℚ x)
        = (fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹ * fdet (glFin (𝓞 ℚ) ℚ s₂)) * fdet (glFin (𝓞 ℚ) ℚ x) := by
          rw [mul_comm (fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹), hs₂c, one_mul]
      _ = fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹ * (fdet (glFin (𝓞 ℚ) ℚ s₂) * fdet (glFin (𝓞 ℚ) ℚ x)) := by
          rw [mul_assoc]
      _ = fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹ *
            (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) *
              fdet (glFin (𝓞 ℚ) ℚ u₂)) := by rw [e₂]
  rw [map_mul, ha₁, hx]
  have hre : fdet (glFin (𝓞 ℚ) ℚ s₁) *
        (fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹ *
          (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) *
            fdet (glFin (𝓞 ℚ) ℚ u₂))) *
        fdet (glFin (𝓞 ℚ) ℚ u₁)⁻¹ *
        algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)⁻¹ =
      fdet (glFin (𝓞 ℚ) ℚ s₁) * fdet (glFin (𝓞 ℚ) ℚ s₂)⁻¹ * fdet (glFin (𝓞 ℚ) ℚ u₂) *
          fdet (glFin (𝓞 ℚ) ℚ u₁)⁻¹ *
        (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) *
          algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)⁻¹) := by
    ring
  rw [hre, ha₂, mul_one]
  exact mul_mem_integralFiniteAdeles
    (mul_mem_integralFiniteAdeles (mul_mem_integralFiniteAdeles hs₁i hs₂i') hu₂i) hu₁i'

private theorem abs_det_eq_abs_det {N : Ideal (𝓞 ℚ)} {x s₁ s₂ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hs₁ : glFin (𝓞 ℚ) ℚ s₁ ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    (hs₂ : glFin (𝓞 ℚ) ℚ s₂ ∈ finiteIntegralGL2 (𝓞 ℚ) ℚ)
    {γ₁ γ₂ : GL (Fin 2) ℚ} {h₁ u₁ h₂ u₂ : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)}
    (hu₁ : u₁ ∈ (productionPinsCompact ℚ).U N) (hfin₁ : glFin (𝓞 ℚ) ℚ h₁ = 1)
    (hg₁ : s₁ * x = globalPoints (𝓞 ℚ) ℚ γ₁ * h₁ * u₁)
    (hu₂ : u₂ ∈ (productionPinsCompact ℚ).U N) (hfin₂ : glFin (𝓞 ℚ) ℚ h₂ = 1)
    (hg₂ : s₂ * x = globalPoints (𝓞 ℚ) ℚ γ₂ * h₂ * u₂) :
    |((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ)| = |((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)| := by
  have hq₁ := algebraMap_det_mul_inv_det_mem hs₁ hs₂ hu₁ hfin₁ hg₁ hu₂ hfin₂ hg₂
  have hq₂ := algebraMap_det_mul_inv_det_mem hs₂ hs₁ hu₂ hfin₂ hg₂ hu₁ hfin₁ hg₁
  have hinv : (((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ) * ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)⁻¹)⁻¹ =
      ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ) * ((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ)⁻¹ := by
    rw [mul_inv, inv_inv, mul_comm]
  have hne : ((GeneralLinearGroup.det γ₁ : ℚˣ) : ℚ) * ((GeneralLinearGroup.det γ₂ : ℚˣ) : ℚ)⁻¹ ≠ 0 :=
    mul_ne_zero (GeneralLinearGroup.det γ₁).ne_zero (inv_ne_zero (GeneralLinearGroup.det γ₂).ne_zero)
  have habs := abs_eq_one_of_mem_integral hne hq₁ (by rw [hinv]; exact hq₂)
  rw [abs_mul, abs_inv] at habs
  exact (mul_inv_eq_one₀ (abs_pos.mpr (GeneralLinearGroup.det γ₂).ne_zero).ne').mp habs

private theorem exists_bound_on_translate (N : Ideal (𝓞 ℚ)) (f : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) (c u d₁ d₂ : ℝ)
    (x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ B : ℝ, ∀ s ∈ centreCutSiegelSet ℚ c u d₁ d₂, ‖weightOneLift N f (s * x)‖ ≤ B := by
  by_cases hex : ∃ s₀ ∈ centreCutSiegelSet ℚ c u d₁ d₂, HasWeightOneDecomp N (s₀ * x)
  · obtain ⟨s₀, hs₀, hd₀⟩ := hex
    obtain ⟨γ₀, h₀, u₀, hu₀, hfin₀, _, hg₀⟩ := hd₀
    set κ : ℝ := ((|((GeneralLinearGroup.det γ₀ : ℚˣ) : ℚ)| : ℚ) : ℝ) with hκ_def
    have hκ : 0 < κ := by
      rw [hκ_def]
      exact_mod_cast abs_pos.mpr (GeneralLinearGroup.det γ₀).ne_zero
    refine ⟨|C| * Real.sqrt (d₂ * archDetNorm (default : InfinitePlace ℚ) x / κ), ?_⟩
    intro s hs
    unfold DihedralWeightOne.weightOneLift
    split_ifs with H
    · obtain ⟨hu, hfin, hpos, hg⟩ := H.choose_spec.choose_spec.choose_spec
      set γ := H.choose with hγ_def
      set h := H.choose_spec.choose with hh_def
      set u' := H.choose_spec.choose_spec.choose with hu'_def
      have hpos' : 0 < (ratArch h).det.val := hpos
      have hR1 := norm_weightOneArchLift_le f C hC (ratArch h) hpos'
      have hdet : (ratArch h).det.val = archDetNorm (default : InfinitePlace ℚ) h := by
        rw [archDetNorm_default_eq, abs_of_pos hpos']
      have hsx : archDetNorm (default : InfinitePlace ℚ) (s * x) =
          |(((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ)| * archDetNorm (default : InfinitePlace ℚ) h := by
        rw [hg, archDetNorm_default_mul, archDetNorm_default_mul, archDetNorm_default_eq_one_of_mem_U hu,
          mul_one, archDetNorm_default_eq (globalPoints (𝓞 ℚ) ℚ γ), det_ratArch_globalPoints]
      have hγ : |((GeneralLinearGroup.det γ : ℚˣ) : ℚ)| = |((GeneralLinearGroup.det γ₀ : ℚˣ) : ℚ)| :=
        abs_det_eq_abs_det hs.1 hs₀.1 hu hfin hg hu₀ hfin₀ hg₀
      have hγR : |(((GeneralLinearGroup.det γ : ℚˣ) : ℚ) : ℝ)| = κ := by
        rw [hκ_def, ← Rat.cast_abs, hγ]
      have hsd : archDetNorm (default : InfinitePlace ℚ) s ≤ d₂ := (hs.2.2.2 default).2
      have hAx : 0 ≤ archDetNorm (default : InfinitePlace ℚ) x := (archDetNorm_pos _ x).le
      have hbound : archDetNorm (default : InfinitePlace ℚ) (s * x) ≤
          d₂ * archDetNorm (default : InfinitePlace ℚ) x := by
        rw [archDetNorm_default_mul]
        exact mul_le_mul_of_nonneg_right hsd hAx
      have hh : (ratArch h).det.val ≤ d₂ * archDetNorm (default : InfinitePlace ℚ) x / κ := by
        rw [le_div_iff₀ hκ, hdet]
        calc archDetNorm (default : InfinitePlace ℚ) h * κ
            = κ * archDetNorm (default : InfinitePlace ℚ) h := mul_comm _ _
          _ = archDetNorm (default : InfinitePlace ℚ) (s * x) := by rw [hsx, hγR]
          _ ≤ d₂ * archDetNorm (default : InfinitePlace ℚ) x := hbound
      calc ‖weightOneArchLift f (LanglandsTunnell.ratArchGL2 h)‖
          = ‖weightOneArchLift f (ratArch h)‖ := rfl
        _ ≤ C * Real.sqrt (ratArch h).det.val := hR1
        _ ≤ |C| * Real.sqrt (ratArch h).det.val :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _)
        _ ≤ |C| * Real.sqrt (d₂ * archDetNorm (default : InfinitePlace ℚ) x / κ) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hh) (abs_nonneg C)
    · rw [norm_zero]
      positivity
  · refine ⟨0, fun s hs => ?_⟩
    have hnot : ¬ HasWeightOneDecomp N (s * x) := fun hd => hex ⟨s, hs, hd⟩
    unfold DihedralWeightOne.weightOneLift
    rw [dif_neg hnot, norm_zero]

private theorem windowBound_of_bound (N : Ideal (𝓞 ℚ)) (f : ℍ → ℂ) (C : ℝ)
    (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    IsBoundedOnSiegelWindows ℚ (weightOneLift N f) := by
  intro c u d₁ d₂ T _ _
  choose B hB using fun x : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) =>
    exists_bound_on_translate N f C hC c u d₁ d₂ x
  refine ⟨T.sum fun y => |B y|, ?_⟩
  intro g hg
  rw [Set.mem_iUnion₂] at hg
  obtain ⟨x, hxT, s, hs, rfl⟩ := hg
  calc ‖weightOneLift N f (s * x)‖ ≤ B x := hB x s hs
    _ ≤ |B x| := le_abs_self _
    _ ≤ T.sum fun y => |B y| := Finset.single_le_sum (fun y _ => abs_nonneg (B y)) hxT

end

end P2GProbe.WindowBound

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne in
theorem solution
    {n : ℕ} (f : ℍ → ℂ)
    (C : ℝ) (hC : ∀ τ : ℍ, ‖f τ‖ ≤ C / τ.im ^ (((1 : ℤ) : ℝ) / 2)) :
    IsBoundedOnSiegelWindows ℚ (weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f) := by
  exact P2GProbe.WindowBound.windowBound_of_bound _ f C hC

end S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift
end P2MW
export P2MW.S_LanglandsTunnell_isBoundedOnSiegelWindows_weightOneLift (solution)
