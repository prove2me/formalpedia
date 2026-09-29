-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.w_hom_comp_eq_comp_w_hom_of_pinned
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5ad11b84-154c-5a8b-8213-df224ca8f21a

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_mul_eq_qExpand_of_coe_eq_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_w_hom_comp_eq_comp_w_hom_of_pinned
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_w_hom_comp_eq_comp_w_hom_of_pinned.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRLevel.R DRLevel.X DRLevel.toBase DRModelPackageLevel IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin qExpand modularFunctionFieldFull atkinLehnerInvolutionFull coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq coe_atkinLehnerInvolutionFull_mul_eq_qExpand_of_coe_eq_qExpand"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "isProper theta_spec w comp w_over theta isIntegral w_chart π"
namespace WCompat
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

private theorem isDominant_ιFin (M q : ℕ) [NeZero M] [Fact q.Prime] [IsIntegral (IgusaScheme M q)] :
    IsDominant (IgusaScheme.ιFin M q) :=
  ⟨(IgusaScheme.ιFin M q).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)⟩

private theorem comm_of_chart (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ)
    (π : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hπ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π.1 = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hθ : ∀ b, 𝔓'.theta (ι b) = ι (𝔓.theta b)) :
    𝔓'.w.hom ≫ π.1 = π.1 ≫ 𝔓.w.hom := by
  haveI : IsIntegral (DRLevel.X (N₀ * ℓ) q) := 𝔓'.isIntegral
  haveI : IsProper (DRLevel.toBase N₀ q) := 𝔓.isProper
  haveI := isDominant_ιFin (N₀ * ℓ * q) q
  have hring : 𝔓'.theta.toRingEquiv.toRingHom.comp ι.toRingHom = ι.toRingHom.comp 𝔓.theta.toRingEquiv.toRingHom :=
    RingHom.ext fun b => by simpa using hθ b
  refine ext_of_isDominant_of_isSeparated (DRLevel.toBase N₀ q) ?_ (IgusaScheme.ιFin (N₀ * ℓ * q) q) ?_
  · rw [Category.assoc, Category.assoc, π.2, 𝔓'.w_over, 𝔓.w_over, π.2]
  · calc IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ 𝔓'.w.hom ≫ π.1
          = Spec.map (CommRingCat.ofHom 𝔓'.theta.toRingEquiv.toRingHom) ≫ Spec.map (CommRingCat.ofHom ι.toRingHom) ≫
              IgusaScheme.ιFin (N₀ * q) q := by
            rw [← Category.assoc, 𝔓'.w_chart, Category.assoc, hπ]
      _ = Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ Spec.map (CommRingCat.ofHom 𝔓.theta.toRingEquiv.toRingHom) ≫
              IgusaScheme.ιFin (N₀ * q) q := by
            rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
      _ = IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π.1 ≫ 𝔓.w.hom := by
            rw [← Category.assoc (IgusaScheme.ιFin (N₀ * ℓ * q) q), hπ, Category.assoc, 𝔓.w_chart]

end ModularCurve.DRModelPackageLevel.WCompat

open ModularCurve.DRModelPackageLevel.WCompat in

theorem solution (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)
    (𝔓 : DRModelPackageLevel N₀ q hqN) (ℓ : ℕ) [Fact ℓ.Prime] (hqNℓ : ¬ q ∣ N₀ * ℓ)
    (𝔓' : DRModelPackageLevel (N₀ * ℓ) q hqNℓ)
    (π₁ π₂ : SchemeHomOver (DRLevel.toBase (N₀ * ℓ) q) (DRLevel.toBase N₀ q))
    (ι₁ ι₂ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) →ₐ[DRLevel.R q] ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q))
    (hι₁ : ∀ b, (((ι₁ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hι₂ : ∀ b, (((ι₂ b : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
        qExpand ℚ ℓ ((b : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ))
    (hπ₁ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₁.1 = Spec.map (CommRingCat.ofHom ι₁.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q)
    (hπ₂ : IgusaScheme.ιFin (N₀ * ℓ * q) q ≫ π₂.1 = Spec.map (CommRingCat.ofHom ι₂.toRingHom) ≫ IgusaScheme.ιFin (N₀ * q) q) :
    𝔓'.w.hom ≫ π₁.1 = π₁.1 ≫ 𝔓.w.hom ∧ 𝔓'.w.hom ≫ π₂.1 = π₂.1 ≫ 𝔓.w.hom := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have coeInj : ∀ {x y : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)},
      (((x : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) =
      (((y : ↥(IgusaScheme.chartAlgFin (N₀ * ℓ * q) q)) : ↥(modularFunctionFieldFull (N₀ * ℓ * q))) : LaurentSeries ℚ) → x = y :=
    fun h => Subtype.ext (Subtype.ext h)
  refine ⟨comm_of_chart N₀ q hqN 𝔓 ℓ hqNℓ 𝔓' π₁ ι₁ hπ₁ fun b => coeInj ?_,
    comm_of_chart N₀ q hqN 𝔓 ℓ hqNℓ 𝔓' π₂ ι₂ hπ₂ fun b => coeInj ?_⟩
  · rw [𝔓'.theta_spec, hι₁ (𝔓.theta b), 𝔓.theta_spec]
    exact coe_atkinLehnerInvolutionFull_mul_eq_of_coe_eq N₀ q ℓ hqNℓ _ _ (hι₁ b)
  · rw [𝔓'.theta_spec, hι₂ (𝔓.theta b), 𝔓.theta_spec]
    exact coe_atkinLehnerInvolutionFull_mul_eq_qExpand_of_coe_eq_qExpand N₀ q ℓ hqNℓ _ _ (hι₂ b)

end S_ModularCurve_DRModelPackageLevel_w_hom_comp_eq_comp_w_hom_of_pinned
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_w_hom_comp_eq_comp_w_hom_of_pinned (solution)
