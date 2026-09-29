-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/f56450f2-88ff-5365-8aa2-a4cd19af4c31

import Definitions.Def_ModularCurve_DRModelPackageLevel
import Theorems.Thm_ModularCurve_atkinLehnerInvolutionFull_apply_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
p2m_open "ModularCurve P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top.ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel"

namespace ModularCurve
p2m_export "ModularCurve" "DRModelPackageLevel.neZero_mul DRModelPackageLevel IgusaScheme.chartAlgFin IgusaScheme IgusaScheme.ιFin modularFunctionFieldFull atkinLehnerInvolutionFull_apply_apply"
namespace DRModelPackageLevel
p2m_export "ModularCurve.DRModelPackageLevel" "neZero_mul theta_spec w theta w_chart"
p2m_open "ModularCurve.DRModelPackageLevel ModularCurve"

namespace DisjAux

variable {N₀ q : ℕ} [NeZero N₀] [Fact q.Prime] {hqN : ¬ q ∣ N₀} (𝔓 : DRModelPackageLevel N₀ q hqN)

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem theta_theta (b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : 𝔓.theta (𝔓.theta b) = b := by
  apply Subtype.ext
  change ((𝔓.theta (𝔓.theta b) : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) = _
  rw [𝔓.theta_spec, 𝔓.theta_spec, atkinLehnerInvolutionFull_apply_apply N₀ q hqN]

theorem w_ιFin (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :
    𝔓.w.hom.base ((IgusaScheme.ιFin (N₀ * q) q).base 𝔮) =
      (IgusaScheme.ιFin (N₀ * q) q).base ((Spec.map (CommRingCat.ofHom 𝔓.theta.toRingEquiv.toRingHom)).base 𝔮) := by
  rw [← Scheme.Hom.comp_apply, 𝔓.w_chart, Scheme.Hom.comp_apply]

theorem asIdeal_specMap_theta (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) :
    ((Spec.map (CommRingCat.ofHom 𝔓.theta.toRingEquiv.toRingHom)).base 𝔮).asIdeal = Ideal.comap 𝔓.theta.toRingEquiv.toRingHom 𝔮.asIdeal :=
  rfl

end DisjAux

end ModularCurve.DRModelPackageLevel

open _root_.ModularCurve.DRModelPackageLevel _root_.P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top.ModularCurve.DRModelPackageLevel ModularCurve.DRModelPackageLevel.DisjAux in
attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul in

theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (a b : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hab : Ideal.span {a} ⊔ Ideal.span {𝔓.theta b} = ⊤)
    (𝔮 𝔮' : PrimeSpectrum ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) (ha : a ∈ 𝔮.asIdeal) (hb : b ∈ 𝔮'.asIdeal) :
    (IgusaScheme.ιFin (N₀ * q) q).base 𝔮 ≠ 𝔓.w.hom.base ((IgusaScheme.ιFin (N₀ * q) q).base 𝔮') := by
  intro heq
  rw [w_ιFin] at heq
  have h𝔮 := (IgusaScheme.ιFin (N₀ * q) q).isOpenEmbedding.injective heq
  have hθb : 𝔓.theta b ∈ 𝔮.asIdeal := by
    rw [h𝔮, asIdeal_specMap_theta, Ideal.mem_comap]
    change 𝔓.theta (𝔓.theta b) ∈ 𝔮'.asIdeal
    rw [theta_theta]
    exact hb
  exact 𝔮.isPrime.ne_top (top_le_iff.1 (hab ▸ sup_le ((Ideal.span_singleton_le_iff_mem _).2 ha) ((Ideal.span_singleton_le_iff_mem _).2 hθb)))

end S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top (solution)
