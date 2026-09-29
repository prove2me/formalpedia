-- Prove2me | solution 1 for ModularCurve.differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9ccdbc25-fe6a-5a73-ad52-652e1111d6e5

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm
import Theorems.Thm_AlgebraicCurve_traceDiff_apply
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D

set_option autoImplicit false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along SeparableAlong Differential.pullbackAlong Differential.pullbackAlong_D Differential.pullbackAlong_smul Differential.traceAlong Differential.traceAlong_smul_pullbackAlong Differential.correspondence Differential.correspondence_apply traceDiff traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm traceDiff_apply"
namespace D6bGlue
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pullbackAlong_dlog (φ : F →ₐ[K] F') (f : F) :
    Differential.pullbackAlong φ (f⁻¹ • D K F f) = (φ f)⁻¹ • D K F' (φ f) := by
  rw [Differential.pullbackAlong_smul, Differential.pullbackAlong_D, map_inv₀]

theorem traceAlong_apply_eq_traceDiff (ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ)
    (ω' : Ω[F'⁄K]) :
    Differential.traceAlong ψ ω' =
      (letI := algebraAlong ψ; haveI := isScalarTower_along ψ; traceDiff K F F' ω') := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Algebra.IsSeparable F F' := hsep
  haveI : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  obtain ⟨t, rfl⟩ := (tensorKaehlerEquivOfFormallyEtale K F F').surjective ω'
  induction t using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u ω =>
      have htm : tensorKaehlerEquivOfFormallyEtale K F F' (u ⊗ₜ ω) =
          u • Differential.pullbackAlong ψ ω := by
        rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul]
        rfl
      rw [htm, Differential.traceAlong_smul_pullbackAlong ψ hsep]
      exact (AlgebraicCurve.traceDiff_apply K F F' u ω).symm

theorem traceAlong_pullbackAlong_dlog (φ ψ : F →ₐ[K] F') (hsep : SeparableAlong K ψ) (f : F) :
    Differential.traceAlong ψ (Differential.pullbackAlong φ (f⁻¹ • D K F f)) =
      (letI := algebraAlong ψ; Algebra.norm F (φ f))⁻¹ •
        D K F (letI := algebraAlong ψ; Algebra.norm F (φ f)) := by
  letI := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Algebra.IsSeparable F F' := hsep
  rw [pullbackAlong_dlog, traceAlong_apply_eq_traceDiff ψ hsep]
  exact AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm K F F' (φ f)

end AlgebraicCurve.D6bGlue

end

theorem solution
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hsep : haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
      AlgebraicCurve.SeparableAlong K (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ))
    (f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
        AlgebraicCurve.Differential.correspondence (ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ) (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ))
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ f))⁻¹ •
        KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩;
            @Algebra.norm (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM) ⊓ CongruenceSubgroup.Gamma0 ((M / p) * ℓ))) _ _
              ((ModularCurve.heckeAlphaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ).toRingHom.toAlgebra)
              (ModularCurve.heckeBetaModLH K (M / p) (ModularCurve.infSubgroup p M H hpM) ℓ f)) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  rw [AlgebraicCurve.Differential.correspondence_apply]
  exact AlgebraicCurve.D6bGlue.traceAlong_pullbackAlong_dlog _ _ hsep f

end S_ModularCurve_differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D
end P2MW
export P2MW.S_ModularCurve_differentialCorrespondence_heckeAlphaModLH_heckeBetaModLH_inv_smul_D (solution)
