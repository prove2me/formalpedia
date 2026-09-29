-- Prove2me | solution 1 for ModularCurve.heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/d5865cb3-354c-5cb8-ba95-5ba0a1863de1

import Mathlib
import Theorems.Thm_AlgebraicCurve_SemilinearAut_pullbackAlong_smul
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_ShimuraKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hβN : ModularCurve.HeckeBetaHDefined (M / p) (ModularCurve.infSubgroup p M H hpM) p)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H)]
    (ι : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) →ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H))
    (hιcoe : ∀ u : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      ((ι u : ↥(ModularCurve.xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hι : ι.toRingHom.IsIntegral) (hFIι : AlgebraicCurve.FundamentalIdentityAlong (AlgebraicClosure ℚ) ι hι)
    (hιs : Function.Surjective ι)
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (θ : ↥(ModularCurve.xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(ModularCurve.xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθ₂ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    ∀ (c : (ZMod (M / p))ˣ), (c : ZMod (M / p)) = (p : ZMod (M / p)) →
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = ((diamondAutHBar (M / p) (infSubgroup p M H hpM) c u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ))) :
    let ιe : ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))) ≃ₐ[AlgebraicClosure ℚ]
        ↥(ModularCurve.xHFunctionFieldBar M H) := AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hιs⟩
    let W := (ιe.trans θ.symm).trans ιe.symm
    (∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) ∧
    (∀ x : ↥(ModularCurve.xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM)),
        W (ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p x) =
          ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p
            ((ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pb).symm x)) ∧
    (∀ x₁ : Pic0 (AlgebraicClosure ℚ)
        ↥(ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.xHTopFunctionFieldC ℚ (M / p) (ModularCurve.infSubgroup p M H hpM) (M / p * p))),
      SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFIι x₁ =
        Pic0.pullbackAlongHom ι hι hFIι (SemilinearAut.ofAlgAut W.symm • x₁)) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  intro ιe W
  have hιe : ∀ a, ιe a = ι a := fun _ => rfl
  have hιe' : ∀ b, ι (ιe.symm b) = b := fun b => by rw [← hιe, AlgEquiv.apply_symm_apply]

  have hW : ∀ a, W a = ιe.symm (θ.symm (ι a)) := fun _ => rfl
  have hWs : ∀ a, ι (W.symm a) = θ (ι a) := by
    intro a
    show ι (ιe.symm (θ.symm.symm (ιe.symm.symm a))) = θ (ι a)
    rw [hιe', AlgEquiv.symm_symm, AlgEquiv.symm_symm, hιe]

  set α := ModularCurve.heckeAlphaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p with hαdef
  set β := ModularCurve.heckeBetaHBar (AlgebraicClosure ℚ) (M / p) (ModularCurve.infSubgroup p M H hpM) p with hβdef
  have pin1 : ∀ x, θ (ι (α x)) = ι (β x) := by
    intro x
    apply Subtype.ext
    rw [hθ (ι (α x)) x (by rw [hιcoe, hαdef, ModularCurve.coe_heckeAlphaHBar]), hιcoe, hβdef,
      ModularCurve.coe_heckeBetaHBar _ _ _ hβN]
  have pin2 : ∀ x, θ (ι (β x)) = ι (α (ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pb x)) := by
    intro x
    apply Subtype.ext
    rw [hθ₂ pb hpb (ι (β x)) x (by rw [hιcoe, hβdef, ModularCurve.coe_heckeBetaHBar _ _ _ hβN]), hιcoe, hαdef,
      ModularCurve.coe_heckeAlphaHBar]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x
    apply ι.toRingHom.injective
    show ι (W (β x)) = ι (α x)
    rw [hW, hιe', ← pin1, AlgEquiv.symm_apply_apply]
  ·
    intro x
    apply ι.toRingHom.injective
    show ι (W (α x)) = ι (β ((ModularCurve.diamondAutHBar (M / p) (ModularCurve.infSubgroup p M H hpM) pb).symm x))
    rw [hW, hιe']
    apply θ.injective
    rw [AlgEquiv.apply_symm_apply, pin2, AlgEquiv.apply_symm_apply]
  ·
    have hint : SemilinearAut.IntertwinesAlong ι.toRingHom (SemilinearAut.ofAlgAut W.symm) (SemilinearAut.ofAlgAut θ) := by
      intro x
      rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
      exact (hWs x).symm
    intro x₁
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x₁
    rw [Pic0.pullbackAlongHom_mk, SemilinearAut.pic0_smul_mk, SemilinearAut.pic0_smul_mk, Pic0.pullbackAlongHom_mk]
    congr 1
    apply Subtype.ext
    rw [SemilinearAut.coe_degZeroSMulHom, Pic0.coe_pullbackAlongDegZeroHom, Pic0.coe_pullbackAlongDegZeroHom,
      SemilinearAut.coe_degZeroSMulHom, SemilinearAut.pullbackAlong_smul ι hι hint]

end S_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins
end P2MW
export P2MW.S_ModularCurve_heckeBetaHBar_pins_and_smul_pullbackAlongHom_of_qExpand_pins (solution)
