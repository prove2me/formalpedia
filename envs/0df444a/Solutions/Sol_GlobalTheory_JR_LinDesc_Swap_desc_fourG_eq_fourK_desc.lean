-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.Swap.desc_fourG_eq_fourK_desc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:42:01.460801+00:00
-- url     : https://prove2.me/submissions/df3ebbae-64d7-4721-8859-c1953862d6fa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearDescentPartialFourierEqFourierDescent
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_eta_det
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_psi
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_act
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_K_inst
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_continuous_pt
import Theorems.Thm_GlobalTheory_JR_LinDesc_Swap_swap_triple
import Theorems.Thm_GlobalTheory_JR_EtInv_invK_regular_iff_isUnit


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc GlobalTheory.JR.LinDesc.Swap
namespace GlobalTheory.JR.LinDesc.Swap
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ μK : Measure A.K, SelfDual μK (A.kerK ψ) → ∀ (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → (∀ (g : GL (Fin r) F) (b c : A.K), fourG M ψ f' (act g (LinDesc.pt A hG lam b c)) = A.fourK μK ψ (fun x => f' (act g (LinDesc.pt A hG lam x.1 x.2))) (b, c)) → ∀ x : A.K × A.K, LinDesc.desc A M hG lam α (fourG M ψ f') x = A.fourK μK ψ (LinDesc.desc A M hG lam α f') x := by
  intro F E _ _ _ _ _ A r τ p hG lam M ψ hψ μK hμK α f' hf' hα hαc hyp x
  letI := M.mG
  haveI := M.bG
  haveI := M.haarG
  haveI : LocallyCompactSpace F := Unram.lcF (F := F) (E := E)
  haveI : IsUltrametricDist F := Unram.ultraF (F := F) (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨hT2, hSC⟩ := K_inst A hG
  haveI := hT2
  haveI := hSC
  haveI := hμK.1
  set k : GL (Fin r) F → A.K → A.K → ℂ := fun g b' c' =>
    f' (act g (pt A hG lam b' c')) * A.psiK ψ (x.1 * c' + b' * x.2) *
      (eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ)) with hk
  have hL : desc A M hG lam α (fourG M ψ f') x = ∫ g, ∫ b', ∫ c', k g b' c' ∂μK ∂μK ∂M.μG := by
    unfold desc
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    rw [hyp g x.1 x.2]
    unfold Et.fourK
    rw [mul_assoc, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
    simp only
    rw [← integral_mul_const]
  have hR : A.fourK μK ψ (desc A M hG lam α f') x = ∫ b', ∫ c', ∫ g, k g b' c' ∂M.μG ∂μK ∂μK := by
    unfold Et.fourK desc
    refine integral_congr_ae (Eventually.of_forall fun b' => ?_)
    refine integral_congr_ae (Eventually.of_forall fun c' => ?_)
    simp only
    rw [← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [hk]; ring
  rw [hL, hR]
  have hbij := (GlobalTheory.JR.EtInv.invK_regular_iff_isUnit F E A r τ p lam hG).1
  let ρl : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i : Fin r => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  let ρe : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρl (by exact hbij)
  have hρs : Continuous ρe.symm := IsModuleTopology.continuous_of_linearMap ρe.symm.toLinearMap
  have hes : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (bas A hG).equivFun.symm.toLinearMap
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hST : IsCompact (tsupport α ×ˢ tsupport f') := hαc.prod hf'.2
  refine swap_triple M.μG μK k ?_ (tsupport α)
    ((bas A hG).equivFun.symm '' ((fun z : GL (Fin r) F × Gl r F =>
      ((z.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) *ᵥ z.2.2.1) '' (tsupport α ×ˢ tsupport f')))
    (ρe.symm '' ((fun z : GL (Fin r) F × Gl r F =>
      z.2.2.2.1 ᵥ* (z.1 : Matrix (Fin r) (Fin r) F)) '' (tsupport α ×ˢ tsupport f')))
    hαc ?_ ?_ ?_
  · have h1 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => f' (act z.2 (pt A hG lam z.1.1 z.1.2))) :=
      hf'.1.continuous.comp ((continuous_act r).comp
        (continuous_snd.prodMk ((continuous_pt A hG lam).comp continuous_fst)))
    have h2 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => A.psiK ψ (x.1 * z.1.2 + z.1.1 * x.2)) :=
      (continuous_psi ψ hψ).comp (htr.comp
        ((continuous_const.mul continuous_fst.snd).add (continuous_fst.fst.mul continuous_const)))
    have h3 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => eta ((z.2 : Matrix (Fin r) (Fin r) F).det)) :=
      (continuous_eta_det r).comp continuous_snd
    have h4 : Continuous (fun z : (A.K × A.K) × GL (Fin r) F => ((α z.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (hα.continuous.comp continuous_snd)
    exact (h1.mul h2).mul (h3.mul h4)
  · exact (hST.image ((Units.continuous_coe_inv.comp continuous_fst).matrix_mulVec
      continuous_snd.snd.fst)).image hes
  · exact (hST.image (continuous_snd.snd.snd.fst.matrix_vecMul
      (Units.continuous_val.comp continuous_fst))).image hρs
  · intro g b c hne
    have hf0 : f' (act g (pt A hG lam b c)) ≠ 0 := fun h => hne (by simp only [hk, h, zero_mul])
    have hα0 : α g ≠ 0 := fun h => hne (by simp only [hk, h, Complex.ofReal_zero, mul_zero])
    have hgS : g ∈ tsupport α := subset_tsupport _ hα0
    have hYT : act g (pt A hG lam b c) ∈ tsupport f' := subset_tsupport _ hf0
    have hinv : ((g⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) * (g : Matrix (Fin r) (Fin r) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    refine ⟨hgS, ⟨_, ⟨(g, _), ⟨hgS, hYT⟩, rfl⟩, ?_⟩, ⟨_, ⟨(g, _), ⟨hgS, hYT⟩, rfl⟩, ?_⟩⟩
    · simp only [act, pt, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, LinearEquiv.symm_apply_apply]
    · have hρc : ρe c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := rfl
      simp only [act, pt, Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
      rw [← hρc, LinearEquiv.symm_apply_apply]
end GlobalTheory.JR.LinDesc.Swap
