-- Prove2me | solution 1 for GlobalTheory.JR.LinDesc.desc_isTest
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:48:27.890562+00:00
-- url     : https://prove2.me/submissions/38fd4e30-e779-487a-a0ff-e70980db977d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LeftMulTau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisInvKRegularIffIsUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocallyConstantCompactSupportJacquetRallisDesc
import Theorems.Thm_GlobalTheory_JR_LinDesc_eta_det_isLocallyConstant
import Theorems.Thm_GlobalTheory_JR_LinDesc_act_mul
import Theorems.Thm_GlobalTheory_JR_LinDesc_act_one
import Theorems.Thm_GlobalTheory_T_jacquetRallis_invK_regular_iff_isUnit


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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.LinDesc
set_option maxHeartbeats 800000
namespace GlobalTheory.JR.LinDesc
theorem _root_.solution : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ (M : Meas r F E) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ), IsTest f' → IsLocallyConstant α → HasCompactSupport α → IsTest (LinDesc.desc A M hG lam α f') := by
  intro F E _ _ _ _ hU A r τ p hG lam M α f' hf hα hαc
  haveI : IsUltrametricDist F := hU.ultraF

  let ρL : A.K →ₗ[F] (Fin r → F) :=
    LinearMap.pi fun i => (Algebra.trace F A.K).comp (LinearMap.mulLeft F (τ ^ (i : ℕ)))
  have hρL : ∀ c, ρL c = fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c) := fun c => rfl
  have hbij : Function.Bijective ρL := by
    have := (GlobalTheory.T.jacquetRallis_invK_regular_iff_isUnit F E A r τ p lam hG).1
    rw [show (⇑ρL) = fun (a : A.K) (i : Fin r) => Algebra.trace F A.K (τ ^ (i : ℕ) * a) from funext hρL]
    exact this
  let ρE : A.K ≃ₗ[F] (Fin r → F) := LinearEquiv.ofBijective ρL hbij
  have hι : Continuous (bas A hG).equivFun :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.toLinearMap
  have hρ : Continuous ρL := IsModuleTopology.continuous_of_linearMap (R := F) ρL
  have hιs : Continuous (bas A hG).equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) (bas A hG).equivFun.symm.toLinearMap
  have hρs : Continuous ρE.symm :=
    IsModuleTopology.continuous_of_linearMap (R := F) ρE.symm.toLinearMap
  have hpt : Continuous (fun x : A.K × A.K => pt A hG lam x.1 x.2) := by
    unfold pt
    exact continuous_const.prodMk ((hι.comp continuous_fst).prodMk
      ((hρ.comp continuous_snd).prodMk continuous_const))
  have hact : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1 q.2) := by
    unfold act
    have h1 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1 : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp continuous_fst
    have h2 : Continuous (fun q : GL (Fin r) F × Gl r F => ((q.1⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F)) :=
      Units.continuous_val.comp (continuous_inv.comp continuous_fst)
    exact ((h1.matrix_mul (continuous_fst.comp continuous_snd)).matrix_mul h2).prodMk
      ((h1.matrix_mulVec (continuous_fst.comp (continuous_snd.comp continuous_snd))).prodMk
        (((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).matrix_vecMul h2).prodMk
          (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))))
  have heta := eta_det_isLocallyConstant (F := F) r

  have hΦ : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F =>
      f' (act q.2 (pt A hG lam q.1.1 q.1.2)) * eta ((q.2 : Matrix (Fin r) (Fin r) F).det) * (α q.2 : ℂ)) := by
    have a1 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => f' (act q.2 (pt A hG lam q.1.1 q.1.2))) :=
      hf.1.comp_continuous (hact.comp (continuous_snd.prodMk (hpt.comp continuous_fst)))
    have a2 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => eta ((q.2 : Matrix (Fin r) (Fin r) F).det)) :=
      heta.comp_continuous continuous_snd
    have a3 : IsLocallyConstant (fun q : (A.K × A.K) × GL (Fin r) F => (α q.2 : ℂ)) :=
      (hα.comp_continuous continuous_snd).comp (fun t : ℝ => (t : ℂ))
    exact (a1.mul a2).mul a3
  have hloc : IsLocallyConstant (LinDesc.desc A M hG lam α f') := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x₀
    have h1 : ∀ᶠ x in 𝓝 x₀, ∀ g ∈ tsupport α,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) =
          f' (act g (pt A hG lam x₀.1 x₀.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) := by
      refine hαc.eventually_forall_of_forall_eventually fun g _ => ?_
      have h2 := (hΦ.prodMk (hΦ.comp_continuous (f := fun q : (A.K × A.K) × GL (Fin r) F => (x₀, q.2))
        (continuous_const.prodMk continuous_snd))).eventually_eq (x₀, g)
      filter_upwards [h2] with q hq
      simp only [Prod.mk.injEq, Function.comp] at hq
      rw [hq.1, hq.2]
    filter_upwards [h1] with x hx
    unfold desc
    congr 1
    funext g
    by_cases hg : g ∈ tsupport α
    · exact hx g hg
    · rw [image_eq_zero_of_notMem_tsupport hg]; simp
  refine ⟨hloc, ?_⟩

  let L : (Fin r → F) × (Fin r → F) → A.K × A.K := fun u => ((bas A hG).equivFun.symm u.1, ρE.symm u.2)
  have hL : Continuous L := (hιs.comp continuous_fst).prodMk (hρs.comp continuous_snd)
  let T : GL (Fin r) F × Gl r F → A.K × A.K := fun q => L ((act q.1⁻¹ q.2).2.1, (act q.1⁻¹ q.2).2.2.1)
  have hT : Continuous T := by
    have : Continuous (fun q : GL (Fin r) F × Gl r F => act q.1⁻¹ q.2) :=
      hact.comp ((continuous_inv.comp continuous_fst).prodMk continuous_snd)
    exact hL.comp ((continuous_fst.comp (continuous_snd.comp this)).prodMk
      (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp this))))
  have hS : IsCompact (T '' (tsupport α ×ˢ tsupport f')) := (hαc.prod hf.2).image hT
  have hsub : Function.support (LinDesc.desc A M hG lam α f') ⊆ T '' (tsupport α ×ˢ tsupport f') := by
    intro x hx
    by_contra hxS
    apply hx
    have h0 : ∀ g : GL (Fin r) F,
        f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) = 0 := by
      intro g
      by_contra hne
      apply hxS
      have hαg : α g ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      have hfg : f' (act g (pt A hG lam x.1 x.2)) ≠ 0 := by
        intro h0; apply hne; rw [h0]; simp
      refine ⟨(g, act g (pt A hG lam x.1 x.2)), ⟨subset_tsupport _ hαg, subset_tsupport _ hfg⟩, ?_⟩
      have hback : act g⁻¹ (act g (pt A hG lam x.1 x.2)) = pt A hG lam x.1 x.2 := by
        rw [← act_mul, inv_mul_cancel, act_one]
      show L ((act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.1, (act g⁻¹ (act g (pt A hG lam x.1 x.2))).2.2.1) = x
      rw [hback]
      show ((bas A hG).equivFun.symm ((bas A hG).equivFun x.1), ρE.symm (ρL x.2)) = x
      rw [LinearEquiv.symm_apply_apply]
      have : ρE.symm (ρL x.2) = x.2 := ρE.symm_apply_apply x.2
      rw [this]
    unfold desc
    simp only [h0, integral_zero]
  have hcl : IsClosed (Function.support (LinDesc.desc A M hG lam α f')) := by
    have := hloc.isOpen_fiber 0
    rw [← isOpen_compl_iff]
    convert this using 1
    ext x; simp
  unfold HasCompactSupport tsupport
  rw [hcl.closure_eq]
  exact hS.of_isClosed_subset hcl hsub
end GlobalTheory.JR.LinDesc
