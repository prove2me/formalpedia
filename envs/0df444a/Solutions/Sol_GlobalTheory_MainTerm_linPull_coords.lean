-- Prove2me | solution 1 for GlobalTheory.MainTerm.linPull_coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:54:14.794967+00:00
-- url     : https://prove2.me/submissions/4284ebc1-70c7-4e07-ba51-507e7041195a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_CoeffSubstSumLPowPowMvPowerSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FormalGroupCoordinatesPullbackLinearTangentBasis
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_U_det_ne
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_be_zero
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_Sys_cur_zero_inl
import Theorems.Thm_GlobalTheory_T_coeff_subst_sum_l_pow_pow_mvPowerSeries


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
open GlobalTheory GlobalTheory.MainTerm
namespace GlobalTheory.MainTerm
theorem _root_.solution : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) (I J : Type) [Fintype I] [Fintype J] (G : Cart V d I J) (S : Sys G) (t : I → MvPowerSeries I C), S.IsT t → ∀ (ι : Type) [Fintype ι] (e : ι → I → C) (z : I → ι → C) (al : I → ℕ → I → C), (∀ j x, e j x = ∑ b, z b j * S.tan b x) → (∀ c b, al c 0 b = if c = b then 1 else 0) → (∀ c (k : ℕ) x, 1 ≤ k → S.al c k x = ∑ b, al c k b * S.al b 0 x) → (∀ c, MvPowerSeries.constantCoeff (linPull e (t c)) = 0) ∧ (∀ (b : I) (μ : ι →₀ ℕ), ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) = MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b j) * (MvPowerSeries.X j : MvPowerSeries ι C))) ∧ ∀ (κ : J) (μ : ι →₀ ℕ), MvPowerSeries.coeff μ (linPull e (S.ze t κ)) = -∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.be c s κ * MvPowerSeries.coeff μ (linPull e (t c) ^ (V.l ^ s)) := by
  intro C _ V d I J _ _ G S t ht ι _ e z al he hal0 hal
  obtain ⟨f, hf⟩ : ∃ f : I → MvPowerSeries ι C,
      f = fun x => ∑ j, e j x • (MvPowerSeries.X j : MvPowerSeries ι C) := ⟨_, rfl⟩
  have hlp : ∀ F : MvPowerSeries I C, linPull e F = MvPowerSeries.subst f F := by
    intro F; subst hf; rfl
  have hf0 : ∀ x, MvPowerSeries.constantCoeff (f x) = 0 := by
    intro x
    simp [hf, map_sum, MvPowerSeries.smul_eq_C_mul]
  have hsub : MvPowerSeries.HasSubst f := MvPowerSeries.hasSubst_of_constantCoeff_zero hf0
  have hl : 2 ≤ V.l := V.l_prime.two_le
  have hal' : ∀ c s x, S.al c s x = ∑ b', al c s b' * S.tan b' x := by
    intro c s x
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · simp only [hal0, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      exact S.cur_zero_inl c x
    · rw [hal c s x hs]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [show S.al b' 0 x = S.tan b' x from S.cur_zero_inl b' x]
  simp only [hlp]
  refine ⟨fun c => MvPowerSeries.constantCoeff_subst_eq_zero hsub hf0 (ht.1 c), fun b μ => ?_,
    fun κ μ => ?_⟩
  · set P : I → ℕ → C := fun c s =>
      MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) with hP
    set Y : I → C := fun b' => ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s with hY
    set Zf : I → C := fun b' =>
      MvPowerSeries.coeff μ (∑ j, MvPowerSeries.C (R := C) (z b' j) *
        (MvPowerSeries.X j : MvPowerSeries ι C)) with hZ
    have hx : ∀ x, ∑ b', (Y b' - Zf b') * S.tan b' x = 0 := by
      intro x
      have h := GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => S.al c s x) t (MvPowerSeries.X x) f hf0 ht.1
        (fun μ' => by rw [MvPowerSeries.coeff_X, ht.2 x μ']) μ
      rw [MvPowerSeries.subst_X hsub] at h
      have eL : MvPowerSeries.coeff μ (f x) = ∑ b', Zf b' * S.tan b' x := by
        simp only [hf, hZ, map_sum, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_C_mul, he,
          Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun j _ => ?_
        ring
      have eR : ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, S.al c s x *
          MvPowerSeries.coeff μ (MvPowerSeries.subst f (t c) ^ V.l ^ s) =
          ∑ b', Y b' * S.tan b' x := by
        calc _ = ∑ s ∈ Finset.range (μ.degree + 1), ∑ b', ∑ c,
              al c s b' * P c s * S.tan b' x := by
              refine Finset.sum_congr rfl fun s _ => ?_
              simp only [hP, hal', Finset.sum_mul]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b' _ => Finset.sum_congr rfl fun c _ => ?_
              ring
          _ = ∑ b', ∑ s ∈ Finset.range (μ.degree + 1), ∑ c, al c s b' * P c s * S.tan b' x :=
              Finset.sum_comm
          _ = _ := by simp only [hY, Finset.sum_mul]
      rw [eL, eR] at h
      simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
    have hv : Matrix.vecMul (fun b' => Y b' - Zf b') (Matrix.of S.tan) = 0 := by
      funext x
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hx x
    have h0 := congrFun (Matrix.eq_zero_of_vecMul_eq_zero S.U_det_ne hv) b
    exact sub_eq_zero.mp h0
  · have hF : ∀ μ' : I →₀ ℕ, MvPowerSeries.coeff μ' (S.ze t κ) =
        ∑ s ∈ Finset.range (μ'.degree + 1), ∑ c, (-S.be c s κ) *
          MvPowerSeries.coeff μ' (t c ^ V.l ^ s) := by
      intro μ'
      show -(∑ s ∈ Finset.Icc 1 μ'.degree, ∑ c : I,
        S.be c s κ * MvPowerSeries.coeff μ' (t c ^ V.l ^ s)) = _
      simp only [neg_mul, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_subset
      · intro s hs
        simp only [Finset.mem_Icc, Finset.mem_range] at hs ⊢
        omega
      · intro s hs hns
        have hs0 : s = 0 := by
          simp only [Finset.mem_Icc, Finset.mem_range] at hs hns
          omega
        subst hs0
        simp [show ∀ c, S.be c 0 κ = 0 from fun c => S.be_zero c κ]
    rw [GlobalTheory.T.coeff_subst_sum_l_pow_pow_mvPowerSeries C I ι I V.l hl (fun c s => -S.be c s κ) t (S.ze t κ) f hf0 ht.1 hF μ]
    simp only [neg_mul, Finset.sum_neg_distrib]
end GlobalTheory.MainTerm
