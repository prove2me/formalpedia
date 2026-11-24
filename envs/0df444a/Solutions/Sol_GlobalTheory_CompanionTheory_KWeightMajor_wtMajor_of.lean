-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KWeightMajor.wtMajor_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:56:06.024997+00:00
-- url     : https://prove2.me/submissions/35dc37f1-9624-4c43-85c3-2b008318f49f

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_EigenspaceCyclicDensity_LowKMultOneP
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactCasimirHighestWeight
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IsCompactInvariantCompactSpan
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_HighestWeights_PRVComponents_HighestWeightDifferencesNat
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InnerEqZeroOfWeight
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsPowEqZero
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_norm_identity
import Theorems.Thm_GlobalTheory_CompanionTheory_KWeightMajor_perm_weight
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_cons
import Theorems.Thm_CompanionTheory_D_gk_HwAlg_word_nil
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_map_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_REAL_highestWeightExists_holds
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_inner_eq_zero_of_weight
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kcomm_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_KLowSpan_kstab_orthogonal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HW_lie_relation_raise_lower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_cons
attribute [local simp] CompanionTheory.D.gk.HwAlg.word_nil


section
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
namespace GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
private lemma casK_mul_comm_of_eq_sign {A : Type} [Ring A] {F : Fin n → Fin n → A} (hF : KRel ε F) {c d : Fin n}
    (hcd : ε c = ε d) : CasK ε F * F c d = F c d * CasK ε F := by
  rw [← sub_eq_zero]
  have key : ∀ a b : Fin n, (if ε a = ε b then F a b * F b a else 0) * F c d -
      F c d * (if ε a = ε b then F a b * F b a else 0) =
      (if ε a = ε b ∧ a = c then F a b * F b d else 0) - (if ε a = ε b ∧ d = b then F a b * F c a else 0) +
      ((if ε a = ε b ∧ b = c then F a d * F b a else 0) - (if ε a = ε b ∧ d = a then F c b * F b a else 0)) := by
    intro a b
    by_cases hab : ε a = ε b
    · have h1 := hF b a c d hab.symm hcd
      have h2 := hF a b c d hab hcd
      have h3 : F a b * F b a * F c d - F c d * (F a b * F b a) =
          F a b * (F b a * F c d - F c d * F b a) + (F a b * F c d - F c d * F a b) * F b a := by
        noncomm_ring
      rw [if_pos hab, h3, h1, h2]
      simp only [hab, true_and, mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
    · simp [hab]
  unfold CasK
  simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [key, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ a, ∑ b, (if ε a = ε b ∧ a = c then F a b * F b d else 0) =
      ∑ b, (if ε c = ε b then F c b * F b d else 0) := by
    rw [Fintype.sum_eq_single c]
    · simp
    · intro a ha; simp [ha]
  have e4 : ∑ a, ∑ b, (if ε a = ε b ∧ d = a then F c b * F b a else 0) =
      ∑ b, (if ε c = ε b then F c b * F b d else 0) := by
    rw [Fintype.sum_eq_single d]
    · simp [hcd]
    · intro a ha; simp [Ne.symm ha]
  have e2 : ∑ a, ∑ b, (if ε a = ε b ∧ d = b then F a b * F c a else 0) =
      ∑ a, (if ε a = ε c then F a d * F c a else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single d]
    · simp [hcd]
    · intro b hb; simp [Ne.symm hb]
  have e3 : ∑ a, ∑ b, (if ε a = ε b ∧ b = c then F a d * F b a else 0) =
      ∑ a, (if ε a = ε c then F a d * F c a else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_eq_single c]
    · simp
    · intro b hb; simp [hb]
  rw [e1, e2, e3, e4]
  abel
private lemma casK_apply_eq_of_kHighest (hF : KRel ε E) {ν : Fin n → ℝ} {y : V} (hy : KHighest ε E ν y) :
    CasK ε E y = ((PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) : ℝ) : ℂ) • y := by
  classical
  have hterm : ∀ a b : Fin n, (if ε a = ε b then E a b * E b a else 0) y =
      (((if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ)) : ℂ) • y := by
    intro a b
    by_cases hab : ε a = ε b
    · simp only [if_pos hab, Module.End.mul_apply]
      rcases lt_trichotomy a b with hlt | heq | hgt
      · rw [if_neg hlt.ne, if_pos hlt, ReciprocityTheory.ChartRestriction.DS.HW.lie_relation_raise_lower hF hab, hy.2 a b hlt hab, map_zero,
          zero_add, hy.1 a, hy.1 b, ← sub_smul, Complex.ofReal_sub]
      · subst heq
        rw [if_pos rfl, hy.1 a, map_smul, hy.1 a, smul_smul, Complex.ofReal_pow, sq]
      · rw [if_neg hgt.ne', if_neg (not_lt.mpr hgt.le), hy.2 b a hgt hab.symm, map_zero]
        simp
    · simp [hab]
  have hsum : ∑ a, ∑ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) =
      PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) := by
    have h2ρ : ∀ a, 2 * PI.UpqRep.rhoC ε a =
        ∑ b, (if a < b ∧ ε b = ε a then (1 : ℝ) else 0) - ∑ b, (if b < a ∧ ε b = ε a then (1 : ℝ) else 0) := by
      intro a
      simp only [PI.UpqRep.rhoC, Finset.sum_boole]
      ring
    have hR : PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) =
        ∑ a, ν a ^ 2 + (∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν a else 0) -
          ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν b else 0)) := by
      have e1 : PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε) =
          ∑ a, (ν a ^ 2 + ν a * (2 * PI.UpqRep.rhoC ε a)) := by
        simp only [PI.UpqRep.nsq, PI.UpqRep.dot, Pi.add_apply, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun a _ => by ring
      have e2 : ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν a else 0) =
          ∑ a, ν a * ∑ b, (if a < b ∧ ε b = ε a then (1 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        by_cases h : ε a = ε b
        · simp [h]
        · simp [h, Ne.symm h]
      have e3 : ∑ a, ∑ b, (if a < b ∧ ε a = ε b then ν b else 0) =
          ∑ a, ν a * ∑ b, (if b < a ∧ ε b = ε a then (1 : ℝ) else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        simp
      rw [e1, e2, e3]
      simp only [h2ρ, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [hR]
    have hL : ∀ a, ∑ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) =
        ν a ^ 2 + (∑ b, (if a < b ∧ ε a = ε b then ν a else 0) - ∑ b, (if a < b ∧ ε a = ε b then ν b else 0)) := by
      intro a
      rw [← Finset.sum_sub_distrib]
      have hb : ∀ b, (if ε a = ε b then (if a = b then ν a ^ 2 else if a < b then ν a - ν b else 0) else 0 : ℝ) =
          (if b = a then ν a ^ 2 else 0) +
            ((if a < b ∧ ε a = ε b then ν a else 0) - (if a < b ∧ ε a = ε b then ν b else 0)) := by
        intro b
        by_cases hba : b = a
        · subst hba; simp
        · by_cases h : ε a = ε b
          · by_cases hlt : a < b
            · simp [h, hlt, Ne.symm hba, hba]
            · simp [h, hlt, Ne.symm hba, hba]
          · simp [h, hba]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp
    rw [Finset.sum_congr rfl fun a _ => hL a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  unfold CasK
  rw [← hsum]
  simp only [LinearMap.sum_apply, hterm, Complex.ofReal_sum, Finset.sum_smul]
end GlobalTheory.CompanionTheory.KWeightMajor
end
end

set_option autoImplicit false
open scoped InnerProductSpace
open Formalism.REAL (KHighest IsWeight CasK kSpan)
open CompanionTheory.D.DSIC (KRel KUnit KStab)
open GlobalTheory.CompanionTheory.KLowSpan (kcomm_apply inner_eq_zero_of_weight kstab_orthogonal)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KWeightMajor
variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}
namespace GlobalTheory.CompanionTheory.KWeightMajor
theorem _root_.solution (hlow : CompanionTheory.D.DSIC.LowSpan) : CompanionTheory.D.LK.WtMajor := by
  unfold CompanionTheory.D.LK.WtMajor
  intro n ε V _ _ E hF hU hLF μ s x hx0 hxw hcas
  classical
  obtain ⟨S, hSfd, hSst, hxS⟩ := hLF x
  have main : ∀ (N : ℕ) (T : Submodule ℂ V), Module.finrank ℂ T = N → FiniteDimensional ℂ T →
      KStab ε E T → (∀ v ∈ T, CasK ε E v = s • v) → x ∈ T →
      ∃ ν y, y ≠ 0 ∧ KHighest ε E ν y ∧
        s = ↑(PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε)) ∧
        (∀ c d : Fin n, c < d → ε c = ε d → ν d ≤ ν c) ∧
        ∀ w : Equiv.Perm (Fin n), (∀ c, ε (w c) = ε c) → PI.UpqRep.CDom ε (μ ∘ w) ν := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
    intro T hN hTfd hTst hTcas hxT
    haveI : FiniteDimensional ℂ T := hTfd
    have hTne : T ≠ ⊥ := by
      intro h
      rw [h] at hxT
      exact hx0 ((Submodule.mem_bot ℂ).mp hxT)
    obtain ⟨y, hyT, hy0, ν, hyH⟩ := Formalism.REAL.highestWeightExists_holds V n ε E T hTfd hF hU hTst hTne
    obtain ⟨L, hLT, hyL, hLst, -, hLdom, -⟩ := hlow n ε V E ν y T hF hU hy0 hyH hTfd hTst hyT
    haveI : FiniteDimensional ℂ L := Submodule.finiteDimensional_of_le hLT
    obtain ⟨xL, hxL, xp, hxp, hxsplit⟩ := Submodule.exists_add_mem_mem_orthogonal (K := L) x
    have hLpst := kstab_orthogonal hU hLst
    have hsplit : ∀ (A : Module.End ℂ V) (c : ℂ), (∀ v ∈ L, A v ∈ L) → (∀ v ∈ Lᗮ, A v ∈ Lᗮ) →
        A x = c • x → A xL = c • xL := by
      intro A c hAL hAp hAx
      have h1 : A xL - c • xL ∈ L := L.sub_mem (hAL _ hxL) (L.smul_mem _ hxL)
      have h0 : A xL + A xp = c • xL + c • xp := by
        rw [← map_add, ← smul_add, ← hxsplit, hAx]
      have h2 : A xL - c • xL = -(A xp - c • xp) := by
        rw [neg_sub, sub_eq_sub_iff_add_eq_add, add_comm (c • xp)]
        exact h0
      have h3 : A xL - c • xL ∈ Lᗮ := by
        rw [h2]
        exact Lᗮ.neg_mem (Lᗮ.sub_mem (hAp _ hxp) (Lᗮ.smul_mem _ hxp))
      exact sub_eq_zero.mp (inner_self_eq_zero.mp (Submodule.inner_right_of_mem_orthogonal h1 h3))
    by_cases hxL0 : xL = 0
    · have hxp' : x ∈ Lᗮ := by rw [hxsplit, hxL0, zero_add]; exact hxp
      have hlt : T ⊓ Lᗮ < T := by
        refine lt_of_le_of_ne inf_le_left fun h => hy0 ?_
        have hy' : y ∈ T ⊓ Lᗮ := by rw [h]; exact hyT
        exact inner_self_eq_zero.mp
          (Submodule.inner_right_of_mem_orthogonal hyL (Submodule.mem_inf.mp hy').2)
      have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
      refine ih _ (hN ▸ hlt') (T ⊓ Lᗮ) rfl (Submodule.finiteDimensional_of_le inf_le_left) ?_ ?_
        (Submodule.mem_inf.mpr ⟨hxT, hxp'⟩)
      · intro a b hab v hv
        exact Submodule.mem_inf.mpr ⟨hTst a b hab v (Submodule.mem_inf.mp hv).1,
          hLpst a b hab v (Submodule.mem_inf.mp hv).2⟩
      · intro v hv
        exact hTcas v (Submodule.mem_inf.mp hv).1
    · have hxLw : IsWeight E μ xL := fun a =>
        hsplit (E a a) (μ a) (fun v hv => hLst a a rfl v hv) (fun v hv => hLpst a a rfl v hv) (hxw a)
      have hform := casK_apply_eq_of_kHighest hF hyH
      rw [hTcas y hyT] at hform
      have hs : s = ↑(PI.UpqRep.nsq (ν + PI.UpqRep.rhoC ε) - PI.UpqRep.nsq (PI.UpqRep.rhoC ε)) :=
        smul_left_injective ℂ hy0 hform
      refine ⟨ν, y, hy0, hyH, hs, ?_, ?_⟩
      · intro c d hcd he
        have hid := norm_identity hF hU he hyH.1
        rw [hyH.2 c d hcd he, norm_zero] at hid
        have hy2 : 0 < ‖y‖ ^ 2 := pow_pos (norm_pos_iff.mpr hy0) 2
        nlinarith [sq_nonneg ‖E d c y‖]
      · intro w hεw
        obtain ⟨z', hz'L, hz'0, hz'⟩ := perm_weight hF hU hLst _ w rfl hεw hxL hxL0 hxLw
        exact hLdom _ z' hz'L hz'0 hz'
  let T0 : Submodule ℂ V := S ⊓ LinearMap.ker (CasK ε E - s • (1 : Module.End ℂ V))
  have hT0cas : ∀ v ∈ T0, CasK ε E v = s • v := by
    intro v hv
    have h := (Submodule.mem_inf.mp hv).2
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
    exact h
  have hT0st : KStab ε E T0 := by
    intro a b hab v hv
    refine Submodule.mem_inf.mpr ⟨hSst a b hab v (Submodule.mem_inf.mp hv).1, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    have hc := congrArg (fun T : Module.End ℂ V => T v) (casK_mul_comm_of_eq_sign hF hab)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hT0cas v hv, map_smul]
  have hxT0 : x ∈ T0 := by
    refine Submodule.mem_inf.mpr ⟨hxS, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    exact hcas
  exact main _ T0 rfl (Submodule.finiteDimensional_of_le inf_le_left) hT0st hT0cas hxT0
end GlobalTheory.CompanionTheory.KWeightMajor
