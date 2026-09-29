-- Prove2me | solution 1 for HeckeEis.isParabolicCocycle_cocycle_of_isEichlerIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/7b4cd390-34f4-528d-a193-f8320f464bae

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_ModularGroup_exists_eq_conj_T_zpow_of_trace_sq_eq_four
import Theorems.Thm_HeckeEis_IsEichlerIntegral_vadd_sub_T_zpow_apply_mem_range
import Theorems.Thm_HeckeEis_binaryFormRepSL_neg_one_apply
import Theorems.Thm_HeckeEis_IsEichlerIntegral_slash
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral

set_option autoImplicit false

open scoped Manifold MatrixGroups

noncomputable section

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binaryFormRepSL IsParabolicCocycle IsEquivariantPrimitiveWith IsEichlerIntegral binaryFormRepSL_neg_one_apply"
namespace ParabolicSol
p2m_open "HeckeEis"

p2m_open "UpperHalfPlane MvPolynomial CongruenceSubgroup HeckeEis P2MW.S_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral.HeckeEis"
open scoped Manifold MatrixGroups ModularForm Pointwise

theorem periodic_slash_comp_ofComplex_of_conj_T_zpow_mem {k : ℤ} {Γ : Subgroup SL(2, ℤ)} {F' : Type*}
    [FunLike F' ℍ ℂ] [SlashInvariantFormClass F' (Γ : Subgroup (GL (Fin 2) ℝ)) k] (f : F') (δ : SL(2, ℤ)) {h : ℤ}
    (hmem : δ * ModularGroup.T ^ h * δ⁻¹ ∈ Γ) :
    Function.Periodic (((f : ℍ → ℂ) ∣[k] δ) ∘ ofComplex) ((h : ℝ) : ℂ) := by
  refine SlashInvariantFormClass.periodic_comp_ofComplex
    (SlashInvariantForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ δ)) ?_
  rw [Subgroup.mem_strictPeriods_iff, map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  have hTh : Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.T ^ h)
      = Matrix.GeneralLinearGroup.upperRightHom (h : ℝ) := by
    rw [Units.ext_iff, Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe,
      ModularGroup.coe_T_zpow, Matrix.GeneralLinearGroup.upperRightHom_apply]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [← hTh, ← map_mul, ← map_inv, ← map_mul]
  exact Subgroup.mem_map_of_mem _ hmem

theorem Gamma_le_Gamma0 (N : ℕ) : Gamma N ≤ Gamma0 N := fun _ hA =>
  Gamma0_mem.mpr (Gamma_mem.mp hA).2.2.1

end HeckeEis.ParabolicSol

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral.HeckeEis HeckeEis.ParabolicSol UpperHalfPlane CongruenceSubgroup in
open scoped ModularForm Pointwise in
theorem solution (N n : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2)) {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hEI : HeckeEis.IsEichlerIntegral n f F)
    (hF : HeckeEis.IsEquivariantPrimitiveWith
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F) :
    HeckeEis.IsParabolicCocycle
      ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) hF.cocycle := by
  haveI : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_Gamma0 N)
  set ρ := (binaryFormRepSL ℂ n).comp (Gamma0 N).subtype with hρ
  set R := binaryFormRepSL ℂ n with hR
  have hρapp : ∀ γ : Gamma0 N, ρ γ = R (γ : SL(2, ℤ)) := fun γ => rfl
  have hneg1 : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have hRinv : ∀ (x : SL(2, ℤ)) (v : ↥(BinaryForm ℂ n)), R x⁻¹ (R x v) = v := fun x v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hRinv' : ∀ (x : SL(2, ℤ)) (v : ↥(BinaryForm ℂ n)), R x (R x⁻¹ v) = v := fun x v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  intro γ hγ
  rcases Nat.even_or_odd n with heven | hodd
  ·
    obtain ⟨ε, δ, h, hε, hγeq⟩ := ModularGroup.exists_eq_conj_T_zpow_of_trace_sq_eq_four (γ : SL(2, ℤ)) hγ
    have hRε : R ε = 1 := by
      rcases hε with rfl | rfl
      · exact map_one R
      · refine LinearMap.ext fun P => ?_
        rw [hR, binaryFormRepSL_neg_one_apply, Even.neg_one_pow heven, one_smul, Module.End.one_apply]
    have hRεx : ∀ x : SL(2, ℤ), R (ε * x) = R x := fun x => by rw [map_mul, hRε, one_mul]
    have hεsmul : ∀ (x : SL(2, ℤ)) (τ : ℍ), (ε * x) • τ = x • τ := by
      rcases hε with rfl | rfl
      · intro x τ; rw [one_mul]
      · intro x τ; rw [neg_one_mul]; exact ModularGroup.SL_neg_smul x τ
    have hσ : δ * ModularGroup.T ^ h * δ⁻¹ ∈ Gamma0 N := by
      rcases hε with rfl | rfl
      · rw [one_mul] at hγeq; rw [← hγeq]; exact γ.2
      · have e : δ * ModularGroup.T ^ h * δ⁻¹ = -1 * (γ : SL(2, ℤ)) := by rw [hγeq, ← mul_assoc, neg_one_mul, neg_neg, one_mul]
        rw [e]; exact Subgroup.mul_mem _ hneg1 γ.2

    set g : ℍ → ℂ := (f : ℍ → ℂ) ∣[((n : ℤ) + 2)] δ with hg
    set G : ℍ → ↥(BinaryForm ℂ n) := fun τ => R δ⁻¹ (F (δ • τ)) with hGdef
    have hGEI : IsEichlerIntegral n g G := hEI.slash δ
    have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := (CuspFormClass.holo f).slash _ _
    have hgzero : IsZeroAtImInfty g := CuspFormClass.zero_at_infty_slash f δ
    have hgper : Function.Periodic (g ∘ ofComplex) ((h : ℝ) : ℂ) :=
      periodic_slash_comp_ofComplex_of_conj_T_zpow_mem f δ hσ
    have hFG : ∀ u : ℍ, F (δ • u) = R δ (G u) := fun u => by rw [hGdef, hRinv']

    have hcoc : hF.cocycle γ = R δ (G (ModularGroup.T ^ h • I) - R (ModularGroup.T ^ h) (G I)) := by
      rw [← hF.sub_eq_cocycle γ (δ • I), hρapp, hγeq, hεsmul, hRεx, ← mul_smul, inv_mul_cancel_right, mul_smul,
        hFG, hFG, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hRinv, map_sub]

    have htrans : ∀ y ∈ LinearMap.range (R (ModularGroup.T ^ h) - 1), R δ y ∈ LinearMap.range (ρ γ - 1) := by
      rintro _ ⟨w, rfl⟩
      refine ⟨R δ w, ?_⟩
      rw [LinearMap.sub_apply, Module.End.one_apply, hρapp, hγeq, hRεx, map_mul, map_mul, Module.End.mul_apply,
        Module.End.mul_apply, hRinv, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [hcoc]
    apply htrans
    rcases eq_or_ne h 0 with rfl | hh
    · simp
    · rw [UpperHalfPlane.modular_T_zpow_smul]
      exact hGEI.vadd_sub_T_zpow_apply_mem_range hh hgper hghol hgzero I
  ·
    set m : Gamma0 N := ⟨-1, hneg1⟩ with hm
    have hρm : ∀ v, ρ m v = -v := fun v => by
      rw [hρapp]
      show binaryFormRepSL ℂ n (-1) v = -v
      rw [binaryFormRepSL_neg_one_apply, Odd.neg_one_pow hodd]
      exact neg_one_smul ℂ v
    have hz := hF.cocycle_mem_coeffCocycles
    have hcomm : γ * m = m * γ := Subtype.ext (by simp [hm])
    have h1 := hz γ m
    have h2 := hz m γ
    rw [hcomm, h2, hρm] at h1

    have h4 : hF.cocycle γ + hF.cocycle γ = hF.cocycle m - ρ γ (hF.cocycle m) := by
      rw [eq_sub_iff_add_eq]
      calc hF.cocycle γ + hF.cocycle γ + ρ γ (hF.cocycle m)
          = hF.cocycle γ + (hF.cocycle γ + ρ γ (hF.cocycle m)) := by abel
        _ = hF.cocycle γ + (hF.cocycle m + -hF.cocycle γ) := by rw [h1]
        _ = hF.cocycle m := by abel
    refine ⟨-((2 : ℂ)⁻¹ • hF.cocycle m), ?_⟩
    rw [LinearMap.sub_apply, Module.End.one_apply, map_neg, map_smul, sub_neg_eq_add]
    calc -((2 : ℂ)⁻¹ • ρ γ (hF.cocycle m)) + (2 : ℂ)⁻¹ • hF.cocycle m
        = (2 : ℂ)⁻¹ • (hF.cocycle m - ρ γ (hF.cocycle m)) := by rw [smul_sub]; abel
      _ = (2 : ℂ)⁻¹ • (hF.cocycle γ + hF.cocycle γ) := by rw [h4]
      _ = hF.cocycle γ := by rw [← two_smul ℂ, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]

end

end S_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral
end P2MW
export P2MW.S_HeckeEis_isParabolicCocycle_cocycle_of_isEichlerIntegral (solution)
