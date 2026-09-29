-- Prove2me | solution 1 for HeckeEis.eichlerShimuraMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5089a8cd-b936-511e-b0bb-1db690e83a66

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_HeckeEis_IsEichlerIntegral_hasDerivAt_eval_iterate_pderiv
import Theorems.Thm_HeckeEis_IsEichlerIntegral_isBoundedAtImInfty_eval
import Theorems.Thm_HeckeEis_IsEichlerIntegral_eq_zero_of_eval_eq_const
import Theorems.Thm_HeckeEis_jFactor_pow_mul_eval_binaryFormRepSL
import Theorems.Thm_HeckeEis_exists_isEichlerIntegral_isParabolicCocycle
import Theorems.Thm_HeckeEis_eichlerShimuraMap_eq_coeffH1parMk
import Theorems.Thm_HeckeEis_IsEichlerIntegral_slash
import Theorems.Thm_HeckeEis_existsEichlerShimuraMapLinear
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_eichlerShimuraMap_injective

set_option autoImplicit false

namespace HeckeEis
p2m_export "HeckeEis" "BinaryForm binaryFormRepSL mem_coeffCoboundaries_iff coeffH1parMk_eq_zero_iff jFactor_eq_denom IsEichlerIntegral eichlerShimuraMap jFactor_pow_mul_eval_binaryFormRepSL exists_isEichlerIntegral_isParabolicCocycle eichlerShimuraMap_eq_coeffH1parMk existsEichlerShimuraMapLinear"
namespace MainAux
p2m_open "HeckeEis"

open UpperHalfPlane MvPolynomial CongruenceSubgroup Filter Function
open scoped MatrixGroups Manifold Topology ModularForm Pointwise

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

theorem conj_T_zpow_mem_Gamma0 (N : ℕ) (δ : SL(2, ℤ)) :
    δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := by
  have hTN : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
    have := CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma (N : ℤ) (N : ℤ) dvd_rfl
    simpa using this
  exact Gamma_le_Gamma0 N ((CongruenceSubgroup.Gamma_normal N).conj_mem _ hTN δ)

theorem mdifferentiable_eval {n : ℕ} {g : ℍ → ℂ} {G : ℍ → ↥(BinaryForm ℂ n)} (hG : IsEichlerIntegral n g G) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
      (fun τ : ℍ => MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((G τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) := by
  rw [UpperHalfPlane.mdifferentiable_iff]
  intro z hz
  have h := (hG.hasDerivAt_eval_iterate_pderiv (Nat.zero_le n) ⟨z, hz⟩).differentiableAt
  simp only [Function.iterate_zero, id_eq] at h
  refine (h.congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hz] with w hw
  simp only [Function.comp_apply]
  rw [ofComplex_apply_of_im_pos hw]

theorem exists_eq_const_of_slash_invariant {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} (hk : k ≤ 0)
    {F : ℍ → ℂ} (hinv : ∀ γ ∈ Γ, F ∣[k] γ = F) (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F)
    (hbdd : ∀ δ : SL(2, ℤ), IsBoundedAtImInfty (F ∣[k] δ)) : ∃ c : ℂ, ∀ τ : ℍ, F τ = c := by
  let M : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k :=
    { toFun := F
      slash_action_eq' := by
        intro g hg
        obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hg
        exact hinv γ hγ
      holo' := hhol
      bdd_at_cusps' := by
        intro c hc
        have hle : (Γ : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ := by
          rintro g ⟨γ, -, rfl⟩
          exact ⟨γ, rfl⟩
        obtain ⟨δ, rfl⟩ := isCusp_SL2Z_iff'.mp (hc.mono hle)
        rw [OnePoint.isBoundedAt_iff (g := Matrix.SpecialLinearGroup.mapGL ℝ δ) rfl]
        exact hbdd δ }
  have hMF : ∀ τ : ℍ, M τ = F τ := fun τ => rfl
  rcases hk.lt_or_eq with hlt | heq
  · refine ⟨0, fun τ => ?_⟩
    have hM : M = 0 := ModularForm.isZero_of_neg_weight hlt M
    rw [← hMF τ, hM]
    rfl
  · subst heq
    obtain ⟨c, hc⟩ := ModularForm.eq_const_of_weight_zero M
    exact ⟨c, fun τ => by rw [← hMF τ, hc]; rfl⟩

end HeckeEis.MainAux

open _root_.HeckeEis _root_.P2MW.S_HeckeEis_eichlerShimuraMap_injective.HeckeEis HeckeEis.MainAux UpperHalfPlane CongruenceSubgroup MvPolynomial in
open scoped ModularForm Pointwise Manifold MatrixGroups in
theorem solution (N : ℕ) [NeZero N] (n : ℕ) :
    Function.Injective
      (fun f : CuspForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2) ↦ HeckeEis.eichlerShimuraMap n N f) := by
  haveI : (Gamma0 N).FiniteIndex := Subgroup.finiteIndex_of_le (Gamma_le_Gamma0 N)

  obtain ⟨ES, hES⟩ := existsEichlerShimuraMapLinear n N
  suffices hker : ∀ f : CuspForm (Gamma0 N) ((n : ℤ) + 2), eichlerShimuraMap n N f = 0 → f = 0 by
    intro f g hfg
    have h1 : ES (f - g) = 0 := by
      rw [map_sub, hES, hES, sub_eq_zero]
      exact hfg
    rw [hES] at h1
    exact sub_eq_zero.mp (hker _ h1)
  intro f hf0
  set R := binaryFormRepSL ℂ n with hR
  obtain ⟨F, hEI, hF, hpar⟩ := exists_isEichlerIntegral_isParabolicCocycle N n f
  rw [eichlerShimuraMap_eq_coeffH1parMk n N f hEI hF hpar, coeffH1parMk_eq_zero_iff] at hf0
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hf0

  set F₁ : ℍ → ↥(BinaryForm ℂ n) := fun τ => F τ + v with hF₁
  have hEI₁ : IsEichlerIntegral n f F₁ := by
    intro d τ
    have := (hEI d τ).add_const (coeff d ((v : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
    simpa [hF₁, Submodule.coe_add, coeff_add] using this
  have hEq : ∀ γ ∈ Gamma0 N, ∀ τ : ℍ, F₁ (γ • τ) = R γ (F₁ τ) := by
    intro γ hγ τ
    have h1 := hF.sub_eq_cocycle ⟨γ, hγ⟩ τ
    have h2 := congrFun hv ⟨γ, hγ⟩
    simp only at h2
    rw [← h2] at h1

    simp only [hF₁, map_add]
    change F (γ • τ) + v = R γ (F τ) + R γ v
    have h3 : F (γ • τ) - R γ (F τ) = R γ v - v := h1
    rw [sub_eq_iff_eq_add.mp h3]
    abel

  set P : ℍ → ℂ := fun τ => MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((F₁ τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
    with hP
  set Gδ : SL(2, ℤ) → ℍ → ↥(BinaryForm ℂ n) := fun δ τ => R δ⁻¹ (F₁ (δ • τ)) with hGδ
  have hGδEI : ∀ δ : SL(2, ℤ), IsEichlerIntegral n (⇑f ∣[((n : ℤ) + 2)] δ) (Gδ δ) := fun δ => hEI₁.slash δ
  have hRR : ∀ (δ : SL(2, ℤ)) (τ : ℍ), R δ (Gδ δ τ) = F₁ (δ • τ) := fun δ τ => by
    simp only [hGδ]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hslash : ∀ (δ : SL(2, ℤ)) (τ : ℍ), (P ∣[-(n : ℤ)] δ) τ
      = MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((Gδ δ τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) := by
    intro δ τ
    rw [ModularForm.SL_slash_apply, hP, neg_neg]
    simp only []
    have key := HeckeEis.jFactor_pow_mul_eval_binaryFormRepSL n δ τ (Gδ δ τ)
    rw [hRR, jFactor_eq_denom] at key
    rw [← key, mul_comm, zpow_natCast]
    rfl

  have hinv : ∀ γ ∈ Gamma0 N, P ∣[-(n : ℤ)] γ = P := by
    intro γ hγ
    funext τ
    rw [hslash γ τ, hP]
    simp only [hGδ]
    rw [hEq γ hγ τ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) P := mdifferentiable_eval hEI₁
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hbdd : ∀ δ : SL(2, ℤ), IsBoundedAtImInfty (P ∣[-(n : ℤ)] δ) := by
    intro δ
    have hfun : P ∣[-(n : ℤ)] δ
        = fun τ : ℍ => MvPolynomial.eval ![(1 : ℂ), -(τ : ℂ)] ((Gδ δ τ : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ) :=
      funext (hslash δ)
    rw [hfun]
    have hσ : δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ ∈ Gamma0 N := conj_T_zpow_mem_Gamma0 N δ
    have hgper : Function.Periodic ((⇑f ∣[((n : ℤ) + 2)] δ) ∘ ofComplex) (((N : ℤ) : ℝ) : ℂ) :=
      periodic_slash_comp_ofComplex_of_conj_T_zpow_mem f δ hσ
    have hghol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (⇑f ∣[((n : ℤ) + 2)] δ) := (CuspFormClass.holo f).slash _ _
    have hgbdd : IsBoundedAtImInfty (⇑f ∣[((n : ℤ) + 2)] δ) := ModularFormClass.bdd_at_infty_slash f δ
    have hT : ∀ τ : ℍ, Gδ δ ((((N : ℤ) : ℝ)) +ᵥ τ) = R (ModularGroup.T ^ (N : ℤ)) (Gδ δ τ) := by
      intro τ
      simp only [hGδ]
      have h1 := hEq _ hσ (δ • τ)
      have hpt : ((δ * ModularGroup.T ^ (N : ℤ) * δ⁻¹ : SL(2, ℤ)) • δ • τ) = δ • ((((N : ℤ) : ℝ)) +ᵥ τ) := by
        rw [← UpperHalfPlane.modular_T_zpow_smul, smul_smul, smul_smul]
        congr 1
        group
      rw [hpt] at h1
      rw [h1, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    exact (hGδEI δ).isBoundedAtImInfty_eval hNpos hgper hghol hgbdd hT
  obtain ⟨c, hc⟩ := exists_eq_const_of_slash_invariant (Γ := Gamma0 N) (k := -(n : ℤ)) (by omega) hinv hhol hbdd
  have hzero : (⇑f : ℍ → ℂ) = 0 := hEI₁.eq_zero_of_eval_eq_const hc
  exact DFunLike.ext f 0 fun τ => by rw [congrFun hzero τ]; rfl

#print axioms solution

end S_HeckeEis_eichlerShimuraMap_injective
end P2MW
export P2MW.S_HeckeEis_eichlerShimuraMap_injective (solution)
