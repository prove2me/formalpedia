-- Prove2me | solution 1 for HeckeEis.exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/22581354-1bce-5827-b226-fd6435ac940e

import Mathlib
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Definitions.Def_HeckeEis_EichlerIntegral
import Theorems.Thm_HeckeEis_exists_isEichlerIntegral
import Theorems.Thm_HeckeEis_isEquivariantPrimitiveWith_of_isEichlerIntegral
import Theorems.Thm_HeckeEis_coeff_single_one_eq_eval_of_mem_binaryForm
import Theorems.Thm_HeckeEis_mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero
import Theorems.Thm_HeckeEis_IsEichlerIntegral_coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash
import Theorems.Thm_CongruenceSubgroup_finsum_addMonoidHom_conj_T_zpow_eq_zero
import Theorems.Thm_ModularForm_exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le
import Theorems.Thm_ModularForm_exists_gamma0_weight_two_forall_tendsto_slash_atImInfty
import Theorems.Thm_UpperHalfPlane_intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles

set_option autoImplicit false

namespace A2BES

open UpperHalfPlane MvPolynomial CongruenceSubgroup HeckeEis Filter
open scoped MatrixGroups ModularForm Manifold Topology

section Prelim

variable (n : ℕ)

abbrev V : Type := ↥(BinaryForm ℂ n)

noncomputable abbrev R : SL(2, ℤ) →* (V n →ₗ[ℂ] V n) := binaryFormRepSL ℂ n

theorem eval_binarySubst (M : Matrix (Fin 2) (Fin 2) ℤ) (x : Fin 2 → ℂ) (P : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval x (binarySubst ℂ M P)
      = MvPolynomial.eval (fun j => ∑ i : Fin 2, x i * ((M i j : ℤ) : ℂ)) P := by
  unfold binarySubst
  rw [MvPolynomial.aeval_eq_bind₁]
  change MvPolynomial.eval₂Hom (RingHom.id ℂ) x (MvPolynomial.bind₁ _ P) = _
  rw [MvPolynomial.eval₂Hom_bind₁]
  change MvPolynomial.eval (fun i => MvPolynomial.eval x _) P = _
  congr 2
  funext j
  simp [Fin.sum_univ_two, mul_comm]

noncomputable def top (P : V n) : ℂ := MvPolynomial.coeff (Finsupp.single 1 n) (P : MvPolynomial (Fin 2) ℂ)

theorem top_eq_eval (P : V n) : top n P = MvPolynomial.eval ![0, 1] (P : MvPolynomial (Fin 2) ℂ) :=
  coeff_single_one_eq_eval_of_mem_binaryForm P.2

noncomputable def topLin : V n →ₗ[ℂ] ℂ where
  toFun := top n
  map_add' P Q := by simp [top]
  map_smul' c P := by simp [top]

@[scoped simp] theorem topLin_apply (P : V n) : topLin n P = top n P := rfl

theorem top_add (P Q : V n) : top n (P + Q) = top n P + top n Q := (topLin n).map_add P Q
theorem top_sub (P Q : V n) : top n (P - Q) = top n P - top n Q := (topLin n).map_sub P Q
theorem top_smul (c : ℂ) (P : V n) : top n (c • P) = c * top n P := (topLin n).map_smul c P

theorem top_T_zpow (m : ℤ) (P : V n) : top n (R n (ModularGroup.T ^ m) P) = top n P := by
  rw [top_eq_eval, top_eq_eval, binaryFormRepSL_apply_coe, eval_binarySubst, ModularGroup.coe_T_zpow]
  have h : (fun j : Fin 2 => ∑ i : Fin 2, (![0, 1] : Fin 2 → ℂ) i * (((!![1, m; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ))
      = ![0, 1] := by
    funext j
    fin_cases j <;> simp [Fin.sum_univ_two]
  rw [h]

theorem binarySubst_neg_one : binarySubst ℂ (-1 : Matrix (Fin 2) (Fin 2) ℤ) = MvPolynomial.aeval fun j => -X j := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [binarySubst_X, MvPolynomial.aeval_X, Fin.sum_univ_two]
  fin_cases j <;> simp

theorem sum_support_eq_of_isHomogeneous {φ : MvPolynomial (Fin 2) ℂ} {m : ℕ} (hφ : φ.IsHomogeneous m)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ φ.support) : ∑ i ∈ d.support, d i = m := by
  have h := hφ (MvPolynomial.mem_support_iff.mp hd)
  simpa [Finsupp.degree, Finsupp.weight, Finsupp.sum, Finsupp.linearCombination, Finsupp.lsum] using h

theorem aeval_neg_X_of_isHomogeneous {φ : MvPolynomial (Fin 2) ℂ} (hφ : φ.IsHomogeneous n) :
    MvPolynomial.aeval (fun j => -X j) φ = (-1 : ℂ) ^ n • φ := by
  conv_lhs => rw [φ.as_sum]
  conv_rhs => rw [φ.as_sum]
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  have hdeg := sum_support_eq_of_isHomogeneous hφ hd
  have hprod : (d.prod fun i e => (-X i : MvPolynomial (Fin 2) ℂ) ^ e)
      = (-1 : MvPolynomial (Fin 2) ℂ) ^ n * d.prod fun i e => (X i : MvPolynomial (Fin 2) ℂ) ^ e := by
    simp only [Finsupp.prod, neg_pow (X _ : MvPolynomial (Fin 2) ℂ), Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [hdeg]
  rw [hprod, MvPolynomial.algebraMap_eq, MvPolynomial.smul_eq_C_mul, map_pow, map_neg, map_one]
  ring

theorem R_neg_one (P : V n) : R n (-1) P = (-1 : ℂ) ^ n • P := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
    binarySubst_neg_one, Submodule.coe_smul]
  exact aeval_neg_X_of_isHomogeneous n ((mem_homogeneousSubmodule n _).mp P.2)

theorem eq_C_of_mem_zero {P : MvPolynomial (Fin 2) ℂ} (hP : P ∈ BinaryForm ℂ 0) : P = C (MvPolynomial.coeff 0 P) := by
  have hφ : P.IsHomogeneous 0 := (mem_homogeneousSubmodule 0 _).mp hP
  have hsupp : ∀ d ∈ P.support, d = 0 := by
    intro d hd
    have h := sum_support_eq_of_isHomogeneous hφ hd
    ext i
    by_contra hi
    have hi' : i ∈ d.support := Finsupp.mem_support_iff.mpr hi
    have := Finset.sum_eq_zero_iff.mp h i hi'
    exact hi this
  conv_lhs => rw [P.as_sum]
  rcases Finset.eq_empty_or_nonempty P.support with h0 | ⟨d, hd⟩
  · have hP0 : P = 0 := MvPolynomial.support_eq_empty.mp h0
    simp [hP0]
  · have hs : P.support = {0} := by
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨?_, hsupp⟩
      rw [← hsupp d hd]; exact hd
    rw [hs, Finset.sum_singleton]
    rfl

theorem R_zero (g : SL(2, ℤ)) (P : V 0) : R 0 g P = P := by
  apply Subtype.ext
  rw [binaryFormRepSL_apply_coe, eq_C_of_mem_zero P.2, binarySubst_C]

end Prelim

section Group

variable (N : ℕ)

theorem T_zpow_mem_Gamma : ModularGroup.T ^ (N : ℤ) ∈ Gamma N := by
  have h : ((ModularGroup.T ^ (N : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (N : ℤ); 0, 1] :=
    ModularGroup.coe_T_zpow _
  rw [Gamma_mem, h]
  simp

theorem conj_T_zpow_mem_Gamma (σ : SL(2, ℤ)) : σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ ∈ Gamma N :=
  (Gamma_normal N).conj_mem _ (T_zpow_mem_Gamma N) σ

theorem mem_Gamma0_of_mem_Gamma {γ : SL(2, ℤ)} (h : γ ∈ Gamma N) : γ ∈ Gamma0 N := by
  rw [Gamma_mem] at h
  rw [Gamma0_mem]
  exact h.2.2.1

def conjT (σ : SL(2, ℤ)) : Gamma0 N :=
  ⟨σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹, mem_Gamma0_of_mem_Gamma N (conj_T_zpow_mem_Gamma N σ)⟩

@[scoped simp] theorem coe_conjT (σ : SL(2, ℤ)) : ((conjT N σ : Gamma0 N) : SL(2, ℤ)) = σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹ := rfl

theorem conjT_mul_T_zpow (σ : SL(2, ℤ)) (j : ℤ) : conjT N (σ * ModularGroup.T ^ j) = conjT N σ := by
  refine Subtype.ext ?_
  simp only [coe_conjT, mul_inv_rev]
  rw [← zpow_neg]
  group

theorem conjT_mul_left (γ : Gamma0 N) (σ : SL(2, ℤ)) : conjT N ((γ : SL(2, ℤ)) * σ) = γ * conjT N σ * γ⁻¹ := by
  refine Subtype.ext ?_
  simp only [coe_conjT, mul_inv_rev, Subgroup.coe_mul, Subgroup.coe_inv]
  group

def negOne : Gamma0 N := ⟨-1, by rw [Gamma0_mem]; simp⟩

@[scoped simp] theorem coe_negOne : ((negOne N : Gamma0 N) : SL(2, ℤ)) = -1 := rfl

theorem negOne_mul_comm (g : Gamma0 N) : negOne N * g = g * negOne N := by
  refine Subtype.ext ?_
  simp only [Subgroup.coe_mul, coe_negOne]
  rw [neg_one_mul, mul_neg_one]

end Group

section Cocycle

variable {N : ℕ} {n : ℕ}

noncomputable abbrev ρC (N n : ℕ) : Representation ℂ (Gamma0 N) (V n) := (binaryFormRepSL ℂ n).comp (Gamma0 N).subtype

theorem ρC_apply (g : Gamma0 N) : ρC N n g = R n (g : SL(2, ℤ)) := rfl

variable {z : Gamma0 N → V n}

theorem cocycle_one (hz : z ∈ coeffCocycles (ρC N n)) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  exact left_eq_add.mp h |> fun h0 => h0

theorem cocycle_inv (hz : z ∈ coeffCocycles (ρC N n)) (g : Gamma0 N) : z g⁻¹ = -(ρC N n g⁻¹ (z g)) := by
  have h := hz g g⁻¹
  rw [mul_inv_cancel, cocycle_one hz] at h
  have h2 : ρC N n g⁻¹ (ρC N n g (z g⁻¹)) = z g⁻¹ := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← h2, eq_neg_iff_add_eq_zero, ← map_add, add_comm, ← h, map_zero]

theorem cocycle_conj (hz : z ∈ coeffCocycles (ρC N n)) (γ u : Gamma0 N) :
    z (γ * u * γ⁻¹) = z γ + ρC N n γ (z u) - ρC N n (γ * u * γ⁻¹) (z γ) := by
  rw [hz (γ * u) γ⁻¹, hz γ u, cocycle_inv hz γ, map_neg, ← sub_eq_add_neg]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]

end Cocycle

section Odd

variable {N : ℕ} {n : ℕ}

theorem mem_coeffCoboundaries_of_odd (hn : Odd n) {z : Gamma0 N → V n} (hz : z ∈ coeffCocycles (ρC N n)) :
    z ∈ coeffCoboundaries (ρC N n) := by

  have hneg : ∀ P : V n, ρC N n (negOne N) P = -P := by
    intro P
    rw [ρC_apply, coe_negOne, R_neg_one, hn.neg_one_pow, neg_one_smul ℂ P]

  set v : V n := z (negOne N) with hv
  have key : ∀ g : Gamma0 N, ρC N n g ((-(2 : ℂ)⁻¹) • v) - (-(2 : ℂ)⁻¹) • v = z g := by
    intro g
    have h1 := hz (negOne N) g
    have h2 := hz g (negOne N)
    rw [negOne_mul_comm, h2, hneg, ← hv] at h1

    have h3 := eq_sub_of_add_eq' h1
    rw [map_smul, h3]
    module
  rw [mem_coeffCoboundaries_iff]
  exact ⟨(-(2 : ℂ)⁻¹) • v, funext fun g => key g⟩

end Odd

section BV

variable (N : ℕ) (n : ℕ)

noncomputable def bv (z : Gamma0 N → V n) (σ : SL(2, ℤ)) : ℂ := top n (R n σ⁻¹ (z (conjT N σ)))

variable {N n}

theorem bv_sub (z w : Gamma0 N → V n) (σ : SL(2, ℤ)) : bv N n (z - w) σ = bv N n z σ - bv N n w σ := by
  simp [bv, top_sub]

theorem bv_mul_T_zpow (z : Gamma0 N → V n) (σ : SL(2, ℤ)) (j : ℤ) :
    bv N n z (σ * ModularGroup.T ^ j) = bv N n z σ := by
  rw [bv, bv, conjT_mul_T_zpow, mul_inv_rev, map_mul, Module.End.mul_apply, ← zpow_neg, top_T_zpow]

theorem bv_mul_left {z : Gamma0 N → V n} (hz : z ∈ coeffCocycles (ρC N n)) (γ : Gamma0 N) (σ : SL(2, ℤ)) :
    bv N n z ((γ : SL(2, ℤ)) * σ) = bv N n z σ := by
  rw [bv, bv, conjT_mul_left, cocycle_conj hz, mul_inv_rev, map_mul (R n) σ⁻¹]
  set u := conjT N σ with hu

  have h1 : (R n σ⁻¹ * R n ((γ : SL(2, ℤ)))⁻¹) (ρC N n γ (z u)) = R n σ⁻¹ (z u) := by
    rw [Module.End.mul_apply, ρC_apply, ← Module.End.mul_apply (R n (↑γ)⁻¹), ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]

  have hgrp : σ⁻¹ * ((γ : SL(2, ℤ)))⁻¹ * ((γ * u * γ⁻¹ : Gamma0 N) : SL(2, ℤ))
      = ModularGroup.T ^ (N : ℤ) * (σ⁻¹ * ((γ : SL(2, ℤ)))⁻¹) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hu, coe_conjT]
    group
  have eL : (R n σ⁻¹ * R n ((γ : SL(2, ℤ)))⁻¹) (ρC N n (γ * u * γ⁻¹) (z γ))
      = R n (σ⁻¹ * ((γ : SL(2, ℤ)))⁻¹ * ((γ * u * γ⁻¹ : Gamma0 N) : SL(2, ℤ))) (z γ) := by
    simp only [map_mul, Module.End.mul_apply, ρC_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  have eR : R n (ModularGroup.T ^ (N : ℤ)) ((R n σ⁻¹ * R n ((γ : SL(2, ℤ)))⁻¹) (z γ))
      = R n (ModularGroup.T ^ (N : ℤ) * (σ⁻¹ * ((γ : SL(2, ℤ)))⁻¹)) (z γ) := by
    simp only [map_mul, Module.End.mul_apply]
  have h2 : (R n σ⁻¹ * R n ((γ : SL(2, ℤ)))⁻¹) (ρC N n (γ * u * γ⁻¹) (z γ))
      = R n (ModularGroup.T ^ (N : ℤ)) ((R n σ⁻¹ * R n ((γ : SL(2, ℤ)))⁻¹) (z γ)) := by
    rw [eL, eR, hgrp]
  rw [map_sub, map_add, h1, h2, top_sub, top_add, top_T_zpow]
  ring

theorem bv_invariant {z : Gamma0 N → V n} (hz : z ∈ coeffCocycles (ρC N n)) (σ γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N)
    (j : ℤ) : bv N n z (γ * σ * ModularGroup.T ^ j) = bv N n z σ := by
  rw [bv_mul_T_zpow, show γ = ((⟨γ, hγ⟩ : Gamma0 N) : SL(2, ℤ)) from rfl, bv_mul_left hz]

theorem sub_mem_coeffParabolicCocycles [NeZero N] (hn : Even n) {z w : Gamma0 N → V n}
    (hz : z ∈ coeffCocycles (ρC N n)) (hw : w ∈ coeffCocycles (ρC N n)) (h : ∀ σ, bv N n z σ = bv N n w σ) :
    z - w ∈ coeffParabolicCocycles (ρC N n) := by
  refine mem_coeffParabolicCocycles_of_forall_coeff_binaryFormRepSL_inv_apply_eq_zero N n hn (Submodule.sub_mem _ hz hw)
    fun σ γ hγ => ?_
  have hγ' : γ = conjT N σ := Subtype.ext hγ
  have := h σ
  rw [← sub_eq_zero, ← bv_sub] at this
  rw [hγ']
  exact this

end BV

section Zero

variable {N : ℕ}

theorem finsum_bv_eq_zero [NeZero N] {z : Gamma0 N → V 0} (hz : z ∈ coeffCocycles (ρC N 0)) :
    ∑ᶠ q : SL(2, ℤ) ⧸ Gamma0 N, bv N 0 z q.out⁻¹ = 0 := by

  have hadd : ∀ g h : Gamma0 N, z (g * h) = z g + z h := by
    intro g h
    rw [hz g h, ρC_apply, R_zero]
  let φ : Additive (Gamma0 N) →+ ℂ :=
    { toFun := fun g => top 0 (z g.toMul)
      map_zero' := by
        change top 0 (z 1) = 0
        rw [cocycle_one hz]; simp [top]
      map_add' := fun g h => by
        change top 0 (z (g.toMul * h.toMul)) = top 0 (z g.toMul) + top 0 (z h.toMul)
        rw [hadd, top_add] }
  have h := CongruenceSubgroup.finsum_addMonoidHom_conj_T_zpow_eq_zero N φ (fun q => conjT N q.out⁻¹) (fun q => by
    rw [coe_conjT, inv_inv])
  refine Eq.trans (finsum_congr fun q => ?_) h
  change top 0 (R 0 (q.out⁻¹)⁻¹ (z (conjT N q.out⁻¹))) = top 0 (z (conjT N q.out⁻¹))
  rw [R_zero]

end Zero

section Analytic

variable {N : ℕ} {k : ℤ}

def mulN (N : ℕ) [NeZero N] (τ : ℍ) : ℍ :=
  ⟨(N : ℂ) * τ, by
    rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) τ.im_pos⟩

@[scoped simp] theorem coe_mulN [NeZero N] (τ : ℍ) : ((mulN N τ : ℍ) : ℂ) = (N : ℂ) * τ := rfl

theorem im_mulN [NeZero N] (τ : ℍ) : (mulN N τ).im = N * τ.im := by
  rw [← UpperHalfPlane.coe_im, coe_mulN, Complex.mul_im]; simp

theorem tendsto_mulN [NeZero N] : Tendsto (mulN N) atImInfty atImInfty := by
  rw [atImInfty, tendsto_comap_iff]
  have : UpperHalfPlane.im ∘ mulN N = fun τ => (N : ℝ) * τ.im := funext fun τ => im_mulN τ
  rw [this]
  exact Tendsto.const_mul_atTop (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))) tendsto_comap

theorem denom_T_zpow (m : ℤ) (τ : ℍ) : denom (ModularGroup.T ^ m : SL(2, ℤ)) τ = 1 := by
  rw [ModularGroup.denom_apply]
  simp [ModularGroup.coe_T_zpow]

theorem slash_T_zpow_apply (g : ℍ → ℂ) (m : ℤ) (τ : ℍ) :
    (g ∣[k] (ModularGroup.T ^ m)) τ = g ((m : ℝ) +ᵥ τ) := by
  rw [ModularForm.SL_slash_apply, denom_T_zpow, one_zpow, mul_one, modular_T_zpow_smul]

theorem slash_periodic (f : ModularForm (Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    ((⇑f) ∣[k] σ) (((N : ℤ) : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
  rw [← slash_T_zpow_apply (k := k) ((⇑f) ∣[k] σ) (N : ℤ) τ, ← SlashAction.slash_mul]
  have hmul : σ * ModularGroup.T ^ (N : ℤ) = (conjT N σ : SL(2, ℤ)) * σ := by rw [coe_conjT]; group
  have hinv : (⇑f) ∣[k] ((conjT N σ : SL(2, ℤ))) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ (conjT N σ : SL(2, ℤ)))
      (Subgroup.mem_map_of_mem _ (conjT N σ).2)
  rw [hmul, SlashAction.slash_mul, hinv]

theorem slash_periodic' (f : ModularForm (Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    ((⇑f) ∣[k] σ) ((N : ℝ) +ᵥ τ) = ((⇑f) ∣[k] σ) τ := by
  have := slash_periodic f σ τ
  rwa [Int.cast_natCast] at this

theorem mdifferentiable_slash (f : ModularForm (Gamma0 N) k) (σ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) ((⇑f) ∣[k] σ) := by
  rw [ModularForm.SL_slash]
  exact f.holo'.slash k _

theorem continuous_real_vadd (P : ℍ) : Continuous fun t : ℝ => t +ᵥ P := by
  refine UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr ?_
  have : ((↑) : ℍ → ℂ) ∘ (fun t : ℝ => t +ᵥ P) = fun t : ℝ => (t : ℂ) + (P : ℂ) := by
    funext t; simp [UpperHalfPlane.coe_vadd]
  rw [this]
  fun_prop

variable [NeZero N]

theorem integral_slash_eq (f : ModularForm (Gamma0 N) k) (σ : SL(2, ℤ)) {L : ℂ}
    (hL : Tendsto (fun τ => ((⇑f) ∣[k] σ) τ) atImInfty (𝓝 L)) (τ₀ : ℍ) :
    ∫ t in (0 : ℝ)..(N : ℝ), ((⇑f) ∣[k] σ) ((t : ℝ) +ᵥ τ₀) = N * L := by
  set g : ℍ → ℂ := (⇑f) ∣[k] σ with hgdef
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hNneC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g := mdifferentiable_slash f σ
  have hgc : Continuous g := hg.continuous

  set ω : ℍ → ℂ := fun τ => g (mulN N τ) - L with hωdef
  have hper : ∀ τ : ℍ, ω ((1 : ℝ) +ᵥ τ) = ω τ := by
    intro τ
    have hpt : mulN N ((1 : ℝ) +ᵥ τ) = (N : ℝ) +ᵥ mulN N τ := by
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, mul_add]
    simp only [hωdef, hpt]
    exact congrArg (· - L) (slash_periodic' f σ _)
  have hcusp : Tendsto ω atImInfty (𝓝 0) := by
    have h1 : Tendsto (fun τ => g (mulN N τ)) atImInfty (𝓝 L) := hL.comp tendsto_mulN
    have := h1.sub_const L
    rwa [sub_self] at this
  have hhol : ∀ τ : ℍ, (0 : ℝ) < τ.im → ∃ G : ℂ → ℂ, AnalyticAt ℂ G (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) = G z := by
    intro τ _

    have hdiff : DifferentiableOn ℂ (g ∘ ofComplex) {z : ℂ | 0 < z.im} := UpperHalfPlane.mdifferentiable_iff.mp hg
    refine ⟨fun z => (g ∘ ofComplex) ((N : ℂ) * z) - L, ?_, ?_⟩
    · have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_upperHalfPlaneSet
      have hmaps : ∀ z : ℂ, 0 < z.im → 0 < ((N : ℂ) * z).im := by
        intro z hz
        rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
        exact mul_pos hNpos hz
      have hd : DifferentiableOn ℂ (fun z => (g ∘ ofComplex) ((N : ℂ) * z) - L) {z : ℂ | 0 < z.im} := by
        refine DifferentiableOn.sub_const ?_ L
        exact hdiff.comp ((differentiable_id.const_mul (N : ℂ)).differentiableOn) fun z hz => hmaps z hz
      exact (hd.analyticOnNhd hopen) _ τ.im_pos
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)]
        with w _ hw
      have hw' : 0 < ((N : ℂ) * w).im := by
        rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
        exact mul_pos hNpos hw
      simp only [hωdef, Function.comp_apply]
      congr 2
      apply UpperHalfPlane.ext
      rw [coe_mulN, ofComplex_apply_of_im_pos hw, ofComplex_apply_of_im_pos hw']

  set y : ℝ := τ₀.im / N with hy
  have hypos : 0 < y := div_pos τ₀.im_pos hNpos
  have hzero := UpperHalfPlane.intervalIntegral_eq_zero_of_periodic_of_tendsto_atImInfty ω 0 le_rfl hper hcusp hhol y hypos
  set P : ℍ := ⟨(τ₀.im : ℂ) * Complex.I, by simpa using τ₀.im_pos⟩ with hP

  have hpts : ∀ x : ℝ, mulN N (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) = ((N : ℝ) * x : ℝ) +ᵥ P := by
    intro x
    have him : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hypos
    apply UpperHalfPlane.ext
    rw [coe_mulN, ofComplex_apply_of_im_pos him, UpperHalfPlane.coe_vadd]
    change (N : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) = (((N : ℝ) * x : ℝ) : ℂ) + (τ₀.im : ℂ) * Complex.I
    rw [hy]
    push_cast
    field_simp

  have hcont : Continuous fun x : ℝ => g (((N : ℝ) * x : ℝ) +ᵥ P) :=
    hgc.comp ((continuous_real_vadd P).comp (continuous_const.mul continuous_id))
  have h1 : ∫ x in (0 : ℝ)..1, g (((N : ℝ) * x : ℝ) +ᵥ P) = L := by
    have hint : ∫ x in (0 : ℝ)..1, ω (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)) = 0 := hzero
    have heq : (fun x : ℝ => ω (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)))
        = fun x : ℝ => g (((N : ℝ) * x : ℝ) +ᵥ P) - L := by
      funext x; simp only [hωdef, hpts]
    rw [heq, intervalIntegral.integral_sub (hcont.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, sub_zero, one_smul, sub_eq_zero] at hint
    exact hint

  have h2 : ∫ t in (0 : ℝ)..(N : ℝ), g ((t : ℝ) +ᵥ P) = N * L := by
    have h := intervalIntegral.integral_comp_mul_left (fun t : ℝ => g ((t : ℝ) +ᵥ P)) hNne (a := 0) (b := 1)
    simp only [mul_zero, mul_one] at h
    rw [h1] at h

    have : (∫ x in (0 : ℝ)..(N : ℝ), g ((x : ℝ) +ᵥ P)) = (N : ℝ) • L := by
      rw [h, smul_smul, mul_inv_cancel₀ hNne, one_smul]
    rw [this, Complex.real_smul, Complex.ofReal_natCast]

  have hτ₀ : τ₀ = (τ₀.re : ℝ) +ᵥ P := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd]
    change (τ₀ : ℂ) = ((τ₀.re : ℝ) : ℂ) + (τ₀.im : ℂ) * Complex.I
    rw [← UpperHalfPlane.coe_re, ← UpperHalfPlane.coe_im, Complex.re_add_im]
  have hperG : Function.Periodic (fun t : ℝ => g ((t : ℝ) +ᵥ P)) (N : ℝ) := by
    intro t
    change g (((t + N : ℝ)) +ᵥ P) = g ((t : ℝ) +ᵥ P)
    rw [add_comm, ← vadd_vadd]
    exact slash_periodic' f σ _
  calc ∫ t in (0 : ℝ)..(N : ℝ), g ((t : ℝ) +ᵥ τ₀)
      = ∫ t in (0 : ℝ)..(N : ℝ), g (((t + τ₀.re : ℝ)) +ᵥ P) := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          change g ((t : ℝ) +ᵥ τ₀) = g (((t + τ₀.re : ℝ)) +ᵥ P)
          conv_lhs => rw [hτ₀, vadd_vadd]
    _ = ∫ t in (0 + τ₀.re : ℝ)..(N + τ₀.re : ℝ), g ((t : ℝ) +ᵥ P) := by
          rw [intervalIntegral.integral_comp_add_right (fun t : ℝ => g ((t : ℝ) +ᵥ P))]
    _ = ∫ t in (0 : ℝ)..(0 + N : ℝ), g ((t : ℝ) +ᵥ P) := by
          rw [zero_add, add_comm, hperG.intervalIntegral_add_eq τ₀.re 0]
    _ = N * L := by rw [zero_add, h2]

end Analytic

section Main

variable (N : ℕ) [NeZero N] (n : ℕ)

theorem bv_cocycle_eq (f : ModularForm (Gamma0 N) ((n : ℤ) + 2)) {F : ℍ → V n} (hEI : IsEichlerIntegral n (⇑f) F)
    (hF : IsEquivariantPrimitiveWith (ρC N n) F) (σ : SL(2, ℤ)) {L : ℂ}
    (hL : Tendsto (fun τ => ((⇑f) ∣[((n : ℤ) + 2)] σ) τ) atImInfty (𝓝 L)) :
    bv N n hF.cocycle σ = N * L := by
  have hcoc : hF.cocycle (conjT N σ)
      = F ((σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹) • UpperHalfPlane.I)
          - R n (σ * ModularGroup.T ^ (N : ℤ) * σ⁻¹) (F UpperHalfPlane.I) := rfl
  rw [bv, top, hcoc, hEI.coeff_binaryFormRepSL_inv_apply_sub_eq_intervalIntegral_slash f.holo' σ (N : ℤ) UpperHalfPlane.I,
    Int.cast_natCast]
  exact integral_slash_eq f σ hL _

theorem exists_form (hn : Even n) (v : SL(2, ℤ) → ℂ)
    (hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ)
    (hsum : n = 0 → ∑ᶠ q : SL(2, ℤ) ⧸ Gamma0 N, v q.out⁻¹ = 0) :
    ∃ f : ModularForm (Gamma0 N) ((n : ℤ) + 2), ∀ σ : SL(2, ℤ),
      Tendsto (fun τ => ((⇑f) ∣[((n : ℤ) + 2)] σ) τ) atImInfty (𝓝 (v σ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp only [Nat.cast_zero, zero_add]
    exact ModularForm.exists_gamma0_weight_two_forall_tendsto_slash_atImInfty N v hv (hsum rfl)
  · have h3 : (3 : ℤ) ≤ (n : ℤ) + 2 := by
      have : n ≠ 1 := fun h => by rw [h] at hn; exact Nat.not_even_one hn
      omega
    have he : Even ((n : ℤ) + 2) := (Int.even_coe_nat n |>.mpr hn).add even_two
    exact ModularForm.exists_gamma0_forall_tendsto_slash_atImInfty_of_three_le N ((n : ℤ) + 2) h3 he v hv

theorem main (z : ↥(coeffCocycles (ρC N n))) :
    ∃ (f : ModularForm (Gamma0 N) ((n : ℤ) + 2)) (F : ℍ → V n) (_ : IsEichlerIntegral n (⇑f) F)
      (hF : IsEquivariantPrimitiveWith (ρC N n) F),
      (z : Gamma0 N → V n) - hF.cocycle ∈ coeffParabolicCocycles (ρC N n) := by
  rcases Nat.even_or_odd n with hn | hn
  ·
    have hNne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    set v : SL(2, ℤ) → ℂ := fun σ => bv N n z σ / N with hvdef
    have hv : ∀ (σ γ : SL(2, ℤ)), γ ∈ Gamma0 N → ∀ j : ℤ, v (γ * σ * ModularGroup.T ^ j) = v σ := by
      intro σ γ hγ j
      simp only [hvdef, bv_invariant z.2 σ γ hγ j]
    have hsum : n = 0 → ∑ᶠ q : SL(2, ℤ) ⧸ Gamma0 N, v q.out⁻¹ = 0 := by
      rintro rfl
      have h0 := finsum_bv_eq_zero (N := N) z.2
      have : (fun q : SL(2, ℤ) ⧸ Gamma0 N => v q.out⁻¹) = fun q => (N : ℂ)⁻¹ • bv N 0 z q.out⁻¹ := by
        funext q; simp only [hvdef, smul_eq_mul]; ring
      rw [this, ← smul_finsum, h0, smul_zero]
    obtain ⟨f, hf⟩ := exists_form N n hn v hv hsum
    obtain ⟨F, hEI⟩ := exists_isEichlerIntegral n (f := ⇑f) f.holo'
    have hinv : ∀ γ ∈ Gamma0 N, (⇑f) ∣[((n : ℤ) + 2)] γ = ⇑f := fun γ hγ =>
      SlashInvariantFormClass.slash_action_eq f (Matrix.SpecialLinearGroup.mapGL ℝ γ) (Subgroup.mem_map_of_mem _ hγ)
    have hF : IsEquivariantPrimitiveWith (ρC N n) F := isEquivariantPrimitiveWith_of_isEichlerIntegral hEI hinv
    refine ⟨f, F, hEI, hF, sub_mem_coeffParabolicCocycles hn z.2 hF.cocycle_mem_coeffCocycles fun σ => ?_⟩
    rw [bv_cocycle_eq N n f hEI hF σ (hf σ), hvdef]
    field_simp
  ·
    have hEI : IsEichlerIntegral n (⇑(0 : ModularForm (Gamma0 N) ((n : ℤ) + 2))) (fun _ => 0) := by
      intro d τ
      simpa using hasDerivAt_const (τ : ℂ) (MvPolynomial.coeff d ((0 : V n) : MvPolynomial (Fin 2) ℂ))
    have hF : IsEquivariantPrimitiveWith (ρC N n) (fun _ : ℍ => (0 : V n)) := fun γ => ⟨0, fun τ => by simp⟩
    have hcoc : hF.cocycle = 0 := by
      funext γ; simp [IsEquivariantPrimitiveWith.cocycle]
    refine ⟨0, fun _ => 0, hEI, hF, ?_⟩
    rw [hcoc, sub_zero]
    exact coeffCoboundaries_le_coeffParabolicCocycles _ (mem_coeffCoboundaries_of_odd hn z.2)

end Main

end A2BES
p2m_reactivate "P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles.A2BES"

theorem solution (N : ℕ) [NeZero N] (n : ℕ)
    (z : ↥(HeckeEis.coeffCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype))) :
    ∃ (f : ModularForm (CongruenceSubgroup.Gamma0 N) ((n : ℤ) + 2))
      (F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)) (_ : HeckeEis.IsEichlerIntegral n f F)
      (hF : HeckeEis.IsEquivariantPrimitiveWith
        ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) F),
      (z : CongruenceSubgroup.Gamma0 N → ↥(HeckeEis.BinaryForm ℂ n)) - hF.cocycle ∈
        HeckeEis.coeffParabolicCocycles ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype) :=
  A2BES.main N n z

end S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles
end P2MW
export P2MW.S_HeckeEis_exists_modularForm_coeffCocycles_sub_cocycle_mem_coeffParabolicCocycles (solution)
