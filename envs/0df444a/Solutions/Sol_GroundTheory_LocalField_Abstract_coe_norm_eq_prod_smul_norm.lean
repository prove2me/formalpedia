-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_norm_eq_prod_smul_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:13.799346+00:00
-- url     : https://prove2.me/submissions/298aeed2-5a51-4194-8689-317f9d4c43e4

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_NormFormula
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_Reciprocity
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_CoeNormEqProdSmulNorm
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_intCast_mem_multiples_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_mem_multiples
import Theorems.Thm_GroundTheory_LocalField_Abstract_ProfiniteInteger_proj_eq_zero_iff
import Theorems.Thm_GroundTheory_LocalField_Abstract_coe_norm
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
open ProfiniteInteger
variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (d : G →* Multiplicative ℤ̂) {K S J : Subgroup G} {f n : ℕ}
    (hn : 0 < n) (hf : 0 < f) (hSK : S ≤ K)
    (hdS : ∀ s ∈ S, Multiplicative.toAdd (d s) ∈ multiples (n * f))
    (hsurj : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples (n * f) → ∃ s ∈ S, d s = d k)
    (hdK : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples f)
    (hJ : ∀ q ∈ K ⊓ d.ker, q ∈ S ↔ q ∈ J)
    {φ : G} (hφK : φ ∈ K) (hdφ : d φ = Multiplicative.ofAdd (f : ℤ̂))
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf (K ⊓ d.ker)).FiniteIndex]
    (a : fixedModule A S) (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) =
      ∏ ν : Fin n, φ ^ (ν : ℕ) • (norm A (K ⊓ d.ker) J ⟨a, ha⟩ : A) := by
  classical
  set Q := K ⊓ d.ker with hQ
  have hQK : Q ≤ K := inf_le_left

  let incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  let φK : K := ⟨φ, hφK⟩
  let F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K := fun p => (φK ^ (p.1 : ℕ)) • incl p.2
  have hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) =
      ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) := fun _ _ => rfl

  have hdeg : ∀ (m : ℤ) (q : G), q ∈ Q →
      Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂) := by
    intro m q hq
    rw [map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
      zsmul_eq_mul]
    push_cast
    ring
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ν, x⟩ ⟨μ, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy

        have hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) =
            (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q') := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          group
        have hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) =
            ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂) := by
          rw [map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]
          exact hdeg _ _ q'.2
        have hmem := hdS _ hxy
        rw [hx, hdq] at hmem
        have hdvd := (intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem
        push_cast at hdvd
        have hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν :=
          (mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd
        have hνμ : ν = μ := by
          have hμ := μ.2
          have hν := ν.2
          have h0 : ((μ : ℤ) - ν) = 0 :=
            Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
          exact Fin.ext (by omega)
        subst hνμ
        have hqq : (q : G)⁻¹ * q' ∈ S := by simpa [mul_assoc] using hxy
        have hqQ : (q : G)⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
        refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (hJ _ hqQ).1 hqq
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨w, hw⟩ := mem_multiples.1 (hdK k k.2)
        set N : ℕ+ := ⟨n, hn⟩ with hNdef
        set ν : ℕ := (proj N w).val with hνdef
        have hνn : ν < n := ZMod.val_lt _
        have hw' : w - (ν : ℤ̂) ∈ multiples n := by
          have := (proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by
            rw [map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])
          simpa [hNdef] using this
        obtain ⟨z, hz⟩ := mem_multiples.1 hw'
        have hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f) := by
          rw [map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]
          refine mem_multiples.2 ⟨z, ?_⟩
          have : w = (ν : ℤ̂) + n • z := by rw [← hz]; ring
          rw [this]
          simp only [nsmul_eq_mul, zsmul_eq_mul]
          push_cast
          ring
        obtain ⟨s, hs, hds⟩ := hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk
        set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef
        have hqQ : q ∈ Q := by
          refine ⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩
          show d q = 1
          rw [hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]
        refine ⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]
        have : ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s := by
          rw [zpow_neg, zpow_natCast]
          group
        rw [this]
        exact hs
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]
  let _ := Fintype.ofFinite (Q ⧸ J.subgroupOf Q)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H q =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]
    rfl
end GroundTheory.LocalField.Abstract
