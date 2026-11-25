-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.integral_mul_coeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:04:36.38055+00:00
-- url     : https://prove2.me/submissions/966ae81a-fa3a-4a8f-976e-b61a60831621

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_HaarCosets
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJInducedCoeff
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
import Theorems.Thm_GroundTheory_Automorphic_integral_eq_smul_finsum_coset
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal Parabolic Iwasawa MeasureTheory
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]
    {K : Subgroup (GL (Fin n) F)} (hKc : IsCompact (K : Set (GL (Fin n) F)))
    (hKo : IsOpen (K : Set (GL (Fin n) F)))
    {lam : Module.Dual ℂ (parabolicIndSpace F n β σ)}
    {φ : parabolicIndSpace F n β σ} (hφ : φ ∈ fixedVectors (parabolicInd F n β σ) K)
    {R : Finset (GL (Fin n) F)} {ℓ : GL (Fin n) F → Module.Dual ℂ W}
    (hdec : ∀ ψ ∈ fixedVectors (parabolicInd F n β σ) K,
      lam ψ = ∑ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x))
    {h : GL (Fin n) F → ℂ} (hh : HasCompactSupport h) (hhl : ∀ k ∈ K, ∀ g, h (k * g) = h g)
    (hhr : ∀ k ∈ K, ∀ g, h (g * k) = h g) :
    ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ =
      ∑ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ := by
  classical
  let Ko : OpenSubgroup (GL (Fin n) F) := ⟨K, hKo⟩
  have hφk : ∀ k ∈ K, parabolicInd F n β σ k φ = φ := fun k hk => hφ k hk

  have hfin : (QuotientGroup.mk '' tsupport h : Set (GL (Fin n) F ⧸ K)).Finite :=
    finite_image_mk_tsupport Ko hh

  have hL : ∫ g, h g * lam (parabolicInd F n β σ g φ) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * lam (parabolicInd F n β σ (g * k) φ) = h g * lam (parabolicInd F n β σ g φ)
    rw [hhr k hk, map_mul, Module.End.mul_apply, hφk k hk]
  have hR : ∀ x ∈ R, ∫ g, h g * ℓ x ((φ : GL (Fin n) F → W) (x * g)) ∂μ = μ.real (K : Set (GL (Fin n) F)) •
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    refine integral_eq_smul_finsum_coset μ Ko hKc (hh.mul_right) fun g k hk => ?_
    show h (g * k) * ℓ x ((φ : GL (Fin n) F → W) (x * (g * k))) = h g * ℓ x ((φ : GL (Fin n) F → W) (x * g))
    have := congrArg (fun f : parabolicIndSpace F n β σ => (f : GL (Fin n) F → W) (x * g)) (hφk k hk)
    simp only [coe_indRep_apply] at this
    rw [hhr k hk, ← mul_assoc, this]

  set ψ : parabolicIndSpace F n β σ := ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out • parabolicInd F n β σ c.out φ
    with hψdef
  have hψsupp : (Function.support fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ).Finite :=
    hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
      QuotientGroup.out_eq' c⟩
  have hψK : ψ ∈ fixedVectors (parabolicInd F n β σ) K := by
    intro k hk
    rw [hψdef, map_finsum (parabolicInd F n β σ k) hψsupp]
    have hterm : ∀ c : GL (Fin n) F ⧸ K,
        parabolicInd F n β σ k (h c.out • parabolicInd F n β σ c.out φ) =
        (fun c : GL (Fin n) F ⧸ K => h c.out • parabolicInd F n β σ c.out φ)
          (MulAction.toPerm k c) := by
      intro c
      have hmk : (QuotientGroup.mk (k * c.out) : GL (Fin n) F ⧸ K) = MulAction.toPerm k c := by
        show QuotientGroup.mk (k * c.out) = k • c
        conv_rhs => rw [← QuotientGroup.out_eq' c]
        rfl
      obtain ⟨j, hj, hjeq⟩ : ∃ j ∈ K, k * c.out = (MulAction.toPerm k c).out * j := by
        refine ⟨((MulAction.toPerm k c).out)⁻¹ * (k * c.out), ?_, by group⟩
        have := QuotientGroup.eq.1 ((QuotientGroup.out_eq' (MulAction.toPerm k c)).trans hmk.symm)
        simpa using this
      have hhc : h c.out = h (MulAction.toPerm k c).out := by
        rw [← hhl k hk c.out, hjeq, hhr j hj]
      dsimp only
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, hjeq, map_mul, Module.End.mul_apply,
        hφk j hj, hhc]
    rw [finsum_congr hterm]
    exact finsum_comp_equiv (MulAction.toPerm k) (f := fun c : GL (Fin n) F ⧸ K =>
      h c.out • parabolicInd F n β σ c.out φ)

  have h1 : lam ψ = ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * lam (parabolicInd F n β σ c.out φ) := by
    rw [hψdef, map_finsum lam hψsupp]
    simp only [map_smul, smul_eq_mul]
  have h2 : ∀ x ∈ R, ℓ x ((ψ : GL (Fin n) F → W) x) =
      ∑ᶠ c : GL (Fin n) F ⧸ K, h c.out * ℓ x ((φ : GL (Fin n) F → W) (x * c.out)) := by
    intro x _
    let ev : parabolicIndSpace F n β σ →ₗ[ℂ] W :=
      LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin n) F => W) x ∘ₗ
        (parabolicIndSpace F n β σ).subtype
    have hev : (ψ : GL (Fin n) F → W) x = ev ψ := rfl
    rw [hev, hψdef, map_finsum ev hψsupp, map_finsum (ℓ x)]
    · refine finsum_congr fun c => ?_
      simp [ev, coe_indRep_apply]
    · exact hfin.subset fun c hc => ⟨c.out, subset_tsupport h fun h0 => hc (by simp [h0]),
        QuotientGroup.out_eq' c⟩
  rw [hL, ← h1, hdec ψ hψK, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [hR x hx, h2 x hx]
end GroundTheory.Automorphic.GodementJacquet
