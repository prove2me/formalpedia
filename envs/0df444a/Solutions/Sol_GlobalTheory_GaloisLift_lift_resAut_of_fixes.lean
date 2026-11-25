-- Prove2me | solution 1 for GlobalTheory.GaloisLift.lift_resAut_of_fixes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:37:33.637948+00:00
-- url     : https://prove2.me/submissions/925499fc-eada-4aaf-a375-cc325ef32321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFixingActsAsFrobeniusPowerResidue
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Pointwise
open GlobalTheory GlobalTheory.GaloisLift
namespace GlobalTheory.GaloisLift
theorem _root_.solution (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (K : IntermediateField E Ω) [FiniteDimensional E K]
    (σ₀ : G E Ω) (hσ₀ : σ₀ ∈ Dec (F := E) A)
    (hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1) :
    ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ρ ∈ Dec (F := E) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (ρ b - σ₀ b) < 1 := by
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set Q := primeBelow (F := K) A with hQ
  set P := Q.under (𝓞 K) with hP
  haveI : Q.LiesOver P := ⟨rfl⟩

  have hint : ∀ (g : G E Ω) (b : IntCl K Ω), IsIntegral (𝓞 K) (g (b : Ω)) := fun g b =>
    ((isIntegral_int_of_isIntegral b.2).map (g.toAlgHom.restrictScalars ℤ)).tower_top
  let e : IntCl K Ω ≃+* IntCl K Ω :=
    { toFun := fun b => ⟨σ₀ b, hint σ₀ b⟩
      invFun := fun b => ⟨σ₀⁻¹ b, hint σ₀⁻¹ b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (mul_inv_apply (b : Ω))
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have he : ∀ b : IntCl K Ω, ((e b : IntCl K Ω) : Ω) = σ₀ b := fun _ => rfl
  have hQe : Q = Q.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap]
    show A.valuation (b : Ω) < 1 ↔ A.valuation (σ₀⁻¹ (b : Ω)) < 1
    exact (valuation_apply_lt_one_iff ((Dec (F := E) A).inv_mem hσ₀) _).symm
  let ψ₀ : (IntCl K Ω ⧸ Q) ≃+* (IntCl K Ω ⧸ Q) := Ideal.quotientEquiv Q Q e hQe
  have hψ₀ : ∀ b, ψ₀ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (e b) := fun _ => rfl
  have hlin : ∀ x : 𝓞 K ⧸ P, ψ₀ (algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x) =
      algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hψ₀, Ideal.Quotient.eq]
    have hz : ((algebraMap (𝓞 K) (IntCl K Ω) a : IntCl K Ω) : Ω) ∈ K := ((a : K)).2
    have := hK _ hz (valuation_le_one_intCl A _)
    exact this
  let ψ : (IntCl K Ω ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (IntCl K Ω ⧸ Q) := AlgEquiv.ofRingEquiv (f := ψ₀) hlin
  obtain ⟨⟨ρ₀, hρ₀Q⟩, hρ₀⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) P Q ψ
  have hρ₀Q' : ρ₀ • Q = Q := hρ₀Q
  have hcong : ∀ b : IntCl K Ω, A.valuation (ρ₀ (b : Ω) - σ₀ b) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ₀ • b) = Ideal.Quotient.mk Q (e b) :=
      DFunLike.congr_fun hρ₀ (Ideal.Quotient.mk Q b)
    have h2 : ρ₀ • b - e b ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
    exact h2
  have hdec : ρ₀ • A = A := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (ρ₀ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρ₀Q']
  refine ⟨ρ₀.restrictScalars E, fun z hz => ρ₀.commutes ⟨z, hz⟩, ?_, fun b hb => hcong ⟨b, hb.tower_top⟩⟩
  show (ρ₀.restrictScalars E) • A = A
  conv_rhs => rw [← hdec]
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl
end GlobalTheory.GaloisLift
