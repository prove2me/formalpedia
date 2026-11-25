-- Prove2me | solution 1 for GlobalTheory.finrank_skewHermitian_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:46:26.071901+00:00
-- url     : https://prove2.me/submissions/f1d46200-b21e-4c5e-b29d-5dea7dfbd659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_NormConst
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CuspFree
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RdOrbIntOfLatZ
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__ExistsNormTensor_9eff20d6b37353d0
import Definitions.Def_Development_AbelianVarietyTheory_Statements_HyperbolicHypotheses_HypothesesInhabitedHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankRatSkewHermitianMatricesCmField
import Theorems.Thm_GlobalTheory_two_mul_card_of_cmType_finset
import Theorems.Thm_Formalism_L2_Pj_FJ_FnVia_smul_apply
import Theorems.Thm_GlobalTheory_HostModel_host_d
import Theorems.Thm_GlobalTheory_HostModel_host_rt
import Theorems.Thm_GlobalTheory_HostModel_host_rt0_eq_I_mul_sqrt_seven
import Theorems.Thm_GlobalTheory_HostModel_host_w0_eq_halfSqrtNegSeven
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_p
import Theorems.Thm_GlobalTheory_HostModel_hypDatum_q
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.HostModel.host_d
attribute [local simp] GlobalTheory.HostModel.host_rt
attribute [local simp] GlobalTheory.HostModel.host_rt0_eq_I_mul_sqrt_seven
attribute [local simp] GlobalTheory.HostModel.host_w0_eq_halfSqrtNegSeven
attribute [local simp] GlobalTheory.HostModel.hypDatum_p
attribute [local simp] GlobalTheory.HostModel.hypDatum_q



set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ρ : ℕ) (Ψ : Finset (E →+* ℂ)),
      (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) →
      ∀ W : Submodule ℚ (Matrix (Fin ρ) (Fin ρ) E), (∀ β, β ∈ W ↔ FJ.IsSkew β) →
        Module.finrank ℚ W = Ψ.card * ρ ^ 2 := by
  intro E _ _ _ ρ Ψ hΨ W hW
  have hcard := two_mul_card_of_cmType_finset E Ψ hΨ
  obtain ⟨δ, hδ0, hδ⟩ : ∃ δ : E, δ ≠ 0 ∧ IsCMField.complexConj E δ = -δ := by
    have hne : IsCMField.complexConj E ≠ 1 := IsCMField.complexConj_ne_one E
    obtain ⟨x, hx⟩ : ∃ x : E, IsCMField.complexConj E x ≠ x := by
      by_contra h
      push Not at h
      exact hne (AlgEquiv.ext h)
    refine ⟨x - IsCMField.complexConj E x, sub_ne_zero.mpr hx.symm, ?_⟩
    rw [map_sub, IsCMField.complexConj_apply_apply]
    ring
  have hW' : ∀ β, β ∈ W ↔ ∀ a b, IsCMField.complexConj E (β a b) = -β b a := hW
  let f : (W × W) →ₗ[ℚ] Matrix (Fin ρ) (Fin ρ) E :=
    { toFun := fun p => (p.1 : Matrix (Fin ρ) (Fin ρ) E) + δ • (p.2 : Matrix (Fin ρ) (Fin ρ) E)
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, smul_add]
        abel
      map_smul' := by
        intro c p
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, RingHom.id_apply,
          smul_comm δ c] }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨A, B⟩ h
    have hA := (hW' _).mp A.2
    have hB := (hW' _).mp B.2
    have h0 : ∀ a b, (A : Matrix (Fin ρ) (Fin ρ) E) a b + δ * (B : Matrix (Fin ρ) (Fin ρ) E) a b = 0 :=
      fun a b => by
        have := congrFun (congrFun h a) b
        simpa [f] using this
    have h1 : ∀ a b, (A : Matrix (Fin ρ) (Fin ρ) E) a b = 0 ∧ (B : Matrix (Fin ρ) (Fin ρ) E) a b = 0 := by
      intro a b
      have e1 := h0 a b
      have e2 := congrArg (IsCMField.complexConj E) (h0 b a)
      rw [map_add, map_mul, hδ, hA, hB, map_zero] at e2
      have e3 : (A : Matrix (Fin ρ) (Fin ρ) E) a b = 0 := by linear_combination (e1 - e2) / 2
      refine ⟨e3, ?_⟩
      rw [e3, zero_add] at e1
      exact (mul_eq_zero.mp e1).resolve_left hδ0
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext a b; exact (h1 a b).1
    · ext a b; exact (h1 a b).2
  have hsurj : Function.Surjective f := by
    intro M
    refine ⟨(⟨Matrix.of fun a b => (M a b - IsCMField.complexConj E (M b a)) / 2, (hW' _).mpr ?_⟩,
      ⟨Matrix.of fun a b => (M a b + IsCMField.complexConj E (M b a)) / (2 * δ), (hW' _).mpr ?_⟩), ?_⟩
    · intro a b
      simp only [Matrix.of_apply, map_div₀, map_sub, IsCMField.complexConj_apply_apply, map_ofNat]
      ring
    · intro a b
      simp only [Matrix.of_apply, map_div₀, map_add, map_mul, hδ,
        IsCMField.complexConj_apply_apply, map_ofNat]
      field_simp
      ring
    · ext a b
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk, Matrix.add_apply, Matrix.smul_apply,
        Matrix.of_apply, smul_eq_mul]
      field_simp
      ring
  have hfin := (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩).finrank_eq
  rw [Module.finrank_prod, Module.finrank_matrix, ← hcard, Fintype.card_fin] at hfin
  have : 2 * Module.finrank ℚ W = 2 * (Ψ.card * ρ ^ 2) := by
    rw [two_mul, hfin]; ring
  omega
end GlobalTheory
