-- Prove2me | solution 1 for GroundTheory.Automorphic.IsExpLieAlgebra.exists_aeval_laplacian_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:38:28.366803+00:00
-- url     : https://prove2.me/submissions/e2e8a7c6-8033-47f6-97f7-b734e9425b7f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ZKFinite
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Theorems.Thm_GroundTheory_Automorphic_casimir_mem_center
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_AdL_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_Ad_one
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_Ad
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_bracket
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightDerivEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_coe_rightTranslateEnd
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_derivLie_apply
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_finiteDimensional_zkSpan
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightDeriv_mem_of_isKStable
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightTranslate_mem_zkSpan
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction_mem_zkSpan
import Theorems.Thm_GroundTheory_Automorphic_IsExpLieAlgebra_self_mem_zkSpan
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_coe_restrict_apply
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
import Theorems.Thm_P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.AdL_apply
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.Ad_one
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_Ad
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_bracket
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightDerivEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.coe_rightTranslateEnd
attribute [local simp] GroundTheory.Automorphic.IsExpLieAlgebra.derivLie_apply
attribute [local simp] GroundTheory.Automorphic.UnitaryRep.coe_restrict_apply
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_rightUAction___d9062316eb7b
attribute [local simp] P2M_GroundTheory_Automorphic_IsExpLieAlgebra_uAction___195cbae0e32a



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open Set Filter Topology
set_option linter.unusedSectionVars false
attribute [local instance 100] LieRing.ofAssociativeRing
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}
open GroundTheory.Automorphic.IsExpLieAlgebra
variable (h : IsExpLieAlgebra G 𝔤)
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {ι : Type*} [Fintype ι]
namespace GroundTheory.Automorphic.IsExpLieAlgebra
theorem _root_.solution [DecidableEq ι] (K : Subgroup G)
    (B : LinearMap.BilinForm ℝ h.lieSubalgebra) (b : Module.Basis ι ℝ h.lieSubalgebra) (ε : ι → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (horth : ∀ i j, B (b i) (b j) = if i = j then ε i else 0)
    (hsymm : ∀ X Y : h.lieSubalgebra, B X Y = B Y X)
    (hinv : ∀ X Y Z : h.lieSubalgebra, B ⁅X, Y⁆ Z = -B Y ⁅X, Z⁆)
    (hK : ∀ i, ε i = -1 → ∀ t : ℝ, h.expG (t • h.ofLie (b i)) ∈ K)
    (f : h.smoothFuns (F := F)) (hfK : IsRightKFinite K (f : G → F)) (hfZ : h.IsZFinite f) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (h.laplacian (F := F) b) P f = 0 := by
  have hε2 : ∀ i, ε i * ε i = 1 := fun i => by rcases hε i with e | e <;> rw [e] <;> norm_num
  set V := h.zkSpan K f
  haveI : FiniteDimensional ℂ V := h.finiteDimensional_zkSpan K f hfK hfZ
  have hVK : ∀ (k : K), ∀ w ∈ V, h.rightTranslateEnd (k : G) w ∈ V :=
    fun k w hw => h.rightTranslate_mem_zkSpan K f k hw

  have hΔ : h.laplacian (F := F) b = h.rightUAction (casimir b ε) +
      ∑ i, (1 - ε i) • (h.rightDerivEnd (h.ofLie (b i)) * h.rightDerivEnd (h.ofLie (b i))) := by
    simp only [laplacian, casimir, map_sum, map_smul, map_mul, rightUAction_ι,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← add_smul, add_sub_cancel, one_smul]
  have hΩ := casimir_mem_center (hε2) horth hsymm hinv (b := b)
  have hmapsto : ∀ w ∈ V, h.laplacian (F := F) b w ∈ V := by
    intro w hw
    rw [hΔ, LinearMap.add_apply, LinearMap.sum_apply]
    refine Submodule.add_mem _ (h.rightUAction_mem_zkSpan K f hΩ hw) (Submodule.sum_mem _ fun i _ => ?_)
    rw [LinearMap.smul_apply, Module.End.mul_apply]
    rcases hε i with e | e
    · rw [e, sub_self, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_of_tower_mem _ _ ?_
      exact h.rightDeriv_mem_of_isKStable K hVK (hK i e)
        (h.rightDeriv_mem_of_isKStable K hVK (hK i e) hw)
  have hf : f ∈ V := h.self_mem_zkSpan K f
  by_cases hf0 : f = 0
  · refine ⟨Polynomial.X, Polynomial.monic_X, by simp, ?_⟩
    simp [hf0]
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ, Δ = h.laplacian (F := F) b := ⟨_, rfl⟩
  rw [← hΔdef]
  rw [← hΔdef] at hmapsto
  have hmemk : ∀ k : ℕ, (Δ ^ k) f ∈ V := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih => rw [pow_succ', Module.End.mul_apply]; exact hmapsto _ ih
  set n := Module.finrank ℂ V
  let u : Fin (n + 1) → h.smoothFuns (F := F) := fun i => (Δ ^ (i : ℕ)) f
  have hspan : Submodule.span ℂ (range u) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hmemk i
  have hnot : ¬ LinearIndependent ℂ u := fun hli => by
    have h1 := finrank_span_eq_card hli
    have h2 := Submodule.finrank_mono hspan
    rw [h1, Fintype.card_fin] at h2
    omega
  obtain ⟨g, hg, i, hi⟩ := Fintype.not_linearIndependent_iff.1 hnot
  obtain ⟨Q, hQdef⟩ : ∃ Q : Polynomial ℂ,
      Q = ∑ j : Fin (n + 1), Polynomial.C (g j) * Polynomial.X ^ (j : ℕ) := ⟨_, rfl⟩
  have hQf : Polynomial.aeval Δ Q f = 0 := by
    have e1 : Polynomial.aeval Δ Q f = ∑ j : Fin (n + 1), g j • (Δ ^ (j : ℕ)) f := by
      rw [hQdef, map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, Module.End.mul_apply,
        Module.algebraMap_end_apply]
    rw [e1]
    exact hg
  have hQ0 : Q ≠ 0 := by
    intro h0
    apply hi
    have := congrArg (fun P => P.coeff (i : ℕ)) h0
    simp only [hQdef, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single i] at this
    · simpa using this
    · intro j _ hj
      have : (i : ℕ) ≠ (j : ℕ) := fun e => hj (Fin.ext e).symm
      simp [this]
    · simp
  refine ⟨Q * Polynomial.C Q.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hQ0, ?_, ?_⟩
  · rw [Polynomial.natDegree_mul_C (inv_ne_zero (Polynomial.leadingCoeff_ne_zero.2 hQ0))]
    by_contra hdeg
    push_neg at hdeg
    have hQc := Polynomial.eq_C_of_natDegree_le_zero hdeg
    have hc : Q.coeff 0 ≠ 0 := by
      intro hc; apply hQ0; rw [hQc, hc, map_zero]
    rw [hQc, Polynomial.aeval_C, Module.algebraMap_end_apply] at hQf
    exact hf0 ((smul_eq_zero.1 hQf).resolve_left hc)
  · rw [map_mul, Polynomial.aeval_C, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul,
      hQf, smul_zero]
end GroundTheory.Automorphic.IsExpLieAlgebra
