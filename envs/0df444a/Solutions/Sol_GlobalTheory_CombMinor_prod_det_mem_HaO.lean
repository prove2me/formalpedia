-- Prove2me | solution 1 for GlobalTheory.CombMinor.prod_det_mem_HaO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:31:43.058859+00:00
-- url     : https://prove2.me/submissions/cd97b8b4-de5a-4c33-a03f-5e00681fcebb

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ProdDetMemHaO
import Theorems.Thm_GlobalTheory_CombMinor_cMat_supported
import Theorems.Thm_GlobalTheory_CombMinor_cMat_range
import Theorems.Thm_GlobalTheory_CombMinor_cMat_rowShift
import Theorems.Thm_GlobalTheory_CombMinor_cMat_hom
import Theorems.Thm_Formalism_L2_Pj_Crude_crPderiv_supported
import Theorems.Thm_Formalism_L2_Pj_Crude_crW_weight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical MvPolynomial Formalism.L2.Pj Formalism.L2.Pj.Crude
open GlobalTheory GlobalTheory.CombMinor
variable {Ty : Type} {r : Ty → ℕ} {n : ℕ} {k : Type} [Field k]
namespace GlobalTheory.CombMinor
theorem _root_.solution : ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (k : Type) [Field k] (O : Subring k) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ) (A : Type) [Fintype A] (σ : A → Ty) (s : A → ℕ) (hs : ∀ α, s α ≤ r (σ α)) (B : ∀ α, Fin (s α) → Fin n → k) (e : A → ℕ), (∀ α ρ b, B α ρ b ∈ O) → (∀ τ, cc τ ≠ τ) → (∀ α α', e α ≠ 0 → e α' ≠ 0 → σ α' = cc (σ α) → ∀ ρ ρ' b, B α ρ b = 0 ∨ B α' ρ' b = 0) → (∀ (τ : Ty) (i : Fin (r τ)), ∑ α ∈ Finset.univ.filter (fun α => σ α = τ ∧ i.val < s α), e α = a τ i) → (∏ α, (Matrix.of fun ρ i : Fin (s α) => ∑ b, MvPolynomial.C (B α ρ b) * (MvPolynomial.X ⟨σ α, Fin.castLE (hs α) i, b⟩ : MvPolynomial (Letter Ty r n) k)).det ^ e α) ∈ HaO r n k O cc isX a := by
  intro Ty _ r n k _ O cc isX a A _ σ s hs B e hO _ hdis hdeg
  change (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ _
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · let S : Set (Letter Ty r n) := {ℓ | ∃ α, e α ≠ 0 ∧ σ α = ℓ.1 ∧ ∃ ρ, B α ρ ℓ.2.2 ≠ 0}
    have hS : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈ supported k S := by
      refine Subalgebra.prod_mem _ fun α _ => ?_
      by_cases he : e α = 0
      · rw [he, pow_zero]; exact Subalgebra.one_mem _
      · exact Subalgebra.pow_mem _ (cMat_supported _ _ _ _ S fun ρ i b hb =>
          (show _ ∈ S from ⟨α, he, rfl, ρ, hb⟩)) _
    generalize (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) = P at hS
    simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker]
    intro τ _ i i'
    simp only [lap, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun b' _ => ?_
    by_cases hb : b = b'
    · subst hb
      have key : pderiv (⟨τ, i, b⟩ : Letter Ty r n) (pderiv (⟨cc τ, i', b⟩ : Letter Ty r n) P) = 0 := by
        by_cases hg : (⟨cc τ, i', b⟩ : Letter Ty r n) ∈ S
        · have hg' : (⟨τ, i, b⟩ : Letter Ty r n) ∉ S := by
            rintro ⟨α, he, hσ, ρ, hρ⟩
            obtain ⟨α', he', hσ', ρ', hρ'⟩ := hg
            rcases hdis α α' he he' (by rw [hσ', hσ]) ρ ρ' b with h | h
            · exact hρ h
            · exact hρ' h
          exact pderiv_eq_zero_of_notMem_vars
            (fun hv => hg' (mem_supported.1 (crPderiv_supported _ hS) hv))
        · rw [pderiv_eq_zero_of_notMem_vars (fun hv => hg (mem_supported.1 hS hv)), map_zero]
      simpa using congrArg (fun x => (1 : k) • x) key
    · simp [Matrix.one_apply_ne hb]
  · intro τ i i' hii t
    rw [map_prod]
    refine Finset.prod_congr rfl fun α _ => ?_
    rw [map_pow, cMat_rowShift _ _ _ _ _ _ _ hii]
  · intro m hm τ i
    rw [← crW_weight]
    have h := IsWeightedHomogeneous.prod Finset.univ (fun α => (cMat (σ α) (s α) (hs α) (B α)).det ^ e α)
      (fun α => e α • (if σ α = τ ∧ i.val < s α then 1 else 0))
      (fun α _ => (cMat_hom (σ α) (s α) (hs α) (B α) τ i.val).pow (e α))
    rw [h (Finsupp.mem_support_iff.1 hm), ← hdeg τ i, Finset.sum_filter]
    refine Finset.sum_congr rfl fun α _ => ?_
    split_ifs <;> simp
  · intro m
    obtain ⟨Q, hQ⟩ : (∏ α, (cMat (σ α) (s α) (hs α) (B α)).det ^ e α) ∈
        (MvPolynomial.map (σ := Letter Ty r n) O.subtype).range :=
      Subring.prod_mem _ fun α _ => Subring.pow_mem _ (cMat_range O _ _ _ _ (hO α)) _
    rw [← hQ, coeff_map]
    exact (Q.coeff m).2
end GlobalTheory.CombMinor
