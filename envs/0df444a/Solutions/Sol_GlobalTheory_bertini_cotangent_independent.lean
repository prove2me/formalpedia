-- Prove2me | solution 1 for GlobalTheory.bertini_cotangent_independent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:32.696075+00:00
-- url     : https://prove2.me/submissions/8d2bd8af-2338-4faa-b254-0f5a0ea07976

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationSplitKaehlerDSmoothStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BertiniGeneralMembersNoDerivativeRelationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GenericResidueLinearIndependence
import Theorems.Thm_GlobalTheory_residue_algebraMap_eq_zero_iff_mem
import Theorems.Thm_GlobalTheory_cotangent_relation_derivation
import Theorems.Thm_GlobalTheory_T_bertini_general_members_no_derivative_relation
import Theorems.Thm_GlobalTheory_T_exists_derivation_split_kaehlerD_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsLocalRing
namespace GlobalTheory
theorem _root_.solution : ∀ (k A : Type) [Field k] [CharZero k] [CommRing A] [Algebra k A] [Algebra.Smooth k A] {ι : Type} [Fintype ι] (f : ι → A) (M : ℕ), ∃ Q : MvPolynomial (Fin M × ι) k, Q ≠ 0 ∧ ∀ u : Fin M × ι → k, MvPolynomial.eval u Q ≠ 0 → ∀ (q : Ideal A) [q.IsPrime] (R : Type) [CommRing R] [IsLocalRing R] [Algebra A R] [IsLocalization.AtPrime R q], (∃ p, f p ∉ q) → LinearIndependent (IsLocalRing.ResidueField R) (fun j : {j : Fin M // algebraMap A R (∑ p, u (j, p) • f p) ∈ IsLocalRing.maximalIdeal R} => ((IsLocalRing.maximalIdeal R).toCotangent ⟨_, j.2⟩ : IsLocalRing.CotangentSpace R)) := by
  intro k A _ _ _ _ _ ι _ f M
  obtain ⟨n, δ, ω, hD⟩ := GlobalTheory.T.exists_derivation_split_kaehlerD_smooth k A
  have hC := fun (J : Finset (Fin M)) (i₀ : Fin M) (p₀ : ι) (h : i₀ ∈ J) =>
    GlobalTheory.T.bertini_general_members_no_derivative_relation k A n δ ω hD f M J i₀ p₀ h
  classical
  let Qf : Finset (Fin M) × Fin M × ι → MvPolynomial (Fin M × ι) k := fun x =>
    if h : x.2.1 ∈ x.1 then (hC x.1 x.2.1 x.2.2 h).choose else 1
  refine ⟨∏ x, Qf x, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro x _
    simp only [Qf]
    split_ifs with h
    · exact (hC _ _ _ h).choose_spec.1
    · exact one_ne_zero
  · intro u hu q _ R _ _ _ _ hp
    obtain ⟨p₀, hp₀⟩ := hp
    rw [map_prod, Finset.prod_ne_zero_iff] at hu
    rw [linearIndependent_iff']
    intro s w hw i₀ hi₀
    by_contra hne
    let ψ : A →+* ResidueField R := (residue R).comp (algebraMap A R)
    letI : Algebra k (ResidueField R) := (ψ.comp (algebraMap k A)).toAlgebra
    let φ : A →ₐ[k] ResidueField R := { ψ with commutes' := fun _ => rfl }
    let J : Finset (Fin M) := s.map (Function.Embedding.subtype _)
    let c : Fin M → ResidueField R := fun j =>
      if h : algebraMap A R (∑ p, u (j, p) • f p) ∈ maximalIdeal R then w ⟨j, h⟩ / w i₀ else 0
    have hJ : i₀.1 ∈ J := Finset.mem_map_of_mem _ hi₀
    have hx := hu (J, i₀.1, p₀) (Finset.mem_univ _)
    simp only [Qf, dif_pos hJ] at hx
    refine (hC J i₀.1 p₀ hJ).choose_spec.2 u hx (ResidueField R) φ c ?_ ?_ ?_ ?_
    · exact fun h => hp₀ ((residue_algebraMap_eq_zero_iff_mem q _).1 h)
    · show c i₀.1 = 1
      rw [show c i₀.1 = w i₀ / w i₀ from dif_pos i₀.2]
      exact div_self hne
    · intro i hi
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.1 hi
      exact (residue_eq_zero_iff _).2 j.2
    · intro l
      have hrel : ∑ j ∈ s, (w j / w i₀) •
          (maximalIdeal R).toCotangent ⟨_, j.2⟩ = 0 := by
        simp_rw [div_eq_mul_inv, mul_comm _ (w i₀)⁻¹, mul_smul]
        rw [← Finset.smul_sum, hw, smul_zero]
      have key := cotangent_relation_derivation q (δ l) s
        (fun j => ∑ p, u (j.1, p) • f p) (fun j => j.2) (fun j => w j / w i₀) hrel
      rw [Finset.sum_map]
      convert key using 2 with j hj
      show c j.1 * φ _ = _
      rw [show c j.1 = w j / w i₀ from dif_pos j.2]
      rfl
end GlobalTheory
