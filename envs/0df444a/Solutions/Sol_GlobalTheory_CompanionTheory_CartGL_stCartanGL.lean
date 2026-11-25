-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CartGL.stCartanGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:32:56.778492+00:00
-- url     : https://prove2.me/submissions/d48aa027-a73e-44ae-a795-8b410f4c0534

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_EntryMulSubOne
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistsUniformizerNonarchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGlNonarchimedeanStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsOpenStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupIsCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupsNeighborhoodBasisStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceSubgroupNormalInMaximalCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosetsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MatrixNearIdentityInCongruenceSubgroupStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_NearIdentityUpperLowerFactorizationStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesUpperCongruenceStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantConjugationPreservesLowerCongruenceStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DominantMonoidElementsAreAntitonePowersStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AntitonePowersInDominantMonoidStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGL
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_dPow_add
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_mem_congK
import Theorems.Thm_GlobalTheory_T_antitone_powers_in_dominant_monoid
import Theorems.Thm_GlobalTheory_T_cartan_decomposition_gl_nonarchimedean
import Theorems.Thm_GlobalTheory_T_compact_subgroup_finite_open_cosets
import Theorems.Thm_GlobalTheory_T_congruence_subgroup_is_compact
import Theorems.Thm_GlobalTheory_T_congruence_subgroup_is_open
import Theorems.Thm_GlobalTheory_T_congruence_subgroup_normal_in_maximal_compact
import Theorems.Thm_GlobalTheory_T_congruence_subgroups_neighborhood_basis
import Theorems.Thm_GlobalTheory_T_dominant_conjugation_preserves_lower_congruence
import Theorems.Thm_GlobalTheory_T_dominant_conjugation_preserves_upper_congruence
import Theorems.Thm_GlobalTheory_T_dominant_monoid_elements_are_antitone_powers
import Theorems.Thm_GlobalTheory_T_exists_uniformizer_nonarchimedean
import Theorems.Thm_GlobalTheory_T_matrix_near_identity_in_congruence_subgroup
import Theorems.Thm_GlobalTheory_T_near_identity_upper_lower_factorization


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CartGL
namespace GlobalTheory.CompanionTheory.CartGL
theorem _root_.solution : StCartanGL := by
  unfold CompanionTheory.Rg.Fl.StCartanGL CompanionTheory.Rg.Fl.HasCartan
  intro L _ _ _ n U hU
  obtain ⟨p, hp⟩ := GlobalTheory.T.exists_uniformizer_nonarchimedean L
  have hp1 : ‖(p : L)‖ < 1 := by
    unfold GlobalTheory.CompanionTheory.CartGL.IsUnif at hp
    exact hp.1
  obtain ⟨ε, hε, hεU⟩ := GlobalTheory.T.congruence_subgroups_neighborhood_basis L n (U : Set (GL (Fin n) L)) hU U.one_mem
  obtain ⟨r, hr0, hr1, hrε⟩ : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ r ≤ ε :=
    ⟨min ε (1 / 2), lt_min hε (by norm_num), lt_of_le_of_lt (min_le_right _ _) (by norm_num), min_le_left _ _⟩
  have h0 : 0 ≤ r := hr0.le
  have h1 : r ≤ 1 := hr1.le
  refine ⟨GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, fun x hx => hεU r h0 h1 hrε hx,
    GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0, GlobalTheory.T.congruence_subgroup_is_compact L n r h0 h1, ?_⟩
  obtain ⟨d, c, hc, hcK⟩ := GlobalTheory.T.compact_subgroup_finite_open_cosets (GL (Fin n) L) (GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) (GlobalTheory.T.congruence_subgroup_is_compact L n 1 zero_le_one le_rfl) (GlobalTheory.T.congruence_subgroup_is_open L n r h0 h1 hr0)
  refine ⟨d, n + 2, ?_⟩
  unfold CompanionTheory.Rg.Fl.IsCartan
  refine ⟨c, GlobalTheory.CompanionTheory.CartGL.tGen p, ?_, ?_, ?_, ?_⟩
  · intro i k
    constructor
    · intro hk
      exact GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i) k (hc i) hk
    · intro hk
      have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c i)⁻¹ _ (Subgroup.inv_mem _ (hc i)) hk
      have e : (c i)⁻¹ * (c i * k * (c i)⁻¹) * (c i)⁻¹⁻¹ = k := by group
      rwa [e] at h2
  · intro i j
    show GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) =
      GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n j) * GlobalTheory.CompanionTheory.CartGL.dPow p (GlobalTheory.CompanionTheory.CartGL.tExp n i)
    rw [← GlobalTheory.CompanionTheory.CartGL.dPow_add, ← GlobalTheory.CompanionTheory.CartGL.dPow_add, add_comm]
  · intro g
    obtain ⟨a, ha, k₁, hk₁, k₂, hk₂, rfl⟩ := GlobalTheory.T.cartan_decomposition_gl_nonarchimedean L n p hp g
    obtain ⟨i, κ₁, hκ₁, rfl⟩ := hcK k₁ hk₁
    obtain ⟨j, κ₂, hκ₂, rfl⟩ := hcK k₂ hk₂
    refine ⟨i, j, GlobalTheory.CompanionTheory.CartGL.dPow p a, GlobalTheory.T.antitone_powers_in_dominant_monoid L n p a ha, κ₁, hκ₁, (c j)⁻¹ * κ₂ * c j, ?_, ?_⟩
    · have h2 := GlobalTheory.T.congruence_subgroup_normal_in_maximal_compact L n r h0 h1 (c j)⁻¹ κ₂ (Subgroup.inv_mem _ (hc j)) hκ₂
      rwa [inv_inv] at h2
    · group
  · intro s hs s' hs' k hk
    obtain ⟨a₁, ha₁, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s hs
    obtain ⟨a₂, ha₂, rfl⟩ := GlobalTheory.T.dominant_monoid_elements_are_antitone_powers L n p s' hs'
    have hkA : ∀ i j, ‖((k : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := fun i j =>
      (GlobalTheory.CompanionTheory.CartGL.mem_congK.mp hk i j).1
    obtain ⟨Um, Wm, hUl, hWu, hUr, hWr, hUW⟩ := GlobalTheory.T.near_identity_upper_lower_factorization L n r h0 hr1 (k : Matrix (Fin n) (Fin n) L) hkA
    obtain ⟨kU, -, hkUv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Um hUr
    obtain ⟨kW, -, hkWv⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 Wm hWr
    have hk_eq : k = kU * kW := Units.ext (by rw [Units.val_mul, hkUv, hkWv, hUW])
    have hA : GlobalTheory.CompanionTheory.CartGL.dPow p a₁ * kU * (GlobalTheory.CompanionTheory.CartGL.dPow p a₁)⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_upper_congruence L n p hp1 a₁ ha₁ r kU (fun i j hij => by rw [hkUv]; exact hUl i j hij)
        (fun i j => by rw [hkUv]; exact hUr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    have hB : (GlobalTheory.CompanionTheory.CartGL.dPow p a₂)⁻¹ * kW * GlobalTheory.CompanionTheory.CartGL.dPow p a₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
      have hb := GlobalTheory.T.dominant_conjugation_preserves_lower_congruence L n p hp1 a₂ ha₂ r kW (fun i j hij => by rw [hkWv]; exact hWu i j hij)
        (fun i j => by rw [hkWv]; exact hWr i j)
      obtain ⟨k', hk', hk'v⟩ := GlobalTheory.T.matrix_near_identity_in_congruence_subgroup L n r h0 h1 hr1 _ hb
      rw [← Units.ext hk'v]
      exact hk'
    refine ⟨_, hA, _, hB, ?_⟩
    rw [hk_eq]
    group
end GlobalTheory.CompanionTheory.CartGL
