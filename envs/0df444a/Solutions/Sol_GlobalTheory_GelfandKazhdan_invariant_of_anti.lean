-- Prove2me | solution 1 for GlobalTheory.GelfandKazhdan.invariant_of_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:35:08.448529+00:00
-- url     : https://prove2.me/submissions/053817bd-3333-4b6b-b9df-06d22ec25c3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SchwartzBruhatDistributionEqZeroBaireStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_MatrixConjTransposeBySymmetricTausskyZassenhausStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_TransposeInvariantOfConjInvariantDistributionGL
import Theorems.Thm_GlobalTheory_GelfandKazhdan_anti_inv
import Theorems.Thm_GlobalTheory_GelfandKazhdan_exists_stable
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_T_schwartzBruhat_distribution_eq_zero_baire


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
noncomputable section
open GlobalTheory GlobalTheory.GelfandKazhdan
variable {G : Type} [Group G] [TopologicalSpace G]
namespace GlobalTheory.GelfandKazhdan
theorem _root_.solution [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (t : G ≃ₜ G) (hm : ∀ x y, t (x * y) = t y * t x)
    (ht : ∀ x, t (t x) = x) (K₀ : Subgroup G) (hKo : IsOpen (K₀ : Set G))
    (hKc : IsCompact (K₀ : Set G)) (hK : ∀ x ∈ K₀, t x ∈ K₀)
    (hb : ∀ U ∈ 𝓝 (1 : G), ∃ J : Subgroup G, IsOpen (J : Set G) ∧
      (J : Set G) ⊆ U ∧ J ≤ K₀ ∧ ∀ x ∈ K₀, ∀ j ∈ J, x * j * x⁻¹ ∈ J)
    (hs : ∀ x, ∃ s, t s = s ∧ s * x = t x * s) (T : SB G →ₗ[ℂ] ℂ)
    (hT : ∀ (g : G) (φ ψ : SB G), (∀ x, ψ.1 x = φ.1 (g * x * g⁻¹)) → T ψ = T φ) (φ : SB G) :
    T (pull t φ) = T φ := by
  obtain ⟨U, hU⟩ := (𝓝 (1 : G)).exists_antitone_basis
  choose J hJo hJU hJK hJn hJt using fun m =>
    exists_stable t hm ht K₀ hK hb (U m) (hU.1.mem_of_mem trivial)
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable S := hSc.to_subtype
  let K : S → ℕ → Subgroup G := fun c m => J m ⊓ (J m).comap (MulAut.conj (c : G)).toMonoidHom
  have hKm : ∀ c m y, y ∈ K c m ↔ y ∈ J m ∧ (c : G) * y * (c : G)⁻¹ ∈ J m := fun c m y => Iff.rfl
  have hD : T - T.comp (pull t) = 0 := by
    refine GlobalTheory.T.schwartzBruhat_distribution_eq_zero_baire G S K (fun c m => ?_) (fun c V hV => ?_) _ fun x => ?_
    · have ho : IsOpen (K c m : Set G) :=
        (hJo m).inter ((hJo m).preimage (f := fun y => (c : G) * y * (c : G)⁻¹) (by fun_prop))
      exact ⟨ho, hKc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun y hy => hJK m hy.1⟩
    · obtain ⟨m, -, hm⟩ := hU.1.mem_iff.1 hV
      exact ⟨m, fun y hy => hm (hJU m hy.1)⟩
    · obtain ⟨s, hts, hsx⟩ := hs x
      obtain ⟨c, hc, hcS⟩ := hSd.inter_open_nonempty _
        (hKo.preimage (f := fun y => y * s⁻¹) (by fun_prop)) ⟨s, by simp⟩
      have hc' : c * s⁻¹ ∈ K₀ := hc
      refine ⟨⟨c, hcS⟩, fun m ψ hψ => ?_⟩
      have hK' : ∀ y, y ∈ K ⟨c, hcS⟩ m ↔ y ∈ J m ∧ s * y * s⁻¹ ∈ J m := fun y => by
        rw [hKm]
        refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
        · have := hJn m _ (inv_mem hc') _ h
          convert this using 1
          simp only []
          group
        · have := hJn m _ hc' _ h
          convert this using 1
          simp only []
          group
      have hτ : ∀ y, t (s * y * s⁻¹) = s⁻¹ * t y * s := fun y => by
        rw [hm, hm, anti_inv hm, hts, mul_assoc]
      have hτK : ∀ y ∈ K ⟨c, hcS⟩ m, s⁻¹ * t y * s ∈ K ⟨c, hcS⟩ m := fun y hy => by
        rw [hK'] at hy ⊢
        refine ⟨hτ y ▸ hJt m _ hy.2, ?_⟩
        convert hJt m _ hy.1 using 1
        group
      have h1 : ∀ y, y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} →
          s⁻¹ * t y * s ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b} := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨_, hτK b hb, _, hτK a ha, ?_⟩
        have : t x = s * x * s⁻¹ := by rw [hsx]; group
        rw [hm, hm, this]
        group
      have h2 : ∀ y, s⁻¹ * t (s⁻¹ * t y * s) * s = y := fun y => by
        rw [hm, hm, anti_inv hm, hts, ht]
        group
      have h3 : T ψ = T (pull t ψ) := hT s _ _ fun y => by
        show ψ.1 y = ψ.1 (t (s * y * s⁻¹))
        rw [hτ, hψ]
        by_cases hy : y ∈ {g : G | ∃ a ∈ K ⟨c, hcS⟩ m, ∃ b ∈ K ⟨c, hcS⟩ m, g = a * x * b}
        · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (h1 y hy)]
        · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem fun h => hy (h2 y ▸ h1 _ h)]
      exact sub_eq_zero.2 h3
  exact (sub_eq_zero.1 (LinearMap.congr_fun hD φ)).symm
end GlobalTheory.GelfandKazhdan
