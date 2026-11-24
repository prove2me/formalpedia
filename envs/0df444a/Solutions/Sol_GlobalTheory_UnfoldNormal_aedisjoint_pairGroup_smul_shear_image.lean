-- Prove2me | solution 1 for GlobalTheory.UnfoldNormal.aedisjoint_pairGroup_smul_shear_image
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:11:37.385669+00:00
-- url     : https://prove2.me/submissions/65b7df29-1816-4ec6-88a4-a8de67f67bab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NullMeasurableSetShearImage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_AedisjointPairGroupSmulShearedDomain
import Theorems.Thm_GlobalTheory_UnfoldNormal_measurableEmbedding_shear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Function
open scoped Pointwise
open GlobalTheory GlobalTheory.UnfoldNormal
namespace GlobalTheory.UnfoldNormal
theorem _root_.solution : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H], ∀ (ν : Measure H) [ν.IsHaarMeasure] (Γ N : Subgroup H), Countable Γ → IsClosed (N : Set H) → ∀ (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) (κ : Measure N) (𝓝 : Set N), κ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓝 κ → (∀ (γ : H) (hγ : γ ∈ Γ), κ.map (fun n : N => (⟨γ * n * γ⁻¹, hN γ hγ n n.2⟩ : N)) = κ) → ∀ 𝓕 : Set H, IsFundamentalDomain Γ 𝓕 ν → Pairwise (AEDisjoint ((κ.prod ν).map (GlobalTheory.UnfoldNormal.shear N)) on fun g : GlobalTheory.UnfoldNormal.pairGroup Γ N hN => g • (GlobalTheory.UnfoldNormal.shear N '' (𝓝 ×ˢ 𝓕))) := by
  intro H _ _ _ _ _ _ _ _ ν _ Γ N _ hNc hN κ 𝓝 _ h𝓝 hconj 𝓕 h𝓕
  have key : ∀ (g : pairGroup Γ N hN) (x : N × H), shear N x ∈ g • (shear N '' (𝓝 ×ˢ 𝓕)) →
      ∃ n ∈ 𝓝, ∃ h ∈ 𝓕, (x.1 : H) * x.2 = g.1.1 * n * h ∧ x.2 = g.1.2 * h := by
    rintro g ⟨a, b⟩ hx
    obtain ⟨_, ⟨⟨n, h⟩, ⟨hn, hh⟩, rfl⟩, he⟩ := Set.mem_smul_set.1 hx
    refine ⟨n, hn, h, hh, ?_⟩
    have := Prod.ext_iff.1 he
    simp only [Subgroup.smul_def, shear, smul_eq_mul, Prod.fst_mul, Prod.snd_mul] at this
    exact ⟨by rw [← this.1, mul_assoc], this.2.symm⟩
  rintro ⟨⟨u, v⟩, hg⟩ ⟨⟨u', v'⟩, hg'⟩ hne
  obtain ⟨hu, hv, huv⟩ := hg
  obtain ⟨hu', hv', huv'⟩ := hg'
  change ((κ.prod ν).map (shear N)) (_ ∩ _) = 0
  rw [(measurableEmbedding_shear hNc).map_apply]
  by_cases hvv : v = v'
  · subst hvv
    have huu : u ≠ u' := by
      rintro rfl
      exact hne rfl
    have memN : ∀ w, w ∈ Γ → w * v⁻¹ ∈ N → v⁻¹ * w ∈ N := by
      intro w _ hw
      have := hN v⁻¹ (Γ.inv_mem hv) (w * v⁻¹) hw
      have e : v⁻¹ * (w * v⁻¹) * v⁻¹⁻¹ = v⁻¹ * w := by group
      rwa [e] at this
    let δ : Γ.subgroupOf N := ⟨⟨v⁻¹ * u, memN u hu huv⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu)⟩
    let δ' : Γ.subgroupOf N := ⟨⟨v⁻¹ * u', memN u' hu' huv'⟩, Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.inv_mem hv) hu')⟩
    have hδ : δ ≠ δ' := by
      intro h
      have := congrArg (fun d : Γ.subgroupOf N => ((d : N) : H)) h
      simp only [δ, δ', mul_right_inj] at this
      exact huu this
    have hW : κ (δ • 𝓝 ∩ δ' • 𝓝) = 0 := h𝓝.aedisjoint hδ
    let c : N → N := fun n : N => (⟨v⁻¹ * n * v⁻¹⁻¹, hN v⁻¹ (Γ.inv_mem hv) n n.2⟩ : N)
    have hc : Continuous c :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    have hcW : κ (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) = 0 := by
      have h1 := Measure.le_map_apply hc.measurable.aemeasurable (μ := κ) (δ • 𝓝 ∩ δ' • 𝓝)
      have h2 : κ.map c = κ := hconj v⁻¹ (Γ.inv_mem hv)
      rw [h2, hW] at h1
      exact le_antisymm h1 bot_le
    refine measure_mono_null (t := (c ⁻¹' (δ • 𝓝 ∩ δ' • 𝓝)) ×ˢ Set.univ) ?_ ?_
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨n, hn, h, hh, e1, e2⟩ := key _ _ h1
      obtain ⟨n', hn', h', hh', e1', e2'⟩ := key _ _ h2
      have av : ∀ (w : H) (m : N) (k : H), (a : H) * b = w * m * k → b = v * k → (a : H) * v = w * m := by
        intro w m k e e'
        rw [e'] at e
        have := congrArg (· * k⁻¹) e
        simpa [mul_assoc] using this
      refine ⟨⟨Set.mem_smul_set.2 ⟨n, hn, ?_⟩, Set.mem_smul_set.2 ⟨n', hn', ?_⟩⟩, Set.mem_univ _⟩
      · apply Subtype.ext
        show v⁻¹ * u * (n : H) = v⁻¹ * a * v⁻¹⁻¹
        rw [inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1 e2, mul_assoc]
      · apply Subtype.ext
        show v⁻¹ * u' * (n' : H) = v⁻¹ * a * v⁻¹⁻¹
        rw [inv_inv, mul_assoc v⁻¹ (a : H), av _ _ _ e1' e2', mul_assoc]
    · exact le_antisymm ((Measure.prod_prod_le _ _).trans (by rw [hcW, zero_mul])) bot_le
  · have hZ : ν ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕) = 0 :=
      h𝓕.aedisjoint (fun h => hvv (congrArg Subtype.val h))
    refine measure_mono_null (t := Set.univ ×ˢ ((⟨v, hv⟩ : Γ) • 𝓕 ∩ (⟨v', hv'⟩ : Γ) • 𝓕)) ?_ ?_
    · rintro ⟨a, b⟩ ⟨h1, h2⟩
      obtain ⟨n, hn, h, hh, e1, e2⟩ := key _ _ h1
      obtain ⟨n', hn', h', hh', e1', e2'⟩ := key _ _ h2
      exact ⟨Set.mem_univ _, Set.mem_smul_set.2 ⟨h, hh, by rw [e2]; rfl⟩,
        Set.mem_smul_set.2 ⟨h', hh', by rw [e2']; rfl⟩⟩
    · exact le_antisymm ((Measure.prod_prod_le _ _).trans (by rw [hZ, mul_zero])) bot_le
end GlobalTheory.UnfoldNormal
