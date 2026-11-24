-- Prove2me | solution 1 for GlobalTheory.Cyc.AlmostTrace.exists_finite_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:34.386668+00:00
-- url     : https://prove2.me/submissions/56ba843c-e11e-47c0-982d-a52813f117fb

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_Hinf_le_Gj
import Theorems.Thm_GlobalTheory_Cyc_AlmostTrace_exists_Gj_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.AlmostTrace
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.Cyc.AlmostTrace
theorem _root_.solution (K : FinExt l) (L : IntermediateField ℚ_[l] (Om l)) (S : Finset (GQ l))
    (hS : ∀ s ∈ S, s ∈ Hinf K)
    (hrep : ∀ h ∈ Hinf K, ∃! s, s ∈ S ∧ s⁻¹ * h ∈ L.fixingSubgroup) :
    ∃ L' : FinExt l, L'.1 ≤ L ∧ ∃ i₀, ∀ i ≥ i₀, ∀ h ∈ Gj K i,
      ∃! s, s ∈ S ∧ s⁻¹ * h ∈ (L'.1 ⊔ Ks K i).fixingSubgroup := by
  classical
  have hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → ∃ x ∈ L, (s⁻¹ * t) x ≠ x := by
    intro s hs t ht hst
    by_contra hne
    push Not at hne
    apply hst
    have hmem : s⁻¹ * t ∈ L.fixingSubgroup := (IntermediateField.mem_fixingSubgroup_iff _ _).2 hne
    exact (hrep t (hS t ht)).unique ⟨hs, hmem⟩ ⟨ht, by rw [inv_mul_cancel]; exact one_mem _⟩
  choose! xf hxL hxne using hsep
  let T : Finset (Om l) := ((S ×ˢ S).filter fun p => p.1 ≠ p.2).image fun p => xf p.1 p.2
  have hTmem : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → xf s t ∈ (T : Set (Om l)) := by
    intro s hs t ht hst
    simp only [T, Finset.coe_image, Finset.coe_filter]
    exact ⟨(s, t), ⟨Finset.mem_product.2 ⟨hs, ht⟩, hst⟩, rfl⟩
  let L' : FinExt l := ⟨IntermediateField.adjoin ℚ_[l] (T : Set (Om l)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  have hL'L : L'.1 ≤ L := by
    show IntermediateField.adjoin ℚ_[l] (T : Set (Om l)) ≤ L
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    simp only [T, Finset.coe_image, Finset.coe_filter, Set.mem_image] at hx
    obtain ⟨p, ⟨hp, hpne⟩, rfl⟩ := hx
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
    exact hxL p.1 hp1 p.2 hp2 hpne
  have : FiniteDimensional ℚ_[l] L'.1 := L'.2
  let U : Set (GQ l) := ⋃ s ∈ S, {σ | s⁻¹ * σ ∈ L'.1.fixingSubgroup}
  have hUo : IsOpen U := isOpen_biUnion fun s _ =>
    (IntermediateField.fixingSubgroup_isOpen L'.1).preimage (continuous_const.mul continuous_id)
  have hHU : (Hinf K : Set (GQ l)) ⊆ U := by
    intro σ hσ
    obtain ⟨s, ⟨hs, hsm⟩, -⟩ := hrep σ hσ
    exact Set.mem_biUnion hs (IntermediateField.fixingSubgroup_antitone hL'L hsm)
  obtain ⟨i₀, hi₀⟩ := exists_Gj_subset K hUo hHU
  refine ⟨L', hL'L, i₀, fun i hi h hh => ?_⟩
  obtain ⟨s, hs, hsm⟩ := Set.mem_iUnion₂.1 (hi₀ i hi hh)
  have hsG : s⁻¹ * h ∈ Gj K i := mul_mem (inv_mem (Hinf_le_Gj K i (hS s hs))) hh
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hsm, hsG⟩
  · rintro t ⟨ht, htm⟩
    by_contra hts
    have htm' : t⁻¹ * h ∈ L'.1.fixingSubgroup :=
      IntermediateField.fixingSubgroup_antitone le_sup_left htm
    have hm : t⁻¹ * s ∈ L'.1.fixingSubgroup := by
      have := mul_mem htm' (inv_mem hsm)
      rwa [show t⁻¹ * h * (s⁻¹ * h)⁻¹ = t⁻¹ * s by group] at this
    have hxT : xf t s ∈ L'.1 := IntermediateField.subset_adjoin _ _ (hTmem t ht s hs hts)
    exact hxne t ht s hs hts ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hm _ hxT)
end GlobalTheory.Cyc.AlmostTrace
