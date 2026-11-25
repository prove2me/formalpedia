-- Prove2me | solution 1 for GlobalTheory.NAK.lintegral_eq_nak
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:02:38.533222+00:00
-- url     : https://prove2.me/submissions/8e6dd756-b17d-46d9-9ad7-641a28b86e71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HaarSK
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PSemidirectHaar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HaarMeasureIwasawaQuotient
import Theorems.Thm_GlobalTheory_NAK_map_mul_right_eq_of_mem_compact
import Theorems.Thm_GlobalTheory_NAK_exists_eq_smul_map_mulMap_of_right
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_equivOfIsometry_apply
import Theorems.Thm_GroundTheory_Automorphic_HermitianForm_restrict_apply
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_finiteAdeleUnitaryEquiv_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_SemidirectHaar_proof_026c949566ef
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.HermitianForm.equivOfIsometry_apply
attribute [local simp] GroundTheory.Automorphic.HermitianForm.restrict_apply
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.finiteAdeleUnitaryEquiv_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
open MeasureTheory Measure Topology Set Function TopologicalSpace GroundTheory.Automorphic.HaarSK
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.NAK
namespace GlobalTheory.NAK
theorem _root_.solution : ∀ (G Λ : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [Group Λ] [TopologicalSpace Λ] [IsTopologicalGroup Λ] [LocallyCompactSpace Λ]
    [SecondCountableTopology Λ] [T2Space Λ] [MeasurableSpace Λ] [BorelSpace Λ]
    (N K : Subgroup G) (j : Λ →* G) (δ : Λ →* ℝ≥0) (μG : Measure G) (μN : Measure N) (μK : Measure K) (μΛ : Measure Λ),
    μG.IsHaarMeasure → μN.IsHaarMeasure → μK.IsHaarMeasure → μΛ.IsHaarMeasure →
    IsCompact (K : Set G) → Continuous j → Continuous δ →
    (∀ x, ∀ n ∈ N, j x * n * (j x)⁻¹ ∈ N) →
    IsClosedEmbedding (fun p : N × Λ => (p.1 : G) * j p.2) →
    (∀ x (f : G → ℝ≥0∞), Measurable f → ∫⁻ n, f (j x * n.1 * (j x)⁻¹) ∂μN = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ * ∫⁻ n, f n.1 ∂μN) →
    (∀ g, ∃ n ∈ N, ∃ x, ∃ k ∈ K, g = n * j x * k) →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ g, φ g ∂μG = c * ∫⁻ k, ∫⁻ x, ∫⁻ n, φ (n.1 * j x * k.1) * ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ ∂μN ∂μΛ ∂μK := by
  intro G Λ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ N K j δ μG μN μK μΛ hG hN hK hΛ hKc hj hδ hconj hemb hmod hdec
  classical
  set f : N × Λ → G := fun p => (p.1 : G) * j p.2 with hf

  let P : Subgroup G :=
    { carrier := Set.range f
      mul_mem' := by
        rintro _ _ ⟨⟨n, x⟩, rfl⟩ ⟨⟨n', x'⟩, rfl⟩
        refine ⟨(⟨(n : G) * (j x * n' * (j x)⁻¹), N.mul_mem n.2 (hconj x n' n'.2)⟩, x * x'), ?_⟩
        simp only [hf, map_mul]
        group
      one_mem' := ⟨(1, 1), by simp [hf]⟩
      inv_mem' := by
        rintro _ ⟨⟨n, x⟩, rfl⟩
        refine ⟨(⟨j x⁻¹ * (n : G)⁻¹ * (j x⁻¹)⁻¹, hconj x⁻¹ _ (N.inv_mem n.2)⟩, x⁻¹), ?_⟩
        simp only [hf, map_inv]
        group }
  have hmemP : ∀ g, g ∈ P ↔ g ∈ Set.range f := fun g => Iff.rfl
  have hPc : IsClosed (P : Set G) := hemb.isClosed_range
  have hNc : IsClosed (N : Set G) := by
    have h := hemb.isClosedMap _ (isClosed_univ.prod (isClosed_singleton (x := (1 : Λ))))
    convert h using 1
    ext g
    constructor
    · intro hg
      exact ⟨(⟨g, hg⟩, 1), ⟨trivial, rfl⟩, by simp [hf]⟩
    · rintro ⟨⟨n, x⟩, ⟨-, hx⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      simp [hf]
  have hNP : N ≤ P := fun n hn => (hmemP n).2 ⟨(⟨n, hn⟩, 1), by simp [hf]⟩
  have hjP : ∀ x, j x ∈ P := fun x => (hmemP _).2 ⟨(1, x), by simp [hf]⟩

  let e : N × Λ ≃ₜ Set.range f := hemb.isEmbedding.toHomeomorph
  have he : ∀ q : Set.range f, f (e.symm q) = q := fun q => congrArg Subtype.val (e.apply_symm_apply q)
  let β : P → Λ := fun p => (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).2
  have hβc : Continuous β :=
    continuous_snd.comp (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
  have hβ : ∀ p : P, (p : G) * (j (β p))⁻¹ ∈ N := by
    intro p
    have h1 : f (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩) = p := he _
    have h2 : (p : G) * (j (β p))⁻¹ = ((e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).1 : G) := by
      conv_lhs => rw [← h1]
      simp [hf, β]
    rw [h2]
    exact (e.symm ⟨p.1, (hmemP p.1).1 p.2⟩).1.2
  have hτH : ∀ t, j t ∈ N → t = 1 := by
    intro t ht
    have := hemb.injective (show f (⟨j t, ht⟩, 1) = f (1, t) by simp [hf])
    exact (congrArg Prod.snd this).symm

  have hδmul : ∀ x, δ x * δ x⁻¹ = 1 := fun x => by rw [← map_mul, mul_inv_cancel, map_one]
  have hδ0 : ∀ x, δ x ≠ 0 := fun x h => by simpa [h] using hδmul x
  have hδinv : ∀ x, (δ x)⁻¹ = δ x⁻¹ := fun x => inv_eq_of_mul_eq_one_right (hδmul x)
  set δF : Λ → ℝ≥0 := fun x => δ x⁻¹ with hδF
  have hδFc : Continuous δF := hδ.comp continuous_inv
  have hδF' : ∀ x, ((δF x : ℝ≥0) : ℝ≥0∞) = ((δ x : ℝ≥0) : ℝ≥0∞)⁻¹ := fun x => by
    rw [hδF]
    dsimp only
    rw [← hδinv, ENNReal.coe_inv (hδ0 x)]
  have hmodF : ∀ (t : Λ) (g : G → ℝ≥0∞), Measurable g →
      ∫⁻ x, g (j t * x * (j t)⁻¹) ∂μN = δF t * ∫⁻ x, g x ∂μN := fun t g hg => by
    rw [hmod t g hg, hδF']

  haveI : LocallyCompactSpace P := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace N := hNc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology P := inferInstanceAs (SecondCountableTopology (P : Set G))
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  let μP : Measure P := Measure.haar
  obtain ⟨c1, hc1, hP⟩ := GroundTheory.Heights₂.Heights.FiniteCovolume.SemidirectHaar.proof G Λ P N hPc hNc hNP j β δF
    hj hβc hδFc hjP hconj hτH hβ μP μN μΛ hmodF

  have hright : ∀ k ∈ K, μG.map (· * k) = μG := fun k hk =>
    map_mul_right_eq_of_mem_compact μG K hKc k hk
  have hsurj : Surjective (mulMap P K) := by
    intro g
    obtain ⟨n, hn, x, k, hk, rfl⟩ := hdec g
    exact ⟨(⟨(n : G) * j x, (hmemP _).2 ⟨(⟨n, hn⟩, x), rfl⟩⟩, ⟨k, hk⟩), rfl⟩
  obtain ⟨c2, hc2⟩ := exists_eq_smul_map_mulMap_of_right P K μG hright hPc hKc hsurj μP μK
  have hc2ne : c2 ≠ 0 := by
    rintro rfl
    have h0 := (isOpen_univ (X := G)).measure_pos μG univ_nonempty
    rw [hc2] at h0
    simp at h0
  refine ⟨(c2 : ℝ≥0∞) * c1, mul_ne_zero (by exact_mod_cast hc2ne) (by exact_mod_cast hc1),
    ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top, ?_⟩
  intro φ hφ
  have hm : Measurable (mulMap P K) :=
    (measurable_subtype_coe.comp measurable_fst).mul (measurable_subtype_coe.comp measurable_snd)
  rw [hc2, lintegral_smul_measure, lintegral_map hφ hm, lintegral_prod_symm (fun q => φ (mulMap P K q)) (hφ.comp hm).aemeasurable,
    ENNReal.smul_def, smul_eq_mul, mul_assoc]
  congr 1
  rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  refine lintegral_congr fun k => ?_
  have h := hP (fun g => φ (g * k)) (hφ.comp (measurable_mul_const _))
  show ∫⁻ p, φ ((p : G) * k) ∂μP = _
  rw [h]
  congr 1
  refine lintegral_congr fun t => ?_
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hδ0 t)), hδF', mul_comm]
end GlobalTheory.NAK
