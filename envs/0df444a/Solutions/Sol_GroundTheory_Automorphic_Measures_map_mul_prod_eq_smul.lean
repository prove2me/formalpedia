-- Prove2me | solution 1 for GroundTheory.Automorphic.Measures.map_mul_prod_eq_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:29:09.019518+00:00
-- url     : https://prove2.me/submissions/d3105438-705e-466d-b04f-57d57a34eacf

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresModulus
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresChart
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_Measures
import Theorems.Thm_GroundTheory_Automorphic_Measures_map_mul_right_eq_self_of_compactSpace
import Theorems.Thm_GroundTheory_Automorphic_Measures_isPiSystem_smallCosets
import Theorems.Thm_GroundTheory_Automorphic_Measures_borel_eq_generateFrom_smallCosets
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_exists_compactOpenSubgroup_normalized
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Measure Topology Filter Set ValuativeRel
open scoped NNReal ENNReal Pointwise
set_option linter.unusedSectionVars false
open GroundTheory.Automorphic.Measures
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (K : Subgroup G)
variable {K}
namespace GroundTheory.Automorphic.Measures
theorem _root_.solution [TotallyDisconnectedSpace G] (P K : Subgroup G)
    (hP : IsClosed (P : Set G))
    (hKo : IsOpen (K : Set G)) (hKc : IsCompact (K : Set G))
    (hPK : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k)
    (μG : Measure G) [μG.IsHaarMeasure] (μP : Measure P) [μP.IsHaarMeasure] (μK : Measure K)
    [μK.IsHaarMeasure] :
    μG K • map (fun x : P × K => (x.1 : G) * x.2) (μP.prod μK) =
      (μP (Subtype.val ⁻¹' (K : Set G)) * μK univ) • μG := by
  have hN : ∀ U ∈ 𝓝 (1 : G), ∃ N : Subgroup G, IsSmallNormal K N ∧ (N : Set G) ⊆ U := by
    intro U hU
    obtain ⟨N, -, hNU, hNK⟩ :=
      exists_compactOpenSubgroup_normalized hKc (inter_mem hU (hKo.mem_nhds K.one_mem))
    exact ⟨N, ⟨N.isOpen, fun x hx => (hNU hx).2, hNK⟩, fun x hx => (hNU hx).1⟩
  have : LocallyCompactSpace P := hP.locallyCompactSpace
  have : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
  have : SecondCountableTopology K := IsEmbedding.subtypeVal.secondCountableTopology
  have : BorelSpace P := Subtype.borelSpace (P : Set G)
  have : BorelSpace K := Subtype.borelSpace (K : Set G)
  set m : P × K → G := fun x => (x.1 : G) * x.2 with hm_def
  have hm : Measurable m :=
    (measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)
  set ν := map m (μP.prod μK) with hν
  have hleft : ∀ p : P, map ((p : G) * ·) ν = ν := by
    intro p
    rw [hν, map_map (continuous_const_mul _).measurable hm]
    have : ((p : G) * ·) ∘ m = m ∘ Prod.map (p * ·) id := by
      funext x
      simp [m, mul_assoc]
    rw [this, ← map_map hm ((continuous_const_mul p).measurable.prodMap measurable_id),
      ← map_prod_map _ _ (continuous_const_mul p).measurable measurable_id,
      map_mul_left_eq_self, Measure.map_id]
  have hright : ∀ k : K, map (· * (k : G)) ν = ν := by
    intro k
    rw [hν, map_map (continuous_mul_const _).measurable hm]
    have : (· * (k : G)) ∘ m = m ∘ Prod.map id (· * k) := by
      funext x
      simp [m, mul_assoc]
    rw [this, ← map_map hm (measurable_id.prodMap (continuous_mul_const k).measurable),
      ← map_prod_map _ _ measurable_id (continuous_mul_const k).measurable,
      map_mul_right_eq_self_of_compactSpace, Measure.map_id]
  have hνK : ν K = μP (Subtype.val ⁻¹' (K : Set G)) * μK univ := by
    rw [hν, map_apply hm hKo.measurableSet]
    have : m ⁻¹' (K : Set G) = (Subtype.val ⁻¹' (K : Set G)) ×ˢ (univ : Set K) := by
      ext ⟨p, k⟩
      simp only [Set.mem_preimage, SetLike.mem_coe, Set.mem_prod, Set.mem_univ, and_true, m]
      exact K.mul_mem_cancel_right k.2
    rw [this, prod_prod]
  have hPKc : IsCompact (Subtype.val ⁻¹' (K : Set G) : Set P) :=
    hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc
  have hνKfin : ν K ≠ ∞ := by
    rw [hνK]
    exact ENNReal.mul_ne_top hPKc.measure_lt_top.ne (measure_ne_top _ _)
  have hcoset : ∀ N, IsSmallNormal K N → ∀ x : G, ν (x • (N : Set G)) = ν N := by
    intro N hN x
    obtain ⟨p, hp, k, hk, rfl⟩ := hPK x
    have h1 : ν ((p * k) • (N : Set G)) = ν (k • (N : Set G)) := by
      have := congrArg (fun μ : Measure G => μ ((p * k) • (N : Set G))) (hleft ⟨p, hp⟩)
      simp only at this
      rw [map_apply (continuous_const_mul _).measurable (hN.1.smul _).measurableSet] at this
      rw [← this]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
      rw [show (p * k)⁻¹ * (p * y) = k⁻¹ * y by group]
    have h2 : ν (k • (N : Set G)) = ν N := by
      have := congrArg (fun μ : Measure G => μ N) (hright ⟨k⁻¹, K.inv_mem hk⟩)
      simp only at this
      rw [map_apply (continuous_mul_const _).measurable hN.1.measurableSet] at this
      rw [← this]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul,
        SetLike.mem_coe]
      constructor
      · intro h
        have := hN.2.2 k hk _ h
        simpa [mul_assoc] using this
      · intro h
        have := hN.2.2 k⁻¹ (K.inv_mem hk) _ h
        simpa [mul_assoc] using this
    rw [h1, h2]
  have hfin : ∀ N, IsSmallNormal K N → ∀ x : G, ν (x • (N : Set G)) ≠ ∞ := fun N hN x => by
    rw [hcoset N hN x]
    exact ne_top_of_le_ne_top hνKfin (measure_mono hN.2.1)
  have hKsmall : IsSmallNormal K K :=
    ⟨hKo, le_rfl, fun k hk y hy => K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℕ → G, ⋃ i, B i • (K : Set G) = univ := by
    obtain ⟨T, hTc, hT⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun x : G => x • (K : Set G)) fun x => hKo.smul x
    have hU : ⋃ x : G, x • (K : Set G) = univ :=
      eq_univ_of_forall fun y => mem_iUnion.2 ⟨y, ⟨1, K.one_mem, mul_one y⟩⟩
    have hTne : T.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h, hU] at hT
      exact Set.empty_ne_univ (by simpa using hT)
    obtain ⟨f, rfl⟩ := hTc.exists_eq_range hTne
    refine ⟨f, ?_⟩
    rw [← hU, ← hT, Set.biUnion_range]
  have hpre : ∀ (g x : G) (S : Set G), ((g * ·) ⁻¹' (x • S)) = (g⁻¹ * x) • S := by
    intro g x S
    ext y
    simp only [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul]
    rw [show x⁻¹ * (g * y) = (g⁻¹ * x)⁻¹ * y by group]
  have hinv : ν.IsMulLeftInvariant := ⟨fun g => by
    refine ext_of_generateFrom_of_iUnion (smallCosets K) (fun i => B i • (K : Set G))
      (borel_eq_generateFrom_smallCosets hN) (isPiSystem_smallCosets K) hB
      (fun i => ⟨B i, K, hKsmall, rfl⟩) (fun i => ?_) ?_
    · rw [map_apply (continuous_const_mul g).measurable (hKo.smul _).measurableSet, hpre]
      exact hfin K hKsmall _
    · rintro _ ⟨x, N, hN', rfl⟩
      rw [map_apply (continuous_const_mul g).measurable (hN'.1.smul _).measurableSet, hpre,
        hcoset N hN', hcoset N hN']⟩
  have hfc : IsFiniteMeasureOnCompacts ν := ⟨fun C hC => by
    obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun x : G => x • (K : Set G))
      (fun x => hKo.smul x) fun y _ => mem_iUnion.2 ⟨y, ⟨1, K.one_mem, mul_one y⟩⟩
    calc ν C ≤ ν (⋃ x ∈ t, x • (K : Set G)) := measure_mono ht
      _ ≤ ∑ x ∈ t, ν (x • (K : Set G)) := measure_biUnion_finset_le _ _
      _ < ∞ := ENNReal.sum_lt_top.2 fun x _ => (hfin K hKsmall x).lt_top⟩
  have e := isMulLeftInvariant_eq_smul ν μG
  rw [← hνK, e]
  ext s hs
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  ring
end GroundTheory.Automorphic.Measures
