-- Prove2me | solution 1 for GlobalTheory.Mass.ShortVector.exists_gen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:51.633515+00:00
-- url     : https://prove2.me/submissions/e9bde437-2f52-4e49-b016-fd737b0b9b99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_DiscreteSeriesUnitary__MaxMass_96db7412d6455637
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RegulatorLeSumSmallIdealsInClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsShortVectorIntegralHermitianLatticeRankOne
import Theorems.Thm_GlobalTheory_Mass_ShortVector_idxN_span
import Theorems.Thm_GlobalTheory_Mass_ShortVector_span_isLattice
import Theorems.Thm_Formalism_HermitianLatticesTheory_dualBasic_mem_dual
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_dual
import Theorems.Thm_GlobalTheory_Mass_DiscOrder_idxN_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
namespace GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
private theorem apply_self_ne_zero_and_span_of_finrank_one [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hn : h.Nondegenerate) (h1 : Module.finrank K V = 1) {m : V} (hm : m ≠ 0) :
    h m m ≠ 0 ∧ ∀ y : V, ∃ c : K, c • m = y := by
  have hsp : Submodule.span K {m} = ⊤ := (finrank_eq_one_iff_of_nonzero m hm).mp h1
  have hy : ∀ y : V, ∃ c : K, c • m = y := fun y =>
    Submodule.mem_span_singleton.mp (hsp ▸ Submodule.mem_top)
  refine ⟨fun h0 => hm (hn.1 m fun y => ?_), hy⟩
  obtain ⟨c, rfl⟩ := hy y
  rw [LinearMap.map_smul, h0, smul_zero]
private theorem exists_integer_eq_conj (s : 𝓞 K) :
    ∃ t : 𝓞 K, algebraMap (𝓞 K) K t = starRingEnd K (algebraMap (𝓞 K) K s) :=
  ⟨⟨starRingEnd K (algebraMap (𝓞 K) K s),
    (RingOfIntegers.isIntegral_coe s).map (starRingEnd K).toIntAlgHom⟩, rfl⟩
private theorem smul_mem_dual_span_of_mul_apply_self_integral (h : V →ₗ⋆[K] V →ₗ[K] K) (x : V) (c : K) (t : 𝓞 K)
    (ht : algebraMap (𝓞 K) K t = c * h x x) :
    c • x ∈ dual h (Submodule.span (𝓞 K) {x}) := by
  rw [dualBasic_mem_dual]
  intro y hy
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hy
  obtain ⟨s', hs'⟩ := exists_integer_eq_conj s
  rw [← algebraMap_smul K s x, LinearMap.map_smulₛₗ₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
  refine Submodule.mem_one.mpr ⟨s' * t, ?_⟩
  rw [map_mul, ht, hs']
end GlobalTheory.Mass.ShortVector
end

set_option autoImplicit false
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
open GlobalTheory GlobalTheory.Mass GlobalTheory.Mass.ShortVector
open GlobalTheory.Mass.DiscOrder
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
namespace GlobalTheory.Mass.ShortVector
theorem _root_.solution [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
    (h1 : Module.finrank K V = 1) (M : Submodule (𝓞 K) V) (hM : IsIntLat h M) :
    ∃ (x : V) (b : 𝓞 K) (I : Ideal (𝓞 K)), x ≠ 0 ∧ (b : K) * h x x = 1 ∧ I ≠ ⊥ ∧ (∀ r ∈ I, r • x ∈ M) ∧
      Ideal.absNorm I ^ 2 = Ideal.absNorm (Ideal.span {b}) * discN h M := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ h1
  have hMne : M ≠ ⊥ := by
    intro hbot
    have h2 := hM.1.span_eq_top
    rw [hbot] at h2
    simp at h2
  obtain ⟨m, hmM, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hMne
  obtain ⟨hmm, hspan⟩ := apply_self_ne_zero_and_span_of_finrank_one h hn h1 hm0
  set x₀ : V := (h m m)⁻¹ • m with hx₀
  have hx0 : x₀ ≠ 0 := smul_ne_zero (inv_ne_zero hmm) hm0
  obtain ⟨hxx, -⟩ := apply_self_ne_zero_and_span_of_finrank_one h hn h1 hx0
  set L : Submodule (𝓞 K) V := Submodule.span (𝓞 K) {x₀} with hL
  have hMd : M ≤ dual h M := fun y hy =>
    (dualBasic_mem_dual h M y).mpr fun z hz => hM.2 z hz y hy
  have hdL : dual h M ≤ L := by
    intro y hy
    obtain ⟨c, rfl⟩ := hspan y
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp ((dualBasic_mem_dual h M _).mp hy m hmM)
    rw [LinearMap.map_smul, smul_eq_mul] at hu
    refine Submodule.mem_span_singleton.mpr ⟨u, ?_⟩
    rw [← algebraMap_smul K u x₀, hu, hx₀, smul_smul, mul_assoc, mul_inv_cancel₀ hmm, mul_one]
  have hML : M ≤ L := hMd.trans hdL
  have hLd : dual h L ≤ dual h M := fun y hy =>
    (dualBasic_mem_dual h M y).mpr fun z hz => (dualBasic_mem_dual h L y).mp hy z (hML hz)
  obtain ⟨b, hb⟩ : ∃ b : 𝓞 K, b • x₀ = (h x₀ x₀)⁻¹ • x₀ :=
    Submodule.mem_span_singleton.mp
      (hdL (hLd (smul_mem_dual_span_of_mul_apply_self_integral h x₀ _ 1 (by rw [map_one, inv_mul_cancel₀ hxx]))))
  have hbK : algebraMap (𝓞 K) K b = (h x₀ x₀)⁻¹ := by
    rw [← algebraMap_smul K b x₀] at hb
    exact smul_left_injective K hx0 hb
  have hcomap : Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x₀) (dual h L) =
      Ideal.span {b} := by
    ext r
    simp only [Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Ideal.mem_span_singleton']
    constructor
    · intro hr
      obtain ⟨u, hu⟩ := Submodule.mem_one.mp
        ((dualBasic_mem_dual h L _).mp hr x₀ (Submodule.mem_span_singleton_self x₀))
      refine ⟨u, FaithfulSMul.algebraMap_injective (𝓞 K) K ?_⟩
      rw [map_mul, hu, ← algebraMap_smul K r x₀, LinearMap.map_smul, smul_eq_mul, hbK, mul_assoc,
        mul_inv_cancel₀ hxx, mul_one]
    · rintro ⟨u, rfl⟩
      rw [← algebraMap_smul K (u * b) x₀]
      exact smul_mem_dual_span_of_mul_apply_self_integral h x₀ _ u (by rw [map_mul, hbK, mul_assoc, inv_mul_cancel₀ hxx, mul_one])
  have hLlat : Submodule.IsLattice K L := span_isLattice h1 hx0
  have e1 := idxN_mul hMd hdL
  have e2 := idxN_mul hLd hdL
  have e3 := idxN_dual h hs hn hM.1 _ L hLlat hML rfl
  have e4 := idxN_span x₀ M
  have e5 := idxN_span x₀ (dual h L)
  rw [hcomap] at e5
  refine ⟨x₀, b, Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x₀) M, hx0, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (· * h x₀ x₀) hbK).trans (inv_mul_cancel₀ hxx)
  · obtain ⟨t, ht⟩ := Submodule.mem_one.mp (hM.2 m hmM m hmM)
    intro hbot
    have htI : t ∈ Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) V x₀) M := by
      simp only [Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
      rw [← algebraMap_smul K t x₀, ht, hx₀, smul_smul, mul_inv_cancel₀ hmm, one_smul]
      exact hmM
    rw [hbot] at htI
    have ht0 : t = 0 := (Submodule.mem_bot _).mp htI
    rw [ht0, map_zero] at ht
    exact hmm ht.symm
  · intro r hr
    exact hr
  · rw [← e4, ← e5, discN, ← e2, e3, ← e1]
    ring
end GlobalTheory.Mass.ShortVector
