-- Prove2me | solution 1 for GlobalTheory.InertUnitOrb.ModelOfN.exists_unit_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:01:27.771591+00:00
-- url     : https://prove2.me/submissions/270ff487-6f73-4038-a451-6df112880b96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_smul_right
import Theorems.Thm_GlobalTheory_InertUnitOrb_ModelOfN_herm_expand
import Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_cO_spec
import Theorems.Thm_GlobalTheory_UnitLemma_UnramNorm_unram_quadratic_facts


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
noncomputable section
open GlobalTheory GlobalTheory.InertUnitOrb GlobalTheory.InertUnitOrb.ModelOfN
variable {K : UQ} {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V] [IsScalarTower K.O K.E V]
namespace GlobalTheory.InertUnitOrb.ModelOfN
theorem _root_.solution [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z)
    (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z) (hsym : ∀ y z, h z y = K.c (h y z))
    (hpos : 0 < Module.finrank K.E V) (L : Submodule K.O V) (hfg : L.FG)
    (hspan : Submodule.span K.E (L : Set V) = ⊤)
    (hdual : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ u ∈ L, h u u = 1 := by
  obtain ⟨hN, -, ⟨ϖ, hϖ, -⟩, -⟩ := UnramNorm.unram_quadratic_facts K
  obtain ⟨θ, θ', hθ, hθm⟩ := K.c_res
  have hinj : Function.Injective (algebraMap K.O K.E) := IsFractionRing.injective _ _
  set ι := algebraMap K.O K.E with hι
  set m := IsLocalRing.maximalIdeal K.O with hm
  by_contra hno
  push_neg at hno
  have c1 : ∀ v ∈ L, ∃ a ∈ m, h v v = ι a := by
    intro v hv
    obtain ⟨a, ha⟩ := (hdual v).1 hv v hv
    refine ⟨a, ?_, ha.symm⟩
    by_contra ham
    have hau : IsUnit a := by
      by_contra hnu
      exact ham ((IsLocalRing.mem_maximalIdeal _).2 hnu)
    have hfix : K.c (ι (hau.unit : K.O)) = ι (hau.unit : K.O) := by
      simp only [IsUnit.unit_spec]
      rw [ha, ← hsym v v]
    obtain ⟨z, hz⟩ := hN hau.unit hfix
    simp only [IsUnit.unit_spec] at hz
    apply hno (((z⁻¹ : K.Oˣ) : K.O) • v) (L.smul_mem _ hv)
    rw [← algebraMap_smul K.E (((z⁻¹ : K.Oˣ) : K.O)) v, hsmul, herm_smul_right h hsmul hsym, ← ha, hz]
    have he : ι ((z⁻¹ : K.Oˣ) : K.O) * ι (z : K.O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hce : K.c (ι ((z⁻¹ : K.Oˣ) : K.O)) * K.c (ι (z : K.O)) = 1 := by
      rw [← map_mul, he, map_one]
    linear_combination (K.c (ι ((z⁻¹ : K.Oˣ) : K.O)) * K.c (ι (z : K.O))) * he + hce
  have c2 : ∀ y ∈ L, ∀ z ∈ L, ∃ a ∈ m, h y z = ι a := by
    intro y hy z hz
    obtain ⟨a, ha⟩ := (hdual y).1 hy z hz
    refine ⟨a, ?_, ha.symm⟩
    have hzy : h z y = ι (UnramNorm.cO K a) := by rw [UnramNorm.cO_spec, ha, ← hsym]
    obtain ⟨a2, ha2m, ha2⟩ := c1 y hy
    obtain ⟨a3, ha3m, ha3⟩ := c1 z hz
    obtain ⟨a1, ha1m, ha1⟩ := c1 (θ • y + z) (L.add_mem (L.smul_mem θ hy) hz)
    obtain ⟨a4, ha4m, ha4⟩ := c1 ((1 : K.O) • y + z) (L.add_mem (L.smul_mem 1 hy) hz)
    rw [← algebraMap_smul K.E θ y, herm_expand h hadd hsmul hsym, hθ, ha2, ha3, ← ha, hzy] at ha1
    rw [← algebraMap_smul K.E (1 : K.O) y, herm_expand h hadd hsmul hsym, ha2, ha3, ← ha, hzy,
      map_one, map_one] at ha4
    have e1 : a1 = θ * θ' * a2 + θ * a + θ' * UnramNorm.cO K a + a3 := hinj (by
      rw [← ha1]; simp only [map_add, map_mul]; rfl)
    have e4 : a4 = a2 + a + UnramNorm.cO K a + a3 := hinj (by
      rw [← ha4]; simp only [map_add, map_mul]; ring)
    have hmem : (θ - θ') * a ∈ m := by
      have : (θ - θ') * a = (a1 - θ * θ' * a2 - a3) - θ' * (a4 - a2 - a3) := by
        rw [e1, e4]; ring
      rw [this]
      refine m.sub_mem (m.sub_mem (m.sub_mem ha1m (m.mul_mem_left _ ha2m)) ha3m) (m.mul_mem_left _ ?_)
      exact m.sub_mem (m.sub_mem ha4m ha2m) ha3m
    rcases (IsLocalRing.maximalIdeal.isMaximal K.O).isPrime.mem_or_mem hmem with h1 | h1
    · exact absurd h1 hθm
    · exact h1
  have hϖ0 : ι ϖ ≠ 0 := fun h0 => hϖ.ne_zero (hinj (by rw [h0, map_zero]))
  have hmϖ : m = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have c3 : L ≤ m • L := by
    intro y hy
    have hy' : (ι ϖ)⁻¹ • y ∈ L := by
      rw [hdual]
      intro z hz
      obtain ⟨a, ham, ha⟩ := c2 y hy z hz
      rw [hmϖ, Ideal.mem_span_singleton'] at ham
      obtain ⟨d, rfl⟩ := ham
      refine ⟨d, ?_⟩
      rw [hsmul, ha, map_mul]
      field_simp
    have : y = ϖ • ((ι ϖ)⁻¹ • y) := by
      rw [← algebraMap_smul K.E ϖ, smul_smul, mul_inv_cancel₀ hϖ0, one_smul]
    rw [this]
    exact Submodule.smul_mem_smul (by rw [hmϖ]; exact Ideal.mem_span_singleton_self ϖ) hy'
  have hL : L = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot m L hfg c3
    (le_of_eq (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).symm)
  have htop : (⊤ : Submodule K.E V) = ⊥ := by rw [← hspan, hL]; simp
  haveI := Module.finrank_pos_iff.1 hpos
  exact bot_ne_top htop.symm
end GlobalTheory.InertUnitOrb.ModelOfN
