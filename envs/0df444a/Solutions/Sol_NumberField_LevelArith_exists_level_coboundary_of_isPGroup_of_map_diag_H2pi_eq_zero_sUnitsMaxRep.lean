-- Prove2me | solution 1 for NumberField.LevelArith.exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/168a50fe-d703-5174-8dd5-942f56dabf4c

import Mathlib
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_NumberField_IdeleClassGroup_isZero_H1_of_isPGroup
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_exists_mulDistribMulAction_smul_eq_classAct
import Theorems.Thm_NumberField_SIdele_exists_addMonoidHom_obj_adeleRing_units_apply
import Theorems.Thm_NumberField_LevelArith_exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Theorems.Thm_NumberField_LevelArith_exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep
import Theorems.Thm_groupCohomology_exists_cor_map_res_two_eq_index_smul
import Theorems.Thm_groupCohomology_subsingleton_H2_of_isUnit_card
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_valuation_eq_ofAdd_neg_count_spanSingleton
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import Theorems.Thm_NumberField_PlaceTransport_under_smul
import Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
p2m_attr_erase "instance" "M4aHerbrand.isMulCommutative_ideleClassGroup M4aHerbrand.isMulCommutative_sIdeleClassGroup LanglandsTunnell.P2.Artin.ArtinPairCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTENΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instFE LanglandsTunnell.P2.Artin.ArtinPairCore.instAKE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKN LanglandsTunnell.P2.Artin.ArtinPairCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instAjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instCΘ LanglandsTunnell.P2.Artin.ArtinFieldCore.instFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNZq LanglandsTunnell.P2.Artin.ArtinPairCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKjE LanglandsTunnell.P2.Artin.ArtinFieldCore.instCN LanglandsTunnell.P2.Artin.ArtinFieldCore.instANΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKLN LanglandsTunnell.P2.Artin.ArtinPairCore.instGEN LanglandsTunnell.P2.Artin.ArtinPairCore.instAiE LanglandsTunnell.P2.Artin.instCommGroupIp LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instAEN LanglandsTunnell.P2.Artin.ArtinPairCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instALN LanglandsTunnell.P2.Artin.ArtinFieldCore.instFN LanglandsTunnell.P2.Artin.ArtinPairCore.instAKN LanglandsTunnell.P2.Artin.ArtinFieldCore.instSTKEN LanglandsTunnell.P2.Artin.ArtinFieldCore.instGEΘ LanglandsTunnell.P2.Artin.ArtinPairCore.instSTKiE LanglandsTunnell.P2.Artin.ArtinFieldCore.instNFN LanglandsTunnell.P2.Artin.ArtinFieldCore.instAKE LanglandsTunnell.P2.Artin.ArtinPairCore.instNFE LanglandsTunnell.P2.Artin.ArtinFieldCore.instALN LanglandsTunnell.P2.Artin.primeAbove_liesOver"
p2m_attr_erase "instance" "LanglandsTunnell.P2.Artin.isGaloisGroup_ringOfIntegers LanglandsTunnell.P2.Artin.primeAbove_isMaximal LanglandsTunnell.P2.Artin.primeAbove_finite Deep.NTSupply.instNormalRayClassSubgroup instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions NumberField.LevelArith.instCommGroupUnitsModPow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "M4aHerbrand.IdeleGaloisDescent.sClassAct_mk M4aHerbrand.SIdeleClassGroup.ofLE_mk M4aHerbrand.repHomOfMulEquivariant_hom_apply M4aHerbrand.coe_finPart_apply M4aHerbrand.SIdeleClassGroup.ofLE_toSIdeleClass M4aHerbrand.IdeleGaloisDescent.sClassAct_toSIdeleClass M4aHerbrand.coe_infPart_apply M4aHerbrand.toSIdeleClass_mk M4aHerbrand.IdeleGaloisDescent.classAct_mk Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk LanglandsTunnell.P2.Artin.ArtinPairCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.sizeOf_spec LanglandsTunnell.P2.Artin.ArtinFieldCore.mk.injEq LanglandsTunnell.P2.Artin.ArtinPairCore.mk.injEq NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

namespace N3Cap
open CategoryTheory groupCohomology

section GenericCohomology
variable {k G : Type} [CommRing k] [Group G]

theorem natCard_smul_mem_coboundaries₂ [Finite G] (A : Rep.{0} k G) (f : cocycles₂ A) :
    (Nat.card G) • (⇑f) ∈ coboundaries₂ A := by
  classical
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_cor_map_res_two_eq_index_smul A (⊥ : Subgroup G)
  have hsub : Subsingleton (groupCohomology (Rep.res (⊥ : Subgroup G).subtype A) 2) := by
    letI : Fintype (⊥ : Subgroup G) := Fintype.ofFinite _
    have h1 : IsUnit ((Fintype.card (⊥ : Subgroup G) : k)) := by
      rw [Fintype.card_eq_nat_card, Subgroup.card_bot, Nat.cast_one]; exact isUnit_one
    exact groupCohomology.subsingleton_H2_of_isUnit_card (Rep.res (⊥ : Subgroup G).subtype A) h1
  have h := hcor (H2π A f)
  rw [Subsingleton.elim ((map (⊥ : Subgroup G).subtype (𝟙 (Rep.res (⊥ : Subgroup G).subtype A)) 2).hom (H2π A f)) 0,
    map_zero, Subgroup.index_bot] at h
  have h2 : H2π A ((Nat.card G) • f) = 0 := by rw [map_nsmul]; exact h.symm
  rw [H2π_eq_zero_iff] at h2
  exact h2

theorem exists_eq_rho_sub_of_isZero_H1_top (M : Rep.{0} k G)
    (h0 : Limits.IsZero (groupCohomology (Rep.res (⊤ : Subgroup G).subtype M) 1))
    (c : G → M) (hc : ∀ g h : G, c (g * h) = M.ρ g (c h) + c g) :
    ∃ β : M, ∀ g : G, c g = M.ρ g β - β := by
  let c' : (⊤ : Subgroup G) → (Rep.res (⊤ : Subgroup G).subtype M) := fun g => c g.1
  have hc' : c' ∈ cocycles₁ (Rep.res (⊤ : Subgroup G).subtype M) := by
    rw [mem_cocycles₁_iff]
    intro g h
    exact hc g.1 h.1
  haveI := ModuleCat.subsingleton_of_isZero h0
  have hz : H1π _ ⟨c', hc'⟩ = 0 := Subsingleton.elim _ _
  rw [H1π_eq_zero_iff] at hz
  obtain ⟨β, hβ⟩ := hz
  refine ⟨β, fun g => ?_⟩
  have := congrFun hβ ⟨g, Subgroup.mem_top g⟩
  rw [cocycles₁.coe_mk, d₀₁_hom_apply] at this
  exact this.symm

end GenericCohomology
end N3Cap

namespace N3Cap
open CategoryTheory groupCohomology

theorem exists_eq_smul_div_of_isZero_H1_top {G C : Type} [Group G] [CommGroup C] [MulDistribMulAction G C]
    (h0 : Limits.IsZero (groupCohomology (Rep.res (⊤ : Subgroup G).subtype (Rep.ofMulDistribMulAction G C)) 1))
    (c : G → C) (hc : ∀ g h : G, c (g * h) = g • c h * c g) :
    ∃ β : C, ∀ g : G, c g = g • β / β := by
  obtain ⟨β, hβ⟩ := exists_eq_rho_sub_of_isZero_H1_top (Rep.ofMulDistribMulAction G C) h0
    (fun g => Additive.ofMul (c g)) (fun g h => by
      show Additive.ofMul (c (g * h)) = Additive.ofMul (g • c h) + Additive.ofMul (c g)
      rw [hc, ofMul_mul])
  exact ⟨Additive.toMul β, fun g => Additive.ofMul.injective (by rw [ofMul_div]; exact hβ g)⟩

end N3Cap

namespace N3Cap
open CategoryTheory groupCohomology IsDedekindDomain NumberField M4aHerbrand

section LayerCFT
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (S : Finset (HeightOneSpectrum (𝓞 E)))

noncomputable def prinHom : Kˣ →* (AdeleRing (𝓞 K) K)ˣ :=
  Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)

omit [IsGalois E K] [Algebra E K] [NumberField E] [Field E] in
theorem prinHom_apply (k : Kˣ) : prinHom K k = Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k := rfl

omit [IsGalois E K] [Algebra E K] [NumberField E] [Field E] in
theorem coe_prinHom_apply (k : Kˣ) : ((prinHom K k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) = algebraMap K (AdeleRing (𝓞 K) K) k := rfl

omit [IsGalois E K] [Algebra E K] [NumberField E] [Field E] in
theorem prinHom_injective : Function.Injective (prinHom K) := fun _ _ h =>
  Units.ext (NumberField.AdeleRing.algebraMap_injective (𝓞 K) K (congrArg (fun u : (AdeleRing (𝓞 K) K)ˣ => (u : AdeleRing (𝓞 K) K)) h))

omit [IsGalois E K] [Algebra E K] [NumberField E] [Field E] in
theorem mem_principalIdeles_iff (z : (AdeleRing (𝓞 K) K)ˣ) : z ∈ principalIdeles (𝓞 K) K ↔ ∃ k, prinHom K k = z := Iff.rfl

omit [IsGalois E K] [NumberField E] in
theorem unitsAct_prinHom (D : IdeleGaloisDescent (𝓞 K) E K) (σ : K ≃ₐ[E] K) (k : Kˣ) :
    D.unitsAct σ (prinHom K k) = prinHom K (Units.map (σ : K →* K) k) :=
  Units.ext (D.compat σ (k : K))

omit [IsGalois E K] [NumberField E] in
theorem classAct_mk (D : IdeleGaloisDescent (𝓞 K) E K) (σ : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ) :
    D.classAct σ (QuotientGroup.mk x : IdeleClassGroup (𝓞 K) K) = QuotientGroup.mk (D.unitsAct σ x) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem exists_descent_class_principal_coboundary (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (K ≃ₐ[E] K))
    (f' : (K ≃ₐ[E] K) × (K ≃ₐ[E] K) → NumberField.SUnits.sUnitsRep E K S)
    (u : (K ≃ₐ[E] K) → NumberField.SIdele.obj E K S)
    (hu : ∀ σ τ : K ≃ₐ[E] K, (NumberField.SIdele.diag E K S).hom (f' (σ, τ)) =
      (NumberField.SIdele.obj E K S).ρ σ (u τ) - u (σ * τ) + u σ) :
    ∃ (β : IdeleClassGroup (𝓞 K) K),
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, (QuotientGroup.mk b : IdeleClassGroup (𝓞 K) K) = β →
        ∃ kk : (K ≃ₐ[E] K) → Kˣ,
          (∀ σ τ : K ≃ₐ[E] K, NumberField.SUnits.val E K S (f' (σ, τ)) = σ • kk τ * (kk (σ * τ))⁻¹ * kk σ) ∧
          (∀ σ : K ≃ₐ[E] K, (M4aHerbrand.GenuineDescent.genuineDescentDatum E K).unitsAct σ b * b⁻¹ * prinHom K (kk σ) ∈
            NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}) := by
  classical
  let D : IdeleGaloisDescent (𝓞 K) E K := M4aHerbrand.GenuineDescent.genuineDescentDatum E K
  obtain ⟨inst, hact⟩ := M4aHerbrand.IdeleGaloisDescent.exists_mulDistribMulAction_smul_eq_classAct E K D
  letI := inst
  obtain ⟨Φ, hΦinj, hΦrange, hΦequiv, hΦdiag, -, -, -⟩ :=
    NumberField.SIdele.exists_addMonoidHom_obj_adeleRing_units_apply E K S D

  set x : (K ≃ₐ[E] K) → (AdeleRing (𝓞 K) K)ˣ := fun σ => Additive.toMul (Φ (u σ)) with hx
  have hxmem : ∀ σ, x σ ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S} := by
    intro σ
    have : Φ (u σ) ∈ Φ.range := ⟨u σ, rfl⟩
    rw [hΦrange] at this
    exact this

  have hdx : ∀ σ τ : K ≃ₐ[E] K, D.unitsAct σ (x τ) * (x (σ * τ))⁻¹ * x σ =
      prinHom K (NumberField.SUnits.val E K S (f' (σ, τ))) := by
    intro σ τ
    have h1 := congrArg (fun y => Additive.toMul (Φ y)) (hu σ τ)
    simp only [map_add, map_sub, toMul_add, toMul_sub, hΦdiag, hΦequiv, toMul_ofMul] at h1
    rw [prinHom_apply, h1]
    simp only [hx, div_eq_mul_inv]

  let c : (K ≃ₐ[E] K) → IdeleClassGroup (𝓞 K) K := fun σ => QuotientGroup.mk (x σ)
  have hc : ∀ g h : K ≃ₐ[E] K, c (g * h) = g • c h * c g := by
    intro g h
    show (QuotientGroup.mk (x (g * h)) : IdeleClassGroup (𝓞 K) K) =
      g • (QuotientGroup.mk (x h) : IdeleClassGroup (𝓞 K) K) * QuotientGroup.mk (x g)
    rw [hact, classAct_mk, ← QuotientGroup.mk_mul, eq_comm, QuotientGroup.eq, mem_principalIdeles_iff]
    refine ⟨(NumberField.SUnits.val E K S (f' (g, h)))⁻¹, ?_⟩
    rw [map_inv, ← hdx g h]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  obtain ⟨β, hβ⟩ := exists_eq_smul_div_of_isZero_H1_top
    (NumberField.IdeleClassGroup.isZero_H1_of_isPGroup E K p hG D hact ⊤) c hc
  refine ⟨β, fun b hb => ?_⟩

  have hcls : ∀ σ : K ≃ₐ[E] K, ∃ k : Kˣ, D.unitsAct σ b * b⁻¹ * prinHom K k = x σ := by
    intro σ
    have h1 : (QuotientGroup.mk (x σ) : IdeleClassGroup (𝓞 K) K) = σ • β / β := hβ σ
    rw [← hb, hact, classAct_mk, ← QuotientGroup.mk_div, QuotientGroup.eq, mem_principalIdeles_iff] at h1
    obtain ⟨k, hk⟩ := h1
    refine ⟨k⁻¹, ?_⟩
    rw [map_inv, hk]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_div]
    abel
  choose kk hkk using hcls
  refine ⟨kk, fun σ τ => ?_, fun σ => by rw [hkk]; exact hxmem σ⟩

  apply prinHom_injective K
  rw [← hdx σ τ, ← hkk τ, ← hkk (σ * τ), ← hkk σ]
  have e1 : D.unitsAct σ (D.unitsAct τ b) = D.unitsAct (σ * τ) b := by rw [map_mul]; rfl
  have e2 : (Units.map (σ : K →* K) (kk τ)) = σ • kk τ := rfl
  simp only [map_mul, map_inv, unitsAct_prinHom, e1, e2]

  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end LayerCFT
end N3Cap

namespace N3Cap
open IsDedekindDomain NumberField
open scoped nonZeroDivisors

section Arith

theorem exists_mtrick (p : ℕ) (hp : p.Prime) (n h : ℕ) (hh : h ≠ 0) :
    ∃ m a k : ℕ, 0 < m ∧ p ^ n ∣ (m - 1) ∧ m * p ^ a = h * k := by
  obtain ⟨a, h', hnd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hh p hp.one_lt.ne'
  have hco : (p ^ n).Coprime h' := (Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd))
  obtain ⟨m0, hm1, hm0⟩ := Nat.chineseRemainder hco 1 0
  refine ⟨m0 + p ^ n * h', a, (m0 + p ^ n * h') / h', ?_, ?_, ?_⟩
  · have : 0 < p ^ n * h' := Nat.pos_of_ne_zero (by
      intro h0; rcases Nat.mul_eq_zero.1 h0 with h0 | h0
      · exact hp.ne_zero (pow_eq_zero_iff'.1 h0).1
      · exact hnd (h0 ▸ dvd_zero p))
    omega
  · rcases Nat.eq_zero_or_pos m0 with h0 | h0
    · subst h0
      have h1' : p ^ n ∣ 1 := by simpa using (Nat.modEq_iff_dvd' (Nat.zero_le 1)).1 hm1
      rw [Nat.dvd_one.1 h1']
      exact one_dvd _
    · have h1' : p ^ n ∣ m0 - 1 := (Nat.modEq_iff_dvd' h0).1 hm1.symm
      have : m0 + p ^ n * h' - 1 = (m0 - 1) + p ^ n * h' := by omega
      rw [this]
      exact dvd_add h1' (dvd_mul_right _ _)
  · have hdvd : h' ∣ m0 + p ^ n * h' := by
      have : h' ∣ m0 := (Nat.modEq_zero_iff_dvd.1 hm0)
      exact dvd_add this (dvd_mul_left _ _)
    obtain ⟨k, hk⟩ := hdvd
    rw [hk, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (by rintro rfl; exact hnd (dvd_zero p)))]
    ring

end Arith

section Content
variable (K : Type) [Field K] [NumberField K]

noncomputable def logv (b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) : ℤ :=
  WithZero.log (Valued.v (((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w))

theorem valued_snd_ne_zero (b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) ≠ 0 := by
  rw [Valuation.ne_zero_iff]
  exact (FiniteAdeleRing.isUnit_iff.1 (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom b).isUnit).1 w

theorem valued_snd_eq_exp (b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) = WithZero.exp (logv K b w) := by
  rw [logv, WithZero.exp_log (valued_snd_ne_zero K b w)]

theorem logv_mul (b c : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) : logv K (b * c) w = logv K b w + logv K c w := by
  rw [logv, logv, logv, ← WithZero.log_mul (valued_snd_ne_zero K b w) (valued_snd_ne_zero K c w), ← Valuation.map_mul]
  rfl

theorem logv_inv (b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) : logv K b⁻¹ w = -logv K b w := by
  have := logv_mul K b b⁻¹ w
  rw [mul_inv_cancel] at this
  have h1 : logv K 1 w = 0 := by
    have := logv_mul K 1 1 w; rw [mul_one] at this; omega
  omega

theorem valued_snd_prinHom (k : Kˣ) (w : HeightOneSpectrum (𝓞 K)) :
    Valued.v (((prinHom K k : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) = w.valuation K k := by
  rw [coe_prinHom_apply, NumberField.AdeleRing.algebraMap_snd_apply]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : K)

theorem logv_prinHom (k : Kˣ) (w : HeightOneSpectrum (𝓞 K)) :
    logv K (prinHom K k) w = -FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K)) := by
  rw [logv, valued_snd_prinHom, HeightOneSpectrum.valuation_eq_ofAdd_neg_count_spanSingleton w (k : K) k.ne_zero]
  rfl

theorem finite_logv_ne_zero (b : (AdeleRing (𝓞 K) K)ˣ) : ∀ᶠ w in Filter.cofinite, logv K b w = 0 := by
  have h := (FiniteAdeleRing.isUnit_iff.1 (Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).toMonoidHom b).isUnit).2
  filter_upwards [h] with w hw
  rw [logv]
  change WithZero.log (Valued.v (((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w)) = 0
  have : Valued.v (((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 w) = 1 := hw
  rw [this, WithZero.log_one]

noncomputable def fracIdeal (b : (AdeleRing (𝓞 K) K)ˣ) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 K), (w.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ (-(logv K b w))

theorem count_fracIdeal (b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K w (fracIdeal K b) = -logv K b w := by
  rw [fracIdeal, FractionalIdeal.count_finprod]
  filter_upwards [finite_logv_ne_zero K b] with v hv
  rw [hv, neg_zero]

theorem fracIdeal_ne_zero (b : (AdeleRing (𝓞 K) K)ˣ) : fracIdeal K b ≠ 0 := by
  rw [fracIdeal]
  exact finprod_induction (fun I => I ≠ 0) one_ne_zero (fun _ _ h1 h2 => mul_ne_zero h1 h2)
    (fun w => zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.2 w.ne_bot))

theorem FI_eq_of_count_eq {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K w I = FractionalIdeal.count K w J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI, ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun w => by rw [h w]

theorem fracIdeal_mul (b c : (AdeleRing (𝓞 K) K)ˣ) : fracIdeal K (b * c) = fracIdeal K b * fracIdeal K c := by
  refine FI_eq_of_count_eq K (fracIdeal_ne_zero K _) (mul_ne_zero (fracIdeal_ne_zero K _) (fracIdeal_ne_zero K _)) fun w => ?_
  rw [FractionalIdeal.count_mul K w (fracIdeal_ne_zero K _) (fracIdeal_ne_zero K _), count_fracIdeal, count_fracIdeal, count_fracIdeal, logv_mul, neg_add]

theorem fracIdeal_prinHom (k : Kˣ) : fracIdeal K (prinHom K k) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
  refine FI_eq_of_count_eq K (fracIdeal_ne_zero K _) (FractionalIdeal.spanSingleton_ne_zero_iff.2 k.ne_zero) fun w => ?_
  rw [count_fracIdeal, logv_prinHom]; exact neg_neg _

theorem exists_rep_fracIdeal_eq_coeIdeal (b₀ : (AdeleRing (𝓞 K) K)ˣ) :
    ∃ (d : Kˣ) (J : Ideal (𝓞 K)), J ≠ ⊥ ∧ fracIdeal K (b₀ * prinHom K d) = (J : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨a, J, ha, hJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (fracIdeal K b₀)
  have ha' : (algebraMap (𝓞 K) K a) ≠ 0 := fun h0 => ha ((IsFractionRing.to_map_eq_zero_iff (K := K)).1 h0)
  refine ⟨Units.mk0 _ ha', J, ?_, ?_⟩
  · rintro rfl
    apply fracIdeal_ne_zero K b₀
    rw [hJ]; simp
  · rw [fracIdeal_mul, fracIdeal_prinHom, hJ, Units.val_mk0, mul_comm, ← mul_assoc,
      FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv_cancel₀ ha', FractionalIdeal.spanSingleton_one, one_mul]

theorem exists_pow_mul_pow_eq_span (p : ℕ) (hp : p.Prime) (n : ℕ) (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) :
    ∃ (m a : ℕ) (g : 𝓞 K), 0 < m ∧ p ^ n ∣ (m - 1) ∧ g ≠ 0 ∧ (J ^ m) ^ p ^ a = Ideal.span {g} := by
  classical
  have hJ0 : J ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.2 hJ
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hh0 : h ≠ 0 := Fintype.card_ne_zero
  obtain ⟨m, a, k, hm, hdvd, hmk⟩ := exists_mtrick p hp n h hh0

  have hprin : (J ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨J, hJ0⟩ : (Ideal (𝓞 K))⁰) ^ h = 1 := pow_card_eq_one
    rw [← map_pow] at h1
    have h2 : (⟨J, hJ0⟩ : (Ideal (𝓞 K))⁰) ^ h = ⟨J ^ h, pow_mem hJ0 h⟩ := Subtype.ext (by simp)
    rw [h2, ClassGroup.mk0_eq_one_iff] at h1
    exact h1
  obtain ⟨g, hg⟩ := hprin
  refine ⟨m, a, g ^ k, hm, hdvd, ?_, ?_⟩
  · intro h0
    have : J ^ h = ⊥ := by
      rw [hg, Ideal.submodule_span_eq, Ideal.span_singleton_eq_bot]
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [mul_zero, Nat.mul_eq_zero] at hmk
        rcases hmk with hmk | hmk
        · omega
        · exact hp.ne_zero (pow_eq_zero_iff'.1 hmk).1
      exact (pow_eq_zero_iff hk0).1 h0
    exact pow_ne_zero h hJ this
  · rw [← pow_mul, hmk, pow_mul, hg, Ideal.submodule_span_eq, Ideal.span_singleton_pow]

end Content
end N3Cap

namespace N3Cap
open IsDedekindDomain NumberField M4aHerbrand
open scoped nonZeroDivisors NumberField.PlaceTransport

section LayerVal
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem logv_eq_zero_of_mem_unitIdelesOutside {T : Set (HeightOneSpectrum (𝓞 K))} {x : (AdeleRing (𝓞 K) K)ˣ}
    (hx : x ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T) {w : HeightOneSpectrum (𝓞 K)} (hw : w ∉ T) :
    logv K x w = 0 := by
  have key : ∀ y : (AdeleRing (𝓞 K) K)ˣ, y ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K T → logv K y w ≤ 0 := by
    intro y hy
    have h1 := ((NumberField.AdeleRing.mem_unitIdelesOutside_iff T y).1 hy w hw).1
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    rw [logv, WithZero.log_le_iff_le_exp (valued_snd_ne_zero K y w), WithZero.exp_zero]
    exact h1
  have h1 := key x hx
  have h2 := key x⁻¹ (inv_mem hx)
  rw [logv_inv] at h2
  omega

theorem logv_unitsAct_smul (σ : K ≃ₐ[E] K) (b : (AdeleRing (𝓞 K) K)ˣ) (w : HeightOneSpectrum (𝓞 K)) :
    logv K ((M4aHerbrand.GenuineDescent.genuineDescentDatum E K).unitsAct σ b) (σ • w) = logv K b w := by
  rw [logv, logv]
  congr 1
  have h := M4aHerbrand.GenuineDescent.genuineDescentDatum_act_snd_apply E K σ ((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K) (rfl : σ • w = σ • w)
  change Valued.v (((M4aHerbrand.GenuineDescent.genuineDescentDatum E K).act σ ((b : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 (σ • w)) = _
  rw [h, NumberField.PlaceTransport.valued_transport]

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

theorem count_spanSingleton_eq_of_mem (σ : K ≃ₐ[E] K) (b : (AdeleRing (𝓞 K) K)ˣ) (k : Kˣ) (J : Ideal (𝓞 K))
    (hJ : fracIdeal K b = (J : FractionalIdeal (𝓞 K)⁰ K))
    (hmem : (M4aHerbrand.GenuineDescent.genuineDescentDatum E K).unitsAct σ b * b⁻¹ * prinHom K k ∈
      NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (w : HeightOneSpectrum (𝓞 K)) (hw : w.under (𝓞 E) ∉ S) :
    FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K)) =
      FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K) - FractionalIdeal.count K (σ⁻¹ • w) (J : FractionalIdeal (𝓞 K)⁰ K) := by
  have h0 := logv_eq_zero_of_mem_unitIdelesOutside K hmem (T := {w | w.under (𝓞 E) ∈ S}) (w := w) hw
  rw [logv_mul, logv_mul, logv_inv, logv_prinHom] at h0
  have h1 := logv_unitsAct_smul E K σ b (σ⁻¹ • w)
  rw [smul_inv_smul] at h1
  rw [h1] at h0
  rw [← hJ, count_fracIdeal, count_fracIdeal]
  omega

end LayerVal
end N3Cap

namespace N3Cap
open IsDedekindDomain NumberField
open scoped nonZeroDivisors

section general

theorem ramificationIdx_map_map_of_forall_apply {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (τR : R ≃+* R) (τS : S ≃+* S) (h : ∀ r, τS (algebraMap R S r) = algebraMap R S (τR r))
    (p : Ideal R) (P : Ideal S) :
    (p.map (τR : R →+* R)).ramificationIdx' (P.map (τS : S →+* S)) = p.ramificationIdx' P := by
  dsimp only [Ideal.ramificationIdx']
  congr 1
  ext n
  simp only [Set.mem_setOf_eq]
  have hcomp : (algebraMap R S).comp (τR : R →+* R) = (τS : S →+* S).comp (algebraMap R S) :=
    RingHom.ext fun r => (h r).symm
  rw [Ideal.map_map, hcomp, ← Ideal.map_map, ← Ideal.map_pow]
  constructor
  · intro hle
    have := Ideal.map_mono (f := (τS.symm : S →+* S)) hle
    rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this
  · exact fun hle => Ideal.map_mono hle

end general

section HB
variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev ramIdx (W : HeightOneSpectrum (𝓞 L)) : ℕ :=
  (W.under (𝓞 K)).asIdeal.ramificationIdx' W.asIdeal

scoped instance liesOver_under (W : HeightOneSpectrum (𝓞 L)) :
    W.asIdeal.LiesOver (W.under (𝓞 K)).asIdeal := ⟨rfl⟩

omit [NumberField K] in

theorem ramIdx_ne_zero (W : HeightOneSpectrum (𝓞 L)) : ramIdx K L W ≠ 0 :=
  Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver W.asIdeal (W.under (𝓞 K)).ne_bot

theorem multiplicity_map_eq_ramIdx_mul (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (W : HeightOneSpectrum (𝓞 L)) :
    multiplicity W.asIdeal (J.map (algebraMap (𝓞 K) (𝓞 L))) =
      ramIdx K L W * multiplicity (W.under (𝓞 K)).asIdeal J := by
  have hJ' : J.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hJ
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx_mul (S := 𝓞 L) hJ
    (W.under (𝓞 K)).irreducible W.irreducible W.ne_bot
  rw [(FiniteMultiplicity.of_prime_left W.prime hJ').emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left (W.under (𝓞 K)).prime hJ).emultiplicity_eq_multiplicity] at h
  exact_mod_cast h

theorem count_map_eq_ramIdx_mul_count (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (W : HeightOneSpectrum (𝓞 L)) :
    FractionalIdeal.count L W ((J.map (algebraMap (𝓞 K) (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)) =
      (ramIdx K L W : ℤ) * FractionalIdeal.count K (W.under (𝓞 K)) (J : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  have hJ' : J.map (algebraMap (𝓞 K) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hJ
  rw [FractionalIdeal.count_coe L W hJ', FractionalIdeal.count_coe K (W.under (𝓞 K)) hJ,
    Ideal.count_associates_factors_eq hJ' W.isPrime W.ne_bot,
    Ideal.count_associates_factors_eq hJ (W.under (𝓞 K)).isPrime (W.under (𝓞 K)).ne_bot,
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hJ',
    HeightOneSpectrum.count_normalizedFactors_eq_multiplicity hJ,
    multiplicity_map_eq_ramIdx_mul K L J hJ W]
  push_cast
  rfl

theorem intValuation_algebraMap_eq_pow (r : 𝓞 K) (W : HeightOneSpectrum (𝓞 L)) :
    W.intValuation (algebraMap (𝓞 K) (𝓞 L) r) = ((W.under (𝓞 K)).intValuation r) ^ (ramIdx K L W) := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [map_zero, map_zero, map_zero, zero_pow (ramIdx_ne_zero K L W)]
  have hr' : algebraMap (𝓞 K) (𝓞 L) r ≠ 0 :=
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 L))).2 hr
  have hspan : Ideal.span {algebraMap (𝓞 K) (𝓞 L) r} = (Ideal.span {r}).map (algebraMap (𝓞 K) (𝓞 L)) := by
    rw [Ideal.map_span, Set.image_singleton]
  have hspan0 : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [W.intValuation_eq_exp_neg_multiplicity hr', (W.under (𝓞 K)).intValuation_eq_exp_neg_multiplicity hr,
    ← WithZero.exp_nsmul, hspan, multiplicity_map_eq_ramIdx_mul K L _ hspan0 W]
  congr 1
  push_cast
  ring

theorem valuation_algebraMap_eq_pow (x : K) (W : HeightOneSpectrum (𝓞 L)) :
    W.valuation L (algebraMap K L x) = ((W.under (𝓞 K)).valuation K x) ^ (ramIdx K L W) := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : ∀ c : 𝓞 K, algebraMap K L (algebraMap (𝓞 K) K c) = algebraMap (𝓞 L) L (algebraMap (𝓞 K) (𝓞 L) c) :=
    fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, div_pow, h1, h1, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intValuation_algebraMap_eq_pow, intValuation_algebraMap_eq_pow]

end HB

section RC
open scoped NumberField.PlaceTransport
variable {E K L : Type*} [Field E] [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L]

omit [NumberField K] [NumberField L] [IsScalarTower E K L] in

theorem smul_algebraMap_of_forall_apply (σL : L ≃ₐ[E] L) (σK : K ≃ₐ[E] K)
    (hσ : ∀ x : K, σL (algebraMap K L x) = algebraMap K L (σK x)) (r : 𝓞 K) :
    σL • algebraMap (𝓞 K) (𝓞 L) r = algebraMap (𝓞 K) (𝓞 L) (σK • r) := by
  apply RingOfIntegers.coe_injective
  show σL (algebraMap K L (algebraMap (𝓞 K) K r)) = algebraMap K L (algebraMap (𝓞 K) K (σK • r))
  rw [hσ]
  rfl

omit [NumberField K] [NumberField L] [IsScalarTower E K L] in

theorem inv_forall_apply_of_forall_apply (σL : L ≃ₐ[E] L) (σK : K ≃ₐ[E] K)
    (hσ : ∀ x : K, σL (algebraMap K L x) = algebraMap K L (σK x)) (x : K) :
    σL⁻¹ (algebraMap K L x) = algebraMap K L (σK⁻¹ x) := by
  rw [AlgEquiv.aut_inv, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hσ, AlgEquiv.apply_symm_apply]

omit [NumberField K] [NumberField L] [IsScalarTower E K L] in

theorem under_smul_of_forall_apply (σL : L ≃ₐ[E] L) (σK : K ≃ₐ[E] K)
    (hσ : ∀ x : K, σL (algebraMap K L x) = algebraMap K L (σK x)) (W : HeightOneSpectrum (𝓞 L)) :
    (σL • W).under (𝓞 K) = σK • (W.under (𝓞 K)) := by
  have hc := smul_algebraMap_of_forall_apply σL⁻¹ σK⁻¹ (inv_forall_apply_of_forall_apply σL σK hσ)
  apply HeightOneSpectrum.ext
  ext x
  rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap,
    NumberField.PlaceTransport.mem_smul_asIdeal_iff, NumberField.PlaceTransport.mem_smul_asIdeal_iff,
    HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, hc]

omit [NumberField K] [NumberField L] [IsScalarTower E K L] in

theorem ramIdx_smul_of_forall_apply (σL : L ≃ₐ[E] L) (σK : K ≃ₐ[E] K)
    (hσ : ∀ x : K, σL (algebraMap K L x) = algebraMap K L (σK x)) (W : HeightOneSpectrum (𝓞 L)) :
    ramIdx K L (σL • W) = ramIdx K L W := by
  rw [ramIdx, ramIdx, under_smul_of_forall_apply σL σK hσ, NumberField.PlaceTransport.smul_asIdeal_eq_map,
    NumberField.PlaceTransport.smul_asIdeal_eq_map]
  refine ramificationIdx_map_map_of_forall_apply _ _ (fun r => ?_) _ _
  rw [MulSemiringAction.toRingEquiv_apply, MulSemiringAction.toRingEquiv_apply]
  exact smul_algebraMap_of_forall_apply σL σK hσ r

end RC
end N3Cap
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

namespace N3Cap
open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField.PlaceTransport

section Eta
variable {E K L : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra E K] [Algebra E L] [Algebra K L] [IsScalarTower E K L]

omit [NumberField E] [Algebra E K] in

theorem valuation_eq_exp_neg_count (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    w.valuation K x = WithZero.exp (-FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) :=
  HeightOneSpectrum.valuation_eq_ofAdd_neg_count_spanSingleton w x hx

theorem valuation_integer_eq_exp_neg_count (W : HeightOneSpectrum (𝓞 L)) (t : 𝓞 L) (ht : t ≠ 0) :
    W.valuation L (t : L) = WithZero.exp (-FractionalIdeal.count L W ((Ideal.span {t} : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)) := by
  rw [FractionalIdeal.coeIdeal_span_singleton]
  exact valuation_eq_exp_neg_count W (t : L) (by exact_mod_cast ht)

omit [NumberField E] [NumberField K] [NumberField L] in

theorem under_under_ringOfIntegers (W : HeightOneSpectrum (𝓞 L)) : (W.under (𝓞 K)).under (𝓞 E) = W.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
  exact Ideal.under_under _

omit [NumberField E] in

theorem valuation_eta_eq_one (S : Finset (HeightOneSpectrum (𝓞 E)))
    (σL : L ≃ₐ[E] L) (σK : K ≃ₐ[E] K) (hσ : ∀ x : K, σL (algebraMap K L x) = algebraMap K L (σK x))
    (J : Ideal (𝓞 K)) (hJ : J ≠ ⊥) (m : ℕ) (t : 𝓞 L) (ht0 : t ≠ 0)
    (ht : (J ^ m).map (algebraMap (𝓞 K) (𝓞 L)) = Ideal.span {t})
    (k : Kˣ)
    (hk : ∀ w : HeightOneSpectrum (𝓞 K), w.under (𝓞 E) ∉ S →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K)) =
        FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K) - FractionalIdeal.count K (σK⁻¹ • w) (J : FractionalIdeal (𝓞 K)⁰ K))
    (W : HeightOneSpectrum (𝓞 L)) (hW : W.under (𝓞 E) ∉ S) :
    W.valuation L ((algebraMap K L (k : K)) ^ m * σL (t : L) / (t : L)) = 1 := by

  set w : HeightOneSpectrum (𝓞 K) := W.under (𝓞 K) with hw
  have hwS : w.under (𝓞 E) ∉ S := by
    rwa [hw, under_under_ringOfIntegers]
  set W₁ : HeightOneSpectrum (𝓞 L) := σL⁻¹ • W with hW₁
  have hσ' := inv_forall_apply_of_forall_apply σL σK hσ
  have hw₁ : W₁.under (𝓞 K) = σK⁻¹ • w := under_smul_of_forall_apply σL⁻¹ σK⁻¹ hσ' W
  have he₁ : ramIdx K L W₁ = ramIdx K L W := ramIdx_smul_of_forall_apply σL⁻¹ σK⁻¹ hσ' W
  have hJm : J ^ m ≠ ⊥ := pow_ne_zero m hJ

  have h1 : W.valuation L (algebraMap K L (k : K)) =
      WithZero.exp (-((ramIdx K L W : ℤ) * (FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K) -
        FractionalIdeal.count K (σK⁻¹ • w) (J : FractionalIdeal (𝓞 K)⁰ K)))) := by
    rw [valuation_algebraMap_eq_pow, valuation_eq_exp_neg_count _ _ k.ne_zero, hk w hwS, ← WithZero.exp_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  have h2 : W.valuation L (t : L) = WithZero.exp (-((ramIdx K L W : ℤ) * (m * FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K)))) := by
    rw [valuation_integer_eq_exp_neg_count W t ht0, ← ht, count_map_eq_ramIdx_mul_count K L _ hJm, FractionalIdeal.coeIdeal_pow,
      FractionalIdeal.count_pow]
  have h3 : W.valuation L (σL (t : L)) = WithZero.exp (-((ramIdx K L W : ℤ) * (m * FractionalIdeal.count K (σK⁻¹ • w) (J : FractionalIdeal (𝓞 K)⁰ K)))) := by
    have e1 : W = σL • W₁ := by rw [hW₁, smul_inv_smul]
    have e2 : W.valuation L (σL (t : L)) = W₁.valuation L (t : L) := by
      conv_lhs => rw [e1]
      exact NumberField.PlaceTransport.valuation_smul_apply σL W₁ (t : L)
    rw [e2, valuation_integer_eq_exp_neg_count W₁ t ht0, ← ht,
      count_map_eq_ramIdx_mul_count K L _ hJm, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow, hw₁, he₁]
  rw [map_div₀, map_mul, map_pow, h1, h2, h3, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_sub]
  conv_rhs => rw [← WithZero.exp_zero]
  congr 1
  simp only [nsmul_eq_mul]
  ring

end Eta
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"
end N3Cap
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

namespace N3Cap
open IsDedekindDomain NumberField
open scoped nonZeroDivisors NumberField.PlaceTransport

section SUnitsMem
variable (E L : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
  (S : Finset (HeightOneSpectrum (𝓞 E)))

omit [NumberField E] in

theorem mem_sUnits_of_forall_valuation_eq_one (x : Lˣ)
    (h : ∀ W : HeightOneSpectrum (𝓞 L), W.under (𝓞 E) ∉ S → W.valuation L (x : L) = 1) :
    x ∈ NumberField.SUnits.sUnits E L S := by
  rw [NumberField.SUnits.mem_sUnits_iff]
  intro σ W hW
  have e1 : W = σ • (σ⁻¹ • W) := (smul_inv_smul σ W).symm
  have e2 : W.valuation L (σ (x : L)) = (σ⁻¹ • W).valuation L (x : L) := by
    conv_lhs => rw [e1]
    exact NumberField.PlaceTransport.valuation_smul_apply σ _ (x : L)
  rw [e2]
  apply h
  rwa [NumberField.PlaceTransport.under_smul]

omit [NumberField E] in

theorem valuation_eq_one_of_mem_sUnits {x : Lˣ} (hx : x ∈ NumberField.SUnits.sUnits E L S)
    (W : HeightOneSpectrum (𝓞 L)) (hW : W.under (𝓞 E) ∉ S) : W.valuation L (x : L) = 1 := by
  have := (NumberField.SUnits.mem_sUnits_iff E L S x).1 hx 1 W hW
  simpa using this

end SUnitsMem
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

section DEta
variable {E K L : Type} [Field E] [Field K] [Field L] [Algebra E K] [Algebra E L] [Algebra K L]

theorem d_eta (r : (L ≃ₐ[E] L) →* (K ≃ₐ[E] K)) (hr : ∀ (σ : L ≃ₐ[E] L) (x : K), σ (algebraMap K L x) = algebraMap K L (r σ x))
    (fv : (K ≃ₐ[E] K) × (K ≃ₐ[E] K) → K) (kk ζ : (K ≃ₐ[E] K) → K)
    (hkk0 : ∀ σ, kk σ ≠ 0) (hζ0 : ∀ σ, ζ σ ≠ 0)
    (m' : ℕ)
    (hf : ∀ σ τ : K ≃ₐ[E] K, fv (σ, τ) * kk (σ * τ) = σ (kk τ) * kk σ)
    (hz : ∀ σ τ : K ≃ₐ[E] K, fv (σ, τ) ^ m' * ζ (σ * τ) = σ (ζ τ) * ζ σ)
    (t : L) (ht : t ≠ 0) (σ τ : L ≃ₐ[E] L) :
    let η : (L ≃ₐ[E] L) → L := fun σ => (algebraMap K L (kk (r σ))) ^ (m' + 1) * σ t / t * (algebraMap K L (ζ (r σ)))⁻¹
    σ (η τ) * (η (σ * τ))⁻¹ * η σ = algebraMap K L (fv (r σ, r τ)) := by
  intro η
  have hι : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hkk0' : ∀ σ, algebraMap K L (kk σ) ≠ 0 := fun σ => (map_ne_zero_iff _ hι).2 (hkk0 σ)
  have hζ0' : ∀ σ, algebraMap K L (ζ σ) ≠ 0 := fun σ => (map_ne_zero_iff _ hι).2 (hζ0 σ)
  have hσt : σ t ≠ 0 := (map_ne_zero σ).2 ht
  have hτt : τ t ≠ 0 := (map_ne_zero τ).2 ht
  have hστt : σ (τ t) ≠ 0 := (map_ne_zero σ).2 hτt
  have hf' : ∀ σ τ : K ≃ₐ[E] K, fv (σ, τ) = σ (kk τ) * kk σ / kk (σ * τ) := fun σ τ => by
    rw [eq_div_iff (hkk0 _)]; exact hf σ τ
  have hz' : ∀ σ τ : K ≃ₐ[E] K, fv (σ, τ) ^ m' = σ (ζ τ) * ζ σ / ζ (σ * τ) := fun σ τ => by
    rw [eq_div_iff (hζ0 _)]; exact hz σ τ

  have hfv : fv (r σ, r τ) = (fv (r σ, r τ)) ^ (m' + 1) * ((fv (r σ, r τ)) ^ m')⁻¹ := by
    have h0 : fv (r σ, r τ) ≠ 0 := by rw [hf']; exact div_ne_zero (mul_ne_zero ((map_ne_zero _).2 (hkk0 _)) (hkk0 _)) (hkk0 _)
    rw [pow_succ', mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ h0), mul_one]
  rw [hfv, hz', hf', map_mul]
  simp only [η, map_mul, map_pow, map_inv₀, map_div₀, hr, AlgEquiv.mul_apply]
  have e1 : ∀ x : K, algebraMap K L ((r σ) x) = σ (algebraMap K L x) := fun x => (hr σ x).symm
  simp only [e1]
  have a1 := hkk0' (r τ); have a2 := hkk0' (r σ * r τ); have a3 := hkk0' (r σ)
  have b1 := hζ0' (r τ); have b2 := hζ0' (r σ * r τ); have b3 := hζ0' (r σ)
  have c1 : σ (algebraMap K L (kk (r τ))) ≠ 0 := (map_ne_zero σ).2 a1
  have c2 : σ (algebraMap K L (ζ (r τ))) ≠ 0 := (map_ne_zero σ).2 b1
  simp only [div_eq_mul_inv, mul_pow, inv_pow, mul_inv]
  field_simp

end DEta
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"
end N3Cap
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

namespace N3Cap
open CategoryTheory groupCohomology IsDedekindDomain NumberField M4aHerbrand
open scoped nonZeroDivisors NumberField.PlaceTransport

section LayerData
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (S : Finset (HeightOneSpectrum (𝓞 E)))

theorem layer_data (p : ℕ) [Fact p.Prime] (hG : IsPGroup p (K ≃ₐ[E] K))
    (f' : cocycles₂ (NumberField.SUnits.sUnitsRep E K S))
    (u : (K ≃ₐ[E] K) → NumberField.SIdele.obj E K S)
    (hu : ∀ σ τ : K ≃ₐ[E] K, (NumberField.SIdele.diag E K S).hom (f' (σ, τ)) =
      (NumberField.SIdele.obj E K S).ρ σ (u τ) - u (σ * τ) + u σ) :
    ∃ (J : Ideal (𝓞 K)) (_ : J ≠ ⊥) (kk : (K ≃ₐ[E] K) → Kˣ) (ζ : (K ≃ₐ[E] K) → NumberField.SUnits.sUnitsRep E K S)
      (m' a : ℕ) (g : 𝓞 K) (_ : g ≠ 0),
      (∀ σ τ : K ≃ₐ[E] K, NumberField.SUnits.val E K S (f' (σ, τ)) = σ • kk τ * (kk (σ * τ))⁻¹ * kk σ) ∧
      (∀ σ τ : K ≃ₐ[E] K, m' • f' (σ, τ) = (NumberField.SUnits.sUnitsRep E K S).ρ σ (ζ τ) - ζ (σ * τ) + ζ σ) ∧
      (J ^ (m' + 1)) ^ p ^ a = Ideal.span {g} ∧
      (∀ (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)), w.under (𝓞 E) ∉ S →
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (kk σ : K)) =
          FractionalIdeal.count K w (J : FractionalIdeal (𝓞 K)⁰ K) - FractionalIdeal.count K (σ⁻¹ • w) (J : FractionalIdeal (𝓞 K)⁰ K)) := by
  classical

  obtain ⟨β, hβ⟩ := exists_descent_class_principal_coboundary E K S p hG (fun στ => f' στ) u (fun σ τ => hu σ τ)

  obtain ⟨d, J, hJ0, hJ⟩ := exists_rep_fracIdeal_eq_coeIdeal K (Quotient.out β)
  have hb : (QuotientGroup.mk (Quotient.out β * prinHom K d) : IdeleClassGroup (𝓞 K) K) = β := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', (QuotientGroup.eq_one_iff _).2 ((mem_principalIdeles_iff _ _).2 ⟨d, rfl⟩)]
    exact mul_one β
  obtain ⟨kk, hkk, hmem⟩ := hβ _ hb

  obtain ⟨n, hn⟩ := hG.exists_card_eq
  obtain ⟨m, a, g, hm, hdvd, hg0, hIg⟩ := exists_pow_mul_pow_eq_span K p Fact.out n J hJ0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨t1, ht1⟩ := hdvd
  have htors := natCard_smul_mem_coboundaries₂ _ f'
  have hζmem : m' • (⇑f') ∈ coboundaries₂ (NumberField.SUnits.sUnitsRep E K S) := by
    have : m' = t1 * Nat.card (K ≃ₐ[E] K) := by rw [hn, mul_comm]; simpa using ht1
    rw [this, mul_smul]
    exact nsmul_mem htors t1
  obtain ⟨ζ, hζ⟩ := hζmem
  refine ⟨J, hJ0, kk, ζ, m', a, g, hg0, fun σ τ => hkk σ τ, fun σ τ => ?_, hIg, fun σ w hw => ?_⟩
  · have := congrFun hζ (σ, τ)
    rw [d₁₂_hom_apply] at this
    exact this.symm
  · exact count_spanSingleton_eq_of_mem E K S σ _ (kk σ) J hJ (hmem σ) w hw

end LayerData
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"
end N3Cap
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

section MainCard
open CategoryTheory groupCohomology NumberField.LevelArith NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.LevelArith NumberField.PlaceTransport nonZeroDivisors

local instance N3Cap.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance N3Cap.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance N3Cap.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
local instance N3Cap.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

namespace N3Cap

lemma fixingSubgroup_normal' (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [hF : Normal ℚ F] : F.fixingSubgroup.Normal := by
  refine ⟨fun s hs g => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hgx : g⁻¹ x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 hF g⁻¹) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hgx]
  simp

lemma levelGal_out_eq (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F]
    [Normal ↥L ↥(levelField L F hLF)] (g : ↥L.fixingSubgroup) :
    levelGal L F hLF (Quotient.out (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) = levelGal L F hLF g := by
  obtain ⟨-, hker⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L F hLF
  have h := QuotientGroup.mk_out_eq_mul (F.fixingSubgroup.comap L.fixingSubgroup.subtype) g
  obtain ⟨s, hs⟩ := h
  have hs1 : levelGal L F hLF (s : ↥L.fixingSubgroup) = 1 := by
    rw [← MonoidHom.mem_ker, hker]; exact s.2
  simp only [hs, map_mul, hs1, mul_one]

end N3Cap
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 25600000 in

theorem solution
    (p : ℕ) (S : Finset Nat.Primes) (hpS : ∃ q ∈ S, (q : ℕ) = p)
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (hF : F.IsUnramifiedOutside S)
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hιg : ∀ g : ↥L.fixingSubgroup,
      ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφ : Function.Bijective φ.hom)
    (hφval : ∀ x,
      ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) :
          ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : groupCohomology.cocycles₂
      ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (himg : (groupCohomology.map ι
        (φ ≫ NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) 2)
        (groupCohomology.H2π _ f) = 0) :
    ∃ (F' : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : F'.IsUnramifiedOutside S) (_ : IsGalois ℚ F') (_ : F ≤ F')
      (y : (↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) →
        (sUnitsMaxRep S L).quotientToInvariants (F'.fixingSubgroup.comap L.fixingSubgroup.subtype)),
      ∀ g h : ↥L.fixingSubgroup,
        ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
              (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
            (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L)
          = (sUnitsMaxRep S L).ρ g (y (h : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype))
            - (y ((g * h : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) :
                sUnitsMaxRep S L)
            + y (g : ↥L.fixingSubgroup ⧸ F'.fixingSubgroup.comap L.fixingSubgroup.subtype) := by
  classical

  obtain ⟨q, hqS, hqp⟩ := hpS
  haveI hp : Fact p.Prime := ⟨hqp ▸ q.2⟩
  haveI : IsGalois ↥L ↥(levelField L F hLF) := IsGalois.mk
  obtain ⟨hsurj, hker⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L F hLF
  have hιinj : Function.Injective ι := by
    intro σ τ h
    obtain ⟨g, rfl⟩ := hsurj σ
    obtain ⟨g', rfl⟩ := hsurj τ
    rw [hιg, hιg, QuotientGroup.eq, ← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at h
    exact h
  have hGal : IsPGroup p (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := hG.of_injective ι hιinj

  have hz : H2π (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
      (mapCocycles₂ ι (φ ≫ NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)) f) = 0 := by
    rw [← H2π_comp_map_apply]; exact himg
  rw [H2π_eq_zero_iff] at hz
  obtain ⟨u, hu⟩ := hz
  have hu' : ∀ σ τ : ↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF),
      (NumberField.SIdele.diag ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).hom (φ.hom (f (ι σ, ι τ))) =
      (NumberField.SIdele.obj ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)).ρ σ (u τ) - u (σ * τ) + u σ := by
    intro σ τ
    have := congrFun hu (σ, τ)
    rw [d₁₂_hom_apply] at this
    exact this.symm

  obtain ⟨J, hJ0, kk, ζ, m', a, g, hg0, hkk, hζ', hIg, hk⟩ := N3Cap.layer_data ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) p hGal
    (mapCocycles₂ ι φ f) u hu'

  have hpS' : ExtCitation.pPrime p ∈ S := by
    have : ExtCitation.pPrime p = q := Subtype.ext hqp.symm
    rw [this]; exact hqS
  set eKF : 𝓞 ↥(levelField L F hLF) ≃+* 𝓞 ↥F := NumberField.RingOfIntegers.mapRingEquiv (levelFieldEquiv L F hLF).symm with heKF
  have hIF : ((J ^ (m' + 1)).map (eKF : 𝓞 ↥(levelField L F hLF) →+* 𝓞 ↥F)) ^ p ^ a = Ideal.span {eKF g} := by
    rw [← Ideal.map_pow, hIg, Ideal.map_span, Set.image_singleton]; rfl
  have hg0' : eKF g ≠ 0 := (map_ne_zero_iff _ eKF.injective).2 hg0
  obtain ⟨F₁, hFF₁, hF₁, hprinc⟩ := NumberField.LevelArith.exists_isUnramifiedOutside_map_isPrincipal_of_pow_eq_span S hpS' F hF
    ((J ^ (m' + 1)).map (eKF : 𝓞 ↥(levelField L F hLF) →+* 𝓞 ↥F)) a (eKF g) hg0' hIF
  haveI : FiniteDimensional ℚ ↥F₁ := hF₁.1
  obtain ⟨hF'', hGal'', hFF'', hrest⟩ : ∃ (hF'' : (IntermediateField.normalClosure ℚ ↥F₁ (AlgebraicClosure ℚ)).IsUnramifiedOutside S)
      (_ : IsGalois ℚ ↥(IntermediateField.normalClosure ℚ ↥F₁ (AlgebraicClosure ℚ))) (_ : F ≤ IntermediateField.normalClosure ℚ ↥F₁ (AlgebraicClosure ℚ)), True := by
    exact ⟨hF₁.normalClosure, IsGalois.normalClosure ℚ (↥F₁) (AlgebraicClosure ℚ), hFF₁.trans (IntermediateField.le_normalClosure F₁), trivial⟩

  generalize hF''def : IntermediateField.normalClosure ℚ ↥F₁ (AlgebraicClosure ℚ) = F'' at hF'' hGal'' hFF''
  have hF₁F'' : F₁ ≤ F'' := hF''def ▸ IntermediateField.le_normalClosure F₁
  haveI : IsGalois ℚ ↥F'' := hGal''
  haveI : FiniteDimensional ℚ ↥F'' := hF''.1
  have hLF'' : L ≤ F'' := hLF.trans hFF''
  have hnorm'' : IsNormalLevel L F'' := fun g _ s hs => (N3Cap.fixingSubgroup_normal' F'').conj_mem s hs g
  haveI : Normal ↥L ↥(levelField L F'' hLF'') := NumberField.LevelArith.normal_levelField_of_isNormalLevel L F'' hLF'' hnorm''
  haveI : IsGalois ↥L ↥(levelField L F'' hLF'') := IsGalois.mk

  have hle : levelField L F hLF ≤ levelField L F'' hLF'' := fun x hx =>
    (IntermediateField.mem_extendScalars hLF'').2 (hFF'' ((IntermediateField.mem_extendScalars hLF).1 hx))
  letI algKK : Algebra ↥(levelField L F hLF) ↥(levelField L F'' hLF'') := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ↥L ↥(levelField L F hLF) ↥(levelField L F'' hLF'') :=
    IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion hle).commutes x).symm
  have halg : ∀ x : ↥(levelField L F hLF), ((algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') x : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) = x :=
    fun x => rfl

  set r : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) :=
    AlgEquiv.restrictNormalHom ↥(levelField L F hLF) with hrdef
  have hr : ∀ (σ : ↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) (x : ↥(levelField L F hLF)),
      σ (algebraMap _ _ x) = algebraMap _ _ (r σ x) := fun σ x => (AlgEquiv.restrictNormal_commutes σ _ x).symm
  have hrg : ∀ g : ↥L.fixingSubgroup, r (levelGal L F'' hLF'' g) = levelGal L F hLF g := by
    intro g
    apply AlgEquiv.ext; intro x; apply Subtype.ext
    rw [← halg ((r _) x), ← hr, levelGal_apply_coe, halg, levelGal_apply_coe]

  obtain ⟨t₁, ht₁⟩ := hprinc.principal
  set incl₂ : 𝓞 ↥F₁ →+* 𝓞 ↥F'' := NumberField.RingOfIntegers.mapRingHom (IntermediateField.inclusion hF₁F'').toRingHom with hincl₂
  set eFK : 𝓞 ↥F'' ≃+* 𝓞 ↥(levelField L F'' hLF'') := NumberField.RingOfIntegers.mapRingEquiv (levelFieldEquiv L F'' hLF'') with heFK
  set t : 𝓞 ↥(levelField L F'' hLF'') := eFK (incl₂ t₁) with htdef
  have hchain : algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF'')) =
      ((eFK : 𝓞 ↥F'' →+* 𝓞 ↥(levelField L F'' hLF'')).comp incl₂).comp
        ((NumberField.RingOfIntegers.mapRingHom (IntermediateField.inclusion hFF₁).toRingHom).comp
          (eKF : 𝓞 ↥(levelField L F hLF) →+* 𝓞 ↥F)) := by
    apply RingHom.ext; intro x; apply NumberField.RingOfIntegers.ext; apply Subtype.ext; rfl
  have ht : (J ^ (m' + 1)).map (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF''))) = Ideal.span {t} := by
    rw [hchain, ← Ideal.map_map, ← Ideal.map_map, ← Ideal.map_map, ht₁, Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton,
      Ideal.map_span, Set.image_singleton]
    rfl
  have ht0 : t ≠ 0 := by
    intro h0
    have h1 : ((J ^ (m' + 1)).map (algebraMap (𝓞 ↥(levelField L F hLF)) (𝓞 ↥(levelField L F'' hLF'')))) = ⊥ := by
      rw [ht, h0, Ideal.span_singleton_eq_bot]
    rw [Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h1
    exact pow_ne_zero _ hJ0 h1

  set ηv : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) → ↥(levelField L F'' hLF'') := fun σ =>
    (algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'') (kk (r σ) : ↥(levelField L F hLF))) ^ (m' + 1) * σ (t : ↥(levelField L F'' hLF'')) / (t : ↥(levelField L F'' hLF'')) *
      (algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'')
        (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (ζ (r σ)) : ↥(levelField L F hLF)))⁻¹ with hηv
  have htL : (t : ↥(levelField L F'' hLF'')) ≠ 0 := by exact_mod_cast ht0
  have hιinj' : Function.Injective (algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'')) := (algebraMap ↥(levelField L F hLF) ↥(levelField L F'' hLF'')).injective
  have hηv0 : ∀ σ, ηv σ ≠ 0 := by
    intro σ
    simp only [hηv]
    refine mul_ne_zero (div_ne_zero (mul_ne_zero (pow_ne_zero _ ?_) ((map_ne_zero σ).2 htL)) htL) (inv_ne_zero ?_)
    · exact (map_ne_zero_iff _ hιinj').2 (Units.ne_zero _)
    · exact (map_ne_zero_iff _ hιinj').2 (Units.ne_zero _)
  have hηval : ∀ σ (W : HeightOneSpectrum (𝓞 ↥(levelField L F'' hLF''))), W.under (𝓞 ↥L) ∉ placesOverPrimesFinset ↥L S →
      W.valuation ↥(levelField L F'' hLF'') (ηv σ) = 1 := by
    intro σ W hW
    simp only [hηv]
    rw [map_mul, N3Cap.valuation_eta_eq_one (placesOverPrimesFinset ↥L S) σ (r σ) (hr σ) J hJ0 (m' + 1) t ht0 ht (kk (r σ)) (hk (r σ)) W hW,
      one_mul, map_inv₀, N3Cap.valuation_algebraMap_eq_pow, N3Cap.valuation_eq_one_of_mem_sUnits ↥L ↥(levelField L F hLF)
        (placesOverPrimesFinset ↥L S) (NumberField.SUnits.val_mem _ _ _ (ζ (r σ))) _ (by rwa [N3Cap.under_under_ringOfIntegers]),
      one_pow, inv_one]
  set ηS : (↥(levelField L F'' hLF'') ≃ₐ[↥L] ↥(levelField L F'' hLF'')) →
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) := fun σ =>
    ⟨Additive.ofMul (Units.mk0 (ηv σ) (hηv0 σ)),
      (NumberField.SUnits.mem_sUnitsSubmodule _ _ _ _).2 (N3Cap.mem_sUnits_of_forall_valuation_eq_one ↥L ↥(levelField L F'' hLF'')
        (placesOverPrimesFinset ↥L S) _ (hηval σ))⟩ with hηS
  have hηSval : ∀ σ, ((NumberField.SUnits.val ↥L ↥(levelField L F'' hLF'') (placesOverPrimesFinset ↥L S) (ηS σ) : (↥(levelField L F'' hLF''))ˣ) : ↥(levelField L F'' hLF'')) = ηv σ :=
    fun σ => rfl

  obtain ⟨e'', he''val, -⟩ := NumberField.LevelArith.exists_addEquiv_quotientToInvariants_sUnitsMaxRep_sUnitsRep S L F'' hLF'' hF''
  refine ⟨F'', hF'', hGal'', hFF'', fun qq => e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out qq))), fun g h => ?_⟩

  have hvalinj : ∀ z₁ z₂ : sUnitsMaxRep S L,
      ((sUnitsMaxRep.val S L z₁ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((sUnitsMaxRep.val S L z₂ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) → z₁ = z₂ :=
    fun z₁ z₂ hz => Subtype.ext (Additive.toMul.injective (Units.ext hz))
  apply hvalinj

  have hY : ∀ k : ↥L.fixingSubgroup,
      ((sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF''
        (Quotient.out (k : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype))))).1 : sUnitsMaxRep S L) :
        (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((ηv (levelGal L F'' hLF'' k) : ↥(levelField L F'' hLF'')) : AlgebraicClosure ℚ) := by
    intro k
    rw [← he''val, AddEquiv.apply_symm_apply, N3Cap.levelGal_out_eq]
    rfl

  have hL : ((sUnitsMaxRep.val S L ((f ((g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
      (h : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) : (sUnitsMaxRep S L).quotientToInvariants _) : sUnitsMaxRep S L) :
        (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom (f (ι (levelGal L F hLF g), ι (levelGal L F hLF h)))) :
        ↥(levelField L F hLF)) : AlgebraicClosure ℚ) := by
    rw [hιg, hιg]; exact (hφval (f (_, _))).symm

  have hR : ((sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ g
      ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out ((h : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L)
      - ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out (((g * h : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L)
      + ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out ((g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L)) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
      = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          ((sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out ((h : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        * (((sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out (((g * h : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))⁻¹
        * ((sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out ((g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
    show ((((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) •
        sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out ((h : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L)
        / sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out (((g * h : ↥L.fixingSubgroup) : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L)
        * sUnitsMaxRep.val S L ((e''.symm (ηS (levelGal L F'' hLF'' (Quotient.out ((g : ↥L.fixingSubgroup ⧸ F''.fixingSubgroup.comap L.fixingSubgroup.subtype)))))).1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) = _
    rw [Units.val_mul, Units.val_div_eq_div_val, AlgEquiv.smul_units_def, Units.coe_map, div_eq_mul_inv]
    rfl
  rw [hL, hR, hY h, hY (g * h), hY g, map_mul, ← levelGal_apply_coe L F'' hLF'' g]

  have hcoe : ∀ x : ↥(levelField L F'' hLF''), (x : AlgebraicClosure ℚ) = algebraMap ↥(levelField L F'' hLF'') (AlgebraicClosure ℚ) x := fun x => rfl
  rw [hcoe, hcoe, hcoe, ← map_inv₀, ← map_mul, ← map_mul, ← halg, hcoe]
  congr 1

  have hde := N3Cap.d_eta (E := ↥L) r hr
    (fun στ => (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom (f (ι στ.1, ι στ.2))) : ↥(levelField L F hLF)))
    (fun σ => (kk σ : ↥(levelField L F hLF)))
    (fun σ => (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (ζ σ) : ↥(levelField L F hLF)))
    (fun σ => Units.ne_zero _) (fun σ => Units.ne_zero _) m' ?_ ?_ t htL (levelGal L F'' hLF'' g) (levelGal L F'' hLF'' h)
  · rw [hrg, hrg] at hde
    exact hde.symm
  ·
    intro σ τ
    have h1 := congrArg (fun u : (↥(levelField L F hLF))ˣ => (u : ↥(levelField L F hLF))) (hkk σ τ)
    simp only [Units.val_mul, Units.val_inv_eq_inv_val, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe] at h1
    change (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ((mapCocycles₂ ι φ f) (σ, τ)) : ↥(levelField L F hLF)) * _ = _
    rw [h1]
    field_simp
  ·
    intro σ τ
    have h1 := hζ' σ τ
    rw [sub_add_eq_add_sub, eq_sub_iff_add_eq, ← natCast_zsmul] at h1
    have h2 := congrArg (fun z => ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) z : (↥(levelField L F hLF))ˣ) : ↥(levelField L F hLF))) h1
    exact h2

end MainCard
p2m_reactivate "P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep.N3Cap"

end S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep
end P2MW
export P2MW.S_NumberField_LevelArith_exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep (solution)
