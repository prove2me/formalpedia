-- Prove2me | solution 1 for NumberField.IdeleLocalInv.map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/882d7515-cbb3-511b-a148-96fd75ab6b2a

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside

import Definitions.Def_GroupCohomology_RepCokernel
import Theorems.Thm_GroupCohomology_RepCokernel_seq_shortExact
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
import Theorems.Thm_NumberField_AdeleRing_finiteIndex_principalIdeles_sup_unitIdelesOutside
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_M4aHerbrand_Bridge_valued_finiteConorm_apply_and_finprod_pow_eq
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation
set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
p2m_open "CategoryTheory groupCohomology NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField IsDedekindDomain M4aHerbrand"
open M4aHerbrand.GenuineDescent
open scoped NumberField.PlaceDecomp

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk place RingOfIntegers AdeleRing RingOfIntegers.algebraMap.injective AdeleRing.unitIdelesOutside AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside"
namespace IdeleLocalInv
namespace CapKillArith
p2m_open "NumberField.IdeleLocalInv NumberField"

open scoped nonZeroDivisors

section ClassMap
variable {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S] (f : R →+* S) (hf : Function.Injective f)

include hf in
private theorem map_mem_nonZeroDivisors (I : (Ideal R)⁰) : (I : Ideal R).map f ∈ (Ideal S)⁰ := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  intro h
  have hI : (I : Ideal R) ≠ ⊥ := mem_nonZeroDivisors_iff_ne_zero.mp I.2
  exact hI ((Ideal.map_eq_bot_iff_of_injective hf).mp h)

private noncomputable def mapIdeal0 (I : (Ideal R)⁰) : (Ideal S)⁰ := ⟨(I : Ideal R).map f, map_mem_nonZeroDivisors f hf I⟩

private theorem coe_mapIdeal0 (I : (Ideal R)⁰) : ((mapIdeal0 f hf I : (Ideal S)⁰) : Ideal S) = (I : Ideal R).map f := rfl

include hf in
private theorem mk0_map_eq_of_mk0_eq {I J : (Ideal R)⁰} (h : ClassGroup.mk0 I = ClassGroup.mk0 J) :
    ClassGroup.mk0 (mapIdeal0 f hf I) = ClassGroup.mk0 (mapIdeal0 f hf J) := by
  rw [ClassGroup.mk0_eq_mk0_iff] at h ⊢
  obtain ⟨x, y, hx, hy, hxy⟩ := h
  refine ⟨f x, f y, fun h0 => hx (hf (by rw [h0, map_zero])), fun h0 => hy (hf (by rw [h0, map_zero])), ?_⟩
  have := congrArg (Ideal.map f) hxy
  rwa [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at this

private noncomputable def classMap : ClassGroup R →* ClassGroup S where
  toFun c := ClassGroup.mk0 (mapIdeal0 f hf (Classical.choose (ClassGroup.mk0_surjective c)))
  map_one' := by
    have h1 : ClassGroup.mk0 (Classical.choose (ClassGroup.mk0_surjective (1 : ClassGroup R))) = ClassGroup.mk0 (1 : (Ideal R)⁰) := by
      rw [Classical.choose_spec (ClassGroup.mk0_surjective (1 : ClassGroup R)), map_one]
    rw [mk0_map_eq_of_mk0_eq f hf h1]
    have : mapIdeal0 f hf (1 : (Ideal R)⁰) = 1 := Subtype.ext (by rw [coe_mapIdeal0]; simp [Ideal.map_top])
    rw [this, map_one]
  map_mul' c c' := by
    have hcc : ClassGroup.mk0 (Classical.choose (ClassGroup.mk0_surjective (c * c'))) =
        ClassGroup.mk0 (Classical.choose (ClassGroup.mk0_surjective c) * Classical.choose (ClassGroup.mk0_surjective c')) := by
      rw [map_mul, Classical.choose_spec (ClassGroup.mk0_surjective c), Classical.choose_spec (ClassGroup.mk0_surjective c'),
        Classical.choose_spec (ClassGroup.mk0_surjective (c * c'))]
    rw [mk0_map_eq_of_mk0_eq f hf hcc, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [coe_mapIdeal0, Submonoid.coe_mul, Ideal.map_mul]

private theorem classMap_mk0 (I : (Ideal R)⁰) : classMap f hf (ClassGroup.mk0 I) = ClassGroup.mk0 (mapIdeal0 f hf I) := by
  show ClassGroup.mk0 (mapIdeal0 f hf (Classical.choose (ClassGroup.mk0_surjective (ClassGroup.mk0 I)))) = _
  exact mk0_map_eq_of_mk0_eq f hf (Classical.choose_spec (ClassGroup.mk0_surjective (ClassGroup.mk0 I)))

end ClassMap

private theorem exists_mul_of_pow_mem {G : Type*} [CommGroup G] [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G)
    (c : G) (k : ℕ) (hck : c ^ p ^ k ∈ H) :
    ∃ c₁ h : G, c = c₁ * h ∧ (∃ j : ℕ, c₁ ^ p ^ j = 1) ∧ h ∈ H := by
  classical
  by_cases hk : k = 0
  · subst hk
    exact ⟨1, c, by rw [one_mul], ⟨0, one_pow _⟩, by simpa using hck⟩

  obtain ⟨a, m, hm, hG⟩ : ∃ a m : ℕ, ¬ p ∣ m ∧ Nat.card G = p ^ a * m :=
    ⟨(Nat.card G).factorization p, Nat.card G / p ^ (Nat.card G).factorization p,
      Nat.not_dvd_ordCompl hp Nat.card_pos.ne', (Nat.ordProj_mul_ordCompl_eq_self _ _).symm⟩

  have hcop : Nat.Coprime m (p ^ k) := Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm
  obtain ⟨w, -, hw⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (Nat.one_lt_pow hk hp.one_lt)
  set q := m * w / p ^ k with hq
  have hmw : m * w = 1 + p ^ k * q := by
    have h0 := Nat.mod_add_div (m * w) (p ^ k)
    rw [hw] at h0
    rw [hq]
    exact h0.symm
  have hcG : c ^ (p ^ a * m) = 1 := by rw [← hG]; exact pow_card_eq_one'
  refine ⟨c ^ (m * w), ((c ^ p ^ k) ^ q)⁻¹, ?_, ⟨a, ?_⟩, H.inv_mem (H.pow_mem hck q)⟩
  · rw [hmw, pow_add, pow_one, pow_mul, mul_inv_cancel_right]
  · rw [← pow_mul, show m * w * p ^ a = (p ^ a * m) * w by ring, pow_mul, hcG, one_pow]

end NumberField.IdeleLocalInv.CapKillArith

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk place RingOfIntegers AdeleRing RingOfIntegers.algebraMap.injective AdeleRing.unitIdelesOutside AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside"
namespace IdeleLocalInv
namespace CapKillArith
p2m_open "NumberField.IdeleLocalInv NumberField"

open scoped nonZeroDivisors

section Classes
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

private noncomputable def ideal0 (v : HeightOneSpectrum R) : (Ideal R)⁰ := ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 v.ne_bot⟩

@[scoped simp] private theorem coe_ideal0 (v : HeightOneSpectrum R) : ((ideal0 R v : (Ideal R)⁰) : Ideal R) = v.asIdeal := rfl

private theorem mk_eq_finprod_of_coe_eq {ι : Type*} (U : (FractionalIdeal R⁰ K)ˣ) (u : ι → (FractionalIdeal R⁰ K)ˣ) (n : ι → ℤ)
    (hfin : {i | n i ≠ 0}.Finite) (h : (U : FractionalIdeal R⁰ K) = ∏ᶠ i, (u i : FractionalIdeal R⁰ K) ^ n i) :
    ClassGroup.mk K U = ∏ᶠ i, ClassGroup.mk K (u i) ^ n i := by
  have hsupp : (Function.mulSupport fun i => u i ^ n i).Finite := by
    refine hfin.subset fun i hi => ?_
    intro h0
    exact hi (by simp [h0])
  have hU : U = ∏ᶠ i, u i ^ n i := by
    apply Units.ext
    rw [h, show ((∏ᶠ i, u i ^ n i : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      ∏ᶠ i, ((u i ^ n i : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) from (Units.coeHom (FractionalIdeal R⁰ K)).map_finprod hsupp]
    simp only [Units.val_zpow_eq_zpow_val]
  have hsupp' : (Function.mulSupport fun i => ClassGroup.mk K (u i) ^ n i).Finite := by
    refine hfin.subset fun i hi => ?_
    intro h0
    exact hi (by simp [h0])
  rw [hU, MonoidHom.map_finprod _ hsupp]
  simp only [map_zpow]

private theorem mk_mk0_ideal0 (v : HeightOneSpectrum R) :
    ClassGroup.mk K (FractionalIdeal.mk0 K (ideal0 R v)) = ClassGroup.mk0 (ideal0 R v) := ClassGroup.mk_mk0 K _

include K in

private theorem mk0_mem_of_forall_dvd (H : Subgroup (ClassGroup R)) (J : (Ideal R)⁰)
    (hJ : ∀ w : HeightOneSpectrum R, w.asIdeal ∣ (J : Ideal R) → ClassGroup.mk0 (ideal0 R w) ∈ H) :
    ClassGroup.mk0 J ∈ H := by
  classical
  have hJ0 : ((J : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
    exact mem_nonZeroDivisors_iff_ne_zero.1 J.2
  have hJ0' : (J : Ideal R) ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.1 J.2

  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ0
  have hfin : {w : HeightOneSpectrum R | FractionalIdeal.count K w ((J : Ideal R) : FractionalIdeal R⁰ K) ≠ 0}.Finite :=
    (FractionalIdeal.finite_factors ((J : Ideal R) : FractionalIdeal R⁰ K))
  have hmk := mk_eq_finprod_of_coe_eq R K (FractionalIdeal.mk0 K J) (fun w => FractionalIdeal.mk0 K (ideal0 R w))
    (fun w => FractionalIdeal.count K w ((J : Ideal R) : FractionalIdeal R⁰ K)) hfin
    (by rw [FractionalIdeal.coe_mk0]; exact hfac.symm.trans (finprod_congr fun w => by rw [FractionalIdeal.coe_mk0]; rfl))
  rw [← ClassGroup.mk_mk0 K, hmk]
  refine finprod_induction (fun c => c ∈ H) H.one_mem (fun _ _ => H.mul_mem) fun w => ?_
  by_cases hc : FractionalIdeal.count K w ((J : Ideal R) : FractionalIdeal R⁰ K) = 0
  · rw [hc, zpow_zero]; exact H.one_mem
  · refine H.zpow_mem ?_ _
    rw [mk_mk0_ideal0]
    apply hJ
    rw [FractionalIdeal.count_coe K w hJ0'] at hc
    exact (Associates.count_ne_zero_iff_dvd hJ0' w.irreducible).1 (by exact_mod_cast hc)

end Classes

section FiniteIdele
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

private theorem finite_valued_ne_one (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | Valued.v ((x : FiniteAdeleRing R K) v) ≠ 1}.Finite := by
  have h1 : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, (x : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    (x : FiniteAdeleRing R K).2
  have h2 : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v ∈ v.adicCompletionIntegers K :=
    ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K).2
  have h3 : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, Valued.v ((x : FiniteAdeleRing R K) v) = 1 := by
    filter_upwards [h1, h2] with v hv hv'
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hv hv'
    have hmul : (x : FiniteAdeleRing R K) v * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v = 1 := by
      have e : ((x : FiniteAdeleRing R K) * ((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K)) v = (1 : FiniteAdeleRing R K) v := by
        rw [x.mul_inv]
      exact e
    have hvm := congrArg Valued.v hmul
    rw [map_mul, map_one] at hvm
    apply le_antisymm hv
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v ((x : FiniteAdeleRing R K) v) * Valued.v (((x⁻¹ : (FiniteAdeleRing R K)ˣ) : FiniteAdeleRing R K) v) := hvm.symm
      _ ≤ Valued.v ((x : FiniteAdeleRing R K) v) * 1 := mul_le_mul_right hv' _
      _ = Valued.v ((x : FiniteAdeleRing R K) v) := mul_one _
  exact Filter.eventually_cofinite.1 h3

private theorem finite_log_valued_ne_zero (x : (FiniteAdeleRing R K)ˣ) :
    {v : HeightOneSpectrum R | -(WithZero.log (Valued.v ((x : FiniteAdeleRing R K) v))) ≠ 0}.Finite := by
  refine (finite_valued_ne_one R K x).subset fun v hv => ?_
  intro h1
  apply hv
  simp [h1]

end FiniteIdele

end NumberField.IdeleLocalInv.CapKillArith
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv"
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk place RingOfIntegers AdeleRing RingOfIntegers.algebraMap.injective AdeleRing.unitIdelesOutside AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside"
namespace IdeleLocalInv
namespace CapKillArith
p2m_open "NumberField.IdeleLocalInv NumberField"

open scoped nonZeroDivisors

section FinitePart
variable (R : Type*) [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [NumberField K] [Algebra R K] [IsFractionRing R K]

private noncomputable abbrev fin : (AdeleRing R K)ˣ →* (FiniteAdeleRing R K)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing R K)).toMonoidHom

private theorem fin_principal (a : Kˣ) :
    fin R K (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) a) =
      Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K) a := Units.ext rfl

private theorem mem_sup_iff_fin_mem_sup (T : Set (HeightOneSpectrum R)) (w : (AdeleRing R K)ˣ) :
    w ∈ principalIdeles R K ⊔ NumberField.AdeleRing.unitIdelesOutside R K T ↔
      fin R K w ∈ (Units.map (algebraMap K (FiniteAdeleRing R K) : K →* FiniteAdeleRing R K)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T := by
  constructor
  · intro hw
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := hy
    rw [map_mul]
    exact Subgroup.mul_mem_sup ⟨a, (fin_principal R K a).symm⟩ hz
  · intro hw
    obtain ⟨y, ⟨a, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup.mp hw
    refine Subgroup.mem_sup.mpr ⟨Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) a, ⟨a, rfl⟩,
      (Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) a)⁻¹ * w, ?_, mul_inv_cancel_left _ _⟩
    show fin R K ((Units.map (algebraMap K (AdeleRing R K) : K →* AdeleRing R K) a)⁻¹ * w) ∈ IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside R K T
    rw [map_mul, map_inv, fin_principal, ← hyz, inv_mul_cancel_left]
    exact hz

end FinitePart
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"

private theorem units_map_β_mem_sup_of_pow_mem_sup
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K'']
    (S : Finset (HeightOneSpectrum (𝓞 E))) (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)
    (w : (AdeleRing (𝓞 K) K)ˣ) (k : ℕ)
    (hw : w ^ p ^ k ∈ principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {v | v.under (𝓞 E) ∈ S}) :
    Units.map (genuineBaseChange K K'').β.toMonoidHom w ∈
      principalIdeles (𝓞 K'') K'' ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K'') K'' {v | v.under (𝓞 E) ∈ S} := by
  classical

  rw [mem_sup_iff_fin_mem_sup]
  set x : (FiniteAdeleRing (𝓞 K) K)ˣ := fin (𝓞 K) K w with hx
  have hxk : x ^ p ^ k ∈ (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K) : K →* FiniteAdeleRing (𝓞 K) K)).range ⊔
      IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 K) K {v | v.under (𝓞 E) ∈ S} := by
    rw [hx, ← map_pow]; exact (mem_sup_iff_fin_mem_sup (𝓞 K) K _ _).mp hw
  have hβ : fin (𝓞 K'') K'' (Units.map (genuineBaseChange K K'').β.toMonoidHom w) =
      Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K K'' (𝓞 K'')).toMonoidHom x := Units.ext rfl
  rw [hβ]

  obtain ⟨φ₁, hφ₁, -, -, -, hcrit₁⟩ := IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff (𝓞 K) K
  obtain ⟨φ₂, hφ₂, -, -, -, hcrit₂⟩ := IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff (𝓞 K'') K''
  have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 K'')) := RingOfIntegers.algebraMap.injective K K''
  let cm : ClassGroup (𝓞 K) →* ClassGroup (𝓞 K'') := classMap (algebraMap (𝓞 K) (𝓞 K'')) hinj

  set e : HeightOneSpectrum (𝓞 K) → ℤ := fun v => -(WithZero.log (Valued.v ((x : (FiniteAdeleRing (𝓞 K) K)) v))) with he
  have hefin : {v | e v ≠ 0}.Finite := finite_log_valued_ne_zero (𝓞 K) K x
  have hc1 : ClassGroup.mk K (φ₁ x) = ∏ᶠ v, ClassGroup.mk0 (ideal0 (𝓞 K) v) ^ e v := by
    rw [mk_eq_finprod_of_coe_eq (𝓞 K) K (φ₁ x) (fun v => FractionalIdeal.mk0 K (ideal0 (𝓞 K) v)) e hefin
      (by rw [hφ₁ x]; exact finprod_congr fun v => by rw [FractionalIdeal.coe_mk0]; rfl)]
    exact finprod_congr fun v => by rw [mk_mk0_ideal0]
  have hc2 : ClassGroup.mk K'' (φ₂ (Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K K'' (𝓞 K'')).toMonoidHom x)) =
      cm (ClassGroup.mk K (φ₁ x)) := by
    have hb := (M4aHerbrand.Bridge.valued_finiteConorm_apply_and_finprod_pow_eq (𝓞 K) K K'' (𝓞 K'') x).2
    have hval : (φ₂ (Units.map (M4aHerbrand.Bridge.finiteConorm (𝓞 K) K K'' (𝓞 K'')).toMonoidHom x) : FractionalIdeal (𝓞 K'')⁰ K'') =
        ∏ᶠ v, ((FractionalIdeal.mk0 K'' (mapIdeal0 (algebraMap (𝓞 K) (𝓞 K'')) hinj (ideal0 (𝓞 K) v)) : (FractionalIdeal (𝓞 K'')⁰ K'')ˣ) :
          FractionalIdeal (𝓞 K'')⁰ K'') ^ e v := by
      rw [hφ₂, hb]
      exact finprod_congr fun v => by rw [FractionalIdeal.coe_mk0]; rfl
    rw [mk_eq_finprod_of_coe_eq (𝓞 K'') K'' _ _ e hefin hval, hc1]
    have hsupp : (Function.mulSupport fun v => ClassGroup.mk0 (ideal0 (𝓞 K) v) ^ e v).Finite := by
      refine hefin.subset fun v hv => ?_
      intro h0
      exact hv (by simp [h0])
    rw [MonoidHom.map_finprod _ hsupp]
    refine finprod_congr fun v => ?_
    rw [map_zpow, ClassGroup.mk_mk0, classMap_mk0]

  have hkill : ∀ c : ClassGroup (𝓞 K), (∃ j : ℕ, c ^ p ^ j = 1) → cm c = 1 := by
    rintro c ⟨j, hj⟩
    obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective c
    rw [← map_pow, show I ^ p ^ j = ⟨(I : Ideal (𝓞 K)) ^ p ^ j, (I ^ p ^ j).2⟩ from rfl, ClassGroup.mk0_eq_one_iff] at hj
    obtain ⟨a, ha⟩ := hj
    have ha' : (I : Ideal (𝓞 K)) ^ p ^ j = Ideal.span {a} := ha
    have ha0 : a ≠ 0 := by
      intro h0
      have : ((I ^ p ^ j : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = 0 := by
        show (I : Ideal (𝓞 K)) ^ p ^ j = 0
        rw [ha', h0, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.zero_eq_bot]
      exact mem_nonZeroDivisors_iff_ne_zero.mp (I ^ p ^ j).2 this
    have hprin := hcap (I : Ideal (𝓞 K)) j a ha0 ha'
    rw [show cm (ClassGroup.mk0 I) = ClassGroup.mk0 (mapIdeal0 (algebraMap (𝓞 K) (𝓞 K'')) hinj I) from classMap_mk0 _ hinj I]
    exact (ClassGroup.mk0_eq_one_iff _).mpr hprin

  have hmem1 := (hcrit₁ {v | v.under (𝓞 E) ∈ S} (x ^ p ^ k)).1 hxk
  rw [map_pow, map_pow] at hmem1
  obtain ⟨c₁, hh, hc, ⟨j, hj⟩, hhmem⟩ := exists_mul_of_pow_mem (Fact.out : p.Prime) _ (ClassGroup.mk K (φ₁ x)) k hmem1

  rw [hcrit₂, hc2, hc, map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  · rw [hkill c₁ ⟨j, hj⟩]
    exact Subgroup.one_mem _
  ·
    have hle : (Subgroup.closure {c : ClassGroup (𝓞 K) | ∃ v ∈ {v : HeightOneSpectrum (𝓞 K) | v.under (𝓞 E) ∈ S},
        ∃ h0 : v.asIdeal ∈ (Ideal (𝓞 K))⁰, ClassGroup.mk0 ⟨v.asIdeal, h0⟩ = c}).map cm ≤
        Subgroup.closure {c : ClassGroup (𝓞 K'') | ∃ v ∈ {v : HeightOneSpectrum (𝓞 K'') | v.under (𝓞 E) ∈ S},
          ∃ h0 : v.asIdeal ∈ (Ideal (𝓞 K''))⁰, ClassGroup.mk0 ⟨v.asIdeal, h0⟩ = c} := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_le _ |>.2
      rintro _ ⟨c', ⟨v, hvT, hv0, rfl⟩, rfl⟩
      rw [show (⟨v.asIdeal, hv0⟩ : (Ideal (𝓞 K))⁰) = ideal0 (𝓞 K) v from rfl, classMap_mk0]
      apply mk0_mem_of_forall_dvd (𝓞 K'') K'' _ (mapIdeal0 (algebraMap (𝓞 K) (𝓞 K'')) hinj (ideal0 (𝓞 K) v))
      intro w'' hw
      apply Subgroup.subset_closure
      refine ⟨w'', ?_, (ideal0 (𝓞 K'') w'').2, rfl⟩

      have hle := Ideal.le_of_dvd hw
      rw [coe_mapIdeal0, coe_ideal0] at hle
      have hunder : w''.under (𝓞 K) = v := by
        apply HeightOneSpectrum.ext
        rw [HeightOneSpectrum.under_asIdeal]
        exact (v.isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) (Ideal.map_le_iff_le_comap.mp hle)).symm
      show w''.under (𝓞 E) ∈ S
      have : w''.under (𝓞 E) = (w''.under (𝓞 K)).under (𝓞 E) := by
        apply HeightOneSpectrum.ext
        rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.under_under]
      rw [this, hunder]
      exact hvT
    exact hle ⟨hh, hhmem, rfl⟩

end NumberField.IdeleLocalInv.CapKillArith
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"

namespace NumberField
p2m_export "NumberField" "InfiniteAdeleRing mk place RingOfIntegers AdeleRing RingOfIntegers.algebraMap.injective AdeleRing.unitIdelesOutside AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside"
namespace IdeleLocalInv
namespace CapKill
p2m_open "NumberField.IdeleLocalInv NumberField"

private theorem exists_delta_eq_of_map_eq_zero {G : Type} [Group G] {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) (i j : ℕ) (hij : i + 1 = j)
    (u : groupCohomology X.X₁ j) (hu : (groupCohomology.map (MonoidHom.id G) X.f j).hom u = 0) :
    ∃ c : groupCohomology X.X₃ i, (groupCohomology.δ hX i j hij).hom c = u := by

  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).1 (groupCohomology.mapShortComplex₁_exact hX hij) u hu
  exact ⟨c, hc⟩

private theorem delta_natural {G G'' : Type} [Group G] [Group G''] (r : G'' →* G)
    {X : ShortComplex (Rep ℤ G)} (hX : X.ShortExact) {Y : ShortComplex (Rep ℤ G'')} (hY : Y.ShortExact)
    (φ₁ : Rep.res r X.X₁ ⟶ Y.X₁) (φ₂ : Rep.res r X.X₂ ⟶ Y.X₂) (φ₃ : Rep.res r X.X₃ ⟶ Y.X₃)
    (h12 : (Rep.resFunctor r).map X.f ≫ φ₂ = φ₁ ≫ Y.f) (h23 : (Rep.resFunctor r).map X.g ≫ φ₃ = φ₂ ≫ Y.g)
    (i j : ℕ) (hij : i + 1 = j) (c : groupCohomology X.X₃ i) :
    (groupCohomology.δ hY i j hij).hom ((groupCohomology.map r φ₃ i).hom c) =
      (groupCohomology.map r φ₁ j).hom ((groupCohomology.δ hX i j hij).hom c) := by

  let Φ : X.map (groupCohomology.cochainsFunctor ℤ G) ⟶ Y.map (groupCohomology.cochainsFunctor ℤ G'') :=
    { τ₁ := groupCohomology.cochainsMap r φ₁
      τ₂ := groupCohomology.cochainsMap r φ₂
      τ₃ := groupCohomology.cochainsMap r φ₃
      comm₁₂ := by
        change groupCohomology.cochainsMap r φ₁ ≫ groupCohomology.cochainsMap (MonoidHom.id G'') Y.f =
          groupCohomology.cochainsMap (MonoidHom.id G) X.f ≫ groupCohomology.cochainsMap r φ₂
        rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
        exact congrArg (groupCohomology.cochainsMap r) h12.symm
      comm₂₃ := by
        change groupCohomology.cochainsMap r φ₂ ≫ groupCohomology.cochainsMap (MonoidHom.id G'') Y.g =
          groupCohomology.cochainsMap (MonoidHom.id G) X.g ≫ groupCohomology.cochainsMap r φ₃
        rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
        exact congrArg (groupCohomology.cochainsMap r) h23.symm }
  have nat := HomologicalComplex.HomologySequence.δ_naturality Φ (groupCohomology.map_cochainsFunctor_shortExact hX)
    (groupCohomology.map_cochainsFunctor_shortExact hY) i j hij
  have happ := congrArg (fun T => (ModuleCat.Hom.hom T) c) nat
  exact happ.symm

private theorem exists_pPrimary_preimage {A B : Type} [AddCommGroup A] [AddCommGroup B] (f : A →+ B) (p : ℕ) (hp : p.Prime)
    (N : ℕ) (hN : 0 < N) (c : A) (hc : (N : ℤ) • c = 0) (k : ℕ) (hk : (p ^ k : ℤ) • f c = 0) :
    ∃ (c' : A) (a : ℕ), (p ^ a : ℤ) • c' = 0 ∧ f c' = f c := by
  classical
  obtain ⟨a, m, hm, hNeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' p hp.one_lt.ne'
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm))
  obtain ⟨α, β, hαβ⟩ := hcop
  have hαβ' : α * (p ^ k : ℤ) + β * (m : ℤ) = 1 := by push_cast at hαβ; exact hαβ
  refine ⟨(β * (m : ℤ)) • c, a, ?_, ?_⟩
  · rw [smul_smul, show (p ^ a : ℤ) * (β * (m : ℤ)) = β * (N : ℤ) by rw [hNeq]; push_cast; ring, ← smul_smul, hc, zsmul_zero]
  · rw [map_zsmul]
    have h2 : (α * (p ^ k : ℤ)) • f c = 0 := by rw [← smul_smul, hk, zsmul_zero]
    calc (β * (m : ℤ)) • f c = (α * (p ^ k : ℤ)) • f c + (β * (m : ℤ)) • f c := by rw [h2, zero_add]
      _ = (α * (p ^ k : ℤ) + β * (m : ℤ)) • f c := (add_zsmul _ _ _).symm
      _ = f c := by rw [hαβ', one_zsmul]

private theorem map_eq_zero_of_forall_torsion_eq_zero {G G'' : Type} [Group G] [Finite G] [Group G''] (r : G'' →* G)
    {Q : Rep ℤ G} [Finite Q] {Q'' : Rep ℤ G''} (φ : Rep.res r Q ⟶ Q'') (p : ℕ) (hp : p.Prime)
    (hφ : ∀ q : Q, (∃ k : ℕ, (p ^ k : ℤ) • q = 0) → φ.hom q = 0)
    (n : ℕ) (c : groupCohomology Q (n + 1)) (k : ℕ) (hc : (p ^ k : ℤ) • c = 0) :
    (groupCohomology.map r φ (n + 1)).hom c = 0 := by
  classical

  have hQ0 : Nat.card Q ≠ 0 := Nat.card_pos.ne'
  obtain ⟨a, m, hm, hQeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hQ0 p hp.one_lt.ne'
  have hcop : IsCoprime ((p ^ k : ℕ) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hm))
  obtain ⟨α, β, hαβ⟩ := hcop
  have hαβ' : α * (p ^ k : ℤ) + β * (m : ℤ) = 1 := by push_cast at hαβ; exact hαβ

  have hmq : ∀ q : Q, φ.hom ((m : ℤ) • q) = 0 := fun q => hφ _ ⟨a, by
    rw [smul_smul, show (p ^ a : ℤ) * (m : ℤ) = (Nat.card Q : ℤ) by rw [hQeq]; push_cast; ring, natCast_zsmul]
    exact card_nsmul_eq_zero'⟩

  obtain ⟨z, rfl⟩ : ∃ z, (groupCohomology.π Q (n + 1)).hom z = c :=
    groupCohomology_induction_on (C := fun x => ∃ z, (groupCohomology.π Q (n + 1)).hom z = x) c (fun z => ⟨z, rfl⟩)
  have hz : groupCohomology.cocyclesMap r φ (n + 1) ((m : ℤ) • z) = 0 := by
    apply (ModuleCat.mono_iff_injective (iCocycles Q'' (n + 1))).1 inferInstance
    rw [map_zero]
    have hi := congrArg (fun T => (ModuleCat.Hom.hom T) ((m : ℤ) • z))
      (HomologicalComplex.cyclesMap_i (cochainsMap r φ) (n + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hi
    change (ModuleCat.Hom.hom (iCocycles Q'' (n + 1))) ((ModuleCat.Hom.hom (cocyclesMap r φ (n + 1))) ((m : ℤ) • z)) = 0
    rw [hi, map_zsmul, cochainsMap_f]
    funext g
    change φ.hom (((m : ℤ) • (iCocycles Q (n + 1)).hom z) (r ∘ g)) = 0
    exact hmq _
  have hmc : (groupCohomology.map r φ (n + 1)).hom ((m : ℤ) • (groupCohomology.π Q (n + 1)).hom z) = 0 := by
    rw [← map_zsmul, groupCohomology.π_map_apply, hz, map_zero]

  have hc1 : (groupCohomology.π Q (n + 1)).hom z = β • ((m : ℤ) • (groupCohomology.π Q (n + 1)).hom z) := by
    have h2 : (α * (p ^ k : ℤ)) • (groupCohomology.π Q (n + 1)).hom z = 0 := by rw [← smul_smul, hc, zsmul_zero]
    calc (groupCohomology.π Q (n + 1)).hom z = (α * (p ^ k : ℤ) + β * (m : ℤ)) • (groupCohomology.π Q (n + 1)).hom z := by
          rw [hαβ', one_zsmul]
      _ = β • ((m : ℤ) • (groupCohomology.π Q (n + 1)).hom z) := by rw [add_zsmul, h2, zero_add, smul_smul]
  rw [hc1, map_zsmul, hmc, zsmul_zero]

end NumberField.IdeleLocalInv.CapKill
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"
p2m_reactivate "P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation.NumberField.IdeleLocalInv.CapKillArith"

open NumberField.IdeleLocalInv.CapKill GroupCohomology in
theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (D'' : IdeleGaloisDescent (𝓞 K'') E K'')
    [MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ]
    (hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x)

    (M : Rep ℤ (K ≃ₐ[E] K)) (ι : M ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ)) (hιinj : Function.Injective ι.hom)
    (hιrange : ∀ w : (AdeleRing (𝓞 K) K)ˣ, (∃ m, ι.hom m = Additive.ofMul w) ↔
      w ∈ principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S})
    (M'' : Rep ℤ (K'' ≃ₐ[E] K'')) (ι'' : M'' ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ)) (hι''inj : Function.Injective ι''.hom)
    (hι''range : ∀ w : (AdeleRing (𝓞 K'') K'')ˣ, (∃ m, ι''.hom m = Additive.ofMul w) ↔
      w ∈ principalIdeles (𝓞 K'') K'' ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K'') K'' {w | w.under (𝓞 E) ∈ S})

    (B : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) M ⟶ M'')
    (hB : ∀ m, Additive.toMul (ι''.hom (B.hom m)) = Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul (ι.hom m)))

    (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)

    (u : groupCohomology M 2) (k : ℕ) (hu : (p ^ k : ℤ) • u = 0)
    (hdie : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) ι 2).hom u = 0) :
    (groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) B 2).hom u = 0 := by
  classical
  haveI : FiniteDimensional E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance

  let X : ShortComplex (Rep ℤ (K ≃ₐ[E] K)) := RepCokernel.seq ι
  have hX : X.ShortExact := RepCokernel.seq_shortExact ι hιinj
  let Y : ShortComplex (Rep ℤ (K'' ≃ₐ[E] K'')) := RepCokernel.seq ι''
  have hY : Y.ShortExact := RepCokernel.seq_shortExact ι'' hι''inj

  obtain ⟨J, hJ⟩ : ∃ J : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ),
      ∀ z : (AdeleRing (𝓞 K) K)ˣ, Additive.toMul (J.hom (Additive.ofMul z)) = Units.map (genuineBaseChange K K'').β.toMonoidHom z := by
    let fJ : (AdeleRing (𝓞 K) K)ˣ →* (AdeleRing (𝓞 K'') K'')ˣ := Units.map (genuineBaseChange K K'').β.toMonoidHom
    have hfJ : ∀ (σ : (K'' ≃ₐ[E] K'')) (z : (AdeleRing (𝓞 K) K)ˣ), fJ ((AlgEquiv.restrictNormalHom K σ) • z) = σ • fJ z := by
      intro σ z
      rw [hactI, hactI'']
      exact (M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange E K K'' D D'' σ z).symm
    refine ⟨Rep.ofHom ⟨(MonoidHom.toAdditive fJ).toIntLinearMap, fun σ => LinearMap.ext fun z => ?_⟩, fun z => rfl⟩
    change Additive.ofMul (fJ ((AlgEquiv.restrictNormalHom K σ) • (Additive.toMul z : (AdeleRing (𝓞 K) K)ˣ))) = Additive.ofMul (σ • fJ (Additive.toMul z : (AdeleRing (𝓞 K) K)ˣ))
    rw [hfJ]

  have h12 : (Rep.resFunctor (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K))).map X.f ≫ J = B ≫ Y.f := by
    refine Rep.hom_ext (DFunLike.ext _ _ fun m => ?_)
    show J.hom (ι.hom m) = ι''.hom (B.hom m)
    apply Additive.toMul.injective
    rw [hB m]
    exact hJ (Additive.toMul (ι.hom m))

  obtain ⟨Bbar, h23⟩ : ∃ Bbar : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) X.X₃ ⟶ Y.X₃,
      (Rep.resFunctor (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K))).map X.g ≫ Bbar = J ≫ Y.g := by

    refine ⟨Rep.ofHom ⟨Submodule.mapQ _ _ J.hom.toLinearMap ?_, fun σ => Submodule.linearMap_qext _ (LinearMap.ext fun y => ?_)⟩,
      Rep.hom_ext (DFunLike.ext _ _ fun y => rfl)⟩
    · rintro _ ⟨m, rfl⟩
      refine ⟨B.hom m, ?_⟩
      have e := congrArg (fun T : (Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) X.X₁ ⟶ Y.X₂) => (Rep.Hom.hom T) m) h12
      change J.hom (ι.hom m) = ι''.hom (B.hom m) at e
      exact e.symm
    · exact congrArg (fun z => (GroupCohomology.RepCokernel.π ι'').hom z) (Rep.hom_comm_apply J σ y)

  obtain ⟨c, hc⟩ := exists_delta_eq_of_map_eq_zero hX 1 2 rfl u hdie

  have hGc : ((Nat.card (K ≃ₐ[E] K) : ℕ) : ℤ) • c = 0 := by

    obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup (K ≃ₐ[E] K)) X.X₃ 1
    have hz : Limits.IsZero (groupCohomology (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype X.X₃) 1) :=
      isZero_groupCohomology_succ_of_subsingleton _ 0
    haveI := ModuleCat.subsingleton_of_isZero hz
    have h0 : (groupCohomology.map (⊥ : Subgroup (K ≃ₐ[E] K)).subtype (𝟙 (Rep.res (⊥ : Subgroup (K ≃ₐ[E] K)).subtype X.X₃)) 1).hom c = 0 :=
      Subsingleton.elim _ _
    have := hcor c
    rw [h0, map_zero, Subgroup.index_bot] at this
    rw [natCast_zsmul]
    exact this.symm
  obtain ⟨c', a, hc'p, hc'⟩ := exists_pPrimary_preimage (groupCohomology.δ hX 1 2 rfl).hom.toAddMonoidHom p Fact.out
    (Nat.card (K ≃ₐ[E] K)) Nat.card_pos c hGc k (by
      show (p ^ k : ℤ) • (groupCohomology.δ hX 1 2 rfl).hom c = 0
      rw [hc]; exact hu)
  have hc'u : (groupCohomology.δ hX 1 2 rfl).hom c' = u := by
    rw [← hc]; exact hc'

  have hcap' : ∀ q : X.X₃, (∃ k : ℕ, (p ^ k : ℤ) • q = 0) → Bbar.hom q = 0 := by

    rintro q ⟨k₀, hq⟩
    obtain ⟨y, rfl⟩ := GroupCohomology.RepCokernel.π_hom_surjective ι q
    have hy : (Additive.toMul y : (AdeleRing (𝓞 K) K)ˣ) ^ p ^ k₀ ∈
        principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {v | v.under (𝓞 E) ∈ S} := by
      have h0 : (GroupCohomology.RepCokernel.π ι).hom (((p ^ k₀ : ℕ) : ℤ) • y) = 0 := by
        rw [map_zsmul]; exact_mod_cast hq
      rw [GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff] at h0
      obtain ⟨m, hm⟩ := h0
      rw [← hιrange]
      refine ⟨m, ?_⟩
      rw [show (ι.hom : M → _) m = ((p ^ k₀ : ℕ) : ℤ) • y from hm]
      show ((p ^ k₀ : ℕ) : ℤ) • (Additive.ofMul (Additive.toMul y : (AdeleRing (𝓞 K) K)ˣ) : Additive (AdeleRing (𝓞 K) K)ˣ) =
        Additive.ofMul ((Additive.toMul y : (AdeleRing (𝓞 K) K)ˣ) ^ p ^ k₀)
      rw [← ofMul_zpow, zpow_natCast]
    have hβ := NumberField.IdeleLocalInv.CapKillArith.units_map_β_mem_sup_of_pow_mem_sup E K K'' S p hcap (Additive.toMul y) k₀ hy
    rw [← hι''range] at hβ
    obtain ⟨m'', hm''⟩ := hβ
    have hJy : J.hom y = Additive.ofMul (Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul y)) := by
      apply Additive.toMul.injective
      exact hJ (Additive.toMul y)
    have hπ : (GroupCohomology.RepCokernel.π ι'').hom (J.hom y) = 0 := by
      rw [GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff]
      exact ⟨m'', by rw [hJy]; exact hm''⟩
    have hsq := congrArg (fun T => T.hom y) h23
    exact hsq.trans hπ

  haveI : Finite X.X₃ := by

    have hfi := NumberField.AdeleRing.finiteIndex_principalIdeles_sup_unitIdelesOutside E K S
    let N : Subgroup (AdeleRing (𝓞 K) K)ˣ := principalIdeles (𝓞 K) K ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K {v | v.under (𝓞 E) ∈ S}
    let πa : Additive (AdeleRing (𝓞 K) K)ˣ →+ X.X₃ := (GroupCohomology.RepCokernel.π ι).hom.toAddMonoidHom
    have hπa : Function.Surjective πa := GroupCohomology.RepCokernel.π_hom_surjective ι
    have hker : πa.ker = Subgroup.toAddSubgroup N := by
      ext z
      rw [AddMonoidHom.mem_ker]
      show (GroupCohomology.RepCokernel.π ι).hom z = 0 ↔ Additive.toMul z ∈ N
      rw [GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff, ← hιrange]
      constructor
      · rintro ⟨m, hm⟩
        exact ⟨m, by rw [ofMul_toMul]; exact hm⟩
      · rintro ⟨m, hm⟩
        exact ⟨m, by rw [ofMul_toMul] at hm; exact hm⟩
    haveI : (Subgroup.toAddSubgroup N).FiniteIndex := Subgroup.finiteIndex_toAddSubgroup_iff.mpr hfi
    haveI : πa.ker.FiniteIndex := by rw [hker]; infer_instance
    haveI : Finite (Additive (AdeleRing (𝓞 K) K)ˣ ⧸ πa.ker) := AddSubgroup.finite_quotient_of_finiteIndex
    exact Finite.of_equiv _ (QuotientAddGroup.quotientKerEquivOfSurjective πa hπa).toEquiv
  have hkill : (groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) Bbar 1).hom c' = 0 :=
    map_eq_zero_of_forall_torsion_eq_zero (AlgEquiv.restrictNormalHom K) Bbar p Fact.out hcap' 0 c' a hc'p

  have key := delta_natural (AlgEquiv.restrictNormalHom K) hX hY B J Bbar h12 h23 1 2 rfl c'
  rw [hkill, map_zero] at key
  rw [← hc'u]
  exact key.symm

end S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation (solution)
