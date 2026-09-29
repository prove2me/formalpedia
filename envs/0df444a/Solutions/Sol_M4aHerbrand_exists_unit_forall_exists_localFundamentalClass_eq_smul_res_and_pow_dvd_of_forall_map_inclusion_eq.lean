-- Prove2me | solution 1 for M4aHerbrand.exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5de6991b-e834-5578-9251-d2d881864d9a

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Theorems.Thm_NumberField_PlaceDecomp_exists_conj_and_transport_repHom_of_smul_eq
import Theorems.Thm_NumberField_PlaceDecomp_exists_isLocalFundamentalClass_map_eq_map_of_smul_eq
import Theorems.Thm_groupCohomology_map_conj_eq_id
import Theorems.Thm_M4aHerbrand_subsingleton_ideleGaloisDescent
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_snd_apply
import Theorems.Thm_M4aHerbrand_GenuineDescent_genuineDescentDatum_act_fst_apply
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq.M4aHerbrand"
open scoped NumberField.PlaceDecomp
open scoped NumberField.PlaceTransport

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart coe_infPart_apply coe_finPart_apply IdeleClassGroup IdeleGaloisDescent subsingleton_ideleGaloisDescent GenuineDescent.genuineDescentDatum_act_snd_apply GenuineDescent.genuineDescentDatum GenuineDescent.genuineDescentDatum_act_fst_apply"
namespace L2Skel
p2m_open "M4aHerbrand"

theorem exists_zsmul_eq_of_span_eq_top {M : Type} [AddCommGroup M] [Module ℤ M]
    (y : M) (hy : Submodule.span ℤ {y} = ⊤) (m : M) : ∃ n : ℤ, n • y = m := by
  have hm : m ∈ Submodule.span ℤ {y} := by rw [hy]; exact Submodule.mem_top
  obtain ⟨n, hn⟩ := Submodule.mem_span_singleton.mp hm
  exact ⟨n, (int_smul_eq_zsmul _ n y).symm.trans hn⟩

theorem natCard_eq_addOrderOf_of_span_eq_top {M : Type} [AddCommGroup M] [Module ℤ M] [Finite M]
    (y : M) (hy : Submodule.span ℤ {y} = ⊤) : Nat.card M = addOrderOf y := by
  have htop : AddSubgroup.zmultiples y = ⊤ := by
    rw [eq_top_iff]
    intro m _
    obtain ⟨n, hn⟩ := exists_zsmul_eq_of_span_eq_top y hy m
    exact ⟨n, hn⟩
  rw [← Nat.card_zmultiples, htop, AddSubgroup.card_top]

theorem natCard_dvd_of_span_eq_top_of_zsmul_eq_zero {M : Type} [AddCommGroup M] [Module ℤ M] [Finite M]
    (y : M) (hy : Submodule.span ℤ {y} = ⊤) (t : ℤ) (ht : t • y = 0) : (Nat.card M : ℤ) ∣ t := by
  rw [natCard_eq_addOrderOf_of_span_eq_top y hy]
  exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr ht

theorem span_singleton_eq_top_of_eq_zsmul {M : Type} [AddCommGroup M] [Module ℤ M]
    (x y : M) (hx : Submodule.span ℤ {x} = ⊤) (a : ℤ) (h : x = a • y) : Submodule.span ℤ {y} = ⊤ := by
  rw [eq_top_iff, ← hx, Submodule.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
  rw [h]
  exact int_smul_eq_zsmul _ a y

theorem not_dvd_of_span_eq_top_of_eq_zsmul {M : Type} [AddCommGroup M] [Module ℤ M] [Finite M] {p : ℕ} (hp : p.Prime)
    (x y : M) (hx : Submodule.span ℤ {x} = ⊤) (a : ℤ) (h : x = a • y) (hM : p ∣ Nat.card M) : ¬ (p : ℤ) ∣ a := by
  intro hpa
  have hy := span_singleton_eq_top_of_eq_zsmul x y hx a h
  obtain ⟨b, hb⟩ := exists_zsmul_eq_of_span_eq_top x hx y

  have hzero : (a * b - 1) • x = 0 := by
    rw [sub_zsmul, one_zsmul, mul_zsmul, hb, ← h, add_neg_cancel]
  have hdvd := natCard_dvd_of_span_eq_top_of_zsmul_eq_zero x hx _ hzero
  have hp' : (p : ℤ) ∣ a * b - 1 := (Int.natCast_dvd_natCast.mpr hM).trans hdvd
  have : (p : ℤ) ∣ 1 := by
    have := (dvd_mul_of_dvd_left hpa b)
    have h1 : (1 : ℤ) = a * b - (a * b - 1) := by ring
    rw [h1]; exact dvd_sub this hp'
  exact hp.one_lt.ne' (by exact_mod_cast Int.eq_one_of_dvd_one (by positivity) this)

theorem exists_coeff_not_dvd (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (p : ℕ) [Fact p.Prime]
    (u₀ : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
    (h2 : ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S)
    (h3 : ∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀} = ⊤)
    (P : Subgroup (F ≃ₐ[E] F)) (hP : IsPGroup p P)
    (uP : groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) (hspan : Submodule.span ℤ {uP} = ⊤) :
    ∃ a : ℤ, ¬ (p : ℤ) ∣ a ∧ (groupCohomology.map P.subtype (𝟙 (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ = a • uP := by
  have hp : p.Prime := Fact.out
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  haveI : Fintype ↥P := Fintype.ofFinite _
  obtain ⟨a₀, ha₀⟩ := exists_zsmul_eq_of_span_eq_top uP hspan
    ((groupCohomology.map P.subtype (𝟙 (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀)
  have hcardM : Nat.card (groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Nat.card ↥P := by
    rw [h2 P, Nat.card_eq_fintype_card]
  haveI : Finite (groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) := Nat.finite_of_card_ne_zero (by
    rw [hcardM]; exact Nat.card_pos.ne')
  by_cases hpa : (p : ℤ) ∣ a₀
  ·
    refine ⟨1, by exact_mod_cast hp.one_lt.ne' ∘ Nat.dvd_one.mp ∘ Int.natCast_dvd_natCast.mp, ?_⟩
    rcases hP.card_eq_or_dvd with h1 | hdvd
    · haveI : Subsingleton (groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) :=
        (Nat.card_eq_one_iff_unique.mp (hcardM.trans h1)).1
      exact Subsingleton.elim _ _
    · exact absurd hpa (not_dvd_of_span_eq_top_of_eq_zsmul hp _ uP (h3 P) a₀ ha₀.symm (hcardM ▸ hdvd))
  · exact ⟨a₀, hpa, ha₀.symm⟩

theorem exists_smul_pow_dvd_natCard_inf (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (p : ℕ) [Fact p.Prime] (P : Subgroup (F ≃ₐ[E] F)) (hP : IsPGroup p P) (hPidx : ¬ p ∣ P.index)
    (w : HeightOneSpectrum (𝓞 F)) :
    ∃ σ : F ≃ₐ[E] F, p ^ ((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)).factorization p) ∣ Nat.card ↥((NumberField.PlaceDecomp.decomp E F (σ • w)) ⊓ P) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F

  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hPcard : Nat.card ↥P = p ^ (Nat.card (F ≃ₐ[E] F)).factorization p := by
    rw [← P.card_mul_index, Nat.factorization_mul_apply_of_coprime, hk, hp.factorization_pow,
      Nat.factorization_eq_zero_of_not_dvd hPidx]
    · simp
    · rw [hk]
      exact Nat.Coprime.pow_left k (hp.coprime_iff_not_dvd.mpr hPidx)
  let PS : Sylow p (F ≃ₐ[E] F) := Sylow.ofCard P hPcard

  obtain ⟨Q₀⟩ : Nonempty (Sylow p ↥(NumberField.PlaceDecomp.decomp E F w)) := inferInstance
  have hQ₁ : IsPGroup p ↥((Q₀ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)).map (NumberField.PlaceDecomp.decomp E F w).subtype) := Q₀.isPGroup'.map _
  obtain ⟨R, hR⟩ := hQ₁.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (F ≃ₐ[E] F) R PS
  refine ⟨g, ?_⟩

  obtain ⟨-, c, -, hbij, hcc, -⟩ :=
    NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq E F w (g • w) g rfl
  have hsub : (((Q₀ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)).map (NumberField.PlaceDecomp.decomp E F w).subtype).map (MulAut.conj g).toMonoidHom) ≤
      (NumberField.PlaceDecomp.decomp E F (g • w)) ⊓ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    have hyD : y ∈ (NumberField.PlaceDecomp.decomp E F w) := by
      obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hy
      exact z.2
    refine ⟨?_, ?_⟩
    · obtain ⟨τ, hτ⟩ := hbij.2 ⟨y, hyD⟩
      have hval : g⁻¹ * (τ : F ≃ₐ[E] F) * g = y := by
        have := congrArg Subtype.val hτ
        rwa [hcc] at this
      have hτ' : (MulAut.conj g).toMonoidHom y = (τ : F ≃ₐ[E] F) := by
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← hval]
        group
      rw [hτ']
      exact τ.2
    · have hmem : (MulAut.conj g) y ∈ ((g • R : Sylow p (F ≃ₐ[E] F)) : Subgroup (F ≃ₐ[E] F)) := by
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR hy)
      rw [hg] at hmem
      exact hmem
  have hcard : Nat.card ↥(((Q₀ : Subgroup ↥(NumberField.PlaceDecomp.decomp E F w)).map (NumberField.PlaceDecomp.decomp E F w).subtype).map (MulAut.conj g).toMonoidHom) =
      p ^ (Nat.card ↥(NumberField.PlaceDecomp.decomp E F w)).factorization p := by
    rw [Subgroup.card_map_of_injective (fun a b h => (MulAut.conj g).injective h),
      Subgroup.card_map_of_injective Subtype.val_injective, Sylow.card_eq_multiplicity]
  exact hcard ▸ Subgroup.card_dvd_of_le hsub

theorem pow_dvd_sub_one_of_good_place (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (p : ℕ) [Fact p.Prime]
    (u₀ : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
    (h2 : ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S)
    (h3 : ∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀} = ⊤)
    (P : Subgroup (F ≃ₐ[E] F))
    (uP : groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2)
    (a : ℤ) (ha : (groupCohomology.map P.subtype (𝟙 (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ = a • uP)
    (w₁ : HeightOneSpectrum (𝓞 F))
    (hgood : p ^ ((Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁)).factorization p) ∣ Nat.card ↥((NumberField.PlaceDecomp.decomp E F w₁) ⊓ P))

    (ℓ : groupCohomology (Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) (c : ℤ)
    (hc : ℓ = c • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w₁).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀)
    (hℓ : ((groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w₁) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w₁)))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w₁) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w₁))) (Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom ℓ
            : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w₁) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) =
          ((groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w₁) ⊓ P ≤ P))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w₁) ⊓ P ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom uP
            : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w₁) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2)) :
    ∀ n : ℕ, p ^ n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w₁) → (p : ℤ) ^ n ∣ c * a - 1 := by
  have hp : p.Prime := Fact.out
  haveI : FiniteDimensional E F := Module.Finite.of_restrictScalars_finite ℚ E F
  intro n hn

  let Dg : Subgroup (F ≃ₐ[E] F) := (NumberField.PlaceDecomp.decomp E F w₁)
  let Q : Subgroup (F ≃ₐ[E] F) := (NumberField.PlaceDecomp.decomp E F w₁) ⊓ P
  haveI : Fintype ↥Q := Fintype.ofFinite _

  have eD : ∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      ((groupCohomology.map (Subgroup.inclusion (inf_le_left : Q ≤ Dg))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : Q ≤ Dg)) (Rep.res Dg.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          ((groupCohomology.map Dg.subtype (𝟙 (Rep.res Dg.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x)
        : groupCohomology (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) =
      (groupCohomology.map Q.subtype (𝟙 (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x := by
    intro x
    have hmc := groupCohomology.map_comp Dg.subtype (Subgroup.inclusion (inf_le_left : Q ≤ Dg))
      (𝟙 (Rep.res Dg.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : Q ≤ Dg)) (Rep.res Dg.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at hmc
    exact (congrArg (fun t => (ModuleCat.Hom.hom t) x) hmc).symm
  have eP : ∀ x : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2,
      ((groupCohomology.map (Subgroup.inclusion (inf_le_right : Q ≤ P))
          (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : Q ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          ((groupCohomology.map P.subtype (𝟙 (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x)
        : groupCohomology (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) =
      (groupCohomology.map Q.subtype (𝟙 (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom x := by
    intro x
    have hmc := groupCohomology.map_comp P.subtype (Subgroup.inclusion (inf_le_right : Q ≤ P))
      (𝟙 (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : Q ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2
    rw [CategoryTheory.Functor.map_id, Category.comp_id] at hmc
    exact (congrArg (fun t => (ModuleCat.Hom.hom t) x) hmc).symm

  haveI : Finite (groupCohomology (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) :=
    Nat.finite_of_card_ne_zero (by rw [h2 Q]; exact Fintype.card_ne_zero)
  obtain ⟨y, hy⟩ : ∃ y : groupCohomology (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2, y =
    ((groupCohomology.map (Subgroup.inclusion (inf_le_right : Q ≤ P))
      (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : Q ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom uP
      : groupCohomology (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) := ⟨_, rfl⟩
  have hres : (groupCohomology.map Q.subtype (𝟙 (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ = a • y := by
    rw [← eP, ha, map_zsmul, hy]
    rfl
  have hygen : Submodule.span ℤ {y} = ⊤ := span_singleton_eq_top_of_eq_zsmul _ y (h3 Q) a hres

  have hkill : (c * a - 1) • y = 0 := by
    have h1 : y = c • (groupCohomology.map Q.subtype (𝟙 (Rep.res Q.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ := by
      rw [hy, ← hℓ, hc, map_zsmul, eD]
      rfl
    rw [sub_zsmul, one_zsmul, mul_zsmul, ← hres, ← h1, add_neg_cancel]

  have hdvd := natCard_dvd_of_span_eq_top_of_zsmul_eq_zero y hygen (c * a - 1) hkill
  rw [h2 Q, ← Nat.card_eq_fintype_card] at hdvd
  have hpn : p ^ n ∣ Nat.card ↥Q := by
    refine (Nat.pow_dvd_pow p ?_).trans hgood
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hn
  exact (Int.natCast_dvd_natCast.mpr hpn |>.trans (by exact_mod_cast hdvd))

noncomputable def conjCoeff (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F)
    (cσ : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((cσ τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ) :
    Rep.res cσ (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) ⟶ Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) :=
  Rep.ofHom
    { toLinearMap := (((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ)
      isIntertwining' := fun τ => by
        apply LinearMap.ext
        intro m
        change ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ (((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ ((cσ τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) m) = ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ (τ : F ≃ₐ[E] F) (((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ m)
        rw [hc, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 1
        group }

noncomputable def conjCoeffG (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)] (σ : F ≃ₐ[E] F) :
    Rep.res (MulAut.conj σ⁻¹).toMonoidHom (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) :=
  Rep.ofHom
    { toLinearMap := (((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ)
      isIntertwining' := fun τ => by
        apply LinearMap.ext
        intro m
        change ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ (((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ ((MulAut.conj σ⁻¹).toMonoidHom τ) m) = ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ τ (((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ m)
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 1
        group }

open CategoryTheory in

theorem map_id_then {k G H : Type} [CommRing k] [Group G] [Group H] (g : G →* H)
    {A B : Rep k H} {C : Rep k G} (φ : A ⟶ B) (ψ : Rep.res g B ⟶ C) (n : ℕ) :
    groupCohomology.map (MonoidHom.id H) φ n ≫ groupCohomology.map g ψ n =
      groupCohomology.map g ((Rep.resFunctor g).map φ ≫ ψ) n :=
  (groupCohomology.map_comp (MonoidHom.id H) g φ ψ n).symm

open CategoryTheory in

theorem map_then_id {k G H : Type} [CommRing k] [Group G] [Group H] (f : G →* H)
    {A : Rep k H} {B C : Rep k G} (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) (n : ℕ) :
    groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id G) ψ n = groupCohomology.map f (φ ≫ ψ) n :=
  (groupCohomology.map_comp f (MonoidHom.id G) φ ψ n).symm

theorem unitsAct_iota_eq (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)
    (u : (w.adicCompletion F)ˣ) (v : (w₁.adicCompletion F)ˣ)
    (huv : (v : w₁.adicCompletion F) = NumberField.PlaceTransport.transport σ hσ (u : w.adicCompletion F)) :
    D.unitsAct σ (ι w u) = ι w₁ v := by
  haveI := M4aHerbrand.subsingleton_ideleGaloisDescent (𝓞 F) E F
  obtain rfl : D = GenuineDescent.genuineDescentDatum E F := Subsingleton.elim _ _
  subst hσ
  apply Units.ext
  change (GenuineDescent.genuineDescentDatum E F).act σ ((ι w u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) =
    ((ι (σ • w) v : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)

  have hdiag : ∀ (w₀ : HeightOneSpectrum (𝓞 F)) (x : (w₀.adicCompletion F)ˣ),
      ((ι w₀ x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w₀ = (x : w₀.adicCompletion F) := by
    intro w₀ x
    rw [← coe_finPart_apply, (hι w₀ x).1]
  have hoff : ∀ (w₀ : HeightOneSpectrum (𝓞 F)) (x : (w₀.adicCompletion F)ˣ) (w' : HeightOneSpectrum (𝓞 F)), w' ≠ w₀ →
      ((ι w₀ x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 w' = 1 := by
    intro w₀ x w' hw
    rw [← coe_finPart_apply, (hι w₀ x).2.1 w' hw, Units.val_one]
  have hinf : ∀ (w₀ : HeightOneSpectrum (𝓞 F)) (x : (w₀.adicCompletion F)ˣ),
      ((ι w₀ x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := by
    intro w₀ x
    rw [← coe_infPart_apply, (hι w₀ x).2.2, Units.val_one]
  refine Prod.ext ?_ ?_
  ·
    funext w'
    rw [GenuineDescent.genuineDescentDatum_act_fst_apply E F σ _ (smul_inv_smul σ w'), hinf, hinf]
    exact map_one _
  ·
    ext w' : 1
    by_cases hw' : w' = σ • w
    · subst hw'
      rw [GenuineDescent.genuineDescentDatum_act_snd_apply E F σ _ rfl, hdiag, hdiag]
      exact huv.symm
    · have hne : σ⁻¹ • w' ≠ w := fun h => hw' (by rw [← h, smul_inv_smul])
      rw [GenuineDescent.genuineDescentDatum_act_snd_apply E F σ _ (smul_inv_smul σ w'), hoff w u _ hne, map_one,
        hoff (σ • w) v w' hw']

theorem conjCoeff_lam_eq_lam_T (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶ Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)
    (cσ : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((cσ τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (T : Rep.res cσ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶ Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
    (hT : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F))
    (u : (w.adicCompletion F)ˣ) :
    (conjCoeff E F w w₁ σ cσ hc).hom ((lam w).hom (Additive.ofMul u)) = (lam w₁).hom (T.hom (Additive.ofMul u)) := by
  have hTv : T.hom (Additive.ofMul u) = Additive.ofMul (Additive.toMul (T.hom (Additive.ofMul u))) := rfl
  have hconj : ∀ y, (conjCoeff E F w w₁ σ cσ hc).hom y = ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ y := fun _ => rfl
  have hcls : ∀ y : (AdeleRing (𝓞 F) F)ˣ, D.classAct σ (QuotientGroup.mk y : IdeleClassGroup (𝓞 F) F) =
      QuotientGroup.mk (D.unitsAct σ y) := fun y => QuotientGroup.congr_mk _ _ _ _ y
  rw [hlam, hTv, hlam, hconj, Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, hact, hcls,
    unitsAct_iota_eq E F D ι hι w w₁ σ hσ u _ (hT u)]
  rfl

theorem map_conjCoeff_map_lam_eq (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶ Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F) (hσ : σ • w = w₁)
    (cσ : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((cσ τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (T : Rep.res cσ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶ Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w₁)) (w₁.adicCompletion F)ˣ)
    (hT : ∀ x : (w.adicCompletion F)ˣ, ((Additive.toMul (T.hom (Additive.ofMul x)) : (w₁.adicCompletion F)ˣ) : w₁.adicCompletion F) =
      NumberField.PlaceTransport.transport σ hσ (x : w.adicCompletion F))
    (z : groupCohomology (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) 2) :
    (groupCohomology.map cσ (conjCoeff E F w w₁ σ cσ hc) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom z) =
      (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w₁)) (lam w₁) 2).hom ((groupCohomology.map cσ T 2).hom z) := by
  have h1 := congrArg (fun t => (ModuleCat.Hom.hom t) z) (map_id_then cσ (lam w) (conjCoeff E F w w₁ σ cσ hc) 2)
  have h2 := congrArg (fun t => (ModuleCat.Hom.hom t) z) (map_then_id cσ T (lam w₁) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1 h2
  rw [h1, h2]
  have e3 : ((Rep.resFunctor cσ).map (lam w) ≫ conjCoeff E F w w₁ σ cσ hc :
      Rep.res cσ (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ) ⟶ Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) =
      T ≫ lam w₁ := by
    apply Rep.hom_ext
    ext x
    obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
    exact conjCoeff_lam_eq_lam_T E F D hact ι hι lam hlam w w₁ σ hσ cσ hc T hT u
  rw [← e3]

theorem map_conjCoeff_res_eq_res (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (w w₁ : HeightOneSpectrum (𝓞 F)) (σ : F ≃ₐ[E] F)
    (cσ : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* ↥(NumberField.PlaceDecomp.decomp E F w))
    (hc : ∀ τ : ↥(NumberField.PlaceDecomp.decomp E F w₁), ((cσ τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = σ⁻¹ * (τ : F ≃ₐ[E] F) * σ)
    (u₀ : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2) :
    (groupCohomology.map cσ (conjCoeff E F w w₁ σ cσ hc) 2).hom ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀) =
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w₁).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ := by

  have aux : ∀ (f : ↥(NumberField.PlaceDecomp.decomp E F w₁) →* (F ≃ₐ[E] F))
      (hf : f = (MulAut.conj σ⁻¹).toMonoidHom.comp (NumberField.PlaceDecomp.decomp E F w₁).subtype)
      (φ : Rep.res f (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) ⟶ Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
      (hφ : ∀ m, φ.hom m = ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ m),
      (groupCohomology.map f φ 2).hom u₀ =
        (groupCohomology.map (NumberField.PlaceDecomp.decomp E F w₁).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ := by
    intro f hf φ hφ
    subst hf
    have hmc := groupCohomology.map_comp (MulAut.conj σ⁻¹).toMonoidHom (NumberField.PlaceDecomp.decomp E F w₁).subtype
      (conjCoeffG E F σ) (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w₁).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2
    rw [Category.comp_id, groupCohomology.map_conj_eq_id (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) σ⁻¹ 2 (conjCoeffG E F σ)
      (fun m => by change ((Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))).ρ σ m = _; rw [inv_inv]), Category.id_comp] at hmc
    have hφ' : φ = (Rep.resFunctor (NumberField.PlaceDecomp.decomp E F w₁).subtype).map (conjCoeffG E F σ) := by
      apply Rep.hom_ext
      ext m
      exact hφ m
    rw [hφ', hmc]

  have hmc := groupCohomology.map_comp (NumberField.PlaceDecomp.decomp E F w).subtype cσ
    (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) (conjCoeff E F w w₁ σ cσ hc) 2
  erw [Category.id_comp] at hmc
  have happ := congrArg (fun t => (ModuleCat.Hom.hom t) u₀) hmc
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at happ
  rw [← happ]
  refine aux _ ?_ _ (fun m => rfl)
  apply MonoidHom.ext
  intro τ
  change ((cσ τ : ↥(NumberField.PlaceDecomp.decomp E F w)) : F ≃ₐ[E] F) = (MulAut.conj σ⁻¹) (τ : F ≃ₐ[E] F)
  rw [hc, MulAut.conj_apply, inv_inv]

end M4aHerbrand.L2Skel

open M4aHerbrand.L2Skel in

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    (D : IdeleGaloisDescent (𝓞 F) E F)
    [MulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)]
    (hact : ∀ (g : F ≃ₐ[E] F) (c : IdeleClassGroup (𝓞 F) F), g • c = D.classAct g c)
    (ι : ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ →* (AdeleRing (𝓞 F) F)ˣ)
    (hι : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      finPart w (ι w x) = x ∧ (∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → finPart w' (ι w x) = 1) ∧ infPart (ι w x) = 1)
    (lam : ∀ w : HeightOneSpectrum (𝓞 F),
      Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ ⟶
        Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))
    (hlam : ∀ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ),
      (lam w).hom (Additive.ofMul x) = Additive.ofMul (QuotientGroup.mk (ι w x) : IdeleClassGroup (𝓞 F) F))
    (u₀ : groupCohomology (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)) 2)
    (h2 : ∀ (S : Subgroup (F ≃ₐ[E] F)) [Fintype S], Nat.card
        (groupCohomology (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) = Fintype.card S)
    (h3 : ∀ S : Subgroup (F ≃ₐ[E] F), Submodule.span ℤ
        {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀} = ⊤)
    (P : Subgroup (F ≃ₐ[E] F)) (hP : IsPGroup p P) (hPidx : ¬ p ∣ P.index)
    (uP : groupCohomology (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) (hspan : Submodule.span ℤ {uP} = ⊤)
    (hloc :
      ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ((groupCohomology.map (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w)))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_left : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ (NumberField.PlaceDecomp.decomp E F w))) (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2) =
        ((groupCohomology.map (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P))
            (𝟙 (Rep.res (Subgroup.inclusion (inf_le_right : (NumberField.PlaceDecomp.decomp E F w) ⊓ P ≤ P)) (Rep.res P.subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))))) 2).hom
          uP : groupCohomology (Rep.res ((NumberField.PlaceDecomp.decomp E F w) ⊓ P).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F))) 2)) :
    ∃ a : ℤ, ¬ (p : ℤ) ∣ a ∧
      ∀ (w : HeightOneSpectrum (𝓞 F))
        (q : ℕ) [Fact q.Prime] (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L']
        [MulSemiringAction (↥(NumberField.PlaceDecomp.decomp E F w)) L'] [MulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ]
        (Φ : w.adicCompletion F ≃+* L')
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x)
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (v : (↥L')ˣ), ((g • v : (↥L')ˣ) : L') = g • (v : L'))
        (_ : ∀ (g : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : w.adicCompletion F), Φ (g • x) = g • Φ x)
        (K₀ : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K₀]
        (_ : ExtCitation.LocalLevel.IsBase q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀)
        (θ : Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ ⟶
          Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (w.adicCompletion F)ˣ)
        (_ : ∀ v : (↥L')ˣ, ((Additive.toMul (θ.hom (Additive.ofMul v)) : (w.adicCompletion F)ˣ) : w.adicCompletion F) = Φ.symm (v : L'))
        (u' : groupCohomology.H2 (Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E F w)) (↥L')ˣ))
        (_ : ExtCitation.LocalLevel.IsLocalFundamentalClass q L' (↥(NumberField.PlaceDecomp.decomp E F w)) K₀ u'),
        ∃ c : ℤ, ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u')) = c • ((groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀) ∧
          ∀ n : ℕ, p ^ n ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp E F w) → (p : ℤ) ^ n ∣ c * a - 1 := by
  classical
  obtain ⟨a, hpa, ha⟩ := exists_coeff_not_dvd E F p u₀ h2 h3 P hP uP hspan
  refine ⟨a, hpa, ?_⟩
  intro w q _ L' _ _ _ Φ hΦ1 hΦ2 hΦ3 K₀ _ hK₀ θ hθ u' hu'

  have hmem : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) (lam w) 2).hom
      ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F w)) θ 2).hom u') ∈
      Submodule.span ℤ {(groupCohomology.map (NumberField.PlaceDecomp.decomp E F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F w).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀} := by
    rw [h3]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
  have hc' := hc.symm.trans (int_smul_eq_zsmul _ c _)
  refine ⟨c, hc', fun n hn => ?_⟩

  obtain ⟨σ, hgood⟩ := exists_smul_pow_dvd_natCard_inf E F p P hP hPidx w

  obtain ⟨hcard, cσ, T, -, hcσ, hT⟩ :=
    NumberField.PlaceDecomp.exists_conj_and_transport_repHom_of_smul_eq E F w (σ • w) σ rfl
  obtain ⟨-, inst1, inst2, Φ₁, θ₁, u₁, hΦ₁1, hΦ₁2, hΦ₁3, hK₀₁, hθ₁, hu₁, htrans⟩ :=
    NumberField.PlaceDecomp.exists_isLocalFundamentalClass_map_eq_map_of_smul_eq E F w (σ • w) σ rfl cσ hcσ T hT
      q L' Φ hΦ1 hΦ2 hΦ3 K₀ hK₀ θ hθ u' hu'
  letI := inst1
  letI := inst2

  have hℓ₁ := hloc (σ • w) q L' Φ₁ hΦ₁1 hΦ₁2 hΦ₁3 K₀ hK₀₁ θ₁ hθ₁ u₁ hu₁

  have hc₁ : (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (σ • w))) (lam (σ • w)) 2).hom
        ((groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp E F (σ • w))) θ₁ 2).hom u₁) =
      c • (groupCohomology.map (NumberField.PlaceDecomp.decomp E F (σ • w)).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp E F (σ • w)).subtype (Rep.ofMulDistribMulAction (F ≃ₐ[E] F) (IdeleClassGroup (𝓞 F) F)))) 2).hom u₀ := by
    rw [← htrans, ← map_conjCoeff_map_lam_eq E F D hact ι hι lam hlam w (σ • w) σ rfl cσ hcσ T hT, hc', map_zsmul,
      map_conjCoeff_res_eq_res E F w (σ • w) σ cσ hcσ u₀]

  rw [← hcard] at hn hgood
  exact pow_dvd_sub_one_of_good_place E F p u₀ h2 h3 P uP a ha (σ • w) hgood _ c hc₁ hℓ₁ n hn

end S_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq
end P2MW
export P2MW.S_M4aHerbrand_exists_unit_forall_exists_localFundamentalClass_eq_smul_res_and_pow_dvd_of_forall_map_inclusion_eq (solution)
