-- Prove2me | solution 1 for NumberField.sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bb68da3b-a3f2-57d9-a7d2-375b6a6bc5b2

import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Theorems.Thm_NumberField_isOpen_range_idelicNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero"

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace XIO

noncomputable def psi : AddCircle (1 : ℚ) →+ AddCircle (1 : ℝ) :=
  QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      intro x hx
      obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
      refine AddSubgroup.mem_comap.mpr (AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ?_⟩)
      simp)

theorem psi_injective : Function.Injective psi := by
  refine (injective_iff_map_eq_zero psi).mpr fun x hx => ?_
  induction x using QuotientAddGroup.induction_on with
  | H q =>
    have h1 : psi (q : AddCircle (1 : ℚ)) = ((q : ℝ) : AddCircle (1 : ℝ)) := rfl
    rw [h1, AddCircle.coe_eq_zero_iff] at hx
    obtain ⟨k, hk⟩ := hx
    rw [AddCircle.coe_eq_zero_iff]
    refine ⟨k, ?_⟩
    have hk' : ((k : ℚ) : ℝ) = (q : ℝ) := by rw [← hk]; simp
    have hkq : (k : ℚ) = q := by exact_mod_cast hk'
    rw [zsmul_eq_mul, mul_one]
    exact hkq

theorem toUnits_injective : Function.Injective Circle.toUnits := by
  intro a b h
  have h' := congrArg Units.val h
  rw [Circle.toUnits_apply, Circle.toUnits_apply, Units.val_mk0, Units.val_mk0] at h'
  exact Subtype.ext h'

theorem exists_monoidHom_apply_ne_one {Q : Type*} [CommGroup Q] (q : Q) (hq : q ≠ 1) :
    ∃ χ : Q →* ℂˣ, χ q ≠ 1 := by
  have ha : (Additive.ofMul q : Additive Q) ≠ 0 := by simpa using hq
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  let f : Q → ℂˣ := fun x => Circle.toUnits (AddCircle.toCircle (psi (c (Additive.ofMul x))))
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · simp only [f, ofMul_one, map_zero, AddCircle.toCircle_zero, map_one]
  · intro x y
    simp only [f, ofMul_mul, map_add, AddCircle.toCircle_add, map_mul]
  · intro h
    apply hc
    change Circle.toUnits (AddCircle.toCircle (psi (c (Additive.ofMul q)))) = 1 at h
    have h1 : AddCircle.toCircle (psi (c (Additive.ofMul q))) = AddCircle.toCircle (0 : AddCircle (1 : ℝ)) := by
      rw [AddCircle.toCircle_zero]
      exact toUnits_injective (by rw [h, map_one])
    have h2 : psi (c (Additive.ofMul q)) = 0 := AddCircle.injective_toCircle one_ne_zero h1
    exact (injective_iff_map_eq_zero psi).mp psi_injective _ h2

theorem continuous_of_forall_mem_eq_one {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) (χ : G →* ℂˣ) (hχ : ∀ g ∈ H, χ g = 1) : Continuous χ := by
  refine continuous_of_continuousAt_one χ ?_
  refine (continuousAt_const : ContinuousAt (fun _ : G => (1 : ℂˣ)) 1).congr ?_
  exact Filter.eventuallyEq_of_mem (hH.mem_nhds H.one_mem) fun g hg => (hχ g hg).symm

end XIO

open XIO in

theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (Ξ : Finset ((⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ))
    (hΞ : ∀ ξ : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ, ξ ∈ Ξ ↔
      ((Continuous fun z : (AdeleRing (𝓞 K) K)ˣ => ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)) ∧
        (∀ z : (AdeleRing (𝓞 K) K)ˣ,
          z ∈ (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K)).range →
            ξ ⟨z, Subgroup.mem_top z⟩ = 1) ∧
        ∀ z : (AdeleRing (𝓞 L) L)ˣ,
          ξ ⟨(M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z, Subgroup.mem_top _⟩ =
            ξL ⟨z, Subgroup.mem_top z⟩)) :
    (∀ z : (AdeleRing (𝓞 K) K)ˣ,
      z ∉ (M4aHerbrand.principalIdeles (𝓞 K) K ⊔
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) →
        ∑ ξ ∈ Ξ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = 0) ∧
    (∀ (k : Kˣ) (w : (AdeleRing (𝓞 L) L)ˣ),
      ∑ ξ ∈ Ξ, ((ξ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k *
          (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm w, Subgroup.mem_top _⟩ : ℂˣ) : ℂ) =
        (Ξ.card : ℂ) * ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ)) := by
  classical
  set N := (M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm with hNdef
  set H : Subgroup (AdeleRing (𝓞 K) K)ˣ := M4aHerbrand.principalIdeles (𝓞 K) K ⊔ N.range with hHdef
  refine ⟨?_, ?_⟩
  swap
  ·
    intro k w
    have hterm : ∀ ξ ∈ Ξ, ((ξ ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k * N w,
        Subgroup.mem_top _⟩ : ℂˣ) : ℂ) = ((ξL ⟨w, Subgroup.mem_top w⟩ : ℂˣ) : ℂ) := by
      intro ξ hξ
      obtain ⟨-, htriv, hnorm⟩ := (hΞ ξ).mp hξ
      have hsplit : (⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k * N w, Subgroup.mem_top _⟩ :
          (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ)) =
          ⟨Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) k, Subgroup.mem_top _⟩ *
            ⟨N w, Subgroup.mem_top _⟩ := rfl
      rw [hsplit, map_mul, htriv _ ⟨k, rfl⟩, one_mul, hnorm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  ·
    intro z hz

    have hNopen : IsOpen ((N.range : Subgroup (AdeleRing (𝓞 K) K)ˣ) : Set (AdeleRing (𝓞 K) K)ˣ) :=
      NumberField.isOpen_range_idelicNorm K L (M4aHerbrand.GenuineDescent.genuineBaseChange K L)
    have hHopen : IsOpen (H : Set (AdeleRing (𝓞 K) K)ˣ) := by
      refine Subgroup.isOpen_of_mem_nhds H (Filter.mem_of_superset (hNopen.mem_nhds (N.range.one_mem)) ?_)
      intro x hx
      exact Subgroup.mem_sup_right hx

    have hz1 : (QuotientGroup.mk z : (AdeleRing (𝓞 K) K)ˣ ⧸ H) ≠ 1 := by
      rwa [Ne, QuotientGroup.eq_one_iff]
    obtain ⟨χ₀, hχ₀⟩ := exists_monoidHom_apply_ne_one _ hz1
    set χ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ := χ₀.comp (QuotientGroup.mk' H) with hχdef
    have hχH : ∀ g ∈ H, χ g = 1 := fun g hg => by
      rw [hχdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).mpr hg, map_one]
    have hχz : χ z ≠ 1 := by rwa [hχdef, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    have hχc : Continuous χ := continuous_of_forall_mem_eq_one H hHopen χ hχH

    set χ' : (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ) →* ℂˣ := χ.comp (⊤ : Subgroup (AdeleRing (𝓞 K) K)ˣ).subtype with hχ'def
    have hχ'app : ∀ x : (AdeleRing (𝓞 K) K)ˣ, χ' ⟨x, Subgroup.mem_top x⟩ = χ x := fun x => rfl
    have hmem : ∀ ξ ∈ Ξ, ξ * χ' ∈ Ξ := by
      intro ξ hξ
      obtain ⟨hcont, htriv, hnorm⟩ := (hΞ ξ).mp hξ
      refine (hΞ _).mpr ⟨?_, ?_, ?_⟩
      · have : (fun x : (AdeleRing (𝓞 K) K)ˣ => (((ξ * χ') ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ)) =
            fun x => ((ξ ⟨x, Subgroup.mem_top x⟩ : ℂˣ) : ℂ) * ((χ x : ℂˣ) : ℂ) := by
          funext x; rw [MonoidHom.mul_apply, hχ'app, Units.val_mul]
        rw [this]
        exact hcont.mul (Units.continuous_val.comp hχc)
      · intro x hx
        rw [MonoidHom.mul_apply, hχ'app, htriv x hx, hχH x (Subgroup.mem_sup_left hx), mul_one]
      · intro w
        rw [MonoidHom.mul_apply, hχ'app, hnorm w, hχH _ (Subgroup.mem_sup_right ⟨w, rfl⟩), mul_one]

    have hsum : ∑ ξ ∈ Ξ, (((ξ * χ') ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = ∑ ξ ∈ Ξ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      refine Finset.sum_nbij (fun ξ => ξ * χ') hmem ?_ ?_ (fun ξ _ => rfl)
      · intro a _ b _ hab
        exact mul_right_cancel hab
      · intro b hb
        obtain ⟨a, ha, hab⟩ := Finset.surj_on_of_inj_on_of_card_le (fun ξ _ => ξ * χ') (fun a ha => hmem a ha)
          (fun a₁ a₂ _ _ h => mul_right_cancel h) le_rfl b hb
        exact ⟨a, ha, hab.symm⟩
    have hfac : ∑ ξ ∈ Ξ, (((ξ * χ') ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) =
        ((χ z : ℂˣ) : ℂ) * ∑ ξ ∈ Ξ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      rw [MonoidHom.mul_apply, hχ'app, Units.val_mul, mul_comm]
    have hne : ((χ z : ℂˣ) : ℂ) ≠ 1 := fun h => hχz (Units.val_eq_one.mp h)
    have key : (1 - ((χ z : ℂˣ) : ℂ)) * ∑ ξ ∈ Ξ, ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) = 0 := by
      rw [sub_mul, one_mul, ← hfac, hsum, sub_self]
    exact (mul_eq_zero.mp key).resolve_left (sub_ne_zero.mpr hne.symm)

end S_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul
end P2MW
export P2MW.S_NumberField_sum_apply_eq_zero_of_not_mem_principalIdeles_sup_range_idelicNorm_and_sum_apply_mul_idelicNorm_eq_card_mul (solution)
