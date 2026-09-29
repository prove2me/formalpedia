-- Prove2me | solution 1 for M4aHerbrand.idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/24af638e-f8cf-5458-9384-719ed1aa7cca

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Theorems.Thm_LT_Artin_eq_artinFrob_of_isArithFrobAt
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd
import Theorems.Thm_LanglandsTunnell_P2_Artin_exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd
import Theorems.Thm_NumberField_exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
import Theorems.Thm_M4aHerbrand_restrictNormalHom_idelicArtinMap_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
p2m_attr_erase "instance" "LanglandsTunnell.Lift48.instDecidablePredMatIsProjOrder LanglandsTunnell.Lift48.instDecidablePredMatIsPM1 FrobeniusDensity.isMaximal_ratPrimeIdeal LanglandsTunnell.P2.primeOver_finite LanglandsTunnell.P2.primeOver_isMaximal instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "AutomorphicForm.CuspidalityNotion.mk.injEq AutomorphicForm.HeckeEigensystem.twist_b AutomorphicForm.satakePow_zero AutomorphicForm.HeckeEigensystem.twist_a AutomorphicForm.HeckeEigensystem.mk.injEq AutomorphicForm.HeckeEigensystem.mk.sizeOf_spec AutomorphicForm.DescentPackage.mk.injEq AutomorphicForm.DescentPackage.mk.sizeOf_spec AutomorphicForm.CuspidalityNotion.mk.sizeOf_spec AutomorphicForm.satakePow_one TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec NumberField.FiniteSIdele.fibre_inr NumberField.FiniteSIdele.fibre_inl GroupCohomology.RepPi.proj_hom_apply GroupCohomology.RepPi.map_hom_apply GroupCohomology.RepPi.piRepresentation_apply GroupCohomology.RepPi.lift_hom_apply Rep.coe_invariantsMap_apply Rep.tateH0Map_mk Rep.coe_tateHneg1Map_apply Representation.coe_normToInvariants_apply Representation.normBar_mk NumberField.AdeleRing.val_finiteUnitsComponent IsDedekindDomain.FiniteAdeleRing.val_unitsComponent NumberField.AdeleRing.val_finitePartUnits NumberField.AdeleRing.val_infiniteUnitsComponent IsLocalRing.principalUnits_zero"
set_option autoImplicit false
p2m_open "NumberField IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt.M4aHerbrand M4aHerbrand.GenuineDescent HeckeCharacter LanglandsTunnell.P2.Artin"
open scoped IsMulCommutative NumberField.PlaceDecomp

namespace M4aHerbrand
p2m_export "M4aHerbrand" "infPart finPart idelesTrivialOn principalIdeles restrictNormalHom_idelicArtinMap_eq"
namespace LocFrob
p2m_open "M4aHerbrand"

open scoped Pointwise

section Inertia

variable {G : Type*} [Group G] {B : Type*} [CommRing B] [MulSemiringAction G B]

theorem inertia_smul_le [IsMulCommutative G] (g : G) (Q : Ideal B) :
    (g • Q).inertia G ≤ Q.inertia G := by
  intro σ hσ y
  have h : σ • (g • y) - g • y ∈ g • Q := hσ (g • y)
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at h
  simp only [smul_sub, smul_smul, inv_mul_cancel, one_smul] at h
  have hc : g⁻¹ * (σ * g) = σ := by rw [mul_comm σ g, inv_mul_cancel_left]
  rw [hc] at h
  exact h

theorem inertia_smul_eq [IsMulCommutative G] (g : G) (Q : Ideal B) :
    (g • Q).inertia G = Q.inertia G := by
  refine le_antisymm (inertia_smul_le g Q) ?_
  have h := inertia_smul_le g⁻¹ (g • Q)
  rwa [inv_smul_smul] at h

end Inertia

theorem inertia_eq_bot_of_inertia_eq_bot
    (E L : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L]
    [IsGalois E L] [IsMulCommutative (L ≃ₐ[E] L)]
    (p : Ideal (𝓞 E)) (Q₀ : Ideal (𝓞 L)) [Q₀.IsPrime] [Q₀.LiesOver p]
    (h0 : Q₀.inertia (L ≃ₐ[E] L) = ⊥) (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver p] :
    Q.inertia (L ≃ₐ[E] L) = ⊥ := by
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup p Q₀ Q (L ≃ₐ[E] L)
  rw [← hσ, inertia_smul_eq, h0]

theorem algebraMap_ringOfIntegers_smul_restrictNormalHom
    (E L F : Type*) [Field E] [Field L] [Field F]
    [Algebra E L] [Algebra E F] [Algebra L F] [IsScalarTower E L F] [Normal E L]
    (φ : F ≃ₐ[E] F) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 F) (AlgEquiv.restrictNormalHom L φ • x) = φ • algebraMap (𝓞 L) (𝓞 F) x := by
  apply RingOfIntegers.coe_injective
  change algebraMap L F ((AlgEquiv.restrictNormalHom L φ) (x : L)) = φ (algebraMap L F (x : L))
  exact AlgEquiv.restrictNormal_commutes φ L x

theorem isArithFrobAt_restrictNormalHom
    (E L F : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra E F] [Algebra L F] [IsScalarTower E L F] [IsGalois E F] [IsGalois E L]
    {φ : F ≃ₐ[E] F} {P : Ideal (𝓞 F)}
    (H : IsArithFrobAt (𝓞 E) φ P) :
    IsArithFrobAt (𝓞 E) (AlgEquiv.restrictNormalHom L φ) (P.under (𝓞 L)) := by
  unfold IsArithFrobAt AlgHom.IsArithFrobAt at H ⊢
  intro x
  rw [Ideal.under_under, Ideal.under_def, Ideal.mem_comap, map_sub, map_pow,
    MulSemiringAction.toAlgHom_apply, algebraMap_ringOfIntegers_smul_restrictNormalHom E L F]
  have h := H (algebraMap (𝓞 L) (𝓞 F) x)
  rwa [MulSemiringAction.toAlgHom_apply] at h

theorem mem_fixingSubgroup_of_restrictNormalHom_apply_eq
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    (L : IntermediateField E F) [Normal E L] (σ : F ≃ₐ[E] F)
    (h : ∀ y : L, AlgEquiv.restrictNormalHom L σ y = y) : σ ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have h1 := AlgEquiv.restrictNormalHom_apply L σ ⟨y, hy⟩
  rw [h] at h1
  exact h1.symm

section InertiaField

variable (E F : Type*) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
  [IsMulCommutative (F ≃ₐ[E] F)]

attribute [local instance] Ideal.Quotient.field in

theorem inertia_under_inertiaField_eq_bot (w : HeightOneSpectrum (𝓞 F))
    (L : IntermediateField E F) (hL : L = IntermediateField.fixedField (w.asIdeal.inertia (F ≃ₐ[E] F))) :
    (w.asIdeal.under (𝓞 L)).inertia (L ≃ₐ[E] L) = ⊥ := by
  subst hL
  set I := w.asIdeal.inertia (F ≃ₐ[E] F) with hIdef
  set L : IntermediateField E F := IntermediateField.fixedField I with hLdef
  set p : Ideal (𝓞 E) := w.asIdeal.under (𝓞 E) with hpdef
  set QL : Ideal (𝓞 L) := w.asIdeal.under (𝓞 L) with hQLdef
  have hp : p ≠ ⊥ := (HeightOneSpectrum.under (𝓞 E) w).ne_bot
  have hQL : QL ≠ ⊥ := (HeightOneSpectrum.under (𝓞 L) w).ne_bot
  haveI : p.IsMaximal := (HeightOneSpectrum.under (𝓞 E) w).isMaximal
  haveI : QL.IsMaximal := (HeightOneSpectrum.under (𝓞 L) w).isMaximal
  haveI : w.asIdeal.IsMaximal := w.isMaximal
  haveI : w.asIdeal.LiesOver p := ⟨rfl⟩
  haveI : w.asIdeal.LiesOver QL := ⟨rfl⟩
  haveI : QL.LiesOver p := ⟨(Ideal.under_under (A := 𝓞 E) (B := 𝓞 L) (𝔓 := w.asIdeal)).symm⟩
  haveI : Finite (𝓞 E ⧸ p) := Ideal.finiteQuotientOfFreeOfNeBot p hp
  haveI : Finite (𝓞 L ⧸ QL) := Ideal.finiteQuotientOfFreeOfNeBot QL hQL

  have e1 : Nat.card I = p.ramificationIdxIn (𝓞 F) :=
    Ideal.card_inertia_eq_ramificationIdxIn p w.asIdeal
  have e2 : Nat.card (w.asIdeal.inertia (F ≃ₐ[L] F)) = QL.ramificationIdxIn (𝓞 F) :=
    Ideal.card_inertia_eq_ramificationIdxIn QL w.asIdeal
  have e3 : Nat.card (QL.inertia (L ≃ₐ[E] L)) = p.ramificationIdxIn (𝓞 L) :=
    Ideal.card_inertia_eq_ramificationIdxIn p QL

  have hmapp : Ideal.map (algebraMap (𝓞 E) (𝓞 F)) p ≠ ⊥ :=
    fun h => hp ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective E F)).mp h)
  have hmapQ : Ideal.map (algebraMap (𝓞 L) (𝓞 F)) QL ≠ ⊥ :=
    fun h => hQL ((Ideal.map_eq_bot_iff_of_injective (RingOfIntegers.algebraMap.injective L F)).mp h)
  have tower : p.ramificationIdxIn (𝓞 L) * QL.ramificationIdxIn (𝓞 F) = p.ramificationIdxIn (𝓞 F) :=
    Ideal.ramificationIdxIn_mul_ramificationIdxIn QL (L ≃ₐ[E] L) (𝓞 F) (F ≃ₐ[E] F) (F ≃ₐ[L] F)

  have hLfix : L.fixingSubgroup = I := IntermediateField.fixingSubgroup_fixedField I
  have e4 : Nat.card (w.asIdeal.inertia (F ≃ₐ[L] F)) = Nat.card I := Nat.card_congr
    { toFun := fun σ => ⟨σ.1.restrictScalars E, fun x => σ.2 x⟩
      invFun := fun τ => ⟨IntermediateField.fixingSubgroupEquiv L ⟨τ.1, by rw [hLfix]; exact τ.2⟩,
        fun x => τ.2 x⟩
      left_inv := fun σ => Subtype.ext (AlgEquiv.ext fun _ => rfl)
      right_inv := fun τ => Subtype.ext (AlgEquiv.ext fun _ => rfl) }
  have hI0 : Nat.card I ≠ 0 := Nat.card_pos.ne'
  rw [Subgroup.eq_bot_iff_card, e3]
  rw [← e1, ← e2, e4] at tower
  exact (mul_eq_right₀ hI0).mp tower

end InertiaField

theorem exists_isAdmissibleModulusOfDegree_not_dvd
    (E L : Type*) [Field E] [NumberField E] [Field L] [NumberField L] [Algebra E L] [IsGalois E L]
    (v : HeightOneSpectrum (𝓞 E)) (hv0 : (primeAbove E L v).inertia (L ≃ₐ[E] L) = ⊥) (n : ℕ) :
    ∃ 𝔣L : Ideal (𝓞 E), NumberField.NormIndex.IsAdmissibleModulusOfDegree E L n 𝔣L ∧ ¬ v.asIdeal ∣ 𝔣L := by
  obtain ⟨𝔯, h𝔯, hram⟩ := exists_ne_bot_forall_inertia_primeAbove_ne_bot_dvd E L
  obtain ⟨k, 𝔯', hndvd, hfac⟩ := WfDvdMonoid.max_power_factor h𝔯 v.irreducible
  have h𝔯' : 𝔯' ≠ ⊥ := by
    intro h
    apply h𝔯
    rw [hfac, h, Ideal.mul_bot]
  have hram' : ∀ v' : HeightOneSpectrum (𝓞 E),
      (primeAbove E L v').inertia (L ≃ₐ[E] L) ≠ ⊥ → v'.asIdeal ∣ 𝔯' := by
    intro v' hv'
    have hd : v'.asIdeal ∣ v.asIdeal ^ k * 𝔯' := hfac ▸ hram v' hv'
    rcases v'.prime.dvd_or_dvd hd with h | h
    · exfalso
      have h1 : v'.asIdeal ∣ v.asIdeal := v'.prime.dvd_of_dvd_pow h
      have h2 : v.asIdeal = v'.asIdeal :=
        (v.isMaximal.eq_of_le v'.isPrime.ne_top (Ideal.le_of_dvd h1))
      have h3 : v' = v := HeightOneSpectrum.ext h2.symm
      subst h3
      exact hv' hv0
    · exact h
  obtain ⟨𝔣L, -, hsupp, hadmL⟩ :=
    exists_dvd_and_isAdmissibleModulusOfDegree_of_ramified_dvd E L 𝔯' h𝔯' hram' n
  exact ⟨𝔣L, hadmL, fun h => hndvd (hsupp v h)⟩

section Single

variable (E : Type*) [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {x : (AdeleRing (𝓞 E) E)ˣ}

theorem snd_apply_eq_one_of_mem_idelesTrivialOn
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (v' : HeightOneSpectrum (𝓞 E)) (hne : v' ≠ v) :
    ((x : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v' = 1 := by
  have h := hx.2 v' (Set.mem_compl_singleton_iff.mpr hne)
  show (finPart v' x : v'.adicCompletion E) = 1
  rw [h, Units.val_one]

theorem fst_eq_one_of_mem_idelesTrivialOn
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) :
    (x : AdeleRing (𝓞 E) E).1 = 1 := by
  show (infPart x : InfiniteAdeleRing E) = 1
  rw [hx.1, Units.val_one]

theorem placeOrd_projFin_eq_zero_of_ne
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    (v' : HeightOneSpectrum (𝓞 E)) (hne : v' ≠ v) :
    placeOrd E (projFin E x) v' = 0 := by
  rw [placeOrd_eq_zero_iff]
  show Valued.v (((x : AdeleRing (𝓞 E) E).2 : FiniteAdeleRing (𝓞 E) E) v') = 1
  rw [snd_apply_eq_one_of_mem_idelesTrivialOn E hx v' hne, map_one]

theorem isAdjuster_one_of_mem_idelesTrivialOn
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E))))
    {𝔪 : Ideal (𝓞 E)} (h𝔪 : ¬ v.asIdeal ∣ 𝔪) : IsAdjuster E 𝔪 x 1 := by
  have e1 : x * (Units.map (algebraMap E (AdeleRing (𝓞 E) E)) (1 : Eˣ))⁻¹ = x := by
    rw [map_one, inv_one, mul_one]
  refine ⟨fun v' hv' => ?_, fun τ => ?_⟩
  · have hne : v' ≠ v := fun h => h𝔪 (h ▸ hv')
    rw [e1, snd_apply_eq_one_of_mem_idelesTrivialOn E hx v' hne, sub_self, map_one, map_zero]
    exact ⟨rfl, zero_le'⟩
  · rw [e1]
    exact archSign_of_fst_eq_one E τ (fst_eq_one_of_mem_idelesTrivialOn E hx)

end Single

end M4aHerbrand.LocFrob

open M4aHerbrand.LocFrob

theorem solution
    (E F : Type) [Field E] [NumberField E] [Field F] [NumberField F] [Algebra E F] [IsGalois E F]
    [IsMulCommutative (F ≃ₐ[E] F)]

    (𝔣 : Ideal (𝓞 E)) (hadm : NumberField.NormIndex.IsAdmissibleModulusOfDegree E F (Module.finrank E F) 𝔣)
    (r : (AdeleRing (𝓞 E) E)ˣ →* (F ≃ₐ[E] F))
    (hr₁ : principalIdeles (𝓞 E) E ≤ r.ker)
    (hr₂ : r.ker = principalIdeles (𝓞 E) E ⊔ (genuineBaseChange E F).idelicNorm.range)
    (hr₃ : Function.Surjective r)
    (hr₄ : ∀ u : (AdeleRing (𝓞 E) E)ˣ, IsAdjuster E 𝔣 u 1 →
      r u = ∏ᶠ v : HeightOneSpectrum (𝓞 E), artinFrob E F v ^ placeOrd E (projFin E u) v)

    (v : HeightOneSpectrum (𝓞 E)) (a : (v.adicCompletion E)ˣ) (x : (AdeleRing (𝓞 E) E)ˣ)
    (hx : x ∈ idelesTrivialOn (𝓞 E) E ({v}ᶜ : Set (HeightOneSpectrum (𝓞 E)))) (hxv : finPart v x = a)

    (w : HeightOneSpectrum (𝓞 F)) (hw : w.under (𝓞 E) = v)
    (φ : F ≃ₐ[E] F) (hφ : IsArithFrobAt (𝓞 E) φ w.asIdeal) :
    r x * (φ ^ placeOrd E (projFin E x) v)⁻¹ ∈ w.asIdeal.inertia (F ≃ₐ[E] F) := by
  classical
  set I := w.asIdeal.inertia (F ≃ₐ[E] F) with hIdef

  set L : IntermediateField E F := IntermediateField.fixedField I with hLdef
  haveI : IsGalois E L := IsGalois.of_fixedField_normal_subgroup I
  haveI : IsMulCommutative (L ≃ₐ[E] L) := ⟨⟨fun a b => by
    obtain ⟨a', rfl⟩ := AlgEquiv.restrictNormalHom_surjective F a
    obtain ⟨b', rfl⟩ := AlgEquiv.restrictNormalHom_surjective F b
    rw [← map_mul, ← map_mul, mul_comm]⟩⟩
  have hLfix : L.fixingSubgroup = I := IntermediateField.fixingSubgroup_fixedField I

  have hv : w.asIdeal.under (𝓞 E) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hw
  have key : (w.asIdeal.under (𝓞 L)).inertia (L ≃ₐ[E] L) = ⊥ :=
    inertia_under_inertiaField_eq_bot E F w L rfl
  haveI : (w.asIdeal.under (𝓞 L)).LiesOver v.asIdeal :=
    ⟨by rw [Ideal.under_under]; exact hv.symm⟩
  have hv0 : (primeAbove E L v).inertia (L ≃ₐ[E] L) = ⊥ :=
    inertia_eq_bot_of_inertia_eq_bot E L v.asIdeal (w.asIdeal.under (𝓞 L)) key (primeAbove E L v)

  obtain ⟨𝔣L, hadmL, hv𝔣L⟩ :=
    exists_isAdmissibleModulusOfDegree_not_dvd E L v hv0 (Module.finrank E L)
  obtain ⟨rL, hrL₁, hrL₂, hrL₃, hrL₄⟩ :=
    NumberField.exists_idelicArtinMap_ker_eq_and_surjective_and_eq_finprod_artinFrob_of_isAdmissibleModulusOfDegree_finrank
      E L 𝔣L hadmL

  have hrLx : rL x = artinFrob E L v ^ placeOrd E (projFin E x) v := by
    rw [hrL₄ x (isAdjuster_one_of_mem_idelesTrivialOn E hx hv𝔣L)]
    exact finprod_eq_single _ v fun v' hne => by
      rw [placeOrd_projFin_eq_zero_of_ne E hx v' hne, zpow_zero]

  have hcompat : AlgEquiv.restrictNormalHom L (r x) = rL x :=
    M4aHerbrand.restrictNormalHom_idelicArtinMap_eq E F L 𝔣 hadm r hr₁ hr₂ hr₃ hr₄
      𝔣L hadmL rL hrL₁ hrL₂ hrL₃ hrL₄ x
  have hφL : AlgEquiv.restrictNormalHom L φ = artinFrob E L v :=
    LT.Artin.eq_artinFrob_of_isArithFrobAt E L v (isArithFrobAt_restrictNormalHom E L F hφ)
      (by rw [Ideal.under_under]; exact hv) key

  have hres : AlgEquiv.restrictNormalHom L (r x * (φ ^ placeOrd E (projFin E x) v)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_zpow, hcompat, hrLx, hφL, mul_inv_cancel]
  rw [← hLfix]
  exact mem_fixingSubgroup_of_restrictNormalHom_apply_eq L _ fun y => by rw [hres]; rfl

end S_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt
end P2MW
export P2MW.S_M4aHerbrand_idelicArtinMap_single_mul_zpow_inv_mem_inertia_of_isArithFrobAt (solution)
