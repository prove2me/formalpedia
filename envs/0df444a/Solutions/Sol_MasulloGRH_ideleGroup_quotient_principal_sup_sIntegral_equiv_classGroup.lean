-- Prove2me | solution 1 for MasulloGRH.ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:30:54.247998+00:00
-- url     : https://prove2.me/submissions/988c8dee-fe6c-4692-9e31-3ce99f7f37b3

import Mathlib
import Definitions.Def_MasulloGRH_SAdeles
import Theorems.Thm_IsDedekindDomain_FiniteAdeleRing_exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
import Theorems.Thm_NumberField_SClassGroup_pic_localization_exact

open NumberField IsDedekindDomain

set_option autoImplicit false

namespace Sol_MasulloGRH_ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup

open scoped nonZeroDivisors

variable {F : Type*} [Field F] [NumberField F]

/-- A unit of a valued ring has valuation one iff it and its inverse are integral. -/
theorem valued_eq_one_iff (v : HeightOneSpectrum (𝓞 F)) (x : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    Valued.v ((x : FiniteAdeleRing (𝓞 F) F) v) = 1 ↔
      ((x : FiniteAdeleRing (𝓞 F) F) v ∈ v.adicCompletionIntegers F ∧
        ((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v ∈
          v.adicCompletionIntegers F) := by
  have hmul : Valued.v ((x : FiniteAdeleRing (𝓞 F) F) v) *
      Valued.v (((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    rw [← map_mul]
    have : (x : FiniteAdeleRing (𝓞 F) F) v *
        ((x⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v = 1 := by
      have h := congrArg (fun y : FiniteAdeleRing (𝓞 F) F => y v) x.mul_inv
      exact h
    rw [this, map_one]
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro h
    rw [h, one_mul] at hmul
    exact ⟨h.le, hmul.le⟩
  · rintro ⟨h1, h2⟩
    exact eq_one_of_one_le_mul_left h1 h2 hmul.ge

/-- The finite part of an idele. -/
noncomputable abbrev pr (F : Type*) [Field F] [NumberField F] :
    MasulloGRH.IdeleGroup F →* (FiniteAdeleRing (𝓞 F) F)ˣ :=
  Units.map (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toMonoidHom

theorem pr_surjective : Function.Surjective (pr F) := by
  intro x
  refine ⟨MulEquiv.prodUnits.symm (1, x), ?_⟩
  ext
  rfl

theorem pr_principalIdele (k : Fˣ) :
    pr F (MasulloGRH.principalIdele F k) =
      Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) : F →* FiniteAdeleRing (𝓞 F) F) k := by
  ext
  rfl

theorem mem_sup_iff (T : Set (HeightOneSpectrum (𝓞 F))) (g : MasulloGRH.IdeleGroup F) :
    g ∈ MasulloGRH.principalIdeles F ⊔ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T ↔
      pr F g ∈ (Units.map (algebraMap F (FiniteAdeleRing (𝓞 F) F) :
          F →* FiniteAdeleRing (𝓞 F) F)).range ⊔
        IsDedekindDomain.FiniteAdeleRing.unitIdelesOutside (𝓞 F) F T := by
  rw [Subgroup.mem_sup, Subgroup.mem_sup]
  constructor
  · rintro ⟨y, ⟨k, rfl⟩, z, hz, rfl⟩
    exact ⟨_, ⟨k, rfl⟩, pr F z, hz, by rw [map_mul, pr_principalIdele]⟩
  · rintro ⟨y, ⟨k, rfl⟩, z, hz, hyz⟩
    refine ⟨MasulloGRH.principalIdele F k, ⟨k, rfl⟩, (MasulloGRH.principalIdele F k)⁻¹ * g, ?_,
      mul_inv_cancel_left _ _⟩
    rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff]
    change pr F ((MasulloGRH.principalIdele F k)⁻¹ * g) ∈ _
    rw [map_mul, map_inv, pr_principalIdele, ← hyz, inv_mul_cancel_left]
    exact hz

theorem coe_unitIdelesOutside (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ((NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (Sf : Set (HeightOneSpectrum (𝓞 F))) :
      Subgroup (MasulloGRH.IdeleGroup F)) : Set (MasulloGRH.IdeleGroup F)) =
      MasulloGRH.sIntegralIdeles Sf := by
  ext g
  show (∀ v : HeightOneSpectrum (𝓞 F), v ∉ (Sf : Set (HeightOneSpectrum (𝓞 F))) → _) ↔
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ Sf → _
  refine forall_congr' fun v => ?_
  rw [Finset.mem_coe]
  refine imp_congr_right fun _ => ?_
  exact (valued_eq_one_iff v (pr F g)).symm

theorem algebraMap_integer_empty_bijective :
    Function.Bijective (algebraMap (𝓞 F)
      (((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))).integer F)) := by
  constructor
  · intro a b h
    have h' := congrArg (fun x : (((∅ : Finset (HeightOneSpectrum (𝓞 F))) :
      Set (HeightOneSpectrum (𝓞 F))).integer F) => (x : F)) h
    exact IsFractionRing.injective (𝓞 F) F h'
  · rintro ⟨x, hx⟩
    obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F x
      (fun v => hx v (by simp))
    exact ⟨r, Subtype.ext hr⟩

theorem pic_mapAlgebra_bijective :
    Function.Bijective (CommRing.Pic.mapAlgebra (𝓞 F)
      (((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))).integer F)) := by
  set A0 := (((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))).integer F)
  let e : 𝓞 F ≃+* A0 := RingEquiv.ofBijective (algebraMap (𝓞 F) A0) algebraMap_integer_empty_bijective
  have h1 : CommRing.Pic.mapAlgebra (𝓞 F) A0 = CommRing.Pic.mapRingHom e.toRingHom := by
    rw [← CommRing.Pic.mapRingHom_algebraMap]
    rfl
  rw [h1]
  refine Function.bijective_iff_has_inverse.mpr ⟨CommRing.Pic.mapRingHom e.symm.toRingHom, ?_, ?_⟩
  · intro M
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have : e.symm.toRingHom.comp e.toRingHom = RingHom.id (𝓞 F) := by
      ext x; simp
    rw [this, CommRing.Pic.mapRingHom_id_apply]
  · intro M
    rw [CommRing.Pic.mapRingHom_mapRingHom]
    have : e.toRingHom.comp e.symm.toRingHom = RingHom.id A0 := by
      ext x; simp
    rw [this, CommRing.Pic.mapRingHom_id_apply]

end Sol_MasulloGRH_ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup

open MasulloGRH Sol_MasulloGRH_ideleGroup_quotient_principal_sup_sIntegral_equiv_classGroup in
theorem solution (F : Type*) [Field F]
    [NumberField F] (Sf : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ U : Subgroup (IdeleGroup F), (U : Set (IdeleGroup F)) = sIntegralIdeles Sf ∧
      Nonempty ((IdeleGroup F ⧸ (principalIdeles F ⊔ U)) ≃* ClassGroup (SIntegers Sf)) := by
  classical
  obtain ⟨φ, -, -, hφs, -, hφT⟩ :=
    IsDedekindDomain.FiniteAdeleRing.exists_contentHom_eq_finprod_and_mem_sup_unitIdelesOutside_iff
      (𝓞 F) F
  have key := NumberField.SClassGroup.pic_localization_exact F ∅ Sf (Finset.empty_subset _)
  dsimp only at key
  obtain ⟨hps, hpker, -⟩ := key
  set A0 := (((∅ : Finset (HeightOneSpectrum (𝓞 F))) : Set (HeightOneSpectrum (𝓞 F))).integer F)
    with hA0
  set p := CommRing.Pic.mapRingHom (Subalgebra.inclusion (S := A0) (T := SIntegers Sf)
      (fun _ hx v hv => hx v (fun hvS => hv (Finset.empty_subset Sf hvS)))).toRingHom with hp
  let M : ClassGroup (𝓞 F) →* CommRing.Pic A0 :=
    (CommRing.Pic.mapAlgebra (𝓞 F) A0).comp (ClassGroup.equivPic (𝓞 F)).toMonoidHom
  have hM : Function.Bijective M :=
    pic_mapAlgebra_bijective.comp (ClassGroup.equivPic (𝓞 F)).bijective
  let ψ : IdeleGroup F →* ClassGroup (SIntegers Sf) :=
    (ClassGroup.equivPic (SIntegers Sf)).symm.toMonoidHom.comp
      (p.comp (M.comp ((ClassGroup.mk F).comp (φ.comp (pr F)))))
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨P, hP⟩ := (ClassGroup.equivPic (SIntegers Sf)).symm.surjective y
    obtain ⟨Q, hQ⟩ := hps P
    obtain ⟨c, hc⟩ := hM.2 Q
    obtain ⟨I, hI⟩ : ∃ I, ClassGroup.mk F I = c :=
      ClassGroup.induction (K := F) (P := fun c => ∃ I, ClassGroup.mk F I = c)
        (fun I => ⟨I, rfl⟩) c
    obtain ⟨x, hx⟩ := hφs I
    obtain ⟨g, hg⟩ := pr_surjective x
    refine ⟨g, ?_⟩
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hg, hx, hI, hc, hQ, hP]
  set U := NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (Sf : Set (HeightOneSpectrum (𝓞 F)))
    with hU
  have hker : ψ.ker = principalIdeles F ⊔ U := by
    ext g
    rw [MonoidHom.mem_ker, mem_sup_iff, hφT]
    have hset : {c : ClassGroup (𝓞 F) | ∃ v ∈ (Sf : Set (HeightOneSpectrum (𝓞 F))),
        ∃ h : v.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 F)), ClassGroup.mk0 ⟨v.asIdeal, h⟩ = c} =
        Set.range (fun v : ↥(Sf \ ∅) => ClassGroup.mk0
          ⟨v.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.1.ne_bot⟩) := by
      ext c
      constructor
      · rintro ⟨v, hv, h, rfl⟩
        exact ⟨⟨v, by simpa using hv⟩, rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨v.1, by simpa using v.2, _, rfl⟩
    rw [hset, Subgroup.mem_closure_range_iff_of_fintype]
    have h1 : ψ g = 1 ↔ p (M (ClassGroup.mk F (φ (pr F g)))) = 1 := by
      simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      exact MulEquiv.map_eq_one_iff _
    rw [h1, hpker]
    refine exists_congr fun n => ?_
    have hc : CommRing.Pic.mapAlgebra (𝓞 F) A0 (∏ v : ↥(Sf \ ∅),
        (ClassGroup.equivPic (𝓞 F)) (ClassGroup.mk0
          ⟨v.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.1.ne_bot⟩) ^ n v) =
        M (∏ v : ↥(Sf \ ∅), ClassGroup.mk0
          ⟨v.1.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.1.ne_bot⟩ ^ n v) := by
      simp only [M, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, map_prod, map_zpow]
    rw [hc]
    exact ⟨fun h => (hM.1 h).symm, fun h => by rw [h]⟩
  refine ⟨U, coe_unitIdelesOutside Sf, ⟨?_⟩⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)
