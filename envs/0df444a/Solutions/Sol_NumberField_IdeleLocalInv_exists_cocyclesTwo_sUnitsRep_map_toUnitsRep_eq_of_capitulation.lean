-- Prove2me | solution 1 for NumberField.IdeleLocalInv.exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2c9121ed-b8ed-5851-b9f1-5688b0b612be

import Mathlib
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_NumberField_IdeleLocalInvariant
import Theorems.Thm_NumberField_SIdele_existsUnique_map_eq_of_forall_map_prG_eq_zero
import Theorems.Thm_NumberField_AdeleRing_unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower
import Theorems.Thm_NumberField_AdeleRing_principalIdeles_inf_unitIdelesOutside_eq_map_unit
import Theorems.Thm_groupCohomology_exists_map_eq_of_map_eq_zero_of_injective_of_surjective
import Theorems.Thm_groupCohomology_exists_corestriction_comp_res_eq_index_nsmul
import Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_unitsAct_map_genuineBaseChange
import Theorems.Thm_NumberField_IdeleLocalInv_map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation
import Theorems.Thm_NumberField_SIdele_exists_hom_obj_ideles_injective_of_ideleGaloisDescent
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
p2m_attr_erase "instance" "instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing NumberField.instHenselianLocalRingAdicCompletionIntegers instIsAdicCompleteMaximalIdealOfCompactSpace NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain M4aHerbrand
open scoped NumberField.PlaceDecomp

noncomputable section
namespace SLCAssembly

open M4aHerbrand NumberField.AdeleRing

section Generic
universe u
variable {k G : Type u} [CommRing k] [Group G]

theorem exists_lift_of_injective {X Y Z : Rep k G}
    (ψ : X ⟶ Z) (i : Y ⟶ Z) (hi : Function.Injective i.hom) (h : ∀ x : X, ∃ y : Y, i.hom y = ψ.hom x) :
    ∃ θ : X ⟶ Y, θ ≫ i = ψ := by
  classical
  choose t ht using h
  have hadd : ∀ x x', t (x + x') = t x + t x' := fun x x' =>
    hi (by rw [map_add, ht, ht, ht, map_add])
  have hsmul : ∀ (c : k) x, t (c • x) = c • t x := fun c x =>
    hi (by rw [map_smul, ht, ht, map_smul])
  let θl : X →ₗ[k] Y := { toFun := t, map_add' := hadd, map_smul' := hsmul }
  refine ⟨Rep.ofHom ⟨θl, fun g => LinearMap.ext fun x => hi ?_⟩, ?_⟩
  · show i.hom (t (X.ρ g x)) = i.hom (Y.ρ g (t x))
    rw [ht, Rep.hom_comm_apply, Rep.hom_comm_apply, ht]
  · exact Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => ht x))

theorem map_id_comp_apply {A B C : Rep k G} (φ : A ⟶ B) (ψ : B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map (MonoidHom.id G) (φ ≫ ψ) n).hom x =
      (groupCohomology.map (MonoidHom.id G) ψ n).hom ((groupCohomology.map (MonoidHom.id G) φ n).hom x) := by
  rw [groupCohomology.map_id_comp]; rfl

theorem map_res_comp_apply {H : Type u} [Group H] {A B : Rep k H} {C : Rep k G} (f : G →* H)
    (φ : A ⟶ B) (ψ : Rep.res f B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f ((Rep.resFunctor f).map φ ≫ ψ) n).hom x =
      (groupCohomology.map f ψ n).hom ((groupCohomology.map (MonoidHom.id H) φ n).hom x) := by
  rw [show groupCohomology.map f ((Rep.resFunctor f).map φ ≫ ψ) n =
      groupCohomology.map (MonoidHom.id H) φ n ≫ groupCohomology.map f ψ n from
    groupCohomology.map_comp (MonoidHom.id H) f φ ψ n]
  rfl

theorem map_comp_id_apply {H : Type u} [Group H] {A : Rep k H} {B C : Rep k G} (f : G →* H)
    (φ : Rep.res f A ⟶ B) (ψ : B ⟶ C) (n : ℕ) (x : groupCohomology A n) :
    (groupCohomology.map f (φ ≫ ψ) n).hom x =
      (groupCohomology.map (MonoidHom.id G) ψ n).hom ((groupCohomology.map f φ n).hom x) := by
  rw [show groupCohomology.map f (φ ≫ ψ) n = groupCohomology.map f φ n ≫ groupCohomology.map (MonoidHom.id G) ψ n from
    groupCohomology.map_comp f (MonoidHom.id G) φ ψ n]
  rfl

end Generic

section Level
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (D : IdeleGaloisDescent (𝓞 K) E K)
  [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]

abbrev I : Rep ℤ (K ≃ₐ[E] K) := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ

abbrev Usub : Subgroup (AdeleRing (𝓞 K) K)ˣ := unitIdelesOutside (𝓞 K) K {w | w.under (𝓞 E) ∈ S}

abbrev Msub : Subgroup (AdeleRing (𝓞 K) K)ˣ := principalIdeles (𝓞 K) K ⊔ Usub E K S

variable {E K S}

theorem smul_mem_principalIdeles (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (g : K ≃ₐ[E] K) {x : (AdeleRing (𝓞 K) K)ˣ} (hx : x ∈ principalIdeles (𝓞 K) K) :
    g • x ∈ principalIdeles (𝓞 K) K := by
  rw [hactI, ← D.map_principalIdeles g]
  exact ⟨x, hx, rfl⟩

theorem smul_mem_Usub (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (g : K ≃ₐ[E] K) {x : (AdeleRing (𝓞 K) K)ˣ} (hx : x ∈ Usub E K S) : g • x ∈ Usub E K S := by
  obtain ⟨Ψ, -, hrange, -⟩ := NumberField.SIdele.exists_hom_obj_ideles_injective_of_ideleGaloisDescent E K S D hactI
  obtain ⟨t, ht⟩ := (hrange x).2 hx
  refine (hrange (g • x)).1 ⟨(NumberField.SIdele.obj E K S).ρ g t, ?_⟩
  rw [Rep.hom_comm_apply, ht]
  rfl

theorem smul_mem_Msub (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (g : K ≃ₐ[E] K) {x : (AdeleRing (𝓞 K) K)ˣ} (hx : x ∈ Msub E K S) : g • x ∈ Msub E K S := by
  obtain ⟨a, ha, u, hu, rfl⟩ := Subgroup.mem_sup.1 hx
  rw [smul_mul']
  exact Subgroup.mul_mem_sup (smul_mem_principalIdeles D hactI g ha) (smul_mem_Usub D hactI g hu)

variable (E K S)

abbrev Mmod : Submodule ℤ (Additive (AdeleRing (𝓞 K) K)ˣ) := (Msub E K S).toAddSubgroup.toIntSubmodule

noncomputable abbrev M (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x) :
    Rep ℤ (K ≃ₐ[E] K) :=
  Rep.of ((I E K).ρ.subrepresentation (Mmod E K S) fun g x hx => smul_mem_Msub D hactI g hx)

noncomputable def ι (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x) :
    M E K S D hactI ⟶ I E K :=
  Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

variable (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)

theorem ι_hom_apply (m : M E K S D hactI) : (ι E K S D hactI).hom m = m.1 := rfl

theorem ι_injective : Function.Injective (ι E K S D hactI).hom := Subtype.val_injective

theorem ι_range (w : (AdeleRing (𝓞 K) K)ˣ) :
    (∃ m, (ι E K S D hactI).hom m = Additive.ofMul w) ↔ w ∈ Msub E K S :=
  ⟨fun ⟨m, hm⟩ => by
    rw [ι_hom_apply] at hm
    have h2 : Additive.toMul m.1 ∈ Msub E K S := m.2
    rwa [hm] at h2, fun h => ⟨⟨Additive.ofMul w, h⟩, rfl⟩⟩

end Level

end SLCAssembly
end

noncomputable section
namespace SLCAssembly
open M4aHerbrand NumberField.AdeleRing

section Level
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (D : IdeleGaloisDescent (𝓞 K) E K)
  [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
  (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)

theorem exists_codRestrict {X : Rep ℤ (K ≃ₐ[E] K)} (φ : X ⟶ I E K)
    (hφ : ∀ x : X, Additive.toMul (α := (AdeleRing (𝓞 K) K)ˣ) (φ.hom x) ∈ Msub E K S) :
    ∃ φM : X ⟶ M E K S D hactI, φM ≫ ι E K S D hactI = φ :=
  exists_lift_of_injective φ (ι E K S D hactI) (ι_injective E K S D hactI)
    fun x => ⟨⟨φ.hom x, hφ x⟩, rfl⟩

abbrev UinM : Submodule ℤ (M E K S D hactI) :=
  (Submodule.comap (Submodule.subtype (Mmod E K S)) ((Usub E K S).toAddSubgroup.toIntSubmodule))

theorem mem_UinM (m : M E K S D hactI) : m ∈ UinM E K S D hactI ↔ Additive.toMul m.1 ∈ Usub E K S := Iff.rfl

theorem UinM_stable (g : K ≃ₐ[E] K) : UinM E K S D hactI ≤ Submodule.comap ((M E K S D hactI).ρ g) (UinM E K S D hactI) := by
  intro m hm
  change (M E K S D hactI).ρ g m ∈ UinM E K S D hactI
  rw [mem_UinM]
  exact smul_mem_Usub D hactI g ((mem_UinM E K S D hactI m).1 hm)

abbrev Urep : Rep ℤ (K ≃ₐ[E] K) := Rep.of ((M E K S D hactI).ρ.subrepresentation (UinM E K S D hactI) (UinM_stable E K S D hactI))

def iU : Urep E K S D hactI ⟶ M E K S D hactI := Rep.ofHom ⟨Submodule.subtype _, fun _ => rfl⟩

theorem iU_hom_apply (u : Urep E K S D hactI) : (iU E K S D hactI).hom u = u.1 := rfl

abbrev Q : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepCokernel.obj (iU E K S D hactI)

abbrev qM : M E K S D hactI ⟶ Q E K S D hactI := GroupCohomology.RepCokernel.π (iU E K S D hactI)

theorem qM_apply_eq_zero_iff (m : M E K S D hactI) :
    (qM E K S D hactI).hom m = 0 ↔ Additive.toMul m.1 ∈ Usub E K S := by
  rw [GroupCohomology.RepCokernel.π_hom_apply_eq_zero_iff]
  constructor
  · rintro ⟨u, hu⟩
    have : (iU E K S D hactI).hom u = m := hu
    rw [← this, iU_hom_apply]
    exact u.2
  · intro h
    exact ⟨⟨m, h⟩, rfl⟩

end Level

end SLCAssembly
end

noncomputable section
namespace SLCAssembly
open M4aHerbrand M4aHerbrand.GenuineDescent NumberField.AdeleRing

section Torsion
variable {G : Type} [Group G] [Finite G]

theorem natCard_zsmul_eq_zero (A : Rep ℤ G) (x : groupCohomology A 2) : (Nat.card G : ℤ) • x = 0 := by
  obtain ⟨cor, hcor⟩ := groupCohomology.exists_corestriction_comp_res_eq_index_nsmul (⊥ : Subgroup G) A 2
  have hres : (groupCohomology.map (⊥ : Subgroup G).subtype (𝟙 (Rep.res (⊥ : Subgroup G).subtype A)) 2).hom x = 0 :=
    (ModuleCat.subsingleton_of_isZero (isZero_groupCohomology_succ_of_subsingleton (Rep.res (⊥ : Subgroup G).subtype A) 1)).elim _ _
  have := hcor x
  rw [hres, map_zero, Subgroup.index_bot] at this
  rw [natCast_zsmul]
  exact this.symm

theorem exists_ppow_zsmul_eq_zero_and_map_eq {A B : Rep ℤ G} (φ : A ⟶ B) (p : ℕ) [hp : Fact p.Prime]
    (y : groupCohomology B 2) (k : ℕ) (hy : (p ^ k : ℤ) • y = 0)
    (x : groupCohomology A 2) (hx : (groupCohomology.map (MonoidHom.id G) φ 2).hom x = y) :
    ∃ (x' : groupCohomology A 2) (k' : ℕ), (p ^ k' : ℤ) • x' = 0 ∧ (groupCohomology.map (MonoidHom.id G) φ 2).hom x' = y := by
  classical
  haveI : Nonempty G := ⟨1⟩
  obtain ⟨a, m, hm, hcard⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.card_pos (α := G)).ne' p hp.out.one_lt.ne'
  have hcop : IsCoprime (m : ℤ) ((p ^ k : ℕ) : ℤ) :=
    Nat.Coprime.isCoprime (Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm)
  obtain ⟨c, d, hcd⟩ := hcop
  refine ⟨(c * m) • x, a, ?_, ?_⟩
  · have h1 : (p ^ a : ℤ) • (c * (m : ℤ)) • x = (c * (Nat.card G : ℤ)) • x := by
      rw [hcard, ← mul_zsmul]
      congr 1
      push_cast
      ring
    rw [h1, mul_zsmul, natCard_zsmul_eq_zero, zsmul_zero]
  · rw [map_zsmul, hx]
    have h2 : c * (m : ℤ) = 1 - d * (p : ℤ) ^ k := by
      rw [← hcd]; push_cast; ring
    rw [h2, sub_zsmul, one_zsmul, mul_zsmul, hy, zsmul_zero, neg_zero, add_zero]

theorem exists_H2π_eq (A : Rep ℤ G) (x : groupCohomology A 2) :
    ∃ f : groupCohomology.cocycles₂ A, groupCohomology.H2π A f = x :=
  groupCohomology.H2_induction_on (C := fun x => ∃ f : groupCohomology.cocycles₂ A, groupCohomology.H2π A f = x) x
    fun f => ⟨f, rfl⟩

theorem map_zero_apply {H : Type} [Group H] {A : Rep ℤ H} {B : Rep ℤ G} (f : G →* H) (x : groupCohomology A 2) :
    (groupCohomology.map f (0 : Rep.res f A ⟶ B) 2).hom x = 0 := by
  have h : (groupCohomology.map f (0 : Rep.res f A ⟶ B) 2).hom x =
      (groupCohomology.map (MonoidHom.id G) (0 : B ⟶ B) 2).hom ((groupCohomology.map f (0 : Rep.res f A ⟶ B) 2).hom x) := by
    rw [← map_comp_id_apply, Limits.comp_zero]
  rw [h, show groupCohomology.map (MonoidHom.id G) (0 : B ⟶ B) 2 = 0 from (groupCohomology.functor ℤ G 2).map_zero B B]
  rfl

end Torsion

section Level
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  (S : Finset (HeightOneSpectrum (𝓞 E))) (D : IdeleGaloisDescent (𝓞 K) E K)
  [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
  (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)

abbrev F [MulDistribMulAction (K ≃ₐ[E] K) Kˣ] : Rep ℤ (K ≃ₐ[E] K) := Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ

variable [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]

theorem j_mem_Msub (j : F E K ⟶ I E K)
    (hj : ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a))
    (x : F E K) : Additive.toMul (α := (AdeleRing (𝓞 K) K)ˣ) (j.hom x) ∈ Msub E K S := by
  have hx : j.hom x = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Additive.toMul x)) :=
    hj (Additive.toMul x)
  have key : Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) (Additive.toMul x) ∈ Msub E K S :=
    Subgroup.mem_sup_left ⟨Additive.toMul x, rfl⟩
  rw [hx]
  exact key

end Level

end SLCAssembly
end

open M4aHerbrand.GenuineDescent NumberField.AdeleRing in

theorem solution
    (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
    [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K] [IsGalois E K'']
    (S : Finset (HeightOneSpectrum (𝓞 E)))

    (D : IdeleGaloisDescent (𝓞 K) E K)
    [MulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ]
    (hactI : ∀ (g : K ≃ₐ[E] K) (x : (AdeleRing (𝓞 K) K)ˣ), g • x = D.unitsAct g x)
    (prG : ∀ w : HeightOneSpectrum (𝓞 K),
      Rep.res (NumberField.PlaceDecomp.decomp E K w).subtype (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp E K w)) (w.adicCompletion K)ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 K)) (y : (AdeleRing (𝓞 K) K)ˣ), (prG w).hom (Additive.ofMul y) = Additive.ofMul (finPart w y))

    [MulDistribMulAction (K ≃ₐ[E] K) Kˣ]
    (hactF : ∀ (g : (K ≃ₐ[E] K)) (a : Kˣ), ((g • a : Kˣ) : K) = g (a : K))
    (j : (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) (AdeleRing (𝓞 K) K)ˣ))
    (hj : ∀ a : Kˣ, j.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a))

    (incl : Rep.res (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) ⟶ (Rep.ofMulDistribMulAction (K'' ≃ₐ[E] K'') K''ˣ))
    (hincl : ∀ a : Kˣ, incl.hom (Additive.ofMul a) = Additive.ofMul (Units.map (algebraMap K K'' : K →* K'') a))

    (p : ℕ) [Fact p.Prime]
    (hcap : ∀ (I : Ideal (𝓞 K)) (k : ℕ) (a : 𝓞 K), a ≠ 0 → I ^ p ^ k = Ideal.span {a} →
      (I.map (algebraMap (𝓞 K) (𝓞 K''))).IsPrincipal)

    (y : groupCohomology (Rep.ofMulDistribMulAction (K ≃ₐ[E] K) Kˣ) 2) (k : ℕ) (hy : (p ^ k : ℤ) • y = 0)
    (hsupp : ∀ w : HeightOneSpectrum (𝓞 K), (∀ v ∈ S, w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K)) ≠ v.asIdeal) →
      (groupCohomology.map (NumberField.PlaceDecomp.decomp E K w).subtype (prG w) 2).hom
        ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y) = 0) :
    ∃ (f : cocycles₂ (NumberField.SUnits.sUnitsRep E K'' S)) (k' : ℕ),
      (p ^ k' : ℤ) • (H2π _ f) = 0 ∧
      (groupCohomology.map (MonoidHom.id (K'' ≃ₐ[E] K'')) (NumberField.SUnits.toUnitsRep E K'' S) 2).hom (H2π _ f) =
        (groupCohomology.map (AlgEquiv.restrictNormalHom K : (K'' ≃ₐ[E] K'') →* (K ≃ₐ[E] K)) incl 2).hom y := by
  classical

  let G := K ≃ₐ[E] K
  let G'' := K'' ≃ₐ[E] K''
  let r : G'' →* G := AlgEquiv.restrictNormalHom K

  obtain ⟨Ψ, hΨinj, hΨrange, -⟩ :=
    NumberField.SIdele.exists_hom_obj_ideles_injective_of_ideleGaloisDescent E K S D hactI
  have hex := NumberField.SIdele.existsUnique_map_eq_of_forall_map_prG_eq_zero E K S D hactI Ψ hΨinj hΨrange
    prG hprG ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y)
  obtain ⟨z, hz, hzu⟩ := hex (fun w hw => hsupp w hw)
  have hzk : (p ^ k : ℤ) • z = 0 := by
    have h1 : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) Ψ 2).hom (z + (p ^ k : ℤ) • z) =
        (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) j 2).hom y := by
      rw [map_add, map_zsmul, hz, ← map_zsmul, hy, map_zero, add_zero]
    have := hzu (z + (p ^ k : ℤ) • z) h1
    rwa [add_eq_left] at this

  obtain ⟨jM, hjM⟩ := SLCAssembly.exists_codRestrict E K S D hactI j (SLCAssembly.j_mem_Msub E K S j hj)
  obtain ⟨ΨM, hΨM⟩ := SLCAssembly.exists_codRestrict E K S D hactI Ψ
    (fun t => Subgroup.mem_sup_right ((hΨrange (Additive.toMul (α := (AdeleRing (𝓞 K) K)ˣ) (Ψ.hom t))).1 ⟨t, rfl⟩))
  obtain ⟨u, hu_def⟩ : ∃ u : groupCohomology (SLCAssembly.M E K S D hactI) 2,
      u = (groupCohomology.map (MonoidHom.id G) jM 2).hom y - (groupCohomology.map (MonoidHom.id G) ΨM 2).hom z := ⟨_, rfl⟩
  have hdie : (groupCohomology.map (MonoidHom.id G) (SLCAssembly.ι E K S D hactI) 2).hom u = 0 := by
    rw [hu_def, map_sub, ← SLCAssembly.map_id_comp_apply, ← SLCAssembly.map_id_comp_apply, hjM, hΨM, hz, sub_self]
  have huk : (p ^ k : ℤ) • u = 0 := by
    rw [hu_def, zsmul_sub, ← map_zsmul, ← map_zsmul, hy, hzk, map_zero, map_zero, sub_self]

  let D'' : IdeleGaloisDescent (𝓞 K'') E K'' := genuineDescentDatum E K''
  letI : MulDistribMulAction (K'' ≃ₐ[E] K'') (AdeleRing (𝓞 K'') K'')ˣ := MulDistribMulAction.compHom _ D''.unitsAct
  have hactI'' : ∀ (g : K'' ≃ₐ[E] K'') (x : (AdeleRing (𝓞 K'') K'')ˣ), g • x = D''.unitsAct g x := fun _ _ => rfl

  let Jl : Additive (AdeleRing (𝓞 K) K)ˣ →ₗ[ℤ] Additive (AdeleRing (𝓞 K'') K'')ˣ :=
    (MonoidHom.toAdditive (Units.map (genuineBaseChange K K'').β.toMonoidHom)).toIntLinearMap
  have hJl : ∀ x, Jl x = Additive.ofMul (Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul x)) := fun _ => rfl
  let J : Rep.res r (SLCAssembly.I E K) ⟶ SLCAssembly.I E K'' := Rep.ofHom ⟨Jl, fun g => LinearMap.ext fun x => by
    show Jl ((SLCAssembly.I E K).ρ (r g) x) = (SLCAssembly.I E K'').ρ g (Jl x)
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, hJl, hJl, hactI, hactI'']
    change Additive.ofMul (Units.map (genuineBaseChange K K'').β.toMonoidHom (D.unitsAct (r g) (Additive.toMul x))) =
      Additive.ofMul (D''.unitsAct g (Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul x)))
    congr 1
    exact (M4aHerbrand.IdeleGaloisDescent.unitsAct_map_genuineBaseChange E K K'' D D'' g _).symm⟩
  have hJ : ∀ x, J.hom x = Additive.ofMul (Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul x)) := fun _ => rfl

  have hβM : ∀ w : (AdeleRing (𝓞 K) K)ˣ, w ∈ SLCAssembly.Msub E K S →
      Units.map (genuineBaseChange K K'').β.toMonoidHom w ∈ SLCAssembly.Msub E K'' S := by
    intro w hw
    obtain ⟨a, ha, v, hv, rfl⟩ := Subgroup.mem_sup.1 hw
    rw [map_mul]
    obtain ⟨a, rfl⟩ := ha
    exact Subgroup.mul_mem_sup ⟨Units.map (algebraMap K K'' : K →* K'') a, Units.ext ((genuineBaseChange K K'').β_compat (a : K)).symm⟩
      ((NumberField.AdeleRing.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower E K K'' S).1 v hv)
  obtain ⟨B, hB'⟩ := SLCAssembly.exists_lift_of_injective
    ((Rep.resFunctor r).map (SLCAssembly.ι E K S D hactI) ≫ J) (SLCAssembly.ι E K'' S D'' hactI'')
    (SLCAssembly.ι_injective E K'' S D'' hactI'')
    (fun m => ⟨⟨J.hom ((SLCAssembly.ι E K S D hactI).hom m), hβM _ m.2⟩, rfl⟩)
  have hB : ∀ m, Additive.toMul ((SLCAssembly.ι E K'' S D'' hactI'').hom (B.hom m)) =
      Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul ((SLCAssembly.ι E K S D hactI).hom m)) := by
    intro m
    have := congrArg (fun φ => Additive.toMul (φ.hom m)) hB'
    exact this

  have hkill := NumberField.IdeleLocalInv.map_eq_zero_of_zsmul_eq_zero_of_map_eq_zero_of_capitulation E K K'' S D hactI D'' hactI''
    (SLCAssembly.M E K S D hactI) (SLCAssembly.ι E K S D hactI) (SLCAssembly.ι_injective E K S D hactI) (SLCAssembly.ι_range E K S D hactI)
    (SLCAssembly.M E K'' S D'' hactI'') (SLCAssembly.ι E K'' S D'' hactI'') (SLCAssembly.ι_injective E K'' S D'' hactI'') (SLCAssembly.ι_range E K'' S D'' hactI'')
    B hB p hcap u k huk hdie

  let jl'' : Additive K''ˣ →ₗ[ℤ] Additive (AdeleRing (𝓞 K'') K'')ˣ :=
    (MonoidHom.toAdditive (Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K''))).toIntLinearMap
  have hjl'' : ∀ x, jl'' x = Additive.ofMul (Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') (Additive.toMul x)) :=
    fun _ => rfl
  let j'' : SLCAssembly.F E K'' ⟶ SLCAssembly.I E K'' := Rep.ofHom ⟨jl'', fun g => LinearMap.ext fun x => by
    show jl'' ((SLCAssembly.F E K'').ρ g x) = (SLCAssembly.I E K'').ρ g (jl'' x)
    rw [Rep.ofMulDistribMulAction_ρ_apply_apply, Rep.ofMulDistribMulAction_ρ_apply_apply, hjl'', hjl'', hactI'']
    congr 1
    apply Units.ext
    change algebraMap K'' (AdeleRing (𝓞 K'') K'') (((g • Additive.toMul x : K''ˣ) : K'')) =
      D''.act g (algebraMap K'' (AdeleRing (𝓞 K'') K'') ((Additive.toMul x : K''ˣ) : K''))
    rw [D''.compat]
    rfl⟩
  have hj'' : ∀ a : K''ˣ, j''.hom (Additive.ofMul a) =
      Additive.ofMul (Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') a) := fun _ => rfl
  obtain ⟨jM'', hjM''⟩ := SLCAssembly.exists_codRestrict E K'' S D'' hactI'' j'' (SLCAssembly.j_mem_Msub E K'' S j'' hj'')
  have hsq : ∀ x : SLCAssembly.F E K, B.hom (jM.hom x) = jM''.hom (incl.hom x) := by
    intro x
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective x
    apply SLCAssembly.ι_injective E K'' S D'' hactI''
    apply (Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ)).injective
    erw [hB]
    have h1 : (SLCAssembly.ι E K S D hactI).hom (jM.hom (Additive.ofMul a)) = j.hom (Additive.ofMul a) := by
      rw [← hjM]; rfl
    have h2 : (SLCAssembly.ι E K'' S D'' hactI'').hom (jM''.hom (incl.hom (Additive.ofMul a))) = j''.hom (incl.hom (Additive.ofMul a)) := by
      rw [← hjM'']; rfl
    rw [h1, h2, hj, hincl]
    change Units.map (genuineBaseChange K K'').β.toMonoidHom (Units.map (algebraMap K (AdeleRing (𝓞 K) K) : K →* AdeleRing (𝓞 K) K) a) =
      Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') (Units.map (algebraMap K K'' : K →* K'') a)
    apply Units.ext
    exact (genuineBaseChange K K'').β_compat _
  have hsq' : (Rep.resFunctor r).map jM ≫ B = incl ≫ jM'' :=
    Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun x => hsq x))

  have hkey : (groupCohomology.map (MonoidHom.id G'') jM'' 2).hom ((groupCohomology.map r incl 2).hom y) =
      (groupCohomology.map r ((Rep.resFunctor r).map ΨM ≫ B) 2).hom z := by
    have h1 := hkill
    rw [hu_def, map_sub, sub_eq_zero, ← SLCAssembly.map_res_comp_apply, ← SLCAssembly.map_res_comp_apply, hsq',
      SLCAssembly.map_comp_id_apply] at h1
    exact h1

  have hmemU : ∀ t : (Rep.resFunctor r).obj (NumberField.SIdele.obj E K S),
      Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) (B.hom (ΨM.hom t)).1 ∈ SLCAssembly.Usub E K'' S := by
    intro t
    have h1 : Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) (B.hom (ΨM.hom t)).1 =
        Units.map (genuineBaseChange K K'').β.toMonoidHom (Additive.toMul (α := (AdeleRing (𝓞 K) K)ˣ) (Ψ.hom t)) := by
      erw [← SLCAssembly.ι_hom_apply, hB]
      congr 2
      show (ΨM ≫ SLCAssembly.ι E K S D hactI).hom t = Ψ.hom t
      rw [hΨM]
    rw [h1]
    exact (NumberField.AdeleRing.unitsMap_genuineBaseChange_mem_unitIdelesOutside_of_isScalarTower E K K'' S).1 _
      ((hΨrange _).1 ⟨t, rfl⟩)
  obtain ⟨θ, hθ⟩ := SLCAssembly.exists_lift_of_injective ((Rep.resFunctor r).map ΨM ≫ B) (SLCAssembly.iU E K'' S D'' hactI'')
    (fun a b h => Subtype.ext h) (fun t => ⟨⟨B.hom (ΨM.hom t), hmemU t⟩, rfl⟩)
  have hvan : ((Rep.resFunctor r).map ΨM ≫ B) ≫ SLCAssembly.qM E K'' S D'' hactI'' = 0 := by
    rw [← hθ, Category.assoc, show SLCAssembly.iU E K'' S D'' hactI'' ≫ SLCAssembly.qM E K'' S D'' hactI'' = 0 from
      (GroupCohomology.RepCokernel.seq (SLCAssembly.iU E K'' S D'' hactI'')).zero, Limits.comp_zero]
  have hq0 : (groupCohomology.map (MonoidHom.id G'') (jM'' ≫ SLCAssembly.qM E K'' S D'' hactI'') 2).hom
      ((groupCohomology.map r incl 2).hom y) = 0 := by
    rw [SLCAssembly.map_id_comp_apply, hkey, ← SLCAssembly.map_comp_id_apply, hvan, SLCAssembly.map_zero_apply]

  have hinj : Function.Injective (NumberField.SUnits.toUnitsRep E K'' S).hom := fun a b h => Subtype.ext h
  have hjM''1 : ∀ a : K''ˣ, Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) (jM''.hom (Additive.ofMul a)).1 =
      Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') a := by
    intro a
    rw [← SLCAssembly.ι_hom_apply]
    change Additive.toMul ((jM'' ≫ SLCAssembly.ι E K'' S D'' hactI'').hom (Additive.ofMul a)) = _
    rw [hjM'', hj'']
    rfl
  have hUiff : ∀ a : K''ˣ, Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') a ∈ SLCAssembly.Usub E K'' S ↔
      a ∈ NumberField.SUnits.sUnits E K'' S := by
    intro a
    have hPU := NumberField.AdeleRing.principalIdeles_inf_unitIdelesOutside_eq_map_unit (𝓞 K'') K'' {w | w.under (𝓞 E) ∈ S}
    rw [NumberField.SUnits.sUnits_eq_unit]
    change _ ↔ a ∈ Set.unit {w : HeightOneSpectrum (𝓞 K'') | w.under (𝓞 E) ∈ S} K''
    constructor
    · intro hU
      have hPU' : Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') a ∈
          principalIdeles (𝓞 K'') K'' ⊓ SLCAssembly.Usub E K'' S := ⟨⟨a, rfl⟩, hU⟩
      rw [hPU] at hPU'
      obtain ⟨b, hb, hba⟩ := hPU'
      have : b = a := by
        apply Units.ext
        apply NumberField.AdeleRing.algebraMap_injective (𝓞 K'') K''
        exact congrArg (fun u : (AdeleRing (𝓞 K'') K'')ˣ => (u : AdeleRing (𝓞 K'') K'')) hba
      rw [← this]; exact hb
    · intro ha
      have : Units.map (algebraMap K'' (AdeleRing (𝓞 K'') K'') : K'' →* AdeleRing (𝓞 K'') K'') a ∈
          principalIdeles (𝓞 K'') K'' ⊓ SLCAssembly.Usub E K'' S := by
        rw [hPU]; exact ⟨a, ha, rfl⟩
      exact this.2
  have hexact : ∀ a : SLCAssembly.F E K'', (jM'' ≫ SLCAssembly.qM E K'' S D'' hactI'').hom a = 0 ↔
      a ∈ Set.range (NumberField.SUnits.toUnitsRep E K'' S).hom := by
    intro a
    obtain ⟨a, rfl⟩ := Additive.ofMul.surjective a
    change (SLCAssembly.qM E K'' S D'' hactI'').hom (jM''.hom (Additive.ofMul a)) = 0 ↔ _
    rw [SLCAssembly.qM_apply_eq_zero_iff]
    erw [hjM''1, hUiff]
    constructor
    · intro h; exact ⟨⟨Additive.ofMul a, h⟩, rfl⟩
    · rintro ⟨s, hs⟩
      have hs' : Additive.ofMul a = s.1 := hs.symm
      change Additive.toMul (Additive.ofMul a) ∈ NumberField.SUnits.sUnits E K'' S
      rw [hs']
      exact s.2
  have hsurj : Function.Surjective (jM'' ≫ SLCAssembly.qM E K'' S D'' hactI'').hom := by
    intro q
    obtain ⟨m, rfl⟩ := GroupCohomology.RepCokernel.π_hom_surjective (SLCAssembly.iU E K'' S D'' hactI'') q
    have hm : Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) m.1 ∈ SLCAssembly.Msub E K'' S := m.2
    obtain ⟨_, ⟨a, rfl⟩, v, hv, hav⟩ := Subgroup.mem_sup.1 hm
    refine ⟨Additive.ofMul a, ?_⟩
    change (SLCAssembly.qM E K'' S D'' hactI'').hom (jM''.hom (Additive.ofMul a)) = (SLCAssembly.qM E K'' S D'' hactI'').hom m
    rw [← sub_eq_zero, ← map_sub, SLCAssembly.qM_apply_eq_zero_iff]
    have hval : Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) (jM''.hom (Additive.ofMul a) - m).1 = v⁻¹ := by
      have e1 : Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) (jM''.hom (Additive.ofMul a) - m).1 =
          Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) (jM''.hom (Additive.ofMul a)).1 / Additive.toMul (α := (AdeleRing (𝓞 K'') K'')ˣ) m.1 := rfl
      rw [e1, hjM''1, ← hav]
      exact div_mul_cancel_left _ _
    erw [hval]
    exact inv_mem hv
  obtain ⟨f0, hf0⟩ := groupCohomology.exists_map_eq_of_map_eq_zero_of_injective_of_surjective
    (NumberField.SUnits.toUnitsRep E K'' S) (jM'' ≫ SLCAssembly.qM E K'' S D'' hactI'') hinj hsurj hexact 2
    ((groupCohomology.map r incl 2).hom y) hq0

  have hy'' : (p ^ k : ℤ) • (groupCohomology.map r incl 2).hom y = 0 := by rw [← map_zsmul, hy, map_zero]
  obtain ⟨f1, k', hk', hf1⟩ := SLCAssembly.exists_ppow_zsmul_eq_zero_and_map_eq (NumberField.SUnits.toUnitsRep E K'' S) p
    ((groupCohomology.map r incl 2).hom y) k hy'' f0 hf0
  obtain ⟨f, rfl⟩ := SLCAssembly.exists_H2π_eq _ f1
  exact ⟨f, k', hk', hf1⟩

end S_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation
end P2MW
export P2MW.S_NumberField_IdeleLocalInv_exists_cocyclesTwo_sUnitsRep_map_toUnitsRep_eq_of_capitulation (solution)
