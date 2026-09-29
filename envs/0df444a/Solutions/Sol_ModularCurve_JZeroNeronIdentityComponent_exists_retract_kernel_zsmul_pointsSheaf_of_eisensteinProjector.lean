-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/6b6c2314-18e1-5666-85da-3f3f44733482

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq
import Theorems.Thm_Module_bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_isReduced_schemeKer_pow
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector.ModularCurve"

universe v u w

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronIdentityComponent eisensteinPrimaryTorsionBar jZeroTorsion heckeModuleBar heckeModuleBar_C_smul JZero HeckeAlg eisensteinMaximalIdeal JZeroNeronIdentityComponent.exists_notMem_forall_zsmul_eq_zero_imp_app_eq JZeroNeronIdentityComponent.isReduced_schemeKer_pow"
namespace BetaAsm
p2m_open "ModularCurve"

theorem exists_mul_smul_eq_self_of_bijective {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    [Finite M] (t : T) (hb : Function.Bijective (fun x : M => t • x)) :
    ∃ t' : T, ∀ x : M, (t * t') • x = x := by
  classical
  haveI : Finite (M → M) := Pi.finite
  have hpow_inj : ∀ i : ℕ, Function.Injective (fun x : M => (t ^ i) • x) := by
    intro i
    induction i with
    | zero => intro x y h; simpa using h
    | succ k ih =>
      intro x y h
      have h' : t • ((t ^ k) • x) = t • ((t ^ k) • y) := by
        simpa only [pow_succ', mul_smul] using h
      exact ih (hb.1 h')
  obtain ⟨a, b, hab, heq⟩ := Finite.exists_ne_map_eq_of_infinite (fun i : ℕ => fun x : M => (t ^ i) • x)

  rcases lt_or_gt_of_ne hab with hlt | hlt
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨t ^ d, fun x => ?_⟩
    apply hpow_inj a
    have hx := congrFun heq x
    beta_reduce at hx

    calc (t ^ a) • ((t * t ^ d) • x) = (t ^ (a + d + 1)) • x := by
          rw [← mul_smul]; congr 1; ring
      _ = (t ^ a) • x := hx.symm
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    refine ⟨t ^ d, fun x => ?_⟩
    apply hpow_inj b
    have hx := congrFun heq x
    beta_reduce at hx
    calc (t ^ b) • ((t * t ^ d) • x) = (t ^ (b + d + 1)) • x := by
          rw [← mul_smul]; congr 1; ring
      _ = (t ^ b) • x := hx

theorem exists_pow_smul_eq_zero {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (𝔓 : Ideal T) (S : Set M) (hS : S.Finite)
    (h : ∀ x ∈ S, ∃ k : ℕ, ∀ a ∈ 𝔓 ^ k, a • x = 0) :
    ∃ k : ℕ, ∀ x ∈ S, ∀ a ∈ 𝔓 ^ k, a • x = 0 := by
  classical
  choose! k hk using h
  refine ⟨hS.toFinset.sup k, fun x hx a ha => hk x hx a (Ideal.pow_le_pow_right ?_ ha)⟩
  exact Finset.le_sup (hS.mem_toFinset.mpr hx)

section km
variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] {R : Type} [CommRing R] {𝒢 : 𝒞} (n : ℤ) (ρ : R →+* End 𝒢)

theorem hw (t : R) : (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢) := by
  rw [Preadditive.zsmul_comp, Category.id_comp, Preadditive.comp_zsmul, Category.comp_id]

noncomputable abbrev km (t : R) : kernel (n • 𝟙 𝒢) ⟶ kernel (n • 𝟙 𝒢) :=
  kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) (hw n ρ t)

theorem kmι (t : R) : km n ρ t ≫ kernel.ι (n • 𝟙 𝒢) = kernel.ι (n • 𝟙 𝒢) ≫ ρ t := kernel.lift_ι _ _ _

theorem km_mul (a b : R) : km n ρ (a * b) = km n ρ b ≫ km n ρ a := by
  apply (cancel_mono (kernel.ι (n • 𝟙 𝒢))).mp
  rw [kmι, Category.assoc, kmι, ← Category.assoc, kmι, Category.assoc, map_mul, End.mul_def]

theorem km_comm (a b : R) : km n ρ a ≫ km n ρ b = km n ρ b ≫ km n ρ a := by
  rw [← km_mul, ← km_mul, mul_comm]

theorem km_one : km n ρ 1 = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (n • 𝟙 𝒢))).mp
  rw [kmι, map_one, End.one_def, Category.id_comp, Category.comp_id]

theorem km_add (a b : R) : km n ρ (a + b) = km n ρ a + km n ρ b := by
  apply (cancel_mono (kernel.ι (n • 𝟙 𝒢))).mp
  rw [kmι, Preadditive.add_comp, kmι, kmι, map_add]
  exact Preadditive.comp_add _ _ _ _ _ _

theorem km_sub (a b : R) : km n ρ (a - b) = km n ρ a - km n ρ b := by
  rw [eq_sub_iff_add_eq, ← km_add, sub_add_cancel]

theorem kernel_map_eq_km (t : R) (w : (n • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (n • 𝟙 𝒢)) :
    kernel.map (n • 𝟙 𝒢) (n • 𝟙 𝒢) (ρ t) (ρ t) w = km n ρ t := rfl

end km

section secs
variable {ℱ 𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1}}

theorem zsmul_app (f : ℱ ⟶ 𝒢) (n : ℤ) (U : specInt.Fppf) (y : ℱ.1.obj (op U)) :
    (n • f).1.app (op U) y = n • (f.1.app (op U) y) := by
  have h : (n • f).1 = n • f.1 := rfl
  rw [h]; simp

theorem comp_app (f : ℱ ⟶ 𝒢) {ℋ : Sheaf (smallFppfTopology specInt) Ab.{1}} (k : 𝒢 ⟶ ℋ) (U : specInt.Fppf)
    (y : ℱ.1.obj (op U)) : (f ≫ k).1.app (op U) y = k.1.app (op U) (f.1.app (op U) y) := by
  simp

theorem hom_ext_app {f g : ℱ ⟶ 𝒢} (hfg : ∀ (U : specInt.Fppf) (y : ℱ.1.obj (op U)), f.1.app (op U) y = g.1.app (op U) y) :
    f = g := by
  apply Sheaf.hom_ext
  ext U y
  exact hfg U.unop y

theorem app_injective_of_mono (k : ℱ ⟶ 𝒢) [Mono k] (U : specInt.Fppf) : Function.Injective (k.1.app (op U)) := by
  have : Mono (k.1.app (op U)) := (NatTrans.mono_iff_mono_app k.1).mp inferInstance (op U)
  exact (AddCommGrpCat.mono_iff_injective _).mp this

theorem zsmul_kernel_ι_app (n : ℤ) (U : specInt.Fppf) (x : (kernel (n • 𝟙 𝒢)).1.obj (op U)) :
    n • ((kernel.ι (n • 𝟙 𝒢)).1.app (op U) x) = 0 := by
  have h := congrArg (fun φ => φ.1.app (op U) x) (kernel.condition (n • 𝟙 𝒢))
  simp only at h
  rw [comp_app, zsmul_app] at h
  simpa using h

end secs

theorem comp_eq_of_comp_eq {X Y E G S : Scheme.{0}} (A : X ⟶ Y) (B : Y ⟶ E) (i : E ⟶ G) (φ : G ⟶ G)
    (g : E ⟶ S) (u : S ⟶ G) (t : X ⟶ S) (h1 : i ≫ φ = g ≫ u) (h2 : (A ≫ B) ≫ g = t) :
    (A ≫ B ≫ i) ≫ φ = t ≫ u := by
  subst h2
  simp only [Category.assoc, h1]

section pts
variable {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)

theorem one_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℤ)) :
    (N.L.one t).1 = t ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
  have h := N.L.one_natural (𝟙 (Spec (CommRingCat.of ℤ))) t t (Category.comp_id t)
  rw [← h]; rfl

noncomputable abbrev qbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

theorem pts_zero : N.pts 0 = N.L.one (qbar) := by
  letI : Group (SchemeHomOver qbar N.g) := N.L.pointGroup qbar
  have h := N.pts_add 0 0
  rw [add_zero] at h
  have h2 : (N.pts 0 : SchemeHomOver qbar N.g) * (N.pts 0) = N.pts 0 := h.symm
  exact mul_eq_left.mp h2

variable (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
  (e𝒢 : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
  (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e𝒢 U (s + s') = N.L.mul U.hom (e𝒢 U s) (e𝒢 U s'))

include he_add in
theorem e_zero (U : specInt.Fppf) : e𝒢 U 0 = N.L.one U.hom := by
  letI : Group (SchemeHomOver U.hom N.g) := N.L.pointGroup U.hom
  have h := he_add U 0 0
  rw [add_zero] at h
  have h2 : (e𝒢 U 0 : SchemeHomOver U.hom N.g) * (e𝒢 U 0) = e𝒢 U 0 := h.symm
  exact mul_eq_left.mp h2

end pts

section lemmaA
variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]

theorem isMaximal_eisensteinMaximalIdeal : (eisensteinMaximalIdeal p q).IsMaximal := by
  unfold eisensteinMaximalIdeal
  haveI : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible ((Nat.prime_iff_prime_int.mp Fact.out).irreducible)
  exact Ideal.comap_isMaximal_of_surjective _ (fun z => ⟨MvPolynomial.C z, by simp⟩)

theorem exists_forall_mem_sub_one_smul_eq_zero (m : ℕ) (hfin : Finite ↥(jZeroTorsion p (q ^ m)))
    (t : HeckeAlg) (ht𝔓 : t ∉ eisensteinMaximalIdeal p q) :
    letI := heckeModuleBar p
    ∃ t' : HeckeAlg, ∀ v : JZero p, v ∈ eisensteinPrimaryTorsionBar p q m → (t * t' - 1) • v = 0 := by
  letI := heckeModuleBar p
  let Vs : Submodule HeckeAlg (JZero p) :=
    Submodule.torsionBy HeckeAlg (JZero p) (MvPolynomial.C ((q : ℤ) ^ m)) ⊓
      ⨆ k : ℕ, Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)
  have hVs_tors : ∀ x ∈ Vs, ((q : ℤ) ^ m) • x = 0 := by
    intro x hx
    have h1 := (Submodule.mem_inf.mp hx).1
    rw [Submodule.mem_torsionBy_iff, heckeModuleBar_C_smul] at h1
    exact h1
  have hdirS : Directed (· ≤ ·) (fun k : ℕ =>
      Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)) := by
    apply Monotone.directed_le
    intro k l hkl y hy
    rw [Submodule.mem_torsionBySet_iff] at hy ⊢
    rintro ⟨b, hb⟩
    exact hy ⟨b, Ideal.pow_le_pow_right hkl hb⟩
  have hdirA : Directed (· ≤ ·) (fun k : ℕ =>
      (Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup) :=
    hdirS.mono_comp _ (fun _ _ h => Submodule.toAddSubgroup_mono h)
  have hVmem : ∀ x : JZero p, x ∈ eisensteinPrimaryTorsionBar p q m ↔ x ∈ Vs := by
    intro x
    change x ∈ (AddMonoidHom.ker (((q ^ m : ℕ) : ℤ) • AddMonoidHom.id (JZero p))) ⊓ ⨆ k : ℕ,
      (Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup ↔ _
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_iSup_of_directed hdirA, AddMonoidHom.mem_ker, Submodule.mem_inf,
      Submodule.mem_iSup_of_directed _ hdirS, Submodule.mem_torsionBy_iff, heckeModuleBar_C_smul]
    push_cast
    exact Iff.rfl
  haveI : Finite ↥Vs := by
    haveI := hfin
    refine Finite.of_injective (fun x : ↥Vs => (⟨x.1, ?_⟩ : ↥(jZeroTorsion p (q ^ m)))) (fun a b h => ?_)
    · change x.1 ∈ Submodule.torsionBy ℤ (JZero p) ((q ^ m : ℕ) : ℤ)
      rw [Submodule.mem_torsionBy_iff]; push_cast; exact hVs_tors x.1 x.2
    · have h' := Subtype.ext_iff.mp h
      exact Subtype.ext h'
  have hprim : ∀ x : ↥Vs, ∃ k : ℕ, ∀ b ∈ (eisensteinMaximalIdeal p q) ^ k, b • x = 0 := by
    intro x
    obtain ⟨k, hk⟩ := (Submodule.mem_iSup_of_directed _ hdirS).mp (Submodule.mem_inf.mp x.2).2
    refine ⟨k, fun b hb => Subtype.ext ?_⟩
    rw [Submodule.mem_torsionBySet_iff] at hk
    exact hk ⟨b, hb⟩
  obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero (eisensteinMaximalIdeal p q) (Set.univ : Set ↥Vs)
    Set.finite_univ (fun x _ => hprim x)
  have hbij := Module.bijective_smul_of_notMem_of_isMaximal_of_pow_smul_eq_bot (M := ↥Vs)
    (eisensteinMaximalIdeal p q) (isMaximal_eisensteinMaximalIdeal p q) k (fun b hb x => hk x (Set.mem_univ x) b hb) t ht𝔓
  obtain ⟨t', ht'⟩ := exists_mul_smul_eq_self_of_bijective (M := ↥Vs) t hbij
  refine ⟨t', fun v hv => ?_⟩
  have := congrArg Subtype.val (ht' ⟨v, (hVmem v).mp hv⟩)
  simp only [SetLike.val_smul] at this
  rw [sub_smul, one_smul, sub_eq_zero]
  exact this

end lemmaA

section lemmaB
variable {p : ℕ} [Fact p.Prime] (q : ℕ) [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)

set_option maxHeartbeats 1600000 in
theorem comp_eq_unit_of_forall_smul_eq_zero
    [Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)] [LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)]
    (eK : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) (heK_idem : eK.1 ≫ eK.1 = eK.1)
    (E : Scheme.{0}) (gX : E ⟶ Spec (CommRingCat.of ℤ)) (i : E ⟶ N.G) (j : E ⟶ N.L.schemeKer (q ^ m))
    (hi : i ≫ N.g = gX) (hj : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i)
    (hfix : ∀ (hj' : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = gX) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      NeronModelInfra.schemeHomOverComp x eK = x ↔
        ∃ y : SchemeHomOver s gX, NeronModelInfra.schemeHomOverComp y (⟨j, hj'⟩ : SchemeHomOver gX (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) = x)
    (hpts : ∀ x : JZero p, x ∈ eisensteinPrimaryTorsionBar p q m ↔
      ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) gX, y.1 ≫ i = (N.pts x).1)
    (a : HeckeAlg) (φa : SchemeHomOver N.g N.g)
    (hpa : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (a • x)).1 = (N.pts x).1 ≫ φa.1)
    (ha : letI := heckeModuleBar p; ∀ v : JZero p, v ∈ eisensteinPrimaryTorsionBar p q m → a • v = 0) :
    i ≫ φa.1 = gX ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
  letI := heckeModuleBar p
  have hj' : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = gX := by rw [← Category.assoc, hj, hi]

  have hjfix : j ≫ eK.1 = j := by
    have h := (hfix hj' gX (NeronModelInfra.schemeHomOverComp
      (⟨𝟙 E, Category.id_comp _⟩ : SchemeHomOver gX gX) ⟨j, hj'⟩)).mpr ⟨⟨𝟙 E, Category.id_comp _⟩, rfl⟩
    have h2 := congrArg Subtype.val h
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.id_comp] at h2
    exact h2

  let υ : SchemeHomOver N.g N.g := ⟨N.g ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, by
    rw [Category.assoc, (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).2, Category.comp_id]⟩

  haveI : IsReduced (N.L.schemeKer (q ^ m)) := ModularCurve.JZeroNeronIdentityComponent.isReduced_schemeKer_pow p q N m
  haveI : IsSeparated N.g := N.separated
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := @AlgebraicClosure.instIsAlgClosure ℚ _
  let incl : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g := ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩
  have E1 := AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
    (R := ℤ) ℚ (AlgebraicClosure ℚ) (gY := pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (gX := N.g)
    (NeronModelInfra.schemeHomOverComp eK (NeronModelInfra.schemeHomOverComp incl φa))
    (NeronModelInfra.schemeHomOverComp eK (NeronModelInfra.schemeHomOverComp incl υ))
    (fun z => by
      have hzfix : NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z eK) eK =
          NeronModelInfra.schemeHomOverComp z eK := by
        apply Subtype.ext
        simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, heK_idem]
      obtain ⟨y, hy⟩ := (hfix hj' _ _).mp hzfix
      have hy1 : y.1 ≫ j = z.1 ≫ eK.1 := by
        have := congrArg Subtype.val hy
        simpa only [NeronModelInfra.schemeHomOverComp_coe] using this
      have hyG : (y.1 ≫ i) ≫ N.g = qbar := by rw [Category.assoc, hi]; exact y.2
      obtain ⟨v, hv⟩ : ∃ v : JZero p, (N.pts v).1 = y.1 ≫ i :=
        ⟨N.pts.symm ⟨y.1 ≫ i, hyG⟩, by rw [Equiv.apply_symm_apply]⟩
      have hvmem : v ∈ eisensteinPrimaryTorsionBar p q m := (hpts v).mpr ⟨y, hv.symm⟩
      have hav : a • v = 0 := ha v hvmem

      have lhs : z.1 ≫ eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φa.1 = qbar ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
        rw [← Category.assoc z.1, ← hy1, Category.assoc, ← Category.assoc j, hj, ← Category.assoc y.1, ← hv,
          ← hpa, hav, pts_zero, one_coe]
      have rhs : z.1 ≫ eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 =
          qbar ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
        rw [← Category.assoc z.1, ← hy1, Category.assoc, ← Category.assoc j, hj, ← Category.assoc y.1, ← hv,
          ← Category.assoc, (N.pts v).2]
      change z.1 ≫ eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φa.1 = z.1 ≫ eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1
      rw [lhs, rhs])
  have E1' : eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φa.1 = eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
    have := congrArg Subtype.val E1
    simpa only [NeronModelInfra.schemeHomOverComp_coe] using this
  calc i ≫ φa.1 = (j ≫ eK.1) ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φa.1 := by rw [hjfix, ← Category.assoc, hj]
    _ = j ≫ (eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φa.1) := by simp only [Category.assoc]
    _ = j ≫ (eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) := by rw [E1']
    _ = ((j ≫ eK.1) ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by simp only [Category.assoc]
    _ = gX ≫ (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by rw [hjfix, hj']

end lemmaB

section lemmaD
variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞] {R : Type} [CommRing R] {𝒢 : 𝒞} (n : ℤ) (ρ : R →+* End 𝒢)

theorem isIso_of_retract {𝒥 : 𝒞} (ι : 𝒥 ⟶ kernel (n • 𝟙 𝒢)) (π : kernel (n • 𝟙 𝒢) ⟶ 𝒥) (tm t t' a : R)
    (hιπ : ι ≫ π = 𝟙 𝒥) (hπι : π ≫ ι = km n ρ tm) (ha : t * t' - 1 = a) (kill : ι ≫ km n ρ a = 0) :
    IsIso (ι ≫ km n ρ t ≫ π) := by
  have hιtm : ι ≫ km n ρ tm = ι := by
    rw [← hπι, ← Category.assoc, hιπ, Category.id_comp]
  have hmul : km n ρ t ≫ km n ρ t' = 𝟙 _ + km n ρ a := by
    rw [← km_mul, mul_comm, ← ha, ← km_one n ρ, ← km_add, add_sub_cancel]
  have hmul' : km n ρ t' ≫ km n ρ t = 𝟙 _ + km n ρ a := by
    rw [km_comm, hmul]
  have key : ∀ u u' : R, km n ρ u ≫ km n ρ u' = 𝟙 _ + km n ρ a →
      (ι ≫ km n ρ u ≫ π) ≫ (ι ≫ km n ρ u' ≫ π) = 𝟙 _ := by
    intro u u' huu
    calc (ι ≫ km n ρ u ≫ π) ≫ (ι ≫ km n ρ u' ≫ π)
        = ι ≫ km n ρ u ≫ (π ≫ ι) ≫ km n ρ u' ≫ π := by simp only [Category.assoc]
      _ = ι ≫ (km n ρ tm ≫ km n ρ u) ≫ km n ρ u' ≫ π := by rw [hπι, km_comm]; simp only [Category.assoc]
      _ = (ι ≫ km n ρ tm) ≫ (km n ρ u ≫ km n ρ u') ≫ π := by simp only [Category.assoc]
      _ = ι ≫ (𝟙 _ + km n ρ a) ≫ π := by rw [hιtm, huu]
      _ = 𝟙 _ := by
          rw [Preadditive.add_comp, Preadditive.comp_add, Category.id_comp, hιπ, ← Category.assoc, kill, zero_comp,
            add_zero]
  exact ⟨⟨ι ≫ km n ρ t' ≫ π, key t t' hmul, key t' t hmul'⟩⟩

end lemmaD

end ModularCurve.BetaAsm

theorem solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : JZeroNeronIdentityComponent p)

    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e𝒢 : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e𝒢 U (s + s') = N.L.mul U.hom (e𝒢 U s) (e𝒢 U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e𝒢 U (𝒢.1.map k.op s) = GoodReductionJacobian.schemeHomOverComp k.left (MorphismProperty.Over.w k) (e𝒢 V s))
    (ρ : letI := heckeModuleBar p; HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ t).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φ.1)
    (m : ℕ) (hfin : Finite ↥(jZeroTorsion p (q ^ m)))

    (tm : letI := heckeModuleBar p; HeckeAlg) (φt : SchemeHomOver N.g N.g)
    (eK : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → (tm • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : eK.1 ≫ eK.1 = eK.1)
    (hφt_pts : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (tm • x)).1 = (N.pts x).1 ≫ φt.1)
    (hφt_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ tm).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φt.1)
    (heφ : eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1)
    (heK_hom : ∀ (LK : RelativeGroupLaw ℤ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      (∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g) =
          N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩) (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
      ∀ {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
        NeronModelInfra.schemeHomOverComp (LK.mul s x y) eK =
          LK.mul s (NeronModelInfra.schemeHomOverComp x eK) (NeronModelInfra.schemeHomOverComp y eK))

    (E : Scheme.{0}) (gX : E ⟶ (Spec (CommRingCat.of ℤ))) (i : E ⟶ N.G) (j : E ⟶ N.L.schemeKer (q ^ m))
    (LE : RelativeGroupLaw ℤ gX)
    (hi : i ≫ N.g = gX) [IsClosedImmersion i] (hj : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = i) [IsClosedImmersion j]
    [IsAffineHom gX] [Flat gX] [LocallyOfFiniteType gX]
    (hfix : ∀ (hj' : j ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g = gX) {T : Scheme.{0}} (s : T ⟶ (Spec (CommRingCat.of ℤ))) (x : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
      NeronModelInfra.schemeHomOverComp x eK = x ↔
        ∃ y : SchemeHomOver s gX, NeronModelInfra.schemeHomOverComp y (⟨j, hj'⟩ : SchemeHomOver gX (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)) = x)
    (hcommE : ∀ {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX), LE.mul t x y = LE.mul t y x)
    (hi_hom : ∀ (hi' : i ≫ N.g = gX) {T : Scheme.{0}} (t : T ⟶ (Spec (CommRingCat.of ℤ))) (x y : SchemeHomOver t gX),
      NeronModelInfra.schemeHomOverComp (LE.mul t x y) (⟨i, hi'⟩ : SchemeHomOver gX N.g) =
        N.L.mul t (NeronModelInfra.schemeHomOverComp x ⟨i, hi'⟩) (NeronModelInfra.schemeHomOverComp y ⟨i, hi'⟩))
    (hpts : ∀ x : JZero p, x ∈ eisensteinPrimaryTorsionBar p q m ↔
      ∃ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) gX, y.1 ≫ i = (N.pts x).1)
    (H : Type) [CommRing H] [HopfAlgebra ℤ H] [Algebra.FiniteType ℤ H] [Module.Flat ℤ H]
    (hHff : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) H))
    (ePts : ∀ (T : Type) [CommRing T] [Algebra ℤ T],
      WithConv (H →ₐ[ℤ] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ T))) gX)
    (hePts_mul : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (φ ψ : WithConv (H →ₐ[ℤ] T)),
      ePts T (φ * ψ) = LE.mul _ (ePts T φ) (ePts T ψ))
    (hePts_nat : ∀ (T T' : Type) [CommRing T] [Algebra ℤ T] [CommRing T'] [Algebra ℤ T']
        (σ : T →ₐ[ℤ] T') (φ : WithConv (H →ₐ[ℤ] T)),
      (ePts T' (.toConv (σ.comp φ.ofConv))).1 = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ (ePts T φ).1)
    (𝒥 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (sE : ∀ U : specInt.Fppf, 𝒥.1.obj (op U) ≃+ Additive (WithConv (H →ₐ[ℤ] Γ(U.left, ⊤))))
    (hsE : ∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : 𝒥.1.obj (op V)) (h : H),
      (Additive.toMul (sE U (𝒥.1.map f.op s))) h = (Scheme.Γ.map f.left.op) ((Additive.toMul (sE V s)) h)) :
    letI := heckeModuleBar p
    ∃ (ι : 𝒥 ⟶ kernel (((q : ℤ) ^ m) • 𝟙 𝒢)) (π : kernel (((q : ℤ) ^ m) • 𝟙 𝒢) ⟶ 𝒥) (s : HeckeAlg),
      ι ≫ π = 𝟙 𝒥 ∧
      s ∉ eisensteinMaximalIdeal p q ∧
      (∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ s = ρ s ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
        kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ s) (ρ s) w = π ≫ ι) ∧
      (∀ t : HeckeAlg, ∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
        kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ t) (ρ t) w ≫ (π ≫ ι)
          = (π ≫ ι) ≫ kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ t) (ρ t) w) ∧
      (∀ t : HeckeAlg, t ∉ eisensteinMaximalIdeal p q →
        ∃ w : (((q : ℤ) ^ m) • 𝟙 𝒢) ≫ ρ t = ρ t ≫ (((q : ℤ) ^ m) • 𝟙 𝒢),
          IsIso (ι ≫ kernel.map (((q : ℤ) ^ m) • 𝟙 𝒢) (((q : ℤ) ^ m) • 𝟙 𝒢) (ρ t) (ρ t) w ≫ π)) ∧

      (∀ (U : specInt.Fppf) (x : 𝒥.1.obj (op U)),
        (e𝒢 U ((kernel.ι (((q : ℤ) ^ m) • 𝟙 𝒢)).1.app (op U) (ι.1.app (op U) x))).1 =
          U.left.toSpecΓ ≫ (ePts Γ(U.left, ⊤) (Additive.toMul (sE U x))).1 ≫ i) := by
  letI := heckeModuleBar p

  obtain ⟨-, hkeq, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
    N.L N.comm (q ^ m)
  have hq0 : 0 < q ^ m := pow_pos (Fact.out : q.Prime).pos m
  haveI : Flat (N.L.schemeNsmul (q ^ m)) := N.nsmul_flat _ hq0
  haveI : Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) := by
    rw [hkeq]; change Flat (pullback.snd _ _); infer_instance
  haveI : LocallyOfFiniteType N.g := N.locallyOfFiniteType
  haveI : LocallyOfFiniteType (N.L.schemeNsmul (q ^ m) ≫ N.g) := by rw [N.L.schemeNsmul_over]; infer_instance
  haveI : LocallyOfFiniteType (N.L.schemeNsmul (q ^ m)) := locallyOfFiniteType_of_comp _ N.g
  haveI : LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) := by
    rw [hkeq]; change LocallyOfFiniteType (pullback.snd _ _); infer_instance

  obtain ⟨s, hs𝔓, hρs⟩ :=
    ModularCurve.JZeroNeronIdentityComponent.exists_notMem_forall_zsmul_eq_zero_imp_app_eq
      p q N 𝒢 e𝒢 he_add he ρ hρ m hfin tm φt eK ht heK_idem hφt_pts hφt_sec heφ

  obtain ⟨ι, π, w, hιπ, hπι, hι_sec⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_retract_kernel_zsmul_hopfPointsSheaf_of_idempotent
      N.L (fun t x y => N.comm t x y) 𝒢 e𝒢 he_add he (q ^ m) ((q : ℤ) ^ m) (by push_cast; rfl)
      (ρ tm) φt hφt_sec eK heK_idem heφ heK_hom E gX i j LE hi hj hfix hcommE hi_hom H ePts hePts_mul hePts_nat 𝒥 sE hsE

  have hπι' : π ≫ ι = ModularCurve.BetaAsm.km ((q : ℤ) ^ m) ρ tm := hπι

  have hkms : ModularCurve.BetaAsm.km ((q : ℤ) ^ m) ρ s = ModularCurve.BetaAsm.km ((q : ℤ) ^ m) ρ tm := by
    apply (cancel_mono (kernel.ι (((q : ℤ) ^ m) • 𝟙 𝒢))).mp
    rw [ModularCurve.BetaAsm.kmι, ModularCurve.BetaAsm.kmι]
    apply ModularCurve.BetaAsm.hom_ext_app
    intro U x
    rw [ModularCurve.BetaAsm.comp_app, ModularCurve.BetaAsm.comp_app]
    exact hρs U _ (ModularCurve.BetaAsm.zsmul_kernel_ι_app ((q : ℤ) ^ m) U x)

  have hιtm : ι ≫ ModularCurve.BetaAsm.km ((q : ℤ) ^ m) ρ tm = ι := by
    rw [← hπι', ← Category.assoc, hιπ, Category.id_comp]
  refine ⟨ι, π, s, hιπ, hs𝔓, ⟨ModularCurve.BetaAsm.hw ((q : ℤ) ^ m) ρ s, by
    rw [ModularCurve.BetaAsm.kernel_map_eq_km, hkms, hπι']⟩, ?_, ?_, hι_sec⟩
  ·
    intro t
    refine ⟨ModularCurve.BetaAsm.hw ((q : ℤ) ^ m) ρ t, ?_⟩
    rw [ModularCurve.BetaAsm.kernel_map_eq_km, hπι', ModularCurve.BetaAsm.km_comm]
  ·
    intro t ht𝔓
    refine ⟨ModularCurve.BetaAsm.hw ((q : ℤ) ^ m) ρ t, ?_⟩
    rw [ModularCurve.BetaAsm.kernel_map_eq_km]
    obtain ⟨t', ht'⟩ := ModularCurve.BetaAsm.exists_forall_mem_sub_one_smul_eq_zero p q m hfin t ht𝔓
    obtain ⟨φa, hpa, hsa⟩ := hρ (t * t' - 1)
    have E3 := ModularCurve.BetaAsm.comp_eq_unit_of_forall_smul_eq_zero q N m eK heK_idem E gX i j hi hj hfix hpts
      (t * t' - 1) φa hpa ht'

    have kill : ι ≫ ModularCurve.BetaAsm.km ((q : ℤ) ^ m) ρ (t * t' - 1) = 0 := by
      apply ModularCurve.BetaAsm.hom_ext_app
      intro U x
      rw [ModularCurve.BetaAsm.comp_app]
      apply ModularCurve.BetaAsm.app_injective_of_mono (kernel.ι (((q : ℤ) ^ m) • 𝟙 𝒢)) U
      have hzero : (0 : 𝒥 ⟶ kernel (((q : ℤ) ^ m) • 𝟙 𝒢)).1.app (op U) x = 0 := by simp
      rw [hzero, map_zero, ← ModularCurve.BetaAsm.comp_app, ModularCurve.BetaAsm.kmι, ModularCurve.BetaAsm.comp_app]
      apply (e𝒢 U).injective
      apply Subtype.ext
      rw [hsa, hι_sec, ModularCurve.BetaAsm.e_zero N 𝒢 e𝒢 he_add, ModularCurve.BetaAsm.one_coe]
      exact ModularCurve.BetaAsm.comp_eq_of_comp_eq _ _ _ _ _ _ _ E3
        (Limits.IsTerminal.hom_ext AlgebraicGeometry.specZIsTerminal _ _)
    exact ModularCurve.BetaAsm.isIso_of_retract ((q : ℤ) ^ m) ρ ι π tm t t' (t * t' - 1) hιπ hπι' rfl kill

end S_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_retract_kernel_zsmul_pointsSheaf_of_eisensteinProjector (solution)
