-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.exists_notMem_forall_zsmul_eq_zero_imp_app_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/9859deb0-ee0e-5e4c-9548-46628aa1e391

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_Module_exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_isReduced_schemeKer_pow
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq.ModularCurve"

namespace Module p2m_export "Module" "Flat Finite.of_injective End exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp" end Module
p2m_open_scoped "Module" in

theorem Module.eq_zero_of_smul_eq_self_of_mem_of_pow_smul_eq_zero
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (𝔓 : Ideal T) (t : T) (ht : t ∈ 𝔓) (x : M) (hfix : t • x = x)
    (k : ℕ) (hk : ∀ a ∈ 𝔓 ^ k, a • x = 0) : x = 0 := by
  have hpow : ∀ j : ℕ, t ^ j • x = x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hfix, ih]
  rw [← hpow k]
  exact hk _ (Ideal.pow_mem_pow ht k)

p2m_open_scoped "Module" in

theorem Module.smul_eq_zero_of_smul_smul_eq_of_forall_smul_eq_self_imp
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (t : T) (x : M) (hidem : t • (t • x) = t • x) (hfix : ∀ y : M, t • y = y → y = 0) : t • x = 0 :=
  hfix _ hidem

p2m_open_scoped "Module" in

theorem Module.forall_eq_zero_of_mem_of_smul_eq_self_iff
    {T : Type*} [CommRing T] {M : Type*} [AddCommGroup M] [Module T M]
    (𝔓 : Ideal T) (t : T) (ht : t ∈ 𝔓) (V : Set M)
    (hV : ∀ x ∈ V, t • x = x ∧ ∃ k : ℕ, ∀ a ∈ 𝔓 ^ k, a • x = 0) : ∀ x ∈ V, x = 0 := by
  intro x hx
  obtain ⟨hfix, k, hk⟩ := hV x hx
  exact Module.eq_zero_of_smul_eq_self_of_mem_of_pow_smul_eq_zero 𝔓 t ht x hfix k hk

namespace ModularCurve p2m_export "ModularCurve" "JZeroNeronIdentityComponent eisensteinPrimaryTorsionBar jZeroTorsion heckeModuleBar heckeModuleBar_C_smul JZero HeckeAlg eisensteinEval eisensteinMaximalIdeal JZeroNeronIdentityComponent.isReduced_schemeKer_pow" namespace JZeroNeronIdentityComponent p2m_export "ModularCurve.JZeroNeronIdentityComponent" "G L comm separated pts pts_add g isReduced_schemeKer_pow" end ModularCurve.JZeroNeronIdentityComponent
p2m_open_scoped "ModularCurve ModularCurve.JZeroNeronIdentityComponent" in

theorem ModularCurve.JZeroNeronIdentityComponent.schemeHomOver_schemeKer_ext_of_forall_algebraicClosure_point
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : JZeroNeronIdentityComponent p) (m : ℕ)
    [Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)] [LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)]
    (φ ψ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g)
    (h : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g),
      z.1 ≫ φ.1 = z.1 ≫ ψ.1) :
    φ = ψ := by
  haveI : IsReduced (pullback (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) :=
    ModularCurve.JZeroNeronIdentityComponent.isReduced_schemeKer_pow p q N m
  haveI : IsSeparated N.g := N.separated
  exact @AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat ℤ _ _ ℚ _ _ _
    (AlgebraicClosure ℚ) _ (AlgebraicClosure.instAlgebra ℚ) (AlgebraicClosure.instIsAlgClosure ℚ) _ inferInstance
    _ _ _ _ _ _ _ _ φ ψ h

set_option maxHeartbeats 3200000 in

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
    [Flat (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)] [LocallyOfFiniteType (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)]
    (tm : letI := heckeModuleBar p; HeckeAlg) (φt : SchemeHomOver N.g N.g)
    (eK : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g))
    (ht : letI := heckeModuleBar p
      ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → (tm • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m))
    (heK_idem : eK.1 ≫ eK.1 = eK.1)
    (hφt_pts : letI := heckeModuleBar p; ∀ x : JZero p, (N.pts (tm • x)).1 = (N.pts x).1 ≫ φt.1)
    (hφt_sec : ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e𝒢 U ((ρ tm).1.app (op U) s)).1 = (e𝒢 U s).1 ≫ φt.1)
    (heφ : eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1) :
    letI := heckeModuleBar p
    ∃ s : HeckeAlg, s ∉ eisensteinMaximalIdeal p q ∧
      ∀ (U : specInt.Fppf) (x : 𝒢.1.obj (op U)), ((q : ℤ) ^ m) • x = 0 →
        (ρ s).1.app (op U) x = (ρ tm).1.app (op U) x := by
  letI := heckeModuleBar p
  classical
  by_cases htm : tm ∈ eisensteinMaximalIdeal p q
  swap
  · exact ⟨tm, htm, fun U x _ => rfl⟩

  have hV0 : ∀ x : JZero p, x ∈ eisensteinPrimaryTorsionBar p q m → x = 0 := by
    intro x hx
    have hx' := hx
    simp only [eisensteinPrimaryTorsionBar, AddSubgroup.mem_inf, AddMonoidHom.mem_ker] at hx'
    obtain ⟨hq, hP⟩ := hx'
    have hqx : (q ^ m : ℤ) • x = 0 := by
      simpa [AddMonoidHom.smul_apply] using hq
    have hfix : tm • x = x := (ht x hqx).mpr hx

    have hdir : Directed (· ≤ ·) (fun k : ℕ =>
        (Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup) := by
      refine Monotone.directed_le (fun k k' hkk' y hy => ?_)
      simp only [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBySet_iff] at hy ⊢
      intro a
      exact hy ⟨a.1, Ideal.pow_le_pow_right hkk' a.2⟩
    obtain ⟨k, hk⟩ := (AddSubgroup.mem_iSup_of_directed hdir).mp hP
    simp only [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBySet_iff] at hk
    exact Module.eq_zero_of_smul_eq_self_of_mem_of_pow_smul_eq_zero (eisensteinMaximalIdeal p q) tm htm x hfix k
      (fun a ha => hk ⟨a, ha⟩)

  obtain ⟨LK, hstr, hLKcomm, hLKhom, hLKinj, htors⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff N.L
      (fun t x y => N.comm t x y) (q ^ m)

  have hpts_nsmul : ∀ (n : ℕ) (x : JZero p), N.pts (n • x) = N.L.nsmul _ n (N.pts x) := by
    intro n x
    induction n with
    | zero =>
        rw [zero_nsmul, RelativeGroupLaw.nsmul_zero]

        have h0 : N.pts 0 = N.L.mul _ (N.pts 0) (N.pts 0) := by
          conv_lhs => rw [← add_zero (0 : JZero p)]
          exact N.pts_add 0 0
        have := congrArg (fun z => N.L.mul _ z (N.L.inv _ (N.pts 0))) h0
        rw [N.L.mul_inv_cancel, N.L.mul_assoc, N.L.mul_inv_cancel, N.L.mul_one] at this
        exact this.symm
    | succ n ih => rw [succ_nsmul, N.pts_add, ih, RelativeGroupLaw.nsmul_succ]
  have hpts_zero : N.pts 0 = N.L.one _ := by
    have := hpts_nsmul 0 0
    rwa [zero_nsmul, RelativeGroupLaw.nsmul_zero] at this
  have htorpt : ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → N.pts x ∈ N.L.torsionSubset _ (q ^ m) := by
    intro x hx
    have hxn : (q ^ m : ℕ) • x = 0 := by
      rw [← natCast_zsmul]; push_cast; exact hx
    rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def, ← hpts_nsmul, ← hpts_zero, hxn]

  have hidem : ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → tm • (tm • x) = tm • x := by
    intro x hx
    obtain ⟨z, hz⟩ := (htors _ (N.pts x)).mp (htorpt x hx)
    have hz1 : (N.pts x).1 = z.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
      rw [← hz]; rfl
    apply N.pts.injective
    apply Subtype.ext
    calc (N.pts (tm • (tm • x))).1 = (N.pts (tm • x)).1 ≫ φt.1 := hφt_pts _
      _ = ((N.pts x).1 ≫ φt.1) ≫ φt.1 := by rw [hφt_pts]
      _ = ((z.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) ≫ φt.1) ≫ φt.1 := by rw [hz1]
      _ = z.1 ≫ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1) ≫ φt.1 := by simp only [Category.assoc]
      _ = z.1 ≫ (eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) ≫ φt.1 := by rw [← heφ]
      _ = z.1 ≫ eK.1 ≫ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1) := by simp only [Category.assoc]
      _ = z.1 ≫ eK.1 ≫ (eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) := by rw [← heφ]
      _ = z.1 ≫ (eK.1 ≫ eK.1) ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by simp only [Category.assoc]
      _ = z.1 ≫ eK.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by rw [heK_idem]
      _ = z.1 ≫ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1) := by rw [heφ]
      _ = (z.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1) ≫ φt.1 := by simp only [Category.assoc]
      _ = (N.pts x).1 ≫ φt.1 := by rw [← hz1]
      _ = (N.pts (tm • x)).1 := (hφt_pts _).symm

  have hzT : ∀ (n : ℤ) (c : HeckeAlg) (x : JZero p), n • (c • x) = c • (n • x) := by
    intro n c x
    rw [← heckeModuleBar_C_smul, ← heckeModuleBar_C_smul, smul_smul, smul_smul, mul_comm]
  have htm0 : ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → tm • x = 0 := by
    intro x hx
    have hqt : (q ^ m : ℤ) • (tm • x) = 0 := by rw [hzT, hx, smul_zero]
    exact hV0 _ ((ht (tm • x) hqt).mp (hidem x hx))

  let Mq : Submodule HeckeAlg (JZero p) :=
    { carrier := {x | (q ^ m : ℤ) • x = 0}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [zsmul_add, ha, hb, add_zero]
      zero_mem' := by simp only [Set.mem_setOf_eq, zsmul_zero]
      smul_mem' := fun c {x} hx => by
        simp only [Set.mem_setOf_eq] at hx ⊢
        rw [hzT, hx, smul_zero] }
  haveI : Finite Mq := by
    refine Finite.of_injective (fun x : Mq => (⟨x.1, ?_⟩ : ↥(jZeroTorsion p (q ^ m)))) ?_
    · change x.1 ∈ (Submodule.torsionBy ℤ (JZero p) ((q ^ m : ℕ) : ℤ)).toAddSubgroup
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]
      have := x.2
      simp only [Mq, Set.mem_setOf_eq, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk] at this
      push_cast
      exact this
    · intro x y hxy
      exact Subtype.ext (congrArg (fun z : ↥(jZeroTorsion p (q ^ m)) => (z : JZero p)) hxy)
  have hmax : (eisensteinMaximalIdeal p q).IsMaximal := by
    have hsurj : Function.Surjective (eisensteinEval p) := fun n => ⟨algebraMap ℤ HeckeAlg n, AlgHom.commutes _ n⟩
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    haveI : (Ideal.span {(q : ℤ)}).IsMaximal :=
      ((Ideal.span_singleton_prime hq0).mpr (Nat.prime_iff_prime_int.mp Fact.out)).isMaximal
        (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hq0)
    exact Ideal.comap_isMaximal_of_surjective _ hsurj
  obtain ⟨s, hs, hsM⟩ := Module.exists_notMem_forall_smul_eq_zero_of_isMaximal_of_forall_smul_eq_zero_imp
    (M := Mq) (eisensteinMaximalIdeal p q) hmax (by
      intro y hy
      apply Subtype.ext
      apply hV0

      have hyq : (q ^ m : ℤ) • (y : JZero p) = 0 := y.2
      change (y : JZero p) ∈ eisensteinPrimaryTorsionBar p q m
      simp only [eisensteinPrimaryTorsionBar, AddSubgroup.mem_inf, AddMonoidHom.mem_ker]
      refine ⟨by simpa [AddMonoidHom.smul_apply] using hyq, ?_⟩
      apply AddSubgroup.mem_iSup_of_mem 1
      rw [Submodule.mem_toAddSubgroup, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [pow_one] at ha
      have := hy a ha
      exact congrArg Subtype.val this)
  have hs0 : ∀ x : JZero p, (q ^ m : ℤ) • x = 0 → s • x = 0 := fun x hx =>
    congrArg Subtype.val (hsM ⟨x, hx⟩)

  obtain ⟨φs, hφs_pts, hφs_sec⟩ := hρ s
  have hagree : (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φs.1, by
        rw [Category.assoc, φs.2]⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g)
      = ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1, by
        rw [Category.assoc, φt.2]⟩ := by
    apply ModularCurve.JZeroNeronIdentityComponent.schemeHomOver_schemeKer_ext_of_forall_algebraicClosure_point p q N m
    intro z

    let xz : JZero p := N.pts.symm (NeronModelInfra.schemeHomOverComp z
      (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ :
        SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g))
    have hxz : (N.pts xz).1 = z.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
      simp only [xz, Equiv.apply_symm_apply, NeronModelInfra.schemeHomOverComp_coe]
    have hxz_tor : (q ^ m : ℤ) • xz = 0 := by
      have hmem : N.pts xz ∈ N.L.torsionSubset _ (q ^ m) := (htors _ _).mpr ⟨z, by
        apply Subtype.ext; rw [NeronModelInfra.schemeHomOverComp_coe, hxz]⟩
      rw [RelativeGroupLaw.mem_torsionSubset, RelativeGroupLaw.isTorsionPoint_def, ← hpts_nsmul, ← hpts_zero] at hmem
      have := N.pts.injective hmem
      rw [← natCast_zsmul] at this
      push_cast at this
      exact this
    change z.1 ≫ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φs.1)
      = z.1 ≫ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1)
    rw [← Category.assoc, ← Category.assoc, ← hxz, ← hφs_pts, ← hφt_pts, hs0 xz hxz_tor, htm0 xz hxz_tor]
  have hagree1 : pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φs.1
      = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ φt.1 :=
    congrArg Subtype.val hagree

  refine ⟨s, hs, fun U x hx => ?_⟩
  apply (e𝒢 U).injective
  apply Subtype.ext
  rw [hφs_sec, hφt_sec]

  have he0 : e𝒢 U 0 = N.L.one U.hom := by
    have h0 : N.L.mul U.hom (e𝒢 U 0) (e𝒢 U 0) = N.L.mul U.hom (N.L.one U.hom) (e𝒢 U 0) := by
      rw [← he_add, add_zero, N.L.one_mul]
    have := congrArg (fun z => N.L.mul U.hom z (N.L.inv U.hom (e𝒢 U 0))) h0
    rwa [N.L.mul_assoc, N.L.mul_assoc, N.L.mul_inv_cancel, N.L.mul_one, N.L.mul_one] at this
  have he_nsmul : ∀ (n : ℕ) (y : 𝒢.1.obj (op U)), e𝒢 U (n • y) = N.L.nsmul U.hom n (e𝒢 U y) := by
    intro n y
    induction n with
    | zero => rw [zero_smul, RelativeGroupLaw.nsmul_zero]; exact he0
    | succ n ih => rw [add_smul, one_smul, he_add, ih, RelativeGroupLaw.nsmul_succ]
  have htor : e𝒢 U x ∈ N.L.torsionSubset U.hom (q ^ m) := by
    have hxn : (q ^ m : ℕ) • x = 0 := by
      rw [← natCast_zsmul]; push_cast; exact hx
    change N.L.nsmul U.hom (q ^ m) (e𝒢 U x) = N.L.one U.hom
    rw [← he_nsmul, ← he0, hxn]
  obtain ⟨y, hy⟩ := (htors U.hom (e𝒢 U x)).mp htor
  have hy1 : (e𝒢 U x).1 = y.1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 := by
    rw [← hy]; rfl
  rw [hy1, Category.assoc, Category.assoc, hagree1]

end S_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_notMem_forall_zsmul_eq_zero_imp_app_eq (solution)
