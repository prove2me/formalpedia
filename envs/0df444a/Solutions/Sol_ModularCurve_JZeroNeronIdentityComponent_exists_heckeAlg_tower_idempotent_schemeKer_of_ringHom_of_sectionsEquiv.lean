-- Prove2me | solution 1 for ModularCurve.JZeroNeronIdentityComponent.exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fa2699c1-53c5-5733-90c5-9a6246c8b034

import Definitions.Def_ModularCurve_JZeroNeronIdentityComponent
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Theorems.Thm_ModularCurve_exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
import Theorems.Thm_ModularCurve_JZeroNeronIdentityComponent_isReduced_schemeKer_pow
import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "JZeroNeronIdentityComponent eisensteinPrimaryTorsionBar jZeroTorsion heckeModuleBar JZero HeckeAlg exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar JZeroNeronIdentityComponent.schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end JZeroNeronIdentityComponent.isReduced_schemeKer_pow"
namespace IdemLevel
p2m_open "ModularCurve"

variable {p : ℕ} [Fact p.Prime] (N : JZeroNeronIdentityComponent p)

noncomputable abbrev qbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℤ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ (AlgebraicClosure ℚ)))

theorem pts_zero : N.pts 0 = N.L.one qbar := by
  letI := N.L.pointGroup qbar
  have h := N.pts_add 0 0
  rw [add_zero] at h
  have h2 : (N.pts 0 : SchemeHomOver qbar N.g) * (N.pts 0) = N.pts 0 := h.symm
  exact mul_eq_left.mp h2

theorem pts_nsmul (n : ℕ) (y : JZero p) : N.pts (n • y) = N.L.nsmul qbar n (N.pts y) := by
  induction n with
  | zero => rw [zero_nsmul, pts_zero, N.L.nsmul_zero]
  | succ k ih => rw [succ_nsmul, N.pts_add, ih, N.L.nsmul_succ]

theorem pts_mem_torsionSubset_iff (n : ℕ) (y : JZero p) :
    N.pts y ∈ N.L.torsionSubset qbar n ↔ (n : ℤ) • y = 0 := by
  rw [N.L.mem_torsionSubset, N.L.isTorsionPoint_def, ← pts_nsmul, ← pts_zero, N.pts.apply_eq_iff_eq,
    natCast_zsmul]

section level
variable (q : ℕ) [Fact q.Prime] (m : ℕ)

private noncomputable abbrev _root_.ModularCurve.IdemLevel.fst : N.L.schemeKer (q ^ m) ⟶ N.G :=
  pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1

p2m_export "ModularCurve.IdemLevel" "fst"
theorem hq0 : 0 < q ^ m := pow_pos (Fact.out : q.Prime).pos m

theorem flat_fst_comp : Flat (fst N q m ≫ N.g) := by
  obtain ⟨-, hk, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
    N.L N.comm (q ^ m)
  haveI : Flat (N.L.schemeNsmul (q ^ m)) := N.nsmul_flat _ (hq0 q m)
  change Flat (pullback.fst _ _ ≫ N.g)
  rw [hk]
  infer_instance

theorem lft_fst_comp : LocallyOfFiniteType (fst N q m ≫ N.g) := by
  obtain ⟨-, hk, -⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff
    N.L N.comm (q ^ m)
  haveI : LocallyOfFiniteType N.g := N.locallyOfFiniteType
  haveI : LocallyOfFiniteType (N.L.schemeNsmul (q ^ m) ≫ N.g) := by
    rw [N.L.schemeNsmul_over]; infer_instance
  haveI : LocallyOfFiniteType (N.L.schemeNsmul (q ^ m)) := locallyOfFiniteType_of_comp _ N.g
  change LocallyOfFiniteType (pullback.fst _ _ ≫ N.g)
  rw [hk]
  infer_instance

theorem exists_pts_eq (x : SchemeHomOver qbar (fst N q m ≫ N.g)) :
    ∃ y : JZero p, (q ^ m : ℤ) • y = 0 ∧ (N.pts y).1 = x.1 ≫ fst N q m := by
  obtain ⟨-, -, -, -, -, hpts⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff N.L N.comm (q ^ m)
  have hmem : NeronModelInfra.schemeHomOverComp x ⟨fst N q m, rfl⟩ ∈ N.L.torsionSubset qbar (q ^ m) :=
    (hpts qbar _).mpr ⟨x, rfl⟩
  refine ⟨N.pts.symm (NeronModelInfra.schemeHomOverComp x ⟨fst N q m, rfl⟩), ?_, ?_⟩
  · have h2 := (pts_mem_torsionSubset_iff N (q ^ m) (N.pts.symm (NeronModelInfra.schemeHomOverComp x ⟨fst N q m, rfl⟩))).mp
      (by rw [Equiv.apply_symm_apply]; exact hmem)
    exact_mod_cast h2
  · rw [Equiv.apply_symm_apply]
    rfl

theorem rig (ψ₁ ψ₂ : SchemeHomOver N.g N.g)
    (h : ∀ y : JZero p, (q ^ m : ℤ) • y = 0 → (N.pts y).1 ≫ ψ₁.1 = (N.pts y).1 ≫ ψ₂.1) :
    fst N q m ≫ ψ₁.1 = fst N q m ≫ ψ₂.1 := by
  haveI := flat_fst_comp N q m
  haveI := lft_fst_comp N q m
  haveI : IsReduced (N.L.schemeKer (q ^ m)) := ModularCurve.JZeroNeronIdentityComponent.isReduced_schemeKer_pow p q N m
  haveI : IsSeparated N.g := N.separated
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := @AlgebraicClosure.instIsAlgClosure ℚ _
  have key := AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
    (R := ℤ) ℚ (AlgebraicClosure ℚ) (gY := fst N q m ≫ N.g) (gX := N.g)
    (NeronModelInfra.schemeHomOverComp ⟨fst N q m, rfl⟩ ψ₁) (NeronModelInfra.schemeHomOverComp ⟨fst N q m, rfl⟩ ψ₂)
    (fun x => by
      obtain ⟨y, hy, hyx⟩ := exists_pts_eq N q m x
      change x.1 ≫ fst N q m ≫ ψ₁.1 = x.1 ≫ fst N q m ≫ ψ₂.1
      rw [← Category.assoc, ← Category.assoc, ← hyx]
      exact h y hy)
  exact congrArg Subtype.val key

end level

section sections
variable (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
  (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
  (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))

include he_add in
theorem e_zero (U : specInt.Fppf) : e U 0 = N.L.one U.hom := by
  letI : Group (SchemeHomOver U.hom N.g) := N.L.pointGroup U.hom
  have h := he_add U 0 0
  rw [add_zero] at h
  have h2 : (e U 0 : SchemeHomOver U.hom N.g) * (e U 0) = e U 0 := h.symm
  exact mul_eq_left.mp h2

include he_add in
theorem e_nsmul (U : specInt.Fppf) (n : ℕ) (s : 𝒢.1.obj (op U)) : e U (n • s) = N.L.nsmul U.hom n (e U s) := by
  induction n with
  | zero => rw [zero_nsmul, e_zero N 𝒢 e he_add, N.L.nsmul_zero]
  | succ k ih => rw [succ_nsmul, he_add, ih, N.L.nsmul_succ]

include he_add in

theorem exists_lift_of_torsion (q : ℕ) [Fact q.Prime] (m : ℕ) (U : specInt.Fppf) (s : 𝒢.1.obj (op U))
    (hs : (q ^ m : ℤ) • s = 0) : ∃ u : U.left ⟶ N.L.schemeKer (q ^ m), (e U s).1 = u ≫ fst N q m := by
  obtain ⟨-, -, -, -, -, hpts⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_relativeGroupLaw_schemeKer_forall_mem_torsionSubset_iff N.L N.comm (q ^ m)
  have hmem : e U s ∈ N.L.torsionSubset U.hom (q ^ m) := by
    change N.L.nsmul U.hom (q ^ m) (e U s) = N.L.one U.hom
    rw [← e_nsmul N 𝒢 e he_add, ← e_zero N 𝒢 e he_add U]
    congr 1
    rw [← natCast_zsmul]
    exact_mod_cast hs
  obtain ⟨y, hy⟩ := (hpts U.hom _).mp hmem
  exact ⟨y.1, by rw [← hy]; rfl⟩

end sections

end ModularCurve.IdemLevel

open ModularCurve.IdemLevel in

theorem solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (N : JZeroNeronIdentityComponent p)
    (𝒢 : Sheaf (smallFppfTopology specInt) Ab.{1})
    (e : ∀ U : specInt.Fppf, 𝒢.1.obj (op U) ≃ SchemeHomOver U.hom N.g)
    (he_add : ∀ (U : specInt.Fppf) (s s' : 𝒢.1.obj (op U)), e U (s + s') = N.L.mul U.hom (e U s) (e U s'))
    (he : ∀ {U V : specInt.Fppf} (k : U ⟶ V) (s : 𝒢.1.obj (op V)),
        e U (𝒢.1.map k.op s) = schemeHomOverComp k.left (MorphismProperty.Over.w k) (e V s))
    (ρ : HeckeAlg →+* End 𝒢)
    (hρ : letI := heckeModuleBar p
      ∀ t : HeckeAlg, ∃ φ : SchemeHomOver N.g N.g,
        (∀ x : JZero p, (N.pts (t • x)).1 = (N.pts x).1 ≫ φ.1) ∧
        ∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U ((ρ t).1.app (op U) s)).1 = (e U s).1 ≫ φ.1)
    (hfin : ∀ m : ℕ, Finite ↥(jZeroTorsion p (q ^ m))) :
    letI := heckeModuleBar p
    ∃ (t : ℕ → HeckeAlg) (φ : ℕ → SchemeHomOver N.g N.g)
      (eK : ∀ m : ℕ, SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),

      (∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
        t m • (t m • x) = t m • x ∧ (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m) ∧
          t (m + 1) • x = t m • x) ∧

      (∀ (m : ℕ) (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (q ^ m : ℤ) • s = 0 →
        (ρ (t m)).1.app (op U) ((ρ (t m)).1.app (op U) s) = (ρ (t m)).1.app (op U) s ∧
        (ρ (t (m + 1))).1.app (op U) s = (ρ (t m)).1.app (op U) s) ∧

      (∀ m : ℕ,
        (eK m).1 ≫ (eK m).1 = (eK m).1 ∧
        (∀ x : JZero p, (N.pts (t m • x)).1 = (N.pts x).1 ≫ (φ m).1) ∧
        (∀ (U : specInt.Fppf) (s : 𝒢.1.obj (op U)), (e U ((ρ (t m)).1.app (op U) s)).1 = (e U s).1 ≫ (φ m).1) ∧
        (eK m).1 ≫ pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φ m).1 ∧
        pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φ (m + 1)).1 = pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ (φ m).1 ∧
        (∀ (LK : RelativeGroupLaw ℤ (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
          (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
            NeronModelInfra.schemeHomOverComp (LK.mul s x y)
                (⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩ : SchemeHomOver (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g) N.g) =
              N.L.mul s (NeronModelInfra.schemeHomOverComp x ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)
                (NeronModelInfra.schemeHomOverComp y ⟨pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1, rfl⟩)) →
          ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver s (pullback.fst (N.L.schemeNsmul (q ^ m)) (N.L.one (𝟙 (Spec (CommRingCat.of ℤ)))).1 ≫ N.g)),
            NeronModelInfra.schemeHomOverComp (LK.mul s x y) (eK m) =
              LK.mul s (NeronModelInfra.schemeHomOverComp x (eK m)) (NeronModelInfra.schemeHomOverComp y (eK m)))) := by
  letI := heckeModuleBar p
  obtain ⟨t, ht⟩ := ModularCurve.exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar p q hfin

  choose φ hφpts hφsec using fun m => hρ (t m)
  have hφhom : ∀ (m : ℕ) {T : Scheme.{0}} (tt : T ⟶ Spec (CommRingCat.of ℤ)) (x y : SchemeHomOver tt N.g),
      NeronModelInfra.schemeHomOverComp (N.L.mul tt x y) (φ m) =
        N.L.mul tt (NeronModelInfra.schemeHomOverComp x (φ m)) (NeronModelInfra.schemeHomOverComp y (φ m)) :=
    fun m => ModularCurve.JZeroNeronIdentityComponent.schemeHomOverComp_mul_eq_mul_of_sectionsEquiv_end
      p N 𝒢 e he_add he (ρ (t m)) (φ m) (hφsec m)

  have hEK := fun m => GoodReductionJacobian.RelativeGroupLaw.existsUnique_schemeKer_comp_fst_eq_fst_comp_of_hom
    N.L N.comm (q ^ m) (φ m) (hφhom m)
  choose eK heK huniq hhomK using hEK

  have rig_idem : ∀ m, fst N q m ≫ (φ m).1 ≫ (φ m).1 = fst N q m ≫ (φ m).1 := by
    intro m
    have := rig N q m (NeronModelInfra.schemeHomOverComp (φ m) (φ m)) (φ m) (fun y hy => by
      change (N.pts y).1 ≫ (φ m).1 ≫ (φ m).1 = _
      rw [← Category.assoc, ← hφpts, ← hφpts, (ht m y hy).1])
    exact this
  have rig_compat : ∀ m, fst N q m ≫ (φ (m + 1)).1 = fst N q m ≫ (φ m).1 := by
    intro m
    exact rig N q m (φ (m + 1)) (φ m) (fun y hy => by rw [← hφpts, ← hφpts, (ht m y hy).2.2])
  refine ⟨t, φ, eK, ht, ?_, ?_⟩
  ·
    intro m U s hs
    obtain ⟨u, hu⟩ := exists_lift_of_torsion N 𝒢 e he_add q m U s hs
    constructor
    · apply (e U).injective
      apply Subtype.ext
      rw [hφsec, hφsec, hu]
      calc (u ≫ fst N q m) ≫ (φ m).1 ≫ (φ m).1 = u ≫ (fst N q m ≫ (φ m).1 ≫ (φ m).1) := Category.assoc _ _ _
        _ = u ≫ (fst N q m ≫ (φ m).1) := by rw [rig_idem m]
        _ = (u ≫ fst N q m) ≫ (φ m).1 := (Category.assoc _ _ _).symm
    · apply (e U).injective
      apply Subtype.ext
      rw [hφsec, hφsec, hu]
      calc (u ≫ fst N q m) ≫ (φ (m + 1)).1 = u ≫ (fst N q m ≫ (φ (m + 1)).1) := Category.assoc _ _ _
        _ = u ≫ (fst N q m ≫ (φ m).1) := by rw [rig_compat m]
        _ = (u ≫ fst N q m) ≫ (φ m).1 := (Category.assoc _ _ _).symm
  ·
    intro m
    refine ⟨?_, hφpts m, hφsec m, heK m, rig_compat m, hhomK m⟩
    have h2 : (NeronModelInfra.schemeHomOverComp (eK m) (eK m)).1 ≫ fst N q m = fst N q m ≫ (φ m).1 := by
      change ((eK m).1 ≫ (eK m).1) ≫ _ = _
      rw [Category.assoc, heK, ← Category.assoc, heK, Category.assoc, rig_idem]
    have h3 := huniq m _ h2
    exact congrArg Subtype.val h3

end S_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv
end P2MW
export P2MW.S_ModularCurve_JZeroNeronIdentityComponent_exists_heckeAlg_tower_idempotent_schemeKer_of_ringHom_of_sectionsEquiv (solution)
