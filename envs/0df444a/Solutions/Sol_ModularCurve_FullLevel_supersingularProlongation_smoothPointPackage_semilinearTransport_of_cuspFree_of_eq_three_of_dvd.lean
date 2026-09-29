-- Prove2me | solution 1 for ModularCurve.FullLevel.supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_three_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c0387d84-ad76-57be-b921-238a84acc0c4

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringW2
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_PlaceWidthChar
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_three_of_dvd

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup ModularCurve.UVCrossingModel
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

namespace LphiR

open scoped Pointwise

section Generic

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]

theorem mem_smul_toValuationSubring_iff (g : SemilinearAut L F) (P : Place L F) (f : F) :
    f ∈ (g • P).toValuationSubring ↔ g⁻¹ • f ∈ P.toValuationSubring := by
  rw [SemilinearAut.smul_toValuationSubring, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]

theorem isRational_smul (g : SemilinearAut L F) {P : Place L F} (hP : P.IsRational) :
    (g • P).IsRational := by
  intro y
  obtain ⟨x, rfl⟩ := (SemilinearAut.smulResidueRingEquiv g P).surjective y
  obtain ⟨a, rfl⟩ := hP x
  exact ⟨SemilinearAut.baseAut g a, (SemilinearAut.smulResidueRingEquiv_algebraMap g P a).symm⟩

theorem evalAt_smul (g : SemilinearAut L F) {P : Place L F} (hP : P.IsRational) {f : F}
    (hf : f ∈ (g • P).toValuationSubring) :
    (g • P).evalAt f = SemilinearAut.baseAut g (P.evalAt (g⁻¹ • f)) := by
  have hf' : g⁻¹ • f ∈ P.toValuationSubring := (mem_smul_toValuationSubring_iff g P f).mp hf
  apply (g • P).algebraMap_residueField_injective
  rw [(g • P).algebraMap_evalAt (isRational_smul g hP) hf,
    ← SemilinearAut.smulResidueRingEquiv_algebraMap g P, P.algebraMap_evalAt hP hf']
  symm
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  congr 1
  exact Subtype.ext (smul_inv_smul g f)

theorem evalAt_smul_smul (g : SemilinearAut L F) {P : Place L F} (hP : P.IsRational) {f : F}
    (hf : f ∈ P.toValuationSubring) :
    (g • P).evalAt (g • f) = SemilinearAut.baseAut g (P.evalAt f) := by
  have hf' : g • f ∈ (g • P).toValuationSubring := by
    rw [mem_smul_toValuationSubring_iff, inv_smul_smul]; exact hf
  rw [evalAt_smul g hP hf', inv_smul_smul]

theorem valuation_map_lt_one_iff {A : ValuationSubring L} (σ : L ≃+* L) (hσ : ∀ x : L, σ x ∈ A ↔ x ∈ A)
    (x : L) : A.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  have key : ∀ y : L, A.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ A := fun y => by
    by_cases hy : y = 0
    · subst hy; simp
    · rw [← not_le, A.valuation.one_le_val_iff hy, ValuationSubring.valuation_le_one_iff]
      simp [hy]
  rw [key, key, ← map_inv₀ σ, hσ, map_eq_zero_iff σ σ.injective]

def restrictA {A : ValuationSubring L} (σ : L ≃+* L) (hσ : ∀ x : L, σ x ∈ A ↔ x ∈ A) : ↥A ≃+* ↥A where
  toFun a := ⟨σ a, (hσ a).mpr a.2⟩
  invFun b := ⟨σ.symm b, by rw [← hσ, RingEquiv.apply_symm_apply]; exact b.2⟩
  left_inv a := Subtype.ext (σ.symm_apply_apply a)
  right_inv b := Subtype.ext (σ.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul σ (a : L) (b : L))
  map_add' a b := Subtype.ext (map_add σ (a : L) (b : L))

@[scoped simp] theorem coe_restrictA {A : ValuationSubring L} (σ : L ≃+* L) (hσ : ∀ x : L, σ x ∈ A ↔ x ∈ A)
    (a : ↥A) : ((restrictA σ hσ a : ↥A) : L) = σ a := rfl

@[scoped simp] theorem coe_restrictA_symm {A : ValuationSubring L} (σ : L ≃+* L) (hσ : ∀ x : L, σ x ∈ A ↔ x ∈ A)
    (b : ↥A) : (((restrictA σ hσ).symm b : ↥A) : L) = σ.symm b := rfl

theorem ord_map_of_forall_mem_iff {k Fbar : Type*} [Field k] [Field Fbar] [Algebra k Fbar]
    (φF : Fbar ≃+* Fbar) (Q Q' : Place k Fbar)
    (hQ' : ∀ y : Fbar, y ∈ Q'.toValuationSubring ↔ φF.symm y ∈ Q.toValuationSubring) (y : Fbar) :
    Q'.ord (φF y) = Q.ord y := by

  let θ : ↥Q.toValuationSubring ≃+* ↥Q'.toValuationSubring :=
    { toFun := fun z => ⟨φF z, (hQ' _).mpr (by rw [RingEquiv.symm_apply_apply]; exact z.2)⟩
      invFun := fun w => ⟨φF.symm w, (hQ' _).mp w.2⟩
      left_inv := fun z => Subtype.ext (φF.symm_apply_apply z)
      right_inv := fun w => Subtype.ext (φF.apply_symm_apply w)
      map_mul' := fun z w => Subtype.ext (map_mul φF (z : Fbar) (w : Fbar))
      map_add' := fun z w => Subtype.ext (map_add φF (z : Fbar) (w : Fbar)) }
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible Q.toValuationSubring
  obtain ⟨u, hu⟩ := Q.exists_unit_mul_zpow hy hπ
  set n := Q.ord y with hn
  have hπ' : Irreducible (θ π) := (MulEquiv.irreducible_iff θ).mpr hπ
  have hu' : IsUnit (θ (u : Q.toValuationSubring)) := u.isUnit.map θ
  have hcoeu : ((hu'.unit : Q'.toValuationSubring) : Fbar) = φF ((u : Q.toValuationSubring) : Fbar) := by
    rw [IsUnit.unit_spec]; rfl
  have key : φF y = ((hu'.unit : Q'.toValuationSubring) : Fbar) * (((θ π : Q'.toValuationSubring) : Fbar) ^ n) := by
    rw [hcoeu, hu, map_mul, map_zpow₀]; rfl
  rw [key, Q'.ord_unit_smul_zpow hu'.unit hπ' n]

end Generic

section Pkg

variable {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F] (A : ValuationSubring L)
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]

def Pkg (R : RegularProlongation A F Fbar) (Q : Place (ResidueField ↥A) Fbar)
    (S : Subring F) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A) (D : Set (Place L F)) : Prop :=
          (∀ a : ↥A, algebraMap L F (a : L) ∈ S) ∧
          (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
          (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : F) = algebraMap L F (a : L)) ∧
          (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
          χ₀ (φ Polynomial.X) = 0 ∧
          (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
            ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
          (∀ f : ↥(S), ∃ hR : (f : F) ∈ R.integers, ∃ hm : R.residue ⟨(f : F), hR⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : F), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
          (∃ hR : ((φ Polynomial.X : ↥(S)) : F) ∈ R.integers,
            Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : F), hR⟩) = 1) ∧
          (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : F) ∈ P.toValuationSubring ∧ P.evalAt (f : F) ∈ A) ∧
            (∀ f : ↥(S), A.valuation (P.evalAt (f : F)) < 1 ↔ χ₀ f = 0))) ∧
          (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
            (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
            ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : F) = ((χ f : ↥A) : L)) ∧
          (∀ P ∈ D, ∀ f : F, f ∈ P.toValuationSubring ↔
            ∃ g h : ↥(S), P.evalAt (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) ∧
          (∀ f : F, f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
            ∃ (c : L) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap L F c * f = ((u : ↥(S)) : F)) ∧
          (∀ f : F, f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)

theorem Pkg.transport (R : RegularProlongation A F Fbar)
    (g : SemilinearAut L F)
    (hgA : ∀ x : L, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A)
    (hgR : ∀ f : F, g • f ∈ R.integers ↔ f ∈ R.integers)
    (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
    (hψ : ∀ a : ↥A, ψ (IsLocalRing.residue ↥A a) =
      IsLocalRing.residue ↥A ⟨SemilinearAut.baseAut g (a : L), (hgA (a : L)).mpr a.2⟩)
    (φF : Fbar ≃+* Fbar)
    (hφ : ∀ (f : F) (hf : f ∈ R.integers), R.residue ⟨g • f, (hgR f).mpr hf⟩ = φF (R.residue ⟨f, hf⟩))
    (Q Q' : Place (ResidueField ↥A) Fbar)
    (hQ' : ∀ y : Fbar, y ∈ Q'.toValuationSubring ↔ φF.symm y ∈ Q.toValuationSubring)
    (S : Subring F) (φS : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A) (D : Set (Place L F))
    (h : Pkg A R Q S φS χ₀ D) :
    ∃ (S' : Subring F) (φS' : Polynomial ↥A →+* ↥S') (χ₀' : ↥S' →+* ResidueField ↥A) (D' : Set (Place L F))
      (hS : ∀ f : F, f ∈ S ↔ g • f ∈ S'),
      (∀ f : ↥S, χ₀' ⟨g • (f : F), (hS (f : F)).mp f.2⟩ = ψ (χ₀ f)) ∧
      (∀ P : Place L F, P ∈ D ↔ g • P ∈ D') ∧
      Pkg A R Q' S' φS' χ₀' D' := by
  classical
  obtain ⟨hAS, hsm, hur, hC, hχC, hχX, hsec, hres, hord, hD, hsecP, hval, hunit, hloc⟩ := h

  set σ : L ≃+* L := SemilinearAut.baseAut g with hσ
  let σA : ↥A ≃+* ↥A := restrictA σ hgA
  have hσA : ∀ a : ↥A, ((σA a : ↥A) : L) = σ a := fun a => rfl
  have hσAs : ∀ b : ↥A, ((σA.symm b : ↥A) : L) = σ.symm b := fun b => rfl
  have hψ' : ∀ a : ↥A, ψ (IsLocalRing.residue ↥A a) = IsLocalRing.residue ↥A (σA a) := hψ
  have hψs : ∀ b : ↥A, ψ.symm (IsLocalRing.residue ↥A b) = IsLocalRing.residue ↥A (σA.symm b) := by
    intro b
    apply ψ.injective
    rw [RingEquiv.apply_symm_apply, hψ', RingEquiv.apply_symm_apply]
  let τ : F ≃+* F := SemilinearAut.toRingAut g
  have hτ : ∀ f : F, g • f = τ f := fun f => rfl
  have hτs : ∀ f : F, g⁻¹ • f = τ.symm f := fun f => rfl

  let S' : Subring F := S.map τ.toRingHom
  have hS'mem : ∀ f : F, f ∈ S' ↔ g⁻¹ • f ∈ S := by
    intro f
    constructor
    · rintro ⟨s, hs, hsf⟩
      have : g⁻¹ • f = s := by
        rw [hτs, ← hsf]; exact τ.symm_apply_apply s
      rw [this]; exact hs
    · intro hf
      exact ⟨g⁻¹ • f, hf, by rw [hτs]; exact τ.apply_symm_apply f⟩
  have hS : ∀ f : F, f ∈ S ↔ g • f ∈ S' := by
    intro f; rw [hS'mem, inv_smul_smul]
  let eS : ↥S ≃+* ↥S' := τ.subringMap
  have heS : ∀ s : ↥S, ((eS s : ↥S') : F) = g • (s : F) := fun s => rfl
  have heSs : ∀ s' : ↥S', ((eS.symm s' : ↥S) : F) = g⁻¹ • (s' : F) := fun s' => rfl

  let φS' : Polynomial ↥A →+* ↥S' := eS.toRingHom.comp (φS.comp (Polynomial.mapRingHom σA.symm.toRingHom))
  let χ₀' : ↥S' →+* ResidueField ↥A := ψ.toRingHom.comp (χ₀.comp eS.symm.toRingHom)
  let D' : Set (Place L F) := {P | g⁻¹ • P ∈ D}
  have hφ'C : ∀ a : ↥A, φS' (Polynomial.C a) = eS (φS (Polynomial.C (σA.symm a))) := by
    intro a
    show eS (φS (Polynomial.map σA.symm.toRingHom (Polynomial.C a))) = _
    rw [Polynomial.map_C]; rfl
  have hφ'X : φS' Polynomial.X = eS (φS Polynomial.X) := by
    show eS (φS (Polynomial.map σA.symm.toRingHom Polynomial.X)) = _
    rw [Polynomial.map_X]
  have hχ₀' : ∀ s' : ↥S', χ₀' s' = ψ (χ₀ (eS.symm s')) := fun s' => rfl
  have hχ₀'e : ∀ s : ↥S, χ₀' (eS s) = ψ (χ₀ s) := by
    intro s; rw [hχ₀', RingEquiv.symm_apply_apply]
  have hD'mem : ∀ P : Place L F, P ∈ D' ↔ g⁻¹ • P ∈ D := fun P => Iff.rfl

  have hgalg : ∀ x : L, g • algebraMap L F x = algebraMap L F (σ x) := fun x => SemilinearAut.smul_algebraMap g x
  have hgalgs : ∀ x : L, g⁻¹ • algebraMap L F x = algebraMap L F (σ.symm x) := by
    intro x
    rw [SemilinearAut.smul_algebraMap, SemilinearAut.baseAut_inv]
  refine ⟨S', φS', χ₀', D', hS, ?_, ?_, ?_⟩
  ·
    intro f
    have : (⟨g • (f : F), (hS (f : F)).mp f.2⟩ : ↥S') = eS f := Subtype.ext rfl
    rw [this, hχ₀'e]
  ·
    intro P
    show P ∈ D ↔ g⁻¹ • (g • P) ∈ D
    rw [inv_smul_smul]

  let θ : ↥Q.toValuationSubring ≃+* ↥Q'.toValuationSubring :=
    { toFun := fun z => ⟨φF z, (hQ' _).mpr (by rw [RingEquiv.symm_apply_apply]; exact z.2)⟩
      invFun := fun w => ⟨φF.symm w, (hQ' _).mp w.2⟩
      left_inv := fun z => Subtype.ext (φF.symm_apply_apply z)
      right_inv := fun w => Subtype.ext (φF.apply_symm_apply w)
      map_mul' := fun z w => Subtype.ext (map_mul φF (z : Fbar) (w : Fbar))
      map_add' := fun z w => Subtype.ext (map_add φF (z : Fbar) (w : Fbar)) }
  have hθ : ∀ z : ↥Q.toValuationSubring, ((θ z : ↥Q'.toValuationSubring) : Fbar) = φF z := fun z => rfl

  have hφFconst : ∀ x : ResidueField ↥A,
      φF (algebraMap (ResidueField ↥A) Fbar x) = algebraMap (ResidueField ↥A) Fbar (ψ x) := by
    intro x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rw [← R.residue_algebraMap a, ← hφ, hψ']
    rw [← R.residue_algebraMap (σA a)]
    congr 1
    apply Subtype.ext
    show g • algebraMap L F (a : L) = algebraMap L F ((σA a : ↥A) : L)
    rw [hgalg]; rfl
  have hθbar : ∀ x : ResidueField ↥A,
      IsLocalRing.ResidueField.mapEquiv θ (algebraMap (ResidueField ↥A) Q.ResidueField x) =
        algebraMap (ResidueField ↥A) Q'.ResidueField (ψ x) := by
    intro x
    have h3 : θ (algebraMap (ResidueField ↥A) ↥Q.toValuationSubring x) =
        algebraMap (ResidueField ↥A) ↥Q'.toValuationSubring (ψ x) := by
      apply Subtype.ext
      rw [hθ, Place.coe_algebraMap, Place.coe_algebraMap, hφFconst]
    show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
    rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
    exact congrArg _ h3

  have hDrat : ∀ P ∈ D, P.IsRational := fun P hP => ((hD P).mp hP).1
  have hDint : ∀ P ∈ D, ∀ s : ↥S, (s : F) ∈ P.toValuationSubring := fun P hP s => (((hD P).mp hP).2.1 s).1
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8, ?c9, ?c10, ?c11, ?c12, ?c13, ?c14⟩
  case c1 =>
    intro a
    have h1 := (hS _).mp (hAS (σA.symm a))
    rw [hσAs, hgalg, RingEquiv.apply_symm_apply] at h1
    exact h1
  case c2 =>
    have hm : (Polynomial.mapRingHom (R := ↥A) σA.symm.toRingHom).FormallySmooth :=
      RingHom.FormallySmooth.of_bijective (Polynomial.mapEquiv σA.symm).bijective
    have he : (eS.toRingHom).FormallySmooth := RingHom.FormallySmooth.of_bijective eS.bijective
    exact RingHom.FormallySmooth.comp (RingHom.FormallySmooth.comp hm hsm) he
  case c3 =>
    have hm : (Polynomial.mapRingHom (R := ↥A) σA.symm.toRingHom).FormallyUnramified :=
      RingHom.FormallyUnramified.of_surjective (Polynomial.mapEquiv σA.symm).surjective
    have he : (eS.toRingHom).FormallyUnramified := RingHom.FormallyUnramified.of_surjective eS.surjective
    exact RingHom.FormallyUnramified.comp (RingHom.FormallyUnramified.comp hm hur) he
  case c4 =>
    intro a
    rw [hφ'C, heS, hC, hσAs, hgalg, RingEquiv.apply_symm_apply]
  case c5 =>
    intro a
    rw [hφ'C, hχ₀'e, hχC, hψ', RingEquiv.apply_symm_apply]
  case c6 =>
    rw [hφ'X, hχ₀'e, hχX, map_zero]
  case c7 =>
    intro c hc
    have hc₀ : IsLocalRing.residue ↥A (σA.symm c) = 0 := by
      rw [← hψs, hc, map_zero]
    obtain ⟨χ, ⟨hχa, hχr, hχc⟩, huniq⟩ := hsec (σA.symm c) hc₀
    refine ⟨σA.toRingHom.comp (χ.comp eS.symm.toRingHom), ⟨?_, ?_, ?_⟩, ?_⟩
    · intro a
      show σA (χ (eS.symm (φS' (Polynomial.C a)))) = a
      rw [hφ'C, RingEquiv.symm_apply_apply, hχa, RingEquiv.apply_symm_apply]
    · intro f
      show IsLocalRing.residue ↥A (σA (χ (eS.symm f))) = χ₀' f
      rw [← hψ', hχr, hχ₀']
    · show σA (χ (eS.symm (φS' Polynomial.X))) = c
      rw [hφ'X, RingEquiv.symm_apply_apply, hχc, RingEquiv.apply_symm_apply]
    · intro χ'' ⟨h1, h2, h3⟩

      have hback : σA.symm.toRingHom.comp (χ''.comp eS.toRingHom) = χ := by
        apply huniq
        refine ⟨?_, ?_, ?_⟩
        · intro a
          show σA.symm (χ'' (eS (φS (Polynomial.C a)))) = a
          have : eS (φS (Polynomial.C a)) = φS' (Polynomial.C (σA a)) := by
            rw [hφ'C, RingEquiv.symm_apply_apply]
          rw [this, h1, RingEquiv.symm_apply_apply]
        · intro f
          show IsLocalRing.residue ↥A (σA.symm (χ'' (eS f))) = χ₀ f
          rw [← hψs, h2, hχ₀'e, RingEquiv.symm_apply_apply]
        · show σA.symm (χ'' (eS (φS Polynomial.X))) = σA.symm c
          rw [← hφ'X, h3]
      apply RingHom.ext
      intro f'
      show χ'' f' = σA (χ (eS.symm f'))
      rw [← hback]
      show χ'' f' = σA (σA.symm (χ'' (eS (eS.symm f'))))
      rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  case c8 =>
    intro f'
    obtain ⟨hR, hm, hresEq⟩ := hres (eS.symm f')
    have hf'eq : (f' : F) = g • ((eS.symm f' : ↥S) : F) := by
      rw [heSs, smul_inv_smul]
    have hR' : (f' : F) ∈ R.integers := by rw [hf'eq]; exact (hgR _).mpr hR
    have hRes' : R.residue ⟨(f' : F), hR'⟩ = φF (R.residue ⟨((eS.symm f' : ↥S) : F), hR⟩) := by
      rw [← hφ]; congr 1; exact Subtype.ext hf'eq
    have hm' : R.residue ⟨(f' : F), hR'⟩ ∈ Q'.toValuationSubring := by
      rw [hRes', hQ', RingEquiv.symm_apply_apply]; exact hm
    refine ⟨hR', hm', ?_⟩
    have : (⟨R.residue ⟨(f' : F), hR'⟩, hm'⟩ : ↥Q'.toValuationSubring) =
        θ ⟨R.residue ⟨((eS.symm f' : ↥S) : F), hR⟩, hm⟩ := Subtype.ext hRes'
    have key : IsLocalRing.residue ↥Q'.toValuationSubring (θ ⟨R.residue ⟨((eS.symm f' : ↥S) : F), hR⟩, hm⟩) =
        IsLocalRing.ResidueField.mapEquiv θ
          (IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨((eS.symm f' : ↥S) : F), hR⟩, hm⟩) := by
      rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]; rfl
    rw [this, key, hresEq, hθbar, hχ₀']
  case c9 =>
    obtain ⟨hR, hordEq⟩ := hord
    have hXeq : ((φS' Polynomial.X : ↥S') : F) = g • ((φS Polynomial.X : ↥S) : F) := by
      rw [hφ'X, heS]
    have hR' : ((φS' Polynomial.X : ↥S') : F) ∈ R.integers := by rw [hXeq]; exact (hgR _).mpr hR
    refine ⟨hR', ?_⟩
    have : R.residue ⟨((φS' Polynomial.X : ↥S') : F), hR'⟩ = φF (R.residue ⟨((φS Polynomial.X : ↥S) : F), hR⟩) := by
      rw [← hφ]; congr 1; exact Subtype.ext hXeq
    rw [this, ord_map_of_forall_mem_iff φF Q Q' hQ', hordEq]
  case c10 =>
    intro P
    rw [hD'mem, hD (g⁻¹ • P)]
    have hgAs : ∀ x : L, σ.symm x ∈ A ↔ x ∈ A := fun x => by
      rw [← hgA (σ.symm x), hσ, RingEquiv.apply_symm_apply]
    constructor
    · rintro ⟨hrat, hint, hvalP⟩
      have hratP : P.IsRational := by
        have := isRational_smul g hrat; rwa [smul_inv_smul] at this
      refine ⟨hratP, fun f' => ?_, fun f' => ?_⟩
      · obtain ⟨h1, h2⟩ := hint (eS.symm f')
        have hmem : (f' : F) ∈ P.toValuationSubring := by
          rw [heSs] at h1

          have h1' := (mem_smul_toValuationSubring_iff g⁻¹ P (g⁻¹ • (f' : F))).mp h1
          rwa [inv_inv, smul_inv_smul] at h1'
        refine ⟨hmem, ?_⟩
        have hev : (g⁻¹ • P).evalAt ((eS.symm f' : ↥S) : F) = σ.symm (P.evalAt (f' : F)) := by
          rw [heSs, evalAt_smul_smul g⁻¹ hratP hmem, SemilinearAut.baseAut_inv]
        rw [hev] at h2
        exact (hgAs _).mp h2
      · obtain ⟨h1, -⟩ := hint (eS.symm f')
        have hmem : (f' : F) ∈ P.toValuationSubring := by
          rw [heSs] at h1
          have h1' := (mem_smul_toValuationSubring_iff g⁻¹ P (g⁻¹ • (f' : F))).mp h1
          rwa [inv_inv, smul_inv_smul] at h1'
        have hev : (g⁻¹ • P).evalAt ((eS.symm f' : ↥S) : F) = σ.symm (P.evalAt (f' : F)) := by
          rw [heSs, evalAt_smul_smul g⁻¹ hratP hmem, SemilinearAut.baseAut_inv]
        rw [hχ₀', map_eq_zero_iff ψ ψ.injective, ← hvalP (eS.symm f'), hev, valuation_map_lt_one_iff σ.symm hgAs]
    · rintro ⟨hratP, hint, hvalP⟩
      have hrat : (g⁻¹ • P).IsRational := isRational_smul g⁻¹ hratP
      refine ⟨hrat, fun s => ?_, fun s => ?_⟩
      · obtain ⟨h1, h2⟩ := hint (eS s)
        have hmem : (s : F) ∈ (g⁻¹ • P).toValuationSubring := by
          rw [mem_smul_toValuationSubring_iff, inv_inv]; rw [heS] at h1; exact h1
        refine ⟨hmem, ?_⟩
        rw [evalAt_smul g⁻¹ hratP hmem, inv_inv, SemilinearAut.baseAut_inv, hgAs, ← heS]
        exact h2
      · obtain ⟨h1, -⟩ := hint (eS s)
        have hmem : (s : F) ∈ (g⁻¹ • P).toValuationSubring := by
          rw [mem_smul_toValuationSubring_iff, inv_inv]; rw [heS] at h1; exact h1
        rw [evalAt_smul g⁻¹ hratP hmem, inv_inv, SemilinearAut.baseAut_inv, valuation_map_lt_one_iff σ.symm hgAs,
          ← heS, hvalP (eS s), hχ₀'e, map_eq_zero_iff ψ ψ.injective]
  case c11 =>
    intro χ' h1 h2

    let χ : ↥S →+* ↥A := σA.symm.toRingHom.comp (χ'.comp eS.toRingHom)
    have hχapp : ∀ s : ↥S, χ s = σA.symm (χ' (eS s)) := fun s => rfl
    have hχ1 : ∀ a : ↥A, χ (φS (Polynomial.C a)) = a := by
      intro a
      rw [hχapp]
      have : eS (φS (Polynomial.C a)) = φS' (Polynomial.C (σA a)) := by
        rw [hφ'C, RingEquiv.symm_apply_apply]
      rw [this, h1, RingEquiv.symm_apply_apply]
    have hχ2 : ∀ f : ↥S, IsLocalRing.residue ↥A (χ f) = χ₀ f := by
      intro f
      rw [hχapp, ← hψs, h2, hχ₀'e, RingEquiv.symm_apply_apply]
    obtain ⟨P₀, ⟨hP₀D, hP₀ev⟩, hP₀uniq⟩ := hsecP χ hχ1 hχ2
    have hrat₀ : P₀.IsRational := hDrat P₀ hP₀D
    refine ⟨g • P₀, ⟨?_, ?_⟩, ?_⟩
    · show g⁻¹ • (g • P₀) ∈ D
      rw [inv_smul_smul]; exact hP₀D
    · intro f'
      have hmem : ((eS.symm f' : ↥S) : F) ∈ P₀.toValuationSubring := hDint P₀ hP₀D _
      have : (f' : F) = g • ((eS.symm f' : ↥S) : F) := by rw [heSs, smul_inv_smul]
      rw [this, evalAt_smul_smul g hrat₀ hmem, hP₀ev, hχapp, RingEquiv.apply_symm_apply, hσAs, ← hσ,
        RingEquiv.apply_symm_apply]
    · intro P ⟨hPD', hPev⟩
      have hP₀' : g⁻¹ • P = P₀ := by
        apply hP₀uniq
        refine ⟨hPD', fun s => ?_⟩
        have hratP : P.IsRational := by
          have := isRational_smul g (hDrat _ hPD'); rwa [smul_inv_smul] at this
        have hmem : (s : F) ∈ (g⁻¹ • P).toValuationSubring := hDint _ hPD' s
        have hmem' : g • (s : F) ∈ P.toValuationSubring := by
          have := (mem_smul_toValuationSubring_iff g⁻¹ P (s : F)).mp hmem
          rwa [inv_inv] at this
        rw [evalAt_smul g⁻¹ hratP hmem, inv_inv, SemilinearAut.baseAut_inv, ← heS, hPev (eS s), hχapp, hσAs]
      rw [← hP₀', smul_inv_smul]
  case c12 =>
    intro P hPD' f
    have hP₀D : g⁻¹ • P ∈ D := hPD'
    have hrat₀ : (g⁻¹ • P).IsRational := hDrat _ hP₀D
    have hPeq : g • (g⁻¹ • P) = P := smul_inv_smul g P
    constructor
    · intro hf
      have hf₀ : g⁻¹ • f ∈ (g⁻¹ • P).toValuationSubring := by
        rw [mem_smul_toValuationSubring_iff, inv_inv, smul_inv_smul]; exact hf
      obtain ⟨a, b, hb, hab⟩ := (hval _ hP₀D (g⁻¹ • f)).mp hf₀
      refine ⟨eS a, eS b, ?_, ?_⟩
      · rw [heS, ← hPeq, evalAt_smul_smul g hrat₀ (hDint _ hP₀D b)]
        exact (map_ne_zero_iff σ σ.injective).mpr hb
      · rw [heS, heS, ← hab, smul_mul', smul_inv_smul]
    · rintro ⟨a', b', hb', hab'⟩
      have hmemb : ((eS.symm b' : ↥S) : F) ∈ (g⁻¹ • P).toValuationSubring := hDint _ hP₀D _
      have hb : (g⁻¹ • P).evalAt ((eS.symm b' : ↥S) : F) ≠ 0 := by
        intro h0
        apply hb'
        have : (b' : F) = g • ((eS.symm b' : ↥S) : F) := by rw [heSs, smul_inv_smul]
        rw [this, ← hPeq, evalAt_smul_smul g hrat₀ hmemb, h0, map_zero]
      have hab : g⁻¹ • f * ((eS.symm b' : ↥S) : F) = ((eS.symm a' : ↥S) : F) := by
        rw [heSs, heSs, ← smul_mul', hab']
      have hf₀ := (hval _ hP₀D (g⁻¹ • f)).mpr ⟨eS.symm a', eS.symm b', hb, hab⟩
      rw [← hPeq, mem_smul_toValuationSubring_iff]
      exact hf₀
  case c13 =>
    intro f hf0 hordD'
    have hf₀0 : g⁻¹ • f ≠ 0 := by
      rw [hτs]; exact (map_ne_zero_iff τ.symm τ.symm.injective).mpr hf0
    have hord₀ : ∀ P ∈ D, P.ord (g⁻¹ • f) = 0 := by
      intro P₀ hP₀
      have h1 : (g • P₀).ord (g • (g⁻¹ • f)) = P₀.ord (g⁻¹ • f) := SemilinearAut.ord_smul g P₀ _
      rw [smul_inv_smul] at h1
      rw [← h1]
      apply hordD'
      show g⁻¹ • (g • P₀) ∈ D
      rw [inv_smul_smul]; exact hP₀
    obtain ⟨c, u, hc, hcu⟩ := hunit (g⁻¹ • f) hf₀0 hord₀
    refine ⟨σ c, Units.map (eS : ↥S ≃+* ↥S').toMonoidHom u, (map_ne_zero_iff σ σ.injective).mpr hc, ?_⟩
    have : algebraMap L F (σ c) * f = g • (algebraMap L F c * (g⁻¹ • f)) := by
      rw [smul_mul', hgalg, smul_inv_smul]
    rw [this, hcu]
    rfl
  case c14 =>
    intro f hfR hfD'
    have hf₀R : g⁻¹ • f ∈ R.integers := by
      rw [← hgR, smul_inv_smul]; exact hfR
    have hf₀D : ∀ P ∈ D, g⁻¹ • f ∈ P.toValuationSubring := by
      intro P₀ hP₀
      have hmem := hfD' (g • P₀) (show g⁻¹ • (g • P₀) ∈ D by rw [inv_smul_smul]; exact hP₀)
      have := (mem_smul_toValuationSubring_iff g P₀ f).mp hmem
      exact this
    have := hloc (g⁻¹ • f) hf₀R hf₀D
    rw [hS'mem]; exact this

end Pkg

end LphiR
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_three_of_dvd.LphiR"

theorem solution
    (q : ℕ) [Fact q.Prime] (hq3 : q = 3) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ12 : ℓ % 12 = 11) (hℓM' : ℓ ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q M' (ResidueField A))
    (hle : modularFunctionFieldBar M' ≤ fieldBar q M')
    (R₀ : ConstantReduction A ↥(modularFunctionFieldBar M') (modularFunctionFieldC (ResidueField A) M'))
    (hR₀ : ∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ modularFunctionFieldBar M'),
      ∃ h : (⟨coeffMap A.subtype y, hy⟩ : ↥(modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (ResidueField A) M') : LaurentSeries (ResidueField A)) =
          coeffMap (IsLocalRing.residue ↥A) y)
    (s : ↥W)

    (FSS : Type) [Field FSS] [Algebra (ResidueField A) FSS]
    (R : RegularProlongation A (fieldBar q M') FSS)
    (N : Finset (Place (ResidueField ↥A) FSS))
    (Sx : Place (ResidueField ↥A) FSS → Subring ↥(fieldBar q M'))
    (φx : (Q : Place (ResidueField ↥A) FSS) → (Polynomial ↥A →+* ↥(Sx Q)))
    (χ₀x : (Q : Place (ResidueField ↥A) FSS) → (↥(Sx Q) →+* ResidueField ↥A))
    (Dx : Place (ResidueField ↥A) FSS → Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M')))
    (h0 : (∃ t : FSS, Transcendental (ResidueField A) t))
    (h1 : (∀ (f : ↥(modularFunctionFieldBar M')) (hf : f ∈ R₀.integers),
        (∀ P : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar M'),
          0 ≤ P.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(modularFunctionFieldBar M')) → 0 ≤ P.ord (f : ↥(modularFunctionFieldBar M'))) →
        (R₀.residue ⟨f, hf⟩ : modularFunctionFieldC (ResidueField A) M') ∈
            (s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).toValuationSubring →
          ∃ hC : (IntermediateField.inclusion hle f : fieldBar q M') ∈ R.integers,
            R.residue ⟨_, hC⟩ = algebraMap (ResidueField A) FSS
              ((s : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M')).evalAt
                (R₀.residue ⟨f, hf⟩))))
    (h2 : (∀ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' →
        R.integers.comap (levelAutBar q M' ζ γ).toAlgHom.toRingHom = R.integers))
    (hcard : N.card = q + 1)
    (hpkg : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N →

          (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ Sx Q) ∧
          (φx Q).FormallySmooth ∧ (φx Q).FormallyUnramified ∧
          (∀ a : ↥A, ((φx Q (Polynomial.C a) : ↥(Sx Q)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
          (∀ a : ↥A, χ₀x Q (φx Q (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
          χ₀x Q (φx Q Polynomial.X) = 0 ∧
          (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
            ∃! χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) ∧
              (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) ∧ χ (φx Q Polynomial.X) = c) ∧
          (∀ f : ↥(Sx Q), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
            IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
              algebraMap (ResidueField ↥A) Q.ResidueField (χ₀x Q f)) ∧
          (∃ hR : ((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')) ∈ R.integers,
            Q.ord (R.residue ⟨((φx Q Polynomial.X : ↥(Sx Q)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
          (∀ P, P ∈ Dx Q ↔ (P.IsRational ∧ (∀ f : ↥(Sx Q), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
            (∀ f : ↥(Sx Q), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀x Q f = 0))) ∧
          (∀ χ : ↥(Sx Q) →+* ↥A, (∀ a : ↥A, χ (φx Q (Polynomial.C a)) = a) →
            (∀ f : ↥(Sx Q), IsLocalRing.residue ↥A (χ f) = χ₀x Q f) →
            ∃! P, P ∈ Dx Q ∧ ∀ f : ↥(Sx Q), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
          (∀ P ∈ Dx Q, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
            ∃ g h : ↥(Sx Q), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ Dx Q, P.ord f = 0) →
            ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(Sx Q))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(Sx Q)) : ↥(fieldBar q M'))) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ Dx Q, f ∈ P.toValuationSubring) → f ∈ Sx Q)))
    (hdisj : (∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N → Q' ∉ N → ∀ P, P ∈ Dx Q → P ∈ Dx Q' → Q = Q'))
    (hcusp : (∀ Q : Place (ResidueField ↥A) FSS, Q ∉ N → ∀ P ∈ Dx Q, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : fieldBar q M')))
    (heqv : (∀ τ ∈ Subgroup.closure {τ : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M') |
            ∃ (ζ : Idx q) (γ : SL(2, ℤ)), γ ∈ Gamma0 M' ∧ τ = levelAutBar q M' ζ γ},
          ∀ (hτ : ∀ f : ↥(fieldBar q M'), τ f ∈ R.integers ↔ f ∈ R.integers) (Q : Place (ResidueField ↥A) FSS),
            (R.resAut τ hτ • Q ∈ N ↔ Q ∈ N) ∧
            (Q ∉ N → AlgebraicCurve.RegularProlongation.smulDisc τ (Dx Q) = Dx (R.resAut τ hτ • Q))))

    (hNpkg : (∀ Q ∈ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
          (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          ¬ (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S) ∧

          (∀ P ∈ D, 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
            ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))))))

    (hUniq : (∀ Q ∉ N, ∀ (S : Subring ↥(fieldBar q M')) (φ : Polynomial ↥A →+* ↥S) (χ₀ : ↥S →+* ResidueField ↥A)
          (D : Set (Place (AlgebraicClosure ℚ) ↥(fieldBar q M'))),
          (
            (∀ a : ↥A, algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ)) ∈ S) ∧
            (φ).FormallySmooth ∧ (φ).FormallyUnramified ∧
            (∀ a : ↥A, ((φ (Polynomial.C a) : ↥(S)) : ↥(fieldBar q M')) = algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') (a : (AlgebraicClosure ℚ))) ∧
            (∀ a : ↥A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue ↥A a) ∧
            χ₀ (φ Polynomial.X) = 0 ∧
            (∀ c : ↥A, IsLocalRing.residue ↥A c = 0 →
              ∃! χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) ∧
                (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) ∧ χ (φ Polynomial.X) = c) ∧
            (∀ f : ↥(S), ∃ hR : (f : ↥(fieldBar q M')) ∈ R.integers, ∃ hm : R.residue ⟨(f : ↥(fieldBar q M')), hR⟩ ∈ Q.toValuationSubring,
              IsLocalRing.residue ↥Q.toValuationSubring ⟨R.residue ⟨(f : ↥(fieldBar q M')), hR⟩, hm⟩ =
                algebraMap (ResidueField ↥A) Q.ResidueField (χ₀ f)) ∧
            (∃ hR : ((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')) ∈ R.integers,
              Q.ord (R.residue ⟨((φ Polynomial.X : ↥(S)) : ↥(fieldBar q M')), hR⟩) = 1) ∧
            (∀ P, P ∈ D ↔ (P.IsRational ∧ (∀ f : ↥(S), (f : ↥(fieldBar q M')) ∈ P.toValuationSubring ∧ P.evalAt (f : ↥(fieldBar q M')) ∈ A) ∧
              (∀ f : ↥(S), A.valuation (P.evalAt (f : ↥(fieldBar q M'))) < 1 ↔ χ₀ f = 0))) ∧
            (∀ χ : ↥(S) →+* ↥A, (∀ a : ↥A, χ (φ (Polynomial.C a)) = a) →
              (∀ f : ↥(S), IsLocalRing.residue ↥A (χ f) = χ₀ f) →
              ∃! P, P ∈ D ∧ ∀ f : ↥(S), P.evalAt (f : ↥(fieldBar q M')) = ((χ f : ↥A) : (AlgebraicClosure ℚ))) ∧
            (∀ P ∈ D, ∀ f : ↥(fieldBar q M'), f ∈ P.toValuationSubring ↔
              ∃ g h : ↥(S), P.evalAt (h : ↥(fieldBar q M')) ≠ 0 ∧ f * (h : ↥(fieldBar q M')) = (g : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ≠ 0 → (∀ P ∈ D, P.ord f = 0) →
              ∃ (c : (AlgebraicClosure ℚ)) (u : (↥(S))ˣ), c ≠ 0 ∧ algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M') c * f = ((u : ↥(S)) : ↥(fieldBar q M'))) ∧
            (∀ f : ↥(fieldBar q M'), f ∈ R.integers → (∀ P ∈ D, f ∈ P.toValuationSubring) → f ∈ S)) →
          (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ D ↔ P ∈ Dx Q) ∧
          (∀ f : ↥(fieldBar q M'), f ∈ S ↔ f ∈ Sx Q) ∧
          (∀ (f : ↥(fieldBar q M')) (hf : f ∈ S) (hf' : f ∈ Sx Q), χ₀ ⟨f, hf⟩ = χ₀x Q ⟨f, hf'⟩))) :
        (∀ (g : SemilinearAut (AlgebraicClosure ℚ) ↥(fieldBar q M'))
          (hgA : ∀ x : AlgebraicClosure ℚ, SemilinearAut.baseAut g x ∈ A ↔ x ∈ A)
          (hgR : ∀ f : ↥(fieldBar q M'), g • f ∈ R.integers ↔ f ∈ R.integers)
          (hgj : g • (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) =
            IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
              ↥(modularFunctionFieldBar M')))
          (ψ : ResidueField ↥A ≃+* ResidueField ↥A)
          (hψ : ∀ a : ↥A, ψ (IsLocalRing.residue ↥A a) =
            IsLocalRing.residue ↥A ⟨SemilinearAut.baseAut g (a : AlgebraicClosure ℚ), (hgA (a : AlgebraicClosure ℚ)).mpr a.2⟩)
          (φ : FSS ≃+* FSS)
          (hφ : ∀ (f : ↥(fieldBar q M')) (hf : f ∈ R.integers),
            R.residue ⟨g • f, (hgR f).mpr hf⟩ = φ (R.residue ⟨f, hf⟩)),
          ∀ Q Q' : Place (ResidueField ↥A) FSS, Q ∉ N →
            (∀ y : FSS, y ∈ Q'.toValuationSubring ↔ φ.symm y ∈ Q.toValuationSubring) →
            Q' ∉ N ∧
            ∃ hS : ∀ f : ↥(fieldBar q M'), f ∈ Sx Q ↔ g • f ∈ Sx Q',
              (∀ f : ↥(Sx Q), χ₀x Q' ⟨g • (f : ↥(fieldBar q M')), (hS (f : ↥(fieldBar q M'))).mp f.2⟩ = ψ (χ₀x Q f)) ∧
              (∀ P : Place (AlgebraicClosure ℚ) ↥(fieldBar q M'), P ∈ Dx Q ↔ g • P ∈ Dx Q')) := by
  intro g hgA hgR hgj ψ hψ φ hφ Q Q' hQN hQ'
  have hQpkg : LphiR.Pkg A R Q (Sx Q) (φx Q) (χ₀x Q) (Dx Q) := hpkg Q hQN
  obtain ⟨S', φS', χ₀', D', hS, hχ, hD, hT⟩ :=
    LphiR.Pkg.transport A R g hgA hgR ψ hψ φ hφ Q Q' hQ' (Sx Q) (φx Q) (χ₀x Q) (Dx Q) hQpkg

  have hcuspD' : ∀ P ∈ D', 0 ≤ P.ord (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
      ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M')) := by
    intro P hP
    have hP₀ : g⁻¹ • P ∈ Dx Q := by rw [hD, smul_inv_smul]; exact hP
    have h0 := hcusp Q hQN (g⁻¹ • P) hP₀
    have key := SemilinearAut.ord_smul g (g⁻¹ • P)
      (IntermediateField.inclusion hle (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full M' (jq_mem M'))⟩ :
        ↥(modularFunctionFieldBar M')) : ↥(fieldBar q M'))
    rw [smul_inv_smul, hgj] at key
    rw [key]; exact h0
  have hQ'N : Q' ∉ N := by
    intro hmem
    obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14⟩ := hT
    exact hNpkg Q' hmem S' φS' χ₀' D' ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, hcuspD'⟩
  obtain ⟨hDD, hSS, hχχ⟩ := hUniq Q' hQ'N S' φS' χ₀' D' hT
  have hS' : ∀ f : ↥(fieldBar q M'), f ∈ Sx Q ↔ g • f ∈ Sx Q' := fun f => (hS f).trans (hSS (g • f))
  refine ⟨hQ'N, hS', ?_, ?_⟩
  · intro f
    rw [← hχ f]
    exact (hχχ _ _ _).symm
  · intro P
    exact (hD P).trans (hDD (g • P))

end S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_three_of_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_supersingularProlongation_smoothPointPackage_semilinearTransport_of_cuspFree_of_eq_three_of_dvd (solution)
