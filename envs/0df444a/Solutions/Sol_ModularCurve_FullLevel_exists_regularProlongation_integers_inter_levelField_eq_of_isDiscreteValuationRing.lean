-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_regularProlongation_integers_inter_levelField_eq_of_isDiscreteValuationRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/650920ad-5401-5fdb-b3b3-61c0ce71ecd3

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import Theorems.Thm_ValuationSubring_isIntegral_and_exists_totallyRamified_layers_of_henselian
import Theorems.Thm_ValuationSubring_exists_constantsTower_of_totallyRamified_of_isIntegral
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_regularProlongation_integers_inter_levelField_eq_of_isDiscreteValuationRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

namespace IgLiftSol

section Generic

variable {L : Type*} [Field L] (A : ValuationSubring L) {F : Type*} [Field F] [Algebra L F]
  (W : ValuationSubring F) (hA : ∀ x : L, algebraMap L F x ∈ W ↔ x ∈ A)

def toW : A →+* W where
  toFun a := ⟨algebraMap L F a, (hA a).mpr a.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp)

@[scoped simp] theorem toW_apply (a : A) : ((toW A W hA a : W) : F) = algebraMap L F a := rfl

include hA in
theorem isUnit_of_isUnit_toW (a : A) (h : IsUnit (toW A W hA a)) : IsUnit a := by
  have ha0 : (a : L) ≠ 0 := by
    rintro h0
    have : toW A W hA a = 0 := Subtype.ext (by simp [h0])
    rw [this] at h; exact not_isUnit_zero h
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp h
  have hinv : (algebraMap L F a)⁻¹ ∈ W := by
    have : ((u : W) : F) = (algebraMap L F a)⁻¹ := by
      have h1 : algebraMap L F a * (u : F) = 1 := by
        have := congrArg Subtype.val hu; simpa using this
      exact (eq_inv_of_mul_eq_one_right h1)
    rw [← this]; exact u.2
  rw [← map_inv₀, hA] at hinv
  exact isUnit_iff_exists_inv.mpr ⟨⟨(a : L)⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

scoped instance isLocalHom_toW : IsLocalHom (toW A W hA) := ⟨fun a h => isUnit_of_isUnit_toW A W hA a h⟩

@[reducible] def resAlg : Algebra (ResidueField A) (ResidueField W) :=
  (IsLocalRing.ResidueField.map (toW A W hA)).toAlgebra

theorem resAlg_residue (a : A) :
    letI := resAlg A W hA
    algebraMap (ResidueField A) (ResidueField W) (IsLocalRing.residue A a) =
      IsLocalRing.residue W (toW A W hA a) := by
  letI := resAlg A W hA
  show IsLocalRing.ResidueField.map (toW A W hA) (IsLocalRing.residue A a) = _
  rfl

def regularProlongationOf
    (hsm : ∀ f : F, f ≠ 0 → ∃ c : L, ∃ h : c • f ∈ W, IsUnit (⟨c • f, h⟩ : W)) :
    letI := resAlg A W hA
    RegularProlongation A F (ResidueField W) := by
  letI := resAlg A W hA
  exact
  { integers := W
    residue := IsLocalRing.residue W
    algebraMap_mem_iff := hA
    residue_surjective := IsLocalRing.residue_surjective
    ker_residue := IsLocalRing.ker_residue
    residue_algebraMap := fun a => by
      rw [resAlg_residue]; rfl
    exists_smul_mem := fun f hf => by
      obtain ⟨c, h, hu⟩ := hsm f hf
      exact ⟨c, h, (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hu⟩ }

end Generic

abbrev FB (q M' : ℕ) : Type := ↥(fieldBar q M')

variable (q M' : ℕ) (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ))

scoped instance algK : Algebra ↥k₀ (FB q M') :=
  ((algebraMap (AlgebraicClosure ℚ) (FB q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra

def ιL : AlgebraicClosure ℚ →ₐ[↥k₀] FB q M' :=
  { algebraMap (AlgebraicClosure ℚ) (FB q M') with commutes' := fun _ => rfl }

@[scoped simp] theorem ιL_apply (x : AlgebraicClosure ℚ) : ιL q M' k₀ x = algebraMap (AlgebraicClosure ℚ) (FB q M') x := rfl

def Lbar : IntermediateField ↥k₀ (FB q M') := (ιL q M' k₀).fieldRange

def eL : AlgebraicClosure ℚ ≃ₐ[↥k₀] ↥(Lbar q M' k₀) := AlgEquiv.ofInjectiveField (ιL q M' k₀)

theorem eL_apply (x : AlgebraicClosure ℚ) :
    ((eL q M' k₀ x : ↥(Lbar q M' k₀)) : FB q M') = algebraMap (AlgebraicClosure ℚ) (FB q M') x := rfl

def AL (A : ValuationSubring (AlgebraicClosure ℚ)) : ValuationSubring ↥(Lbar q M' k₀) :=
  A.comap (eL q M' k₀).symm.toAlgHom.toRingHom

theorem mem_AL (A : ValuationSubring (AlgebraicClosure ℚ)) (x : ↥(Lbar q M' k₀)) :
    x ∈ AL q M' k₀ A ↔ (eL q M' k₀).symm x ∈ A := Iff.rfl

theorem eL_mem_AL (A : ValuationSubring (AlgebraicClosure ℚ)) (x : AlgebraicClosure ℚ) :
    eL q M' k₀ x ∈ AL q M' k₀ A ↔ x ∈ A := by
  rw [mem_AL, AlgEquiv.symm_apply_apply]

theorem Lbar_eq_adjoin :
    Lbar q M' k₀ = IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := (AlgHom.mem_fieldRange).mp hx
    exact IntermediateField.subset_adjoin ↥k₀ _ ⟨y, rfl⟩
  · exact IntermediateField.adjoin_le_iff.mpr fun x ⟨y, hy⟩ => (AlgHom.mem_fieldRange).mpr ⟨y, hy⟩

end IgLiftSol
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_regularProlongation_integers_inter_levelField_eq_of_isDiscreteValuationRing.IgLiftSol"

end
p2m_reactivate "P2MW.S_ModularCurve_FullLevel_exists_regularProlongation_integers_inter_levelField_eq_of_isDiscreteValuationRing.IgLiftSol"

open AlgebraicCurve ModularCurve ModularCurve.FullLevel IsLocalRing CongruenceSubgroup
open scoped MatrixGroups

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open IgLiftSol in
theorem solution
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) (π₀ : ↥k₀) (hπ : (π₀ : (AlgebraicClosure ℚ)) ∈ A)
    (hdvr : IsDiscreteValuationRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hunif : maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) =
      Ideal.span {(⟨π₀, hπ⟩ : ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))})
    (hhens : HenselianLocalRing ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))))
    (hres : IsAlgClosed (ResidueField ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)))))
    (hκ : ∀ a : (AlgebraicClosure ℚ), a ∈ A → ∃ c : ↥k₀, (c : (AlgebraicClosure ℚ)) ∈ A ∧ ∃ h : a - c ∈ A, (⟨_, h⟩ : A) ∈ maximalIdeal A) :
    letI : Algebra ↥k₀ ↥(fieldBar q M') :=
      ((algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M')).comp (algebraMap ↥k₀ (AlgebraicClosure ℚ))).toAlgebra
    ∀ (F₀ : IntermediateField ↥k₀ ↥(fieldBar q M')),

      (IntermediateField.adjoin ↥k₀ (Set.range (algebraMap (AlgebraicClosure ℚ) ↥(fieldBar q M'))) ⊔ F₀ = ⊤) →
    ∀ (W : ValuationSubring ↥F₀),

      (∀ x : ↥k₀, (x : (AlgebraicClosure ℚ)) ∈ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W) →
      IsDiscreteValuationRing ↥W →
      (∃ hπW : algebraMap ↥k₀ ↥F₀ π₀ ∈ W, maximalIdeal ↥W = Ideal.span {(⟨_, hπW⟩ : ↥W)}) →
    ∃ (FI : Type) (_ : Field FI) (_ : Algebra (ResidueField A) FI)
      (R : RegularProlongation A (fieldBar q M') FI),

      (∀ f : ↥F₀, ((f : ↥(fieldBar q M')) ∈ R.integers ↔ f ∈ W)) ∧

      (∀ z : FI, ∃ (f : ↥F₀) (hf : (f : ↥(fieldBar q M')) ∈ R.integers), R.residue ⟨(f : ↥(fieldBar q M')), hf⟩ = z) := by
  intro F₀ hK1 W hK2a hK2b hK2c
  classical

  haveI hQalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI halg : Algebra.IsAlgebraic ↥k₀ ↥(Lbar q M' k₀) := by
    haveI : Algebra.IsAlgebraic ↥k₀ (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) ↥k₀
    exact (eL q M' k₀).isAlgebraic
  have hkL : ∀ c : ↥k₀, algebraMap ↥k₀ ↥(Lbar q M' k₀) c = eL q M' k₀ (c : AlgebraicClosure ℚ) := fun c =>
    ((eL q M' k₀).commutes c).symm
  have hcomapEq : A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)) =
      (AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀)) := by
    ext x
    show (x : AlgebraicClosure ℚ) ∈ A ↔ algebraMap ↥k₀ ↥(Lbar q M' k₀) x ∈ AL q M' k₀ A
    rw [hkL, eL_mem_AL]
  obtain ⟨hπ', hunif'⟩ : ∃ hπ' : π₀ ∈ (AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀)),
      maximalIdeal ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀))) = Ideal.span {⟨π₀, hπ'⟩} :=
    hcomapEq ▸ (⟨hπ, hunif⟩ : ∃ hπ' : π₀ ∈ A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ)),
      maximalIdeal ↥(A.comap (algebraMap ↥k₀ (AlgebraicClosure ℚ))) = Ideal.span {⟨π₀, hπ'⟩})
  have hdvr' : IsDiscreteValuationRing ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀))) := hcomapEq ▸ hdvr
  have hhens' : HenselianLocalRing ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀))) := hcomapEq ▸ hhens
  have hres' : IsAlgClosed (ResidueField ↥((AL q M' k₀ A).comap (algebraMap ↥k₀ ↥(Lbar q M' k₀)))) := hcomapEq ▸ hres

  obtain ⟨hint, htower⟩ :=
    @ValuationSubring.isIntegral_and_exists_totallyRamified_layers_of_henselian ↥k₀ (FB q M') _ _ _ _ (Lbar q M' k₀)
      halg (AL q M' k₀ A) π₀ hπ' hdvr' hunif' hhens' hres'

  have hgen : Lbar q M' k₀ ⊔ F₀ = ⊤ := by
    rw [Lbar_eq_adjoin]; exact hK1
  have hagree : ∀ x : ↥k₀, algebraMap ↥k₀ ↥(Lbar q M' k₀) x ∈ AL q M' k₀ A ↔ algebraMap ↥k₀ ↥F₀ x ∈ W := by
    intro x; rw [hkL, eL_mem_AL]; exact hK2a x
  obtain ⟨hπW, hunifW⟩ := hK2c
  obtain ⟨O, hOA, hOF₀, hOres, hOsm⟩ :=
    ValuationSubring.exists_constantsTower_of_totallyRamified_of_isIntegral ↥k₀ (FB q M') (Lbar q M' k₀) F₀ hgen
      (AL q M' k₀ A) W hagree hK2b π₀ hπW hunifW hint htower

  have hOA' : ∀ x : AlgebraicClosure ℚ, algebraMap (AlgebraicClosure ℚ) (fieldBar q M') x ∈ O ↔ x ∈ A := by
    intro x
    rw [← eL_mem_AL q M' k₀ A x, ← hOA]
    rfl
  have hsm' : ∀ f : ↥(fieldBar q M'), f ≠ 0 →
      ∃ c : AlgebraicClosure ℚ, ∃ h : c • f ∈ O, IsUnit (⟨c • f, h⟩ : O) := by
    intro f hf
    obtain ⟨c, hc0, h, hu⟩ := hOsm f hf
    have hc : ((eL q M' k₀).symm c) • f = (c : FB q M') * f := by
      rw [Algebra.smul_def]
      congr 1
      have := eL_apply q M' k₀ ((eL q M' k₀).symm c)
      rw [AlgEquiv.apply_symm_apply] at this
      exact this.symm
    refine ⟨(eL q M' k₀).symm c, ?_, ?_⟩
    · rw [hc]; exact h
    · convert hu using 2

  letI instRes := IgLiftSol.resAlg A O hOA'
  refine ⟨ResidueField ↥O, inferInstance, instRes, IgLiftSol.regularProlongationOf A O hOA' hsm', fun f => hOF₀ f, ?_⟩
  intro z
  obtain ⟨w, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨f, hfO, hdiff⟩ := hOres w
  refine ⟨(f : ↥F₀), hfO, ?_⟩
  show IsLocalRing.residue ↥O ⟨_, hfO⟩ = IsLocalRing.residue ↥O w
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
  exact neg_mem hdiff

end S_ModularCurve_FullLevel_exists_regularProlongation_integers_inter_levelField_eq_of_isDiscreteValuationRing
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_regularProlongation_integers_inter_levelField_eq_of_isDiscreteValuationRing (solution)
