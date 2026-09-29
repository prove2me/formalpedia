-- Prove2me | solution 1 for ModularCurve.nonempty_jZeroNeronPrimaryTorsionFFModels
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/c66f96d0-d9f7-50ca-8c37-750dd8f2db82

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_HopfAlgebra_isCocomm_of_isReduced_baseChange_of_withConv_equiv
import Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero
import Theorems.Thm_AlgHom_liftEquiv_symm_withConv_mul
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open GaloisRep
open scoped TensorProduct

namespace ModularCurve
p2m_export "ModularCurve" "eisensteinPrimaryTorsionBar JZeroNeronPrimaryTorsionCore JZeroNeronPrimaryTorsionFFModels JZero"
p2m_open "ModularCurve"
namespace JZeroNeronPrimaryTorsionFFModelsAssembly

variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    (C : JZeroNeronPrimaryTorsionCore p q A hA)

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "Rloc" => GaloisRep.ratLocalizedAt

scoped instance (priority := 10000) instAlgebraH (m : ℕ) : Algebra ℤ (C.H m) :=
  (C.instHopfAlgebra_H m).toAlgebra

scoped instance (priority := 10000) instModuleH (m : ℕ) : Module ℤ (C.H m) :=
  (instAlgebraH C m).toModule

def FiniteBaseChange (R : Type) [CommRing R] (M : Type) [AddCommGroup M] (i : Module ℤ M) : Prop :=
  by letI : Module ℤ M := i; exact Module.Finite R (R ⊗[ℤ] M)

omit [Fact p.Prime] [Fact q.Prime] in
lemma finiteBaseChange_iff (R : Type) [CommRing R] (M : Type) [AddCommGroup M]
    (i₁ i₂ : Module ℤ M) : FiniteBaseChange R M i₁ ↔ FiniteBaseChange R M i₂ := by
  rw [Subsingleton.elim i₁ i₂]

def FlatInt (M : Type) [AddCommGroup M] (i : Module ℤ M) : Prop :=
  by letI : Module ℤ M := i; exact Module.Flat ℤ M

omit [Fact p.Prime] [Fact q.Prime] in
lemma flatInt_iff (M : Type) [AddCommGroup M] (i₁ i₂ : Module ℤ M) :
    FlatInt M i₁ ↔ FlatInt M i₂ := by
  rw [Subsingleton.elim i₁ i₂]

scoped instance instFlatH (m : ℕ) : Module.Flat ℤ (C.H m) := by
  have h : FlatInt (C.H m) _ := C.instFlat_H m
  exact (flatInt_iff (C.H m) _ (instModuleH C m)).mp h

abbrev Hff (m ℓ : ℕ) : Type := ↥(Rloc ℓ) ⊗[ℤ] C.H m

scoped instance (priority := 10000) instModuleIntQbar : Module ℤ ℚbar := Algebra.toModule

scoped instance instIsScalarTowerIntRlocQbar (ℓ : ℕ) :
    @IsScalarTower ℤ ↥(Rloc ℓ) ℚbar Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

scoped instance instIsScalarTowerIntQbarQbar :
    @IsScalarTower ℤ ℚbar ℚbar Algebra.toSMul Algebra.toSMul Algebra.toSMul := IsScalarTower.right

example (m : ℕ) : CommRing (ℚbar ⊗[ℤ] C.H m) := inferInstance
example (m : ℕ) : HopfAlgebra ℚbar (ℚbar ⊗[ℤ] C.H m) := inferInstance

theorem finite_Hff (m ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) :
    Module.Finite ↥(Rloc ℓ) (Hff C m ℓ) := by
  have h : FiniteBaseChange ↥(Rloc ℓ) (C.H m) _ := C.ff_finite m ℓ hℓ hℓp
  exact (finiteBaseChange_iff ↥(Rloc ℓ) (C.H m) _ (instModuleH C m)).mp h

example (m ℓ : ℕ) : CommRing (Hff C m ℓ) := inferInstance
example (m ℓ : ℕ) : HopfAlgebra ↥(Rloc ℓ) (Hff C m ℓ) := inferInstance
example (m ℓ : ℕ) : Module.Flat ↥(Rloc ℓ) (Hff C m ℓ) := inferInstance

omit [Fact p.Prime] in

lemma exists_prime_ne (p : ℕ) : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ p := by
  by_cases h : p = 2
  · exact ⟨3, Nat.prime_three, by omega⟩
  · exact ⟨2, Nat.prime_two, fun h' => h h'.symm⟩

scoped instance instFiniteQbar (m : ℕ) : Module.Finite ℚbar (ℚbar ⊗[ℤ] C.H m) := by
  obtain ⟨ℓ, hℓ, hℓp⟩ := exists_prime_ne p
  haveI : Module.Finite ↥(Rloc ℓ) (Hff C m ℓ) := finite_Hff C m ℓ hℓ hℓp
  exact Module.Finite.equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange ℤ ↥(Rloc ℓ) ℚbar ℚbar (C.H m))

scoped instance instIsReducedQbar (m : ℕ) : IsReduced (ℚbar ⊗[ℤ] C.H m) :=
  HopfAlgebra.isReduced_of_finiteType_of_charZero ℚbar (ℚbar ⊗[ℤ] C.H m)

scoped instance instIsCocommH (m : ℕ) : Coalgebra.IsCocomm ℤ (C.H m) :=
  HopfAlgebra.isCocomm_of_isReduced_baseChange_of_withConv_equiv ℤ ℚbar
    (algebraMap ℤ ℚbar).injective_int (C.H m) (C.genericPoints m) (C.genericConv m)

example (m ℓ : ℕ) : Coalgebra.IsCocomm ↥(Rloc ℓ) (Hff C m ℓ) := inferInstance

def ιW (m ℓ : ℕ) :
    WithConv (Hff C m ℓ →ₐ[↥(Rloc ℓ)] ℚbar) ≃ WithConv (C.H m →ₐ[ℤ] ℚbar) where
  toFun f := WithConv.toConv ((AlgHom.liftEquiv ℤ ↥(Rloc ℓ) (C.H m) ℚbar).symm f.ofConv)
  invFun g := WithConv.toConv ((AlgHom.liftEquiv ℤ ↥(Rloc ℓ) (C.H m) ℚbar) g.ofConv)
  left_inv f := by
    simp only [WithConv.ofConv_toConv, Equiv.apply_symm_apply, WithConv.toConv_ofConv]
  right_inv g := by
    simp only [WithConv.ofConv_toConv, Equiv.symm_apply_apply, WithConv.toConv_ofConv]

lemma ιW_apply (m ℓ : ℕ) (f : WithConv (Hff C m ℓ →ₐ[↥(Rloc ℓ)] ℚbar)) (h : C.H m) :
    (ιW C m ℓ f).ofConv h = f.ofConv (1 ⊗ₜ[ℤ] h) := rfl

lemma ιW_mul (m ℓ : ℕ) (f g : WithConv (Hff C m ℓ →ₐ[↥(Rloc ℓ)] ℚbar)) :
    ιW C m ℓ (f * g) = ιW C m ℓ f * ιW C m ℓ g :=
  AlgHom.liftEquiv_symm_withConv_mul ℤ ↥(Rloc ℓ) (C.H m) ℚbar f g

def ffPoints (m ℓ : ℕ) :
    WithConv (Hff C m ℓ →ₐ[↥(Rloc ℓ)] ℚbar) ≃ ↥(eisensteinPrimaryTorsionBar p q m) :=
  (ιW C m ℓ).trans (C.genericPoints m)

lemma ffPoints_mul (m ℓ : ℕ) (f g : WithConv (Hff C m ℓ →ₐ[↥(Rloc ℓ)] ℚbar)) :
    ffPoints C m ℓ (f * g) = ffPoints C m ℓ f + ffPoints C m ℓ g := by
  simp only [ffPoints, Equiv.trans_apply, ιW_mul]
  exact C.genericConv m _ _

lemma ffPoints_galois (m ℓ : ℕ) (σ : ℚbar ≃ₐ[ℚ] ℚbar)
    (f g : WithConv (Hff C m ℓ →ₐ[↥(Rloc ℓ)] ℚbar)) (hfg : ∀ h, g h = σ (f h)) :
    ((ffPoints C m ℓ g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = σ • ((ffPoints C m ℓ f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p) := by
  simp only [ffPoints, Equiv.trans_apply]
  apply C.genericGalois m σ
  intro h
  show (ιW C m ℓ g).ofConv h = σ ((ιW C m ℓ f).ofConv h)
  rw [ιW_apply, ιW_apply]
  exact hfg (1 ⊗ₜ[ℤ] h)

abbrev HffBarQ (m : ℕ) : Type := ZMod q ⊗[↥(Rloc q)] Hff C m q

example (m : ℕ) : CommRing (HffBarQ (q := q) C m) := inferInstance
example (m : ℕ) : HopfAlgebra (ZMod q) (HffBarQ (q := q) C m) := inferInstance
example (m : ℕ) : Coalgebra.IsCocomm (ZMod q) (HffBarQ (q := q) C m) := inferInstance

def red (m : ℕ) : Hff C m q →+* HffBarQ (q := q) C m :=
  (Algebra.TensorProduct.includeRight : Hff C m q →ₐ[↥(Rloc q)] HffBarQ (q := q) C m).toRingHom

lemma red_apply (m : ℕ) (x : Hff C m q) : red (q := q) C m x = (1 : ZMod q) ⊗ₜ x := rfl

omit [Fact p.Prime] in
lemma residue_surjective : Function.Surjective (algebraMap ↥(Rloc q) (ZMod q)) := by
  intro x
  obtain ⟨n, rfl⟩ := ZMod.intCast_surjective x
  exact ⟨n, by simp⟩

omit [Fact p.Prime] in

lemma ker_residue :
    RingHom.ker (algebraMap ↥(Rloc q) (ZMod q)) = Ideal.span {((q : ℤ) : ↥(Rloc q))} := by
  haveI hloc : IsLocalization.AtPrime ↥(Rloc q) (Ideal.span {(q : ℤ)}) :=
    GaloisRep.isLocalization_ratLocalizedAt (p := q) Fact.out
  apply le_antisymm
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Ideal.span {(q : ℤ)}).primeCompl x
    dsimp only at hx ⊢
    have ha : (Int.castRingHom (ZMod q)) a = 0 := by
      have h2 := congrArg (algebraMap ↥(Rloc q) (ZMod q)) (IsLocalization.mk'_spec ↥(Rloc q) a s)
      rw [map_mul, hx, zero_mul, ← RingHom.comp_apply,
        show (algebraMap ↥(Rloc q) (ZMod q)).comp (algebraMap ℤ ↥(Rloc q)) = Int.castRingHom (ZMod q)
          from Subsingleton.elim _ _] at h2
      exact h2.symm
    rw [Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [← IsLocalization.mul_mk'_eq_mk'_of_mul, eq_intCast]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_intCast]
    exact_mod_cast ZMod.natCast_self q

lemma red_surjective (m : ℕ) : Function.Surjective (red (q := q) C m) := by
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a y =>
    obtain ⟨r, rfl⟩ := residue_surjective (q := q) a
    refine ⟨r • y, ?_⟩
    rw [red_apply, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx; obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

lemma ker_red (m : ℕ) :
    (RingHom.ker (red (q := q) C m) : Ideal (Hff C m q)) = Ideal.span {((q : ℤ) : Hff C m q)} := by
  apply le_antisymm
  ·
    let π : ↥(Rloc q) →ₐ[↥(Rloc q)] ZMod q := Algebra.ofId ↥(Rloc q) (ZMod q)
    have hπ : Function.Surjective π := residue_surjective (q := q)
    let e : Hff C m q ≃ₐ[↥(Rloc q)] ↥(Rloc q) ⊗[↥(Rloc q)] Hff C m q := (Algebra.TensorProduct.lid ↥(Rloc q) (Hff C m q)).symm
    have hex : ∀ x, e x = 1 ⊗ₜ[↥(Rloc q)] x := fun x => by
      apply e.symm.injective
      rw [e.symm_apply_apply]
      simp [e, Algebra.TensorProduct.lid_tmul]
    have hfac : ∀ x, red (q := q) C m x
        = Algebra.TensorProduct.map π (AlgHom.id ↥(Rloc q) (Hff C m q)) (e x) := fun x => by
      rw [hex, Algebra.TensorProduct.map_tmul, map_one]; rfl
    intro x hx
    rw [RingHom.mem_ker, hfac] at hx
    have hx' : e x ∈ RingHom.ker (Algebra.TensorProduct.map π (AlgHom.id ↥(Rloc q) (Hff C m q))) := hx
    rw [Algebra.TensorProduct.rTensor_ker π hπ,
      show RingHom.ker π = Ideal.span {((q : ℤ) : ↥(Rloc q))} from ker_residue (q := q),
      Ideal.map_span, Set.image_singleton] at hx'
    have hx'' := Ideal.mem_map_of_mem (e.symm : ↥(Rloc q) ⊗[↥(Rloc q)] Hff C m q →ₐ[↥(Rloc q)] Hff C m q) hx'
    rw [Ideal.map_span, Set.image_singleton] at hx''
    have h1 : (e.symm : ↥(Rloc q) ⊗[↥(Rloc q)] Hff C m q →ₐ[↥(Rloc q)] Hff C m q) (e x) = x := e.symm_apply_apply x
    have h2 : (e.symm : ↥(Rloc q) ⊗[↥(Rloc q)] Hff C m q →ₐ[↥(Rloc q)] Hff C m q)
        (Algebra.TensorProduct.includeLeft (S := ↥(Rloc q)) ((q : ℤ) : ↥(Rloc q))) = ((q : ℤ) : Hff C m q) := by
      simp [e, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.lid_tmul, Algebra.smul_def]
    rw [h1, h2] at hx''
    exact hx''
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_intCast]
    have h : algebraMap (ZMod q) (HffBarQ (q := q) C m) (q : ZMod q) = (q : HffBarQ (q := q) C m) :=
      map_natCast (algebraMap (ZMod q) (HffBarQ (q := q) C m)) q
    rw [ZMod.natCast_self, map_zero] at h
    exact_mod_cast h.symm

def models : JZeroNeronPrimaryTorsionFFModels p q A hA C where
  Hff m ℓ _ _ := Hff C m ℓ
  instCommRing_Hff m ℓ _ _ := inferInstance
  instHopfAlgebra_Hff m ℓ _ _ := inferInstance
  instFinite_Hff m ℓ hℓ hℓp := finite_Hff C m ℓ hℓ hℓp
  instFlat_Hff m ℓ _ _ := inferInstance
  instCocomm_Hff m ℓ _ _ := inferInstance
  ffPoints m ℓ _ _ := ffPoints C m ℓ
  ffConv m ℓ _ _ f g := ffPoints_mul C m ℓ f g
  ffGalois m ℓ _ _ σ f g hfg := ffPoints_galois C m ℓ σ f g hfg
  HffBarQ m _ := HffBarQ (q := q) C m
  instCommRing_HffBarQ m _ := inferInstance
  instHopfAlgebra_HffBarQ m _ := inferInstance
  instFinite_HffBarQ m hqp := by
    haveI : Module.Finite ↥(Rloc q) (Hff C m q) := finite_Hff C m q Fact.out hqp
    infer_instance
  instCocomm_HffBarQ m _ := inferInstance
  ffBarQ_red m _ := red (q := q) C m
  ffBarQ_red_surjective m _ := red_surjective (q := q) C m
  ffBarQ_red_ker m _ := ker_red (q := q) C m

end JZeroNeronPrimaryTorsionFFModelsAssembly
p2m_reactivate "P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.ModularCurve.JZeroNeronPrimaryTorsionFFModelsAssembly"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.ModularCurve.JZeroNeronPrimaryTorsionFFModelsAssembly P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.ModularCurve.JZeroNeronPrimaryTorsionFFModelsAssembly P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels.ModularCurve in
theorem solution (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) :
    Nonempty (JZeroNeronPrimaryTorsionFFModels p q A hA C) :=
  ⟨JZeroNeronPrimaryTorsionFFModelsAssembly.models C⟩

end S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels
end P2MW
export P2MW.S_ModularCurve_nonempty_jZeroNeronPrimaryTorsionFFModels (solution)
