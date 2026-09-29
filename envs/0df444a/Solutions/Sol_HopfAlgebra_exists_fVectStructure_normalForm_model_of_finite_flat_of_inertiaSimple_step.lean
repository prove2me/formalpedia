-- Prove2me | solution 1 for HopfAlgebra.exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/c0493876-73c9-595a-a685-4f200721703c

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_TameCharacter
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_FVectStructure
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_HopfAlgebra_exists_field_lineAction_of_finite_flat_of_inertiaSimple_step
import Theorems.Thm_ValuationSubring_exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow
import Theorems.Thm_HopfAlgebra_exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step
import Theorems.Thm_HopfAlgebra_exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
import Theorems.Thm_HopfAlgebra_exists_fVectStructure_isFCompatible_of_bialgEquiv
import Theorems.Thm_HopfAlgebra_exists_fVectStructure_baseChange_eq_of_pow_eq_one
import Theorems.Thm_HopfAlgebra_FVect_exists_generators_normalForm_of_finrank_eq_card
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul closureCounit_apply genericFibreAlgHom_tmul tensorInclusion_closureComul coe_closureAntipode_apply tensorToGenericFibre_tmul tensorInclusion_tmul"

set_option autoImplicit false
open scoped TensorProduct

theorem solution
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {H : Type} [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H] [Module.Flat (GaloisRep.ratLocalizedAt p) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H]
    (hMp : ∀ f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ), f ^ p = 1)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (K K' : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)))
    (hKK' : K ≤ K')
    (hK : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K,
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K))
    (hK' : (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
      ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        (∀ h : H, g h = σ (f h)) → g ∈ K'))
    (hstep : ∀ S : Submonoid (WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      K ≤ S → S ≤ K' →
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ S,
        ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
          (∀ h : H, g h = σ (f h)) → g ∈ S) →
      S = K ∨ S = K')
    (s : ℕ) [NeZero s] (hcard : Nat.card K' = p ^ s * Nat.card K) :
    ∃ (R' : Type) (_ : CommRing R') (_ : Algebra R' ↥P)
        (F : Type) (_ : Field F) (_ : Fintype F)
        (B : Type) (_ : CommRing B) (_ : HopfAlgebra R' B)
        (fv : HopfAlgebra.FVectStructure F R' B)
        (χ : Fˣ →* R'ˣ) (ι₀ : F →+* IsLocalRing.ResidueField ↥P)
        (X : Fin s → B) (δ : Fin s → R')
        (q : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) → (B →ₐ[R'] ↥P)),
        Irreducible (p : R') ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : R',
          σ ((algebraMap R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap R' ↥P r : ↥P)) ∧
        Fintype.card F = p ^ s ∧
        (∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap R' ↥P ((χ l : R'ˣ) : R')) = ι₀ l) ∧
        (∀ (i : Fin s) (l : Fˣ), fv.act l (X i) = (((χ ^ (p ^ (i : ℕ))) l : R'ˣ) : R') • X i) ∧
        (∀ i, X i ^ p = δ i • X (i + 1)) ∧
        (∀ i, δ i ∣ (p : R')) ∧
        (∀ i, Coalgebra.counit (R := R') (X i) = 0) ∧
        Algebra.adjoin R' (Set.range X) = ⊤ ∧
        Nat.card (B →ₐ[R'] ↥P) = p ^ s ∧
        (∀ f ∈ K', ∀ g ∈ K',
          WithConv.toConv (q (f * g)) = WithConv.toConv (q f) * WithConv.toConv (q g)) ∧
        (∀ f ∈ K', (WithConv.toConv (q f) = 1 ↔ f ∈ K)) ∧
        (∀ b : B →ₐ[R'] ↥P, ∃ f ∈ K', q f = b) ∧
        (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ f ∈ K',
          ∀ g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
            (∀ h : H, g h = σ (f h)) → ∀ x : B,
              ((q g x : ↥P) : AlgebraicClosure ℚ) = σ ((q f x : ↥P) : AlgebraicClosure ℚ)) := by
  classical
  haveI hpF : Fact p.Prime := ⟨hp⟩

  let D : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) := P.inertiaSubgroupIn ℚ
  let F' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField D
  let R' : ValuationSubring ↥F' := P.comap (algebraMap ↥F' (AlgebraicClosure ℚ))
  obtain ⟨hDVR, hirr, hCZ, hIFR⟩ :=
    ValuationSubring.isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn P p hP
  haveI : IsDiscreteValuationRing ↥R' := hDVR
  haveI : CharZero ↥R' := hCZ
  let iP : ↥R' →+* ↥P :=
    { toFun := fun x => ⟨((x : ↥F') : AlgebraicClosure ℚ), x.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hiP : ∀ x : ↥R', ((iP x : ↥P) : AlgebraicClosure ℚ) = ((x : ↥F') : AlgebraicClosure ℚ) :=
    fun _ => rfl
  have hinj : Function.Injective iP := by
    intro x y h
    have h' := congrArg (fun z : ↥P => (z : AlgebraicClosure ℚ)) h
    simp only [hiP] at h'
    exact Subtype.ext (Subtype.ext h')
  letI algRP : Algebra ↥R' ↥P := iP.toAlgebra
  have hfix : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ r : ↥R',
      σ ((algebraMap ↥R' ↥P r : ↥P) : AlgebraicClosure ℚ) = (algebraMap ↥R' ↥P r : ↥P) := by
    intro σ hσ r
    show σ ((iP r : ↥P) : AlgebraicClosure ℚ) = ((iP r : ↥P) : AlgebraicClosure ℚ)
    rw [hiP]
    exact (IntermediateField.mem_fixedField_iff _ _).mp (r : ↥F').2 σ hσ
  have hunif : Irreducible ((p : ℕ) : ↥R') := hirr

  obtain ⟨F, _iF, _iFt, lact, hF, hla1, hla2, hla3, hla4, hla5, hla6, hla7, hla8, hla9⟩ :=
    HopfAlgebra.exists_field_lineAction_of_finite_flat_of_inertiaSimple_step hp hp2 hMp P hP K K' hKK'
      hK hK' hstep s hcard

  obtain ⟨χ, ι₀, hχ0⟩ :=
    ValuationSubring.exists_units_monoidHom_residue_eq_of_injective_of_card_eq_prime_pow p P hP iP hinj
      (fun y hy hyfix => by
        obtain ⟨x, hx⟩ := hIFR y hy hyfix
        exact ⟨x, by rw [hiP, hx]⟩)
      F s hF
  have hχ : ∀ l : Fˣ, IsLocalRing.residue ↥P (algebraMap ↥R' ↥P ((χ l : (↥R')ˣ) : ↥R')) = ι₀ l :=
    hχ0

  haveI : IsDiscreteValuationRing ↥R' := hDVR
  obtain ⟨B, _iB, _iHB, _iFinB, _iFreeB, _iCocommB, hrank, hBkill, A₁, _iA1, _iHA1, _iFinA1, _iCocA1, _iFinPts,
      e, r, q, hev₁, hrmul, hrker, hrone, hrsurj, hrequiv, hcardV, hqmul, hqker, hqsurj, hqequiv, hcompat⟩ :=
    HopfAlgebra.exists_model_points_genericFibre_of_finite_flat_of_inertiaStable_step hp hMp P K K' hKK'
      hK hK' s hcard hiP hDVR hirr

  obtain ⟨act₁, hact₁, hadd₁, hzero₁, hmul₁, hone₁, hcomp₁⟩ :
      ∃ act₁ : F → (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) →* WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)),
        (∀ a : F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ P.inertiaSubgroupIn ℚ →
          ∀ ν ν' : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ),
            (∀ x : A₁, WithConv.ofConv ν' x = σ (WithConv.ofConv ν x)) →
            ∀ x : A₁, WithConv.ofConv (act₁ a ν') x = σ (WithConv.ofConv (act₁ a ν) x)) ∧
        (∀ (a b : F) (ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)), act₁ (a + b) ν = act₁ a ν * act₁ b ν) ∧
        (∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), act₁ 0 ν = 1) ∧
        (∀ (a b : F) (ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)), act₁ (a * b) ν = act₁ a (act₁ b ν)) ∧
        (∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), act₁ 1 ν = ν) ∧
        (∀ a : F, ∀ f ∈ K', act₁ a (r f) = r (lact a f)) := by

    have hsec := fun ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) => hrsurj ν
    choose sec hsecK' hsecr using hsec
    have hrK : ∀ k ∈ K, r k = 1 := fun k hk => (hrone k (hKK' hk)).mpr hk

    have hunit : ∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), IsUnit ν := by
      intro ν
      obtain ⟨f, hf, rfl⟩ := hrsurj ν
      refine IsUnit.of_mul_eq_one (r (f ^ (p - 1))) ?_
      rw [← hrmul f hf _ (pow_mem hf _), ← pow_succ', Nat.sub_add_cancel hp.one_le, hMp,
        hrK 1 K.one_mem]

    have hW : ∀ (a : F) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (hf : f ∈ K') (g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (hg : g ∈ K'),
        r f = r g → r (lact a f) = r (lact a g) := by
      intro a f hf g hg hfg
      obtain ⟨k, hk, rfl⟩ := (hrker f hf g hg).mp hfg
      obtain ⟨k', hk', hk'eq⟩ := hla2 a f hf k hk
      rw [hk'eq, hrmul _ (hla1 a f hf) _ (hKK' hk'), hrK k' hk', mul_one]
    let act₀ : F → WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) → WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) := fun a ν => r (lact a (sec ν))
    have hact₀ : ∀ (a : F) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (hf : f ∈ K'), act₀ a (r f) = r (lact a f) :=
      fun a f hf => hW a _ (hsecK' _) f hf (hsecr _)
    have hact₀_mul : ∀ (a : F) (ν ν' : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)), act₀ a (ν * ν') = act₀ a ν * act₀ a ν' := by
      intro a ν ν'
      obtain ⟨f, hf, rfl⟩ := hrsurj ν
      obtain ⟨g, hg, rfl⟩ := hrsurj ν'
      rw [← hrmul f hf g hg, hact₀ a _ (K'.mul_mem hf hg), hact₀ a f hf, hact₀ a g hg]
      obtain ⟨k, hk, hkeq⟩ := hla3 a f hf g hg
      rw [hkeq, hrmul _ (K'.mul_mem (hla1 a f hf) (hla1 a g hg)) _ (hKK' hk),
        hrmul _ (hla1 a f hf) _ (hla1 a g hg), hrK k hk, mul_one]
    have hcancel : ∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), ν = ν * ν → ν = 1 := by
      intro ν h
      have h' : ν * ν = ν * 1 := by rw [mul_one]; exact h.symm
      exact (hunit ν).mul_left_cancel h'
    have hact₀_one : ∀ a : F, act₀ a 1 = 1 := fun a =>
      hcancel _ (by have h := hact₀_mul a 1 1; rwa [one_mul] at h)
    let act₁ : F → (WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ) →* WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)) := fun a =>
      { toFun := act₀ a, map_one' := hact₀_one a, map_mul' := hact₀_mul a }
    have hact₁r : ∀ (a : F) (f : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)) (hf : f ∈ K'), act₁ a (r f) = r (lact a f) := hact₀
    have hadd₁ : ∀ (a b : F) (ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)), act₁ (a + b) ν = act₁ a ν * act₁ b ν := by
      intro a b ν
      obtain ⟨f, hf, rfl⟩ := hrsurj ν
      rw [hact₁r _ f hf, hact₁r _ f hf, hact₁r _ f hf]
      obtain ⟨k, hk, hkeq⟩ := hla4 a b f hf
      rw [hkeq, hrmul _ (K'.mul_mem (hla1 a f hf) (hla1 b f hf)) _ (hKK' hk),
        hrmul _ (hla1 a f hf) _ (hla1 b f hf), hrK k hk, mul_one]
    have hzero₁ : ∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), act₁ 0 ν = 1 := fun ν =>
      hcancel _ (by have h := hadd₁ 0 0 ν; rwa [add_zero] at h)
    have hmul₁ : ∀ (a b : F) (ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ)), act₁ (a * b) ν = act₁ a (act₁ b ν) := by
      intro a b ν
      obtain ⟨f, hf, rfl⟩ := hrsurj ν
      rw [hact₁r _ f hf, hact₁r _ f hf, hact₁r _ _ (hla1 b f hf)]
      obtain ⟨k, hk, hkeq⟩ := hla5 a b f hf
      rw [hkeq, hrmul _ (hla1 a _ (hla1 b f hf)) _ (hKK' hk), hrK k hk, mul_one]
    have hone₁ : ∀ ν : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ), act₁ 1 ν = ν := by
      intro ν
      obtain ⟨f, hf, rfl⟩ := hrsurj ν
      rw [hact₁r _ f hf]
      obtain ⟨k, hk, hkeq⟩ := hla6 f hf
      rw [hkeq, hrmul f hf _ (hKK' hk), hrK k hk, mul_one]
    have hact₁eq : ∀ a : F, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ P.inertiaSubgroupIn ℚ →
        ∀ ν ν' : WithConv (A₁ →ₐ[↥(IntermediateField.fixedField (P.inertiaSubgroupIn ℚ))] AlgebraicClosure ℚ),
          (∀ x : A₁, WithConv.ofConv ν' x = σ (WithConv.ofConv ν x)) →
          ∀ x : A₁, WithConv.ofConv (act₁ a ν') x = σ (WithConv.ofConv (act₁ a ν) x) := by
      intro a σ hσ ν ν' hνν'
      obtain ⟨f, hf, rfl⟩ := hrsurj ν

      let g : WithConv (H →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) := WithConv.toConv
        ((((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ).restrictScalars
          (GaloisRep.ratLocalizedAt p)).comp (WithConv.ofConv f))
      have hg : ∀ h : H, g h = σ (f h) := fun _ => rfl
      have hgK' : g ∈ K' := hK' σ hσ f hf g hg
      have hν' : ν' = r g := by
        apply WithConv.ofConv_injective
        apply AlgHom.ext
        intro x
        rw [hνν' x]
        exact (hrequiv σ hσ f hf g hg x).symm
      rw [hν', hact₁r a g hgK', hact₁r a f hf]
      obtain ⟨k, hk, hkeq⟩ := hla7 σ hσ a f hf g hg
      have hg₂K' : lact a g * k ∈ K' := K'.mul_mem (hla1 a g hgK') (hKK' hk)
      have hr₂ : r (lact a g * k) = r (lact a g) := by
        rw [hrmul _ (hla1 a g hgK') _ (hKK' hk), hrK k hk, mul_one]
      intro x
      rw [← hr₂]
      exact hrequiv σ hσ (lact a f) (hla1 a f hf) (lact a g * k) hkeq x
    exact ⟨act₁, hact₁eq, hadd₁, hzero₁, hmul₁, hone₁, fun a f hf => hact₁r a f hf⟩
  obtain ⟨fv₁, hfv₁⟩ :=
    HopfAlgebra.exists_fVectStructure_forall_comp_eq_of_equivariant_of_bijective_evalPoints
      (P.inertiaSubgroupIn ℚ) A₁ hev₁ F act₁ hact₁ hadd₁ hzero₁ hmul₁ hone₁
  obtain ⟨fvK, hfvK, -⟩ := HopfAlgebra.exists_fVectStructure_isFCompatible_of_bialgEquiv fv₁ e

  haveI : Module.Flat ↥R' B := Module.Flat.of_free
  obtain ⟨fv, hfv⟩ :=
    HopfAlgebra.exists_fVectStructure_baseChange_eq_of_pow_eq_one (R := ↥R') ↥F' p hp2 hunif (B := B) 1
      hBkill fvK

  have hpm : (p : ↥R') ∈ IsLocalRing.maximalIdeal ↥R' := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact hunif.not_isUnit
  have hq : IsUnit ((p ^ s : ↥R') - 1) := by
    have h1 : IsUnit (1 - (p : ↥R') ^ s) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
        (Ideal.pow_mem_of_mem _ hpm s (NeZero.pos s))
    rw [show ((p ^ s : ↥R') - 1) = -(1 - (p : ↥R') ^ s) by push_cast; ring]
    exact h1.neg

  have hloc : ∀ x : ↥R', IsUnit (iP x) → IsUnit x := by
    intro x hx
    have hx' : IsUnit ((iP x : ↥P) : AlgebraicClosure ℚ) := hx.map P.subtype
    have hne : ((x : ↥F') : AlgebraicClosure ℚ) ≠ 0 := by rw [← hiP]; exact hx'.ne_zero
    have hxne : (x : ↥F') ≠ 0 := fun h => hne (by rw [h]; rfl)

    have hinvP : ((x : ↥F') : AlgebraicClosure ℚ)⁻¹ ∈ P := by
      obtain ⟨u, hu⟩ := hx
      have h1 := congrArg P.subtype u.mul_inv
      rw [map_mul, map_one, hu] at h1
      rw [show ((x : ↥F') : AlgebraicClosure ℚ) = P.subtype (iP x) from rfl, inv_eq_of_mul_eq_one_right h1]
      exact Subtype.mem _
    have hinvR : (x : ↥F')⁻¹ ∈ R' := by
      show algebraMap (↥F') (AlgebraicClosure ℚ) ((x : ↥F')⁻¹) ∈ P
      rw [map_inv₀]; exact hinvP
    exact ⟨⟨x, ⟨(x : ↥F')⁻¹, hinvR⟩, Subtype.ext (mul_inv_cancel₀ hxne), Subtype.ext (inv_mul_cancel₀ hxne)⟩, rfl⟩
  have hker : ∀ x ∈ IsLocalRing.maximalIdeal ↥R', IsLocalRing.residue ↥P (iP x) = 0 := by
    intro x hx
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu => (IsLocalRing.mem_maximalIdeal _ |>.mp hx) (hloc x hu)
  let resmap : IsLocalRing.ResidueField ↥R' →+* IsLocalRing.ResidueField ↥P :=
    Ideal.Quotient.lift _ ((IsLocalRing.residue ↥P).comp iP) (fun x hx => hker x hx)
  have hresmap : ∀ x : ↥R', resmap (IsLocalRing.residue ↥R' x) = IsLocalRing.residue ↥P (iP x) :=
    fun _ => rfl
  have hresinj : Function.Injective resmap := resmap.injective

  let ιfun : F → IsLocalRing.ResidueField ↥R' := fun l =>
    if h : l = 0 then 0 else IsLocalRing.residue ↥R' (χ (Units.mk0 l h) : ↥R')
  have hιfun : ∀ l : F, resmap (ιfun l) = ι₀ l := by
    intro l
    by_cases h : l = 0
    · simp [ιfun, h]
    · simp only [ιfun, dif_neg h, hresmap]
      have := hχ0 (Units.mk0 l h)
      simpa using this
  let ι : F →+* IsLocalRing.ResidueField ↥R' :=
    { toFun := ιfun
      map_one' := hresinj (by rw [hιfun, map_one, map_one])
      map_mul' := fun a b => hresinj (by rw [hιfun, map_mul, map_mul, hιfun, hιfun])
      map_zero' := hresinj (by rw [hιfun, map_zero, map_zero])
      map_add' := fun a b => hresinj (by rw [hιfun, map_add, map_add, hιfun, hιfun]) }
  have hχ' : ∀ l : Fˣ, IsLocalRing.residue ↥R' (χ l : ↥R') = ι l := by
    intro l
    show IsLocalRing.residue ↥R' (χ l : ↥R') = ιfun l
    simp only [ιfun, dif_neg l.ne_zero, Units.mk0_val]
  obtain ⟨X, δ, h1, h2, h4, h5, hgen⟩ :=
    HopfAlgebra.FVect.exists_generators_normalForm_of_finrank_eq_card ↥R' p s F hF hq χ ι hχ' B hrank fv

  exact ⟨↥R', inferInstance, algRP, F, _iF, _iFt, B, _iB, _iHB, fv, χ, ι₀, X, δ, q, hunif, hfix, hF, hχ,
    h1, h2, h4, h5, hgen, hcardV, hqmul, hqker, hqsurj, hqequiv⟩

end S_HopfAlgebra_exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step
end P2MW
export P2MW.S_HopfAlgebra_exists_fVectStructure_normalForm_model_of_finite_flat_of_inertiaSimple_step (solution)
