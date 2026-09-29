-- Prove2me | solution 1 for IsLocalRing.exists_isDiscreteValuationRing_ringHom_of_finite_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/bf47581a-015b-593a-8909-e17e8170f770

import Mathlib
import Theorems.Thm_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Theorems.Thm_IsAdicComplete_exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
import Theorems.Thm_AdicCompletion_exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap
import Theorems.Thm_AdjoinRoot_exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
p2m_attr_erase "instance" "AdicCompletion.instIsLocalRingMaximalIdeal"

set_option autoImplicit false

universe u

open IsLocalRing Polynomial

namespace CoefAux

theorem isLocalHom_of_map_le {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (f : R →+* S) (h : (maximalIdeal R).map f ≤ maximalIdeal S) : IsLocalHom f :=
  ((local_hom_TFAE f).out 0 2).mpr h

theorem algebraMap_mem_nonZeroDivisors {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] [Module.Flat R B]
    {r : R} (hr : r ∈ nonZeroDivisors R) : algebraMap R B r ∈ nonZeroDivisors B := by
  have hreg : IsSMulRegular B r := Module.Flat.isSMulRegular_of_nonZeroDivisors hr
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply hreg
  simp only [Algebra.smul_def, mul_zero]
  rw [mul_comm] at hx
  exact hx

theorem adicCompletion_dvr (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A)
    (hϖ : maximalIdeal A = Ideal.span {ϖ}) :
    ∃ (_ : IsDomain (AdicCompletion (maximalIdeal A) A)) (_ : IsDiscreteValuationRing (AdicCompletion (maximalIdeal A) A)),
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal A) A)) (AdicCompletion (maximalIdeal A) A) ∧
      maximalIdeal (AdicCompletion (maximalIdeal A) A) =
        Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ} ∧
      Function.Surjective ((residue (AdicCompletion (maximalIdeal A) A)).comp (algebraMap A _)) := by
  obtain ⟨hnoeth, hloc, hmax, hcompl, hcomap, hres⟩ :=
    AdicCompletion.isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal (maximalIdeal A)
  have hspan : maximalIdeal (AdicCompletion (maximalIdeal A) A) =
      Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ} := by
    rw [hmax, hϖ, Ideal.map_span, Set.image_singleton]
  have hflat := IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal A
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  have hreg : algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ ∈ nonZeroDivisors _ :=
    algebraMap_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hirr.ne_zero)
  haveI : (Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ}).IsMaximal := hspan ▸ inferInstance
  haveI : IsAdicComplete (Ideal.span {algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ}) (AdicCompletion (maximalIdeal A) A) :=
    hspan ▸ hcompl
  obtain ⟨hdom, hdvr, -, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal
      (algebraMap A (AdicCompletion (maximalIdeal A) A) ϖ) hreg
  exact ⟨hdom, hdvr, hcompl, hspan, hres⟩

theorem surjective_of_adjoin_simple_eq_top {κ k W : Type*} [Field κ] [Field k] [Algebra κ k] [CommRing W]
    (φ : W →+* k) (α : k) (hα : IsIntegral κ α) (htop : IntermediateField.adjoin κ ({α} : Set k) = ⊤)
    (hκ : ∀ c : κ, algebraMap κ k c ∈ φ.range) (hαmem : α ∈ φ.range) : Function.Surjective φ := by

  let T : Subalgebra κ k :=
    { carrier := φ.range
      mul_mem' := fun ha hb => Subring.mul_mem _ ha hb
      one_mem' := Subring.one_mem _
      add_mem' := fun ha hb => Subring.add_mem _ ha hb
      zero_mem' := Subring.zero_mem _
      algebraMap_mem' := hκ }
  have hadj : Algebra.adjoin κ ({α} : Set k) ≤ T := Algebra.adjoin_le (Set.singleton_subset_iff.mpr hαmem)
  intro x
  have hx : x ∈ (⊤ : IntermediateField κ k) := IntermediateField.mem_top
  rw [← htop, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic] at hx
  exact hadj hx

end CoefAux

open CoefAux in

theorem solution
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (ϖ : A)
    (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S] [Algebra A S] [IsLocalHom (algebraMap A S)]
    [Finite (IsLocalRing.ResidueField S)] :
    ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal W) W) (σ : A →+* W)
      (_ : IsLocalRing.maximalIdeal W = Ideal.span {σ ϖ}) (τ : W →+* S),
      IsLocalHom τ ∧ Function.Surjective ((IsLocalRing.residue S).comp τ) ∧ τ.comp σ = algebraMap A S := by
  classical

  obtain ⟨hdomA, hdvrA, hcomplA, hspanA, hresA⟩ := adicCompletion_dvr A ϖ hϖ
  haveI := hdomA; haveI := hdvrA; haveI := hcomplA
  set Ah : Type u := AdicCompletion (maximalIdeal A) A with hAh
  set ιA : A →+* Ah := algebraMap A Ah with hιA
  have hϖA : maximalIdeal A = Ideal.span {ϖ} := hϖ
  have hϖmem : ϖ ∈ maximalIdeal A := by rw [hϖ]; exact Ideal.mem_span_singleton_self ϖ

  have hleA : (maximalIdeal A).map (algebraMap A S) ≤ maximalIdeal S :=
    ((local_hom_TFAE (algebraMap A S)).out 0 2).mp ‹IsLocalHom (algebraMap A S)›
  obtain ⟨ψ, hψ⟩ := AdicCompletion.exists_ringHom_comp_algebraMap_eq_of_forall_exists_pow_le_comap (maximalIdeal A)
    (maximalIdeal S) (algebraMap A S) (fun n => ⟨n, by
      rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
      exact Ideal.pow_right_mono hleA n⟩)
  have hψι : ∀ a : A, ψ (ιA a) = algebraMap A S a := fun a => by rw [← hψ]; rfl
  haveI hψloc : IsLocalHom ψ := by
    refine isLocalHom_of_map_le ψ ?_
    rw [hspanA, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hψι]
    exact map_nonunit (algebraMap A S) ϖ hϖmem

  letI : Algebra (ResidueField Ah) (ResidueField S) := (ResidueField.map ψ).toAlgebra
  have halg : ∀ w : Ah, algebraMap (ResidueField Ah) (ResidueField S) (residue Ah w) = residue S (ψ w) := fun _ => rfl
  haveI : Finite (ResidueField Ah) := Finite.of_injective _ (ResidueField.map ψ).injective
  haveI : Module.Finite (ResidueField Ah) (ResidueField S) := Module.Finite.of_finite
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField Ah) (ResidueField S)
  have hαint : IsIntegral (ResidueField Ah) α := Algebra.IsIntegral.isIntegral α
  have hgm : (minpoly (ResidueField Ah) α).Monic := minpoly.monic hαint
  have hgirr : Irreducible (minpoly (ResidueField Ah) α) := minpoly.irreducible hαint
  have hgsep : (minpoly (ResidueField Ah) α).Separable := Algebra.IsSeparable.isSeparable (ResidueField Ah) α
  obtain ⟨F, hFg, -, hFm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr (Polynomial.map_surjective (residue Ah) residue_surjective (minpoly (ResidueField Ah) α))) hgm

  haveI hFirr : Fact (Irreducible (F.map (residue Ah))) := ⟨hFg ▸ hgirr⟩
  haveI : Module.Finite (ResidueField Ah) (AdjoinRoot (F.map (residue Ah))) := (hFm.map (residue Ah)).finite_adjoinRoot
  haveI : Algebra.IsSeparable (ResidueField Ah) (AdjoinRoot (F.map (residue Ah))) := inferInstance
  obtain ⟨hWloc, hWhom, hWfin, hWfree, hWet, hWcompl, hWmap, ⟨eW⟩⟩ :=
    AdjoinRoot.exists_isLocalRing_etale_residueField_algEquiv_of_isAdicComplete Ah F hFm
  haveI := hWloc; haveI := hWhom; haveI := hWfin; haveI := hWfree
  have hϖW : maximalIdeal (AdjoinRoot F) = Ideal.span {algebraMap Ah (AdjoinRoot F) (ιA ϖ)} := by
    rw [← hWmap, hspanA, Ideal.map_span, Set.image_singleton]
  have hregW : algebraMap Ah (AdjoinRoot F) (ιA ϖ) ∈ nonZeroDivisors (AdjoinRoot F) := by
    have hirrA : Irreducible (ιA ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hspanA
    exact algebraMap_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hirrA.ne_zero)
  haveI : (Ideal.span {algebraMap Ah (AdjoinRoot F) (ιA ϖ)}).IsMaximal := hϖW ▸ inferInstance
  haveI : IsAdicComplete (Ideal.span {algebraMap Ah (AdjoinRoot F) (ιA ϖ)}) (AdjoinRoot F) := hϖW ▸ hWcompl
  obtain ⟨hdomW, hdvrW, -, -⟩ :=
    IsAdicComplete.exists_isDomain_isDiscreteValuationRing_of_span_singleton_isMaximal _ hregW

  obtain ⟨a₀, ha₀⟩ := residue_surjective (R := S) α
  have hmapres : (F.map ψ).map (residue S) =
      (minpoly (ResidueField Ah) α).map (algebraMap (ResidueField Ah) (ResidueField S)) := by
    rw [← hFg, Polynomial.map_map, Polynomial.map_map]
    rfl
  have hres_eval : ∀ Q : S[X], residue S (Q.eval a₀) = (Q.map (residue S)).eval α := fun Q => by
    rw [← ha₀, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  have heval : (F.map ψ).eval a₀ ∈ maximalIdeal S := by
    rw [← residue_eq_zero_iff, hres_eval, hmapres, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal S) ((F.map ψ).derivative.eval a₀)) := by
    show IsUnit (residue S _)
    rw [isUnit_iff_ne_zero, hres_eval, ← Polynomial.derivative_map, hmapres, Polynomial.derivative_map,
      Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hgsep.aeval_derivative_ne_zero (minpoly.aeval _ _)
  obtain ⟨s, hs, hs₀⟩ := HenselianRing.is_henselian (I := maximalIdeal S) (F.map ψ) (hFm.map ψ) a₀ heval hderiv
  have hsF : F.eval₂ ψ s = 0 := by rwa [Polynomial.IsRoot.def, Polynomial.eval_map] at hs
  let τ : AdjoinRoot F →+* S := AdjoinRoot.lift ψ s hsF
  have hτof : ∀ w : Ah, τ (algebraMap Ah (AdjoinRoot F) w) = ψ w := fun w => by
    rw [AdjoinRoot.algebraMap_eq]; exact AdjoinRoot.lift_of hsF
  have hτroot : τ (AdjoinRoot.root F) = s := AdjoinRoot.lift_root hsF
  have hress : residue S s = α := by
    rw [← ha₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hs₀

  let σ : A →+* AdjoinRoot F := (algebraMap Ah (AdjoinRoot F)).comp ιA
  refine ⟨AdjoinRoot F, inferInstance, hdomW, hdvrW, hWcompl, σ, hϖW, τ, ?_, ?_, ?_⟩
  ·
    refine isLocalHom_of_map_le τ ?_
    rw [hϖW, Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, hτof, hψι]
    exact map_nonunit (algebraMap A S) ϖ hϖmem
  ·
    refine surjective_of_adjoin_simple_eq_top ((residue S).comp τ) α hαint hα (fun c => ?_) ?_
    · obtain ⟨w, rfl⟩ := residue_surjective (R := Ah) c
      exact ⟨algebraMap Ah (AdjoinRoot F) w, by rw [RingHom.comp_apply, hτof, halg]⟩
    · exact ⟨AdjoinRoot.root F, by rw [RingHom.comp_apply, hτroot, hress]⟩
  ·
    ext a
    simp only [σ, RingHom.comp_apply, hτof, hψι]

#print axioms solution

end S_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField
end P2MW
export P2MW.S_IsLocalRing_exists_isDiscreteValuationRing_ringHom_of_finite_residueField (solution)
