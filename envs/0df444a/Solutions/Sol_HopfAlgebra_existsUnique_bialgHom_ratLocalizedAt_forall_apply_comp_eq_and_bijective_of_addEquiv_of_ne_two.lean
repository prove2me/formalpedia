-- Prove2me | solution 1 for HopfAlgebra.existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/6cdada05-3856-5c37-bb50-0df192245835

import Mathlib
import Definitions.Def_GaloisRep_Flat

import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instAlgebraBaseChangeDual CartierDual.instRingBaseChangeDual CartierDual.instModuleRestrictBaseChange CartierDual.instIsScalarTowerRestrictBaseChange MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra instIsScalarTowerTensorProduct_definitions"
p2m_attr_erase "simp" "HopfOrder.doubleCmp_tmul HopfOrder.tensorSqHom_tmul HopfOrder.baseChangeHom_tmul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.FVectStructure.addChar_apply HopfAlgebra.FVectStructure.mk.sizeOf_spec HopfAlgebra.FVectStructure.mk.injEq HopfAlgebra.FVectStructure.unitsAct_apply HopfAlgebra.mem_vanishingIdealOfPoints_iff HopfAlgebra.liftPoint_mk HopfAlgebra.mem_ptSet_iff CartierDual.dualBaseChangeLin_tmul CartierDual.dualBaseChange_tmul CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply mem_flatClosure_iff"

set_option autoImplicit false

namespace RayIsoS17

variable (p : ℕ) [hp : Fact p.Prime]

theorem not_dvd_of_mem {q : ℚ} (hq : q ∈ GaloisRep.ratLocalizedAt p) : ¬ p ∣ q.den :=
  (Nat.Prime.coprime_iff_not_dvd hp.out).mp (Nat.Coprime.symm hq)

theorem mem_of_not_dvd {q : ℚ} (hq : ¬ p ∣ q.den) : q ∈ GaloisRep.ratLocalizedAt p :=
  Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hq)

scoped instance isLocalization : IsLocalization.AtPrime (↥(GaloisRep.ratLocalizedAt p)) (Ideal.span {(p : ℤ)}) where
  map_units := by
    rintro ⟨n, hn⟩
    have hn' : ¬ (p : ℤ) ∣ n := fun h => hn (Ideal.mem_span_singleton.mpr h)
    have hn0 : n ≠ 0 := fun h => hn' (h ▸ dvd_zero _)
    have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn0
    have hmem : (n : ℚ)⁻¹ ∈ GaloisRep.ratLocalizedAt p := by
      apply mem_of_not_dvd
      rw [Rat.inv_intCast_den, if_neg hn0]
      intro h
      exact hn' (Int.natCast_dvd.mpr h)
    refine isUnit_iff_exists_inv.mpr ⟨⟨(n : ℚ)⁻¹, hmem⟩, ?_⟩
    apply Subtype.ext
    show ((algebraMap ℤ ↥(GaloisRep.ratLocalizedAt p) n : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) * (n : ℚ)⁻¹ = 1
    rw [eq_intCast, Subring.coe_intCast, mul_inv_cancel₀ hnQ]
  surj := by
    intro q
    have hden : ((q : ℚ).den : ℤ) ∈ (Ideal.span {(p : ℤ)}).primeCompl := by
      intro h
      exact not_dvd_of_mem p q.2 (Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp h))
    refine ⟨⟨(q : ℚ).num, ⟨((q : ℚ).den : ℤ), hden⟩⟩, ?_⟩
    apply Subtype.ext
    show (q : ℚ) * ((algebraMap ℤ ↥(GaloisRep.ratLocalizedAt p) ((q : ℚ).den : ℤ) : ↥(GaloisRep.ratLocalizedAt p)) : ℚ) =
      ((algebraMap ℤ ↥(GaloisRep.ratLocalizedAt p) (q : ℚ).num : ↥(GaloisRep.ratLocalizedAt p)) : ℚ)
    rw [eq_intCast, eq_intCast, Subring.coe_intCast, Subring.coe_intCast, Int.cast_natCast]
    exact Rat.mul_den_eq_num (q : ℚ)
  exists_of_eq := by
    intro a b h
    refine ⟨1, ?_⟩
    have h' := congrArg (fun x : ↥(GaloisRep.ratLocalizedAt p) => (x : ℚ)) h
    simp only [eq_intCast, Subring.coe_intCast, Int.cast_inj] at h'
    rw [h']

theorem span_ne_bot : (Ideal.span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.out.ne_zero

scoped instance span_isPrime : (Ideal.span {(p : ℤ)} : Ideal ℤ).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.out.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hp.out)

scoped instance isDVR : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt p) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain ℤ (span_ne_bot p) _

scoped instance isFractionRing : IsFractionRing ↥(GaloisRep.ratLocalizedAt p) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Ideal.span {(p : ℤ)}).primeCompl _ _

theorem irreducible_natCast : Irreducible ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)) := by
  apply IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
  · exact_mod_cast hp.out.ne_zero
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {(p : ℤ)}) ↥(GaloisRep.ratLocalizedAt p),
      Ideal.map_span, Set.image_singleton, eq_intCast, Int.cast_natCast]

end RayIsoS17
p2m_reactivate "P2MW.S_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two.RayIsoS17"

theorem solution
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {M₁ M₂ : Type} [AddCommGroup M₁] [AddCommGroup M₂]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₁]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M₂]
    (H₁ : Type) [CommRing H₁] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₁]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₁] [Module.Free (GaloisRep.ratLocalizedAt p) H₁]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₁]
    (hrank₁ : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H₁ = p ^ a)
    (e₁ : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M₁)
    (he₁_add : ∀ f g, e₁ (f * g) = e₁ f + e₁ g)
    (he₁_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₁, g x = σ (f x)) → e₁ g = σ • e₁ f)
    (H₂ : Type) [CommRing H₂] [HopfAlgebra (GaloisRep.ratLocalizedAt p) H₂]
    [Module.Finite (GaloisRep.ratLocalizedAt p) H₂] [Module.Free (GaloisRep.ratLocalizedAt p) H₂]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt p) H₂]
    (hrank₂ : ∃ a : ℕ, Module.finrank (GaloisRep.ratLocalizedAt p) H₂ = p ^ a)
    (e₂ : WithConv (H₂ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ) ≃ M₂)
    (he₂_add : ∀ f g, e₂ (f * g) = e₂ f + e₂ g)
    (he₂_act : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (f g : WithConv (H₂ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ)),
      (∀ x : H₂, g x = σ (f x)) → e₂ g = σ • e₂ f)
    (φ : M₁ ≃+ M₂)
    (hφ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₁), φ (σ • m) = σ • φ m) :
    (∃! g : H₂ →ₐc[GaloisRep.ratLocalizedAt p] H₁,
      ∀ f : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[GaloisRep.ratLocalizedAt p] H₁))) = φ (e₁ f)) ∧
    (∀ g : H₂ →ₐc[GaloisRep.ratLocalizedAt p] H₁,
      (∀ f : WithConv (H₁ →ₐ[GaloisRep.ratLocalizedAt p] AlgebraicClosure ℚ),
        e₂ (WithConv.toConv ((WithConv.ofConv f).comp (g : H₂ →ₐ[GaloisRep.ratLocalizedAt p] H₁))) = φ (e₁ f)) →
      Function.Bijective g) := by
  haveI hQa : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.isAlgebraic ℚ <;> first | rfl | with_reducible_and_instances rfl | exact Subsingleton.elim _ _
  have hirr := RayIsoS17.irreducible_natCast p

  obtain ⟨g, hg, hguniq⟩ :=
    HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
      (↥(GaloisRep.ratLocalizedAt p)) p hp2 hirr ℚ (AlgebraicClosure ℚ) H₁ hrank₁ e₁ he₁_add he₁_act
      H₂ hrank₂ e₂ he₂_add he₂_act (φ : M₁ →+ M₂) (fun σ m => hφ σ m)
  have hφ' : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (m : M₂), φ.symm (σ • m) = σ • φ.symm m := by
    intro σ m
    apply φ.injective
    rw [AddEquiv.apply_symm_apply, hφ, AddEquiv.apply_symm_apply]
  obtain ⟨g', hg', -⟩ :=
    HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
      (↥(GaloisRep.ratLocalizedAt p)) p hp2 hirr ℚ (AlgebraicClosure ℚ) H₂ hrank₂ e₂ he₂_add he₂_act
      H₁ hrank₁ e₁ he₁_add he₁_act (φ.symm : M₂ →+ M₁) (fun σ m => hφ' σ m)
  have hid₁ : g.comp g' = BialgHom.id _ H₁ := by
    obtain ⟨u, -, huniq⟩ :=
      HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
        (↥(GaloisRep.ratLocalizedAt p)) p hp2 hirr ℚ (AlgebraicClosure ℚ) H₁ hrank₁ e₁ he₁_add he₁_act
        H₁ hrank₁ e₁ he₁_add he₁_act (AddMonoidHom.id M₁) (fun σ m => rfl)
    have h1 := huniq (g.comp g') (fun f => by
      have hc : (WithConv.ofConv f).comp (g.comp g' : H₁ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₁) =
          ((WithConv.ofConv f).comp (g : H₂ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₁)).comp
            (g' : H₁ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₂) := AlgHom.ext fun _ => rfl
      rw [hc, ← WithConv.ofConv_toConv (((WithConv.ofConv f).comp (g : H₂ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₁))), hg', WithConv.toConv_ofConv, hg]
      show φ.symm (φ (e₁ f)) = e₁ f
      rw [AddEquiv.symm_apply_apply])
    have h2 := huniq (BialgHom.id _ H₁) (fun f => by
      have hc : (WithConv.ofConv f).comp (BialgHom.id ↥(GaloisRep.ratLocalizedAt p) H₁ : H₁ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₁) =
          WithConv.ofConv f := AlgHom.ext fun _ => rfl
      rw [hc, WithConv.toConv_ofConv]
      rfl)
    exact h1.trans h2.symm
  have hid₂ : g'.comp g = BialgHom.id _ H₂ := by
    obtain ⟨u, -, huniq⟩ :=
      HopfAlgebra.existsUnique_bialgHom_forall_apply_comp_eq_of_finrank_eq_prime_pow_of_irreducible
        (↥(GaloisRep.ratLocalizedAt p)) p hp2 hirr ℚ (AlgebraicClosure ℚ) H₂ hrank₂ e₂ he₂_add he₂_act
        H₂ hrank₂ e₂ he₂_add he₂_act (AddMonoidHom.id M₂) (fun σ m => rfl)
    have h1 := huniq (g'.comp g) (fun f => by
      have hc : (WithConv.ofConv f).comp (g'.comp g : H₂ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₂) =
          ((WithConv.ofConv f).comp (g' : H₁ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₂)).comp
            (g : H₂ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₁) := AlgHom.ext fun _ => rfl
      rw [hc, ← WithConv.ofConv_toConv (((WithConv.ofConv f).comp (g' : H₁ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₂))), hg, WithConv.toConv_ofConv, hg']
      show φ (φ.symm (e₂ f)) = e₂ f
      rw [AddEquiv.apply_symm_apply])
    have h2 := huniq (BialgHom.id _ H₂) (fun f => by
      have hc : (WithConv.ofConv f).comp (BialgHom.id ↥(GaloisRep.ratLocalizedAt p) H₂ : H₂ →ₐ[↥(GaloisRep.ratLocalizedAt p)] H₂) =
          WithConv.ofConv f := AlgHom.ext fun _ => rfl
      rw [hc, WithConv.toConv_ofConv]
      rfl)
    exact h1.trans h2.symm
  refine ⟨⟨g, fun f => hg f, fun g₂ hg₂ => hguniq g₂ (fun f => hg₂ f)⟩, ?_⟩
  intro g₂ hg₂
  have hgg : g₂ = g := hguniq g₂ (fun f => hg₂ f)
  rw [hgg]
  refine Function.bijective_iff_has_inverse.mpr ⟨g', fun x => ?_, fun y => ?_⟩
  · exact DFunLike.congr_fun hid₂ x
  · exact DFunLike.congr_fun hid₁ y

end S_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two
end P2MW
export P2MW.S_HopfAlgebra_existsUnique_bialgHom_ratLocalizedAt_forall_apply_comp_eq_and_bijective_of_addEquiv_of_ne_two (solution)
