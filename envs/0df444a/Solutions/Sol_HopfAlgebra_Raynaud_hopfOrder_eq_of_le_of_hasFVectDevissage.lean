-- Prove2me | solution 1 for HopfAlgebra.Raynaud.hopfOrder_eq_of_le_of_hasFVectDevissage
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f5dd5c2d-b1a7-5004-ab09-f250d5c7a101

import Mathlib
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Definitions.Def_HopfAlgebra_FVectStructure
import Definitions.Def_HopfAlgebra_HasFVectDevissage
import Theorems.Thm_HopfOrder_isHopfOrder_comap_hopfKer
import Theorems.Thm_HopfAlgebra_FVect_hopfOrder_eq_of_le
import Theorems.Thm_HopfOrder_isHopfOrder_map
import Theorems.Thm_HopfOrder_eq_of_le_of_comap_hopfKer_eq_of_map_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HopfAlgebra_Raynaud_hopfOrder_eq_of_le_of_hasFVectDevissage
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply"

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace S17Star

theorem subalgebra_eq_bot_of_finrank_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A]
    (h1 : Module.finrank K A = 1) (T : Subalgebra R A) [Module.Finite R ↥T] : T = ⊥ := by
  haveI : Nontrivial A := Module.nontrivial_of_finrank_eq_succ h1
  refine le_antisymm ?_ bot_le
  intro t ht
  have hsurj : Function.Surjective (algebraMap K A) := by
    intro a
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : A) one_ne_zero).mp h1 a
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one, hc]⟩
  obtain ⟨c, rfl⟩ := hsurj t
  have hint : IsIntegral R (algebraMap K A c) :=
    (Algebra.IsIntegral.isIntegral (R := R) (⟨algebraMap K A c, ht⟩ : ↥T)).map T.val
  have hinj : Function.Injective (IsScalarTower.toAlgHom R K A) := (algebraMap K A).injective
  have hc : IsIntegral R c := (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K A) hinj).mp hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hc
  rw [← hy, ← IsScalarTower.algebraMap_apply]
  exact Subalgebra.algebraMap_mem _ y

theorem main
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {A : Type v} [CommRing A] [HopfAlgebra K A]
    (hdev : HopfAlgebra.HasFVectDevissage R K p A) :
    ∀ [Algebra R A] [IsScalarTower R K A] [Coalgebra.IsCocomm K A] [Module.Finite K A]
      (S S' : Subalgebra R A),
      Module.Finite R ↥S → Submodule.span K (S : Set A) = ⊤ →
      (∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range) →
      (∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S) →
      (∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) →
      Module.Finite R ↥S' → Submodule.span K (S' : Set A) = ⊤ →
      (∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range) →
      (∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S') →
      (∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) →
      S ≤ S' → S = S' := by
  induction hdev with
  | @nil A _ _ h1 =>
      intro _ _ _ _ S S' hfin hspan hcomul hanti hcounit hfin' hspan' hcomul' hanti' hcounit' hle
      haveI := hfin
      haveI := hfin'
      rw [subalgebra_eq_bot_of_finrank_eq_one (K := K) h1 S, subalgebra_eq_bot_of_finrank_eq_one (K := K) h1 S']
  | @step A _ _ _ _ Ā _ _ _ _ π hπ r _ F _ _ hF hq χ ι hχ hrank σ hĀ ih =>
      intro _ _ _ _ S S' hfin hspan hcomul hanti hcounit hfin' hspan' hcomul' hanti' hcounit' hle
      classical

      letI : Algebra R Ā := ((algebraMap K Ā).comp (algebraMap R K)).toAlgebra
      haveI : IsScalarTower R K Ā := IsScalarTower.of_algebraMap_eq (fun _ => rfl)

      obtain ⟨hk1, hk2, hk3, hk4, hk5⟩ :=
        HopfOrder.isHopfOrder_comap_hopfKer S hfin hspan hcomul hanti hcounit π
      obtain ⟨hk1', hk2', hk3', hk4', hk5'⟩ :=
        HopfOrder.isHopfOrder_comap_hopfKer S' hfin' hspan' hcomul' hanti' hcounit' π
      have hlek : S.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R)
          ≤ S'.comap (((HopfAlgebra.hopfKer π).val : ↥(HopfAlgebra.hopfKer π) →ₐ[K] A).restrictScalars R) :=
        fun x hx => hle hx
      haveI : Module.Finite K ↥(HopfAlgebra.hopfKer π) :=
        Module.Finite.of_injective (HopfAlgebra.hopfKer π).val.toLinearMap Subtype.val_injective
      have hker := HopfAlgebra.FVect.hopfOrder_eq_of_le K p hp2 hunif r F hF hq χ ι hχ hrank σ _ _
        hk1 hk2 hk3 hk4 hk5 hk1' hk2' hk3' hk4' hk5' hlek

      obtain ⟨hi1, hi2, hi3, hi4, hi5⟩ := HopfOrder.isHopfOrder_map S hfin hspan hcomul hanti hcounit π hπ
      obtain ⟨hi1', hi2', hi3', hi4', hi5'⟩ := HopfOrder.isHopfOrder_map S' hfin' hspan' hcomul' hanti' hcounit' π hπ
      have hlei : S.map ((π : A →ₐ[K] Ā).restrictScalars R) ≤ S'.map ((π : A →ₐ[K] Ā).restrictScalars R) :=
        Subalgebra.map_mono hle
      have himg := ih _ _ hi1 hi2 hi3 hi4 hi5 hi1' hi2' hi3' hi4' hi5' hlei

      exact HopfOrder.eq_of_le_of_comap_hopfKer_eq_of_map_eq hle hfin hspan hcomul hanti hcounit
        hfin' hspan' hcomul' hanti' hcounit' π hπ hker himg

end S17Star

theorem solution
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hunif : Irreducible (p : R))
    {A : Type v} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    [Coalgebra.IsCocomm K A] [Module.Finite K A]
    (hdev : HopfAlgebra.HasFVectDevissage R K p A)
    (S S' : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hfin' : Module.Finite R ↥S') (hspan' : Submodule.span K (S' : Set A) = ⊤)
    (hcomul' : ∀ x ∈ S', Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S'.val)).range)
    (hanti' : ∀ x ∈ S', HopfAlgebra.antipode K (A := A) x ∈ S')
    (hcounit' : ∀ x ∈ S', Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (hle : S ≤ S') : S = S' :=
  S17Star.main K p hp2 hunif hdev S S' hfin hspan hcomul hanti hcounit hfin' hspan' hcomul' hanti' hcounit' hle

end S_HopfAlgebra_Raynaud_hopfOrder_eq_of_le_of_hasFVectDevissage
end P2MW
export P2MW.S_HopfAlgebra_Raynaud_hopfOrder_eq_of_le_of_hasFVectDevissage (solution)
