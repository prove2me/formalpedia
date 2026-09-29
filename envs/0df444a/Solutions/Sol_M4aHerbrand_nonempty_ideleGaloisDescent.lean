-- Prove2me | solution 1 for M4aHerbrand.nonempty_ideleGaloisDescent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/5a7340dd-ac9a-50dc-bf8a-165f6cd4ba19

import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_AdeleBaseChange
import Definitions.Def_NumberField_InfiniteAdeleRing_BaseChangeData
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_FiniteAdeleRing_TensorRestrictedProduct
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_Equiv
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 320000
set_option maxSynthPendingDepth 3

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain TensorProduct

section Transfer

variable {R S A : Type*} [TopologicalSpace R] [TopologicalSpace S] [TopologicalSpace A] [Add A]

private theorem IsModuleTopology.of_continuousSMul_iff [SMul R A] [SMul S A]
    (h : ∀ t : TopologicalSpace A, @ContinuousSMul R A _ _ t ↔ @ContinuousSMul S A _ _ t)
    [hR : IsModuleTopology R A] : IsModuleTopology S A := by
  refine ⟨?_⟩
  rw [eq_moduleTopology R A]
  show sInf _ = sInf _
  congr 1
  ext t
  simp only [Set.mem_setOf_eq]
  exact and_congr_left' (h t)

private theorem IsModuleTopology.of_smul_eq (i₁ i₂ : SMul R A)
    (h : ∀ (r : R) (a : A), i₁.smul r a = i₂.smul r a)
    (h₁ : @IsModuleTopology R _ A _ i₁ _) : @IsModuleTopology R _ A _ i₂ _ := by
  have : i₁ = i₂ := by
    cases i₁; cases i₂; congr; funext r a; exact h r a
  subst this
  exact h₁

end Transfer

section PullBack

variable {R₁ R₂ A : Type*} [TopologicalSpace R₁] [TopologicalSpace R₂]

@[reducible] private def smulFst [SMul R₁ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.1 • a⟩

@[reducible] private def smulSnd [SMul R₂ A] : SMul (R₁ × R₂) A := ⟨fun p a => p.2 • a⟩

private theorem continuousSMul_smulFst_iff [SMul R₁ A] [Zero R₂] (t : TopologicalSpace A) :
    @ContinuousSMul (R₁ × R₂) A smulFst _ t ↔ @ContinuousSMul R₁ A _ _ t := by
  letI : TopologicalSpace A := t
  letI : SMul (R₁ × R₂) A := smulFst
  constructor
  · intro h
    have hc : Continuous fun p : (R₁ × R₂) × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : R₁ × A => p.1 • p.2)
        = (fun p : (R₁ × R₂) × A => p.1 • p.2) ∘ fun p : R₁ × A => ((p.1, (0 : R₂)), p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩
  · intro h
    have hc : Continuous fun p : R₁ × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : (R₁ × R₂) × A => p.1 • p.2)
        = (fun p : R₁ × A => p.1 • p.2) ∘ fun p : (R₁ × R₂) × A => (p.1.1, p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩

private theorem continuousSMul_smulSnd_iff [SMul R₂ A] [Zero R₁] (t : TopologicalSpace A) :
    @ContinuousSMul (R₁ × R₂) A smulSnd _ t ↔ @ContinuousSMul R₂ A _ _ t := by
  letI : TopologicalSpace A := t
  letI : SMul (R₁ × R₂) A := smulSnd
  constructor
  · intro h
    have hc : Continuous fun p : (R₁ × R₂) × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : R₂ × A => p.1 • p.2)
        = (fun p : (R₁ × R₂) × A => p.1 • p.2) ∘ fun p : R₂ × A => (((0 : R₁), p.1), p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩
  · intro h
    have hc : Continuous fun p : R₂ × A => p.1 • p.2 := h.continuous_smul
    have he : (fun p : (R₁ × R₂) × A => p.1 • p.2)
        = (fun p : R₂ × A => p.1 • p.2) ∘ fun p : (R₁ × R₂) × A => (p.1.2, p.2) := by
      funext p; rfl
    exact ⟨by rw [he]; exact hc.comp (by fun_prop)⟩

private theorem isModuleTopology_smulFst [Add A] [SMul R₁ A] [Zero R₂] [TopologicalSpace A]
    [IsModuleTopology R₁ A] :
    @IsModuleTopology (R₁ × R₂) _ A _ smulFst _ :=
  @IsModuleTopology.of_continuousSMul_iff R₁ (R₁ × R₂) A _ _ _ _ _ smulFst
    (fun t => (continuousSMul_smulFst_iff t).symm) _

private theorem isModuleTopology_smulSnd [Add A] [SMul R₂ A] [Zero R₁] [TopologicalSpace A]
    [IsModuleTopology R₂ A] :
    @IsModuleTopology (R₁ × R₂) _ A _ smulSnd _ :=
  @IsModuleTopology.of_continuousSMul_iff R₂ (R₁ × R₂) A _ _ _ _ _ smulSnd
    (fun t => (continuousSMul_smulSnd_iff t).symm) _

end PullBack

section AlgEquiv

variable {R A : Type*} [CommSemiring R] [TopologicalSpace R] [Semiring A] [Algebra R A]
  [TopologicalSpace A] [IsModuleTopology R A] [ContinuousAdd A]

private theorem continuous_algEquiv (e : A ≃ₐ[R] A) : Continuous e :=
  (IsModuleTopology.continuous_of_linearMap e.toLinearMap).congr fun _ => rfl

end AlgEquiv

section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

private noncomputable def conjAct [Algebra (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F)
    (σ : F ≃ₐ[E] F) : AdeleRing S F ≃+* AdeleRing S F :=
  (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te)).toRingEquiv

private theorem continuous_conjAct [Algebra (AdeleRing R E) (AdeleRing S F)]
    [IsModuleTopology (AdeleRing R E) (AdeleRing S F)]
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct R E S F te σ) :=
  (continuous_algEquiv (te.symm.trans ((Algebra.TensorProduct.congr AlgEquiv.refl σ).trans te))).congr
    fun _ => rfl

omit [Algebra E F] in

private theorem isModuleTopology_adeleRing_prodMap
    (βi : InfiniteAdeleRing E →+* InfiniteAdeleRing F)
    (βf : FiniteAdeleRing R E →+* FiniteAdeleRing S F)
    (hi : letI := βi.toAlgebra; IsModuleTopology (InfiniteAdeleRing E) (InfiniteAdeleRing F))
    (hf : letI := βf.toAlgebra; IsModuleTopology (FiniteAdeleRing R E) (FiniteAdeleRing S F)) :
    letI : Algebra (AdeleRing R E) (AdeleRing S F) := (RingHom.prodMap βi βf).toAlgebra
    IsModuleTopology (AdeleRing R E) (AdeleRing S F) := by
  letI : Algebra (InfiniteAdeleRing E) (InfiniteAdeleRing F) := βi.toAlgebra
  letI : Algebra (FiniteAdeleRing R E) (FiniteAdeleRing S F) := βf.toAlgebra

  letI mi : Module (InfiniteAdeleRing E × FiniteAdeleRing R E) (InfiniteAdeleRing F) :=
    Module.compHom _ (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing R E))
  letI mf : Module (InfiniteAdeleRing E × FiniteAdeleRing R E) (FiniteAdeleRing S F) :=
    Module.compHom _ (RingHom.snd (InfiniteAdeleRing E) (FiniteAdeleRing R E))
  have hi' : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E) (InfiniteAdeleRing F) :=
    IsModuleTopology.of_smul_eq smulFst _ (fun _ _ => rfl) isModuleTopology_smulFst
  have hf' : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E) (FiniteAdeleRing S F) :=
    IsModuleTopology.of_smul_eq smulSnd _ (fun _ _ => rfl) isModuleTopology_smulSnd
  have hprod : IsModuleTopology (InfiniteAdeleRing E × FiniteAdeleRing R E)
      (InfiniteAdeleRing F × FiniteAdeleRing S F) := IsModuleTopology.instProd
  exact IsModuleTopology.of_smul_eq _ _ (fun _ _ => rfl) hprod

end Adele

end M4aHerbrand.Bridge

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain TensorProduct

section OMT

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra A B]

private theorem isModuleTopology_of_continuous_algebraMap_of_sigmaCompact
    [SigmaCompactSpace A] [T2Space B] [BaireSpace B] [Module.Free A B] [Module.Finite A B]
    (hβ : Continuous (algebraMap A B)) : IsModuleTopology A B := by
  let b := Module.Free.chooseBasis A B
  let Φ : (Module.Free.ChooseBasisIndex A B → A) ≃ₗ[A] B := b.equivFun.symm
  have hΦ : Continuous Φ := by
    have he : (Φ : (Module.Free.ChooseBasisIndex A B → A) → B)
        = fun c => ∑ i, algebraMap A B (c i) * b i := by
      funext c
      show b.equivFun.symm c = _
      rw [b.equivFun_symm_apply]
      simp_rw [Algebra.smul_def]
    rw [he]
    exact continuous_finsetSum _ fun i _ => (hβ.comp (continuous_apply i)).mul continuous_const
  have hopen : IsOpenMap Φ :=
    AddMonoidHom.isOpenMap_of_sigmaCompact Φ.toLinearMap.toAddMonoidHom Φ.surjective hΦ
  have hsymm : Continuous Φ.symm :=
    (Φ.toEquiv.toHomeomorphOfContinuousOpen hΦ hopen).continuous_symm
  let Ψ : (Module.Free.ChooseBasisIndex A B → A) ≃L[A] B :=
    { Φ with continuous_toFun := hΦ, continuous_invFun := hsymm }
  exact IsModuleTopology.iso Ψ

end OMT

section Adele

variable (R E : Type*) [CommRing R] [IsDedekindDomain R] [Field E] [Algebra R E]
  [IsFractionRing R E]
variable (S F : Type*) [CommRing S] [IsDedekindDomain S] [Field F] [Algebra S F]
  [IsFractionRing S F]
variable [Algebra E F]

open scoped RestrictedProduct in

private scoped instance instT2SpaceAdeleRing : T2Space (AdeleRing S F) :=
  inferInstanceAs (T2Space (((v : InfinitePlace F) → v.Completion) ×
    Πʳ v : HeightOneSpectrum S, [v.adicCompletion F, v.adicCompletionIntegers F]))

private theorem isModuleTopology_adeleRing_of_continuous [Module.Finite E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    [SigmaCompactSpace (AdeleRing R E)] [LocallyCompactSpace (AdeleRing S F)]
    (hβ : Continuous (algebraMap (AdeleRing R E) (AdeleRing S F)))
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) :
    IsModuleTopology (AdeleRing R E) (AdeleRing S F) := by
  haveI : Module.Free (AdeleRing R E) (AdeleRing S F) := Module.Free.of_equiv te.toLinearEquiv
  haveI : Module.Finite (AdeleRing R E) (AdeleRing S F) := Module.Finite.equiv te.toLinearEquiv
  exact isModuleTopology_of_continuous_algebraMap_of_sigmaCompact hβ

private theorem continuous_conjAct_of_continuous [Module.Finite E F]
    [Algebra (AdeleRing R E) (AdeleRing S F)]
    [SigmaCompactSpace (AdeleRing R E)] [LocallyCompactSpace (AdeleRing S F)]
    (hβ : Continuous (algebraMap (AdeleRing R E) (AdeleRing S F)))
    (te : ((AdeleRing R E) ⊗[E] F) ≃ₐ[AdeleRing R E] AdeleRing S F) (σ : F ≃ₐ[E] F) :
    Continuous (conjAct R E S F te σ) :=
  haveI := isModuleTopology_adeleRing_of_continuous R E S F hβ te
  continuous_conjAct R E S F te σ

end Adele

end M4aHerbrand.Bridge
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain TensorProduct

section Infinite

variable (K : Type*) [Field K]

private scoped instance sigmaCompactSpace_completion (v : InfinitePlace K) : SigmaCompactSpace v.Completion :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).isClosedEmbedding.sigmaCompactSpace

private scoped instance sigmaCompactSpace_infiniteAdeleRing [NumberField K] : SigmaCompactSpace (InfiniteAdeleRing K) :=
  inferInstanceAs (SigmaCompactSpace ((v : InfinitePlace K) → v.Completion))

end Infinite
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

section Finite

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K] in

private theorem countable_of_free_finite_int [Module.Free ℤ R] [Module.Finite ℤ R] : Countable R :=
  Countable.of_equiv _ (Module.Free.chooseBasis ℤ R).equivFun.toEquiv.symm

private theorem iUnion_smul_integralFiniteAdeles :
    ⋃ s : R, (fun z => algebraMap K (FiniteAdeleRing R K) (algebraMap R K s)⁻¹ * z) ''
      NumberField.AdelicBox.integralFiniteAdeles R K = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  obtain ⟨s, hs0, hs⟩ := NumberField.AdelicBox.exists_mul_mem_integralFiniteAdeles R K y
  refine Set.mem_iUnion.mpr ⟨s, _, hs, ?_⟩
  have hsK : algebraMap R K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hs0
  show algebraMap K (FiniteAdeleRing R K) (algebraMap R K s)⁻¹ *
      (algebraMap R (FiniteAdeleRing R K) s * y) = y
  rw [← mul_assoc, IsScalarTower.algebraMap_apply R K (FiniteAdeleRing R K) s, ← map_mul,
    inv_mul_cancel₀ hsK, map_one, one_mul]

variable [Module.Free ℤ R] [Module.Finite ℤ R]

private theorem isCompact_integralFiniteAdeles :
    IsCompact (NumberField.AdelicBox.integralFiniteAdeles R K) := by
  haveI : ∀ v : HeightOneSpectrum R,
      CompactSpace ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) := fun v =>
    inferInstanceAs (CompactSpace (v.adicCompletionIntegers K))
  have h := isCompact_range (RestrictedProduct.isOpenEmbedding_structureMap
    (R := fun v : HeightOneSpectrum R => v.adicCompletion K)
    (A := fun v : HeightOneSpectrum R => (v.adicCompletionIntegers K : Set (v.adicCompletion K)))
    Fact.out).continuous
  rw [RestrictedProduct.range_structureMap] at h
  exact h

private scoped instance sigmaCompactSpace_finiteAdeleRing : SigmaCompactSpace (FiniteAdeleRing R K) := by
  haveI : Countable R := countable_of_free_finite_int R
  refine ⟨?_⟩
  rw [← iUnion_smul_integralFiniteAdeles R K]
  exact isSigmaCompact_iUnion_of_isCompact _ fun s =>
    (isCompact_integralFiniteAdeles R K).image (continuous_const.mul continuous_id)

private scoped instance sigmaCompactSpace_adeleRing [NumberField K] : SigmaCompactSpace (AdeleRing R K) :=
  inferInstanceAs (SigmaCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))

end Finite
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

section RoadO

variable (A K B L : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [NumberField K] [Algebra A K]
  [IsFractionRing A K] [Module.Free ℤ A] [Module.Finite ℤ A]
  [CommRing B] [IsDedekindDomain B] [Field L] [NumberField L] [Algebra B L] [IsFractionRing B L]
  [Module.Free ℤ B] [Module.Finite ℤ B] [Algebra K L]

private theorem continuous_conjAct_of_continuous_of_free
    [Algebra (AdeleRing A K) (AdeleRing B L)]
    (hβ : Continuous (algebraMap (AdeleRing A K) (AdeleRing B L)))
    (te : ((AdeleRing A K) ⊗[K] L) ≃ₐ[AdeleRing A K] AdeleRing B L) (σ : L ≃ₐ[K] L) :
    Continuous (conjAct A K B L te σ) :=
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  continuous_conjAct_of_continuous A K B L hβ te σ

end RoadO
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

end M4aHerbrand.Bridge
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section AKLB

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]

include K L in
omit [IsFractionRing B L] in

private theorem tendsto_under_cofinite :
    Filter.Tendsto (HeightOneSpectrum.under A : HeightOneSpectrum B → HeightOneSpectrum A)
      Filter.cofinite Filter.cofinite := by
  intro S hS
  exact preimage_comap_finite A K L B Sᶜ hS

private def finiteLocalHom (w : HeightOneSpectrum B) : (w.under A).adicCompletion K →+* w.adicCompletion L :=
  (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).toRingHom

private theorem finiteLocalHom_apply (w : HeightOneSpectrum B) (x : (w.under A).adicCompletion K) :
    finiteLocalHom A K L B w x =
      Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) x := rfl

private theorem continuous_finiteLocalHom (w : HeightOneSpectrum B) : Continuous (finiteLocalHom A K L B w) :=
  Extension.adicCompletionSemialgHom_continuous K L (⟨w, rfl⟩ : (w.under A).Extension B)

private theorem finiteLocalHom_mapsTo (w : HeightOneSpectrum B) :
    Set.MapsTo (finiteLocalHom A K L B w)
      ((w.under A).adicCompletionIntegers K : Set ((w.under A).adicCompletion K))
      (w.adicCompletionIntegers L : Set (w.adicCompletion L)) :=
  Set.mapsTo_iff_image_subset.2
    (Extension.adicCompletionSemialgHom_image_adicCompletionIntegers K L
      (⟨w, rfl⟩ : (w.under A).Extension B))

private def finiteConorm : FiniteAdeleRing A K →+* FiniteAdeleRing B L :=
  RestrictedProduct.mapAlongRingHom
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w => finiteLocalHom A K L B w)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)

@[scoped simp] private theorem finiteConorm_apply (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    finiteConorm A K L B x w =
      Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) (x (w.under A)) :=
  rfl

private theorem continuous_finiteConorm : Continuous (finiteConorm A K L B) :=
  RestrictedProduct.mapAlong_continuous
    (fun v : HeightOneSpectrum A => v.adicCompletion K)
    (fun w : HeightOneSpectrum B => w.adicCompletion L)
    (HeightOneSpectrum.under A) (tendsto_under_cofinite A K L B)
    (fun w x => finiteLocalHom A K L B w x)
    (Filter.Eventually.of_forall fun w => finiteLocalHom_mapsTo A K L B w)
    (fun w => continuous_finiteLocalHom A K L B w)

private theorem finiteConorm_algebraMap (k : K) :
    finiteConorm A K L B (algebraMap K (FiniteAdeleRing A K) k) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap K L k) := by
  refine FiniteAdeleRing.ext L fun w => ?_
  rw [FiniteAdeleRing.algebraMap_apply]
  exact (Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B)).commutes k

end AKLB
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

end M4aHerbrand.Bridge
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

end
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace ArchSemilocal
p2m_open "M4aHerbrand"

open NumberField NumberField.InfinitePlace TensorProduct

open scoped NumberField.LiesOver

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
private theorem liesOver_of_comap_eq {v : InfinitePlace K} {w : InfinitePlace L}
    (h : w.comap (algebraMap K L) = v) : w.1.LiesOver v.1 :=
  ⟨congrArg Subtype.val h⟩

omit [NumberField K] [NumberField L] in
private theorem finiteDimensional_completion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.1.LiesOver v.1] : FiniteDimensional v.Completion w.Completion := by
  by_cases h : w.IsUnramified K
  · exact FiniteDimensional.of_finrank_pos
      (by rw [Completion.finrank_eq_one_of_isUnramified v h]; norm_num)
  · exact FiniteDimensional.of_finrank_pos
      (by rw [Completion.finrank_eq_two_of_isRamified v h]; norm_num)

private instance instIsScalarTowerCompletion (w : InfinitePlace L) : IsScalarTower K L w.Completion :=
  .of_algebraMap_eq fun x => NumberField.InfinitePlace.Completion.ext <| by
    rw [NumberField.InfinitePlace.Completion.algebraMap_toCompletion,
      NumberField.InfinitePlace.Completion.algebraMap_toCompletion,
      UniformSpace.Completion.algebraMap_def, UniformSpace.Completion.algebraMap_def,
      IsScalarTower.algebraMap_apply K L (WithAbs w.1)]

private def psiFactor (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    (v.Completion ⊗[K] L) →ₐ[v.Completion] w.Completion :=
  Algebra.TensorProduct.lift (Algebra.ofId v.Completion w.Completion)
    (IsScalarTower.toAlgHom K L w.Completion) (fun _ _ => Commute.all _ _)

omit [NumberField K] [NumberField L] in
@[scoped simp] private theorem psiFactor_tmul (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1]
    (c : v.Completion) (l : L) :
    psiFactor v w (c ⊗ₜ[K] l) = algebraMap v.Completion w.Completion c * algebraMap L w.Completion l := by
  simp [psiFactor, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply,
    IsScalarTower.coe_toAlgHom']

omit [NumberField K] [NumberField L] in
private theorem psiFactor_one_tmul (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] (l : L) :
    psiFactor v w ((1 : v.Completion) ⊗ₜ[K] l) = algebraMap L w.Completion l := by
  rw [psiFactor_tmul, map_one, one_mul]

@[reducible] private def nontriviallyNormedCompletion (v : InfinitePlace K) :
    NontriviallyNormedField v.Completion :=
  NontriviallyNormedField.ofNormNeOne (by
    have h2 : ‖(2 : v.Completion)‖ = 2 := by
      rw [← (Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _), map_ofNat]
      exact Complex.norm_two
    refine ⟨2, ?_, ?_⟩
    · exact norm_ne_zero_iff.mp (by rw [h2]; norm_num)
    · rw [h2]; norm_num)

omit [NumberField L] in
private theorem denseRange_algebraMap_completion (w : InfinitePlace L) :
    DenseRange (algebraMap L w.Completion) := by
  have h := UniformSpace.Completion.denseRange_coe (α := WithAbs w.1)
  exact (NumberField.InfinitePlace.Completion.ofCompletion_surjective w).denseRange.comp
    (h.comp (WithAbs.equiv w.1).symm.surjective.denseRange (UniformSpace.Completion.continuous_coe _))
    (NumberField.InfinitePlace.Completion.continuous_ofCompletion w)

private theorem psiFactor_surjective (v : InfinitePlace K) (w : InfinitePlace L) [w.1.LiesOver v.1] :
    Function.Surjective (psiFactor v w) := by
  letI : NontriviallyNormedField v.Completion := nontriviallyNormedCompletion v
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : FiniteDimensional v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  set S : Submodule v.Completion w.Completion := LinearMap.range (psiFactor v w).toLinearMap with hS
  haveI : FiniteDimensional v.Completion ↥S := inferInstance
  have hclosed : IsClosed (S : Set w.Completion) := S.closed_of_finiteDimensional
  have hsub : Set.range (algebraMap L w.Completion) ⊆ (S : Set w.Completion) := by
    rintro - ⟨l, rfl⟩
    exact ⟨(1 : v.Completion) ⊗ₜ[K] l, psiFactor_one_tmul v w l⟩
  have htop : (S : Set w.Completion) = Set.univ := by
    have hdense := (denseRange_algebraMap_completion w).mono hsub
    have h1 := hdense.closure_eq
    rwa [hclosed.closure_eq] at h1
  intro y
  have : y ∈ (S : Set w.Completion) := htop ▸ Set.mem_univ y
  exact this

omit [NumberField L] in
private theorem norm_algebraMap_completion (w : InfinitePlace L) (l : L) :
    ‖algebraMap L w.Completion l‖ = w l := by
  have he : algebraMap L w.Completion l = ((WithAbs.equiv w.1).symm l : w.Completion) := rfl
  rw [he, Completion.norm_coe]
  rfl

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in
set_option synthInstance.maxHeartbeats 320000 in
private theorem aux_ker_ne (v : InfinitePlace K) (w w' : InfinitePlace L)
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] {x : L} (hx : w x < 1) (hx' : ¬ w' x < 1) :
    RingHom.ker (psiFactor v w) ≠ RingHom.ker (psiFactor v w') := by
  intro hker
  letI : NontriviallyNormedField v.Completion := nontriviallyNormedCompletion v
  haveI := finiteDimensional_completion v w
  haveI := finiteDimensional_completion v w'

  let e₁ := Ideal.quotientKerAlgEquivOfSurjective (psiFactor_surjective v w)
  let e₂ := Ideal.quotientKerAlgEquivOfSurjective (psiFactor_surjective v w')
  let em : ((v.Completion ⊗[K] L) ⧸ RingHom.ker (psiFactor v w)) ≃ₐ[v.Completion]
      ((v.Completion ⊗[K] L) ⧸ RingHom.ker (psiFactor v w')) :=
    Ideal.quotientEquivAlgOfEq v.Completion hker
  let φ : w.Completion ≃ₐ[v.Completion] w'.Completion := (e₁.symm.trans em).trans e₂
  have hφcont : Continuous φ := φ.toLinearMap.continuous_of_finiteDimensional
  have hφψ : ∀ a : v.Completion ⊗[K] L, φ (psiFactor v w a) = psiFactor v w' a := by
    intro a
    have h0 : e₁.symm (psiFactor v w a) = Ideal.Quotient.mk _ a :=
      e₁.toEquiv.symm_apply_eq.mpr
        (Ideal.quotientKerAlgEquivOfSurjective_mk (psiFactor_surjective v w) a).symm
    show e₂ (em (e₁.symm (psiFactor v w a))) = _
    rw [h0]
    have hem : em (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := by
      simp [em, Ideal.quotientEquivAlgOfEq]
    rw [hem]
    exact Ideal.quotientKerAlgEquivOfSurjective_mk (psiFactor_surjective v w') a
  have hφalg : ∀ l : L, φ (algebraMap L w.Completion l) = algebraMap L w'.Completion l := by
    intro l
    rw [← psiFactor_one_tmul v w l, hφψ, psiFactor_one_tmul]

  have h1 : Filter.Tendsto (fun n : ℕ => (algebraMap L w.Completion x) ^ n)
      Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mpr
      (by rw [norm_algebraMap_completion]; exact hx)
  have h2 : Filter.Tendsto (fun n : ℕ => (algebraMap L w'.Completion x) ^ n)
      Filter.atTop (nhds 0) := by
    have := (hφcont.tendsto 0).comp h1
    simp only [Function.comp_def, map_pow, hφalg, map_zero] at this
    exact this
  have h3 : ‖algebraMap L w'.Completion x‖ < 1 :=
    (tendsto_pow_atTop_nhds_zero_iff_norm_lt_one).mp h2
  rw [norm_algebraMap_completion] at h3
  exact hx' h3

private theorem ker_psiFactor_ne (v : InfinitePlace K) (w w' : InfinitePlace L)
    [w.1.LiesOver v.1] [w'.1.LiesOver v.1] (hne : w ≠ w') :
    RingHom.ker (psiFactor v w) ≠ RingHom.ker (psiFactor v w') := by
  have hnequiv : ¬ w.1.IsEquiv w'.1 := fun h => hne (eq_iff_isEquiv.mpr h)
  rw [AbsoluteValue.isEquiv_iff_lt_one_iff] at hnequiv
  push Not at hnequiv
  obtain ⟨x, hx⟩ := hnequiv
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact aux_ker_ne v w w' h1 (not_lt.mpr h2)
  · exact (aux_ker_ne v w' w h2 (not_lt.mpr h1)).symm

omit [NumberField K] [NumberField L] in

private theorem extLiesOver (v : InfinitePlace K) (w : v.Extension L) : w.1.1.LiesOver v.1 :=
  liesOver_of_comap_eq w.2

attribute [local instance] extLiesOver

private def psi (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) →ₐ[v.Completion]
      ((w : v.Extension L) → w.1.Completion) :=
  Pi.algHom _ _ (fun w => psiFactor v w.1)

omit [NumberField K] [NumberField L] in
@[scoped simp] private theorem psi_apply (v : InfinitePlace K) (z : v.Completion ⊗[K] L) (w : v.Extension L) :
    psi v z w = psiFactor v w.1 z := rfl

set_option maxHeartbeats 3200000 in
private theorem psi_surjective (v : InfinitePlace K) : Function.Surjective (psi (K := K) (L := L) v) := by
  classical
  intro y

  have hsurj : ∀ w : v.Extension L, ∃ a, psiFactor v w.1 a = y w := fun w =>
    psiFactor_surjective v w.1 (y w)
  choose xw hxw using hsurj

  haveI hmax : ∀ w : v.Extension L, (RingHom.ker (psiFactor v w.1)).IsMaximal :=
    fun w => RingHom.ker_isMaximal_of_surjective _ (psiFactor_surjective v w.1)
  have hcop : ∀ w w' : v.Extension L, w ≠ w' →
      IsCoprime (RingHom.ker (psiFactor v w.1))
        (RingHom.ker (psiFactor v w'.1)) := fun w w' hne =>
    Ideal.isCoprime_of_isMaximal (ker_psiFactor_ne v w.1 w'.1 (fun h => hne (Subtype.ext h)))

  obtain ⟨zq, hzq⟩ := Ideal.quotientInfToPiQuotient_surj
    (I := fun w : v.Extension L => RingHom.ker (psiFactor v w.1)) hcop
    (fun w => Ideal.Quotient.mk _ (xw w))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective zq
  refine ⟨a, ?_⟩
  funext w
  have hcomp := congrFun hzq w
  rw [Ideal.quotientInfToPiQuotient_mk'] at hcomp
  have hmem : a - xw w ∈ RingHom.ker (psiFactor v w.1) :=
    Ideal.Quotient.eq.mp hcomp
  have hval : psiFactor v w.1 a = psiFactor v w.1 (xw w) := by
    have h0 : psiFactor v w.1 (a - xw w) = 0 := hmem
    rw [map_sub, sub_eq_zero] at h0
    exact h0
  rw [psi_apply, hval]
  exact hxw w

private def extensionEquivPlacesOver (v : InfinitePlace K) : v.Extension L ≃ ↥(v.placesOver L) where
  toFun w := ⟨w.1, liesOver_of_comap_eq w.2⟩
  invFun w := ⟨w.1, by haveI : w.1.1.LiesOver v.1 := w.2; exact LiesOver.comap_eq w.1 v⟩
  left_inv w := Subtype.ext rfl
  right_inv w := Subtype.ext rfl

private theorem finrank_pi_extension (v : InfinitePlace K) :
    Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion)
      = Module.finrank K L := by
  classical
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype v.Completion]
  rw [← sum_inertiaDeg_eq_finrank K L v]
  rw [← Finset.sum_coe_sort ((placesOver L v).toFinset) (fun w => v.inertiaDeg w)]
  let E : v.Extension L ≃ {w : InfinitePlace L // w ∈ (placesOver L v).toFinset} :=
    { toFun := fun w =>
        ⟨w.1, Set.mem_toFinset.mpr
          (show (w.1 : InfinitePlace L) ∈ placesOver L v from extLiesOver v w)⟩
      invFun := fun w =>
        have hmem : (w.1 : InfinitePlace L) ∈ placesOver L v := Set.mem_toFinset.mp w.2
        haveI : w.1.1.LiesOver v.1 := hmem
        ⟨w.1, LiesOver.comap_eq w.1 v⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl }
  exact Fintype.sum_equiv E _ _ (fun w => (inertiaDeg_eq_finrank v w.1).symm)

private theorem psi_bijective (v : InfinitePlace K) : Function.Bijective (psi (K := K) (L := L) v) := by
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : Module.Finite v.Completion ((w : v.Extension L) → w.1.Completion) :=
    Module.Finite.pi
  haveI : FiniteDimensional v.Completion (v.Completion ⊗[K] L) :=
    Module.Finite.base_change K v.Completion L
  have hdim : Module.finrank v.Completion (v.Completion ⊗[K] L)
      = Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion) := by
    rw [Module.finrank_baseChange, finrank_pi_extension]
  have hsurjL : Function.Surjective (psi (K := K) (L := L) v).toLinearMap :=
    psi_surjective v
  have hinjL :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurjL
  exact ⟨hinjL, psi_surjective v⟩

private def placeEquivAlg (v : InfinitePlace K) :
    (v.Completion ⊗[K] L) ≃ₐ[v.Completion] ((w : v.Extension L) → w.1.Completion) :=
  AlgEquiv.ofBijective (psi v) (psi_bijective v)

private def genuineInfinitePlaceData : FLT.InfiniteAdeleBaseChange.InfinitePlaceData K L where
  placeEquiv v := (placeEquivAlg (K := K) (L := L) v).toRingEquiv
  placeEquiv_one_tmul v l w := psiFactor_one_tmul v w.1 l

omit [NumberField K] [NumberField L] in
private theorem continuous_algebraMap_completion (v : InfinitePlace K) (w : InfinitePlace L)
    [w.1.LiesOver v.1] : Continuous (algebraMap v.Completion w.Completion) := by
  have he : (algebraMap v.Completion w.Completion : v.Completion → w.Completion)
      = fun c => c • (1 : w.Completion) := by
    funext c
    rw [Algebra.algebraMap_eq_smul_one]
  rw [he]
  exact continuous_id.smul continuous_const

set_option maxHeartbeats 1600000 in
private theorem continuous_conorm :
    Continuous (genuineInfinitePlaceData (K := K) (L := L)).conorm := by
  refine continuous_pi fun w => ?_
  haveI : w.1.LiesOver (w.comap (algebraMap K L)).1 := liesOver_of_comap_eq rfl
  have hcomp : (fun x : InfiniteAdeleRing K =>
      (genuineInfinitePlaceData (K := K) (L := L)).conorm x w)
      = fun x => algebraMap ((w.comap (algebraMap K L)).Completion) w.Completion
          (x (w.comap (algebraMap K L))) := by
    funext x
    show psiFactor (w.comap (algebraMap K L)) w
        ((x (w.comap (algebraMap K L))) ⊗ₜ[K] (1 : L)) = _
    rw [psiFactor_tmul, map_one, mul_one]
  rw [hcomp]
  exact (continuous_algebraMap_completion _ w).comp (continuous_apply _)

end
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

end M4aHerbrand.ArchSemilocal
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TensorProduct RestrictedProduct

open scoped TensorProduct RestrictedProduct

set_option synthInstance.maxHeartbeats 1600000
set_option maxSynthPendingDepth 3

section AKLB

variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]
    [FiniteDimensional K L] [Module.Finite A B]

section shortcut_instances

variable (v : HeightOneSpectrum A) (w' : HeightOneSpectrum B)

private scoped instance : IsUniformAddGroup (WithVal (v.valuation K)) := inferInstance
private noncomputable scoped instance : AddCommGroup (v.adicCompletion K) := inferInstance
private noncomputable scoped instance : AddCommMonoid (v.adicCompletion K) := inferInstance
private noncomputable scoped instance : CommRing (v.adicCompletion K) := inferInstance
private noncomputable scoped instance : Ring (v.adicCompletion K) := inferInstance
private noncomputable scoped instance : Module A (v.adicCompletion K) := inferInstance
private noncomputable scoped instance : AddCommGroup (B ⊗[A] v.adicCompletion K) := inferInstance
private noncomputable scoped instance : AddCommMonoid (B ⊗[A] v.adicCompletion K) := inferInstance
private noncomputable scoped instance : CommRing (B ⊗[A] v.adicCompletion K) := inferInstance
private noncomputable scoped instance : Module B (B ⊗[A] v.adicCompletion K) := inferInstance
private scoped instance : IsUniformAddGroup (WithVal (w'.valuation L)) := inferInstance
private noncomputable scoped instance : AddCommGroup (w'.adicCompletion L) := inferInstance
private noncomputable scoped instance : AddCommMonoid (w'.adicCompletion L) := inferInstance
private noncomputable scoped instance : CommRing (w'.adicCompletion L) := inferInstance
private noncomputable scoped instance : Ring (w'.adicCompletion L) := inferInstance
private noncomputable scoped instance : AddCommGroup ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance
private noncomputable scoped instance : AddCommMonoid ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance
private noncomputable scoped instance : CommRing ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance
private noncomputable scoped instance : Module B ((w : v.Extension B) → w.1.adicCompletion L) := inferInstance

end shortcut_instances
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

private theorem finiteAdeleRing_mul_apply (x y : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    (x * y) v = x v * y v := rfl

private theorem finiteAdeleRing_one_apply (v : HeightOneSpectrum A) : (1 : FiniteAdeleRing A K) v = 1 := rfl

private def moduleStructureBridge :
    (FiniteAdeleRing A K) ≃ₗ[A]
      (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, adicCompletion.integerSubmodule K v]) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    ext v : 1
    change ((a • x : FiniteAdeleRing A K) v) = a • (x v)
    rw [Algebra.smul_def a (x v)]
    rw [show (a • x : FiniteAdeleRing A K) = algebraMap A (FiniteAdeleRing A K) a * x from
      Algebra.smul_def a x]
    rw [finiteAdeleRing_mul_apply]
    congr 1
  left_inv _ := rfl
  right_inv _ := rfl

@[scoped simp] private theorem moduleStructureBridge_apply (x : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    moduleStructureBridge A K x v = x v := rfl

include K L in
omit [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [FiniteDimensional K L] [Module.Finite A B] in
private theorem flat_of_aklb : Module.Flat A B := by
  haveI := HeightOneSpectrum.isTorsionFree A K L B
  infer_instance

private def tensorComponents :
    (B ⊗[A] (FiniteAdeleRing A K)) ≃ₗ[B]
      (Πʳ v : HeightOneSpectrum A, [B ⊗[A] (v.adicCompletion K),
        rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) v]) :=
  haveI := flat_of_aklb A K L B
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) (moduleStructureBridge A K)).trans
    (lTensorEquivLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
      (fun u => adicCompletion.integerSubmodule K u) Filter.cofinite)

omit [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [FiniteDimensional K L] in
private theorem tensorComponents_tmul (b : B) (x : FiniteAdeleRing A K) (v : HeightOneSpectrum A) :
    tensorComponents A K L B (b ⊗ₜ x) v = b ⊗ₜ (x v) := by
  haveI := flat_of_aklb A K L B
  haveI : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  rw [show tensorComponents A K L B (b ⊗ₜ x)
      = lTensorEquivLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) Filter.cofinite
          ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B)
            (moduleStructureBridge A K)) (b ⊗ₜ x)) from rfl]
  rw [TensorProduct.AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply, lTensorEquivLeft_tmul,
    moduleStructureBridge_apply]

set_option maxHeartbeats 3200000 in
omit [IsIntegralClosure B A L] [Algebra.IsIntegral A B] [IsFractionRing B L] [FiniteDimensional K L] in
private theorem tensorComponents_mul_apply (z₁ z₂ : B ⊗[A] (FiniteAdeleRing A K)) (v : HeightOneSpectrum A) :
    tensorComponents A K L B (z₁ * z₂) v
      = tensorComponents A K L B z₁ v * tensorComponents A K L B z₂ v := by
  induction z₁ using TensorProduct.induction_on with
  | zero =>
    rw [zero_mul, map_zero, RestrictedProduct.zero_apply, zero_mul]
  | add u₁ u₂ h₁ h₂ =>
    rw [add_mul, map_add, map_add, RestrictedProduct.add_apply, RestrictedProduct.add_apply,
      h₁, h₂, add_mul]
  | tmul b₁ x₁ =>
    induction z₂ using TensorProduct.induction_on with
    | zero =>
      rw [mul_zero, map_zero, RestrictedProduct.zero_apply, mul_zero]
    | add u₁ u₂ h₁ h₂ =>
      rw [mul_add, map_add, map_add, RestrictedProduct.add_apply, RestrictedProduct.add_apply,
        h₁, h₂, mul_add]
    | tmul b₂ x₂ =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tensorComponents_tmul, tensorComponents_tmul,
        tensorComponents_tmul, finiteAdeleRing_mul_apply, Algebra.TensorProduct.tmul_mul_tmul]

omit [IsIntegralClosure B A L] in

private theorem integerBaseChangeLinearEquiv_mul (v : HeightOneSpectrum A) (s t : B ⊗[A] (v.adicCompletion K)) :
    adicCompletion.integerBaseChangeLinearEquiv K L B v (s * t) =
      adicCompletion.integerBaseChangeLinearEquiv K L B v s *
        adicCompletion.integerBaseChangeLinearEquiv K L B v t := by
  induction s using TensorProduct.induction_on with
  | zero => rw [zero_mul, LinearEquiv.map_zero, zero_mul]
  | add u₁ u₂ h₁ h₂ => rw [add_mul, LinearEquiv.map_add, h₁, h₂, LinearEquiv.map_add, add_mul]
  | tmul b₁ x₁ =>
    induction t using TensorProduct.induction_on with
    | zero => rw [mul_zero, LinearEquiv.map_zero, mul_zero]
    | add u₁ u₂ h₁ h₂ => rw [mul_add, LinearEquiv.map_add, h₁, h₂, LinearEquiv.map_add, mul_add]
    | tmul b₂ x₂ =>
      funext w
      rw [Algebra.TensorProduct.tmul_mul_tmul, Pi.mul_apply,
        adicCompletion.integerBaseChangeLinearEquiv_tmul_apply,
        adicCompletion.integerBaseChangeLinearEquiv_tmul_apply,
        adicCompletion.integerBaseChangeLinearEquiv_tmul_apply, RingHom.map_mul, RingHom.map_mul]
      ring

omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [Module.Finite A B] in

private theorem rangeLTensorLeft_eq_range_tensorCoe (v : HeightOneSpectrum A) :
    ((rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
        (fun u => adicCompletion.integerSubmodule K u) v :
          Submodule B (B ⊗[A] (v.adicCompletion K))) : Set (B ⊗[A] (v.adicCompletion K))) =
      Set.range (adicCompletionIntegers.tensorCoe K B v) := by
  rw [← LinearMap.coe_range]
  refine SetLike.coe_set_eq.mpr ?_
  apply le_antisymm
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add u₁ u₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | tmul b y =>
      rw [TensorProduct.AlgebraTensorModule.lTensor_tmul]
      exact ⟨b ⊗ₜ ⟨y.1, y.2⟩, rfl⟩
  · rintro _ ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add u₁ u₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | tmul b y =>
      rw [adicCompletionIntegers.tensorCoe_tmul]
      exact ⟨b ⊗ₜ ⟨y.1, y.2⟩, rfl⟩

omit [Algebra A L] [IsScalarTower A B L] [IsIntegralClosure B A L] [Module.Finite A B] in

private theorem coe_pi_integerSubmodule (v : HeightOneSpectrum A) :
    ((Submodule.pi Set.univ fun (w : v.Extension B) => adicCompletion.integerSubmodule L w.1 :
        Submodule B ((w : v.Extension B) → w.1.adicCompletion L)) :
          Set ((w : v.Extension B) → w.1.adicCompletion L)) =
      Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L)) :=
  Set.ext fun _ => Iff.rfl

omit [IsIntegralClosure B A L] in

private theorem integerBaseChangeLinearEquiv_bijOn' (v : HeightOneSpectrum A) :
    Set.BijOn (adicCompletion.integerBaseChangeLinearEquiv K L B v)
      ((rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
        (fun u => adicCompletion.integerSubmodule K u) v :
          Submodule B (B ⊗[A] (v.adicCompletion K))) : Set (B ⊗[A] (v.adicCompletion K)))
      (Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))) := by
  rw [rangeLTensorLeft_eq_range_tensorCoe, ← coe_pi_integerSubmodule]
  exact adicCompletion.integerBaseChangeLinearEquiv_bijOn K L v

private def congrPlaces :
    (Πʳ v : HeightOneSpectrum A, [B ⊗[A] (v.adicCompletion K),
        rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) v])
      ≃ (Πʳ v : HeightOneSpectrum A, [(w : v.Extension B) → w.1.adicCompletion L,
        Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))]) :=
  Equiv.restrictedProductCongrRight
    (fun v => (adicCompletion.integerBaseChangeLinearEquiv K L B v).toEquiv)
    (Filter.Eventually.of_forall fun v => integerBaseChangeLinearEquiv_bijOn' A K L B v)

omit [IsIntegralClosure B A L] in
@[scoped simp] private theorem congrPlaces_apply
    (x : Πʳ v : HeightOneSpectrum A, [B ⊗[A] (v.adicCompletion K),
        rangeLTensorLeft A B (fun (u : HeightOneSpectrum A) => u.adicCompletion K)
          (fun u => adicCompletion.integerSubmodule K u) v])
    (v : HeightOneSpectrum A) :
    congrPlaces A K L B x v = adicCompletion.integerBaseChangeLinearEquiv K L B v (x v) := rfl

private def flattenPlaces :
    (Πʳ v : HeightOneSpectrum A, [(w : v.Extension B) → w.1.adicCompletion L,
        Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))])
      ≃ FiniteAdeleRing B L :=
  RestrictedProduct.flatten_equiv'
    (fun w : HeightOneSpectrum B => ((w.adicCompletionIntegers L : Set (w.adicCompletion L))))
    (tendsto_under_cofinite A K L B)

omit [IsIntegralClosure B A L] [FiniteDimensional K L] [Module.Finite A B] in
@[scoped simp] private theorem flattenPlaces_apply
    (x : Πʳ v : HeightOneSpectrum A, [(w : v.Extension B) → w.1.adicCompletion L,
        Set.univ.pi fun (w : v.Extension B) => (w.1.adicCompletionIntegers L : Set (w.1.adicCompletion L))])
    (w : HeightOneSpectrum B) :
    flattenPlaces A K L B x w = x (w.under A) (⟨w, rfl⟩ : (w.under A).Extension B) := rfl

private def tensorAdeleEquiv : (B ⊗[A] (FiniteAdeleRing A K)) ≃ (FiniteAdeleRing B L) :=
  (tensorComponents A K L B).toEquiv.trans ((congrPlaces A K L B).trans (flattenPlaces A K L B))

omit [IsIntegralClosure B A L] in
private theorem tensorAdeleEquiv_apply (z : B ⊗[A] (FiniteAdeleRing A K)) (w : HeightOneSpectrum B) :
    tensorAdeleEquiv A K L B z w =
      adicCompletion.integerBaseChangeLinearEquiv K L B (w.under A)
        (tensorComponents A K L B z (w.under A)) (⟨w, rfl⟩ : (w.under A).Extension B) := rfl

private def tensorAdeleRingEquiv : (B ⊗[A] (FiniteAdeleRing A K)) ≃+* (FiniteAdeleRing B L) where
  toEquiv := tensorAdeleEquiv A K L B
  map_mul' z₁ z₂ := by
    show tensorAdeleEquiv A K L B (z₁ * z₂) = tensorAdeleEquiv A K L B z₁ * tensorAdeleEquiv A K L B z₂
    apply FiniteAdeleRing.ext
    intro w
    rw [finiteAdeleRing_mul_apply, tensorAdeleEquiv_apply, tensorAdeleEquiv_apply, tensorAdeleEquiv_apply,
      tensorComponents_mul_apply, integerBaseChangeLinearEquiv_mul, Pi.mul_apply]
  map_add' z₁ z₂ := by
    show tensorAdeleEquiv A K L B (z₁ + z₂) = tensorAdeleEquiv A K L B z₁ + tensorAdeleEquiv A K L B z₂
    apply FiniteAdeleRing.ext
    intro w
    rw [show ((tensorAdeleEquiv A K L B z₁ + tensorAdeleEquiv A K L B z₂ : FiniteAdeleRing B L) w)
        = tensorAdeleEquiv A K L B z₁ w + tensorAdeleEquiv A K L B z₂ w from rfl,
      tensorAdeleEquiv_apply, tensorAdeleEquiv_apply, tensorAdeleEquiv_apply, map_add,
      RestrictedProduct.add_apply, map_add, Pi.add_apply]

omit [IsIntegralClosure B A L] in
@[scoped simp] private theorem tensorAdeleRingEquiv_apply (z : B ⊗[A] (FiniteAdeleRing A K)) :
    tensorAdeleRingEquiv A K L B z = tensorAdeleEquiv A K L B z := rfl

omit [IsIntegralClosure B A L] in
private theorem tensorAdeleRingEquiv_tmul_apply (b : B) (x : FiniteAdeleRing A K) (w : HeightOneSpectrum B) :
    tensorAdeleRingEquiv A K L B (b ⊗ₜ x) w =
      algebraMap B (w.adicCompletion L) b *
        Extension.adicCompletionSemialgHom K L (⟨w, rfl⟩ : (w.under A).Extension B) (x (w.under A)) := by
  rw [tensorAdeleRingEquiv_apply, tensorAdeleEquiv_apply, tensorComponents_tmul,
    adicCompletion.integerBaseChangeLinearEquiv_tmul_apply]
  rfl

omit [IsIntegralClosure B A L] in
private theorem tensorAdeleRingEquiv_one_tmul (x : FiniteAdeleRing A K) :
    tensorAdeleRingEquiv A K L B ((1 : B) ⊗ₜ x) = finiteConorm A K L B x := by
  apply FiniteAdeleRing.ext
  intro w
  rw [tensorAdeleRingEquiv_tmul_apply, map_one, one_mul, finiteConorm_apply]

private def integralTensorRingEquiv : (B ⊗[A] (FiniteAdeleRing A K)) ≃+* (L ⊗[K] (FiniteAdeleRing A K)) where
  toFun := (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K)).symm
  invFun := (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K))
  left_inv z :=
    (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K)).apply_symm_apply z
  right_inv z :=
    (IsDedekindDomain.linearEquivTensorProductModuleLeft A K L B (FiniteAdeleRing A K)).symm_apply_apply z
  map_add' z₁ z₂ := map_add _ z₁ z₂
  map_mul' z₁ z₂ := by
    induction z₁ using TensorProduct.induction_on with
    | zero => rw [zero_mul, map_zero, zero_mul]
    | add u₁ u₂ h₁ h₂ => rw [add_mul, map_add, h₁, h₂, map_add, add_mul]
    | tmul b₁ m₁ =>
      induction z₂ using TensorProduct.induction_on with
      | zero => rw [mul_zero, map_zero, mul_zero]
      | add u₁ u₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂, map_add, mul_add]
      | tmul b₂ m₂ =>
        rw [Algebra.TensorProduct.tmul_mul_tmul,
          IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul,
          IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul,
          IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul,
          Algebra.TensorProduct.tmul_mul_tmul, map_mul]

omit [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B] [Module.Finite A B] in
@[scoped simp] private theorem integralTensorRingEquiv_tmul (b : B) (m : FiniteAdeleRing A K) :
    integralTensorRingEquiv A K L B (b ⊗ₜ m) = (algebraMap B L b) ⊗ₜ m :=
  IsDedekindDomain.linearEquivTensorProductModuleLeft_symm_tmul A K L B (FiniteAdeleRing A K) b m

omit [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B] [Module.Finite A B] in
private theorem integralTensorRingEquiv_symm_algebraMap_tmul (b : B) (m : FiniteAdeleRing A K) :
    (integralTensorRingEquiv A K L B).symm ((algebraMap B L b) ⊗ₜ m) = b ⊗ₜ m := by
  rw [RingEquiv.symm_apply_eq, integralTensorRingEquiv_tmul]

omit [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B] [Module.Finite A B] in
private theorem integralTensorRingEquiv_symm_one_tmul (m : FiniteAdeleRing A K) :
    (integralTensorRingEquiv A K L B).symm ((1 : L) ⊗ₜ m) = (1 : B) ⊗ₜ m := by
  have h := integralTensorRingEquiv_symm_algebraMap_tmul A K L B 1 m
  rwa [map_one] at h

private def finiteBaseChangeRingEquiv : ((FiniteAdeleRing A K) ⊗[K] L) ≃+* (FiniteAdeleRing B L) :=
  ((Algebra.TensorProduct.comm K (FiniteAdeleRing A K) L).toRingEquiv.trans
    (integralTensorRingEquiv A K L B).symm).trans (tensorAdeleRingEquiv A K L B)

private theorem finiteBaseChangeRingEquiv_apply (z : (FiniteAdeleRing A K) ⊗[K] L) :
    finiteBaseChangeRingEquiv A K L B z =
      tensorAdeleRingEquiv A K L B ((integralTensorRingEquiv A K L B).symm
        ((Algebra.TensorProduct.comm K (FiniteAdeleRing A K) L) z)) := rfl

private theorem finiteBaseChangeRingEquiv_tmul_one (x : FiniteAdeleRing A K) :
    finiteBaseChangeRingEquiv A K L B (x ⊗ₜ (1 : L)) = finiteConorm A K L B x := by
  rw [finiteBaseChangeRingEquiv_apply, Algebra.TensorProduct.comm_tmul,
    integralTensorRingEquiv_symm_one_tmul, tensorAdeleRingEquiv_one_tmul]

private theorem finiteBaseChangeRingEquiv_one_tmul_algebraMap (b : B) :
    finiteBaseChangeRingEquiv A K L B ((1 : FiniteAdeleRing A K) ⊗ₜ (algebraMap B L b)) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap B L b) := by
  rw [finiteBaseChangeRingEquiv_apply, Algebra.TensorProduct.comm_tmul,
    integralTensorRingEquiv_symm_algebraMap_tmul]
  apply FiniteAdeleRing.ext
  intro w
  rw [tensorAdeleRingEquiv_tmul_apply, finiteAdeleRing_one_apply, map_one, mul_one,
    FiniteAdeleRing.algebraMap_apply, IsScalarTower.algebraMap_apply B L (w.adicCompletion L)]
  rfl

private theorem finiteBaseChangeRingEquiv_one_tmul (l : L) :
    finiteBaseChangeRingEquiv A K L B ((1 : FiniteAdeleRing A K) ⊗ₜ l) =
      algebraMap L (FiniteAdeleRing B L) l := by
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := B) l
  have hy0 : algebraMap B L y ≠ 0 := fun h =>
    nonZeroDivisors.ne_zero hy (IsFractionRing.injective B L (by rw [h, map_zero]))
  have hl : l * algebraMap B L y = algebraMap B L x := by
    rw [← hxy, div_mul_cancel₀ _ hy0]
  have ht : ((1 : FiniteAdeleRing A K) ⊗ₜ[K] l) * (1 ⊗ₜ (algebraMap B L y)) =
      (1 : FiniteAdeleRing A K) ⊗ₜ (algebraMap B L x) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hl]
  have happ := congrArg (finiteBaseChangeRingEquiv A K L B) ht
  rw [map_mul, finiteBaseChangeRingEquiv_one_tmul_algebraMap,
    finiteBaseChangeRingEquiv_one_tmul_algebraMap] at happ
  have hr : algebraMap L (FiniteAdeleRing B L) l *
      algebraMap L (FiniteAdeleRing B L) (algebraMap B L y) =
      algebraMap L (FiniteAdeleRing B L) (algebraMap B L x) := by
    rw [← map_mul, hl]
  have hu : IsUnit (algebraMap L (FiniteAdeleRing B L) (algebraMap B L y)) :=
    (IsUnit.mk0 _ hy0).map (algebraMap L (FiniteAdeleRing B L))
  exact hu.mul_right_cancel (happ.trans hr.symm)

private def finiteTensorEquiv :
    letI := (finiteConorm A K L B).toAlgebra
    ((FiniteAdeleRing A K) ⊗[K] L) ≃ₐ[FiniteAdeleRing A K] (FiniteAdeleRing B L) :=
  letI := (finiteConorm A K L B).toAlgebra
  AlgEquiv.ofRingEquiv (f := finiteBaseChangeRingEquiv A K L B) (fun x => by
    rw [show algebraMap (FiniteAdeleRing A K) ((FiniteAdeleRing A K) ⊗[K] L) x = x ⊗ₜ 1 from rfl]
    rw [finiteBaseChangeRingEquiv_tmul_one]
    rfl)

private theorem finiteTensorEquiv_apply (z : (FiniteAdeleRing A K) ⊗[K] L) :
    finiteTensorEquiv A K L B z = finiteBaseChangeRingEquiv A K L B z := rfl

private theorem finiteTensorEquiv_one_tmul (l : L) :
    finiteTensorEquiv A K L B ((1 : FiniteAdeleRing A K) ⊗ₜ l) = algebraMap L (FiniteAdeleRing B L) l :=
  finiteBaseChangeRingEquiv_one_tmul A K L B l

private theorem finiteTensorEquiv_tmul_one (x : FiniteAdeleRing A K) :
    finiteTensorEquiv A K L B (x ⊗ₜ (1 : L)) = finiteConorm A K L B x :=
  finiteBaseChangeRingEquiv_tmul_one A K L B x

end AKLB
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end M4aHerbrand.Bridge
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain M4aHerbrand.ArchSemilocal

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def genuineβ : AdeleRing (𝓞 K) K →+* AdeleRing (𝓞 L) L :=
  RingHom.prodMap (genuineInfinitePlaceData (K := K) (L := L)).conorm (finiteConorm (𝓞 K) K L (𝓞 L))

private theorem continuous_genuineβ : Continuous (genuineβ K L) :=
  Continuous.prodMap continuous_conorm (continuous_finiteConorm (𝓞 K) K L (𝓞 L))

private theorem genuineβ_compat (e : K) :
    genuineβ K L (algebraMap K (AdeleRing (𝓞 K) K) e) = algebraMap L (AdeleRing (𝓞 L) L) (algebraMap K L e) :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).conorm_algebraMap e)
    (finiteConorm_algebraMap (𝓞 K) K L (𝓞 L) e)

end Genuine
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end M4aHerbrand.Bridge
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace Bridge
p2m_open "M4aHerbrand"

open NumberField IsDedekindDomain TensorProduct M4aHerbrand.ArchSemilocal

open scoped TensorProduct

section ProdSplit

variable (K P Q L : Type*) [CommRing K] [CommRing P] [CommRing Q] [CommRing L]
  [Algebra K P] [Algebra K Q] [Algebra K L]

private theorem prodLeft_tmul_proj (x : P × Q) (l : L) :
    TensorProduct.prodLeft K K P Q L (x ⊗ₜ[K] l) = (x.1 ⊗ₜ[K] l, x.2 ⊗ₜ[K] l) := by
  obtain ⟨p, q⟩ := x
  rfl

private def prodTensorAlgEquiv : ((P × Q) ⊗[K] L) ≃ₐ[K] ((P ⊗[K] L) × (Q ⊗[K] L)) :=
  AlgEquiv.ofLinearEquiv (TensorProduct.prodLeft K K P Q L)
    (by
      rw [Algebra.TensorProduct.one_def, prodLeft_tmul_proj]
      exact Prod.ext rfl rfl)
    (fun x y => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul p a =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul q b =>
          simp only [Algebra.TensorProduct.tmul_mul_tmul, prodLeft_tmul_proj,
            Prod.mk_mul_mk, Prod.fst_mul, Prod.snd_mul]
        | add y₁ y₂ h₁ h₂ => simp only [mul_add, map_add, h₁, h₂]
      | add x₁ x₂ h₁ h₂ => simp only [add_mul, map_add, h₁, h₂])

@[scoped simp] private theorem prodTensorAlgEquiv_tmul (x : P × Q) (l : L) :
    prodTensorAlgEquiv K P Q L (x ⊗ₜ[K] l) = (x.1 ⊗ₜ[K] l, x.2 ⊗ₜ[K] l) :=
  prodLeft_tmul_proj K P Q L x l

end ProdSplit
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] in

private theorem moduleFinite_ringOfIntegers : Module.Finite (𝓞 K) (𝓞 L) :=
  Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) (𝓞 L)

attribute [local instance] moduleFinite_ringOfIntegers

private def genuineRingEquiv : ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃+* AdeleRing (𝓞 L) L :=
  ((prodTensorAlgEquiv K (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K) L).toRingEquiv).trans
    (RingEquiv.prodCongr (genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv
      (finiteBaseChangeRingEquiv (𝓞 K) K L (𝓞 L)))

private theorem genuineRingEquiv_one_tmul (l : L) :
    genuineRingEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv_one_tmul l)
    (finiteBaseChangeRingEquiv_one_tmul (𝓞 K) K L (𝓞 L) l)

private theorem genuineRingEquiv_tmul_one (x : AdeleRing (𝓞 K) K) :
    genuineRingEquiv K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  Prod.ext ((genuineInfinitePlaceData (K := K) (L := L)).baseChangeRingEquiv_tmul_one x.1)
    (finiteBaseChangeRingEquiv_tmul_one (𝓞 K) K L (𝓞 L) x.2)

private def genuineTensorEquiv :
    letI := (genuineβ K L).toAlgebra
    ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L :=
  letI := (genuineβ K L).toAlgebra
  AlgEquiv.ofRingEquiv (f := genuineRingEquiv K L) (fun x => by
    exact genuineRingEquiv_tmul_one K L x)

private theorem genuineTensorEquiv_apply (z : (AdeleRing (𝓞 K) K) ⊗[K] L) :
    genuineTensorEquiv K L z = genuineRingEquiv K L z := rfl

private theorem genuineTensorEquiv_one_tmul (l : L) :
    genuineTensorEquiv K L ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l :=
  genuineRingEquiv_one_tmul K L l

private theorem genuineTensorEquiv_tmul_one (x : AdeleRing (𝓞 K) K) :
    genuineTensorEquiv K L (x ⊗ₜ[K] (1 : L)) = genuineβ K L x :=
  genuineRingEquiv_tmul_one K L x

end Genuine
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end M4aHerbrand.Bridge
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

set_option autoImplicit false

noncomputable section

namespace M4aHerbrand
p2m_export "M4aHerbrand" "IdeleGaloisDescent actOf AdeleBaseChange"
namespace H1dGenuine
p2m_open "M4aHerbrand"

p2m_open "NumberField TensorProduct IsDedekindDomain M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge"

section AnyProducer

variable {A K B' L : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [NumberField K] [Algebra A K]
  [IsFractionRing A K] [Module.Free ℤ A] [Module.Finite ℤ A]
  [CommRing B'] [IsDedekindDomain B'] [Field L] [NumberField L] [Algebra B' L] [IsFractionRing B' L]
  [Module.Free ℤ B'] [Module.Finite ℤ B'] [Algebra K L]

private theorem hcont_of_continuous_β (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) :
    ∀ σ : L ≃ₐ[K] L, letI := B.β.toAlgebra; Continuous (actOf A K B' L B.tensorEquiv σ) := by
  letI := B.β.toAlgebra
  intro σ
  exact continuous_conjAct_of_continuous_of_free A K B' L hβ B.tensorEquiv σ

private def descentOfContinuousβ (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) : IdeleGaloisDescent B' K L :=
  B.toIdeleGaloisDescent (hcont_of_continuous_β B hβ)

private theorem descentOfContinuousβ_act (B : AdeleBaseChange A K B' L) (hβ : Continuous B.β) (g : L ≃ₐ[K] L) :
    (descentOfContinuousβ B hβ).act g = letI := B.β.toAlgebra; actOf A K B' L B.tensorEquiv g := rfl

omit [NumberField K] [Module.Free ℤ A] [Module.Finite ℤ A] [NumberField L] [Module.Free ℤ B'] [Module.Finite ℤ B'] in

private theorem continuous_β_of_prodMap (B : AdeleBaseChange A K B' L)
    (βi : InfiniteAdeleRing K →+* InfiniteAdeleRing L) (βf : FiniteAdeleRing A K →+* FiniteAdeleRing B' L)
    (h : B.β = RingHom.prodMap βi βf) (hinf : Continuous βi) (hfin : Continuous βf) : Continuous B.β := by
  rw [h]; exact Continuous.prodMap hinf hfin

end AnyProducer
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"
section RingOfIntegers

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def genuineDescent (B : AdeleBaseChange (𝓞 K) K (𝓞 L) L) (hβ : Continuous B.β) : IdeleGaloisDescent (𝓞 L) K L :=
  descentOfContinuousβ B hβ

end RingOfIntegers
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

section Genuine

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def bgenOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    AdeleBaseChange (𝓞 K) K (𝓞 L) L where
  β := genuineβ K L
  β_compat := genuineβ_compat K L
  tensorEquiv := te
  tensorEquiv_one_tmul := hte

private def genuineDescentOfTensorEquiv
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) :
    IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescent (bgenOfTensorEquiv K L te hte) (continuous_genuineβ K L)

private theorem genuineDescentOfTensorEquiv_act
    (te : letI := (genuineβ K L).toAlgebra;
      ((AdeleRing (𝓞 K) K) ⊗[K] L) ≃ₐ[AdeleRing (𝓞 K) K] AdeleRing (𝓞 L) L)
    (hte : ∀ l : L, letI := (genuineβ K L).toAlgebra;
      te ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] l) = algebraMap L (AdeleRing (𝓞 L) L) l) (g : L ≃ₐ[K] L) :
    (genuineDescentOfTensorEquiv K L te hte).act g =
      letI := (genuineβ K L).toAlgebra; actOf (𝓞 K) K (𝓞 L) L te g := rfl

end Genuine
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

section Inhabitant

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

private def genuineBaseChange : AdeleBaseChange (𝓞 K) K (𝓞 L) L :=
  bgenOfTensorEquiv K L (genuineTensorEquiv K L) (genuineTensorEquiv_one_tmul K L)

private theorem genuineBaseChange_β : (genuineBaseChange K L).β = genuineβ K L := rfl

private def genuineDescentPaid : IdeleGaloisDescent (𝓞 L) K L :=
  genuineDescentOfTensorEquiv K L (genuineTensorEquiv K L) (genuineTensorEquiv_one_tmul K L)

private theorem genuineDescentPaid_act (g : L ≃ₐ[K] L) :
    (genuineDescentPaid K L).act g =
      letI := (genuineβ K L).toAlgebra; actOf (𝓞 K) K (𝓞 L) L (genuineTensorEquiv K L) g := rfl

end Inhabitant
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end M4aHerbrand.H1dGenuine
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

end
p2m_reactivate "P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.Bridge P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent.M4aHerbrand.ArchSemilocal"

open NumberField

theorem solution
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    Nonempty (M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :=
  ⟨M4aHerbrand.H1dGenuine.genuineDescentPaid K L⟩

end S_M4aHerbrand_nonempty_ideleGaloisDescent
end P2MW
export P2MW.S_M4aHerbrand_nonempty_ideleGaloisDescent (solution)
