-- Prove2me | solution 1 for MazurTransfer.original_relative_norm_kernel_hopf_representability
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-21T00:52:13.3452+00:00
-- url     : https://prove2.me/submissions/4c0fbdae-6fed-417e-b1a7-bec06735d80a

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The generic kernel Hopf construction preserves the attribution of its complete official Anthropic FLT group-scheme input at exact pin 6e837e75355538c7f80bab5b956861e86c4eacc2.
Design boundary: the same scheme-theoretic kernel of a given relative group endomorphism has its original point naturality and commutative finite-flat Hopf representation, with every group preservation and finiteness hypothesis retained.
Named downstream consumer: actual integral nineteen norm kernels and their same norm-preimage torsors.
-/
import Definitions.Def_MazurTransfer_OriginalRelativeNormKernelSchemePointsAndGroupLawData20261020
import Theorems.Thm_AlgebraicGeometry_exists_hopfAlgebra_flat_of_grpObj_over_spec
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian NeronModelInfra
open MazurTransfer.RelativeGroupLawFiniteFlatKernelHopf
open scoped CategoryTheory.MonObj
universe u
namespace MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityBoundary20261020
end MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityBoundary20261020
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The kernel group-law and Hopf representability construction adapts the
complete official Anthropic FLT scalar-kernel proof at
6e837e75355538c7f80bab5b956861e86c4eacc2 to a relative group endomorphism.
Design boundary: the ACTUAL scheme-theoretic kernel of a finite-flat
relative endomorphism, with its algebra-valued points, multiplication
and all coefficient base changes; the map must preserve the given law.
Named downstream consumer: the two actual integral nineteen norm kernels.
-/

noncomputable section
namespace MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityProof20261020
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GoodReductionJacobian NeronModelInfra
open scoped CategoryTheory.MonObj
variable {R : Type u} [CommRing R] {A : Scheme.{u}}
variable {f : A ⟶ Spec (CommRingCat.of R)}
variable (L : RelativeGroupLaw R f) (F : SchemeHomOver f f)











section Points
variable {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))











theorem kernelPointsEquiv_natural {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t (kernelStr L F)) :
    (kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (kernelPointsEquiv L F t a).val := by
  apply Subtype.ext
  exact Category.assoc _ _ _
end Points

variable
  (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
    NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t)
  (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) F =
      L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F))







theorem kernelLaw_isCommutative (hc : L.IsCommutative) :
    (kernelLaw L F hOne hMul).IsCommutative := fun t x y => by
  show (kernelPointsEquiv L F t).symm _ = (kernelPointsEquiv L F t).symm _
  exact congrArg _ (Subtype.ext (hc t _ _))

include hOne hMul in
theorem exists_kernel_hopf_model (hc : L.IsCommutative) [IsFinite F.val] [Flat F.val] :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ kernelPoints L F (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          (e T (φ * ψ)).val = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (g.comp φ.ofConv))).val.val =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.val) := by
  letI gK : GrpObj (Over.mk (kernelStr L F)) := (kernelLaw L F hOne hMul).grpObjOverMk
  letI : IsCommMonObj (Over.mk (kernelStr L F)) :=
    (kernelLaw L F hOne hMul).isCommMonObj_grpObjOverMk_iff_mul_comm.mpr
      (fun t x y => kernelLaw_isCommutative L F hOne hMul hc t x y)
  letI : IsFinite (Over.mk (kernelStr L F)).hom := by
    change IsFinite (kernelStr L F); infer_instance
  letI : Flat (Over.mk (kernelStr L F)).hom := by
    change Flat (kernelStr L F); infer_instance
  obtain ⟨H, iCR, iHA, hFin, hFlat, hComm, e, hEMul, hENat⟩ :=
    AlgebraicGeometry.exists_hopfAlgebra_flat_of_grpObj_over_spec R (Over.mk (kernelStr L F))
  let pts (T : Type u) [CommRing T] [Algebra R T] :=
    (schemeHomOverEquivOverHom (Spec.map (CommRingCat.ofHom (algebraMap R T)))
      (kernelStr L F)).symm.trans (kernelPointsEquiv L F _)
  refine ⟨H, iCR, iHA, hFin, hFlat, hComm, fun T _ _ => (e T).trans (pts T), ?_, ?_⟩
  · intro T _ _ φ ψ
    rw [Equiv.trans_apply, hEMul]
    change (kernelPointsEquiv L F _ (overHomToSchemeHomOver (e T φ * e T ψ))).val = _
    rw [(kernelLaw L F hOne hMul).overHomToSchemeHomOver_mul]
    exact congrArg Subtype.val ((kernelPointsEquiv L F _).apply_symm_apply _)
  · intro T T' _ _ _ _ g φ
    change (kernelPointsEquiv L F _ (overHomToSchemeHomOver (e T' (.toConv (g.comp φ.ofConv))))).val.val = _
    change (e T' (.toConv (g.comp φ.ofConv))).left ≫ kernelIncl L F = _
    rw [hENat]
    exact Category.assoc _ _ _



include hOne hMul in
theorem exists_kernel_finite_free_hopf_model [IsLocalRing R]
    (hc : L.IsCommutative) [IsFinite F.val] [Flat F.val] :
    HasFiniteFreeKernelHopfModel L F := by
  obtain ⟨H, iCR, iHA, hFin, hFlat, hComm, e, hMulE, hNatE⟩ :=
    exists_kernel_hopf_model L F hOne hMul hc
  letI := iCR
  letI := iHA
  letI := hFin
  letI := hFlat
  exact ⟨H, iCR, iHA, hFin, Module.free_of_flat_of_isLocalRing, hComm, e, hMulE, hNatE⟩

end MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityProof20261020


theorem solution : (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), ∀ {T' : Scheme.{u}} (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (a : SchemeHomOver t (kernelStr L F)),
(kernelPointsEquiv L F t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a)).val =
      GoodReductionJacobian.schemeHomOverComp ψ hψ (kernelPointsEquiv L F t a).val) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)), ∀ (hc : L.IsCommutative),
(kernelLaw L F hOne hMul).IsCommutative) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)), ∀ (hc : L.IsCommutative) [IsFinite F.val] [Flat F.val],
∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H),
      Module.Finite R H ∧ Module.Flat R H ∧ Coalgebra.IsCocomm R H ∧
      ∃ e : ∀ (T : Type u) [CommRing T] [Algebra R T],
          WithConv (H →ₐ[R] T) ≃ kernelPoints L F (Spec.map (CommRingCat.ofHom (algebraMap R T))),
        (∀ (T : Type u) [CommRing T] [Algebra R T] (φ ψ : WithConv (H →ₐ[R] T)),
          (e T (φ * ψ)).val = L.mul _ (e T φ).val (e T ψ).val) ∧
        (∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
            (g : T →ₐ[R] T') (φ : WithConv (H →ₐ[R] T)),
          (e T' (.toConv (g.comp φ.ofConv))).val.val =
            Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (e T φ).val.val)) ∧ (∀ {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (F : SchemeHomOver f f), ∀ (hOne : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), NeronModelInfra.schemeHomOverComp (L.one t) F = L.one t) (hMul : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f), NeronModelInfra.schemeHomOverComp (L.mul t x y) F = L.mul t (NeronModelInfra.schemeHomOverComp x F) (NeronModelInfra.schemeHomOverComp y F)), ∀ [IsLocalRing R]
    (hc : L.IsCommutative) [IsFinite F.val] [Flat F.val],
HasFiniteFreeKernelHopfModel L F) := by
  exact ⟨MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityProof20261020.kernelPointsEquiv_natural, MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityProof20261020.kernelLaw_isCommutative, MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityProof20261020.exists_kernel_hopf_model, MazurTransfer.OriginalRelativeNormKernelHopfRepresentabilityProof20261020.exists_kernel_finite_free_hopf_model⟩
#print axioms solution
