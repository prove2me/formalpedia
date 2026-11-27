-- Prove2me | solution 1 for GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:52.839943+00:00
-- url     : https://prove2.me/submissions/edaf971d-ac88-4165-81e6-c579f604165f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped TensorProduct
namespace GlobalTheory
open scoped TensorProduct in
private lemma algebraMap_injective_of_denseP_unique_lift {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    (P : Set (Ideal R)) (hP : _root_.GlobalTheory.ZM.DenseP P)
    (hpt : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
      RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) :
    Function.Injective (algebraMap R B) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply hP a
  intro p hp _
  obtain ⟨K, _, _, x, hx, y, hy, -⟩ := hpt p hp
  rw [← hx, RingHom.mem_ker, ← hy, RingHom.comp_apply, ha, map_zero]
open scoped TensorProduct in
private lemma algebraMap_surjective_of_unique_algHom (K A : Type) [Field K] [IsAlgClosed K] [CommRing A]
    [Algebra K A] [Module.Finite K A] [Algebra.FormallyUnramified K A]
    (φ₀ : A →ₐ[K] K) (hφ₀ : ∀ φ : A →ₐ[K] K, φ = φ₀) : Function.Surjective (algebraMap K A) := by
  haveI := Algebra.FormallyUnramified.isReduced_of_field K A
  haveI : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hφ₀s : Function.Surjective φ₀ := fun c => ⟨algebraMap K A c, by simp⟩
  have hmax : ∀ m : Ideal A, m.IsMaximal → m = RingHom.ker φ₀ := by
    intro m hm
    letI := Ideal.Quotient.field m
    have hs : Function.Surjective (algebraMap K (A ⧸ m)) := IsSepClosed.algebraMap_surjective K (A ⧸ m)
    let e : K ≃ₐ[K] A ⧸ m := AlgEquiv.ofBijective (Algebra.ofId K (A ⧸ m))
      ⟨(algebraMap K (A ⧸ m)).injective, hs⟩
    have h := hφ₀ ((e.symm : (A ⧸ m) →ₐ[K] K).comp (Ideal.Quotient.mkₐ K m))
    rw [← h]
    ext a
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  haveI : IsLocalRing A := IsLocalRing.of_unique_max_ideal
    ⟨RingHom.ker φ₀, RingHom.ker_isMaximal_of_surjective _ hφ₀s, fun m hm => hmax m hm⟩
  have hfield := IsArtinianRing.isField_of_isReduced_of_isLocalRing A
  have hinj : Function.Injective φ₀ := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    obtain ⟨b, hb⟩ := hfield.mul_inv_cancel hne
    have := congrArg φ₀ hb
    simp [ha] at this
  intro a
  exact ⟨φ₀ a, hinj (by simp)⟩
open scoped TensorProduct in
private lemma exists_smul_mem_range_algebraMap_of_unique_lift {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Algebra.FormallyUnramified R B] {K : Type} [Field K] [IsAlgClosed K]
    (x : R →+* K) (hy : ∃! y : B →+* K, y.comp (algebraMap R B) = x) :
    ∃ f : R, f ∉ RingHom.ker x ∧ ∀ b : B, ∃ a : R, f • b = algebraMap R B a := by
  letI : Algebra R K := x.toAlgebra
  obtain ⟨y, hyx, hyu⟩ := hy
  let y' : B →ₐ[R] K := { y with commutes' := fun r => congrArg (fun g : R →+* K => g r) hyx }
  let φ₀ : K ⊗[R] B →ₐ[K] K := Algebra.TensorProduct.productLeftAlgHom (AlgHom.id K K) y'
  have hΦ : ∀ φ : K ⊗[R] B →ₐ[K] K, φ = φ₀ := by
    intro φ
    have h1 : ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hyu
      ext r
      exact ((φ.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    have h2 : ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).toRingHom = y := by
      apply hyu
      ext r
      exact ((φ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight).commutes r
    apply Algebra.TensorProduct.ext (Subsingleton.elim _ _)
    apply AlgHom.coe_ringHom_injective
    exact h1.trans h2.symm
  have hsurj := algebraMap_surjective_of_unique_algHom K (K ⊗[R] B) φ₀ hΦ
  let N : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  have hsub : Subsingleton (K ⊗[R] (B ⧸ N)) := by
    refine ⟨fun u v => ?_⟩
    have key : ∀ w : K ⊗[R] (B ⧸ N), w = 0 := by
      intro w
      obtain ⟨t, rfl⟩ := LinearMap.lTensor_surjective K (Submodule.mkQ_surjective N) w
      obtain ⟨c, rfl⟩ := hsurj t
      have h1 : (N.mkQ (1 : B)) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact ⟨1, by simp⟩
      simp [Algebra.TensorProduct.algebraMap_apply, h1]
    rw [key u, key v]
  have hq : (RingHom.ker x).IsPrime := RingHom.ker_isPrime x
  let xb : (RingHom.ker x).ResidueField →+* K := Ideal.ResidueField.lift (RingHom.ker x) x le_rfl
    (fun a ha => by
      simp only [Submonoid.mem_comap, IsUnit.mem_submonoid_iff, isUnit_iff_ne_zero]
      exact ha)
  letI : Algebra (RingHom.ker x).ResidueField K := xb.toAlgebra
  haveI : IsScalarTower R (RingHom.ker x).ResidueField K := IsScalarTower.of_algebraMap_eq (fun r => by
    simp [xb, RingHom.algebraMap_toAlgebra])
  have hsub2 : Subsingleton ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N)) := by
    have e := TensorProduct.AlgebraTensorModule.cancelBaseChange R (RingHom.ker x).ResidueField K K (B ⧸ N)
    haveI : Subsingleton (K ⊗[(RingHom.ker x).ResidueField] ((RingHom.ker x).ResidueField ⊗[R] (B ⧸ N))) :=
      e.toEquiv.subsingleton
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right _ _).mp this
  have hns : (⟨RingHom.ker x, hq⟩ : PrimeSpectrum R) ∉ Module.support R (B ⧸ N) := by
    rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct]
    exact not_nontrivial_iff_subsingleton.mpr hsub2
  rw [Module.mem_support_iff_of_finite] at hns
  obtain ⟨f, hfann, hfq⟩ := SetLike.not_le_iff_exists.mp hns
  refine ⟨f, hfq, fun b => ?_⟩
  have h0 := Module.mem_annihilator.mp hfann (N.mkQ b)
  rw [← LinearMap.map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0
  obtain ⟨a, ha⟩ := h0
  exact ⟨a, by simpa using ha.symm⟩
end GlobalTheory
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open scoped TensorProduct
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (R B : Type) [CommRing R] [IsReduced R] [CommRing B] [Algebra R B] [Module.Finite R B]
      [Algebra.FormallyUnramified R B] (P : Set (Ideal R)),
      (∀ (q : Ideal R) (f : R), q.IsPrime → f ∉ q → ∃ p ∈ P, p.IsPrime ∧ q ≤ p ∧ f ∉ p) →
      (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K),
        RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) →
      Function.Bijective (algebraMap R B) := by
  intro R B _ _ _ _ _ _ P hP hpt
  have hdense : _root_.GlobalTheory.ZM.DenseP P := by
    intro a ha
    apply IsReduced.eq_zero
    rw [nilpotent_iff_mem_prime]
    intro q hq
    by_contra haq
    obtain ⟨p, hpP, hp, -, hap⟩ := hP q a hq haq
    exact hap (ha p hpP hp)
  refine ⟨algebraMap_injective_of_denseP_unique_lift P hdense hpt, fun b => ?_⟩
  let M : Submodule R B := LinearMap.range (Algebra.linearMap R B)
  let s : Set R := {f | ∃ a : R, f • b = algebraMap R B a}
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, hpP, -, hmp, h1p⟩ := hP m 1 hm.isPrime
      (fun h => hm.ne_top ((Ideal.eq_top_iff_one m).mpr h))
    have hpm : p = m := (hm.eq_of_le ((Ideal.ne_top_iff_one p).mpr h1p) hmp).symm
    obtain ⟨K, _, _, x, hx, hy⟩ := hpt p hpP
    obtain ⟨f, hf, hfb⟩ := exists_smul_mem_range_algebraMap_of_unique_lift x hy
    apply hf
    rw [hx, hpm]
    exact hsm (Ideal.subset_span (hfb b))
  have hb := Submodule.mem_of_span_eq_top_of_smul_pow_mem M s hs b (fun r => ⟨1, by
    obtain ⟨a, ha⟩ := r.2
    rw [pow_one, ha]
    exact ⟨a, rfl⟩⟩)
  obtain ⟨a, ha⟩ := hb
  exact ⟨a, ha⟩
end _root_.GlobalTheory
end GlobalTheory
