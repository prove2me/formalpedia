-- Prove2me | solution 1 for OAI.EuclideanRamsey.finite_lattice_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:29:58.351841+00:00
-- url     : https://prove2.me/submissions/5a3f5a2b-4d75-4839-ab18-61aa4638a319

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/AdicLifting.lean:L422-L442
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.finite_lattice_identity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_AdicLifting
import Theorems.Thm_OAI_EuclideanRamsey_quadraticStencil_moments

-- ---- from OAI.Combinatorics.EuclideanRamsey.LatticeMoments ----
namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix

open scoped TensorProduct
namespace EuclideanRamsey

section Algebra
variable {k : ℕ}

lemma monomial_sub_one_mem (γ : Lattice k) :
    AddMonoidAlgebra.single γ 1 - 1 ∈ (augmentationIdeal : Ideal (LatticeRing k)) := by
  change augmentation _ = 0
  simp

lemma mem_augmentationIdeal (x : LatticeRing k) :
    x ∈ augmentationIdeal ↔ mass x = 0 := by
  change augmentation x = 0 ↔ _
  rw [augmentation_eq_mass]

lemma augmentation_sq_le_jetOne : (augmentationIdeal : Ideal (LatticeRing k)) ^ 2 ≤ jetOne := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx0 := (mem_augmentationIdeal x).mp hx
  have hy0 := (mem_augmentationIdeal y).mp hy
  change mass (x*y) = 0 ∧ ∀ a, firstMoment (x*y) a = 0
  simp [firstMoment_mul, hx0, hy0]

lemma augmentation_cube_le_jetTwo : (augmentationIdeal : Ideal (LatticeRing k)) ^ 3 ≤ jetTwo := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx0 := (mem_augmentationIdeal x).mp hx
  have hy0 : mass y = 0 ∧ ∀ a, firstMoment y a = 0 := augmentation_sq_le_jetOne hy
  change mass (x*y) = 0 ∧ (∀ a, firstMoment (x*y) a = 0) ∧ ∀ a b, secondMoment (x*y) a b = 0
  simp [firstMoment_mul, secondMoment_mul, hx0, hy0]

lemma moments_eq_of_sub_mem_cube {x y : LatticeRing k}
    (h : x-y ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 3) :
    mass x = mass y ∧ (∀ a, firstMoment x a = firstMoment y a) ∧
      ∀ a b, secondMoment x a b = secondMoment y a b := by
  have hh := augmentation_cube_le_jetTwo h
  change mass (x-y) = 0 ∧ (∀ a, firstMoment (x-y) a = 0) ∧ ∀ a b, secondMoment (x-y) a b = 0 at hh
  simpa only [mass_sub, firstMoment_sub, secondMoment_sub, sub_eq_zero] using hh

end Algebra
end EuclideanRamsey

end

end OAI

-- ---- from OAI.Combinatorics.EuclideanRamsey.AdicLifting ----
namespace OAI

universe uRing uGroup uSemigroup uModule uModuleTarget uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

open scoped TensorProduct
namespace EuclideanRamsey

section NilpotentLog
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
open Finset

end NilpotentLog

section LogCharacter
variable {R : Type uRing} [CommRing R] [Algebra ℚ R]
  {I : Ideal R} {n : ℕ} (hI : I ^ n = ⊥)

variable {G : Type uGroup} [AddCommGroup G] (χ : Multiplicative G →* R)
  (hχ : ∀ γ : G, χ (Multiplicative.ofAdd γ) - 1 ∈ I)

end LogCharacter

section LatticeLog
variable {k : ℕ} {R : Type uRing} [CommRing R] [Algebra ℚ R]

lemma rationalExtension_lattice (f : (Fin k → ℤ) →+ R) (γ : Fin k → ℤ) :
    rationalExtension f (fun j => (γ j : ℚ)) = f γ := by
  dsimp [rationalExtension]
  simp_rw [Int.cast_smul_eq_zsmul, ← map_zsmul]
  rw [← map_sum]
  congr 1
  convert Finset.univ_sum_single γ using 1
  congr 1
  ext j
  rw [← Pi.single_smul]
  simp

end LatticeLog

section AdicLifting
variable {R : Type uRing} {M : Type uModule} {N : Type uModuleTarget} [CommRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [Module.Finite R N]

lemma adic_kernel_lifting (I : Ideal R) (f : M →ₗ[R] N) (q : ℕ) :
    ∃ n : ℕ, ∀ x : M, f x ∈ I ^ n • (⊤ : Submodule R N) →
      ∃ y : M, f y = 0 ∧ x - y ∈ I ^ q • (⊤ : Submodule R M) := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (LinearMap.range f)
  refine ⟨k + q, ?_⟩
  intro x hx
  have hfx : f x ∈ I ^ (k + q) • (⊤ : Submodule R N) ⊓ LinearMap.range f :=
    ⟨hx, ⟨x, rfl⟩⟩
  rw [hk (k + q) (by omega), Nat.add_sub_cancel_left] at hfx
  have hle : I ^ q • (I ^ k • (⊤ : Submodule R N) ⊓ LinearMap.range f) ≤
      I ^ q • LinearMap.range f := smul_mono_right _ inf_le_right
  have hf' : f x ∈ I ^ q • LinearMap.range f := hle hfx
  have hm : I ^ q • LinearMap.range f = Submodule.map f (I ^ q • (⊤ : Submodule R M)) := by
    rw [Submodule.map_smul'']
    simp
  rw [hm] at hf'
  obtain ⟨z, hz, he⟩ := hf'
  refine ⟨x - z, ?_, ?_⟩
  · rw [map_sub, he, sub_self]
  · simpa using hz

end AdicLifting

section IntersectionLifting
variable {R : Type uRing} [CommRing R] [IsNoetherianRing R]
  {ι : Type uIndex} [Fintype ι] (I : Ideal R) (J : ι → Ideal R)

lemma adic_intersection_lifting (q : ℕ) :
    ∃ n : ℕ, ∀ x : R, (∀ i, x ∈ J i ⊔ I ^ n) →
      ∃ y : R, (∀ i, y ∈ J i) ∧ x - y ∈ I ^ q := by
  classical
  let f : R →ₗ[R] (∀ i, R ⧸ J i) := LinearMap.pi (fun i => Algebra.linearMap R (R ⧸ J i))
  obtain ⟨n, hn⟩ := adic_kernel_lifting I f q
  refine ⟨n, fun x hx => ?_⟩
  have hm : f x ∈ I ^ n • (⊤ : Submodule R (∀ i, R ⧸ J i)) := by
    have hz : ∀ i, ∃ z ∈ I ^ n, (Ideal.Quotient.mk (J i)) z = (Ideal.Quotient.mk (J i)) x := by
      intro i
      obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (hx i)
      refine ⟨z, hz, ?_⟩
      rw [← he, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hy, zero_add]
    choose z hz he using hz
    have he' : f x = ∑ i, z i • Pi.single i (1 : R ⧸ J i) := by
      simp_rw [← Pi.single_smul, Algebra.smul_def, mul_one,
        Ideal.Quotient.algebraMap_eq, he]
      exact (Finset.univ_sum_single _).symm
    rw [he']
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem_smul (hz i) Submodule.mem_top)
  obtain ⟨y, hy, hxy⟩ := hn x hm
  refine ⟨y, ?_, ?_⟩
  · intro i
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact congrFun hy i
  · simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hxy

end IntersectionLifting

section Construction
variable {k : ℕ}

lemma tensor_quotient_quadratic {S : Type uSemigroup} [CommRing S] [Algebra ℚ S]
    (V : Submodule ℚ (RationalSpace k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (f : RationalSpace k →ₗ[ℚ] S) (hf : V ≤ LinearMap.ker f)
    (hC : TensorProduct.map V.mkQ V.mkQ (matrixTensor C) = 0) :
    (∑ a, ∑ b, C a b • (f (Pi.single a 1) * f (Pi.single b 1))) = 0 := by
  let u := V.liftQ f hf
  let φ := (Algebra.TensorProduct.lmul' ℚ : S ⊗[ℚ] S →ₐ[ℚ] S).toLinearMap.comp
    (TensorProduct.map u u)
  have hh := congrArg φ hC
  simpa [φ, u, matrixTensor, LinearMap.comp_apply] using hh

lemma mem_cosetIdeal_iff (Λ : AddSubgroup (Lattice k)) (x : LatticeRing k) :
    x ∈ cosetIdeal Λ ↔ cosetPushforward Λ x = 0 := by
  change cosetMap Λ x = 0 ↔ _
  rw [← AddMonoidAlgebra.coeff_injective.eq_iff, AddMonoidAlgebra.coeff_zero]
  rfl

lemma monomial_sub_one_mem_cosetIdeal (Λ : AddSubgroup (Lattice k)) {γ : Lattice k}
    (hγ : γ ∈ Λ) : AddMonoidAlgebra.single γ 1 - 1 ∈ cosetIdeal Λ := by
  change cosetMap Λ (AddMonoidAlgebra.single γ 1 - 1) = 0
  rw [map_sub, map_one]
  simp only [cosetMap, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  have hh : QuotientAddGroup.mk' Λ γ = 0 := (QuotientAddGroup.eq_zero_iff γ).mpr hγ
  rw [hh]
  exact sub_self _

lemma quotient_nil_augmentation (N : ℕ) :
    (Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (augmentationIdeal : Ideal (LatticeRing k))) ^ N = ⊥ := by
  rw [← Ideal.map_pow, Ideal.map_quotient_self]

lemma finite_order_logs (N : ℕ) :
    ∃ f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N),
      (∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal) ∧
      (∀ γ, IsNilpotent.exp (f γ) =
        (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1)) := by
  let q := Ideal.Quotient.mkₐ ℚ ((augmentationIdeal : Ideal (LatticeRing k)) ^ N)
  let χ : Multiplicative (Lattice k) →* (LatticeRing k ⧸ augmentationIdeal ^ N) :=
    q.toMonoidHom.comp (AddMonoidAlgebra.of ℚ (Lattice k))
  have hχ : ∀ γ : Lattice k, χ (Multiplicative.ofAdd γ) - 1 ∈
      Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal := by
    intro γ
    have h := Ideal.mem_map_of_mem (Ideal.Quotient.mk (augmentationIdeal ^ N))
      (monomial_sub_one_mem γ)
    simpa [χ, q, AddMonoidAlgebra.of_apply, map_sub] using h
  refine ⟨characterLogHom (quotient_nil_augmentation N) χ hχ, ?_, ?_⟩
  · intro γ
    exact characterLog_mem (quotient_nil_augmentation N) χ hχ γ
  · intro γ
    simpa [χ, q, AddMonoidAlgebra.of_apply, characterLogHom] using
      characterLog_exp (quotient_nil_augmentation N) χ hχ γ

lemma log_quadratic_mod_coset (N : ℕ) (f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N))
    (hf : ∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal)
    (hfexp : ∀ γ, IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1))
    (Λ : AddSubgroup (Lattice k)) (C : Matrix (Fin k) (Fin k) ℚ)
    (hC : quotientTensor Λ (matrixTensor C) = 0)
    (l : Fin k → LatticeRing k)
    (hl : ∀ a, (Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a) = f (Pi.single a 1)) :
    quadraticStencil C l ∈ cosetIdeal Λ ⊔ augmentationIdeal ^ N := by
  let J := cosetIdeal Λ ⊔ (augmentationIdeal : Ideal (LatticeRing k)) ^ N
  let ψ := Ideal.Quotient.factorₐ ℚ (show augmentationIdeal ^ N ≤ J from le_sup_right)
  let g := ψ.toLinearMap.comp (rationalExtension f)
  have hgγ : ∀ γ ∈ Λ, g (rationalize γ) = 0 := by
    intro γ hγ
    have hn := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf γ)
    change ψ (rationalExtension f (rationalize γ)) = 0
    rw [show rationalize γ = (fun j => (γ j : ℚ)) from rfl, rationalExtension_lattice]
    apply (nil_exp_eq_one_iff (hn.map ψ)).mp
    rw [← hn.map_exp ψ, hfexp]
    change (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1) = 1
    have hm : AddMonoidAlgebra.single γ (1 : ℚ) - 1 ∈ J :=
      Ideal.mem_sup_left (monomial_sub_one_mem_cosetIdeal Λ hγ)
    have hz : (Ideal.Quotient.mk J) (AddMonoidAlgebra.single γ 1 - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hm
    simpa only [map_sub, map_one, sub_eq_zero] using hz
  have hg : latticeSpan Λ ≤ LinearMap.ker g := by
    apply Submodule.span_le.mpr
    rintro _ ⟨γ, hγ, rfl⟩
    exact hgγ γ hγ
  have hquad := tensor_quotient_quadratic (latticeSpan Λ) C g hg hC
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change (Ideal.Quotient.mkₐ ℚ J) (quadraticStencil C l) = 0
  have hlj : ∀ a, (Ideal.Quotient.mkₐ ℚ J) (l a) = g (Pi.single a 1) := by
    intro a
    change ψ ((Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a)) =
      ψ (rationalExtension f (Pi.single a 1))
    rw [hl, rationalExtension_single]
  simp only [quadraticStencil, map_smul, map_sum, map_mul, hlj, hquad, smul_zero]

lemma finite_order_log_lifts (N : ℕ) (hN : 2 ≤ N)
    (f : Lattice k →+ (LatticeRing k ⧸ augmentationIdeal ^ N))
    (hf : ∀ γ, f γ ∈ Ideal.map (Ideal.Quotient.mk (augmentationIdeal ^ N)) augmentationIdeal)
    (hfexp : ∀ γ, IsNilpotent.exp (f γ) =
      (Ideal.Quotient.mk (augmentationIdeal ^ N)) (AddMonoidAlgebra.single γ 1)) :
    ∃ l : Fin k → LatticeRing k,
      (∀ a, (Ideal.Quotient.mk (augmentationIdeal ^ N)) (l a) = f (Pi.single a 1)) ∧
      (∀ a, mass (l a) = 0) ∧
      (∀ a b, firstMoment (l a) b = if a = b then 1 else 0) := by
  classical
  let I : Ideal (LatticeRing k) := augmentationIdeal
  let q := Ideal.Quotient.mk (I ^ N)
  let M := Ideal.map q I
  have hex : ∀ a : Fin k, ∃ x ∈ I, q x = f (Pi.single a 1) := by
    intro a
    exact (Ideal.mem_map_iff_of_surjective q (Ideal.Quotient.mk_surjective)).mp (hf _)
  choose l hlI hl using hex
  refine ⟨l, hl, fun a => (mem_augmentationIdeal _).mp (hlI a), ?_⟩
  have hker : RingHom.ker q = I ^ N := by
    ext x
    exact Ideal.Quotient.eq_zero_iff_mem
  have hpre : Ideal.comap q (Ideal.map q (I ^ 2)) = I ^ 2 := by
    rw [Ideal.comap_map_of_surjective' q Ideal.Quotient.mk_surjective, hker]
    exact sup_eq_left.mpr (Ideal.pow_le_pow_right hN)
  intro a b
  let z : LatticeRing k := AddMonoidAlgebra.single (Pi.single a 1) 1 - 1
  have hdiff : l a - z ∈ I ^ 2 := by
    rw [← hpre]
    change q (l a - z) ∈ Ideal.map q (I ^ 2)
    rw [Ideal.map_pow]
    have hn := nilpotent_of_mem_nil_ideal (quotient_nil_augmentation N) (hf (Pi.single a 1))
    have hr : IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1) ∈ M ^ 2 :=
      nil_exp_sub_one_sub_mem hn (hf _)
    have hre : q (l a - z) = -(IsNilpotent.exp (f (Pi.single a 1)) - 1 - f (Pi.single a 1)) := by
      rw [hfexp, map_sub, hl]
      dsimp [z, q]
      rw [map_sub, map_one]
      ring
    rw [hre]
    exact (M ^ 2).neg_mem hr
  have hj := augmentation_sq_le_jetOne hdiff
  have hjb := hj.2 b
  simp only [firstMoment_sub, sub_eq_zero] at hjb
  rw [hjb]
  simp [z, Pi.single_apply, eq_comm]

theorem finite_lattice_identity : FiniteLatticeIdentity := by
  intro k s hk hs Λ C hCs hC
  let I : Ideal (LatticeRing k) := augmentationIdeal
  obtain ⟨n, hn⟩ := adic_intersection_lifting I (fun i => cosetIdeal (Λ i)) 3
  let N := n + 3
  obtain ⟨f, hf, hfexp⟩ := finite_order_logs (k := k) N
  obtain ⟨l, hl, hm, hfirst⟩ := finite_order_log_lifts N (by omega) f hf hfexp
  have hx : ∀ i, quadraticStencil C l ∈ cosetIdeal (Λ i) ⊔ I ^ n := by
    intro i
    apply (sup_le_sup_left (α := Ideal (LatticeRing k))
      (Ideal.pow_le_pow_right (show n ≤ N by omega)) (cosetIdeal (Λ i)))
    exact log_quadratic_mod_coset N f hf hfexp (Λ i) C (hC i) l hl
  obtain ⟨y, hy, hxy⟩ := hn (quadraticStencil C l) hx
  have he := moments_eq_of_sub_mem_cube hxy
  have hM := quadraticStencil_moments C hCs l hm hfirst
  refine ⟨y, fun i => (mem_cosetIdeal_iff _ _).mp (hy i), ?_, ?_, ?_⟩
  · exact he.1.symm.trans hM.1
  · intro a
    exact (he.2.1 a).symm.trans (hM.2.1 a)
  · intro a b
    exact (he.2.2 a b).symm.trans (hM.2.2 a b)

end Construction

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped TensorProduct


theorem solution : type_of% @_root_.OAI.EuclideanRamsey.finite_lattice_identity := @_root_.OAI.EuclideanRamsey.finite_lattice_identity
