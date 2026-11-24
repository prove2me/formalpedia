-- Prove2me | solution 1 for GlobalTheory.DiscrJacobian.associated_discr_norm_jacobian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:32:52.001087+00:00
-- url     : https://prove2.me/submissions/b829aa07-2880-48e7-a022-52edb3dc4eb8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_CoeffEqZeroOfMemSpanPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrMulDetEqNormOfAnnihilator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsUnitDetOfProductMapNeZero
import Theorems.Thm_GlobalTheory_DiscrJacobian_mu_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_mem_span_of_mu_eq_zero
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_der_mul
import Theorems.Thm_GlobalTheory_DiscrJacobian_pairing_tmul
import Theorems.Thm_GlobalTheory_DiscrJacobian_isUnit_det_of_productMap_ne_zero
import Theorems.Thm_GlobalTheory_DiscrJacobian_exists_eq_C_add_sum
import Theorems.Thm_GlobalTheory_DiscrJacobian_X_mem_jacobson
import Theorems.Thm_GlobalTheory_DiscrJacobian_map_mem_radical
import Theorems.Thm_GlobalTheory_SocleDet_det_mul_mem
import Theorems.Thm_GlobalTheory_SocleDet_det_notMem_span
import Theorems.Thm_GlobalTheory_annihilator_diagonal_form_swap
import Theorems.Thm_GlobalTheory_annihilator_diagonal_trace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DiscrJacobian.mu_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.der_tmul
attribute [local simp] GlobalTheory.DiscrJacobian.pairing_tmul
section
namespace GlobalTheory.DiscrJacobian
open scoped TensorProduct
section Diagonal
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B]
end Diagonal
section Socle
variable {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra R C]
end Socle
section Series
open MvPowerSeries IsLocalRing
open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
private theorem tensorMap_det_mul_tmul_sub_eq_zero {g : ℕ} [Module.Finite R B] [Module.FinitePresentation S B]
    (x f : Fin g → S) (hx : ∀ j, x j ∈ (⊥ : Ideal S).jacobson)
    (hgen : ∀ s : S, ∃ (c : R) (u : Fin g → S), s = algebraMap R S c + ∑ j, x j * u j)
    (hf : ∀ i, algebraMap S B (f i) = 0)
    (a : Matrix (Fin g) (Fin g) (S ⊗[R] B))
    (ha : ∀ i, f i ⊗ₜ[R] (1 : B) =
      ∑ j, a i j * (x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)))
    (s : S) :
    Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S B) (AlgHom.id R B) a.det *
      (algebraMap S B s ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] algebraMap S B s) = 0 := by
  classical
  set π := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R S B) (AlgHom.id R B) with hπ
  have hker : ∀ l, a.det * (x l ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x l)) ∈
      RingHom.ker π := by
    intro l
    refine _root_.GlobalTheory.SocleDet.det_mul_mem (RingHom.ker π) a
      (fun j => x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j)) l fun r => ?_
    rw [Matrix.mulVec, dotProduct, ← ha r, RingHom.mem_ker]
    simp [π, hf]
  have hmem := _root_.GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero x hx hgen (s ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B s)
    (by simp)
  rw [Ideal.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hπs : π (s ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B s) =
      algebraMap S B s ⊗ₜ[R] (1 : B) - (1 : B) ⊗ₜ[R] algebraMap S B s := by
    simp [π]
  rw [← hπs, ← map_mul, ← hc, Finset.mul_sum]
  rw [map_sum]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [mul_left_comm, map_mul, RingHom.mem_ker.mp (hker l), mul_zero]
open scoped TensorProduct in
variable {R S B : Type} [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
  [Algebra R B] [IsScalarTower R S B] in
private theorem algebraMap_derivation_eq_sum_mu_mul {g : ℕ} (D : Derivation R S S) (x f : Fin g → S)
    (a : Matrix (Fin g) (Fin g) (S ⊗[R] B))
    (ha : ∀ i, f i ⊗ₜ[R] (1 : B) =
      ∑ j, a i j * (x j ⊗ₜ[R] (1 : B) - (1 : S) ⊗ₜ[R] algebraMap S B (x j))) (i : Fin g) :
    algebraMap S B (D (f i)) = ∑ j, _root_.GlobalTheory.DiscrJacobian.mu R S B (a i j) * algebraMap S B (D (x j)) := by
  have := congrArg (_root_.GlobalTheory.DiscrJacobian.der D) (ha i)
  rw [_root_.GlobalTheory.DiscrJacobian.der_tmul, mul_one, map_sum] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.GlobalTheory.DiscrJacobian.der_mul, map_sub, map_sub]
  simp
open scoped TensorProduct in
private theorem norm_sum_mul_eq_discr_mul_det {R B : Type} [CommRing R] [CommRing B] [Algebra R B]
    {d : ℕ} (b : Module.Basis (Fin d) R B) (M : Matrix (Fin d) (Fin d) R)
    (h : ∀ x : B, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0) :
    Algebra.norm R (∑ i, ∑ j, M i j • (b i * b j)) = Algebra.discr R b * M.det := by
  classical
  have hmul : ∀ l, (∑ i, ∑ j, M i j • (b i * b j)) * b l =
      ∑ j, (∑ i, M i j * Algebra.trace R B (b i * b l)) • b j := by
    intro l
    have hs := _root_.GlobalTheory.annihilator_diagonal_form_swap (⇑b) M h (Algebra.trace R B) (b l)
    rw [← _root_.GlobalTheory.annihilator_diagonal_trace b M h, Finset.sum_mul]
    simp only [Finset.sum_mul, smul_mul_assoc]
    rw [← hs, Finset.sum_comm]
    simp only [Finset.sum_smul]
  have hmat : Algebra.leftMulMatrix b (∑ i, ∑ j, M i j • (b i * b j)) =
      M.transpose * Algebra.traceMatrix R b := by
    ext j l
    rw [Algebra.leftMulMatrix_eq_repr_mul, hmul]
    simp [Matrix.mul_apply, Algebra.traceMatrix_apply, Module.Basis.repr_sum_self,
      Finsupp.single_apply]
  rw [Algebra.norm_eq_matrix_det b, hmat, Matrix.det_mul, Matrix.det_transpose,
    Algebra.discr_def, mul_comm]
end Series
end GlobalTheory.DiscrJacobian
namespace GlobalTheory
end GlobalTheory
end

set_option autoImplicit false
open GlobalTheory GlobalTheory.DiscrJacobian
open scoped TensorProduct
open MvPowerSeries IsLocalRing
open MvPowerSeries IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 800000
namespace GlobalTheory.DiscrJacobian
namespace _root_.GlobalTheory.DiscrJacobian
theorem _root_.solution (R : Type) [CommRing R] [IsLocalRing R]
    (g d : ℕ) (f : Fin g → MvPowerSeries (Fin g) R)
    (b : Module.Basis (Fin d) R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))
    (hf : ∀ i, constantCoeff (f i) ∈ maximalIdeal R) :
    Associated (Algebra.discr R b) (Algebra.norm R (Ideal.Quotient.mk (Ideal.span (Set.range f))
      (Matrix.of fun i j => pderiv R j (f i)).det)) := by
  classical
  haveI : Module.Finite R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) :=
    Module.Finite.of_basis b
  haveI : Module.FinitePresentation (MvPowerSeries (Fin g) R)
      (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) :=
    Module.finitePresentation_of_surjective (Submodule.mkQ (Ideal.span (Set.range f)))
      (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact ⟨Finset.univ.image f, by simp⟩)
  have hx : ∀ j, (X j : MvPowerSeries (Fin g) R) ∈ (⊥ : Ideal (MvPowerSeries (Fin g) R)).jacobson :=
    fun j => _root_.GlobalTheory.DiscrJacobian.X_mem_jacobson j
  have hgen : ∀ s : MvPowerSeries (Fin g) R, ∃ (c : R) (u : Fin g → MvPowerSeries (Fin g) R),
      s = algebraMap R (MvPowerSeries (Fin g) R) c + ∑ j, X j * u j := by
    intro s
    obtain ⟨u, hu⟩ := _root_.GlobalTheory.DiscrJacobian.exists_eq_C_add_sum s
    exact ⟨constantCoeff s, u, hu⟩
  have hf0 : ∀ i, algebraMap (MvPowerSeries (Fin g) R)
      (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (f i) = 0 := fun i =>
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hrow : ∀ i, ∃ r : Fin g → MvPowerSeries (Fin g) R ⊗[R]
      (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)),
      f i ⊗ₜ[R] (1 : MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) = ∑ j, r j *
        (X j ⊗ₜ[R] 1 - (1 : MvPowerSeries (Fin g) R) ⊗ₜ[R] algebraMap (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (X j)) := by
    intro i
    have := _root_.GlobalTheory.DiscrJacobian.mem_span_of_mu_eq_zero X hx hgen
      (f i ⊗ₜ[R] (1 : MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))
      (by simp [hf0])
    rw [Ideal.mem_span_range_iff_exists_fun] at this
    obtain ⟨c, hc⟩ := this
    exact ⟨c, hc.symm⟩
  choose a ha using hrow
  set De := Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (MvPowerSeries (Fin g) R)
    (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) (AlgHom.id R _) (Matrix.of a).det
    with hDe_def
  have hann : ∀ y, De * (y ⊗ₜ[R] 1 - 1 ⊗ₜ[R] y) = 0 := by
    intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact tensorMap_det_mul_tmul_sub_eq_zero X f hx hgen hf0 (Matrix.of a) ha s
  set M : Matrix (Fin d) (Fin d) R := fun i j => (b.tensorProduct b).repr De (i, j) with hM
  have hDe : De = ∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j) := by
    conv_lhs => rw [← (b.tensorProduct b).sum_repr De]
    rw [Fintype.sum_prod_type]
    simp [M, Module.Basis.tensorProduct_apply]
  have h : ∀ x, (∑ i, ∑ j, M i j • TensorProduct.tmul R (b i) (b j)) *
      (TensorProduct.tmul R x 1 - TensorProduct.tmul R 1 x) = 0 := by
    intro x; rw [← hDe]; exact hann x
  have hJ : ∑ i, ∑ j, M i j • (b i * b j) = Ideal.Quotient.mk (Ideal.span (Set.range f))
      (Matrix.of fun i j => pderiv R j (f i)).det := by
    have hlm : ∀ t, Algebra.TensorProduct.lmul' R (Algebra.TensorProduct.map
        (IsScalarTower.toAlgHom R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) (AlgHom.id R _) t) =
        _root_.GlobalTheory.DiscrJacobian.mu R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) t := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]
      | tmul s w => simp
    have hentry : ∀ i j, Ideal.Quotient.mk (Ideal.span (Set.range f)) (pderiv R j (f i)) =
        _root_.GlobalTheory.DiscrJacobian.mu R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (a i j) := by
      intro i j
      have := algebraMap_derivation_eq_sum_mu_mul (pderiv R j) X f (Matrix.of a) ha i
      rw [← Ideal.Quotient.algebraMap_eq, this]
      simp only [Matrix.of_apply]
      rw [Finset.sum_eq_single j (fun k _ hk => by rw [pderiv_X_of_ne hk, map_zero, mul_zero])
        (by simp), pderiv_X_self, map_one, mul_one]
    calc ∑ i, ∑ j, M i j • (b i * b j) = Algebra.TensorProduct.lmul' R De := by
          rw [hDe]; simp [map_sum, Algebra.TensorProduct.lmul'_apply_tmul]
      _ = _root_.GlobalTheory.DiscrJacobian.mu R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) (Matrix.of a).det := hlm _
      _ = _ := by
          rw [← AlgHom.coe_toRingHom, RingHom.map_det, RingHom.map_det]
          congr 1
          ext i j
          simp [RingHom.mapMatrix_apply, hentry]
  have hMunit : IsUnit M.det := by
    let J : Ideal (MvPowerSeries (Fin g) (ResidueField R)) :=
      Ideal.span (Set.range fun i => MvPowerSeries.map (residue R) (f i))
    let red : MvPowerSeries (Fin g) R →ₐ[R] MvPowerSeries (Fin g) (ResidueField R) :=
      MvPowerSeries.mapAlgHom (Algebra.ofId R (ResidueField R))
    have hred : ∀ s, red s = MvPowerSeries.map (residue R) s := fun s => rfl
    let ev0 : MvPowerSeries (Fin g) R →ₐ[R] ResidueField R :=
      { toRingHom := (residue R).comp constantCoeff,
        commutes' := fun r => by simp [MvPowerSeries.algebraMap_apply] }
    have hIev : Ideal.span (Set.range f) ≤ RingHom.ker ev0 := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr (hf i)
    have hIred : Ideal.span (Set.range f) ≤ RingHom.ker ((Ideal.Quotient.mkₐ R J).comp red) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show Ideal.Quotient.mkₐ R J (red (f i)) = 0
      rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hred]
      exact Ideal.subset_span ⟨i, rfl⟩
    let ev : (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) →ₐ[R] ResidueField R :=
      Ideal.Quotient.liftₐ _ ev0 (fun a ha => hIev ha)
    let ρ : (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) →ₐ[R]
        (MvPowerSeries (Fin g) (ResidueField R) ⧸ J) :=
      Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R J).comp red) (fun a ha => hIred ha)
    let n : Ideal (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) :=
      Ideal.span (Set.range fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j))
    have hnrad : n ≤ ((maximalIdeal R).map
        (algebraMap R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))).radical := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have := _root_.GlobalTheory.DiscrJacobian.map_mem_radical (R := R)
        (S := MvPowerSeries (Fin g) R)
        (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)))) (hx j)
      simpa [Ideal.Quotient.algebraMap_eq] using this
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hnrad
      ⟨Finset.univ.image fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j),
        by rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]⟩
    have hev : ∀ w ∈ n, ev w = 0 := by
      intro w hw
      have hle : n ≤ RingHom.ker ev := by
        rw [Ideal.span_le]
        rintro _ ⟨j, rfl⟩
        rw [SetLike.mem_coe, RingHom.mem_ker]
        show residue R (constantCoeff (X j : MvPowerSeries (Fin g) R)) = 0
        simp
      exact hle hw
    have hgenB : ∀ w : MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f),
        ∃ c : R, w - algebraMap R _ c ∈ n := by
      intro w
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective w
      obtain ⟨c, u, hu⟩ := hgen s
      refine ⟨c, ?_⟩
      rw [hu, map_add, Ideal.Quotient.mk_algebraMap, add_sub_cancel_left, map_sum]
      exact Ideal.sum_mem _ fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have hmB : ∀ w ∈ (maximalIdeal R).map
        (algebraMap R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))), ρ w = 0 := by
      intro w hw
      have hle : (maximalIdeal R).map
          (algebraMap R (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) ≤ RingHom.ker ρ := by
        rw [Ideal.map_le_iff_le_comap]
        intro c hc
        rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
          IsScalarTower.algebraMap_apply R (ResidueField R),
          show algebraMap R (ResidueField R) c = 0 from (IsLocalRing.residue_eq_zero_iff c).mpr hc,
          map_zero]
      exact hle hw
    have hpow : ∀ i, (X i : MvPowerSeries (Fin g) (ResidueField R)) ^ N ∈ J := by
      intro i
      have h1 : (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) ^ N ∈ n ^ N :=
        Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self
          (f := fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) i)) N
      have h2 := hmB _ (hN h1)
      have h3 : ρ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X i)) =
          Ideal.Quotient.mk J (X i) := by
        show Ideal.Quotient.mk J (red (X i)) = _
        rw [hred, MvPowerSeries.map_X]
      rw [map_pow, h3, ← map_pow, Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    let ιk := Algebra.ofId (ResidueField R) (MvPowerSeries (Fin g) (ResidueField R))
    let Φ : MvPowerSeries (Fin g) R ⊗[R] (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f)) →ₐ[R]
        MvPowerSeries (Fin g) (ResidueField R) :=
      Algebra.TensorProduct.productMap red ((ιk.restrictScalars R).comp ev)
    have hcomp : ∀ t, Algebra.TensorProduct.productMap ρ
        ((IsScalarTower.toAlgHom R (ResidueField R) _).comp ev)
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (MvPowerSeries (Fin g) R)
          (MvPowerSeries (Fin g) R ⧸ Ideal.span (Set.range f))) (AlgHom.id R _) t) =
        Ideal.Quotient.mk J (Φ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul s w =>
        simp [Φ, ρ, ιk, Ideal.Quotient.algebraMap_eq, Algebra.ofId_apply]
        rfl
    have hrel : ∀ i, MvPowerSeries.map (residue R) (f i) = ∑ j, Φ (a i j) * X j := by
      intro i
      have hevX : ∀ j, ev (Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) = 0 := fun j =>
        hev _ (Ideal.subset_span (Set.mem_range_self
          (f := fun j => Ideal.Quotient.mk (Ideal.span (Set.range f)) (X j)) j))
      have := congrArg Φ (ha i)
      simp only [Φ, map_sum, map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
        map_one, mul_one, one_mul] at this
      rw [← hred, this]
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      simp [hevX j, hred, MvPowerSeries.map_X, Ideal.Quotient.algebraMap_eq]
    have hdet := _root_.GlobalTheory.SocleDet.det_notMem_span (ResidueField R) g N
      (fun i => MvPowerSeries.map (residue R) (f i)) (Φ.toRingHom.mapMatrix (Matrix.of a))
      hrel hpow
    refine _root_.GlobalTheory.DiscrJacobian.isUnit_det_of_productMap_ne_zero b n N hN ev hev hgenB ρ De M hDe
      hann ?_
    intro h0
    apply hdet
    rw [hDe_def, hcomp, Ideal.Quotient.eq_zero_iff_mem, ← AlgHom.coe_toRingHom,
      RingHom.map_det] at h0
    exact h0
  refine ⟨hMunit.unit, ?_⟩
  rw [← hJ, norm_sum_mul_eq_discr_mul_det b M h, IsUnit.unit_spec]
end _root_.GlobalTheory.DiscrJacobian
end GlobalTheory.DiscrJacobian
