-- Prove2me | solution 1 for GlobalTheory.SplittingIdempotents.exists_splitting_idempotents_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:50:08.994539+00:00
-- url     : https://prove2.me/submissions/c9a6d782-a82c-49a3-927e-5275354fb29f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_SplittingIdempotents
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_iff_isUnit_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul


section
open scoped TensorProduct
namespace GlobalTheory.SplittingIdempotents
open GlobalTheory.EigenSplit
private theorem exists_eq_of_isSplitting {A R ι : Type} [CommRing A] [CommRing R] [IsDomain R]
    [Fintype ι] {σ : ι → A →+* R} (h : IsSplitting σ) (χ : A →+* R) : ∃ i, σ i = χ := by
  classical
  let F : R ⊗[ℤ] A →ₐ[R] (Unit → R) := splitMap (fun _ : Unit => χ)
  have h1 : ∑ i, F (idem h i) () = 1 := by
    rw [← Finset.sum_apply, ← map_sum, (completeOrthogonalIdempotents_idem h).complete, map_one]
    rfl
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1 ▸ one_ne_zero :
    ∑ i, F (idem h i) () ≠ 0)
  refine ⟨i, RingHom.ext fun a => ?_⟩
  have h2 := congrArg (fun t => F t ()) (one_tmul_mul_idem h i a)
  simp only [map_mul, map_smul, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h2
  have h3 : F (1 ⊗ₜ a) () = χ a := by simp [F]
  rw [h3] at h2
  exact (mul_right_cancel₀ hi h2).symm
private theorem exists_det_sq (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE]
    [Module.Free ℤ OE] [Module.Finite ℤ OE] [DecidableEq (Module.Free.ChooseBasisIndex ℤ OE)]
    (K : Type) [Field K] [CharZero K] [Algebra OE K] [IsFractionRing OE K]
    (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (R : Type) [CommRing R] [Algebra R C] (hv : v.Integers R) :
    ∃ σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R,
      ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : R) =
        (Matrix.of fun i j => σ i (Module.Free.chooseBasis ℤ OE j)).det ^ 2 := by
  have : IsScalarTower ℤ OE K := AddCommGroup.intIsScalarTower
  have : IsLocalization (Algebra.algebraMapSubmonoid OE (nonZeroDivisors ℤ)) K := inferInstance
  set b := Module.Free.chooseBasis ℤ OE with hb
  let bK := b.localizationLocalization ℚ (nonZeroDivisors ℤ) K
  have : Module.Finite ℚ K := Module.Finite.of_basis bK
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ OE) = Fintype.card (K →ₐ[ℚ] C) := by
    rw [AlgHom.card, Module.finrank_eq_card_basis bK]
  let e := Fintype.equivOfCardEq hcard
  have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ C bK e
  rw [Algebra.discr_localizationLocalization] at h1
  have hent : ∀ j a, ∃ r : R, algebraMap R C r = e j (algebraMap OE K a) := by
    intro j a
    apply hv.exists_of_le_one
    apply hv.mem_of_integral
    have : IsIntegral ℤ (e j (algebraMap OE K a)) :=
      (Algebra.IsIntegral.isIntegral (R := ℤ) a).map
        ((e j).toRingHom.comp (algebraMap OE K)).toIntAlgHom
    exact this.tower_top
  choose N hN using hent
  let σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* R := fun j =>
    { toFun := N j
      map_one' := hv.hom_inj (by simp [hN])
      map_mul' := fun x y => hv.hom_inj (by simp [hN])
      map_zero' := hv.hom_inj (by simp [hN])
      map_add' := fun x y => hv.hom_inj (by simp [hN]) }
  refine ⟨σ, ?_⟩
  have hM : Algebra.embeddingsMatrixReindex ℚ C bK e =
      (algebraMap R C).mapMatrix (Matrix.of fun i j => σ i (b j)).transpose := by
    ext i j
    simp [Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, hN, bK, σ]
  rw [hM, ← RingHom.map_det, ← map_pow, Matrix.det_transpose] at h1
  apply hv.hom_inj
  rw [← h1]
  simp
private theorem exists_isSplitting (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C]
    [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    (hv : v.Integers O) (hp : ¬IsUnit (p : O)) [IsLocalRing O] (OE : Type) [CommRing OE]
    [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE]
    (hd : ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE))) :
    ∃ σ : Module.Free.ChooseBasisIndex ℤ OE → OE →+* O, IsSplitting σ := by
  classical
  obtain ⟨σ, hσ⟩ := exists_det_sq OE (FractionRing OE) C v O hv
  refine ⟨σ, (isSplitting_iff_isUnit_det σ (Module.Free.chooseBasis ℤ OE)).2 ?_⟩
  by_contra hdet
  have hdm : ((Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE) : ℤ) : O) ∈
      IsLocalRing.maximalIdeal O := by
    rw [hσ]
    exact Ideal.pow_mem_of_mem _ (by exact hdet) 2 (by norm_num)
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O := hp
  have hcop : IsCoprime (p : ℤ) (Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) :=
    (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 Fact.out)).2 hd
  obtain ⟨a, b, hab⟩ := hcop
  have h1 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    have := congrArg (Int.cast : ℤ → O) hab
    push_cast at this
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hpm) (Ideal.mul_mem_left _ _ hdm)
  exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end GlobalTheory.SplittingIdempotents
end

set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SplittingIdempotents
open GlobalTheory.EigenSplit
namespace GlobalTheory.SplittingIdempotents
theorem _root_.solution : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsLocalRing O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE], ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∃ (m : ℕ) (τ : Fin m ≃ (OE →+* O)) (ε : Fin m → O ⊗[ℤ] OE) (φ : Equiv.Perm (Fin m)), CompleteOrthogonalIdempotents ε ∧ (∀ i a, (1 ⊗ₜ[ℤ] a) * ε i = τ i a • ε i) ∧ (∀ i j, i ≠ j → ∃ a, IsUnit (τ i a - τ j a)) ∧ ∀ i a, τ (φ i) a - τ i a ^ p ∈ IsLocalRing.maximalIdeal O := by
  intro p _ C _ _ _ v O _ _ hv hp _ _ OE _ _ _ _ _ hd
  classical
  obtain ⟨σ, hσ⟩ := exists_isSplitting p C v O hv hp.out OE hd
  have : IsDomain O := hv.hom_inj.isDomain
  let ι := Module.Free.ChooseBasisIndex ℤ OE
  let k := IsLocalRing.ResidueField O
  let r : O →+* k := IsLocalRing.residue O
  have hσk : IsSplitting (fun i => r.comp (σ i)) := hσ.map r
  have hinj := hσk.injective
  have hpk : (p : k) = 0 := by
    rw [← map_natCast r]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hp.out
  have : CharP k p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hpk
  have hbij : Function.Bijective σ :=
    ⟨hσ.injective, fun χ => exists_eq_of_isSplitting hσ χ⟩
  choose f hf using fun i => exists_eq_of_isSplitting hσk ((frobenius k p).comp (r.comp (σ i)))
  have hfi : Function.Injective f := by
    intro i j hij
    apply hinj
    ext a
    apply frobenius_inj k p
    have h1 := DFunLike.congr_fun (hf i) a
    have h2 := DFunLike.congr_fun (hf j) a
    rw [hij] at h1
    exact h1.symm.trans h2
  let φ : Equiv.Perm ι := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hfi)
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, e.trans (Equiv.ofBijective σ hbij), idem hσ ∘ e,
    (e.trans φ).trans e.symm, ?_, fun i a => ?_, fun i j hij => ?_, fun i a => ?_⟩
  · exact (CompleteOrthogonalIdempotents.equiv e).2 (completeOrthogonalIdempotents_idem hσ)
  · exact one_tmul_mul_idem hσ (e i) a
  · by_contra hne
    push Not at hne
    apply hij
    apply e.injective
    apply hinj
    ext a
    exact Ideal.Quotient.eq.2 (hne a)
  · have h1 := DFunLike.congr_fun (hf (e i)) a
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.ofBijective_apply, φ]
    apply Ideal.Quotient.eq.1
    change r _ = r _
    rw [map_pow]
    exact h1
end GlobalTheory.SplittingIdempotents
