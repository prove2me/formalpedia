-- Prove2me | solution 1 for GlobalTheory.FibreMax.exists_isMaximal_height_ge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:51:46.261947+00:00
-- url     : https://prove2.me/submissions/71947530-9218-48e8-9936-d2538365c87e

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalHeightSuccDim
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.FibreMax
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace GlobalTheory.FibreMax
theorem _root_.solution (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [FaithfulSMul k A] (d : ℕ) (hd : ringKrullDim (FractionRing k ⊗[k] A) = d) :
    ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  classical
  have hloc := IsLocalization.tensorRight (S := A) (FractionRing k) (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (FractionRing k ⊗[k] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
  let f : PrimeSpectrum (FractionRing k ⊗[k] A) → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (FractionRing k ⊗[k] A))
  have hf : StrictMono f :=
    Monotone.strictMono_of_injective (fun _ _ h ↦ Ideal.comap_mono h)
      (PrimeSpectrum.localization_comap_injective _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k)))
  let q := f l.last
  have hq : ∀ c : k, c ≠ 0 → algebraMap k A c ∉ q.asIdeal := by
    intro c hc h
    have hu : IsUnit (algebraMap A (FractionRing k ⊗[k] A) (algebraMap k A c)) :=
      IsLocalization.map_units (FractionRing k ⊗[k] A)
        (⟨algebraMap k A c, c, mem_nonZeroDivisors_of_ne_zero hc, rfl⟩ :
          Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
    exact l.last.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hne : q.asIdeal ≠ M := by
    intro heq
    haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
    haveI : Algebra.FiniteType ℤ k := inferInstance
    haveI : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance inferInstance
    letI := Ideal.Quotient.field M
    haveI : Module.Finite ℤ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ M)
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ M)) := by
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      have h1 : algebraMap ℤ (A ⧸ M) x = Ideal.Quotient.mk M (algebraMap k A (x : k)) := by simp
      rw [h1, Ideal.Quotient.eq_zero_iff_mem, ← heq] at hx
      by_contra hx0
      exact hq (x : k) (Int.cast_ne_zero.2 hx0) hx
    exact Int.not_isField ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))
  let Mp : PrimeSpectrum A := ⟨M, hM.isPrime⟩
  have hlt : (l.map f hf).last < Mp := by
    change q < Mp
    exact lt_of_le_of_ne hqM fun h ↦ hne (congrArg PrimeSpectrum.asIdeal h)
  let L := (l.map f hf).snoc Mp hlt
  have hlen : L.length = d + 1 := by simp [L, hl]
  refine ⟨M, hM, ?_⟩
  rw [show M = Mp.asIdeal from rfl, PrimeSpectrum.height_eq_orderHeight, ← hlen]
  exact Order.length_le_height (by simp [L])
end GlobalTheory.FibreMax
