-- Prove2me | solution 1 for MvPolynomial.exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8fa5ed61-5ca6-5cb5-8e69-bb2fe8138224

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000
set_option Elab.async false

universe u

theorem solution
    (R : Type u) [CommRing R] (N : ℕ) (f : Fin N → MvPolynomial (Fin N) R)
    (e : MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) (he : IsIdempotentElem e) :
    ∃ f' : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R,
      Nonempty ((MvPolynomial (Fin (N + 1)) R ⧸ Ideal.span (Set.range f')) ≃ₐ[R]
        ((MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) ⧸ Ideal.span {e})) := by
  classical

  obtain ⟨et, het⟩ := Ideal.Quotient.mk_surjective e
  let ι : MvPolynomial (Fin N) R →ₐ[R] MvPolynomial (Fin (N + 1)) R := MvPolynomial.rename Fin.castSucc
  let Y : MvPolynomial (Fin (N + 1)) R := MvPolynomial.X (Fin.last N)
  let f' : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R :=
    fun j => Fin.lastCases (motive := fun _ => MvPolynomial (Fin (N + 1)) R) (Y * (1 - ι et) - 1) (fun i => ι (f i)) j
  have hf'last : f' (Fin.last N) = Y * (1 - ι et) - 1 := Fin.lastCases_last
  have hf'cast : ∀ i, f' (Fin.castSucc i) = ι (f i) := fun i => Fin.lastCases_castSucc (i := i)
  refine ⟨f', ⟨?_⟩⟩

  let mkA := Ideal.Quotient.mkₐ R (Ideal.span (Set.range f))
  let mkB := Ideal.Quotient.mkₐ R (Ideal.span ({e} : Set (MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f))))
  let mkQ := Ideal.Quotient.mkₐ R (Ideal.span (Set.range f'))

  let φ : MvPolynomial (Fin (N + 1)) R →ₐ[R] (MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) ⧸
      Ideal.span ({e} : Set (MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f))) :=
    MvPolynomial.aeval fun j => Fin.lastCases (motive := fun _ => _) 1 (fun i => mkB (mkA (MvPolynomial.X i))) j
  have hφι : φ.comp ι = mkB.comp mkA := by
    refine MvPolynomial.algHom_ext fun i => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply]
    change MvPolynomial.aeval _ (MvPolynomial.rename Fin.castSucc (MvPolynomial.X i)) = _
    rw [MvPolynomial.rename_X, MvPolynomial.aeval_X]
    exact Fin.lastCases_castSucc (i := i)
  have hφι' : ∀ p, φ (ι p) = mkB (mkA p) := fun p => AlgHom.congr_fun hφι p
  have hφY : φ Y = 1 := by
    change MvPolynomial.aeval _ (MvPolynomial.X (Fin.last N)) = 1
    rw [MvPolynomial.aeval_X]
    exact Fin.lastCases_last
  have hBe : mkB (mkA et) = 0 := by
    change Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span (Set.range f)) et) = 0
    rw [het]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have hφI' : ∀ a ∈ Ideal.span (Set.range f'), φ a = 0 := by
    suffices h : Ideal.span (Set.range f') ≤ RingHom.ker φ from fun a ha => h ha
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    refine Fin.lastCases ?_ (fun i => ?_) j
    · change φ (f' (Fin.last N)) = 0
      rw [hf'last, map_sub, map_mul, map_sub, map_one, hφY, hφι', hBe]; ring
    · change φ (f' (Fin.castSucc i)) = 0
      rw [hf'cast, hφι']
      change mkB (Ideal.Quotient.mk (Ideal.span (Set.range f)) (f i)) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self i)), map_zero]
  let φbar := Ideal.Quotient.liftₐ (Ideal.span (Set.range f')) φ hφI'

  let ψ₀ : MvPolynomial (Fin N) R →ₐ[R] MvPolynomial (Fin (N + 1)) R ⧸ Ideal.span (Set.range f') := mkQ.comp ι
  have hψ₀I : ∀ a ∈ Ideal.span (Set.range f), ψ₀ a = 0 := by
    suffices h : Ideal.span (Set.range f) ≤ RingHom.ker ψ₀ from fun a ha => h ha
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    change Ideal.Quotient.mk (Ideal.span (Set.range f')) (ι (f i)) = 0
    rw [← hf'cast]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self _))
  let ψ₁ := Ideal.Quotient.liftₐ (Ideal.span (Set.range f)) ψ₀ hψ₀I

  have hεY : mkQ Y * (1 - mkQ (ι et)) = 1 := by
    have h : mkQ (f' (Fin.last N)) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self _))
    rw [hf'last, map_sub, map_one, sub_eq_zero, map_mul, map_sub, map_one] at h
    exact h
  have hε2 : mkQ (ι et) * mkQ (ι et) = mkQ (ι et) := by
    have h1 : Ideal.Quotient.mk (Ideal.span (Set.range f)) (et * et - et) = 0 := by
      rw [map_sub, map_mul, het, sub_eq_zero]; exact he.eq
    have h2 : ψ₁ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (et * et - et)) = 0 := by rw [h1, map_zero]
    have h3 : ψ₁ (Ideal.Quotient.mk (Ideal.span (Set.range f)) (et * et - et)) = ψ₀ (et * et - et) := Ideal.Quotient.liftₐ_apply _ _ _ _
    rw [h3, map_sub, map_mul, sub_eq_zero] at h2
    exact h2
  have hε0 : mkQ (ι et) = 0 := by
    calc mkQ (ι et) = mkQ (ι et) * (mkQ Y * (1 - mkQ (ι et))) := by rw [hεY, mul_one]
      _ = mkQ Y * (mkQ (ι et) - mkQ (ι et) * mkQ (ι et)) := by ring
      _ = 0 := by rw [hε2, sub_self, mul_zero]
  have hY1 : mkQ Y = 1 := by rw [← hεY, hε0, sub_zero, mul_one]
  have hψ₁e : ∀ a ∈ Ideal.span ({e} : Set (MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f))), ψ₁ a = 0 := by
    suffices h : Ideal.span ({e} : Set (MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f))) ≤ RingHom.ker ψ₁ from fun a ha => h ha
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, ← het]
    change ψ₁ (Ideal.Quotient.mk (Ideal.span (Set.range f)) et) = 0
    rw [Ideal.Quotient.liftₐ_apply]
    exact hε0
  let ψ := Ideal.Quotient.liftₐ _ ψ₁ hψ₁e

  refine AlgEquiv.ofAlgHom φbar ψ ?_ ?_
  · refine Ideal.Quotient.algHom_ext _ (Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i => ?_))
    change φbar (ψ (mkB (mkA (MvPolynomial.X i)))) = mkB (mkA (MvPolynomial.X i))
    change φbar (ψ₁ (mkA (MvPolynomial.X i))) = _
    change φbar (ψ₀ (MvPolynomial.X i)) = _
    change φ (ι (MvPolynomial.X i)) = _
    exact hφι' _
  · refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun j => ?_)
    change ψ (φbar (mkQ (MvPolynomial.X j))) = mkQ (MvPolynomial.X j)
    change ψ (φ (MvPolynomial.X j)) = _
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [hφY, map_one]
      exact hY1.symm
    · have hx : MvPolynomial.X (Fin.castSucc i) = ι (MvPolynomial.X i) := (MvPolynomial.rename_X _ _).symm
      rw [hx, hφι']
      rfl

end S_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem
end P2MW
export P2MW.S_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem (solution)
