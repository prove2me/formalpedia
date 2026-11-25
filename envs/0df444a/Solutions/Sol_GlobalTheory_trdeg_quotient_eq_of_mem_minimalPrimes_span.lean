-- Prove2me | solution 1 for GlobalTheory.trdeg_quotient_eq_of_mem_minimalPrimes_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:58:03.825682+00:00
-- url     : https://prove2.me/submissions/203d63c8-ca76-420c-9869-3ee668374ac2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (k : Type u) [Field k] [Algebra R k]
    (hk : Function.Surjective (algebraMap R k)) {ϖ : R} (hϖ0 : ϖ ≠ 0)
    (hker : RingHom.ker (algebraMap R k) = Ideal.span {ϖ})
    {A : Type u} [CommRing A] [IsDomain A] [Algebra R A] [Algebra.FiniteType R A]
    [FaithfulSMul R A] {q : Ideal A}
    (hq : q ∈ (Ideal.span {algebraMap R A ϖ}).minimalPrimes)
    [Algebra k (A ⧸ q)] [IsScalarTower R k (A ⧸ q)] :
    Algebra.trdeg k (A ⧸ q) = Algebra.trdeg R A := by
  have hqp := hq.1.1
  have : Algebra.FiniteType k (A ⧸ q) := .of_restrictScalars_finiteType R k _
  obtain ⟨s, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k (A ⧸ q)
  choose x hx using fun i : Fin s ↦ Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let φ : (MvPolynomial (Fin s) R) →ₐ[R] A := MvPolynomial.aeval x
  have hφ (r : (MvPolynomial (Fin s) R)) :
      Ideal.Quotient.mk q (φ r) = g (MvPolynomial.map (algebraMap R k) r) := by
    have : (Ideal.Quotient.mk q).comp φ.toRingHom =
        g.toRingHom.comp (MvPolynomial.map (algebraMap R k)) := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp only [φ, AlgHom.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
          Function.comp_apply, MvPolynomial.algHom_C, MvPolynomial.map_C]
        rw [← IsScalarTower.algebraMap_apply]
        rfl
      · intro i
        simp [φ, hx]
    exact congr($this r)
  have hmem (r : (MvPolynomial (Fin s) R)) : φ r ∈ q ↔ MvPolynomial.C ϖ ∣ r := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg, ← RingHom.mem_ker,
      MvPolynomial.ker_map, hker, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have hϖA : algebraMap R A ϖ ≠ 0 := by
    intro h
    exact hϖ0 ((FaithfulSMul.algebraMap_injective R A) (h.trans (map_zero _).symm))
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra hr0
    have hnu : ¬ IsUnit (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) := fun h ↦ hqp.ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ((hmem _).mpr dvd_rfl) (h.map φ)
    obtain ⟨n, a, ha, rfl⟩ := WfDvdMonoid.max_power_factor' hr0 hnu
    rw [map_mul, map_pow, MvPolynomial.algHom_C, mul_eq_zero] at hr
    rcases hr with hr | hr
    · exact hϖA (pow_eq_zero_iff'.mp hr).1
    · exact ha ((hmem a).mp (hr ▸ q.zero_mem))
  let := φ.toRingHom.toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin s) R) A :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (φ.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) R) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Algebra.FiniteType (MvPolynomial (Fin s) R) A :=
    .of_restrictScalars_finiteType R (MvPolynomial (Fin s) R) A
  let := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) (A ⧸ q) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) (A ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) (A ⧸ q) := ⟨hint⟩
  have : Algebra.QuasiFiniteAt (MvPolynomial (Fin s) R) q := by
    refine quasiFiniteAt_of_isolated (MvPolynomial (Fin s) R) A q
      (fun q' hq' h hle ↦ ?_) (fun q' hq' h hle ↦ ?_)
    · refine hle.antisymm (hq.2 ⟨hq', ?_⟩ hle)
      rw [Ideal.span_singleton_le_iff_mem]
      have : (MvPolynomial.C ϖ : (MvPolynomial (Fin s) R)) ∈ q'.under (MvPolynomial (Fin s) R) :=
        h.ge ((hmem _).mpr dvd_rfl)
      have : φ (MvPolynomial.C ϖ) ∈ q' := this
      simpa using this
    · have : q'.map (Ideal.Quotient.mk q) = ⊥ := by
        refine Ideal.eq_bot_of_comap_eq_bot (R := MvPolynomial (Fin s) k) (eq_bot_iff.mpr ?_)
        intro y hy
        obtain ⟨r, rfl⟩ := MvPolynomial.map_surjective _ hk y
        have hy : g (MvPolynomial.map (algebraMap R k) r) ∈ q'.map (Ideal.Quotient.mk q) := hy
        rw [← hφ, Ideal.mem_quotient_iff_mem hle] at hy
        have : φ r ∈ q := h.le (show r ∈ q'.under (MvPolynomial (Fin s) R) from hy)
        rw [← Ideal.Quotient.eq_zero_iff_mem, hφ, map_eq_zero_iff g hg] at this
        exact this
      rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at this
      exact this.antisymm hle
  have := isAlgebraic_of_quasiFiniteAt (MvPolynomial (Fin s) R) A q
  rw [trdeg_eq_of_isAlgebraic_top k (MvPolynomial (Fin s) k),
    trdeg_eq_of_isAlgebraic_top R (MvPolynomial (Fin s) R) A,
    MvPolynomial.trdeg_of_isDomain, MvPolynomial.trdeg_of_isDomain]
end GlobalTheory
