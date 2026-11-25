-- Prove2me | solution 1 for GlobalTheory.crt_approx_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:59:54.545737+00:00
-- url     : https://prove2.me/submissions/32d3361c-42a0-488c-a76b-349494d247ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CrtApproxIntegral
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply



set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A : ValuationSubring Ω)
    (c : ℕ), c ≠ 0 →
    ∃ t ∈ K, IsIntegral ℤ t ∧ A.valuation (t - 1) ≤ A.valuation (c : Ω) ∧
      ∀ σ : G E Ω, (∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)) →
        A.valuation (σ t) ≤ A.valuation (c : Ω) := by
  intro E Ω _ _ _ _ _ K _ A c hc
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  haveI : NumberField K := { to_charZero := inferInstance, to_finiteDimensional := Module.Finite.trans E K }
  have hint : ∀ {y : Ω}, IsIntegral ℤ y → A.valuation y ≤ 1 := fun hy =>
    (A.valuation_le_one_iff _).2 (mem_of_isIntegral_int A hy)
  by_cases hcP : A.valuation (c : Ω) < 1
  swap
  · have h1 : 1 ≤ A.valuation (c : Ω) := not_lt.mp hcP
    refine ⟨1, K.one_mem, isIntegral_one, ?_, fun σ _ => ?_⟩
    · rw [sub_self, map_zero]; exact zero_le'
    · rw [map_one, map_one]; exact h1
  set f : 𝓞 K →+* Ω := (algebraMap K Ω).comp (algebraMap (𝓞 K) K) with hf
  have fint : ∀ r : 𝓞 K, IsIntegral ℤ (f r) := fun r =>
    (RingOfIntegers.isIntegral_coe r).map (algebraMap K Ω).toIntAlgHom
  let Pg : (g : 𝓞 K →+* Ω) → (∀ r, IsIntegral ℤ (g r)) → Ideal (𝓞 K) := fun g hg =>
    (IsLocalRing.maximalIdeal A).comap (g.codRestrict A (fun r => mem_of_isIntegral_int A (hg r)))
  have memPg : ∀ g hg r, r ∈ Pg g hg ↔ A.valuation (g r) < 1 := fun g hg r => by
    simp only [Pg, Ideal.mem_comap]; exact A.valuation_lt_one_iff _
  have primePg : ∀ g hg, (Pg g hg).IsPrime := fun g hg => Ideal.comap_isPrime _ _
  have key : ∀ (g : 𝓞 K →+* Ω) (hg : ∀ r, IsIntegral ℤ (g r)) (s u : 𝓞 K), s ∉ Pg g hg →
      s * u ∈ Ideal.span {(c : 𝓞 K)} → A.valuation (g u) ≤ A.valuation (c : Ω) := by
    intro g hg s u hs hsu
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hsu
    have hs1 : A.valuation (g s) = 1 :=
      le_antisymm (hint (hg s)) (not_lt.mp fun h => hs ((memPg g hg s).2 h))
    have := congrArg (fun y => A.valuation (g y)) hw
    simp only [map_mul, map_natCast, hs1, one_mul] at this
    rw [← this]
    exact mul_le_of_le_one_left' (hint (hg w))
  have hcP' : (c : 𝓞 K) ∈ Pg f fint := (memPg f fint _).2 (by rwa [map_natCast])
  have hPne : Pg f fint ≠ ⊥ := fun h => by
    have h' := hcP'
    rw [h, Ideal.mem_bot] at h'
    exact hc (by exact_mod_cast h')
  haveI hPmax : (Pg f fint).IsMaximal := Ideal.IsPrime.isMaximal (primePg f fint) hPne
  have hI : Ideal.span {(c : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hc
  classical
  obtain ⟨J, hPJ, hIJ⟩ := Ideal.eq_prime_pow_mul_coprime hI (Pg f fint)
  set a := Multiset.count (Pg f fint)
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(c : 𝓞 K)})) with ha
  have hJP : J ⊔ Pg f fint ^ a = ⊤ := Ideal.sup_pow_eq_top (by rwa [sup_comm])
  have h1mem : (1 : 𝓞 K) ∈ J ⊔ Pg f fint ^ a := by rw [hJP]; exact Submodule.mem_top
  obtain ⟨z, hz, y, hy, hzy⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨s, hsJ, hsP⟩ : ∃ s ∈ J, s ∉ Pg f fint := by
    by_contra hcon
    push_neg at hcon
    rw [sup_eq_left.2 hcon] at hPJ
    exact hPmax.ne_top hPJ
  have hz1 : z - 1 ∈ Pg f fint ^ a := by
    have e : z - 1 = -y := by rw [← hzy]; ring
    rw [e]; exact neg_mem hy
  refine ⟨f z, (algebraMap (𝓞 K) K z).2, fint z, ?_, ?_⟩
  · have := key f fint s (z - 1) hsP (by rw [hIJ, mul_comm s]; exact Ideal.mul_mem_mul hz1 hsJ)
    simpa only [map_sub, map_one] using this
  · rintro σ ⟨x, hxK, hxint, hx⟩
    set g : 𝓞 K →+* Ω := (σ : Ω →+* Ω).comp f with hg
    have gint : ∀ r, IsIntegral ℤ (g r) := fun r => (fint r).map (σ : Ω →+* Ω).toIntAlgHom
    have hxK' : IsIntegral ℤ (⟨x, hxK⟩ : K) :=
      (isIntegral_algHom_iff (algebraMap K Ω).toIntAlgHom (algebraMap K Ω).injective).1 hxint
    let r : 𝓞 K := ⟨⟨x, hxK⟩, hxK'⟩
    have hne : Pg g gint ≠ Pg f fint := by
      intro heq
      apply hx
      have h1 := memPg g gint r
      have h2 := memPg f fint r
      rw [heq] at h1
      exact h1.symm.trans h2
    obtain ⟨s', hs'P, hs'Q⟩ : ∃ s' ∈ Pg f fint ^ a, s' ∉ Pg g gint := by
      by_contra hcon
      push_neg at hcon
      haveI := primePg g gint
      have h1 : Pg f fint ≤ Pg g gint := Ideal.IsPrime.le_of_pow_le hcon
      exact hne (hPmax.eq_of_le (primePg g gint).ne_top h1).symm
    have := key g gint s' z hs'Q (by rw [hIJ]; exact Ideal.mul_mem_mul hs'P hz)
    exact this
end GlobalTheory
