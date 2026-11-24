-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SiegelChar.finite_nonunit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:47.900191+00:00
-- url     : https://prove2.me/submissions/34565c02-19ab-492d-a823-cfaa3725e72c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_SplitQuadraticAlgebraOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix ValuativeRel GlobalTheory.WeilM MeasureTheory
open scoped ComplexConjugate NNReal
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelChar
namespace GlobalTheory.CompanionTheory.SiegelChar
theorem _root_.solution {F : Type} [Field F] {E : Type} [CommRing E] [Algebra F E] [Module.Finite F E]
    (p : Polynomial E) (τ : E) (h : IsUnit (p.eval τ)) : {t : F | ¬ IsUnit (p.eval (algebraMap F E t))}.Finite := by
  classical
  haveI : IsArtinianRing E := IsArtinianRing.of_finite F E
  have hmax : {m : Ideal E | m.IsMaximal}.Finite := IsArtinianRing.setOf_isMaximal_finite E
  have key : ∀ m : Ideal E, m.IsMaximal → {t : F | p.eval (algebraMap F E t) ∈ m}.Finite := by
    intro m hm
    haveI := hm
    letI : Field (E ⧸ m) := Ideal.Quotient.field m
    obtain ⟨q, hq⟩ : ∃ q : Polynomial (E ⧸ m), q = p.map (Ideal.Quotient.mk m) := ⟨_, rfl⟩
    have hev : ∀ z : E, q.eval (Ideal.Quotient.mk m z) = Ideal.Quotient.mk m (p.eval z) := by
      intro z
      rw [hq, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    have hq0 : q ≠ 0 := by
      intro h0
      have h1 := hev τ
      rw [h0, Polynomial.eval_zero] at h1
      exact (h.map (Ideal.Quotient.mk m)).ne_zero h1.symm
    have hinj : Function.Injective ((Ideal.Quotient.mk m).comp (algebraMap F E)) := RingHom.injective _
    refine ((q.roots.toFinset.finite_toSet).preimage hinj.injOn).subset ?_
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, RingHom.comp_apply]
    rw [Polynomial.mem_roots hq0, Polynomial.IsRoot, hev]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ht
  refine (hmax.biUnion fun m hm => key m hm).subset ?_
  intro t ht
  obtain ⟨m, hm, htm⟩ := exists_max_ideal_of_mem_nonunits ht
  exact Set.mem_biUnion hm htm
end GlobalTheory.CompanionTheory.SiegelChar
