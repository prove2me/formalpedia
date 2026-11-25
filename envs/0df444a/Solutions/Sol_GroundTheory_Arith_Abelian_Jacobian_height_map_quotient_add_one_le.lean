-- Prove2me | solution 1 for GroundTheory.Arith.Abelian.Jacobian.height_map_quotient_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:16:53.403674+00:00
-- url     : https://prove2.me/submissions/434a17ec-e245-4a8d-a5e4-a2770d6ccf5f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_Dimension
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian GroundTheory.Arith.Abelian.Jacobian
open Algebra Cardinal
universe u
variable (k : Type u) [Field k] {A : Type u} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra.FiniteType k A]
omit [Algebra k A] [Algebra.FiniteType k A]
namespace GroundTheory.Arith.Abelian.Jacobian
theorem _root_.solution [IsNoetherianRing A] {p₁ p : Ideal A} [p₁.IsPrime]
    [p.IsPrime] (h : p₁ ≤ p) (h0 : p₁ ≠ ⊥) :
    (p.map (Ideal.Quotient.mk p₁)).height + 1 ≤ p.height := by
  have _ : (p.map (Ideal.Quotient.mk p₁)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  obtain ⟨l, hl, hlen⟩ := (p.map (Ideal.Quotient.mk p₁)).exists_ltSeries_length_eq_height
  let l' := l.map (PrimeSpectrum.comap (Ideal.Quotient.mk p₁))
    (RingHom.strictMono_comap_of_surjective Ideal.Quotient.mk_surjective)
  have hhead : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) < l'.head := by
    rw [← PrimeSpectrum.asIdeal_lt_asIdeal, bot_lt_iff_ne_bot]
    intro hb
    apply h0
    rw [eq_bot_iff, ← hb]
    simp only [l', LTSeries.head_map, PrimeSpectrum.comap_asIdeal]
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact Ideal.zero_mem _
  let l'' := l'.cons _ hhead
  have hlast : l''.last = ⟨p, inferInstance⟩ := by
    ext1
    simp only [l'', l', RelSeries.last_cons, LTSeries.last_map, hl, PrimeSpectrum.comap_asIdeal]
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr h]
  have hle := Order.length_le_height hlast.le
  rw [← PrimeSpectrum.height_eq_orderHeight] at hle
  simpa [l'', l', ← hlen] using hle
end GroundTheory.Arith.Abelian.Jacobian
