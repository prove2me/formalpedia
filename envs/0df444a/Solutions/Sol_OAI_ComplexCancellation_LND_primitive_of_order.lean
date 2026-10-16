-- Prove2me | solution 1 for OAI.ComplexCancellation.LND.primitive_of_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:39:51.414275+00:00
-- url     : https://prove2.me/submissions/b47153ea-1762-4f33-b9d3-c9cf50f0da94

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Primitive.lean:L29-L54
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.LND.primitive_of_order. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Theorems.Thm_OAI_ComplexCancellation_LND_cancel_factor_locallyNilpotent

-- ---- from OAI.Algebra.AffineCancellation.FactorDerivation ----
namespace OAI

noncomputable section

namespace ComplexCancellation.FactorDerivation
variable {k S R : Type*} [CommRing k] [CommRing S] [CommRing R] [IsDomain R]
  [Algebra k S] [Algebra k R]
variable (f : S →ₐ[k] R) (hf : Function.Injective f)
  (D : Derivation k R R) (c : R) (hc : c ≠ 0)
  (h : ∀ s : S, ∃ t : S, D (f s)=c*f t)
lemma apply_spec (s : S) : D (f s)=c*f (derivation f hf D c hc h s) := specification f D c h s
end ComplexCancellation.FactorDerivation

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Primitive ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]
/-- Remove all common powers of a regular parameter from an LND.
The termination certificate is the exact finite order of a single nonzero image. -/
lemma primitive_of_order (q : R) (hq : q ≠ 0) (w b s : R) (hs : ¬q ∣ s)
    (n : ℕ) (D : Derivation k R R) (hD : LocallyNilpotent D)
    (hDq : D q=0) (hDw : D w=0) (hb : D b=q^n*s) :
    ∃ E : Derivation k R R, LocallyNilpotent E ∧ E q=0 ∧ E w=0 ∧ ∃ r, ¬q ∣ E r := by
  induction n generalizing D with
  | zero =>
    refine ⟨D,hD,hDq,hDw,b,?_⟩
    rw [hb,pow_zero,one_mul]
    exact hs
  | succ n ih =>
    by_cases h : ∃ r, ¬q ∣ D r
    · exact ⟨D,hD,hDq,hDw,h⟩
    · push Not at h
      let f := AlgHom.id k R
      have hfac : ∀ r : R, ∃ s : R, D (f r)=q*f s := h
      let E := FactorDerivation.derivation f Function.injective_id D q hq hfac
      have he (r : R) : D r=q*E r := FactorDerivation.apply_spec f Function.injective_id D q hq hfac r
      have hE : LocallyNilpotent E := cancel_factor_locallyNilpotent f Function.injective_id D hD E hq he
      have hEq : E q=0 := (mul_eq_zero.mp (by rw [← he,hDq])).resolve_left hq
      have hEw : E w=0 := (mul_eq_zero.mp (by rw [← he,hDw])).resolve_left hq
      apply ih E hE hEq hEw
      apply mul_left_cancel₀ hq
      rw [← he,hb,pow_succ]
      ring
end ComplexCancellation.LND

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.LND


theorem solution : type_of% @_root_.OAI.ComplexCancellation.LND.primitive_of_order := @_root_.OAI.ComplexCancellation.LND.primitive_of_order
