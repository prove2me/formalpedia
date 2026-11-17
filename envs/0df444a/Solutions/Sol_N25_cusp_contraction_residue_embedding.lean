-- Prove2me | solution 1 for N25.cusp_contraction_residue_embedding
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:31.168064+00:00
-- url     : https://prove2.me/submissions/8404cdce-ff3e-4e80-be78-2374a5f262be

import Mathlib
import Definitions.Def_N25_Endgame

set_option autoImplicit false

noncomputable section

namespace N25

open Endgame AlgebraicCurve

/-- Contraction of an actual geometric place gives the canonical injective residue map. -/
theorem _root_.solution (Q : QPlace) (P : GPlace)
    (hQ : Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom) :
    ∃ ρ : Q.ResidueField →+* P.ResidueField,
      Function.Injective ρ ∧
      ∀ a : Q.toValuationSubring,
        ρ (IsLocalRing.residue _ a) =
          IsLocalRing.residue P.toValuationSubring
            ⟨emb25 a, by
              exact (congrArg (fun S : ValuationSubring FQ => (a : FQ) ∈ S) hQ).mp a.property⟩ := by
  let f : Q.toValuationSubring →+* P.toValuationSubring :=
    { toFun := fun a => ⟨emb25 a, by
        exact (congrArg (fun S : ValuationSubring FQ => (a : FQ) ∈ S) hQ).mp a.property⟩
      map_one' := Subtype.ext (map_one emb25)
      map_mul' a b := Subtype.ext (map_mul emb25 (a : FQ) (b : FQ))
      map_zero' := Subtype.ext (map_zero emb25)
      map_add' a b := Subtype.ext (map_add emb25 (a : FQ) (b : FQ)) }
  have : IsLocalHom f :=
    { map_nonunit := by
        intro a ha
        have ha0 : (a : FQ) ≠ 0 := by
          intro hz
          apply ha.ne_zero
          apply Subtype.ext
          change emb25 (a : FQ) = 0
          rw [hz, map_zero]
        have hi : (emb25 (a : FQ))⁻¹ ∈ P.toValuationSubring := by
          obtain ⟨b,hb⟩ := isUnit_iff_exists_inv.mp ha
          have hbF : emb25 (a : FQ) * (b : FG) = 1 := congrArg Subtype.val hb
          have hn : emb25 (a : FQ) ≠ 0 := by
            intro hz
            apply ha0
            exact emb25.toRingHom.injective (hz.trans (map_zero emb25.toRingHom).symm)
          have hbEq : (b : FG) = (emb25 (a : FQ))⁻¹ := by
            apply mul_left_cancel₀ hn
            rw [mul_inv_cancel₀ hn]
            exact hbF
          exact hbEq ▸ b.property
        have hia : (a : FQ)⁻¹ ∈ Q.toValuationSubring := by
          apply (congrArg (fun S : ValuationSubring FQ => (a : FQ)⁻¹ ∈ S) hQ).mpr
          change emb25 ((a : FQ)⁻¹) ∈ P.toValuationSubring
          rw [map_inv₀]
          exact hi
        exact isUnit_iff_exists_inv.mpr ⟨⟨(a : FQ)⁻¹, hia⟩,
          Subtype.ext (mul_inv_cancel₀ ha0)⟩ }
  refine ⟨IsLocalRing.ResidueField.map f,
    (IsLocalRing.ResidueField.map f).injective, ?_⟩
  intro a
  exact IsLocalRing.ResidueField.map_residue f a

end N25
