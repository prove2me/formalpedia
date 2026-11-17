-- Prove2me | solution 1 for N25.GlobalKummer.cyclotomic_roots_equiv
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:35:44.893621+00:00
-- url     : https://prove2.me/submissions/01021219-4c1e-484b-88e5-3848457d1295

import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance instL_N25_GlobalKummer_cyclotomic_roots_equiv_23397f_sa5e78c : Fact (Nat.Prime 71) := ⟨by decide⟩

/-- The frozen cyclotomic line is equivariantly the additive group of actual
71st roots of unity in the chosen algebraic closure. -/
theorem _root_.solution :
    ∃ e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)),
      ∀ (σ : Gal) (a : ZMod 71),
        e ((ExtCitation.cycloChar 71 σ : ZMod 71) * a) =
          Additive.ofMul (σ • Additive.toMul (e a)) := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ 71 :=
    card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp
      (IsAlgClosed.card_rootsOfUnity_eq (AlgebraicClosure ℚ) 71)
  let u : (AlgebraicClosure ℚ)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 71 := hζ.isUnit_unit (by decide)
  let e : ZMod 71 ≃+ Additive (rootsOfUnity 71 (AlgebraicClosure ℚ)) := by
    rw [← hu.zpowers_eq]
    exact hu.zmodEquivZPowers
  have haction (σ : Gal) (v : rootsOfUnity 71 (AlgebraicClosure ℚ)) :
      σ • v = v ^ (ExtCitation.cycloChar 71 σ : ZMod 71).val := by
    apply Subtype.ext
    apply Units.ext
    exact modularCyclotomicCharacter.spec (AlgebraicClosure ℚ)
      (ExtCitation.card_rootsOfUnity_eq_self 71) σ.toRingEquiv v.property
  refine ⟨e, ?_⟩
  intro σ a
  have hm : (ExtCitation.cycloChar 71 σ : ZMod 71) * a =
      (ExtCitation.cycloChar 71 σ : ZMod 71).val • a := by
    simp only [nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id]
  rw [hm, map_nsmul]
  change Additive.ofMul ((Additive.toMul (e a)) ^
      (ExtCitation.cycloChar 71 σ : ZMod 71).val) =
    Additive.ofMul (σ • Additive.toMul (e a))
  exact congrArg Additive.ofMul (haction σ (Additive.toMul (e a))).symm

end N25.GlobalKummer
