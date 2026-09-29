-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/b4454875-e159-5dad-a23c-7c9d74a6c4c5

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      ∃ t : Spec (CommRingCat.of (IsLocalRing.ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        t ≫ pullback.snd _ _ = 𝟙 _ ∧
        t.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField ↥A)) =
          (𝔛.comp A hA ρ hρ 0).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n) := by
  intro n

  obtain ⟨-, ⟨hc, -⟩⟩ := 𝔛.node_pin A hA ρ hρ n
  have hcl : IsClosed ({(inv (𝔛.efib A hA ρ hρ)).base ((pullback.fst (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)).base n)} :
      Set (𝔛.Mfib A hA ρ hρ).C) := hc

  let q := pointOfClosedPoint (𝔛.Mfib A hA ρ hρ).toBase _ hcl
  refine ⟨q ≫ 𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, 𝔛.comp_over A hA ρ hρ 0, 𝔛.hefib A hA ρ hρ, pointOfClosedPoint_comp]
  · rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, pointOfClosedPoint_apply, ← Scheme.Hom.comp_apply (inv _),
      IsIso.inv_hom_id]
    rfl

end S_ModularCurve_XHDRModelAtP_forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_forall_exists_spec_hom_fibre_comp_snd_eq_id_and_base_closedPoint_eq_comp_fst (solution)
