-- Prove2me | solution 1 for ModularCurve.characterLattice_evalHom_surjective_and_trivial_iff_const
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/bc52586e-8324-5246-8754-c6da284c6059

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const

set_option autoImplicit false

open ModularCurve ModularCurve.CharacterLattice Finset

namespace DZLTorusAux

variable {S : Type*} [Fintype S] [DecidableEq S]

def dzlE (s₀ s : S) : characterLattice S :=
  ⟨Pi.single s 1 - Pi.single s₀ 1, single_sub_single_mem s s₀⟩

@[scoped simp]
theorem coe_dzlE (s₀ s : S) : (dzlE s₀ s : S → ℤ) = Pi.single s 1 - Pi.single s₀ 1 := rfl

theorem sum_smul_dzlE (s₀ : S) (a : characterLattice S) :
    ∑ s, (a : S → ℤ) s • dzlE s₀ s = a := by
  have ha : ∑ s, (a : S → ℤ) s = 0 := mem_characterLattice.1 a.2
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum]
  funext t
  simp only [Finset.sum_apply, Submodule.coe_smul_of_tower, coe_dzlE, Pi.smul_apply, Pi.sub_apply,
    smul_eq_mul, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases ht : t = s₀ <;> simp [ht, ha]

variable {G : Type*} [CommGroup G]

theorem prod_zpow_single (s : S) (n : ℤ) (w : S → G) :
    ∏ t, w t ^ (Pi.single s n : S → ℤ) t = w s ^ n := by
  rw [Fintype.prod_eq_single s fun t ht => by rw [Pi.single_eq_of_ne ht, zpow_zero], Pi.single_eq_same]

theorem evalHom_dzlE (s₀ s : S) (w : S → G) : evalHom (dzlE s₀ s) w = w s * (w s₀)⁻¹ := by
  show zpowProd (Pi.single s (1 : ℤ) - Pi.single s₀ 1) w = _
  rw [sub_eq_add_neg, zpowProd_add, zpowProd_neg, zpowProd_def, zpowProd_def, prod_zpow_single,
    prod_zpow_single, zpow_one, zpow_one]

end DZLTorusAux
p2m_reactivate "P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.DZLTorusAux"

open DZLTorusAux in
theorem solution
    (S : Type*) [Fintype S] [Nonempty S] (G : Type*) [CommGroup G] :
    (∀ χ : ModularCurve.characterLattice S →+ Additive G,
        ∃ w : S → G, ∀ a, Additive.toMul (χ a) = ModularCurve.CharacterLattice.evalHom a w) ∧
    (∀ w : S → G, (∀ a : ModularCurve.characterLattice S, ModularCurve.CharacterLattice.evalHom a w = 1) ↔
        ∃ c : G, w = fun _ => c) := by
  classical
  obtain ⟨s₀⟩ := ‹Nonempty S›
  refine ⟨fun χ => ?_, fun w => ⟨fun h => ⟨w s₀, funext fun s => ?_⟩, ?_⟩⟩
  · refine ⟨fun s => Additive.toMul (χ (dzlE s₀ s)), fun a => ?_⟩
    rw [evalHom_apply]
    conv_lhs => rw [← sum_smul_dzlE s₀ a, map_sum, toMul_sum]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_zsmul, toMul_zsmul]
  · have hs := h (dzlE s₀ s)
    rw [evalHom_dzlE] at hs
    exact mul_inv_eq_one.mp hs
  · rintro ⟨c, rfl⟩ a
    exact evalHom_const a c

end S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const
end P2MW
export P2MW.S_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const (solution)
