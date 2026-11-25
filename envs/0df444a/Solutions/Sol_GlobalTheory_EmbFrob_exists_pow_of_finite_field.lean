-- Prove2me | solution 1 for GlobalTheory.EmbFrob.exists_pow_of_finite_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:15:38.4376+00:00
-- url     : https://prove2.me/submissions/abbb5ff5-fd47-414c-9007-2c85021a59e6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StAvDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueMaximalAbovePlace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPowOfFiniteField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory GlobalTheory.EmbFrob
open Polynomial
namespace GlobalTheory.EmbFrob
theorem _root_.solution (p : ℕ) [Fact p.Prime] {F k : Type} [Field F] [Finite F]
    [Field k] [CharP k p] (f g : F →+* k) : ∃ i : ℕ, ∀ a : F, g a = f a ^ p ^ i := by
  haveI : CharP F p := f.charP f.injective p
  letI : Algebra (ZMod p) F := ZMod.algebra F p
  letI : Algebra (ZMod p) k := ZMod.algebra k p
  letI : Algebra F k := f.toAlgebra
  haveI : IsScalarTower (ZMod p) F k := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let g' : F →ₐ[ZMod p] k :=
    { g with commutes' := fun z =>
        RingHom.congr_fun (Subsingleton.elim (g.comp (algebraMap (ZMod p) F)) (algebraMap _ k)) z }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod p) F).2
    (g'.restrictNormal' F)
  refine ⟨n, fun a => ?_⟩
  have h1 : algebraMap F k (g'.restrictNormal' F a) = g' (algebraMap F F a) :=
    AlgHom.restrictNormal_commutes g' F a
  have h2 : g'.restrictNormal' F a = a ^ p ^ (n : ℕ) := by
    rw [← hn]
    simp [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
  rw [h2, map_pow] at h1
  exact h1.symm
end GlobalTheory.EmbFrob
