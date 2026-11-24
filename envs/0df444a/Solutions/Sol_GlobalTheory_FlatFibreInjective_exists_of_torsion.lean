-- Prove2me | solution 1 for GlobalTheory.FlatFibreInjective.exists_of_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:13:57.872083+00:00
-- url     : https://prove2.me/submissions/23d2cdea-68e5-475c-b625-cef293a7b5bc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.FlatFibreInjective
open TensorProduct
namespace GlobalTheory.FlatFibreInjective
theorem _root_.solution {R₀ N C : Type} [CommRing R₀] [AddCommGroup N] [Module R₀ N]
    [AddCommGroup C] [Module R₀ C] [Module.Flat R₀ C] (p : Ideal R₀) (hp : p.FG)
    (x : N ⊗[R₀] C) (hx : ∀ a ∈ p, a • x = 0) :
    ∃ y, (Submodule.torsionBySet R₀ N p).subtype.rTensor C y = x := by
  classical
  obtain ⟨s, rfl⟩ := hp
  let g : N →ₗ[R₀] (s → N) := LinearMap.pi fun a => (a : R₀) • LinearMap.id
  have hex : Function.Exact (Submodule.torsionBySet R₀ N (Ideal.span (s : Set R₀))).subtype g := by
    rw [LinearMap.exact_iff, Submodule.range_subtype, ← Submodule.torsionBySet_eq_torsionBySet_span]
    ext n
    simp [g, funext_iff, LinearMap.mem_ker]
  have h := Module.Flat.rTensor_exact C hex x
  refine h.1 ?_
  apply (TensorProduct.piLeft R₀ C (fun _ : s => N)).injective
  have key : ∀ z : N ⊗[R₀] C, ∀ a : s,
      TensorProduct.piLeft R₀ C (fun _ : s => N) (g.rTensor C z) a = (a : R₀) • z := by
    intro z a
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul n c => simp [g, smul_tmul']
    | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, smul_add]
  funext a
  rw [key, hx _ (Ideal.subset_span a.2)]
  simp
end GlobalTheory.FlatFibreInjective
