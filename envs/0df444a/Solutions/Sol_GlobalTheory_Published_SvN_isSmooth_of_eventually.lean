-- Prove2me | solution 1 for GlobalTheory.Published.SvN.isSmooth_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:29:21.059131+00:00
-- url     : https://prove2.me/submissions/b4849e2d-7786-40d6-a0f6-2cad171ec69b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfPowClose
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_PlaneFormNondegenerate
import Theorems.Thm_P2M_GlobalTheory_Published_SvN_eventually_psi__9e5e2c7b09ad
import Theorems.Thm_GlobalTheory_Published_SvN_apply_eq
import Theorems.Thm_GlobalTheory_Published_Heisenberg_isTopologicalGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.Published
open GlobalTheory.Published.SvN
open Heisenberg
variable {F W M : Type} [Field F] [AddCommGroup W] [Module F W] {B : LinearMap.BilinForm F W} [AddCommGroup M] [Module ℂ M]
  {ψ : AddChar F ℂ} {π : Representation ℂ (Heisenberg B) M}
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [FiniteDimensional F W] [TopologicalSpace W]
  [IsModuleTopology F W]
namespace GlobalTheory.Published.SvN
theorem _root_.solution (hψ : Continuous ψ) (hπ : ∀ t v, π ⟨0, t⟩ v = ψ t • v)
    (hs : ∀ v, ∀ᶠ u in 𝓝 (0 : W), π ⟨u, 0⟩ v = v) : PRep.IsSmooth π := by
  intro v
  have := Heisenberg.isTopologicalGroup (B := B)
  have h0 : Continuous fun g : Heisenberg B => (g.vec, g.cen) := continuous_induced_dom
  let S : Subgroup (Heisenberg B) :=
    { carrier := {g | π g v = v}
      mul_mem' := fun {x y} hx hy => by
        show π (x * y) v = v
        rw [map_mul, Module.End.mul_apply, hy, hx]
      one_mem' := by simp
      inv_mem' := fun {x} hx => by
        show π x⁻¹ v = v
        conv_lhs => rw [← show π x v = v from hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp }
  refine S.isOpen_of_mem_nhds (g := 1) ?_
  filter_upwards [(h0.fst.tendsto' 1 0 rfl).eventually (hs v), (h0.snd.tendsto' 1 0 rfl).eventually (eventually_psi' hψ)]
    with g h1 h2
  show π g v = v
  rw [apply_eq hπ, h1, h2, one_smul]
end GlobalTheory.Published.SvN
