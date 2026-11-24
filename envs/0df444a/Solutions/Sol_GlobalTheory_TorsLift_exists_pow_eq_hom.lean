-- Prove2me | solution 1 for GlobalTheory.TorsLift.exists_pow_eq_hom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:24:36.302174+00:00
-- url     : https://prove2.me/submissions/8e25fd5d-67fc-456a-b3a8-573f64b5d8cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorsLift
namespace GlobalTheory.TorsLift
theorem _root_.solution {X M : Type} [AddCommGroup X] [Module.Free ℤ X] [CommGroup M] (n : ℕ)
    (h : ∀ m : M, ∃ r : M, r ^ n = m) (f : Multiplicative X →* M) :
    ∃ g : Multiplicative X →* M, g ^ n = f := by
  choose r hr using h
  let b := Module.Free.chooseBasis ℤ X
  let g : X →ₗ[ℤ] Additive M :=
    b.constr ℤ fun i => Additive.ofMul (r (f (Multiplicative.ofAdd (b i))))
  have hg : n • g = (MonoidHom.toAdditiveRight f).toIntLinearMap := by
    refine b.ext fun i => ?_
    simp only [g, LinearMap.smul_apply, Module.Basis.constr_basis]
    rw [← ofMul_pow, hr]
    rfl
  refine ⟨AddMonoidHom.toMultiplicativeLeft g.toAddMonoidHom, MonoidHom.ext fun x => ?_⟩
  exact congrArg Additive.toMul (LinearMap.congr_fun hg x.toAdd)
end GlobalTheory.TorsLift
