-- Prove2me | solution 1 for GlobalTheory.ZH.WtGen.subring_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:25:42.283843+00:00
-- url     : https://prove2.me/submissions/d32e5f69-37c1-4320-867b-8b358bcdf818

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
import Theorems.Thm_GlobalTheory_groupAlgebra_subring_eq_top


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
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
include hb
namespace GlobalTheory.ZH.WtGen
theorem _root_.solution {I : Type} (e : Module.Basis I ℤ X) (S : Subring R) (h0 : ∀ a, f a ∈ S)
    (h : ∀ i, Ideal.span {a : A | f a * m (Multiplicative.ofAdd (e i)) ∈ S} = ⊤ ∧
      Ideal.span {a : A | f a * m (Multiplicative.ofAdd (-e i)) ∈ S} = ⊤) : S = ⊤ := by
  have := GlobalTheory.groupAlgebra_subring_eq_top A X I e
    (S.comap (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
    (fun a => by
      rw [Subring.mem_comap, AddMonoidAlgebra.liftNCRingHom_single, ofAdd_zero, map_one, _root_.mul_one]
      exact h0 a)
    (fun i => by
      simpa only [Subring.mem_comap, AddMonoidAlgebra.liftNCRingHom_single] using h i)
  rw [eq_top_iff]
  intro s _
  obtain ⟨b, rfl⟩ := hb.2 s
  exact Subring.mem_comap.1 (this.ge (Subring.mem_top b))
end GlobalTheory.ZH.WtGen
