-- Prove2me | solution 1 for GlobalTheory.BoxKernel.hasGen_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:53.718908+00:00
-- url     : https://prove2.me/submissions/6aa6e884-8e9f-4051-9ab6-46da363b1ac1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LocGenOfTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_KTrivExternalTensorPowerLineBundle
import Theorems.Thm_GlobalTheory_KerPow_gen_transfer


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.BoxKernel
open GlobalTheory.KerPow
variable {X X' Y B : Scheme.{0}} {L : LB X} {K J : Type} [Fintype K] [Fintype J]
namespace GlobalTheory.BoxKernel
theorem _root_.solution (F : J → (X' ⟶ X)) {ψ : K → (Y ⟶ X')} {ε : K → ℤ}
    (H : HasGen (LB.LinComb L F (fun _ => 1)) ψ ε) :
    HasGen L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) := by
  have le : ∀ (j : K × J → L.ι) (y : Y), y ∈ LB.wchart L (K := K × J) (fun q => ψ q.1 ≫ F q.2) j →
      y ∈ LB.wchart (LB.LinComb L F (fun _ => 1)) ψ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  refine gen_transfer (M := LB.LinComb (LB.LinComb L F (fun _ => 1)) ψ ε)
    (M' := LB.LinComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1))
    (fun j k i => j (k, i)) (fun j y hy => le j y hy) (fun j j' y hj hj' => ?_) H
  refine (gm_linComb L (K := K × J) (fun q => ψ q.1 ≫ F q.2) (fun q => ε q.1) (𝟙 Y) y j j' hj hj').trans
    (Eq.trans ?_ (gm_linComb (LB.LinComb L F (fun _ => 1)) ψ ε (𝟙 Y) y _ _ (le j y hj) (le j' y hj')).symm)
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun k _ => ?_
  refine Eq.trans ?_ (congrArg (· ^ ε k) (gm_linComb L F (fun _ => 1) (𝟙 Y ≫ ψ k) y (fun i => j (k, i))
    (fun i => j' (k, i)) (Set.mem_iInter.1 (le j y hj) k) (Set.mem_iInter.1 (le j' y hj') k)).symm)
  simp only [zpow_one, Category.assoc, Finset.prod_zpow]
end GlobalTheory.BoxKernel
