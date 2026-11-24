-- Prove2me | solution 1 for GlobalTheory.PowSec.down_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:47:41.587641+00:00
-- url     : https://prove2.me/submissions/72cfb3db-3abf-44de-b192-20218a620301

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_ExistsBasisOfIsField
import Theorems.Thm_GlobalTheory_PowSec_appLE_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.PowSec
variable {X Y : Scheme.{0}} (L : LB X) (σ : Y ⟶ X) (ρ : X ⟶ Y) (e : ρ ≫ σ = 𝟙 X) (n : ℤ)
namespace GlobalTheory.PowSec
theorem _root_.solution [IsIso ρ] : Function.Surjective (down L σ ρ e n) := by
  intro t
  choose u hu using fun k : L.ι =>
    (appLE_bijective ρ _ _ (chart_eq L σ ρ e (fun _ => k))).2 (t.f (fun _ => k))
  let F : ∀ j : Fin 1 → L.ι, Γ(Y, LB.wchart L (fun _ : Fin 1 => σ) j) := fun j =>
    (Y.presheaf.map (eqToHom (congrArg (LB.wchart L (fun _ : Fin 1 => σ))
      (funext fun q => congrArg j (Subsingleton.elim q 0) : j = fun _ => j 0))).op).hom (u (j 0))
  have hF : ∀ k, F (fun _ => k) = u k := fun k => by
    show (Y.presheaf.map (𝟙 _)).hom (u k) = u k
    rw [Y.presheaf.map_id]; rfl
  have hF' : ∀ j : PUnit → L.ι,
      (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit)) = t.f j := fun j => by
    rw [hF]; exact hu (j PUnit.unit)
  refine ⟨⟨F, fun i' j' => ?_⟩, ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i : PUnit → L.ι, i' = fun _ => i PUnit.unit :=
      ⟨fun _ => i' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    obtain ⟨j, rfl⟩ : ∃ j : PUnit → L.ι, j' = fun _ => j PUnit.unit :=
      ⟨fun _ => j' 0, funext fun q => by rw [Subsingleton.elim q 0]⟩
    have heq : LB.wchart L (fun _ : PUnit => 𝟙 X) i ⊓ LB.wchart L (fun _ : PUnit => 𝟙 X) j =
      ρ ⁻¹ᵁ (LB.wchart L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) ⊓
        LB.wchart L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit)) :=
      congrArg₂ (· ⊓ ·) (chart_eq L σ ρ e i) (chart_eq L σ ρ e j)
    have hle := heq.le
    refine (appLE_bijective ρ _ _ heq).1 ?_
    refine Eq.trans ?_ (map_mul (ρ.appLE _ _ hle).hom _ _).symm
    have := t.compat i j
    rw [← hF' i, ← hF' j] at this
    refine Eq.trans (Eq.symm ?_) (this.trans (Eq.symm (congrArg₂ (· * ·) ?_ ?_)))
    · exact (congrArg (fun φ => φ.hom (F fun _ => i PUnit.unit))
        ((Scheme.Hom.appLE_map ρ _ _).trans (Scheme.Hom.map_appLE ρ hle _).symm) :)
    · simp only [LB.LinComb, Fintype.prod_unique]
      refine (congrArg Units.val ((map_zpow (Units.map (ρ.appLE _ _ hle).hom.toMonoidHom) _ n).trans
        (congrArg (· ^ n) (Units.ext ?_))) :)
      have h1 : (σ.app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => i PUnit.unit) 0))
          (inf_le_right.trans (LB.wchart_le L (fun _ : Fin 1 => σ) (fun _ => j PUnit.unit) 0)))).op) ≫ ρ.appLE _ _ hle =
          (𝟙 X : X ⟶ X).app (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ≫ X.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) i PUnit.unit))
          (inf_le_right.trans (LB.wchart_le L (fun _ : PUnit => 𝟙 X) j PUnit.unit)))).op :=
        (Scheme.Hom.appLE_comp_appLE ρ σ _ _ _ _ hle).trans (appLE_congr e _ _ _ _)
      exact congrArg (fun φ => φ.hom (L.g (i PUnit.unit) (j PUnit.unit)).val) h1
    · exact (congrArg (fun φ => φ.hom (F fun _ => j PUnit.unit))
        ((Scheme.Hom.map_appLE ρ hle _).trans (Scheme.Hom.appLE_map ρ _ _).symm) :)
  · obtain ⟨tf, tc⟩ := t
    have : (fun j : PUnit → L.ι => (ρ.appLE _ _ (chart_eq L σ ρ e j).le).hom (F (fun _ => j PUnit.unit))) = tf :=
      funext hF'
    subst this
    rfl
end GlobalTheory.PowSec
