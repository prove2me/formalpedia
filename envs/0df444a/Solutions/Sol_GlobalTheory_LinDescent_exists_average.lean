-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_average
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:10:24.730552+00:00
-- url     : https://prove2.me/submissions/8d3af3ae-ea05-4468-920a-4ad335499c20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_sum
import Theorems.Thm_GlobalTheory_LinDescent_gs_appLE
import Theorems.Thm_GlobalTheory_LinDescent_uv_cocycle
import Theorems.Thm_GlobalTheory_LinDescent_exists_translate
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X}
variable {C : Type} {t : C → (X ⟶ X)}
variable [Group C] [Finite C]
namespace GlobalTheory.LinDescent
theorem _root_.solution [Fintype C] (hL : L.IsLB) (ht : ∀ c c', t c ≫ t c' = t (c * c'))
    {u : ∀ c, LB.Gen (twist L (t c))} (hu : ∀ c, (u c).IsGen)
    (hc : ∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c'))
      (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') (t c))))
    {W : X.Opens} (hW : ∀ c, W ≤ t c ⁻¹ᵁ W) {m : ∀ i, Γ(X, W ⊓ L.U i)} (hm : IsLocSec L W m)
    (f : Γ(X, W)) :
    ∃ s : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W s ∧ IsInv u W s ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i (j : C → L.ι), r z ∈ W → r z ∈ L.U i →
        (∀ c, (r ≫ t c) z ∈ L.U (j c)) → gs r z _ (s i) = ∑ c,
          (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) * gs (r ≫ t c) z W f := by
  choose T hT hT' using fun c => exists_translate hL (hu c) (hW c) hm
  let s : ∀ i, Γ(X, W ⊓ L.U i) := fun i =>
    ∑ c, T c i * ((t c).appLE W _ (inf_le_left.trans (hW c))).hom f
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i, r z ∈ W → r z ∈ L.U i →
      gs r z _ (s i) = ∑ c, gs r z _ (T c i) * gs (r ≫ t c) z W f := fun Z r z i hz hi => by
    have h : r z ∈ W ⊓ L.U i := ⟨hz, hi⟩
    rw [gs_sum r z _ h]
    exact Finset.sum_congr rfl fun c _ => by rw [gs_mul r z _ h, gs_appLE r _ z _ _ _ h]
  have v' : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i (j : C → L.ι), r z ∈ W → r z ∈ L.U i →
      (∀ c, (r ≫ t c) z ∈ L.U (j c)) → gs r z _ (s i) = ∑ c,
        (uv (u c) r z i (j c)).val * gs (r ≫ t c) z _ (m (j c)) * gs (r ≫ t c) z W f :=
    fun Z r z i j hz hi hj => by
      rw [v Z r z i hz hi]
      exact Finset.sum_congr rfl fun c _ => by rw [hT' c Z r z i (j c) hz hi (hj c)]
  refine ⟨s, fun Z r z i j hz hi hj => ?_, fun d Z r z i k hz hi hk => ?_, v'⟩
  · rw [v Z r z i hz hi, v Z r z j hz hj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by rw [hT c Z r z i j hz hi hj, mul_assoc]
  · choose j hj using fun c => exists_chart hL ((r ≫ t c) z)
    have e : ∀ c, (r ≫ t d) ≫ t c = r ≫ t (d * c) := fun c => by rw [Category.assoc, ht]
    rw [v' Z r z i j hz hi hj, v' Z (r ≫ t d) z k (fun c => j (d * c)) (hW d hz) hk
      (fun c => by rw [e]; exact hj _), Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft d)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Equiv.coe_mulLeft, e, uv_cocycle hL (ht d c) (hu d) (hu c) (hu _) (hc d c) r z hi hk (hj _),
      Units.val_mul]
    simp only [mul_assoc]
end GlobalTheory.LinDescent
