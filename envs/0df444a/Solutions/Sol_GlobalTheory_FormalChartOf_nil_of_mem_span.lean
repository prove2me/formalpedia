-- Prove2me | solution 1 for GlobalTheory.FormalChartOf.nil_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:48:34.752945+00:00
-- url     : https://prove2.me/submissions/9623c8c5-9ebc-4b28-9cf1-c07baaaeb6e1

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsFormalChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.FormalChartOf
variable {R₀ : Type} [CommRing R₀]
namespace GlobalTheory.FormalChartOf
theorem _root_.solution {S : Type} [CommRing S] {g : ℕ} {a b : Fin g → S} (ha : ∀ i, IsNilpotent (a i))
    (hb : ∀ i, IsNilpotent (b i)) {c : S} (hc : c ∈ Ideal.span (Set.range a ∪ Set.range b)) :
    IsNilpotent c := by
  have : Ideal.span (Set.range a ∪ Set.range b) ≤ nilradical S := by
    rw [Ideal.span_le]
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact mem_nilradical.2 (ha i)
    · exact mem_nilradical.2 (hb i)
  exact mem_nilradical.1 (this hc)
end GlobalTheory.FormalChartOf
