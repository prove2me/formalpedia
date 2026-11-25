-- Prove2me | solution 1 for GlobalTheory.bxFibre_exists_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:41:25.166434+00:00
-- url     : https://prove2.me/submissions/ec4e1d4f-cdba-4eb2-8e1a-49140a3dd398

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PointsFibreProduct

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
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U) {P : Type}
    [CommRing P] [IsLocalRing P] (x : Spec (CommRingCat.of P) ⟶ Y)
    (h : x (closedPoint P) ∈ U) :
    ∃ φ : Γ(Y, U) →+* P, x = Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec := by
  have hx : ⊤ ≤ x ⁻¹ᵁ U := fun p _ => by
    have hsp : (p : PrimeSpectrum P) ⤳ closedPoint P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp
        (IsLocalRing.le_maximalIdeal (p : PrimeSpectrum P).isPrime.ne_top)
    exact hsp.mem_open (x ⁻¹ᵁ U).isOpen h
  refine ⟨(x.appLE U ⊤ hx ≫ (Scheme.ΓSpecIso (CommRingCat.of P)).hom).hom, ?_⟩
  have h := IsAffineOpen.SpecMap_appLE_fromSpec x hU
    (isAffineOpen_top (Spec (CommRingCat.of P))) hx
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, h, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]
end GlobalTheory
