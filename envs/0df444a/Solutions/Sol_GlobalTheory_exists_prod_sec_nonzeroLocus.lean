-- Prove2me | solution 1 for GlobalTheory.exists_prod_sec_nonzeroLocus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:30:03.202654+00:00
-- url     : https://prove2.me/submissions/b0b41a01-2e18-4c7e-a9b8-ac81a1b27bfa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemNonzeroLocusIffMemBasicOpenChart
import Theorems.Thm_GlobalTheory_mem_nonzeroLocus_iff_mem_basicOpen_chart
import Theorems.Thm_GlobalTheory_mem_basicOpen_finset_prod_iff
import Theorems.Thm_GlobalTheory_mem_finset_biInf_opens_iff
import Theorems.Thm_GlobalTheory_AbLaw_SecOnR_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (Y : Scheme.{0}) (H : LB Y) (ι : Type) (s : ι → LB.Sec H) (I : Finset ι), H.IsLB → ∃ σ : LB.Sec (pw H (I.card : ℤ)), (∀ l : H.ι, σ.f l = ∏ i ∈ I, (s i).f l) ∧ nonzeroLocus σ = ⨅ i ∈ I, nonzeroLocus (s i) := by
  intro Y H ι s I hH
  let σ : LB.Sec (pw H (I.card : ℤ)) :=
    { f := fun l : H.ι => ∏ i ∈ I, (s i).f l
      compat := fun k l : H.ι => by
        change (Y.presheaf.map (homOfLE (inf_le_left : H.U k ⊓ H.U l ≤ H.U k)).op).hom
            (∏ i ∈ I, (s i).f k) = ((H.g k l ^ (I.card : ℤ) : Γ(Y, H.U k ⊓ H.U l)ˣ) :
              Γ(Y, H.U k ⊓ H.U l)) *
          (Y.presheaf.map (homOfLE (inf_le_right : H.U k ⊓ H.U l ≤ H.U l)).op).hom
            (∏ i ∈ I, (s i).f l)
        rw [map_prod, map_prod, zpow_natCast, Units.val_pow_eq_pow_val, ← Finset.prod_const,
          ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => (s i).compat k l }
  refine ⟨σ, fun _ => rfl, TopologicalSpace.Opens.ext (Set.ext fun x => ?_)⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (show x ∈ (⊤ : Y.Opens) from trivial))
  refine (mem_nonzeroLocus_iff_mem_basicOpen_chart σ l hl).trans
    (((mem_basicOpen_finset_prod_iff (fun i => (s i).f l) I hl).trans ?_).trans
      (mem_finset_biInf_opens_iff (fun i => nonzeroLocus (s i)) I).symm)
  exact forall₂_congr fun i _ => (mem_nonzeroLocus_iff_mem_basicOpen_chart (s i) l hl).symm
end GlobalTheory
