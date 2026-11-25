-- Prove2me | solution 1 for GlobalTheory.AdmLoc.admissible_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:36:29.707571+00:00
-- url     : https://prove2.me/submissions/123af4b0-7055-4e0e-98da-89ba35b63adc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AdmLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open Formalism.MainNotions.N (twistRep coefRep)
open Formalism.GaloisCohomology (scalRep)
open ReciprocityTheory.Def (Z1 B1 H1 d0 d1 C1)
open scoped Pointwise
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} (emb : ZMod n → (K₀ →ₐ[Qp] LL))
variable (Γ : GalData G Qp LL O) (t : ℕ) (Ut : ZMod n → Multiset ℤ)
variable {PD emb Γ t Ut}
namespace GlobalTheory.AdmLoc
theorem _root_.solution [IsTopologicalRing LL] {M : Type} [AddCommGroup M] [Module O M] [Subsingleton M]
    (π : Representation O G M) : Admissible PD emb Γ t Ut π := by
  have hV : Subsingleton (zeroLat G Qp LL O).V := inferInstanceAs (Subsingleton (Fin 0 → LL))
  refine ⟨inferInstance, 0, zeroLat G Qp LL O, ⟨Fin.elim0, fun j => j.elim0, LinearEquiv.ofSubsingleton _ _,
    fun _ _ j => j.elim0⟩, (zeroLat G Qp LL O).L, 0, le_rfl, fun y => ⟨0, Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, fun x => ⟨fun _ => x.2, fun _ => rfl⟩⟩
end GlobalTheory.AdmLoc
