-- Prove2me | solution 1 for GlobalTheory.AdmLoc.mk_mem_admissibleAt_iff_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:28:16.475056+00:00
-- url     : https://prove2.me/submissions/46e614f6-7a12-40ed-a2a2-81639e11004e

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_StatementTor
import Definitions.Def_ReciprocityTheory_BasicDefinitions_AdRep
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Theorems.Thm_GlobalTheory_AdmLoc_Ea_equiv_of_class_eq
import Theorems.Thm_GlobalTheory_AdmLoc_Admissible_of_equiv

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
variable (PD emb Γ t Ut)
variable {M : Type} [AddCommGroup M] [Module O M] (W : Representation O G M)
  (X : Type) [AddCommGroup X] [Module O X]
variable {PD emb Γ t Ut W X}
namespace GlobalTheory.AdmLoc
theorem _root_.solution {a : ℕ} (ha : ∀ x : X, Γ.lam ^ a • x = 0) (z : ↥(Z1 (twCoef W Γ.χ₁ X) ⊤)) :
    Submodule.Quotient.mk z ∈ admAt PD emb Γ t Ut W X a ha ↔ Admissible PD emb Γ t Ut (Ea W Γ.χ₁ ha z) := by
  refine ⟨?_, fun h => ⟨z, rfl, h⟩⟩
  rintro ⟨z', hz, h⟩
  obtain ⟨e, he, -, -⟩ := Ea_equiv_of_class_eq W Γ.χ₁ ha hz
  exact h.of_equiv e he
end GlobalTheory.AdmLoc
