-- Prove2me | solution 1 for GlobalTheory.AdmLoc.admissible_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:29:44.505178+00:00
-- url     : https://prove2.me/submissions/fa8c4626-b111-4915-844e-5bb09f0b4e9e

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
theorem _root_.solution {μ : ℕ} {T : LocLat G Qp LL O} (hT : SumFull PD emb Γ t Ut μ T)
    (L₂ : Lattice (O := O) T.ρ) (hle : L₂.T ≤ T.L.T) [Finite (↥T.L.T ⧸ L₂.T.comap T.L.T.subtype)] :
    Admissible PD emb Γ t Ut
      ((latRep T.L).quotient (L₂.T.comap T.L.T.subtype) (fun g x hx => L₂.stable g x hx)) :=
  ⟨‹_›, μ, T, hT, L₂, Submodule.mkQ _, hle, Submodule.mkQ_surjective _, fun _ _ => rfl,
    fun _ => Submodule.Quotient.mk_eq_zero _⟩
end GlobalTheory.AdmLoc
