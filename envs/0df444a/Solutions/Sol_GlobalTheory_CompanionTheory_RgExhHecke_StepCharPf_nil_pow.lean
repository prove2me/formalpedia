-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.nil_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:48.836807+00:00
-- url     : https://prove2.me/submissions/3a3e480a-4adf-4093-8cee-e4fe244f885d

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_nil_list

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution {f : Module.End ℂ V} {a : ℂ} (l : List (Module.End ℂ V))
    (hl : ∀ T ∈ l, ∃ b : ℂ, T = f - b • (1 : Module.End ℂ V)) (K : ℕ) :
    ∀ g ∈ f.maxGenEigenspace a, (l.prod ^ K) g = 0 →
      ((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g = 0 := by
  have hP : Commute f l.prod := Commute.list_prod_right _ _ fun T hT => by
    obtain ⟨c, rfl⟩ := hl T hT
    exact (Commute.refl f).sub_right ((Commute.one_right f).smul_right c)
  have hcf : Commute f (f - a • (1 : Module.End ℂ V)) :=
    (Commute.refl f).sub_right ((Commute.one_right f).smul_right a)
  have hPQ : Commute l.prod (f - a • (1 : Module.End ℂ V)) :=
    hP.symm.sub_right ((Commute.one_right _).smul_right a)
  induction K with
  | zero =>
    intro g _ h
    simpa using h
  | succ K ih =>
    intro g hg h
    have hPg : l.prod g ∈ f.maxGenEigenspace a :=
      Module.End.mapsTo_maxGenEigenspace_of_comm hP _ hg
    have e1 : (l.prod ^ K) (l.prod g) = 0 := by
      rw [pow_succ, Module.End.mul_apply] at h
      exact h
    have e2 := ih _ hPg e1
    have e3 : l.prod (((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g) = 0 := by
      have := congrArg (fun T : Module.End ℂ V => T g) (hPQ.pow_right (l.length * K)).eq
      simp only [Module.End.mul_apply] at this
      rw [this, e2]
    have hg' : ((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g ∈ f.maxGenEigenspace a :=
      Module.End.mapsTo_maxGenEigenspace_of_comm (hcf.pow_right _) _ hg
    have e4 := nil_list l hl _ hg' e3
    rw [Nat.mul_succ, add_comm, pow_add, Module.End.mul_apply]
    exact e4
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
