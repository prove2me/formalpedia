-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.nil_list
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:21:23.68583+00:00
-- url     : https://prove2.me/submissions/5cbace76-b26f-4bfa-bfd9-c220049f9f36

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement

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
    (hl : ∀ T ∈ l, ∃ b : ℂ, T = f - b • (1 : Module.End ℂ V)) :
    ∀ g ∈ f.maxGenEigenspace a, l.prod g = 0 → ((f - a • (1 : Module.End ℂ V)) ^ l.length) g = 0 := by
  induction l with
  | nil =>
    intro g _ h
    simpa using h
  | cons T l ih =>
    intro g hg h
    obtain ⟨b, rfl⟩ := hl T (by simp)
    have ih' := ih fun T hT => hl T (by simp [hT])
    have hcf : ∀ c : ℂ, Commute f (f - c • (1 : Module.End ℂ V)) := fun c =>
      (Commute.refl f).sub_right ((Commute.one_right f).smul_right c)
    have hP : Commute f l.prod := Commute.list_prod_right _ _ fun T hT => by
      obtain ⟨c, rfl⟩ := hl T (by simp [hT])
      exact hcf c
    have hPg : l.prod g ∈ f.maxGenEigenspace a :=
      Module.End.mapsTo_maxGenEigenspace_of_comm hP _ hg
    have hh : (f - b • (1 : Module.End ℂ V)) (l.prod g) = 0 := by simpa using h
    by_cases hb : b = a
    · subst hb
      have hcomm : Commute l.prod (f - b • (1 : Module.End ℂ V)) :=
        hP.symm.sub_right ((Commute.one_right _).smul_right b)
      have e : l.prod ((f - b • (1 : Module.End ℂ V)) g) = 0 := by
        have := congrArg (fun T : Module.End ℂ V => T g) hcomm.eq
        simp only [Module.End.mul_apply] at this
        rw [this, hh]
      have hg' : (f - b • (1 : Module.End ℂ V)) g ∈ f.maxGenEigenspace b :=
        Module.End.mapsTo_maxGenEigenspace_of_comm (hcf b) _ hg
      have := ih' _ hg' e
      rw [List.length_cons, pow_succ, Module.End.mul_apply]
      exact this
    · have h0 : l.prod g = 0 := by
        have hmem : l.prod g ∈ f.maxGenEigenspace b := by
          rw [Module.End.mem_maxGenEigenspace]
          exact ⟨1, by simpa using hh⟩
        exact Submodule.disjoint_def.1 (Module.End.disjoint_genEigenspace f hb ⊤ ⊤) _ hmem hPg
      have := ih' g hg h0
      rw [List.length_cons, pow_succ', Module.End.mul_apply, this, map_zero]
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
