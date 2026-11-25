-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.stepChar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:11:43.934881+00:00
-- url     : https://prove2.me/submissions/6be0aba3-52dd-40f3-954b-cc51959624e1

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_algProd
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_polyFn_qdet
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_PolyFn_vanish
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_core
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_ext
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_sub
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_Rs_commute
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_nil_pow
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_capelliPoly_eq_mul_prod_erase
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_capelliPoly_add_single
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_compLeft_pow_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_commute_C_om
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_commute_T_om
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_add
import Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_PolF_mul


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
open Formalism.QuantumDeterminants (capP)
variable {n : ℕ}
namespace GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
theorem _root_.solution (hT : QdetTens) (hC : CayleyHam) : StepChar := by
  intro n X χ s hχ
  obtain ⟨K0, hK0⟩ := hC n X χ hχ
  obtain ⟨k, hk⟩ := hχ
  obtain ⟨z, hz⟩ : ∃ z, z = χ s := ⟨_, rfl⟩
  rw [← hz]
  obtain ⟨a, ha⟩ : ∃ a, a = z - cn n := ⟨_, rfl⟩
  have hstab : ∀ O : Module.End ℂ (Fin n → X.V), Commute O (om X) →
      ∀ x ∈ stepSub X z, O x ∈ stepSub X z := fun O h _ hx =>
    Module.End.mapsTo_maxGenEigenspace_of_comm h.symm _ hx
  have hSa : stepSub X z = (om X).maxGenEigenspace a := by rw [ha]; rfl

  obtain ⟨M, hM⟩ : ∃ M, ∀ g ∈ stepSub X z, ((om X - a • (1 : Module.End ℂ (Fin n → X.V))) ^ M) g = 0 := by
    refine ⟨_, fun g hg => nil_pow (f := om X) (a := a)
      (List.ofFn fun t : Fin n => om X - (χ t - cn n) • (1 : Module.End ℂ (Fin n → X.V)))
      (fun T hT' => ?_) K0 g (hSa ▸ hg) ?_⟩
    · obtain ⟨t, rfl⟩ := (List.mem_ofFn' _ _).1 hT'
      exact ⟨_, rfl⟩
    · rw [hK0]; simp
  have hcomν : Commute (om X - a • (1 : Module.End ℂ (Fin n → X.V))) (om X) :=
    (Commute.refl _).sub_left ((Commute.one_left _).smul_left a)
  let ν : Module.End ℂ (stepSub X z) :=
    (om X - a • (1 : Module.End ℂ (Fin n → X.V))).restrict (hstab _ hcomν)
  let c : ℂ → Module.End ℂ (stepSub X z) := fun u =>
    ((qdet X.E u).compLeft (Fin n)).restrict (hstab _ (commute_C_om X u))
  let D : ℂ → Module.End ℂ (stepSub X z) := fun u => qdet (step X z).E u
  have hRν : Rs ν (om X - a • (1 : Module.End ℂ (Fin n → X.V))) := fun _ => rfl
  have hRc : ∀ u, Rs (c u) ((qdet X.E u).compLeft (Fin n)) := fun _ _ => rfl
  have hRD : ∀ u, Rs (D u) (qdet (tensE X) u) := fun u => Rs.qdet (fun _ _ _ => rfl) u
  have hν : ν ^ M = 0 := (hRν.pow M).ext fun x => by
    simpa using (hM x x.2).symm
  have hcν : ∀ u, Commute (c u) ν := fun u =>
    (hRc u).commute hRν ((commute_C_om X u).sub_right ((Commute.one_right _).smul_right a))
  have hDν : ∀ u, Commute (D u) ν := fun u =>
    (hRD u).commute hRν ((commute_T_om X u).sub_right ((Commute.one_right _).smul_right a))
  have hadd : ∀ u : ℂ, Rs (algebraMap ℂ (Module.End ℂ (stepSub X z)) (u + a) + ν)
      (u • (1 : Module.End ℂ (Fin n → X.V)) + om X) := by
    intro u
    have h := (Rs.alg (S := stepSub X z) (u + a)).add hRν
    have e : algebraMap ℂ (Module.End ℂ (Fin n → X.V)) (u + a) +
        (om X - a • (1 : Module.End ℂ (Fin n → X.V))) =
        u • (1 : Module.End ℂ (Fin n → X.V)) + om X := by
      rw [Algebra.algebraMap_eq_smul_one, add_smul]
      abel
    rwa [e] at h
  have hid : ∀ u, D u * (algebraMap ℂ _ (u + a) + ν) = c u * (algebraMap ℂ _ (u + a + 1) + ν) := by
    intro u
    have e2 : Rs (algebraMap ℂ (Module.End ℂ (stepSub X z)) (u + a + 1) + ν)
        ((u + 1) • (1 : Module.End ℂ (Fin n → X.V)) + om X) := by
      have := hadd (u + 1)
      rwa [show u + 1 + a = u + a + 1 by ring] at this
    refine ((hRD u).mul (hadd u)).ext ?_
    rw [hT n X u]
    exact (hRc u).mul e2
  obtain ⟨R, hRdef⟩ : ∃ R : ℂ → ℂ, R = fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) := ⟨_, rfl⟩
  have hN : ∀ u, (c u - algebraMap ℂ _ (R u * (u + a))) ^ k = 0 := by
    intro u
    have hp : capP χ (u - cn n) = R u * (u + a) := by
      rw [capelliPoly_eq_mul_prod_erase _ s, hRdef, ha, hz]
      congr 1
      ring
    have h0 := hk (u - cn n)
    have e : u - cn n + ((n : ℂ) - 1) / 2 = u := by simp [cn]
    rw [e, hp, ← Algebra.algebraMap_eq_smul_one] at h0
    refine (((hRc u).sub (Rs.alg (R u * (u + a)))).pow k).ext fun x => ?_
    have hz0 : (((qdet X.E u).compLeft (Fin n) -
        algebraMap ℂ (Module.End ℂ (Fin n → X.V)) (R u * (u + a))) ^ k) (x : Fin n → X.V) = 0 := by
      funext i
      rw [compLeft_pow_apply, h0]
      simp
    rw [hz0]
    simp
  have hcore : ∀ u, u + a ≠ 0 → (D u - algebraMap ℂ _ (R u * (u + a + 1))) ^ (k + M) = 0 :=
    fun u hu => core hu hν (hN u) (hcν u) (hDν u) (hid u)
  unfold HasChar
  refine ⟨k + M, fun Y => ?_⟩
  obtain ⟨F, hFdef⟩ : ∃ F : ℂ → Module.End ℂ (stepSub X z), F = fun u =>
      (D u - algebraMap ℂ _ (capP (χ + Pi.single s 1) (u - cn n))) ^ (k + M) := ⟨_, rfl⟩
  have hPF : PolyFn F := by
    rw [hFdef]
    refine PolyFn.pow (PolyFn.sub (polyFn_qdet _) ?_) _
    unfold capP
    refine PolyFn.algProd _ fun t => ?_
    simp only [map_add, map_sub]
    exact (PolyFn.alg.sub (PolyFn.const _)).add (PolyFn.const _)
  have hF : ∀ u, u ≠ -a → F u = 0 := by
    intro u hu
    have hp : capP (χ + Pi.single s 1) (u - cn n) = R u * (u + a + 1) := by
      rw [capelliPoly_add_single, hRdef, ha, hz]
      congr 1
      ring
    rw [hFdef]
    simp only
    rw [hp]
    exact hcore u fun h => hu (eq_neg_of_add_eq_zero_left h)
  have hF0 : ∀ u, F u = 0 := fun u => by
    by_cases h : u = -a
    · rw [h]
      exact hPF.vanish _ hF
    · exact hF u h
  have h := hF0 (Y + cn n)
  rw [hFdef] at h
  simp only [add_sub_cancel_right] at h
  rw [Algebra.algebraMap_eq_smul_one] at h
  exact h
end GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
