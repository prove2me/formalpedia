-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.ideal_sup_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:53:16.756352+00:00
-- url     : https://prove2.me/submissions/35fc8d9c-946c-4746-88c9-ebdf32ea7682

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncChartMultihomogOrderAtPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm
import Theorems.Thm_ReciprocityTheory_AnForm_R_conePts_of_chartIdeal
import Theorems.Thm_ReciprocityTheory_AnForm_R_mem_map_renR_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Ar.Cmp
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
theorem _root_.solution (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k)
    (hP : IsMultiHomogIdeal P) (f : MvPolynomial (Σ k, ι k) ℂ)
    (hf : ∀ z' ∈ conePts P, eval z' f = 0 → z' ∈ conePts D)
    (𝔮 : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k))) ℂ)) (h𝔮 : 𝔮.IsPrime)
    (hI : SncRes.ideal P p ≤ 𝔮) (hg : bind₁ (SncRes.lift p) f ∈ 𝔮) :
    SncRes.ideal (P ⊔ D) p ≤ 𝔮 := by
  classical
  intro h hh
  have hvan : h ∈ vanishingIdeal ℂ (zeroLocus ℂ 𝔮) := by
    rw [mem_vanishingIdeal_iff]
    intro w hw
    have hw0 : ∀ c ∈ 𝔮, eval w c = 0 := fun c hc => by simpa using hw c hc
    let w' : (Σ k, ι k) → ℂ := w ∘ Fintype.equivFin (Σ k, ι k)
    have hpt : renPt w' = w := by
      funext j
      simp [renPt, w']
    have hren : ∀ x, eval w (renC (Σ k, ι k) x) = eval w' x := fun x => by
      rw [← eval_renC w' x, hpt]
    have hchart : ∀ c ∈ chartIdeal P p, eval w' c = 0 := fun c hc => by
      rw [← hren]
      have hs : (renR (Σ k, ι k)).symm (renC (Σ k, ι k) c) = c := (renR (Σ k, ι k)).symm_apply_apply c
      have hm : renC (Σ k, ι k) c ∈ SncRes.ideal P p := by
        unfold SncRes.ideal
        rw [mem_map_renR_iff, hs]
        exact hc
      exact hw0 _ (hI hm)
    obtain ⟨hcone, h1, -⟩ := conePts_of_chartIdeal hP p w' hchart
    have hlift : (fun q => eval w (SncRes.lift p q)) = w' := by
      funext q
      unfold SncRes.lift
      split_ifs with hq
      · obtain ⟨k, i⟩ := q
        simp only at hq
        subst hq
        simp [h1 k]
      · simp [w']
    have hfz : eval w' f = 0 := by
      have h2 : eval w (bind₁ (SncRes.lift p) f) = eval (fun q => eval w (SncRes.lift p q)) f :=
        eval₂Hom_bind₁ _ _ _ _
      rw [← hlift, ← h2]
      exact hw0 _ hg
    have hD := hf w' hcone hfz
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval w') := by
      refine sup_le (sup_le (fun c hc => RingHom.mem_ker.mpr (hcone.2 c hc))
        (fun c hc => RingHom.mem_ker.mpr (hD.2 c hc))) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval w' _ = 0
      simp [h1 k]
    have h3 : eval w' ((renR (Σ k, ι k)).symm h) = 0 :=
      RingHom.mem_ker.mp (hle ((mem_map_renR_iff _ h).1 hh))
    have e1 : renC (Σ k, ι k) ((renR (Σ k, ι k)).symm h) = h := (renR (Σ k, ι k)).apply_symm_apply h
    show eval w h = 0
    rw [← e1, hren, h3]
  rwa [vanishingIdeal_zeroLocus_eq_radical, h𝔮.radical] at hvan
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono
