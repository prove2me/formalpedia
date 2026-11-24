-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.sgStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:38:54.438436+00:00
-- url     : https://prove2.me/submissions/36ed70d7-0774-429d-886b-bef852f4673e

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_conv_congr
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_wallQ
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_wallsS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis
variable {E R : Type} [Field E] [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  [LocallyCompactSpace R] [SecondCountableTopology R]
open Classical
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution : Gallery → Transfer → Twist → GrpTop → ParLaw → LeviS → LeviQ → ConvGrOf → ConvU → SgStep := by
  intro hGal hTr hTw hTop hPar hLS hLQ hCG hCU E R _ _ _ _ _ _ _ A hA hMir ε ι _ _ hN hIH hS W _ _ _ ρ hρ
  obtain ⟨i₀⟩ : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨π, j, -, -, hIw, -⟩ := hLS E R A hA ι ε hS
  obtain ⟨-, -, -, t₄, t₅, t₆, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨Ra, ca₁, ca₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀} (hIw _)
  obtain ⟨Rb, -, cb₂⟩ := hCU E R A hA (hCG E R A hA hMir) ι ε {i₀}ᶜ (hIw _)
  have pS := (hPar E R A hA ι ε Set.univ).2 (hIw _)
  rw [inf_idem] at pS
  have pA := (hPar E R A hA ι ε {i₀}).2 (hIw _)
  have pB := (hPar E R A hA ι ε {i₀}ᶜ).2 (hIw _)
  have hc₀ : ∀ f : Fintype ({i₀}ᶜ : Set ι), @Fintype.card _ f = Fintype.card ι - 1 := fun f => by
    rw [Fintype.card_compl_set]; simp
  have hc₁ : ∀ f : Fintype (({i₀}ᶜ : Set ι)ᶜ : Set ι), @Fintype.card _ f = 1 := fun f => by
    rw [Fintype.card_compl_set, hc₀]; omega
  have hc₀' : ∀ f : Fintype ({i₀}ᶜ : Set ι), ((@Fintype.card _ f : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := fun f => by
    rw [hc₀, Nat.cast_sub (by omega)]; simp
  have hq := fun (s : Set ι) (f : Fintype (sᶜ : Set ι)) (d : DecidableEq (sᶜ : Set ι)) => @hIH (sᶜ : Set ι) f d
  have w₁ := wallQ hTr hTop hPar hLQ A hA ε {i₀} (hIw _)
    (hq _ _ _ (by rw [hc₀]; omega) (by rw [hc₀]; omega)) ρ hρ
  have w₂ := wallQ hTr hTop hPar hLQ A hA ε {i₀}ᶜ (hIw _)
    (hq _ _ _ (hc₁ _).ge (by rw [hc₁]; omega)) ρ hρ
  rw [hc₀'] at w₁
  rw [hc₁] at w₂
  simp only [Nat.cast_one, one_mul] at w₂
  rw [show (fun g => A.uH ε Set.univ g - A.uH ε {i₀}ᶜ g) = fun g => -(A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) from
    funext fun g => by ring] at w₂
  obtain ⟨s₁, s₂, s₃⟩ := wallsS hTr hTw hTop hPar hLS A hA hMir ε i₀ i₀ hN hS ρ hρ
  refine hGal (A.U ε ι) W (A.uK ε ι) ρ t₇ hρ inferInstance (A.uΓ ε ι) (A.uQ ε Set.univ)
    (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀}) (A.uQ ε {i₀}ᶜ) (A.uC ε ι)
    (A.uH ε Set.univ) (A.uH ε {i₀}) (fun g => A.uH ε {i₀}ᶜ g - A.uH ε Set.univ g) (Fintype.card ι)
    inf_le_right inf_le_right inf_le_left inf_le_left pS.1 pA.1 pB.1 pS.2.1 pA.2.1
    (isHt_congr pB.2.1 fun g => by ring) ⟨max Ra Rb, fun y hy => ca₁ y (lt_of_le_of_lt (le_max_left _ _) hy),
      fun z y hz hy => ca₂ z y (lt_of_le_of_lt (le_max_left _ _) hz) (lt_of_le_of_lt (le_max_left _ _) hy),
      fun r y hr hy => conv_congr (cb₂ r y (lt_of_le_of_lt (le_max_right _ _) hr)
        (lt_of_le_of_lt (le_max_right _ _) hy)) fun g => by ring⟩ s₁ w₂ s₂ w₁ s₃
end GlobalTheory.CompanionTheory.RgEis
