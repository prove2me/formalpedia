-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.wallsS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:21:20.182485+00:00
-- url     : https://prove2.me/submissions/a316b6da-0dcc-4d75-94c1-5bba798aee91

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_mono
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_lin
import Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_isHt_congr

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
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (hTr : Transfer) (hTw : Twist) (hTop : GrpTop) (hPar : ParLaw) (hLS : LeviS) (A : Ad E R) (hA : A.Good)
    (hMir : A.MirGL) (ε : ℤˣ) {ι : Type} [Fintype ι] [DecidableEq ι] (i₀ i₁ : ι) (hN : 2 ≤ Fintype.card ι)
    (hS : Iwa (A.uQ ε (Set.univ : Set ι)) (A.uK ε ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasFirst (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)) ρ ∧
    HasWall (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uC ε ι) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g) (A.uH ε {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g) ρ ∧
    HasLast (A.uΓ ε ι ⊓ A.uQ ε Set.univ) (A.uK ε ι) (A.uQ ε Set.univ) (A.uQ ε {i₀} ⊓ A.uQ ε Set.univ)
      (A.uQ ε {i₁}ᶜ ⊓ A.uQ ε Set.univ) (A.uC ε ι) (A.uH ε {i₀}) (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (A.uH ε Set.univ) (Fintype.card ι) ρ := by
  obtain ⟨π, j, hL, hP, -, hH⟩ := hLS E R A hA ι ε hS
  obtain ⟨g₁, g₂, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  have hk := hA.kcpt ι
  obtain ⟨a₁, a₂, ch, h₀, -⟩ := (hPar E R A hA ι ε {i₀}).1
  obtain ⟨b₁, b₂, -, h₁, -⟩ := (hPar E R A hA ι ε {i₁}ᶜ).1
  obtain ⟨u₁, u₂, -, hu, hst⟩ := (hPar E R A hA ι ε Set.univ).1
  rw [hst] at u₁ u₂ hu
  have hPS : IsPull (A.uQ ε Set.univ) (A.uQ ε Set.univ) ⊤ π 1 (A.uC ε ι) (A.cGL ι) := by
    have := hP Set.univ
    rwa [inf_idem, hst] at this
  have e : (1 : GL ι R → ℂ) * A.cGL ι = A.cGL ι := one_mul _
  obtain ⟨m₁, m₂, m₃⟩ := hMir ι i₀ i₁ hN
  have d₁ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ) (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin 1 (-1) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₂ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₁}ᶜ)
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (1 - (Fintype.card ι : ℝ)) h₁ (isHt_mono hu le_top)) fun g => by ring
  have d₃ : IsHt (A.ratGL ι) (A.kGL ι) (stab R {i₀})
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card ι : ℝ) (-1) h₀ (isHt_mono hu le_top)) fun g => by ring
  have p₁ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π (fun g => A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g)
      (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₂ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => A.uH ε Set.univ g + (Fintype.card ι : ℝ) * (A.uH ε {i₁}ᶜ g - A.uH ε Set.univ g))
      (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) := by
    intro q k hk'
    simp only [hH {i₁}ᶜ q k hk', hH Set.univ q k hk']
  have p₃ : PullHt (A.uK ε ι) (A.uQ ε Set.univ) π
      (fun g => (Fintype.card ι : ℝ) * A.uH ε {i₀} g - A.uH ε Set.univ g)
      (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) := by
    intro q k hk'
    simp only [hH {i₀} q k hk', hH Set.univ q k hk']
  have T₁ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₀}) (stab R {i₁}ᶜ) 1 (A.cGL ι) (A.htGL {i₀})
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g)
    (fun g => A.htGL Set.univ g + (Fintype.card ι : ℝ) * (A.htGL {i₁}ᶜ g - A.htGL Set.univ g)) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ a₁ b₁
  have T₂ := hTw (GL ι R) (A.ratGL ι) (A.kGL ι) ⊤ (stab R {i₁}ᶜ) (stab R {i₀}) 1 (A.cGL ι)
    (fun g => A.htGL {i₁}ᶜ g - A.htGL Set.univ g) (A.htGL {i₀})
    (fun g => (Fintype.card ι : ℝ) * A.htGL {i₀} g - A.htGL Set.univ g) (A.htGL Set.univ)
    (Fintype.card ι) hk ch u₁ b₁ a₁
  rw [e] at T₁ T₂
  have X₁ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₀}) (hP {i₁}ᶜ) u₂ a₂ b₂ h₀ d₁ d₂ (hH {i₀}) p₁ p₂ (hH Set.univ)
  have X₂ := hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j 1 _ _ _ _ _ _ _ _ _ _ (Fintype.card ι) hk hL hPS
    (hP {i₁}ᶜ) (hP {i₀}) u₂ b₂ a₂ d₁ h₀ d₃ p₁ (hH {i₀}) p₃ (hH Set.univ)
  exact ⟨X₁.2.1 (T₁.2.1 m₁), X₂.1 (T₂.1 m₂), X₁.2.2 (T₁.2.2 m₃)⟩
end GlobalTheory.CompanionTheory.RgEis
