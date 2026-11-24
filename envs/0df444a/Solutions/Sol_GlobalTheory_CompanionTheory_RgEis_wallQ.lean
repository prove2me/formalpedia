-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgEis.wallQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:59:01.627671+00:00
-- url     : https://prove2.me/submissions/5ae10d08-a4f0-43d9-a952-896dfef31e16

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SiegelInductionFromGallery
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
open Classical
namespace GlobalTheory.CompanionTheory.RgEis
theorem _root_.solution (hTr : Transfer) (hTop : GrpTop) (hPar : ParLaw) (hLQ : LeviQ) (A : Ad E R) (hA : A.Good) (ε : ℤˣ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : Set ι) (hI : Iwa (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uK ε ι))
    (hSg : A.Sg ε (sᶜ : Set ι)) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (ρ : A.uK ε ι →* (W →L[ℂ] W)) (hρ : Continuous ρ) :
    HasWall (A.uΓ ε ι ⊓ A.uQ ε s) (A.uK ε ι) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uQ ε s ⊓ A.uQ ε Set.univ) (A.uC ε ι)
      (fun g => A.uH ε Set.univ g - A.uH ε s g) (fun g => A.uH ε Set.univ g - A.uH ε s g)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g)) ρ := by
  obtain ⟨π, j, c₀, hL, hP, hIw, hPH⟩ := hLQ E R A hA ι ε s hI
  obtain ⟨-, -, -, t₄, t₅, -, t₇⟩ := hTop E R A hA ι ε
  obtain ⟨-, -, -, u₄, u₅, -, u₇⟩ := hTop E R A hA (sᶜ : Set ι) ε
  have hP' := (hPar E R A hA (sᶜ : Set ι) ε Set.univ).2 (by rwa [inf_idem])
  rw [inf_idem] at hP'
  obtain ⟨hp, hh, -⟩ := hP'
  have hβ' : IsHt (A.uΓ ε (sᶜ : Set ι)) (A.uK ε (sᶜ : Set ι)) (A.uQ ε Set.univ)
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) :=
    isHt_congr (isHt_lin (Fintype.card (sᶜ : Set ι) : ℝ) 0 hh hh) fun g => by ring
  have hPβ : PullHt (A.uK ε ι) (A.uQ ε s) π
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * (A.uH ε Set.univ g - A.uH ε s g))
      (fun g => (Fintype.card (sᶜ : Set ι) : ℝ) * A.uH ε Set.univ g) := by
    intro q k hk
    have := hPH q k hk
    simp only at this ⊢
    rw [this]
  exact (hTr _ W _ ρ t₇ hρ _ _ _ _ _ _ _ _ _ _ _ π j c₀ _ _ _ _ _ _ _ _ _ _ 0 u₇ hL hP hP hP hp hp hp hh hh hβ'
    hPH hPH hPβ hPH).1 (hSg hIw)
end GlobalTheory.CompanionTheory.RgEis
