-- Prove2me | solution 1 for OAI.SevenEighths.CenteredMomentCorrelation.fullCorrelation_idealCRT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:22.929233+00:00
-- url     : https://prove2.me/submissions/23af76f3-4bfd-4dd0-a4d1-e2df5db07bcc

import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_Correlation
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_OAI_NumberTheory_DirichletL_Moments_CRT
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_ringEquiv
import Theorems.Thm_OAI_SevenEighths_CenteredMomentCorrelation_fullCorrelation_pi

set_option autoImplicit false
open OAI
open scoped BigOperators Classical
open OAI.SevenEighths OAI.SevenEighths.CenteredMomentCorrelation
noncomputable section
variable {A B : Type*} [CommRing A] [CommRing B] [Fintype A] [Fintype B]
namespace OAI.SevenEighths.CenteredMomentCorrelation
theorem _root_.solution {S ι : Type*} [CommRing S] [Fintype ι]
    (I : ι → Ideal S) (hI : Pairwise (Function.onFun IsCoprime I))
    [Fintype (S ⧸ ⨅ i, I i)] [∀ i, Fintype (S ⧸ I i)]
    (u v k : S ⧸ ⨅ i, I i) (f g : ∀ i, S ⧸ I i → ℂ) :
    let e := Ideal.quotientInfRingEquivPiQuotient I hI
    fullCorrelation (fun x => v * x) (fun y => u * y)
        (fun x => ∏ i, f i (e x i)) (fun y => ∏ i, g i (e y i)) k =
      ∏ i, fullCorrelation (fun x => e v i * x) (fun y => e u i * y)
        (f i) (g i) (e k i) := by
  classical
  dsimp only
  rw [fullCorrelation_ringEquiv (Ideal.quotientInfRingEquivPiQuotient I hI) u v k
    (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)), fullCorrelation_pi]
end OAI.SevenEighths.CenteredMomentCorrelation
