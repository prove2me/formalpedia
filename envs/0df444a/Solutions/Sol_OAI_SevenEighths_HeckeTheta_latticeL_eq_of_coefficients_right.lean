-- Prove2me | solution 1 for OAI.SevenEighths.HeckeTheta.latticeL_eq_of_coefficients_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:49:35.797134+00:00
-- url     : https://prove2.me/submissions/823af4a1-8f57-4455-99e6-209cdca94652

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Family
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_ThetaSeries
import Definitions.Def_OAI_NumberTheory_DirichletL_Continuation
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FamilySeries
import Theorems.Thm_OAI_SevenEighths_HeckeTheta_latticeL_hasSum


set_option autoImplicit false
open OAI
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta
namespace OAI.SevenEighths.HeckeTheta
theorem _root_.solution {N M : ℕ} [NeZero N] [NeZero M]
    (w : Fin N × Fin N → ℂ) (v : Fin M × Fin M → ℂ)
    (hcoeff : ∀ n, periodicCoeff w n = periodicCoeff v n)
    {s : ℂ} (hs : 1 < s.re) : latticeL w s = latticeL v s := by
  have hw := latticeL_hasSum w hs
  simp_rw [hcoeff] at hw
  exact hw.unique (latticeL_hasSum v hs)
end OAI.SevenEighths.HeckeTheta
